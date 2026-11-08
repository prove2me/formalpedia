-- Prove2me | solution 1 for BKAbsorption.absorption_free_term
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T17:12:19.788928+00:00
-- url     : https://prove2.me/submissions/9b23b75f-2f22-4072-a099-33995f69bddd

import Definitions.Def_BKAbsorption_defs
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
Barto–Kozik, Proposition 2.7 (paper proof: Lemma 2.6, Claims 2.8 and 2.9).
-/

universe u₁ v₁ w₁

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

namespace BKAbsorption
namespace P27

variable {L : FirstOrder.Language.{u₁, v₁}} {A : Type w₁} [L.Structure A]

/-- Star composition `t ⋆ s`: `t(s(x_{0,·}), …, s(x_{m-1,·}))` on `m * n` variables. -/
def star {m n : ℕ} (t : L.Term (Fin m)) (s : L.Term (Fin n)) : L.Term (Fin (m * n)) :=
  t.subst (fun j => s.relabel (fun l => finProdFinEquiv (j, l)))

theorem realize_star {m n : ℕ} (t : L.Term (Fin m)) (s : L.Term (Fin n))
    (a : Fin (m * n) → A) :
    (star t s).realize a =
      t.realize (fun j => s.realize (fun l => a (finProdFinEquiv (j, l)))) := by
  simp only [star, Term.realize_subst, Term.realize_relabel, Function.comp_def]

/-- Term operations of an idempotent algebra are idempotent. -/
theorem realize_const (hid : IsIdempotent L A) {α : Type*} (t : L.Term α) (a : A) :
    t.realize (fun _ => a) = a := by
  induction t with
  | var => rfl
  | func f ts ih =>
    simp only [Term.realize]
    rw [show (fun i => (ts i).realize fun _ => a) = fun _ => a from funext ih]
    exact hid _ f a

/-- `W(t, b, i)`: values of `t` on tuples with `b` at coordinate `i`. -/
def W {n : ℕ} (t : L.Term (Fin n)) (b : A) (i : Fin n) : Set A :=
  {c | ∃ a : Fin n → A, a i = b ∧ t.realize a = c}

theorem self_mem_W (hid : IsIdempotent L A) {n : ℕ} (t : L.Term (Fin n)) (b : A) (i : Fin n) :
    b ∈ W t b i :=
  ⟨fun _ => b, rfl, realize_const hid t b⟩

/-- The key expansion step used in Claims 2.8 and 2.9. -/
theorem mem_W_star (hid : IsIdempotent L A) {m n : ℕ} (t : L.Term (Fin m))
    (s : L.Term (Fin n)) (b : A) (j : Fin m) (k : Fin n) (f : Fin m → A)
    (hf : f j ∈ W s b k) : t.realize f ∈ W (star t s) b (finProdFinEquiv (j, k)) := by
  classical
  obtain ⟨a, hak, hav⟩ := hf
  refine ⟨fun p => (fun q : Fin m × Fin n => if q.1 = j then a q.2 else f q.1)
    (finProdFinEquiv.symm p), ?_, ?_⟩
  · simp [hak]
  · rw [realize_star]
    congr 1
    funext j'
    by_cases h : j' = j
    · subst h; simp [hav]
    · simp [h, realize_const hid]

/-- `s` handles the pair `(B, c)`: `c = s(a)` for some tuple `a` from `B`. -/
def Handles {n : ℕ} (s : L.Term (Fin n)) (p : Set A × A) : Prop :=
  ∃ a : Fin n → A, (∀ i, a i ∈ p.1) ∧ s.realize a = p.2

theorem handles_star_left (hid : IsIdempotent L A) {m n : ℕ} (t : L.Term (Fin m))
    (s : L.Term (Fin n)) (p : Set A × A) (h : Handles t p) : Handles (star t s) p := by
  obtain ⟨a, ha, hr⟩ := h
  refine ⟨fun q => a (finProdFinEquiv.symm q).1, fun q => ha _, ?_⟩
  rw [realize_star]
  simp only [Equiv.symm_apply_apply, realize_const hid]
  exact hr

theorem handles_star_right (hid : IsIdempotent L A) {m n : ℕ} (t : L.Term (Fin m))
    (s : L.Term (Fin n)) (p : Set A × A) (h : Handles s p) : Handles (star t s) p := by
  obtain ⟨a, ha, hr⟩ := h
  refine ⟨fun q => a (finProdFinEquiv.symm q).2, fun q => ha _, ?_⟩
  rw [realize_star]
  simp only [Equiv.symm_apply_apply]
  rw [show (fun _ : Fin m => s.realize a) = fun _ => p.2 from funext fun _ => hr]
  exact realize_const hid t p.2

/-- Lemma 2.6 (for nonempty generating sets, with `Sg(B)` given by terms over `B`). -/
theorem lemma26 [Finite A] (hid : IsIdempotent L A) :
    ∃ (ms : ℕ) (s : L.Term (Fin ms)), 0 < ms ∧
      ∀ B : Set A, B.Nonempty → ∀ t : L.Term B, Handles s (B, t.realize Subtype.val) := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have key : ∀ P : Finset (Set A × A),
      (∀ p ∈ P, p.1.Nonempty ∧ ∃ t : L.Term p.1, t.realize Subtype.val = p.2) →
      ∃ (ms : ℕ) (s : L.Term (Fin ms)), 0 < ms ∧ ∀ p ∈ P, Handles s p := by
    intro P
    induction P using Finset.induction_on with
    | empty => intro _; exact ⟨1, var 0, one_pos, by simp⟩
    | insert p P hp ih =>
      intro hP
      obtain ⟨ms, s, hms, hs⟩ := ih (fun q hq => hP q (Finset.mem_insert_of_mem hq))
      obtain ⟨hne, t, ht⟩ := hP p (Finset.mem_insert_self p P)
      let e := Fintype.equivFin p.1
      have hpos : 0 < Fintype.card p.1 := Fintype.card_pos_iff.2 hne.to_subtype
      refine ⟨Fintype.card p.1 * ms, star (t.relabel e) s, Nat.mul_pos hpos hms, ?_⟩
      intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq
      · apply handles_star_left hid
        refine ⟨fun i => (e.symm i : A), fun i => (e.symm i).2, ?_⟩
        rw [Term.realize_relabel]
        rw [← ht]
        congr 1
        funext x
        simp
      · exact handles_star_right hid _ _ _ (hs q hq)
  obtain ⟨ms, s, hms, hs⟩ := key (Finset.univ.filter
    (fun p : Set A × A => p.1.Nonempty ∧ ∃ t : L.Term p.1, t.realize Subtype.val = p.2))
    (fun p hp => (Finset.mem_filter.1 hp).2)
  exact ⟨ms, s, hms, fun B hB t => hs _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hB, t, rfl⟩)⟩

/-- Claim 2.8. -/
theorem claim28 [Finite A] (T : TaylorDatum L) (hA : IsTaylorAlg T A)
    (hnp : ¬ HasProperAbsorbing L A) {m : ℕ} (v : L.Term (Fin m)) (n : ℕ) (hn : 0 < n)
    (hnA : n < Nat.card A)
    (hv : ∀ (b : A) (k : Fin m), ∃ B ⊆ W v b k, IsSubuniverse L B ∧ n ≤ B.ncard) :
    ∀ (b : A) (i : Fin (T.k * m)), n + 1 ≤ (W (star T.t v) b i).ncard := by
  intro b i
  obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨B, hBv, hBsub, hBn⟩ := hv b k
  have hBW : B ⊆ W (star T.t v) b (finProdFinEquiv (j, k)) := by
    intro c hc
    have := mem_W_star hA.1 T.t v b j k (fun _ => c) (hBv hc)
    rwa [realize_const hA.1] at this
  by_cases hBu : B = Set.univ
  · subst hBu
    have : W (star T.t v) b (finProdFinEquiv (j, k)) = Set.univ := Set.eq_univ_of_univ_subset hBW
    rw [this, Set.ncard_univ]; omega
  have hBne : B.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have hnabs : ¬ IsAbsorbing L B := fun habs => hnp ⟨B, habs, hBne, hBu⟩
  let r : L.Term (Fin 2) := T.t.subst (fun l => var (cond (T.σ j l) 1 0))
  have hr : ¬ ∀ (k' : Fin 2) (a : Fin 2 → A), (∀ i, i ≠ k' → a i ∈ B) → r.realize a ∈ B :=
    fun h => hnabs ⟨hBsub, 2, r, two_pos, h⟩
  push_neg at hr
  obtain ⟨k', a, ha, he⟩ := hr
  have hcond : ∀ β : Bool, a (cond β 1 0) = cond β (a 1) (a 0) := by
    intro β; cases β <;> rfl
  have hr1 : r.realize a = T.t.realize (fun l => cond (T.σ j l) (a 1) (a 0)) := by
    simp only [r, Term.realize_subst, Term.realize_var, hcond]
  have hr2 : r.realize a = T.t.realize (fun l => cond (T.τ j l) (a 1) (a 0)) := by
    rw [hr1]; exact hA.2 j (a 0) (a 1)
  have heW : r.realize a ∈ W (star T.t v) b (finProdFinEquiv (j, k)) := by
    by_cases hk' : k' = 0
    · have h1 : a 1 ∈ B := ha 1 (by rw [hk']; decide)
      rw [hr2]
      apply mem_W_star hA.1
      simp only [T.τ_self, cond_true]
      exact hBv h1
    · have h0 : a 0 ∈ B := ha 0 (fun h => hk' h.symm)
      rw [hr1]
      apply mem_W_star hA.1
      simp only [T.σ_self, cond_false]
      exact hBv h0
  have hsub : insert (r.realize a) B ⊆ W (star T.t v) b (finProdFinEquiv (j, k)) :=
    Set.insert_subset heW hBW
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem he (Set.toFinite _)] at this
  omega

/-- Claim 2.9. -/
theorem claim29 (hid : IsIdempotent L A) {ms : ℕ} (s : L.Term (Fin ms))
    (hs : ∀ B : Set A, B.Nonempty → ∀ t : L.Term B, Handles s (B, t.realize Subtype.val))
    {m : ℕ} (w : L.Term (Fin m)) (b : A) (i : Fin (ms * m)) :
    ∃ S ⊆ W (star s w) b i, IsSubuniverse L S ∧ W w b (finProdFinEquiv.symm i).2 ⊆ S := by
  obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective i
  simp only [Equiv.symm_apply_apply]
  refine ⟨{c | ∃ t : L.Term (W w b k), t.realize Subtype.val = c}, ?_, ?_, ?_⟩
  · rintro c ⟨t, rfl⟩
    obtain ⟨a, ha, hr⟩ := hs _ ⟨b, self_mem_W hid w b k⟩ t
    have hr' : s.realize a = t.realize Subtype.val := hr
    rw [← hr']
    exact mem_W_star hid s w b j k a (ha j)
  · intro l f x hx
    choose t ht using hx
    exact ⟨func f t, by simp only [Term.realize, ht]⟩
  · intro c hc
    exact ⟨var ⟨c, hc⟩, rfl⟩

theorem p27_main [Finite A] (T : TaylorDatum L) (hA : IsTaylorAlg T A)
    (hnp : ¬ HasProperAbsorbing L A) :
    ∃ (n : ℕ) (v : L.Term (Fin n)), 0 < n ∧
      ∀ (b c : A) (i : Fin n), ∃ a : Fin n → A, a i = b ∧ v.realize a = c := by
  have hid := hA.1
  by_cases hsub : Subsingleton A
  · refine ⟨1, var 0, one_pos, fun b c i => ⟨fun _ => b, rfl, ?_⟩⟩
    exact Subsingleton.elim _ _
  obtain ⟨x, y, hxy⟩ := (not_subsingleton_iff_nontrivial.1 hsub).exists_pair_ne
  have hcard : 1 ≤ Nat.card A := by
    have : Nonempty A := ⟨x⟩
    exact Nat.card_pos
  have hk : 0 < T.k := by
    rcases Nat.eq_zero_or_pos T.k with h | h
    · exfalso
      have hfun : (fun _ : Fin T.k => x) = fun _ => y :=
        funext fun i => absurd i.2 (by omega)
      apply hxy
      rw [← realize_const hid T.t x, hfun, realize_const hid T.t y]
    · exact h
  obtain ⟨ms, s, hms, hs⟩ := lemma26 hid
  have inv : ∀ n, 1 ≤ n → n ≤ Nat.card A → ∃ (m : ℕ) (v : L.Term (Fin m)), 0 < m ∧
      ∀ (b : A) (k : Fin m), ∃ B ⊆ W v b k, IsSubuniverse L B ∧ n ≤ B.ncard := by
    intro n hn1
    induction n, hn1 using Nat.le_induction with
    | base =>
      intro _
      refine ⟨1, var 0, one_pos, fun b k => ⟨{b}, ?_, ?_, by simp⟩⟩
      · intro c hc
        rw [Set.mem_singleton_iff.1 hc]
        exact self_mem_W hid _ b k
      · intro l f x hx
        have : x = fun _ => b := funext fun i => Set.mem_singleton_iff.1 (hx i)
        rw [this]
        exact Set.mem_singleton_iff.2 (hid l f b)
    | succ n hn ih =>
      intro hnA
      obtain ⟨m, v, hm, hv⟩ := ih (by omega)
      refine ⟨ms * (T.k * m), star s (star T.t v), Nat.mul_pos hms (Nat.mul_pos hk hm),
        fun b i => ?_⟩
      obtain ⟨S, hSW, hSsub, hBS⟩ := claim29 hid s hs (star T.t v) b i
      refine ⟨S, hSW, hSsub, ?_⟩
      have h28 := claim28 T hA hnp v n (by omega) (by omega) hv b (finProdFinEquiv.symm i).2
      exact h28.trans (Set.ncard_le_ncard hBS (Set.toFinite _))
  obtain ⟨m, v, hm, hv⟩ := inv (Nat.card A) hcard le_rfl
  refine ⟨m, v, hm, fun b c i => ?_⟩
  obtain ⟨B, hBW, -, hBn⟩ := hv b i
  have hBu : B = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ B) (by rw [Set.ncard_univ]; exact hBn)
  exact hBW (hBu ▸ Set.mem_univ c)

end P27

end BKAbsorption

open BKAbsorption

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] {A : Type w₁}
    [L.Structure A] [Finite A] (T : TaylorDatum L) (hA : IsTaylorAlg T A)
    (hnp : ¬ HasProperAbsorbing L A) :
    ∃ (n : ℕ) (v : L.Term (Fin n)), 0 < n ∧
      ∀ (b c : A) (i : Fin n), ∃ a : Fin n → A, a i = b ∧ v.realize a = c :=
  P27.p27_main T hA hnp
