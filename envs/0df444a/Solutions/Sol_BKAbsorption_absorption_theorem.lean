-- Prove2me | solution 1 for BKAbsorption.absorption_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T17:16:30.916416+00:00
-- url     : https://prove2.me/submissions/e228519a-5e4a-4837-98ef-dc5e34212ac7

import Definitions.Def_BKAbsorption_defs
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
Barto–Kozik, Theorem 2.11 (Absorption Theorem).  Section `P27` repeats the proof of
Proposition 2.7 (accepted separately as `BKAbsorption.absorption_free_term`); section `P211`
follows the paper's proof of Theorem 2.11 (Claims 2.12, 2.13).
-/

universe u₁ v₁ w₁ w₂

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

namespace P211

open P27

variable {L : FirstOrder.Language.{u₁, v₁}}

section general

variable {M : Type*} [L.Structure M]

theorem realize_mem {S : Set M} (hS : IsSubuniverse L S) {α : Type*} (t : L.Term α)
    (a : α → M) (ha : ∀ i, a i ∈ S) : t.realize a ∈ S := by
  induction t with
  | var i => exact ha i
  | func f ts ih => exact hS _ f _ ih

end general

variable {A : Type w₁} {B : Type w₂} [L.Structure A] [L.Structure B]

theorem realize_prod {α : Type*} (t : L.Term α) (x : α → A × B) :
    t.realize x = (t.realize (fun i => (x i).1), t.realize (fun i => (x i).2)) := by
  induction t with
  | var => rfl
  | func f ts ih =>
    simp only [Term.realize]
    rw [show (fun i => (ts i).realize x) = fun i =>
      ((ts i).realize (fun i => (x i).1), (ts i).realize (fun i => (x i).2)) from funext ih]
    rfl

theorem rel_closed {R : Set (A × B)} (hR : IsSubuniverse L R) {α : Type*} (t : L.Term α)
    (a : α → A) (b : α → B) (h : ∀ i, (a i, b i) ∈ R) : (t.realize a, t.realize b) ∈ R := by
  have := realize_mem hR t (fun i => (a i, b i)) h
  rwa [realize_prod] at this

theorem rel_closed_fun {R : Set (A × B)} (hR : IsSubuniverse L R) {l : ℕ} (f : L.Functions l)
    (a : Fin l → A) (b : Fin l → B) (h : ∀ i, (a i, b i) ∈ R) : (funMap f a, funMap f b) ∈ R :=
  hR _ f (fun i => (a i, b i)) h

/-- The core of the proof of Theorem 2.11: the case `R⁻¹ ∘ R = A × A`. -/
theorem core [Finite A] (hidA : IsIdempotent L A) (hidB : IsIdempotent L B) {n : ℕ}
    (v : L.Term (Fin n)) (hn : 0 < n)
    (hv : ∀ (b c : A) (i : Fin n), ∃ a : Fin n → A, a i = b ∧ v.realize a = c)
    (hnpA : ¬ HasProperAbsorbing L A) (hnpB : ¬ HasProperAbsorbing L B)
    (R : Set (A × B)) (hR : IsSubuniverse L R) (hsnd : ∀ b, ∃ a, (a, b) ∈ R)
    (hRR : ∀ a c, ∃ b, (a, b) ∈ R ∧ (c, b) ∈ R) : ∀ a b, (a, b) ∈ R := by
  classical
  by_cases hAe : IsEmpty A
  · intro a; exact (hAe.false a).elim
  obtain ⟨a0⟩ := not_isEmpty_iff.1 hAe
  -- `N X` and good sets
  let N : Set A → Set B := fun X => {b | ∀ a ∈ X, (a, b) ∈ R}
  let good : Set A → Prop := fun X => ∀ c, ∃ f ∈ N X, (c, f) ∈ R
  let Sg : Set A → Set A := fun X => {c | ∃ t : L.Term X, t.realize Subtype.val = c}
  have hSgsub : ∀ X, IsSubuniverse L (Sg X) := by
    intro X l f x hx
    choose t ht using hx
    exact ⟨func f t, by simp only [Term.realize, ht]⟩
  have hXSg : ∀ X, X ⊆ Sg X := fun X c hc => ⟨var ⟨c, hc⟩, rfl⟩
  -- Claim 2.12
  have hN212 : ∀ X, N X ⊆ N (Sg X) := by
    rintro X b hb c ⟨t, rfl⟩
    have := rel_closed hR t Subtype.val (fun _ => b) (fun i => hb _ i.2)
    rwa [realize_const hidB] at this
  -- N S is closed under v-applications
  have hNv : ∀ S : Set A, ∀ e : Fin n → B, (∀ i, e i ∈ N S) → v.realize e ∈ N S := by
    intro S e he s hs
    have := rel_closed hR v (fun _ => s) e (fun i => he i s hs)
    rwa [realize_const hidA] at this
  -- step: a good nonempty proper subuniverse can be extended
  have hstep : ∀ S : Set A, IsSubuniverse L S → S.Nonempty → S ≠ Set.univ → good S →
      ∃ b ∉ S, good (insert b S) := by
    intro S hS hSne hSu hgood
    have hnabs : ¬ IsAbsorbing L S := fun habs => hnpA ⟨S, habs, hSne, hSu⟩
    have : ¬ ∀ (j : Fin n) (a : Fin n → A), (∀ i, i ≠ j → a i ∈ S) → v.realize a ∈ S :=
      fun h => hnabs ⟨hS, n, v, hn, h⟩
    push_neg at this
    obtain ⟨j, a, ha, hb⟩ := this
    refine ⟨v.realize a, hb, fun c => ?_⟩
    obtain ⟨d, hdj, hdc⟩ := hv (a j) c j
    choose e he hde using fun i => hgood (d i)
    refine ⟨v.realize e, ?_, ?_⟩
    · intro x hx
      rcases hx with rfl | hx
      · apply rel_closed hR v a e
        intro i
        by_cases hij : i = j
        · subst hij; rw [← hdj]; exact hde i
        · exact he i (a i) (ha i hij)
      · exact hNv S e he x hx
    · rw [← hdc]; exact rel_closed hR v d e hde
  -- Claim 2.13: `N A` is nonempty, via growing good sets
  have hgrow : ∀ m, 1 ≤ m → m ≤ Nat.card A → ∃ X, good X ∧ m ≤ X.ncard := by
    intro m hm1
    induction m, hm1 using Nat.le_induction with
    | base =>
      intro _
      refine ⟨{a0}, fun c => ?_, by simp⟩
      obtain ⟨b, h1, h2⟩ := hRR a0 c
      exact ⟨b, fun a ha => (Set.mem_singleton_iff.1 ha) ▸ h1, h2⟩
    | succ m hm ih =>
      intro hmA
      obtain ⟨X, hX, hXm⟩ := ih (by omega)
      have hgS : good (Sg X) := fun c => by
        obtain ⟨f, hf, hcf⟩ := hX c
        exact ⟨f, hN212 X hf, hcf⟩
      have hXS : X.ncard ≤ (Sg X).ncard := Set.ncard_le_ncard (hXSg X) (Set.toFinite _)
      by_cases hSu : Sg X = Set.univ
      · refine ⟨Sg X, hgS, ?_⟩
        rw [hSu, Set.ncard_univ]; exact hmA
      · have hSne : (Sg X).Nonempty := by
          apply Set.nonempty_of_ncard_ne_zero; omega
        obtain ⟨b, hb, hgb⟩ := hstep (Sg X) (hSgsub X) hSne hSu hgS
        refine ⟨insert b (Sg X), hgb, ?_⟩
        rw [Set.ncard_insert_of_notMem hb (Set.toFinite _)]
        omega
  have hcard : 1 ≤ Nat.card A := by
    have : Nonempty A := ⟨a0⟩
    exact Nat.card_pos
  obtain ⟨X, hX, hXc⟩ := hgrow (Nat.card A) hcard le_rfl
  have hXu : X = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ X) (by rw [Set.ncard_univ]; exact hXc)
  subst hXu
  -- final part: `N A = B`
  have hNne : (N Set.univ).Nonempty := by
    obtain ⟨f, hf, -⟩ := hX a0
    exact ⟨f, hf⟩
  have hNsub : IsSubuniverse L (N Set.univ) := by
    intro l f x hx a _
    have := rel_closed_fun hR f (fun _ => a) x (fun i => hx i a trivial)
    rwa [hidA] at this
  by_cases hNu : N Set.univ = Set.univ
  · intro a b
    have : b ∈ N Set.univ := hNu ▸ Set.mem_univ b
    exact this a trivial
  exfalso
  have hnabs : ¬ IsAbsorbing L (N Set.univ) := fun habs => hnpB ⟨_, habs, hNne, hNu⟩
  have : ¬ ∀ (j : Fin n) (b : Fin n → B), (∀ i, i ≠ j → b i ∈ N Set.univ) →
      v.realize b ∈ N Set.univ := fun h => hnabs ⟨hNsub, n, v, hn, h⟩
  push_neg at this
  obtain ⟨j, b, hb, hc⟩ := this
  apply hc
  intro d _
  obtain ⟨a, ha⟩ := hsnd (b j)
  obtain ⟨a', ha'j, ha'd⟩ := hv a d j
  rw [← ha'd]
  apply rel_closed hR v a' b
  intro i
  by_cases hij : i = j
  · subst hij; rw [ha'j]; exact ha
  · exact hb i hij (a' i) trivial

/-- Powers of the linking relation `R⁻¹ ∘ R` on `A`. -/
def SP (R : Set (A × B)) : ℕ → Set (A × A)
  | 0 => {p | p.1 = p.2}
  | k + 1 => {p | ∃ c, (p.1, c) ∈ SP R k ∧ LinkStep R c p.2}

theorem SP_join (R : Set (A × B)) (j : ℕ) : ∀ l (a b c : A), (a, b) ∈ SP R j →
    (b, c) ∈ SP R l → (a, c) ∈ SP R (j + l)
  | 0, a, b, c, hab, hbc => by
    have : b = c := hbc
    subst this; exact hab
  | l + 1, a, b, c, hab, ⟨c', hbc', hst⟩ => ⟨c', SP_join R j l a b c' hab hbc', hst⟩

theorem SP_split (R : Set (A × B)) (j : ℕ) : ∀ l (a c : A), (a, c) ∈ SP R (j + l) →
    ∃ b, (a, b) ∈ SP R j ∧ (b, c) ∈ SP R l
  | 0, a, c, h => ⟨c, h, rfl⟩
  | l + 1, a, c, ⟨c', h, hst⟩ => by
    obtain ⟨b, hab, hbc'⟩ := SP_split R j l a c' h
    exact ⟨b, hab, c', hbc', hst⟩

theorem SP_symm (R : Set (A × B)) : ∀ k (a c : A), (a, c) ∈ SP R k → (c, a) ∈ SP R k
  | 0, a, c, h => by
    have : a = c := h
    subst this; rfl
  | k + 1, a, c, ⟨c', h, b, h1, h2⟩ => by
    have h1' : (c, c') ∈ SP R 1 := ⟨c, rfl, b, h2, h1⟩
    have := SP_join R 1 k c c' a h1' (SP_symm R k a c' h)
    rwa [Nat.add_comm] at this

theorem SP_mono (R : Set (A × B)) (hfst : ∀ a, ∃ b, (a, b) ∈ R) : Monotone (SP R) := by
  apply monotone_nat_of_le_succ
  intro k p hp
  obtain ⟨b, hb⟩ := hfst p.2
  exact ⟨p.2, hp, b, hb, hb⟩

theorem SP_sub (hidA : IsIdempotent L A) (R : Set (A × B)) (hR : IsSubuniverse L R) :
    ∀ k, IsSubuniverse L (SP R k)
  | 0 => by
    intro l f x hx
    show funMap f (fun i => (x i).1) = funMap f (fun i => (x i).2)
    congr 1
    funext i
    exact hx i
  | k + 1 => by
    intro l f x hx
    choose c hc b hb1 hb2 using hx
    refine ⟨funMap f c, ?_, funMap f b, rel_closed_fun hR f c b hb1, rel_closed_fun hR f _ b hb2⟩
    exact SP_sub hidA R hR k _ f (fun i => ((x i).1, c i)) hc

theorem p211_main [Finite A] [Finite B] (T : TaylorDatum L) (hA : IsTaylorAlg T A)
    (hB : IsTaylorAlg T B) (R : L.Substructure (A × B)) (hsd : Subdirect (R : Set (A × B)))
    (hlk : Linked (R : Set (A × B))) (hpr : (R : Set (A × B)) ≠ Set.univ) :
    HasProperAbsorbing L A ∨ HasProperAbsorbing L B := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnpA, hnpB⟩ := hcon
  obtain ⟨n, v, hn, hv⟩ := p27_main T hA hnpA
  set R' : Set (A × B) := (R : Set (A × B)) with hR'def
  have hR : IsSubuniverse L R' := fun _ f x hx => R.fun_mem f x hx
  have hfst : ∀ a, ∃ b, (a, b) ∈ R' := by
    intro a
    have : a ∈ Prod.fst '' R' := by rw [hsd.1]; trivial
    obtain ⟨p, hp, rfl⟩ := this
    exact ⟨p.2, hp⟩
  have hsnd : ∀ b, ∃ a, (a, b) ∈ R' := by
    intro b
    have : b ∈ Prod.snd '' R' := by rw [hsd.2]; trivial
    obtain ⟨p, hp, rfl⟩ := this
    exact ⟨p.1, hp⟩
  have hmono := SP_mono R' hfst
  -- linkedness gives a power equal to `A × A`
  have hreach : ∀ p : A × A, ∃ k, p ∈ SP R' k := by
    rintro ⟨a, a'⟩
    have hrt := hlk a a' (by obtain ⟨b, hb⟩ := hfst a; exact ⟨_, hb, rfl⟩)
      (by obtain ⟨b, hb⟩ := hfst a'; exact ⟨_, hb, rfl⟩)
    induction hrt with
    | refl => exact ⟨0, rfl⟩
    | tail _ hst ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, _, hk, hst⟩
  have : Fintype (A × A) := Fintype.ofFinite _
  choose kf hkf using hreach
  have hK : ∃ k, SP R' (k + 1) = Set.univ := by
    refine ⟨Finset.univ.sup kf, Set.eq_univ_of_forall fun p => ?_⟩
    exact hmono (Nat.le_succ_of_le (Finset.le_sup (Finset.mem_univ p))) (hkf p)
  rcases hk0 : Nat.find hK with _ | j
  · -- `R⁻¹ ∘ R = A × A`
    have h1 : SP R' 1 = Set.univ := by
      have := Nat.find_spec hK; rwa [hk0] at this
    apply hpr
    refine Set.eq_univ_of_forall fun p => ?_
    refine core hA.1 hB.1 v hn hv hnpA hnpB R' hR hsnd ?_ p.1 p.2
    intro a c
    have : (a, c) ∈ SP R' 1 := h1 ▸ Set.mem_univ _
    obtain ⟨c', hc', b, hb1, hb2⟩ := this
    have : a = c' := hc'
    subst this
    exact ⟨b, hb1, hb2⟩
  · -- replace `R` by the power `SP R' (j + 1)`
    have hspec : SP R' (j + 2) = Set.univ := by
      have := Nat.find_spec hK; rwa [hk0] at this
    have hmin : SP R' (j + 1) ≠ Set.univ := by
      have := Nat.find_min hK (m := j) (by omega)
      exact this
    apply hmin
    refine Set.eq_univ_of_forall fun p => ?_
    refine core (B := A) hA.1 hA.1 v hn hv hnpA hnpA (SP R' (j + 1)) (SP_sub hA.1 R' hR (j + 1))
      (fun b => ⟨b, hmono (Nat.zero_le _) (show (b, b) ∈ SP R' 0 from rfl)⟩) ?_ p.1 p.2
    intro a c
    have hac : (a, c) ∈ SP R' ((j + 1) + (j + 1)) :=
      hmono (by omega) (hspec ▸ Set.mem_univ (a, c))
    obtain ⟨b, hab, hbc⟩ := SP_split R' (j + 1) (j + 1) a c hac
    exact ⟨b, hab, SP_symm R' _ b c hbc⟩

end P211

end BKAbsorption

open BKAbsorption

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] {A : Type w₁} {B : Type w₂}
    [L.Structure A] [L.Structure B] [Finite A] [Finite B] (T : TaylorDatum L)
    (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B) (R : L.Substructure (A × B))
    (hsd : Subdirect (R : Set (A × B))) (hlk : Linked (R : Set (A × B)))
    (hpr : (R : Set (A × B)) ≠ Set.univ) :
    HasProperAbsorbing L A ∨ HasProperAbsorbing L B :=
  P211.p211_main T hA hB R hsd hlk hpr
