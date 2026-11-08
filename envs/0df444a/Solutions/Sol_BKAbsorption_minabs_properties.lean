-- Prove2me | solution 1 for BKAbsorption.minabs_properties
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T17:32:42.043332+00:00
-- url     : https://prove2.me/submissions/f52d5f2b-a7b8-4123-a038-f9b07d0c142c

import Definitions.Def_BKAbsorption_defs
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
Barto–Kozik, Proposition 2.15. Sections P27, P211 repeat the accepted proofs of Prop 2.7 and
Thm 2.11; section P215 proves Prop 2.4, Lemma 2.5 and Prop 2.15 (Thm 2.11 is applied to the
subalgebras C, D in key_full).
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

namespace P215

open P27 P211

variable {L : FirstOrder.Language.{u₁, v₁}}

section general

variable {M : Type*} {N : Type*} [L.Structure M] [L.Structure N]

variable (L) in
/-- `X` is a subuniverse absorbing the subset `S` (relative absorption, `X ⊴ S`). -/
def RelAbs (X S : Set M) : Prop :=
  IsSubuniverse L X ∧ ∃ (n : ℕ) (t : L.Term (Fin n)), 0 < n ∧
    ∀ (k : Fin n) (a : Fin n → M), (∀ i, a i ∈ S) → (∀ i, i ≠ k → a i ∈ X) → t.realize a ∈ X

theorem relAbs_univ {X : Set M} : RelAbs L X Set.univ ↔ IsAbsorbing L X := by
  constructor
  · rintro ⟨hX, n, t, hn, ht⟩
    exact ⟨hX, n, t, hn, fun k a ha => ht k a (fun _ => trivial) ha⟩
  · rintro ⟨hX, n, t, hn, ht⟩
    exact ⟨hX, n, t, hn, fun k a _ ha => ht k a ha⟩

/-- Proposition 2.4 (transitivity of absorption), relative form, via the star composition. -/
theorem relAbs_trans {X Y S : Set M} (hXY : X ⊆ Y) (hX : RelAbs L X Y) (hY : RelAbs L Y S) :
    RelAbs L X S := by
  obtain ⟨hXs, n, s, hn, hs⟩ := hX
  obtain ⟨-, m, t, hm, ht⟩ := hY
  refine ⟨hXs, n * m, star s t, Nat.mul_pos hn hm, fun k a ha hak => ?_⟩
  rw [realize_star]
  have hk : ∀ j l, finProdFinEquiv (j, l) = k →
      j = (finProdFinEquiv.symm k).1 ∧ l = (finProdFinEquiv.symm k).2 := by
    intro j l h
    rw [← h, Equiv.symm_apply_apply]
    exact ⟨rfl, rfl⟩
  apply hs (finProdFinEquiv.symm k).1
  · intro j
    by_cases hj : j = (finProdFinEquiv.symm k).1
    · apply ht (finProdFinEquiv.symm k).2
      · intro l; exact ha _
      · intro l hl; apply hXY; apply hak; intro h; exact hl (hk _ _ h).2
    · apply hXY
      apply realize_mem hXs
      intro l; apply hak; intro h; exact hj (hk _ _ h).1
  · intro j hj
    apply realize_mem hXs
    intro l; apply hak; intro h; exact hj (hk _ _ h).1

theorem relAbs_inter {Y S : Set M} (hY : IsAbsorbing L Y) (hS : IsSubuniverse L S) :
    RelAbs L (Y ∩ S) S := by
  obtain ⟨hYs, n, t, hn, ht⟩ := hY
  exact ⟨fun l f x hx => ⟨hYs l f x (fun i => (hx i).1), hS l f x (fun i => (hx i).2)⟩, n, t, hn,
    fun k a ha hak => ⟨ht k a (fun i hi => (hak i hi).1), realize_mem hS t a ha⟩⟩

/-- Proposition 2.4 (intersection of absorbing subuniverses). -/
theorem absorbing_inter {B C : Set M} (hB : IsAbsorbing L B) (hC : IsAbsorbing L C) :
    IsAbsorbing L (B ∩ C) := by
  have h1 : RelAbs L (C ∩ B) B := relAbs_inter hC hB.1
  have h2 : RelAbs L B Set.univ := relAbs_univ.2 hB
  rw [Set.inter_comm]
  exact relAbs_univ.1 (relAbs_trans Set.inter_subset_right h1 h2)

theorem realize_hom (φ : M → N) (hφ : ∀ (n : ℕ) (f : L.Functions n) (x : Fin n → M),
    φ (funMap f x) = funMap f (φ ∘ x)) {α : Type*} (t : L.Term α) (a : α → M) :
    φ (t.realize a) = t.realize (φ ∘ a) := by
  induction t with
  | var => rfl
  | func f ts ih =>
    simp only [Term.realize]
    rw [hφ]
    congr 1
    funext i
    exact ih i

/-- The image of a relatively absorbing set under a homomorphism onto `N` absorbs `N`. -/
theorem image_absorbing (φ : M → N) (hφ : ∀ (n : ℕ) (f : L.Functions n) (x : Fin n → M),
    φ (funMap f x) = funMap f (φ ∘ x)) {X S : Set M} (hXS : X ⊆ S) (hX : RelAbs L X S)
    (hS : φ '' S = Set.univ) : IsAbsorbing L (φ '' X) := by
  obtain ⟨hXs, n, t, hn, ht⟩ := hX
  refine ⟨?_, n, t, hn, ?_⟩
  · intro l f y hy
    have hy' : ∀ i, ∃ m, m ∈ X ∧ φ m = y i := hy
    choose x hx hxy using hy'
    refine ⟨funMap f x, hXs l f x hx, ?_⟩
    rw [hφ]; congr 1; funext i; exact hxy i
  · intro k y hy
    have : ∀ i, ∃ m, m ∈ S ∧ (i ≠ k → m ∈ X) ∧ φ m = y i := by
      intro i
      by_cases hi : i = k
      · have hyS : y i ∈ φ '' S := by rw [hS]; exact Set.mem_univ _
        obtain ⟨m, hm, hmy⟩ := hyS
        exact ⟨m, hm, fun h => absurd hi h, hmy⟩
      · obtain ⟨m, hm, hmy⟩ := hy i hi
        exact ⟨m, hXS hm, fun _ => hm, hmy⟩
    choose x hxS hxX hxy using this
    refine ⟨t.realize x, ht k x hxS hxX, ?_⟩
    rw [realize_hom φ hφ]; congr 1; funext i; exact hxy i

theorem exists_minabs_aux [Finite M] (n : ℕ) : ∀ (X : Set M), X.ncard = n → X.Nonempty →
    IsAbsorbing L X → ∃ D ⊆ X, MinAbsorbing L D := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hn hne hX
  by_cases hmin : MinAbsorbing L X
  · exact ⟨X, subset_rfl, hmin⟩
  · have : ∃ Y : Set M, Y.Nonempty ∧ Y ⊆ X ∧ IsAbsorbing L Y ∧ Y ≠ X := by
      by_contra hcon
      push_neg at hcon
      exact hmin ⟨hne, hX, fun C h1 h2 h3 => hcon C h1 h2 h3⟩
    obtain ⟨Y, hY1, hY2, hY3, hY4⟩ := this
    have hlt : Y.ncard < n := hn ▸ Set.ncard_lt_ncard (lt_of_le_of_ne hY2 hY4)
    obtain ⟨D, hD, hDm⟩ := ih _ hlt Y rfl hY1 hY3
    exact ⟨D, hD.trans hY2, hDm⟩

/-- Every nonempty absorbing subuniverse of a finite algebra contains a minimal one. -/
theorem exists_minabs [Finite M] (X : Set M) (hne : X.Nonempty) (hX : IsAbsorbing L X) :
    ∃ D ⊆ X, MinAbsorbing L D :=
  exists_minabs_aux _ X rfl hne hX

/-! ### Subalgebras -/

theorem coe_realize_sub (S : L.Substructure M) {α : Type*} (t : L.Term α) (a : α → S) :
    ((t.realize a : S) : M) = t.realize (fun i => (a i : M)) :=
  realize_hom (L := L) Subtype.val (fun _ _ _ => rfl) t a

theorem relAbs_of_absorbing_sub (S : L.Substructure M) {X : Set S} (hX : IsAbsorbing L X) :
    RelAbs L (Subtype.val '' X) (S : Set M) := by
  obtain ⟨hXs, n, t, hn, ht⟩ := hX
  refine ⟨?_, n, t, hn, ?_⟩
  · intro l f x hx
    have hx' : ∀ i, ∃ y : S, y ∈ X ∧ (y : M) = x i := hx
    choose y hy hyx using hx'
    refine ⟨funMap f y, hXs l f y hy, ?_⟩
    show funMap f (fun i => (y i : M)) = funMap f x
    congr 1; funext i; exact hyx i
  · intro k a ha hak
    refine ⟨t.realize (fun i => ⟨a i, ha i⟩), ht k _ ?_, ?_⟩
    · intro i hi
      obtain ⟨y, hy, hya⟩ := hak i hi
      have : y = ⟨a i, ha i⟩ := Subtype.ext hya
      exact this ▸ hy
    · exact coe_realize_sub S t _

theorem absorbing_sub_of_relAbs (S : L.Substructure M) {X : Set S}
    (hX : RelAbs L (Subtype.val '' X) (S : Set M)) : IsAbsorbing L X := by
  obtain ⟨hXs, n, t, hn, ht⟩ := hX
  refine ⟨?_, n, t, hn, ?_⟩
  · intro l f y hy
    obtain ⟨z, hz, hzy⟩ := hXs l f (fun i => (y i : M)) (fun i => ⟨y i, hy i, rfl⟩)
    have : z = funMap f y := Subtype.ext hzy
    exact this ▸ hz
  · intro k a hak
    obtain ⟨z, hz, hzy⟩ := ht k (fun i => (a i : M)) (fun i => (a i).2)
      (fun i hi => ⟨a i, hak i hi, rfl⟩)
    have : z = t.realize a := Subtype.ext (hzy.trans (coe_realize_sub S t a).symm)
    exact this ▸ hz

theorem taylor_sub {T : TaylorDatum L} (hM : IsTaylorAlg T M) (S : L.Substructure M) :
    IsTaylorAlg T S := by
  refine ⟨fun n f a => Subtype.ext (hM.1 n f (a : M)), fun j x y => Subtype.ext ?_⟩
  rw [coe_realize_sub, coe_realize_sub]
  have e : ∀ b : Bool, ((cond b y x : S) : M) = cond b (y : M) (x : M) := by
    intro b; cases b <;> rfl
  simp only [e]
  exact hM.2 j x y

/-- A subuniverse viewed as a substructure. -/
def subOf {C : Set M} (hC : IsSubuniverse L C) : L.Substructure M where
  carrier := C
  fun_mem := fun {_} f x hx => hC _ f x hx

/-- A minimal absorbing subalgebra has no proper absorbing subalgebra (uses Prop 2.4). -/
theorem not_proper_minabs {C : Set M} (hC : MinAbsorbing L C) :
    ¬ HasProperAbsorbing L (subOf hC.2.1.1) := by
  rintro ⟨X, hX, hne, hnu⟩
  have h1 : RelAbs L (Subtype.val '' X) C := relAbs_of_absorbing_sub (subOf hC.2.1.1) hX
  have h2 : RelAbs L C Set.univ := relAbs_univ.2 hC.2.1
  have hsub : Subtype.val '' X ⊆ C := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have h3 := relAbs_univ.1 (relAbs_trans hsub h1 h2)
  have heq := hC.2.2 _ (hne.image _) hsub h3
  apply hnu
  ext y
  simp only [Set.mem_univ, iff_true]
  have : (y : M) ∈ Subtype.val '' X := by rw [heq]; exact y.2
  obtain ⟨z, hz, hzy⟩ := this
  exact (Subtype.ext hzy : z = y) ▸ hz

end general

/-! ### Products and neighbourhoods (Lemma 2.5) -/

section prod

variable {A : Type*} {B : Type*} [L.Structure A] [L.Structure B]

theorem absorbing_prod_left {C : Set A} (hC : IsAbsorbing L C) :
    IsAbsorbing L (C ×ˢ (Set.univ : Set B)) := by
  obtain ⟨hCs, n, t, hn, ht⟩ := hC
  refine ⟨fun l f x hx => ⟨hCs l f (fun i => (x i).1) (fun i => (hx i).1), trivial⟩, n, t, hn,
    fun k a ha => ?_⟩
  rw [realize_prod]
  exact ⟨ht k _ (fun i hi => (ha i hi).1), trivial⟩

theorem absorbing_prod_right {D : Set B} (hD : IsAbsorbing L D) :
    IsAbsorbing L ((Set.univ : Set A) ×ˢ D) := by
  obtain ⟨hDs, n, t, hn, ht⟩ := hD
  refine ⟨fun l f x hx => ⟨trivial, hDs l f (fun i => (x i).2) (fun i => (hx i).2)⟩, n, t, hn,
    fun k a ha => ?_⟩
  rw [realize_prod]
  exact ⟨trivial, ht k _ (fun i hi => (ha i hi).2)⟩

theorem absorbing_prod {C : Set A} {D : Set B} (hC : IsAbsorbing L C) (hD : IsAbsorbing L D) :
    IsAbsorbing L (C ×ˢ D) := by
  have h := absorbing_inter (absorbing_prod_left (B := B) hC) (absorbing_prod_right (A := A) hD)
  convert h using 1
  ext ⟨a, b⟩
  simp only [Set.mem_prod, Set.mem_inter_iff, Set.mem_univ, and_true, true_and]

/-- `X⁺` (neighbours in `B`). -/
def nbrR (R : Set (A × B)) (X : Set A) : Set B := {b | ∃ a ∈ X, (a, b) ∈ R}

/-- `Y⁻` (neighbours in `A`). -/
def nbrL (R : Set (A × B)) (Y : Set B) : Set A := {a | ∃ b ∈ Y, (a, b) ∈ R}

/-- Lemma 2.5: `X⁺ ⊴ B` when `X ⊴ A` and `R` projects onto `B`. -/
theorem nbrR_absorbing {R : Set (A × B)} (hR : IsSubuniverse L R)
    (hsnd : Prod.snd '' R = Set.univ) {X : Set A} (hX : IsAbsorbing L X) :
    IsAbsorbing L (nbrR R X) := by
  have h := image_absorbing (L := L) Prod.snd (fun _ _ _ => rfl) Set.inter_subset_right
    (relAbs_inter (absorbing_prod_left (B := B) hX) hR) hsnd
  convert h using 1
  ext b
  constructor
  · rintro ⟨a, ha, hab⟩; exact ⟨(a, b), ⟨⟨ha, trivial⟩, hab⟩, rfl⟩
  · rintro ⟨⟨a, b'⟩, ⟨⟨ha, -⟩, hab⟩, rfl⟩; exact ⟨a, ha, hab⟩

/-- Lemma 2.5: `Y⁻ ⊴ A` when `Y ⊴ B` and `R` projects onto `A`. -/
theorem nbrL_absorbing {R : Set (A × B)} (hR : IsSubuniverse L R)
    (hfst : Prod.fst '' R = Set.univ) {Y : Set B} (hY : IsAbsorbing L Y) :
    IsAbsorbing L (nbrL R Y) := by
  have h := image_absorbing (L := L) Prod.fst (fun _ _ _ => rfl) Set.inter_subset_right
    (relAbs_inter (absorbing_prod_right (A := A) hY) hR) hfst
  convert h using 1
  ext a
  constructor
  · rintro ⟨b, hb, hab⟩; exact ⟨(a, b), ⟨⟨trivial, hb⟩, hab⟩, rfl⟩
  · rintro ⟨⟨a', b⟩, ⟨⟨-, hb⟩, hab⟩, rfl⟩; exact ⟨b, hb, hab⟩

/-- Item (i), relative form: a relatively absorbing subset of a linked relation is linked. -/
theorem linked_of_relAbs (hidA : IsIdempotent L A) {R E : Set (A × B)} (hlk : Linked R)
    (hER : E ⊆ R) (hE : RelAbs L E R) : Linked E := by
  obtain ⟨-, n, t, hn, ht⟩ := hE
  intro a a' ha ha'
  obtain ⟨⟨a0, b⟩, hab, h0⟩ := ha
  obtain ⟨⟨a0', b'⟩, hab', h0'⟩ := ha'
  have e0 : a0 = a := h0
  have e0' : a0' = a' := h0'
  subst e0 e0'
  have hstep := hlk a0 a0' ⟨(a0, b), hER hab, rfl⟩ ⟨(a0', b'), hER hab', rfl⟩
  let gA : ℕ → A → Fin n → A := fun m x j =>
    if j.val < m then a0' else if j.val = m then x else a0
  let gB : ℕ → B → Fin n → B := fun m y j =>
    if j.val < m then b' else if j.val = m then y else b
  have hlink : ∀ m, m < n → ∀ x x', LinkStep R x x' →
      LinkStep E (t.realize (gA m x)) (t.realize (gA m x')) := by
    intro m hm
    have mem : ∀ x y, (x, y) ∈ R → (t.realize (gA m x), t.realize (gB m y)) ∈ E := by
      intro x y hxy
      have h := ht ⟨m, hm⟩ (fun j => (gA m x j, gB m y j)) ?_ ?_
      · rw [realize_prod] at h; exact h
      · intro j
        simp only [gA, gB]
        split_ifs
        · exact hER hab'
        · exact hxy
        · exact hER hab
      · intro j hj
        have hj' : j.val ≠ m := fun h => hj (Fin.ext h)
        simp only [gA, gB]
        split_ifs <;> first | exact hab' | exact hab | (exfalso; omega)
    rintro x x' ⟨y, hxy, hx'y⟩
    exact ⟨t.realize (gB m y), mem x y hxy, mem x' y hx'y⟩
  have hshift : ∀ m, gA m a0' = gA (m + 1) a0 := by
    intro m; funext j; simp only [gA]; split_ifs <;> first | rfl | omega
  have hall : ∀ m, m ≤ n → Relation.ReflTransGen (LinkStep E) a0 (t.realize (gA m a0)) := by
    intro m
    induction m with
    | zero =>
      intro _
      have h0 : gA 0 a0 = fun _ => a0 := by
        funext j; simp only [gA]; split_ifs <;> first | rfl | omega
      have e : t.realize (gA 0 a0) = a0 := by rw [h0]; exact realize_const hidA t a0
      rw [e]
    | succ m ih =>
      intro hm
      refine (ih (by omega)).trans ?_
      rw [← hshift m]
      exact Relation.ReflTransGen.lift (fun x => t.realize (gA m x)) (hlink m (by omega)) _ _ hstep
  have hfin : gA n a0 = fun _ => a0' := by
    funext j; simp only [gA]; split_ifs <;> first | rfl | omega
  have := hall n le_rfl
  rwa [hfin, realize_const hidA] at this

theorem linkAdj_symm {R : Set (A × B)} : ∀ x y, LinkAdj R x y → LinkAdj R y x
  | Sum.inl _, Sum.inr _, h => h
  | Sum.inr _, Sum.inl _, h => h
  | Sum.inl _, Sum.inl _, h => False.elim h
  | Sum.inr _, Sum.inr _, h => False.elim h

/-- Item (ii). -/
theorem part2 {R : Set (A × B)} (hR : IsSubuniverse L R) (hsd : Subdirect R)
    {C : Set A} {D : Set B} (hC : MinAbsorbing L C) (hD : MinAbsorbing L D)
    (hne : (C ×ˢ D ∩ R).Nonempty) :
    Prod.fst '' (C ×ˢ D ∩ R) = C ∧ Prod.snd '' (C ×ˢ D ∩ R) = D := by
  obtain ⟨⟨c0, d0⟩, ⟨hc0, hd0⟩, h0⟩ := hne
  constructor
  · apply Set.Subset.antisymm
    · rintro _ ⟨p, ⟨hp, -⟩, rfl⟩; exact hp.1
    · have habs := absorbing_inter (nbrL_absorbing hR hsd.1 hD.2.1) hC.2.1
      have heq := hC.2.2 (nbrL R D ∩ C) ⟨c0, ⟨d0, hd0, h0⟩, hc0⟩ Set.inter_subset_right habs
      intro c hc
      have hc2 := hc
      rw [← heq] at hc2
      obtain ⟨⟨b, hb, hcb⟩, -⟩ := hc2
      exact ⟨(c, b), ⟨⟨hc, hb⟩, hcb⟩, rfl⟩
  · apply Set.Subset.antisymm
    · rintro _ ⟨p, ⟨hp, -⟩, rfl⟩; exact hp.2
    · have habs := absorbing_inter (nbrR_absorbing hR hsd.2 hC.2.1) hD.2.1
      have heq := hD.2.2 (nbrR R C ∩ D) ⟨d0, ⟨c0, hc0, h0⟩, hd0⟩ Set.inter_subset_right habs
      intro d hd
      have hd2 := hd
      rw [← heq] at hd2
      obtain ⟨⟨a, ha, had⟩, -⟩ := hd2
      exact ⟨(a, d), ⟨⟨ha, hd⟩, had⟩, rfl⟩

end prod

/-! ### Theorem 2.11 inside `C × D` -/

section main

variable {A : Type w₁} {B : Type w₂} [L.Structure A] [L.Structure B]

/-- A linked subdirect subuniverse of `C × D` (`C ⊴⊴ A`, `D ⊴⊴ B`) is all of `C × D`
(Theorem 2.11 applied to the subalgebras `C`, `D`). -/
theorem key_full [Finite A] [Finite B] (T : TaylorDatum L) (hA : IsTaylorAlg T A)
    (hB : IsTaylorAlg T B) {C : Set A} {D : Set B} (hC : MinAbsorbing L C)
    (hD : MinAbsorbing L D) {F : Set (A × B)} (hF : IsSubuniverse L F) (hFCD : F ⊆ C ×ˢ D)
    (h1 : Prod.fst '' F = C) (h2 : Prod.snd '' F = D) (hlk : Linked F) : C ×ˢ D ⊆ F := by
  classical
  let C' := subOf hC.2.1.1
  let D' := subOf hD.2.1.1
  let F' : L.Substructure (C' × D') :=
    { carrier := {p | ((p.1 : A), (p.2 : B)) ∈ F}
      fun_mem := fun {l} f x hx => hF l f (fun i => (((x i).1 : A), ((x i).2 : B))) hx }
  by_contra hne
  have hpr : (F' : Set (C' × D')) ≠ Set.univ := by
    intro heq
    apply hne
    rintro ⟨c, d⟩ ⟨hc, hd⟩
    have : ((⟨c, hc⟩ : C'), (⟨d, hd⟩ : D')) ∈ (F' : Set (C' × D')) := by
      rw [heq]; exact Set.mem_univ _
    exact this
  have hsd : Subdirect (F' : Set (C' × D')) := by
    constructor
    · apply Set.eq_univ_of_forall
      intro c
      have : (c : A) ∈ Prod.fst '' F := by rw [h1]; exact c.2
      obtain ⟨⟨a, b⟩, hab, ha⟩ := this
      have ha' : a = (c : A) := ha
      subst ha'
      exact ⟨(c, ⟨b, (hFCD hab).2⟩), hab, rfl⟩
    · apply Set.eq_univ_of_forall
      intro d
      have : (d : B) ∈ Prod.snd '' F := by rw [h2]; exact d.2
      obtain ⟨⟨a, b⟩, hab, hb⟩ := this
      have hb' : b = (d : B) := hb
      subst hb'
      exact ⟨(⟨a, (hFCD hab).1⟩, d), hab, rfl⟩
  have hlk' : Linked (F' : Set (C' × D')) := by
    have key : ∀ a a', Relation.ReflTransGen (LinkStep F) a a' → ∀ (ha : a ∈ C) (ha' : a' ∈ C),
        Relation.ReflTransGen (LinkStep (F' : Set (C' × D'))) ⟨a, ha⟩ ⟨a', ha'⟩ := by
      intro a a' h
      induction h with
      | refl => intro _ _; exact Relation.ReflTransGen.refl
      | @tail b c _ hbc ih =>
        intro ha hc
        obtain ⟨d, hbd, hcd⟩ := hbc
        have hb : b ∈ C := (hFCD hbd).1
        have hd : d ∈ D := (hFCD hbd).2
        exact (ih ha hb).tail ⟨⟨d, hd⟩, hbd, hcd⟩
    intro c c' _ _
    have hc : (c : A) ∈ Prod.fst '' F := by rw [h1]; exact c.2
    have hc' : (c' : A) ∈ Prod.fst '' F := by rw [h1]; exact c'.2
    exact key _ _ (hlk _ _ hc hc') c.2 c'.2
  rcases p211_main T (taylor_sub hA C') (taylor_sub hB D') F' hsd hlk' hpr with h | h
  · exact not_proper_minabs hC h
  · exact not_proper_minabs hD h

variable [Finite A] [Finite B]

theorem full_of_relAbs (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    {R : Set (A × B)} (hsd : Subdirect R) (hlk : Linked R)
    {C : Set A} {D : Set B} (hC : MinAbsorbing L C) (hD : MinAbsorbing L D)
    {F : Set (A × B)} (hFR : F ⊆ R) (hFCD : F ⊆ C ×ˢ D) (hF : RelAbs L F R)
    (hne : F.Nonempty) : C ×ˢ D ⊆ F := by
  have h1 : Prod.fst '' F = C := hC.2.2 _ (hne.image _)
    (by rintro _ ⟨p, hp, rfl⟩; exact (hFCD hp).1)
    (image_absorbing Prod.fst (fun _ _ _ => rfl) hFR hF hsd.1)
  have h2 : Prod.snd '' F = D := hD.2.2 _ (hne.image _)
    (by rintro _ ⟨p, hp, rfl⟩; exact (hFCD hp).2)
    (image_absorbing Prod.snd (fun _ _ _ => rfl) hFR hF hsd.2)
  exact key_full T hA hB hC hD hF.1 hFCD h1 h2 (linked_of_relAbs hA.1 hlk hFR hF)

/-- Item (iii), first half: `C × D ⊆ R`. -/
theorem prod_sub (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    {R : Set (A × B)} (hR : IsSubuniverse L R) (hsd : Subdirect R) (hlk : Linked R)
    {C : Set A} {D : Set B} (hC : MinAbsorbing L C) (hD : MinAbsorbing L D)
    (hne : (C ×ˢ D ∩ R).Nonempty) : C ×ˢ D ⊆ R := by
  have h := full_of_relAbs T hA hB hsd hlk hC hD Set.inter_subset_right Set.inter_subset_left
    (relAbs_inter (absorbing_prod hC.2.1 hD.2.1) hR) hne
  exact fun p hp => (h hp).2

/-- Item (iv). -/
theorem part4 (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    {R : Set (A × B)} (hR : IsSubuniverse L R) (hsd : Subdirect R) (hlk : Linked R)
    {C : Set A} (hC : MinAbsorbing L C) : ∃ D : Set B, MinAbsorbing L D ∧ C ×ˢ D ⊆ R := by
  obtain ⟨c, hc⟩ := hC.1
  have : c ∈ Prod.fst '' R := by rw [hsd.1]; exact Set.mem_univ _
  obtain ⟨⟨a, b⟩, hab, ha⟩ := this
  have ha' : a = c := ha
  subst ha'
  obtain ⟨D, hDsub, hD⟩ :=
    exists_minabs (nbrR R C) ⟨b, a, hc, hab⟩ (nbrR_absorbing hR hsd.2 hC.2.1)
  obtain ⟨d, hd⟩ := hD.1
  obtain ⟨c', hc', hc'd⟩ := hDsub hd
  exact ⟨D, hD, prod_sub T hA hB hR hsd hlk hC hD ⟨(c', d), ⟨hc', hd⟩, hc'd⟩⟩

/-- Item (iv), the symmetric form for `D ⊴⊴ B`. -/
theorem part4' (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    {R : Set (A × B)} (hR : IsSubuniverse L R) (hsd : Subdirect R) (hlk : Linked R)
    {D : Set B} (hD : MinAbsorbing L D) : ∃ C : Set A, MinAbsorbing L C ∧ C ×ˢ D ⊆ R := by
  obtain ⟨d, hd⟩ := hD.1
  have : d ∈ Prod.snd '' R := by rw [hsd.2]; exact Set.mem_univ _
  obtain ⟨⟨a, b⟩, hab, hb⟩ := this
  have hb' : b = d := hb
  subst hb'
  obtain ⟨C, hCsub, hC⟩ :=
    exists_minabs (nbrL R D) ⟨a, b, hd, hab⟩ (nbrL_absorbing hR hsd.1 hD.2.1)
  obtain ⟨c, hc⟩ := hC.1
  obtain ⟨d', hd', hcd'⟩ := hCsub hc
  exact ⟨C, hC, prod_sub T hA hB hR hsd hlk hC hD ⟨(c, d'), ⟨hc, hd'⟩, hcd'⟩⟩

variable (L) in
/-- Adjacency inside minimal absorbing subuniverses. -/
def G (R : Set (A × B)) : A ⊕ B → A ⊕ B → Prop :=
  fun x y => LinkAdj R x y ∧ InMinAbs L x ∧ InMinAbs L y

theorem sameC (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    {R : Set (A × B)} (hR : IsSubuniverse L R) (hsd : Subdirect R) (hlk : Linked R)
    {C : Set A} (hC : MinAbsorbing L C) {c c' : A} (hc : c ∈ C) (hc' : c' ∈ C) :
    Relation.ReflTransGen (G L R) (Sum.inl c) (Sum.inl c') := by
  obtain ⟨D, hD, hCD⟩ := part4 T hA hB hR hsd hlk hC
  obtain ⟨d, hd⟩ := hD.1
  have h1 : G L R (Sum.inl c) (Sum.inr d) := ⟨hCD ⟨hc, hd⟩, ⟨C, hC, hc⟩, ⟨D, hD, hd⟩⟩
  have h2 : G L R (Sum.inr d) (Sum.inl c') := ⟨hCD ⟨hc', hd⟩, ⟨D, hD, hd⟩, ⟨C, hC, hc'⟩⟩
  exact (Relation.ReflTransGen.single h1).tail h2

/-- Two steps of neighbourhoods: `X ↦ (X⁺)⁻`. -/
def Phi (R : Set (A × B)) (X : Set A) : Set A := nbrL R (nbrR R X)

theorem phi_iter_absorbing {R : Set (A × B)} (hR : IsSubuniverse L R) (hsd : Subdirect R)
    {X : Set A} (hX : IsAbsorbing L X) : ∀ n, IsAbsorbing L ((Phi R)^[n] X)
  | 0 => hX
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact nbrL_absorbing hR hsd.1 (nbrR_absorbing hR hsd.2 (phi_iter_absorbing hR hsd hX n))

theorem claimA (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    {R : Set (A × B)} (hR : IsSubuniverse L R) (hsd : Subdirect R) (hlk : Linked R) (n : ℕ) :
    ∀ (C C' : Set A), MinAbsorbing L C → MinAbsorbing L C' →
      (C' ∩ (Phi R)^[n] C).Nonempty → ∀ c ∈ C, ∀ c' ∈ C',
        Relation.ReflTransGen (G L R) (Sum.inl c) (Sum.inl c') := by
  induction n with
  | zero =>
    rintro C C' hC hC' ⟨x, hx', hx⟩ c hc c' hc'
    exact (sameC T hA hB hR hsd hlk hC hc hx).trans (sameC T hA hB hR hsd hlk hC' hx' hc')
  | succ n ih =>
    rintro C C' hC hC' ⟨x, hx', hx⟩ c hc c' hc'
    rw [Function.iterate_succ_apply'] at hx
    have hYabs := phi_iter_absorbing hR hsd hC.2.1 n
    obtain ⟨b, ⟨y, hy, hyb⟩, hxb⟩ := hx
    have hZ := absorbing_inter (nbrR_absorbing hR hsd.2 hYabs) (nbrR_absorbing hR hsd.2 hC'.2.1)
    obtain ⟨E, hEsub, hE⟩ := exists_minabs (nbrR R ((Phi R)^[n] C) ∩ nbrR R C') ⟨b, ⟨y, hy, hyb⟩, ⟨x, hx', hxb⟩⟩ hZ
    obtain ⟨e, he⟩ := hE.1
    obtain ⟨⟨y', hy', hy'e⟩, ⟨c'', hc'', hc''e⟩⟩ := hEsub he
    have hW := absorbing_inter (nbrL_absorbing hR hsd.1 hE.2.1) hYabs
    obtain ⟨F, hFsub, hF⟩ := exists_minabs (nbrL R E ∩ (Phi R)^[n] C) ⟨y', ⟨e, he, hy'e⟩, hy'⟩ hW
    obtain ⟨f, hf⟩ := hF.1
    obtain ⟨⟨e', he', hfe'⟩, hfY⟩ := hFsub hf
    have h1 := ih C F hC hF ⟨f, hf, hfY⟩ c hc f hf
    have hFE := prod_sub T hA hB hR hsd hlk hF hE ⟨(f, e'), ⟨hf, he'⟩, hfe'⟩
    have hCE := prod_sub T hA hB hR hsd hlk hC' hE ⟨(c'', e), ⟨hc'', he⟩, hc''e⟩
    have h2 : G L R (Sum.inl f) (Sum.inr e) := ⟨hFE ⟨hf, he⟩, ⟨F, hF, hf⟩, ⟨E, hE, he⟩⟩
    have h3 : G L R (Sum.inr e) (Sum.inl c') := ⟨hCE ⟨hc', he⟩, ⟨E, hE, he⟩, ⟨C', hC', hc'⟩⟩
    exact (h1.tail h2).tail h3

omit [Finite A] [Finite B] in
theorem reach {R : Set (A × B)} {X : Set A} {c a : A} (hc : c ∈ X)
    (h : Relation.ReflTransGen (LinkStep R) c a) : ∃ n, a ∈ (Phi R)^[n] X := by
  induction h with
  | refl => exact ⟨0, hc⟩
  | tail _ hst ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨b, h1, h2⟩ := hst
    refine ⟨n + 1, ?_⟩
    rw [Function.iterate_succ_apply']
    exact ⟨b, ⟨_, hn, h1⟩, h2⟩

/-- Item (v). -/
theorem part5 (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    {R : Set (A × B)} (hR : IsSubuniverse L R) (hsd : Subdirect R) (hlk : Linked R) :
    ∀ x y : A ⊕ B, InMinAbs L x → InMinAbs L y → Relation.ReflTransGen (G L R) x y := by
  have toA : ∀ x : A ⊕ B, InMinAbs L x → ∃ (c : A) (C : Set A), MinAbsorbing L C ∧ c ∈ C ∧
      Relation.ReflTransGen (G L R) x (Sum.inl c) := by
    rintro (c | d) hx
    · obtain ⟨C, hC, hc⟩ := hx
      exact ⟨c, C, hC, hc, Relation.ReflTransGen.refl⟩
    · obtain ⟨D, hD, hd⟩ := hx
      obtain ⟨C, hC, hCD⟩ := part4' T hA hB hR hsd hlk hD
      obtain ⟨c, hc⟩ := hC.1
      exact ⟨c, C, hC, hc,
        Relation.ReflTransGen.single ⟨hCD ⟨hc, hd⟩, ⟨D, hD, hd⟩, ⟨C, hC, hc⟩⟩⟩
  have hsymm : ∀ x y, Relation.ReflTransGen (G L R) x y → Relation.ReflTransGen (G L R) y x := by
    intro x y h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hst ih =>
      exact Relation.ReflTransGen.head ⟨linkAdj_symm _ _ hst.1, hst.2.2, hst.2.1⟩ ih
  intro x y hx hy
  obtain ⟨c, C, hC, hc, hxc⟩ := toA x hx
  obtain ⟨c', C', hC', hc', hyc⟩ := toA y hy
  have hl := hlk c c' (by rw [hsd.1]; exact Set.mem_univ _) (by rw [hsd.1]; exact Set.mem_univ _)
  obtain ⟨n, hn⟩ := reach hc hl
  have hcc := claimA T hA hB hR hsd hlk n C C' hC hC' ⟨c', hc', hn⟩ c hc c' hc'
  exact (hxc.trans hcc).trans (hsymm _ _ hyc)

theorem main (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    (R : L.Substructure (A × B)) (hsd : Subdirect (R : Set (A × B))) :
    (Linked (R : Set (A × B)) → ∀ E : Set R, IsAbsorbing L E →
        Linked (Subtype.val '' E : Set (A × B))) ∧
    (∀ (C : Set A) (D : Set B), MinAbsorbing L C → MinAbsorbing L D →
        (C ×ˢ D ∩ (R : Set (A × B))).Nonempty →
        Prod.fst '' (C ×ˢ D ∩ (R : Set (A × B))) = C ∧
          Prod.snd '' (C ×ˢ D ∩ (R : Set (A × B))) = D) ∧
    (Linked (R : Set (A × B)) → ∀ (C : Set A) (D : Set B), MinAbsorbing L C →
        MinAbsorbing L D → (C ×ˢ D ∩ (R : Set (A × B))).Nonempty →
        C ×ˢ D ⊆ (R : Set (A × B)) ∧ MinAbsorbing L {x : R | (x : A × B) ∈ C ×ˢ D}) ∧
    (Linked (R : Set (A × B)) → ∀ C : Set A, MinAbsorbing L C →
        ∃ D : Set B, MinAbsorbing L D ∧ C ×ˢ D ⊆ (R : Set (A × B))) ∧
    (Linked (R : Set (A × B)) → ∀ c d : A ⊕ B, InMinAbs L c → InMinAbs L d →
        Relation.ReflTransGen
          (fun x y => LinkAdj (R : Set (A × B)) x y ∧ InMinAbs L x ∧ InMinAbs L y) c d) := by
  have hRs : IsSubuniverse L (R : Set (A × B)) := fun _ f x hx => R.fun_mem f x hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hlk E hE
    exact linked_of_relAbs hA.1 hlk (by rintro _ ⟨x, -, rfl⟩; exact x.2)
      (relAbs_of_absorbing_sub R hE)
  · intro C D hC hD hne
    exact part2 hRs hsd hC hD hne
  · intro hlk C D hC hD hne
    refine ⟨prod_sub T hA hB hRs hsd hlk hC hD hne, ?_⟩
    have hEdef : Subtype.val '' {x : R | (x : A × B) ∈ C ×ˢ D} =
        C ×ˢ D ∩ (R : Set (A × B)) := by
      ext p; constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.2⟩
      · rintro ⟨hp, hpR⟩; exact ⟨⟨p, hpR⟩, hp, rfl⟩
    have hErel : RelAbs L (C ×ˢ D ∩ (R : Set (A × B))) R :=
      relAbs_inter (absorbing_prod hC.2.1 hD.2.1) hRs
    obtain ⟨p, hpCD, hpR⟩ := hne
    refine ⟨⟨⟨p, hpR⟩, hpCD⟩, absorbing_sub_of_relAbs R (by rw [hEdef]; exact hErel), ?_⟩
    intro F hFne hFsub hFabs
    have hF' := relAbs_of_absorbing_sub R hFabs
    have hFR : Subtype.val '' F ⊆ (R : Set (A × B)) := by rintro _ ⟨x, -, rfl⟩; exact x.2
    have hFCD : Subtype.val '' F ⊆ C ×ˢ D := by rintro _ ⟨x, hx, rfl⟩; exact hFsub hx
    have hfull := full_of_relAbs T hA hB hsd hlk hC hD hFR hFCD hF' (hFne.image _)
    apply Set.Subset.antisymm hFsub
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hfull (show (x : A × B) ∈ C ×ˢ D from hx)
    exact (Subtype.ext hzx : z = x) ▸ hz
  · intro hlk C hC
    exact part4 T hA hB hRs hsd hlk hC
  · intro hlk c d hc hd
    exact part5 T hA hB hRs hsd hlk c d hc hd

end main

end P215

end BKAbsorption

open BKAbsorption

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] {A : Type w₁} {B : Type w₂}
    [L.Structure A] [L.Structure B]
    [Finite A] [Finite B] (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    (R : L.Substructure (A × B)) (hsd : Subdirect (R : Set (A × B))) :
    (Linked (R : Set (A × B)) → ∀ E : Set R, IsAbsorbing L E →
        Linked (Subtype.val '' E : Set (A × B))) ∧
    (∀ (C : Set A) (D : Set B), MinAbsorbing L C → MinAbsorbing L D →
        (C ×ˢ D ∩ (R : Set (A × B))).Nonempty →
        Prod.fst '' (C ×ˢ D ∩ (R : Set (A × B))) = C ∧
          Prod.snd '' (C ×ˢ D ∩ (R : Set (A × B))) = D) ∧
    (Linked (R : Set (A × B)) → ∀ (C : Set A) (D : Set B), MinAbsorbing L C →
        MinAbsorbing L D → (C ×ˢ D ∩ (R : Set (A × B))).Nonempty →
        C ×ˢ D ⊆ (R : Set (A × B)) ∧ MinAbsorbing L {x : R | (x : A × B) ∈ C ×ˢ D}) ∧
    (Linked (R : Set (A × B)) → ∀ C : Set A, MinAbsorbing L C →
        ∃ D : Set B, MinAbsorbing L D ∧ C ×ˢ D ⊆ (R : Set (A × B))) ∧
    (Linked (R : Set (A × B)) → ∀ c d : A ⊕ B, InMinAbs L c → InMinAbs L d →
        Relation.ReflTransGen
          (fun x y => LinkAdj (R : Set (A × B)) x y ∧ InMinAbs L x ∧ InMinAbs L y) c d) :=
  P215.main T hA hB R hsd
