-- Prove2me | solution 1 for BKAbsorption.loop_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-09T16:08:01.937197+00:00
-- url     : https://prove2.me/submissions/b334b811-72ce-442c-aa37-0ae93211baff

import Definitions.Def_BKAbsorption_defs
import Theorems.Thm_BKAbsorption_component_subuniverse
import Theorems.Thm_BKAbsorption_loop_absorbing_step
import Theorems.Thm_BKAbsorption_loop_nonabsorbing_step
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Barto–Kozik, Theorem 3.6 (Loop Lemma), reduced to three platform children:

* `component_subuniverse` (Claim 3.8): the weak component of a vertex of algebraic length 1 is a
  subuniverse;
* `loop_absorbing_step` (Lemma 3.3 + Claims 3.9–3.10): an absorbing `I ≠ S` in such a component
  yields a smaller smooth, connected, algebraic-length-1 absorbing subuniverse `S' ⊊ S`;
* `loop_nonabsorbing_step` (Claim 3.11): without proper absorbing subuniverses, either a loop
  exists or a smaller smooth algebraic-length-1 subuniverse exists.

The paper's induction on `|A|` is carried out on subsets `S ⊆ A` of a fixed ambient algebra
(relative absorption), which avoids passing to subalgebra types.
-/

universe u₁ v₁ w₁

open FirstOrder FirstOrder.Language

namespace BKAbsorption

namespace L36

variable {L : FirstOrder.Language.{u₁, v₁}} {A : Type w₁} [L.Structure A]

/-- Star composition `t ⋆ s` on `m * n` variables. -/
def star {m n : ℕ} (t : L.Term (Fin m)) (s : L.Term (Fin n)) : L.Term (Fin (m * n)) :=
  t.subst (fun j => s.relabel (fun l => finProdFinEquiv (j, l)))

theorem realize_star {m n : ℕ} (t : L.Term (Fin m)) (s : L.Term (Fin n))
    (a : Fin (m * n) → A) :
    (star t s).realize a =
      t.realize (fun j => s.realize (fun l => a (finProdFinEquiv (j, l)))) := by
  simp only [star, Term.realize_subst, Term.realize_relabel, Function.comp_def]

theorem realize_mem {S : Set A} (hS : IsSubuniverse L S) {α : Type*} (t : L.Term α)
    (a : α → A) (ha : ∀ i, a i ∈ S) : t.realize a ∈ S := by
  induction t with
  | var i => exact ha i
  | func f ts ih => exact hS _ f _ ih

variable (L) in
/-- `X` is a subuniverse absorbing the subset `S` (relative absorption). -/
def RelAbs (X S : Set A) : Prop :=
  IsSubuniverse L X ∧ ∃ (n : ℕ) (t : L.Term (Fin n)), 0 < n ∧
    ∀ (k : Fin n) (a : Fin n → A), (∀ i, a i ∈ S) → (∀ i, i ≠ k → a i ∈ X) → t.realize a ∈ X

/-- Proposition 2.4 (transitivity of absorption), relative form. -/
theorem relAbs_trans {X Y S : Set A} (hXY : X ⊆ Y) (hX : RelAbs L X Y) (hY : RelAbs L Y S) :
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

/-- A subuniverse absorbs itself (via a projection). -/
theorem relAbs_self {S : Set A} (hS : IsSubuniverse L S) : RelAbs L S S :=
  ⟨hS, 1, Term.var 0, Nat.one_pos, fun _ _ ha _ => ha 0⟩

/-- Absorption of `S` restricts to absorption of any intermediate `S' ⊆ S`. -/
theorem relAbs_restrict {C S' S : Set A} (hS' : S' ⊆ S) (h : RelAbs L C S) : RelAbs L C S' := by
  obtain ⟨hC, n, t, hn, ht⟩ := h
  exact ⟨hC, n, t, hn, fun k a ha hak => ht k a (fun i => hS' (ha i)) hak⟩

variable (L) in
/-- `J` is a minimal absorbing subuniverse of the subset `S` (relative `J ⊴⊴ S`). -/
def MinRel (S J : Set A) : Prop :=
  J ⊆ S ∧ J.Nonempty ∧ RelAbs L J S ∧
    ∀ C : Set A, C.Nonempty → C ⊆ J → RelAbs L C S → C = J

/-- If `J ⊴⊴ S'` and `S' ⊴ S` then `J ⊴⊴ S`. -/
theorem minRel_trans {S' S J : Set A} (hJ : MinRel L S' J) (hS'S : S' ⊆ S)
    (hS' : RelAbs L S' S) : MinRel L S J :=
  ⟨hJ.1.trans hS'S, hJ.2.1, relAbs_trans hJ.1 hJ.2.2.1 hS',
    fun C hC hCJ hCabs => hJ.2.2.2 C hC hCJ (relAbs_restrict hS'S hCabs)⟩

section walks

variable {E : Set (A × A)}

theorem walk_mem {S : Set A} {a b : A} {z : ℤ} (h : Walk (E ∩ S ×ˢ S) a b z) (ha : a ∈ S) :
    b ∈ S := by
  induction h with
  | refl => exact ha
  | fwd _ hbc _ => exact (Set.mem_prod.1 hbc.2).2
  | bwd _ hcb _ => exact (Set.mem_prod.1 hcb.2).1

/-- A walk inside `S` starting at `a` stays inside the weak component of `a`. -/
theorem walk_restrict {S : Set A} {a b : A} {z : ℤ} (h : Walk (E ∩ S ×ˢ S) a b z) :
    Walk (E ∩ {x | ∃ z, Walk (E ∩ S ×ˢ S) a x z} ×ˢ {x | ∃ z, Walk (E ∩ S ×ˢ S) a x z}) a b z := by
  induction h with
  | refl => exact Walk.refl _
  | fwd h hbc ih =>
    exact Walk.fwd ih (Set.mem_inter hbc.1 (Set.mk_mem_prod ⟨_, h⟩ ⟨_, Walk.fwd h hbc⟩))
  | bwd h hcb ih =>
    exact Walk.bwd ih (Set.mem_inter hcb.1 (Set.mk_mem_prod ⟨_, Walk.bwd h hcb⟩ ⟨_, h⟩))

end walks

/-- The weak component of a vertex inside a smooth induced digraph is again smooth. -/
theorem smooth_component (E : L.Substructure (A × A)) {S : Set A}
    (hsm : ∀ x ∈ S, (∃ y ∈ S, (x, y) ∈ E) ∧ ∃ y ∈ S, (y, x) ∈ E) {a : A} (ha : a ∈ S) :
    ∀ x ∈ {x | ∃ z, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a x z},
      (∃ y ∈ {x | ∃ z, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a x z}, (x, y) ∈ E) ∧
        ∃ y ∈ {x | ∃ z, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a x z}, (y, x) ∈ E := by
  rintro x ⟨z, hz⟩
  have hx := walk_mem hz ha
  obtain ⟨⟨y, hy, hxy⟩, ⟨y', hy', hyx⟩⟩ := hsm x hx
  exact ⟨⟨y, ⟨_, Walk.fwd hz (Set.mem_inter hxy (Set.mk_mem_prod hx hy))⟩, hxy⟩,
    ⟨y', ⟨_, Walk.bwd hz (Set.mem_inter hyx (Set.mk_mem_prod hy' hx))⟩, hyx⟩⟩

variable [L.IsAlgebraic]

/-- The relative Loop Lemma for subsets `S` of a fixed finite Taylor algebra, by strong induction
on `|S|`. -/
theorem main [Finite A] (T : TaylorDatum L) (hA : IsTaylorAlg T A)
    (E : L.Substructure (A × A)) : ∀ (n : ℕ) (S : Set A), S.ncard = n → IsSubuniverse L S →
    (∀ x ∈ S, (∃ y ∈ S, (x, y) ∈ E) ∧ ∃ y ∈ S, (y, x) ∈ E) →
    (∀ a ∈ S, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a a 1 → ∃ x ∈ S, (x, x) ∈ E) ∧
    (∀ I : Set A, RelAbs L I S → I.Nonempty →
      (∃ a ∈ S, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a a 1 ∧
        ∀ x ∈ I, ∃ z, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a x z) →
      ∃ J, MinRel L S J ∧ ∃ x ∈ J, (x, x) ∈ E) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hn hS hsm
  have hlt : ∀ S' : Set A, S' ⊂ S → S'.ncard < n := fun S' h => hn ▸ Set.ncard_lt_ncard h
  -- absorbing case: Lemma 3.3 + Claims 3.9–3.10, then induction on `S'`
  have hB : ∀ a ∈ S, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a a 1 → ∀ I : Set A, I.Nonempty →
      I ≠ S → (∀ x ∈ I, ∃ z, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a x z) → RelAbs L I S →
      ∃ J, MinRel L S J ∧ ∃ x ∈ J, (x, x) ∈ E := by
    intro a ha hl I hI hIS hIc hIabs
    obtain ⟨S', hS'S, hS'ne, hS'abs, hS'sm, b, hb, hbl, hbc⟩ :=
      loop_absorbing_step hA.1 E S hS hsm a ha hl I hI hIS hIc hIabs
    obtain ⟨-, h2⟩ := ih _ (hlt S' hS'S) S' rfl hS'abs.1 hS'sm
    obtain ⟨J, hJ, x, hx, hxx⟩ := h2 S' (relAbs_self hS'abs.1) hS'ne ⟨b, hb, hbl, hbc⟩
    exact ⟨J, minRel_trans hJ hS'S.subset hS'abs, x, hx, hxx⟩
  -- first part
  have p1 : ∀ a ∈ S, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a a 1 → ∃ x ∈ S, (x, x) ∈ E := by
    intro a ha hl
    by_cases hex : ∃ C : Set A, C ⊆ {x | ∃ z, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a x z} ∧
        C.Nonempty ∧ C ≠ S ∧ RelAbs L C S
    · obtain ⟨C, hCH, hCne, hCS, hCabs⟩ := hex
      obtain ⟨J, hJ, x, hx, hxx⟩ := hB a ha hl C hCne hCS (fun x hx => hCH hx) hCabs
      exact ⟨x, hJ.1 hx, hxx⟩
    have hex' : ∀ C : Set A, C ⊆ {x | ∃ z, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a x z} →
        C.Nonempty → RelAbs L C S → C = S :=
      fun C hCH hCne hCabs => by_contra fun h => hex ⟨C, hCH, hCne, h, hCabs⟩
    have hHS : {x | ∃ z, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a x z} ⊆ S :=
      fun x ⟨_, hz⟩ => walk_mem hz ha
    by_cases hHeq : {x | ∃ z, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a x z} = S
    · have hconn : ∀ x ∈ S, ∃ z, Walk ((E : Set (A × A)) ∩ S ×ˢ S) a x z := by
        intro x hx
        rw [← hHeq] at hx
        exact hx
      have hnoabs : ∀ C : Set A, C ⊆ S → C.Nonempty → RelAbs L C S → C = S :=
        fun C hCS hCne hCabs => hex' C (by rw [hHeq]; exact hCS) hCne hCabs
      rcases loop_nonabsorbing_step T hA E S hS hsm a ha hl hconn hnoabs with
        h | ⟨B, hBS, _, hBsub, hBsm, b, hb, hbl⟩
      · exact h
      · obtain ⟨h1, -⟩ := ih _ (hlt B hBS) B rfl hBsub hBsm
        obtain ⟨x, hx, hxx⟩ := h1 b hb hbl
        exact ⟨x, hBS.subset hx, hxx⟩
    · have hHS' := LE.le.ssubset_of_ne hHS hHeq
      obtain ⟨h1, -⟩ := ih _ (hlt _ hHS') _ rfl
        (component_subuniverse hA.1 E S hS hsm a ha hl) (smooth_component E hsm ha)
      obtain ⟨x, hx, hxx⟩ := h1 a ⟨0, Walk.refl a⟩ (walk_restrict hl)
      exact ⟨x, hHS hx, hxx⟩
  refine ⟨p1, ?_⟩
  -- second part
  rintro I hIabs hIne ⟨a, ha, hl, hIc⟩
  by_cases hIS : I = S
  · by_cases hex : ∃ C : Set A, C ⊆ S ∧ C.Nonempty ∧ C ≠ S ∧ RelAbs L C S
    · obtain ⟨C, hCS, hCne, hCS', hCabs⟩ := hex
      exact hB a ha hl C hCne hCS' (fun x hx => hIc x (hIS ▸ hCS hx)) hCabs
    · obtain ⟨x, hx, hxx⟩ := p1 a ha hl
      refine ⟨S, ⟨subset_rfl, hIS ▸ hIne, relAbs_self hS, ?_⟩, x, hx, hxx⟩
      exact fun C hC hCS hCabs => by_contra fun h => hex ⟨C, hCS, hC, h, hCabs⟩
  · exact hB a ha hl I hIne hIS hIc hIabs

end L36

end BKAbsorption

open BKAbsorption

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] {A : Type w₁}
    [L.Structure A] [Finite A] (T : TaylorDatum L)
    (hA : IsTaylorAlg T A) (E : L.Substructure (A × A)) (hsm : Smooth (E : Set (A × A)))
    (hlen : ∃ a, Walk (E : Set (A × A)) a a 1) :
    (∃ a, (a, a) ∈ E) ∧
    (∀ I : Set A, IsAbsorbing L I → I.Nonempty →
      (∃ a, Walk (E : Set (A × A)) a a 1 ∧ ∀ x ∈ I, ∃ z, Walk (E : Set (A × A)) a x z) →
      ∃ J : Set A, MinAbsorbing L J ∧ ∃ a ∈ J, (a, a) ∈ E) := by
  have hE : (E : Set (A × A)) ∩ Set.univ ×ˢ Set.univ = E := by
    rw [Set.univ_prod_univ, Set.inter_univ]
  obtain ⟨h1, h2⟩ := L36.main T hA E _ Set.univ rfl (fun _ _ _ _ => trivial)
    (fun x _ => ⟨⟨(hsm x).1.choose, trivial, (hsm x).1.choose_spec⟩,
      ⟨(hsm x).2.choose, trivial, (hsm x).2.choose_spec⟩⟩)
  rw [hE] at h1 h2
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := hlen
    obtain ⟨x, -, hx⟩ := h1 a trivial ha
    exact ⟨x, hx⟩
  · intro I hI hIne ⟨a, ha, hIc⟩
    have hIabs : L36.RelAbs L I Set.univ := by
      obtain ⟨hIs, n, t, hn, ht⟩ := hI
      exact ⟨hIs, n, t, hn, fun k x _ hx => ht k x hx⟩
    obtain ⟨J, ⟨-, hJne, ⟨hJs, n, t, hn, ht⟩, hJmin⟩, x, hx, hxx⟩ :=
      h2 I hIabs hIne ⟨a, trivial, ha, hIc⟩
    refine ⟨J, ⟨hJne, ⟨hJs, n, t, hn, fun k y hy => ht k y (fun _ => trivial) hy⟩, ?_⟩, x, hx, hxx⟩
    intro C hC hCJ ⟨hCs, m, s, hm, hs⟩
    exact hJmin C hC hCJ ⟨hCs, m, s, hm, fun k y _ hy => hs k y hy⟩
