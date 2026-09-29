-- Prove2me | solution 1 for Garrido.isParadoxical_freeGroup_and_isParadoxical_of_actsFreely
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T14:07:57.172985+00:00
-- url     : https://prove2.me/submissions/abfe4571-59e4-428b-8534-bf49de19043b

import Mathlib
import Definitions.Def_Garrido_BanachTarski
import Definitions.Def_Garrido_Equidecomposability
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Chou_Classes

universe u

namespace Garrido.BT

open scoped ENNReal Pointwise
open Set

/-! ### Reduced words -/

section Words

variable {α : Type*} [DecidableEq α]
set_option linter.unusedSectionVars false

/-- `W c`: the elements whose reduced word starts with the letter `c`. -/
def W (c : α × Bool) : Set (FreeGroup α) := {w | (FreeGroup.toWord w).head? = some c}

theorem one_notMem_W (c : α × Bool) : (1 : FreeGroup α) ∉ W c := by
  simp [W, FreeGroup.toWord_one]

theorem disjoint_W {c d : α × Bool} (h : c ≠ d) : Disjoint (W c) (W d) := by
  rw [Set.disjoint_left]
  intro w h1 h2
  simp only [W, mem_ofPred_eq] at h1 h2
  rw [h1] at h2
  exact h (Option.some_injective _ h2)

theorem isReduced_cons_of_head {c : α × Bool} {L : List (α × Bool)}
    (hL : FreeGroup.IsReduced L) (hh : L.head? ≠ some (c.1, !c.2)) :
    FreeGroup.IsReduced (c :: L) := by
  cases L with
  | nil => exact FreeGroup.IsReduced.singleton
  | cons d L =>
    rw [FreeGroup.isReduced_cons_cons]
    refine ⟨fun h1 => ?_, hL⟩
    by_contra h2
    apply hh
    obtain ⟨c1, c2⟩ := c
    obtain ⟨d1, d2⟩ := d
    simp only at h1 h2
    subst h1
    cases c2 <;> cases d2 <;> simp_all

theorem toWord_mk_cons_mul {c : α × Bool} {w : FreeGroup α}
    (hh : (FreeGroup.toWord w).head? ≠ some (c.1, !c.2)) :
    FreeGroup.toWord (FreeGroup.mk [c] * w) = c :: FreeGroup.toWord w := by
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_mk, FreeGroup.reduce_singleton]
  exact (isReduced_cons_of_head FreeGroup.isReduced_toWord hh).reduce_eq

theorem toWord_tail {c : α × Bool} {r : List (α × Bool)} {w : FreeGroup α}
    (hw : FreeGroup.toWord w = c :: r) :
    w = FreeGroup.mk [c] * FreeGroup.mk r ∧ FreeGroup.toWord (FreeGroup.mk r) = r ∧
      r.head? ≠ some (c.1, !c.2) := by
  have hred : FreeGroup.IsReduced (c :: r) := hw ▸ FreeGroup.isReduced_toWord
  refine ⟨?_, ?_, ?_⟩
  · rw [FreeGroup.mul_mk, List.singleton_append, ← hw, FreeGroup.mk_toWord]
  · rw [FreeGroup.toWord_mk]
    exact FreeGroup.IsReduced.reduce_eq (L := r) (List.IsChain.tail hred)
  · intro h
    cases r with
    | nil => simp at h
    | cons d r =>
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h
      rw [FreeGroup.isReduced_cons_cons] at hred
      obtain ⟨c1, c2⟩ := c
      cases c2 <;> simp at hred

/-- `x ∈ of i • W (i, false) ↔ x ∉ W (i, true)`. -/
theorem mem_of_smul_W_iff (i : α) (x : FreeGroup α) :
    x ∈ FreeGroup.of i • W (i, false) ↔ x ∉ W (i, true) := by
  have hinv : (FreeGroup.of i)⁻¹ = FreeGroup.mk [(i, false)] := by
    rw [FreeGroup.of, FreeGroup.inv_mk]; rfl
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, hinv]
  constructor
  · intro hy hx
    simp only [W, mem_ofPred_eq] at hy hx
    obtain ⟨r, hr⟩ : ∃ r, FreeGroup.toWord x = (i, true) :: r := by
      cases h : FreeGroup.toWord x with
      | nil => rw [h] at hx; simp at hx
      | cons d r => rw [h] at hx; simp only [List.head?_cons, Option.some.injEq] at hx
                    exact ⟨r, by rw [hx]⟩
    obtain ⟨hx1, hx2, hx3⟩ := toWord_tail hr
    have : FreeGroup.mk [(i, false)] * x = FreeGroup.mk r := by
      rw [← hinv, hx1, show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl,
        inv_mul_cancel_left]
    rw [this, hx2] at hy
    exact hx3 hy
  · intro hx
    simp only [W, mem_ofPred_eq]
    rw [toWord_mk_cons_mul (c := (i, false)) (by simpa [W] using hx)]
    rfl

end Words

/-! ### Equidecomposition lemmas (copied from proofs/EQ_Sec1.lean) -/

theorem eq_equidecomposable_union {G X : Type*} [Group G] [MulAction G X] {A B C D : Set X}
    (hAC : Disjoint A C) (hBD : Disjoint B D) (h1 : Equidecomposable G A B)
    (h2 : Equidecomposable G C D) : Equidecomposable G (A ∪ C) (B ∪ D) := by
  classical
  obtain ⟨e, rfl, rfl⟩ := h1
  obtain ⟨e', rfl, rfl⟩ := h2
  refine ⟨⟨e.toPartialEquiv.disjointUnion e'.toPartialEquiv hAC hBD,
    e.witness ∪ e'.witness, ?_⟩, rfl, rfl⟩
  intro a ha
  change a ∈ e.source ∪ e'.source at ha
  by_cases h : a ∈ e.source
  · obtain ⟨g, hg, hga⟩ := e.isDecompOn a h
    refine ⟨g, Finset.mem_union_left _ hg, ?_⟩
    change (e.source.piecewise e e') a = g • a
    rw [Set.piecewise_eq_of_mem _ _ _ h]; exact hga
  · obtain ⟨g, hg, hga⟩ := e'.isDecompOn a (ha.resolve_left h)
    refine ⟨g, Finset.mem_union_right _ hg, ?_⟩
    change (e.source.piecewise e e') a = g • a
    rw [Set.piecewise_eq_of_notMem _ _ _ h]; exact hga

theorem eq_equidecomposable_refl {G X : Type*} [Group G] [MulAction G X] (A : Set X) :
    Equidecomposable G A A :=
  ⟨(Equidecomp.refl X G).restr A, by simp, by simp⟩

theorem eq_equidecomposable_image {G X : Type*} [Group G] [MulAction G X] (e : Equidecomp X G)
    {S : Set X} (hS : S ⊆ e.source) : Equidecomposable G S (e.toPartialEquiv '' S) := by
  refine ⟨e.restr S, Equidecomp.source_restr e hS, ?_⟩
  rw [PartialEquiv.image_eq_target_inter_inv_preimage _ hS]
  rfl


/-- Translation by a single group element, as an equidecomposition of `X` with itself. -/
def transl {G X : Type*} [Group G] [MulAction G X] (g : G) : Equidecomp X G where
  toPartialEquiv := (MulAction.toPerm g : Equiv.Perm X).toPartialEquiv
  isDecompOn' := ⟨{g}, fun _ _ => ⟨g, Finset.mem_singleton_self g, rfl⟩⟩

theorem equidecomposable_smul {G X : Type*} [Group G] [MulAction G X] (g : G) (Q : Set X) :
    Equidecomposable G Q (g • Q) := by
  have h := eq_equidecomposable_image (transl (G := G) (X := X) g) (S := Q) (by
    intro x _; trivial)
  convert h using 1
  rw [← Set.image_smul]
  rfl

theorem two_piece {G X : Type*} [Group G] [MulAction G X] {P Q : Set X} (g : G)
    (hPQ : Disjoint P Q) (hPgQ : Disjoint P (g • Q)) :
    Equidecomposable G (P ∪ Q) (P ∪ g • Q) :=
  eq_equidecomposable_union hPQ hPgQ (eq_equidecomposable_refl P) (equidecomposable_smul g Q)

/-! ### The paradox from an equivariant map to `F₂` -/

theorem preimage_smul_eq {G X : Type*} [Group G] [MulAction G X] (π : X → G)
    (hπ : ∀ (g : G) (x : X), π (g • x) = g * π x) (g : G) (S : Set G) :
    π ⁻¹' (g • S) = g • (π ⁻¹' S) := by
  ext x
  rw [mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem,
    mem_preimage, hπ, smul_eq_mul]

abbrev F2 := FreeGroup (Fin 2)

theorem half_equidecomposable {X : Type*} [MulAction F2 X] (π : X → F2)
    (hπ : ∀ (g : F2) (x : X), π (g • x) = g * π x) (i : Fin 2) :
    Equidecomposable F2 (π ⁻¹' W (i, true) ∪ π ⁻¹' W (i, false)) Set.univ := by
  have hPQ : Disjoint (π ⁻¹' W (i, true)) (π ⁻¹' W (i, false)) :=
    (disjoint_W (by simp)).preimage π
  have hP : Disjoint (π ⁻¹' W (i, true)) (FreeGroup.of i • π ⁻¹' W (i, false)) := by
    rw [← preimage_smul_eq π hπ]
    refine Disjoint.preimage π ?_
    rw [Set.disjoint_left]
    intro x h1 h2
    exact (mem_of_smul_W_iff i x).1 h2 h1
  have h := two_piece (FreeGroup.of i) hPQ hP
  convert h using 1
  rw [← preimage_smul_eq π hπ, ← Set.preimage_union]
  symm
  rw [Set.preimage_eq_univ_iff]
  intro y _
  by_cases hy : y ∈ W (i, true)
  · exact Or.inl hy
  · exact Or.inr ((mem_of_smul_W_iff i y).2 hy)

theorem isParadoxical_of_equivariant {X : Type*} [MulAction F2 X] [Nonempty X] (π : X → F2)
    (hπ : ∀ (g : F2) (x : X), π (g • x) = g * π x) :
    IsParadoxical F2 (Set.univ : Set X) := by
  obtain ⟨x0⟩ := ‹Nonempty X›
  set x : X := (π x0)⁻¹ • x0 with hx
  have hx1 : π x = 1 := by rw [hx, hπ, inv_mul_cancel]
  refine ⟨π ⁻¹' W (0, true) ∪ π ⁻¹' W (0, false), π ⁻¹' W (1, true) ∪ π ⁻¹' W (1, false),
    subset_univ _, subset_univ _, ?_, ?_, ?_, half_equidecomposable π hπ 0,
    half_equidecomposable π hπ 1⟩
  · intro h
    have : x ∈ π ⁻¹' W (0, true) ∪ π ⁻¹' W (0, false) := h ▸ mem_univ x
    rcases this with h | h <;> (rw [mem_preimage, hx1] at h; exact one_notMem_W _ h)
  · intro h
    have : x ∈ π ⁻¹' W (1, true) ∪ π ⁻¹' W (1, false) := h ▸ mem_univ x
    rcases this with h | h <;> (rw [mem_preimage, hx1] at h; exact one_notMem_W _ h)
  · rw [← Set.preimage_union, ← Set.preimage_union]
    refine Disjoint.preimage π ?_
    refine Disjoint.union_left (Disjoint.union_right ?_ ?_) (Disjoint.union_right ?_ ?_) <;>
      exact disjoint_W (by decide)

/-- A free action admits an equivariant map to the group (via orbit representatives). -/
theorem exists_equivariant {G X : Type*} [Group G] [MulAction G X] (hfree : ActsFreely G X) :
    ∃ π : X → G, ∀ (g : G) (x : X), π (g • x) = g * π x := by
  let r : X → X := fun x => (Quotient.mk (MulAction.orbitRel G X) x).out
  have hex : ∀ x, ∃ g : G, g • r x = x := by
    intro x
    have h : r x ∈ MulAction.orbit G x := Quotient.mk_out (s := MulAction.orbitRel G X) x
    obtain ⟨g, hg⟩ := h
    exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  have hr : ∀ (g : G) x, r (g • x) = r x := by
    intro g x
    change (Quotient.mk (MulAction.orbitRel G X) (g • x)).out = _
    rw [Quotient.sound (show (MulAction.orbitRel G X) (g • x) x from
      MulAction.mem_orbit x g)]
  choose p hp using hex
  refine ⟨p, fun g x => ?_⟩
  have h1 := hp (g • x)
  have h2 := hp x
  rw [hr] at h1
  set a := p (g • x)
  set b := p x
  have : (a⁻¹ * (g * b)) • r x = r x := by
    rw [mul_smul, mul_smul, h2, ← h1, inv_smul_smul]
  have h3 := hfree _ _ this
  rw [inv_mul_eq_one] at h3
  exact h3

theorem isParadoxical_of_actsFreely (X : Type*) [MulAction F2 X] [Nonempty X]
    (hfree : ActsFreely F2 X) : IsParadoxical F2 (Set.univ : Set X) := by
  obtain ⟨π, hπ⟩ := exists_equivariant hfree
  exact isParadoxical_of_equivariant π hπ

/-- Garrido Proposition 1.5. -/
theorem isParadoxical_freeGroup_and_isParadoxical_of_actsFreely' :
    IsParadoxical (FreeGroup (Fin 2)) (Set.univ : Set (FreeGroup (Fin 2))) ∧
      ∀ (X : Type u) [MulAction (FreeGroup (Fin 2)) X] [Nonempty X],
        ActsFreely (FreeGroup (Fin 2)) X → IsParadoxical (FreeGroup (Fin 2)) (Set.univ : Set X) :=
  ⟨isParadoxical_of_equivariant (X := F2) id (fun _ _ => rfl),
    fun X _ _ hfree => isParadoxical_of_actsFreely X hfree⟩

/-! ### Amenable groups have no free subgroup of rank two -/

end Garrido.BT


namespace Garrido.BT

open Matrix

end Garrido.BT


namespace Garrido.BT

open Matrix

/-! ### Transfer of equidecompositions from an invariant subtype -/

section Transfer

open Set

variable {G H Y : Type*} [Group G] [MulAction G Y] [Group H]

end Transfer

/-! ### The sphere is uncountable -/

/-! ### Theorem 1.7 (Hausdorff) -/

end Garrido.BT


namespace Garrido.BT

open scoped Pointwise
open Real Matrix

/-! ## Part 2: absorbing a set with disjoint orbit translates -/

/-! ## Part 1: rotations -/

end Garrido.BT


namespace Garrido.BT

open scoped Pointwise
open Set

end Garrido.BT

namespace Garrido.BT

open Matrix

end Garrido.BT

namespace Garrido.BT

open Matrix Set
open scoped ENNReal Pointwise

end Garrido.BT


/-! Garrido, Corollary 1.10 (Banach–Tarski for balls and for ℝ³) and the p. 1 consequence. -/

namespace Garrido.BT
open scoped ENNReal Pointwise
open Set Matrix

/-- A single group element as an equidecomposition. -/
noncomputable def single {G X : Type*} [Group G] [MulAction G X] (g : G) : Equidecomp X G where
  toPartialEquiv := (MulAction.toPerm g : Equiv.Perm X).toPartialEquiv
  isDecompOn' := ⟨{g}, fun _ _ => ⟨g, Finset.mem_singleton_self _, rfl⟩⟩

/-! ## The radial projection -/

/-! ## Absorbing the centre -/

/-! ## The targets -/

end Garrido.BT


/-! ## Composition: every milestone, with no hypotheses -/

namespace Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem isParadoxical_freeGroup_and_isParadoxical_of_actsFreely :
    IsParadoxical (FreeGroup (Fin 2)) (Set.univ : Set (FreeGroup (Fin 2))) ∧
      ∀ (X : Type u) [MulAction (FreeGroup (Fin 2)) X] [Nonempty X],
        ActsFreely (FreeGroup (Fin 2)) X → IsParadoxical (FreeGroup (Fin 2)) (Set.univ : Set X) :=
  Garrido.BT.isParadoxical_freeGroup_and_isParadoxical_of_actsFreely'

end Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem solution :
    IsParadoxical (FreeGroup (Fin 2)) (Set.univ : Set (FreeGroup (Fin 2))) ∧
      ∀ (X : Type u) [MulAction (FreeGroup (Fin 2)) X] [Nonempty X],
        ActsFreely (FreeGroup (Fin 2)) X → IsParadoxical (FreeGroup (Fin 2)) (Set.univ : Set X) :=
  Garrido.BT.Final.isParadoxical_freeGroup_and_isParadoxical_of_actsFreely
