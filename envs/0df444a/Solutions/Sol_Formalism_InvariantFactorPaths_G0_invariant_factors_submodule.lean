-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G0.invariant_factors_submodule
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:34.135076+00:00
-- url     : https://prove2.me/submissions/1d86cfc4-0ae8-4bcf-ae82-67895eec1fba

import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ElementarySymmetricExpBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_LePowOddOfFloorLogbLe
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_ElementarySymmetricExpBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Pointwise
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G0
open Formalism.G0
namespace Formalism.InvariantFactorPaths.G0
theorem _root_.solution : InvariantFactorsSubmodule := by
  intro R X _ _ _ _ _ π M M' P g E hPM' hM'M h
  classical
  obtain ⟨C, hCM, hCg, hC⟩ := h

  let f : (C → R) →ₗ[R] X ⧸ P :=
    { toFun := fun a => ∑ c : C, a c • P.mkQ (c : X)
      map_add' := by
        intro a b
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }
  let W : Submodule R (X ⧸ P) := M'.map (P.mkQ ∘ₗ ((π ^ E) • LinearMap.id))
  let U : Submodule R (C → R) := W.comap f

  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun R C) U
  have hn : n ≤ C.card := by
    have hli : LinearIndependent R (U.subtype ∘ b) :=
      b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
    have h1 := hli.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using h1
  have hm : ∀ i, ∃ x ∈ M', P.mkQ (π ^ E • x) = f (b i) := by
    intro i
    have h1 : f (b i) ∈ W := (b i).2
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.mp h1
    exact ⟨x, hx, hxe⟩
  choose mm hmM hmf using hm
  refine ⟨Finset.univ.image mm, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
    exact hmM i
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    exact hn.trans hCg
  · intro x hx
    obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp (hC x (hM'M hx))
    obtain ⟨coef, -, hcoef⟩ := Submodule.mem_span_finset.mp hz
    have hfa : f (fun c => coef c) = P.mkQ (π ^ E • x) := by
      show ∑ c : C, coef c • P.mkQ (c : X) = _
      rw [← hpz, map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).mpr hp, zero_add,
        ← hcoef, map_sum, ← Finset.sum_coe_sort C]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_smul]
    have ha : (fun c : C => coef (c : X)) ∈ U := by
      show f _ ∈ W
      rw [hfa]
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    have hsum := congrArg Subtype.val (b.sum_repr ⟨_, ha⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    set r := b.repr ⟨_, ha⟩ with hr
    have hq : P.mkQ (π ^ E • x) = P.mkQ (∑ i, r i • π ^ E • mm i) := by
      rw [← hfa, ← hsum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, hmf i]
    have hmem : π ^ E • x - ∑ i, r i • π ^ E • mm i ∈ P := by
      rw [← Submodule.ker_mkQ P, LinearMap.mem_ker, map_sub, hq, sub_self]
    have hspan : ∑ i, r i • π ^ E • mm i ∈
        Submodule.span R (↑(Finset.univ.image mm) : Set X) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem mm (Finset.mem_univ i)))))
    exact Submodule.mem_sup.mpr ⟨_, hmem, _, hspan, sub_add_cancel _ _⟩
end Formalism.InvariantFactorPaths.G0
