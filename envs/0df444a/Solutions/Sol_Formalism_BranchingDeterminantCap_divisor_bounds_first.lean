-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.divisor_bounds_first
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:11.065259+00:00
-- url     : https://prove2.me/submissions/faf07775-a490-4013-90fa-fc9c27086484

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GoodDual
import Theorems.Thm_Formalism_BranchingDeterminantCap_GoodDualLattice_denom
import Theorems.Thm_Formalism_BranchingDeterminantCap_good_dual_deduction
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_hform_eq_dot
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_hform_sepRight
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.DivisionValues.RationalHermitianForm
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : BoundsI := by
  intro K _ _ _ n' n H' E I0 hH' hE hsaM hinj hrange A Bd hA G dG hG hdG hdual hGE
  classical
  have hform_I0 : ∀ x y, Formalism.DivisionValues.hform (I0ᴴ * H' * I0) x y =
      Formalism.DivisionValues.hform H' (I0.mulVec x) (I0.mulVec y) := by
    intro x y
    rw [hform_eq_dot, hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hnd : ∀ x, (∀ y, Formalism.DivisionValues.hform H' y x = 0) → x = 0 :=
    fun x hx => hform_sepRight H' hH'.ne_zero x hx
  have he : E.mulVecLin ∘ₗ E.mulVecLin = E.mulVecLin := by
    rw [← Matrix.mulVecLin_mul, hE]
  have hsa : ∀ x y, Formalism.DivisionValues.hform H' (E.mulVecLin x) y = Formalism.DivisionValues.hform H' x (E.mulVecLin y) := by
    intro x y
    simp only [Matrix.mulVecLin_apply]
    rw [hform_eq_dot, hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hsaM]
  have GD := good_dual_deduction K (Fin n' → K) (Formalism.DivisionValues.hform H') hnd E.mulVecLin he hsa A hA.fg
    hA.span_eq_top
  have hrE : ∀ y : Fin n' → K, y ∈ LinearMap.range E.mulVecLin ↔ ∃ x, I0.mulVec x = y := by
    intro y
    rw [hrange, LinearMap.mem_range]
    constructor
    · rintro ⟨w, rfl⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hE]
    · intro hy
      exact ⟨y, hy⟩
  set M : Submodule (𝓞 K) (Fin n → K) := A.comap ((Matrix.mulVecLin I0).restrictScalars (𝓞 K))
    with hM
  have hMmem : ∀ x, x ∈ M ↔ I0.mulVec x ∈ A := fun x => Iff.rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h1 : (M.map ((Matrix.mulVecLin I0).restrictScalars (𝓞 K))).FG := by
      exact Submodule.FG.of_le hA.fg (Submodule.map_comap_le _ _)
    exact Submodule.fg_of_fg_map_injective _ hinj h1
  · rw [eq_top_iff]
    intro x _
    obtain ⟨s0, _, b, hbs, hs0⟩ := Formalism.HermitianLatticesTheory.dualLattice_basis (R := 𝓞 K) A hA.span_eq_top
    obtain ⟨d, m, hd, hdm⟩ := GoodDualLattice.denom (R := 𝓞 K) b (I0.mulVec x)
    have hdM : d • x ∈ M := by
      rw [hMmem, Matrix.mulVec_smul, hdm]
      exact A.sum_mem fun i _ => A.smul_mem _ (by rw [hbs]; exact hs0 i.2)
    have hd' : algebraMap (𝓞 K) K d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd
    have : x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hdM)
  · intro x hx
    rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hx
    have h1 : I0.mulVec x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H')
          (A ⊓ (LinearMap.range E.mulVecLin).restrictScalars (𝓞 K)) ⊓
        (LinearMap.range E.mulVecLin).restrictScalars (𝓞 K) := by
      refine ⟨?_, (hrE _).mpr ⟨x, rfl⟩⟩
      rw [SetLike.mem_coe, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      rintro y ⟨hyA, hyE⟩
      obtain ⟨y0, rfl⟩ := (hrE y).mp hyE
      rw [← hform_I0]
      exact hx y0 hyA
    rw [GD] at h1
    obtain ⟨z, hz, hzx⟩ := h1
    have hzx' : E.mulVec z = I0.mulVec x := hzx
    have h2 := hGE _ (hdual z hz)
    rw [hMmem, pow_one, Matrix.mulVec_smul, ← hzx', Nat.cast_mul, mul_smul]
    rwa [Matrix.mulVec_smul] at h2
end Formalism.BranchingDeterminantCap
