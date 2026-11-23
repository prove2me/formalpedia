-- Prove2me | solution 1 for Formalism.DivisionValues.imageLcv_len_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:07:13.733485+00:00
-- url     : https://prove2.me/submissions/05126643-44cc-48ea-b82f-0e3e8375cf3b

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv

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
open Formalism Formalism.DivisionValues
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.DivisionValues
theorem _root_.solution (f : W ≃ₗ[R] W) (X Y : Submodule R W) :
    Module.length R (↥(X.map (f : W →ₗ[R] W)) ⧸
        (Y.map (f : W →ₗ[R] W)).comap (X.map (f : W →ₗ[R] W)).subtype) =
      Module.length R (↥X ⧸ Y.comap X.subtype) := by
  symm
  apply LinearEquiv.length_eq
  refine Submodule.Quotient.equiv _ _ (f.submoduleMap X) ?_
  ext ⟨z, hz⟩
  constructor
  · rintro ⟨y, hy, hyz⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hy ⊢
    have : (f : W → W) y = z := by
      have := congrArg Subtype.val hyz
      simpa using this
    rw [← this]
    exact Submodule.mem_map_of_mem hy
  · intro h
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at h
    rw [Submodule.mem_map_equiv] at h
    rw [Submodule.mem_map_equiv] at hz
    refine ⟨⟨f.symm z, hz⟩, h, ?_⟩
    apply Subtype.ext
    simp
end Formalism.DivisionValues
