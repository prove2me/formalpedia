-- Prove2me | solution 1 for Formalism.DivisionValues.imageLcv_lidx_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:00.304125+00:00
-- url     : https://prove2.me/submissions/5930e605-663e-47d7-b6f9-35ff434018eb

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Theorems.Thm_P2M_Formalism_DivisionValues_localization_map__fc10c1f056d1
import Theorems.Thm_Formalism_DivisionValues_imageLcv_len_map

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
theorem _root_.solution (p : Ideal R) [p.IsPrime] (f : W ≃ₗ[R] W) (A B : Submodule R W) :
    Formalism.HermitianLatticesTheory.lidx p (A.map (f : W →ₗ[R] W)) (B.map (f : W →ₗ[R] W)) = Formalism.HermitianLatticesTheory.lidx p A B := by
  have hinf : A.map (f : W →ₗ[R] W) ⊓ B.map (f : W →ₗ[R] W) = (A ⊓ B).map (f : W →ₗ[R] W) :=
    (Submodule.map_inf _ f.injective).symm
  unfold Formalism.HermitianLatticesTheory.lidx Formalism.HermitianLatticesTheory.locLen
  rw [hinf, localization_map', localization_map', localization_map', imageLcv_len_map,
    imageLcv_len_map]
end Formalism.DivisionValues
