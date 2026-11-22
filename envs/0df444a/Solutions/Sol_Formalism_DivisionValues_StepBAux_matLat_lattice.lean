-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.matLat_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:32:40.787269+00:00
-- url     : https://prove2.me/submissions/aed2b044-1c33-49dc-9f00-f1bb29f7b055

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep

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
open Formalism.DivisionValues.StepBAux
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.StepBAux
theorem _root_.solution {d : ℕ} (φ : Matrix (Fin d) (Fin d) K) (hφ : IsUnit φ.det)
    (L : Submodule (𝓞 K) (Fin d → K)) (hL : Submodule.IsLattice K L) :
    Submodule.IsLattice K (matLat φ L) := by
  have hsurj : Function.Surjective φ.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det φ).mpr hφ)
  refine ⟨(Submodule.IsLattice.fg (self := hL)).map _, ?_⟩
  have : ((matLat φ L : Submodule (𝓞 K) (Fin d → K)) : Set (Fin d → K)) =
      (Matrix.mulVecLin φ) '' (L : Set (Fin d → K)) := by
    rw [matLat, Submodule.map_coe]
    rfl
  rw [this, Submodule.span_image, Submodule.IsLattice.span_eq_top (self := hL), Submodule.map_top,
    LinearMap.range_eq_top]
  exact hsurj
end Formalism.DivisionValues.StepBAux
