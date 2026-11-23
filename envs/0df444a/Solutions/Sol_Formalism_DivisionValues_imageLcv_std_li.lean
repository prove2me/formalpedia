-- Prove2me | solution 1 for Formalism.DivisionValues.imageLcv_std_li
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:15:07.219714+00:00
-- url     : https://prove2.me/submissions/2d5bb98e-14b6-41f0-b301-fb8697691bc8

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Theorems.Thm_Formalism_DivisionValues_imageLcv_std_eq

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues
theorem _root_.solution (d : ℕ) : LinearIndependent K (fun i => (Pi.single i 1 : Fin d → K)) := by
  rw [imageLcv_std_eq]
  exact (Pi.basisFun K (Fin d)).linearIndependent
end Formalism.DivisionValues
