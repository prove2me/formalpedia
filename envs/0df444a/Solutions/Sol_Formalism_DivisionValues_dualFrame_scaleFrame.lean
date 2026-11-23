-- Prove2me | solution 1 for Formalism.DivisionValues.dualFrame_scaleFrame
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:28.877076+00:00
-- url     : https://prove2.me/submissions/4d3573e2-9c47-4a84-97dd-5c4f7df82a7d

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Theorems.Thm_Formalism_DivisionValues_inv_inv_real_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.DivisionValues
theorem _root_.solution {d : ℕ} (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det) :
    Formalism.HN.dualFrame (scaleFrame t X) =
      fun v => ((Real.sqrt (t v) : ℝ) : ℂ) • Formalism.HN.dualFrame X v := by
  funext v
  show ((((((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • X v)).transpose)⁻¹ =
    ((Real.sqrt (t v) : ℝ) : ℂ) • ((X v).transpose)⁻¹
  rw [Matrix.transpose_smul]
  exact inv_inv_real_smul _ (Real.sqrt_pos.mpr (ht v)) _ (by rw [Matrix.det_transpose]; exact hX v)
end Formalism.DivisionValues
