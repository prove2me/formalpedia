-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedHeckeModels.logarithmic_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:31.500134+00:00
-- url     : https://prove2.me/submissions/0f1763ac-229b-414c-a531-4f249dfcd56b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LengthQuotientLeOfLatticeSandwich
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedHeckeModels
open Formalism.HermitianLattices.LocalLatticeBases Finset ComplexConjugate
namespace Formalism.HermitianLattices.RamifiedHeckeModels
theorem _root_.solution : LogRatioAtMostOne := by
  intro q hq
  have h3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  rw [div_le_one (by linarith)]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < q - 1 by linarith)
  linarith
end Formalism.HermitianLattices.RamifiedHeckeModels
