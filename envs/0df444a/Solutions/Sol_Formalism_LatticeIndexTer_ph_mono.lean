-- Prove2me | solution 1 for Formalism.LatticeIndexTer.ph_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:51:14.676803+00:00
-- url     : https://prove2.me/submissions/25e02982-fd58-42fc-8548-ee348c74542e

import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Theorems.Thm_Formalism_LatticeIndexTer_le_ph_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Finset
namespace Formalism.LatticeIndexTer
theorem _root_.solution {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : ph a ≤ ph b := by
  have h1 := le_ph_sub (by linarith : (0 : ℝ) < a) hab
  have h2 : 0 ≤ Real.log a := Real.log_nonneg ha
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) h2]
end Formalism.LatticeIndexTer
