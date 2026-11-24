-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.max_zero_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:12:32.243849+00:00
-- url     : https://prove2.me/submissions/93011e85-5774-49a6-9cd2-665499083b21

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_partner_inPhi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
open PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData
theorem _root_.solution {N : ℕ} {a : ℝ} {t : H} {w : E0 × H → ℝ} (hw : ∀ ρ, InPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) {g : E0 × H} (hg : ¬ InPhi g) {m : ℝ} (hm : (N : ℝ) < m) :
    max (a / m - w (partner t g)) 0 = 0 := by
  have hρ := partner_inPhi t hg
  have hwρ := hw _ hρ
  have h1 : a / w (partner t g) < m := lt_of_le_of_lt (hN _ hρ) hm
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (Nat.cast_nonneg N) hm
  have h3 : a < m * w (partner t g) := (div_lt_iff₀ hwρ).1 h1
  have h2 : a / m < w (partner t g) := by
    rw [div_lt_iff₀ hm0]
    linarith [mul_comm m (w (partner t g))]
  exact max_eq_right (by linarith)
end Formalism.LFunctionChainParameters.characterSumData
