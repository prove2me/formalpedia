-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.askD_zero_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:29:19.053003+00:00
-- url     : https://prove2.me/submissions/2353e513-fe36-4760-973b-bea6a5f953ef

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_max_zero_of_gt

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
theorem _root_.solution (D : ArithData H) (hD : HostFacts D) {N : ℕ} {a : ℝ} {t : H} {w : E0 × H → ℝ}
    (hw : ∀ ρ, InPhi ρ → 0 < w ρ) (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) (hdN : N < D.d) :
    askD D N a t w = 0 := by
  classical
  unfold askD
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro g hg
  have hg' : ¬ InPhi g := (Finset.mem_filter.1 hg).2.2
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  apply max_zero_of_gt hw hN hg'
  have h3 : D.d ≤ D.d ^ i := Nat.le_self_pow (by omega) _
  exact_mod_cast lt_of_lt_of_le hdN h3
end Formalism.LFunctionChainParameters.characterSumData
