-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.numeric_product_inequality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:16:03.382907+00:00
-- url     : https://prove2.me/submissions/b31c1b03-8a9a-4cd1-a62c-34170d1f9ca2

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_FinalM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundUnconditionalOfSat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (p a r x : ℕ) (hx : x ≤ 8 * a + r) :
    ((r.choose 2 * Nat.log p x : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 / 2 * lgV2 p a r := by
  have hlb : 0 ≤ Real.logb p (8 * a + r) := by
    unfold Real.logb
    exact div_nonneg (by exact_mod_cast Real.log_natCast_nonneg (8 * a + r)) (Real.log_natCast_nonneg p)
  have hc : ((r.choose 2 : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 / 2 := by
    have h2 : r.choose 2 * 2 ≤ r ^ 2 := by
      rw [Nat.choose_two_right]
      calc r * (r - 1) / 2 * 2 ≤ r * (r - 1) := Nat.div_mul_le_self _ _
        _ ≤ r * r := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = r ^ 2 := (sq r).symm
    have : ((r.choose 2 : ℕ) : ℝ) * 2 ≤ (r : ℝ) ^ 2 := by exact_mod_cast h2
    linarith
  have hlog : ((Nat.log p x : ℕ) : ℝ) ≤ Real.logb p (8 * a + r) := by
    have hm : Nat.log p x ≤ Nat.log p (8 * a + r) := Nat.log_mono_right hx
    have hn : ((Nat.log p (8 * a + r) : ℕ) : ℝ) ≤ Real.logb p (8 * a + r) := by
      exact_mod_cast Real.natLog_le_logb (8 * a + r) p
    calc ((Nat.log p x : ℕ) : ℝ) ≤ ((Nat.log p (8 * a + r) : ℕ) : ℝ) := by exact_mod_cast hm
      _ ≤ _ := hn
  unfold lgV2
  rw [Nat.cast_mul]
  calc ((r.choose 2 : ℕ) : ℝ) * ((Nat.log p x : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 / 2 * Real.logb p (8 * a + r) :=
        mul_le_mul hc hlog (by positivity) (by positivity)
    _ ≤ (r : ℝ) ^ 2 / 2 * (Real.logb p (8 * a + r) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
end Formalism.InvariantFactorPaths.L4
