-- Prove2me | solution 1 for Formalism.L2.Th1.G.GramFrameCompositionTwoFacts.odd_coeff_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:36:47.0848+00:00
-- url     : https://prove2.me/submissions/431c670c-f85d-4c68-be7a-ed6250b338be

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveSecondLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_BridgeTwoMore
import Definitions.Def_Formalism_GaussJetBounds_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_ThetaZeroJetsCurveHolds
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xPlus)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)
open Formalism.L2.Th1.G.GramFrameCompositionTwoFacts
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.G.GramFrameCompositionTwoFacts
theorem _root_.solution {e : PowerSeries K} (h : ∀ n : ℕ, Odd n → PowerSeries.coeff n e = 0) (s2 : K)
    (n : ℕ) (hn : Odd n) : PowerSeries.coeff n (lam e s2) = 0 := by
  have h2 : n ≠ 2 := by
    rintro rfl
    exact absurd hn (by decide)
  rw [lam, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg h2, mul_zero, add_zero,
    dblInt, PowerSeries.coeff_mk]
  split_ifs with h1
  · rfl
  · have h3 : Odd (n - 2) := by
      obtain ⟨k, hk⟩ := hn
      refine ⟨k - 1, ?_⟩
      omega
    rw [h _ h3, zero_div]
end Formalism.L2.Th1.G.GramFrameCompositionTwoFacts
