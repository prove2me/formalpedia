-- Prove2me | solution 1 for Formalism.L2.Th1.G.jetsIn_divPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:22:16.363072+00:00
-- url     : https://prove2.me/submissions/36a6bea3-6b80-471b-b2da-1f0bd732e24c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_one
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_mul
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_pderiv
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_iff_pderiv
import Theorems.Thm_Formalism_L2_Th1_G_pderiv_divPow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_mfact_add_single


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
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral mfact_add_single)
variable {K : Type} [Field K] [CharZero K] {R : Subring K} {ι : Type}
namespace Formalism.L2.Th1.G
theorem _root_.solution {a : MvPowerSeries ι K} (h0 : MvPowerSeries.constantCoeff a = 0)
    (ha : JetsIn R a) (m : ℕ) : JetsIn R (MvPowerSeries.C ((m.factorial : K)⁻¹) * a ^ m) := by
  induction m with
  | zero => simpa using (jetsIn_one (R := R) (ι := ι))
  | succ m ih =>
    rw [jetsIn_iff_pderiv]
    refine ⟨?_, fun i => ?_⟩
    · simp [h0]
    · rw [pderiv_divPow]
      exact jetsIn_mul ih (jetsIn_pderiv ha i)
end Formalism.L2.Th1.G
