-- Prove2me | solution 1 for Formalism.L2.Th1.G.jetsIn_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:13:23.441631+00:00
-- url     : https://prove2.me/submissions/8034756c-f186-4410-a551-224c5fe5f1e8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_one
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_mul
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
variable {K : Type} [Field K] {R : Subring K} {ι : Type}
namespace Formalism.L2.Th1.G
theorem _root_.solution {f : MvPowerSeries ι K} (hf : JetsIn R f) (n : ℕ) : JetsIn R (f ^ n) := by
  induction n with
  | zero => simpa using (jetsIn_one (R := R) (ι := ι))
  | succ n ih => rw [pow_succ]; exact jetsIn_mul ih hf
end Formalism.L2.Th1.G
