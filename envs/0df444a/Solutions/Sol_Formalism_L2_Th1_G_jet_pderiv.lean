-- Prove2me | solution 1 for Formalism.L2.Th1.G.jet_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:47:14.9308+00:00
-- url     : https://prove2.me/submissions/f4434301-2eed-48c9-9336-62b50f73d8b1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
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
theorem _root_.solution (f : MvPowerSeries ι K) (i : ι) (κ : ι →₀ ℕ) :
    ((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ (MvPowerSeries.pderiv K i f) =
      ((mfact (κ + Finsupp.single i 1) : ℕ) : K) *
        MvPowerSeries.coeff (κ + Finsupp.single i 1) f := by
  rw [mfact_add_single, MvPowerSeries.coeff_pderiv]
  push_cast
  ring
end Formalism.L2.Th1.G
