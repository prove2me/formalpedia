-- Prove2me | solution 1 for Formalism.L2.Th1.G.jetsIn_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:02:54.300587+00:00
-- url     : https://prove2.me/submissions/13756000-0f4c-4a67-9c64-142958802a15

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Theorems.Thm_Formalism_L2_Th1_G_mfact_mul_dvd_add
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
theorem _root_.solution {f g : MvPowerSeries ι K} (hf : JetsIn R f) (hg : JetsIn R g) :
    JetsIn R (f * g) := by
  classical
  intro κ
  rw [MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine sum_mem (fun p hp => ?_)
  have hp' : p.1 + p.2 = κ := by
    first
      | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      | simpa using hp
  obtain ⟨q, hq⟩ := mfact_mul_dvd_add p.1 p.2
  rw [← hp', hq]
  have e : ((mfact p.1 * mfact p.2 * q : ℕ) : K) *
      (MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g) =
      (q : K) * (((mfact p.1 : ℕ) : K) * MvPowerSeries.coeff p.1 f) *
        (((mfact p.2 : ℕ) : K) * MvPowerSeries.coeff p.2 g) := by
    push_cast
    ring
  rw [e]
  exact R.mul_mem (R.mul_mem (natCast_mem R q) (hf p.1)) (hg p.2)
end Formalism.L2.Th1.G
