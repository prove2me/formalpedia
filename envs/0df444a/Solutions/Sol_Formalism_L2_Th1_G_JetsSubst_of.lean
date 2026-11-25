-- Prove2me | solution 1 for Formalism.L2.Th1.G.JetsSubst_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:20:39.8848+00:00
-- url     : https://prove2.me/submissions/beb3d9d3-cc0f-425d-ab29-f186c1a3c561

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_jetsIn_term
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


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
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral)
open HurwitzJetIntegrality
namespace Formalism.L2.Th1.G
theorem _root_.solution (h1 : JetsRing) (h2 : JetsDivPow) : JetsSubst := by
  intro K _ _ R ι κ _ f a hf ha0 ha n
  have hs : MvPowerSeries.HasSubst a := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by simp [ha0 i, IsNilpotent.zero])
      | exact ⟨fun i => by simp [ha0 i, IsNilpotent.zero], by simp [Filter.cofinite_eq_bot]⟩
  rw [MvPowerSeries.coeff_subst hs]
  refine finsum_induction (fun x => ((mfact n : ℕ) : K) * x ∈ R) (by simp)
    (fun x y hx hy => by rw [mul_add]; exact R.add_mem hx hy) (fun d => ?_)
  have h := jetsIn_term h1 h2 R f a hf ha0 ha d n
  rw [MvPowerSeries.coeff_C_mul] at h
  simpa only [smul_eq_mul] using h
end Formalism.L2.Th1.G
