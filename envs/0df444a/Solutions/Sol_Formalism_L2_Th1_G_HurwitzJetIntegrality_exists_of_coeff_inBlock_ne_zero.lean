-- Prove2me | solution 1 for Formalism.L2.Th1.G.HurwitzJetIntegrality.exists_of_coeff_inBlock_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:15:06.060821+00:00
-- url     : https://prove2.me/submissions/0e5d5e62-4d60-4e27-9763-8820089d3a69

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_inBlock_eq_rename

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
open Formalism.L2.Th1.G.HurwitzJetIntegrality
namespace Formalism.L2.Th1.G.HurwitzJetIntegrality
theorem _root_.solution {K : Type} [Field K] {ι B : Type} (k : B)
    (f : MvPowerSeries ι K) (x : B × ι →₀ ℕ) (h : MvPowerSeries.coeff x (inBlock k f) ≠ 0) :
    ∃ m : ι →₀ ℕ, x = Finsupp.embDomain (blockEmb B ι k) m := by
  rw [inBlock_eq_rename] at h
  by_contra hx
  push_neg at hx
  apply h
  apply MvPowerSeries.coeff_rename_eq_zero
  rintro ⟨m, rfl⟩
  exact hx m (Finsupp.embDomain_eq_mapDomain _ _).symm
end Formalism.L2.Th1.G.HurwitzJetIntegrality
