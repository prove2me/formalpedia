-- Prove2me | solution 1 for Formalism.L2.Th1.G.HurwitzJetIntegrality.coeff_inBlock_embDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:01:52.256697+00:00
-- url     : https://prove2.me/submissions/6c974c42-fb61-4f16-8977-395c23fabd31

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
theorem _root_.solution {K : Type} [Field K] {ι B : Type} (k : B) (f : MvPowerSeries ι K)
    (κ : ι →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.embDomain (blockEmb B ι k) κ) (inBlock k f) =
      MvPowerSeries.coeff κ f := by
  rw [inBlock_eq_rename, Finsupp.embDomain_eq_mapDomain]
  simp only [MvPowerSeries.coeff_rename]
  rw [Finset.sum_eq_single κ]
  · intro b hb hbk
    exfalso
    apply hbk
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] at hb
    exact Finsupp.mapDomain_injective (blockEmb B ι k).injective hb
  · intro hκ
    exfalso
    apply hκ
    simp
end Formalism.L2.Th1.G.HurwitzJetIntegrality
