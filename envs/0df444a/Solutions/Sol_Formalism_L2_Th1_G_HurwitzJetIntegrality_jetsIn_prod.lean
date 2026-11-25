-- Prove2me | solution 1 for Formalism.L2.Th1.G.HurwitzJetIntegrality.jetsIn_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:13:15.896357+00:00
-- url     : https://prove2.me/submissions/1945c29b-8c01-4227-af27-4904d07a7b66

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Theorems.Thm_Formalism_LT_TorsProof_one_mem


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
open Formalism.L2.Th1.G.HurwitzJetIntegrality
namespace Formalism.L2.Th1.G.HurwitzJetIntegrality
theorem _root_.solution (h1 : JetsRing) {K : Type} [Field K] (R : Subring K) {ι α : Type}
    (s : Finset α) (g : α → MvPowerSeries ι K) (hg : ∀ x ∈ s, JetsIn R (g x)) :
    JetsIn R (∏ x ∈ s, g x) := by
  obtain ⟨hC, -, -, -, hmul⟩ := h1 K R ι
  exact Finset.prod_induction g (JetsIn R) (fun a b ha hb => hmul a b ha hb)
    (by simpa using hC 1 R.one_mem) hg
end Formalism.L2.Th1.G.HurwitzJetIntegrality
