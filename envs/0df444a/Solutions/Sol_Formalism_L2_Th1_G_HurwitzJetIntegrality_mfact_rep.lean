-- Prove2me | solution 1 for Formalism.L2.Th1.G.HurwitzJetIntegrality.mfact_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:47:29.007798+00:00
-- url     : https://prove2.me/submissions/32edf09e-b721-492e-ae40-2c9da795caee

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_rep_apply

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
theorem _root_.solution (B : Type) [Fintype B] {ι : Type} [Fintype ι] (κ : ι →₀ ℕ) :
    mfact (rep B fun _ => κ) = (mfact κ) ^ Fintype.card B := by
  classical
  have hx : ∀ {α : Type} [Fintype α] (x : α →₀ ℕ), mfact x = ∏ p, (x p).factorial := fun x =>
    Finsupp.prod_of_support_subset x (Finset.subset_univ _) (fun _ k => k.factorial) (fun _ _ => rfl)
  rw [hx, hx, Fintype.prod_prod_type]
  simp only [rep_apply]
  rw [Finset.prod_const, Finset.card_univ]
end Formalism.L2.Th1.G.HurwitzJetIntegrality
