-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.lintegral_pi_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:28:40.080134+00:00
-- url     : https://prove2.me/submissions/27b7933e-c794-4a86-8c37-7561ec152ceb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_LintegralFinProd
import Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_ProductExactness_PiM_lintegral_fin_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.ProductExactness Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
theorem _root_.solution {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  have hmp := measurePreserving_piCongrLeft μ e
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have h1 : ∀ g : (∀ i', α (e i')), ∏ i, f i ((MeasurableEquiv.piCongrLeft α e g) i) =
      ∏ i', f (e i') (g i') := by
    intro g
    rw [← Fintype.prod_equiv e (fun i' => f (e i') (MeasurableEquiv.piCongrLeft α e g (e i')))
      (fun i => f i (MeasurableEquiv.piCongrLeft α e g i)) (fun _ => rfl)]
    congr 1
    funext i'
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
  simp only [h1]
  rw [lintegral_fin_prod _ (fun i' => μ (e i')) (fun i' => f (e i')) (fun i' => hf _)]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)
end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
