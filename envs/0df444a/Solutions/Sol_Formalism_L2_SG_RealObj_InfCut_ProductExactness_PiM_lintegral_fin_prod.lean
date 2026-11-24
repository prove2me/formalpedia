-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.lintegral_fin_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:19:25.586798+00:00
-- url     : https://prove2.me/submissions/37c8a5f5-f76f-4804-916a-4760defcbebc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_LintegralFinProd

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
theorem _root_.solution : ∀ (m : ℕ) {α : Fin m → Type} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i → ℝ≥0∞), (∀ i, Measurable (f i)) →
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i
  | 0, α, _, μ, _, f, _ => by
    simp
  | m + 1, α, _, μ, _, f, hf => by
    have hmp := measurePreserving_piFinSuccAbove μ 0
    set g : α 0 × ((j : Fin m) → α (Fin.succAbove 0 j)) → ℝ≥0∞ :=
      fun z => f 0 z.1 * ∏ i : Fin m, f (Fin.succAbove 0 i) (z.2 i) with hg
    have key : ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ =
        ∫⁻ x, g (MeasurableEquiv.piFinSuccAbove α 0 x) ∂Measure.pi μ := by
      congr 1
      funext x
      rw [Fin.prod_univ_succAbove _ 0]
      rfl
    have hpm : ∫⁻ b, g b ∂((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) =
        (∫⁻ x, f 0 x ∂μ 0) * ∫⁻ y : (j : Fin m) → α (Fin.succAbove 0 j), ∏ i, f (Fin.succAbove 0 i) (y i)
          ∂(Measure.pi fun j => μ (Fin.succAbove 0 j)) :=
      lintegral_prod_mul (f := f 0) (g := fun y : (j : Fin m) → α (Fin.succAbove 0 j) => ∏ i, f (Fin.succAbove 0 i) (y i))
        (hf 0).aemeasurable
        (Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)).aemeasurable
    rw [key, hmp.lintegral_comp_emb (MeasurableEquiv.piFinSuccAbove α 0).measurableEmbedding g, hpm,
      solution m (fun j => μ (Fin.succAbove 0 j)) (fun j => f (Fin.succAbove 0 j)) (fun j => hf _),
      Fin.prod_univ_succAbove _ 0]
end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
