-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:42:54.269161+00:00
-- url     : https://prove2.me/submissions/6d17d141-ae5e-467b-9b86-259866cae585

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_LintegralFinProd
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_PiMapMulRight
import Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_ProductExactness_PiM_lintegral_pi_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.ProductExactness Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
variable {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
theorem _root_.solution (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hfin : ∀ i x, f i x ≠ ∞) :
    Measure.pi (fun i => (μ i).withDensity (f i)) = (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  haveI : ∀ i, SigmaFinite ((μ i).withDensity (f i)) := fun i =>
    SigmaFinite.withDensity_of_ne_top (ae_of_all _ (hfin i))
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    lintegral_pi_prod _ _ hf]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i)]
end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
