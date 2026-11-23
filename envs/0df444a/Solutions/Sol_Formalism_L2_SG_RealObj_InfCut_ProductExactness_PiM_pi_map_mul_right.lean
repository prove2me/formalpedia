-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_map_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:52.649685+00:00
-- url     : https://prove2.me/submissions/55dc4589-eda5-4b86-9db5-5ac29f3df59d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_LintegralFinProd
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_PiMapMulRight

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
variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)]
  [∀ i, MeasurableMul (G i)]
namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
theorem _root_.solution (μ : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] (g : ∀ i, G i)
    (h : ∀ i, (μ i).map (fun x => x * g i) = μ i) : (Measure.pi μ).map (fun x => x * g) = Measure.pi μ := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  have hm : Measurable (fun x : ∀ i, G i => x * g) :=
    measurable_pi_lambda _ fun i => (measurable_mul_const (g i)).comp (measurable_pi_apply i)
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : ∀ i, G i => x * g) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => (fun y => y * g i) ⁻¹' s i := by
    ext x; simp [Set.mem_univ_pi]
  rw [hpre, Measure.pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Measure.map_apply (measurable_mul_const (g i)) (hs i), h i]
end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
