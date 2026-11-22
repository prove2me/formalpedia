-- Prove2me | solution 1 for BornVolume.gBlock_map_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:05.751806+00:00
-- url     : https://prove2.me/submissions/d304e93c-d130-41e0-ba26-3d0e40887062

module
public import Definitions.Def_BornVolumeLean_Volume_MomentMarginalUniform
public import Definitions.Def_BornVolumeLean_MeasureTheory_PiCurry
public import Definitions.Def_BornVolumeLean_Volume_MomentBridgeN

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BornVolume
namespace BornVolume
theorem _root_.solution :
    Measure.map gBlock (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) = expHalf := by
  have hpiftwo : gBlock
      = (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) ∘ (MeasurableEquiv.piFinTwo (fun _ => ℝ)) := by
    funext w
    simp only [gBlock, Function.comp_apply, MeasurableEquiv.piFinTwo_apply]
  rw [hpiftwo, ← Measure.map_map (by fun_prop) (MeasurableEquiv.piFinTwo (fun _ => ℝ)).measurable,
    (measurePreserving_piFinTwo (fun _ : Fin 2 => gaussianReal 0 1)).map_eq,
    ← gaussian2_eq_prod, sqNorm_map_gaussian2]
end BornVolume
