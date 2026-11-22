-- Prove2me | solution 1 for BornVolume.blockSqNormCurry_map_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:54.104056+00:00
-- url     : https://prove2.me/submissions/fb6e0a24-8f17-402c-893f-278ac4dc912d

module
public import Definitions.Def_BornVolumeLean_Volume_MomentMarginalUniform
public import Definitions.Def_BornVolumeLean_MeasureTheory_PiCurry
public import Definitions.Def_BornVolumeLean_Volume_MomentBridgeN
public import Theorems.Thm_BornVolume_measurable_gBlock
public import Theorems.Thm_BornVolume_gBlock_map_pi
public import Theorems.Thm_MeasureTheory_map_curryProd_pi


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BornVolume
namespace BornVolume
theorem _root_.solution {N : ℕ} :
    Measure.map (fun y : (Fin N × Fin 2) → ℝ => fun i => (y (i, 0)) ^ 2 + (y (i, 1)) ^ 2)
      (Measure.pi (fun _ : Fin N × Fin 2 => gaussianReal 0 1))
      = Measure.pi (fun _ : Fin N => expHalf) := by
  have hcurry : Measurable (fun y : (Fin N × Fin 2) → ℝ => fun i j => y (i, j)) := by
    apply measurable_pi_iff.mpr; intro i; apply measurable_pi_iff.mpr; intro j
    exact measurable_pi_apply (i, j)
  have hblock : Measurable
      (fun w : Fin N → Fin 2 → ℝ => fun i => gBlock (w i)) := by
    apply measurable_pi_iff.mpr; intro i
    exact measurable_gBlock.comp (measurable_pi_apply i)
  have hcomp : (fun y : (Fin N × Fin 2) → ℝ => fun i => (y (i, 0)) ^ 2 + (y (i, 1)) ^ 2)
      = (fun w : Fin N → Fin 2 → ℝ => fun i => gBlock (w i))
          ∘ (fun y : (Fin N × Fin 2) → ℝ => fun i j => y (i, j)) := by
    funext y; rfl
  rw [hcomp, ← Measure.map_map hblock hcurry,
    map_curryProd_pi (ν := fun _ : Fin N × Fin 2 => gaussianReal 0 1)]
  -- per-factor map: `map (fun w i => gBlock (w i)) (pi μ) = pi (fun i => map gBlock (μ i))`.
  have hsf : ∀ _i : Fin N,
      SigmaFinite (Measure.map gBlock (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1))) := by
    intro _i; rw [gBlock_map_pi]; infer_instance
  rw [Measure.pi_map_pi (f := fun _ : Fin N => gBlock)
    (fun _ => measurable_gBlock.aemeasurable)]
  simp only [gBlock_map_pi]
end BornVolume
