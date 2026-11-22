-- Prove2me | solution 1 for BornVolume.pi_gaussianReal_prod_singleton_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:29.027597+00:00
-- url     : https://prove2.me/submissions/1c54c5f7-38e0-48c5-a5a9-a7ade1e5af83

module
public import Definitions.Def_BornVolumeLean_Volume_GaussianCPN
public import Definitions.Def_BornVolumeLean_Volume_MomentMap
public import Definitions.Def_BornVolumeLean_Volume_MomentRatioUniformN
public import Definitions.Def_BornVolumeLean_Volume_MomentBridgeN
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution :
    Measure.pi (fun _ : Fin (M + 1) × Fin 2 => gaussianReal 0 1)
        {(0 : (Fin (M + 1) × Fin 2) → ℝ)} = 0 := by
  rw [show ({(0 : (Fin (M + 1) × Fin 2) → ℝ)} : Set ((Fin (M + 1) × Fin 2) → ℝ))
        = Set.univ.pi (fun _ => {(0 : ℝ)}) by
      ext f; simp only [Set.mem_singleton_iff, Set.mem_univ_pi, funext_iff]; rfl,
    Measure.pi_pi]
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  exact Finset.prod_eq_zero (Finset.mem_univ ((0 : Fin (M + 1)), (0 : Fin 2)))
    (measure_singleton _)
end BornVolume
