-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.brunn_minkowski_infinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:30.496824+00:00
-- url     : https://prove2.me/submissions/0fe14766-3871-428b-94fe-de07e1c8f595

module
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler
public import Definitions.Def_GaussianPerimeter_BrunnMinkowski

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution
    {d : ℕ} {A B C : Set (Fin (d + 1) → ℝ)}
    (hA : volume A = ⊤) (hB : B.Nonempty) (hABC : A + B ⊆ C)
    : (volume A)^((d:ℝ)+1)⁻¹ + (volume B)^((d:ℝ)+1)⁻¹ ≤ (volume C)^((d:ℝ)+1)⁻¹ := by
  have h_top_pow : (⊤ : ENNReal) ^ ((d : ℝ) + 1)⁻¹ = ⊤ :=
    ENNReal.top_rpow_of_pos Nat.inv_pos_of_nat
  calc
    (volume A)^((d:ℝ)+1)⁻¹ + (volume B)^((d:ℝ)+1)⁻¹ =
        (volume (A + {hB.some}))^((d:ℝ)+1)⁻¹ := by
      simp [hA, h_top_pow]
    _ ≤ (volume (A + B))^((d:ℝ)+1)⁻¹ := by gcongr; exact singleton_subset_iff.mpr hB.some_mem
    _ ≤ (volume C)^((d:ℝ)+1)⁻¹ := by gcongr
end GaussianPerimeter.VolumeComparison
