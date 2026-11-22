-- Prove2me | solution 1 for BornVolume.measure_bornCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:53.779172+00:00
-- url     : https://prove2.me/submissions/5880aaf1-4cbb-4d94-85a5-1b48197c2524

module
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_BornVolumeLean_Volume_BornFrequency
public import Theorems.Thm_BornVolume_born_weight_eq_measure_apexCell
public import Theorems.Thm_BornVolume_born_weight_eq_measure_cell


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (μ : Measure (CPN (M + 1))) [IsProbabilityMeasure μ]
    (hμ : ∀ U : Matrix.unitaryGroup (Fin (M + 1)) ℂ, Measure.map (fun p => U • p) μ = μ)
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ : ‖ψ‖ = 1) (i : Fin (M + 1)) :
    μ (bornCell ψ i) = ENNReal.ofReal (‖ψ i‖ ^ 2) := by
  induction i using Fin.lastCases with
  | last =>
    rw [bornCell, Fin.lastCases_last]
    exact born_weight_eq_measure_apexCell μ hμ ψ hψ
  | cast k =>
    rw [bornCell, Fin.lastCases_castSucc]
    exact born_weight_eq_measure_cell μ hμ ψ hψ k
end BornVolume
