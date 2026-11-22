-- Prove2me | solution 1 for BornVolume.born_frequencies_tendsto_born_weights
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:47.814817+00:00
-- url     : https://prove2.me/submissions/91137f62-d885-4016-8c85-05e9112dee74

module
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_BornVolumeLean_Volume_BornFrequency
public import Theorems.Thm_BornVolume_freq_tendsto_of_iid
public import Theorems.Thm_BornVolume_measurableSet_bornCell
public import Theorems.Thm_BornVolume_measure_bornCell

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (μ : Measure (CPN (M + 1)))
    [IsProbabilityMeasure μ]
    (hμ : ∀ U : Matrix.unitaryGroup (Fin (M + 1)) ℂ, Measure.map (fun p => U • p) μ = μ)
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = μ)
    (hindep : Pairwise fun m n => IndepFun (X m) (X n) Pr) :
    ∀ᵐ ω ∂Pr, ∀ i : Fin (M + 1),
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m, Set.indicator (bornCell ψ i) (fun _ => (1 : ℝ)) (X k ω))
            / (m : ℝ))
        atTop (nhds (‖ψ i‖ ^ 2)) := by
  rw [ae_all_iff]
  intro i
  have hO := measurableSet_bornCell ψ i
  have hfact : ∀ n, Set.indicator (X n ⁻¹' bornCell ψ i) (fun _ => (1 : ℝ))
      = Set.indicator (bornCell ψ i) (fun _ => (1 : ℝ)) ∘ X n := fun n => by
    funext ω
    by_cases hω : X n ω ∈ bornCell ψ i
    · rw [Function.comp_apply, Set.indicator_of_mem (Set.mem_preimage.mpr hω),
        Set.indicator_of_mem hω]
    · rw [Function.comp_apply, Set.indicator_of_notMem (fun h => hω (Set.mem_preimage.mp h)),
        Set.indicator_of_notMem hω]
  have hmeas : Measurable (Set.indicator (bornCell ψ i) (fun _ => (1 : ℝ))) :=
    measurable_const.indicator hO
  have hind : Pairwise
      (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator (X n ⁻¹' bornCell ψ i) (fun _ => (1 : ℝ)))) := by
    intro m n hmn
    simp only [Function.onFun, hfact]
    exact (hindep hmn).comp hmeas hmeas
  have hfreq := freq_tendsto_of_iid hX hlaw hO hind
  rw [measure_bornCell μ hμ ψ hψ i, ENNReal.toReal_ofReal (sq_nonneg _)] at hfreq
  filter_upwards [hfreq] with ω hω
  simpa only [hfact, Function.comp_apply] using hω
end BornVolume
