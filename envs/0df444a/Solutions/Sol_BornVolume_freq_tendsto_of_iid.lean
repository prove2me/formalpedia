-- Prove2me | solution 1 for BornVolume.freq_tendsto_of_iid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:52.229935+00:00
-- url     : https://prove2.me/submissions/5cac2eed-9d8e-4135-ac5a-2449ea86e807

module
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_BornVolumeLean_Volume_BornFrequency

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
open BornVolume
namespace BornVolume
theorem _root_.solution
    {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → S} (hX : ∀ n, Measurable (X n))
    {μp : Measure S} (hlaw : ∀ n, Measure.map (X n) P = μp)
    {O : Set S} (hO : MeasurableSet O)
    (hindep :
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g P)
          (fun n => Set.indicator (X n ⁻¹' O) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ P,
      Tendsto
        (fun N : ℕ =>
          (∑ i ∈ Finset.range N,
              Set.indicator (X i ⁻¹' O) (fun _ => (1 : ℝ)) ω) / (N : ℝ))
        atTop
        (nhds (μp O).toReal) := by
  -- The indicator of trial 0 is bounded, hence integrable.
  have hint : Integrable (Set.indicator (X 0 ⁻¹' O) (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).mono
      ((measurable_const.indicator (hO.preimage (hX 0))).aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        by_cases hω : ω ∈ X 0 ⁻¹' O
        · simp [Set.indicator_of_mem hω]
        · simp [Set.indicator_of_notMem hω])
  -- Each indicator is `(indicator O 1) ∘ X n`, and all `X n` have law `μp`.
  have hident : ∀ n,
      IdentDistrib (Set.indicator (X n ⁻¹' O) (fun _ => (1 : ℝ)))
        (Set.indicator (X 0 ⁻¹' O) (fun _ => (1 : ℝ))) P P := fun n => by
    have hfact : ∀ m,
        Set.indicator (X m ⁻¹' O) (fun _ => (1 : ℝ))
          = (Set.indicator O (fun _ => (1 : ℝ))) ∘ X m := fun m => by
      funext ω
      simp only [Function.comp]
      by_cases hω : X m ω ∈ O
      · rw [Set.indicator_of_mem (Set.mem_preimage.mpr hω), Set.indicator_of_mem hω]
      · rw [Set.indicator_of_notMem (fun h => hω (Set.mem_preimage.mp h)),
            Set.indicator_of_notMem hω]
    have hXident : IdentDistrib (X n) (X 0) P P :=
      ⟨(hX n).aemeasurable, (hX 0).aemeasurable, by rw [hlaw n, hlaw 0]⟩
    rw [hfact n, hfact 0]
    exact hXident.comp (measurable_const.indicator hO)
  -- The strong law: the empirical mean converges to the mean of trial 0.
  have hSLLN :=
    strong_law_ae_real
      (fun n => Set.indicator (X n ⁻¹' O) (fun _ => (1 : ℝ)))
      hint hindep hident
  -- That mean is `(μp O).toReal`.
  have hmean :
      ∫ ω, Set.indicator (X 0 ⁻¹' O) (fun _ => (1 : ℝ)) ω ∂ P = (μp O).toReal := by
    have h1 :
        ∫ ω, Set.indicator (X 0 ⁻¹' O) (fun _ => (1 : ℝ)) ω ∂ P
          = (P (X 0 ⁻¹' O)).toReal := by
      rw [integral_indicator (hO.preimage (hX 0)), setIntegral_const, smul_eq_mul, mul_one]
      simp [Measure.real]
    rw [h1, ← Measure.map_apply (hX 0) hO, hlaw 0]
  filter_upwards [hSLLN] with ω hω
  rwa [hmean] at hω
end BornVolume
