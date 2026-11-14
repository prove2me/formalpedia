-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a150_b0_true_fullcell_Hessian_cross_absolute_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:41:42.607662+00:00
-- url     : https://prove2.me/submissions/4b85e262-7ff3-4500-a8a1-2e765d4c7294

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a168_original_hessian_cross_L1_vanish_of_ae_band_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a169_original_true_fullcell_gaussian_raw_centered_square_cross_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a178_finite_aestrongly_measurable_weighted_Gaussian_cross_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a180_original_masked_gaussian_Hessian_uniform_measurable_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original physical zero-jump Gaussian Hessian correction is absolutely
integrable and vanishes in expected L1 through the true full pre-stop mask. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Err : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω then
        E (s i) * (iteratedDeriv 2 w (Y (s i)) / 2) * (R i^2 - Z i^2) else 0
    (∀ m, Integrable (fun ω => |Err m ω|) P) ∧
    Tendsto (fun m => ∫ ω, |Err m ω| ∂P) atTop (nhds (0 : ℝ)) := by
  classical
  intro Err
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
  let A : ℕ → ℕ → Ω → Prop := fun m i ω => s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω
  let R0 : ℕ → ℕ → Ω → ℝ := fun m i ω => X.X (s m i + Δ m) ω - X.X (s m i) ω
  let Z : ℕ → ℕ → Ω → ℝ := fun m i ω => R0 m i ω - (Δ m : ℝ) * X.c
  let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    if A m i ω then (R0 m i ω)^2 - (Z m i ω)^2 else 0
  let H : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    if A m i ω then Real.exp (-(q * (s m i : ℝ))) *
      iteratedDeriv 2 w (x + X.X (s m i) ω - rightLimit D (s m i) ω)
    else 0
  let Cross : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ Finset.range m,
    if A m i ω then |(R0 m i ω)^2 - (Z m i ω)^2| else 0
  obtain ⟨K,hK,hHm,hHb⟩ :=
    avram_ga_a180_original_masked_gaussian_Hessian_uniform_measurable_bound
      X x hx D hD.1.1 w C hTopCap hw_smooth q (le_of_lt hq)
      n ρ hρstop j hprefix
  have hρm := measurable_coe_nnreal_ennreal_iff.mp hρstop.measurable'
  have hA (m i : ℕ) : MeasurableSet {ω : Ω | A m i ω} := by
    have h1 : MeasurableSet {ω : Ω | s m i < ρ ω} :=
      (show MeasurableSet (Set.Ioi (s m i) : Set ℝ≥0)
        from measurableSet_Ioi).preimage hρm
    have h2 : MeasurableSet {ω : Ω | s m i + Δ m ≤ ρ ω} :=
      (show MeasurableSet (Set.Ici (s m i + Δ m) : Set ℝ≥0)
        from measurableSet_Ici).preimage hρm
    exact h1.inter h2
  have hR (m i : ℕ) : AEStronglyMeasurable (R m i) P := by
    have h0 := (X.adapted (s m i)).mono (𝓕.le _) le_rfl
    have h1 := (X.adapted (s m i + Δ m)).mono (𝓕.le _) le_rfl
    exact (Measurable.ite (hA m i)
      (((h1.sub h0).pow_const 2).sub
        (((h1.sub h0).sub measurable_const).pow_const 2))
      measurable_const).aestronglyMeasurable
  have hEnergy := avram_ga_a169_original_true_fullcell_gaussian_raw_centered_square_cross_L1
    X hNuZero n ρ hρstop
  change (∀ m, Integrable (Cross m) P) ∧
    Tendsto (fun m => ∫ ω, Cross m ω ∂P)
      atTop (𝓝 (0 : ℝ)) at hEnergy
  have hEqCross (m : ℕ) (ω : Ω) :
      (∑ i ∈ Finset.range m, |R m i ω|) = Cross m ω := by
    simp [R,Cross,abs_ite]
  have hRI (m : ℕ) :
      Integrable (fun ω => ∑ i ∈ Finset.range m, |R m i ω|) P :=
    (hEnergy.1 m).congr (Filter.Eventually.of_forall (fun ω => (hEqCross m ω).symm))
  have hRL : Tendsto (fun m => ∫ ω, (∑ i ∈ Finset.range m, |R m i ω|) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
    convert hEnergy.2 using 1
    funext m; exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => hEqCross m ω))
  have hWeightI := avram_ga_a178_finite_aestrongly_measurable_weighted_Gaussian_cross_integrable
    P (fun m => Finset.range m) H R K hK hHm hR hHb hRI
  have hWeightL := avram_ga_a168_original_hessian_cross_L1_vanish_of_ae_band_bound
    P (fun m => Finset.range m) H R K hK hHb hWeightI hRI hRL
  have hEq (m : ℕ) (ω : Ω) :
      Err m ω = ∑ i ∈ Finset.range m, H m i ω / 2 * R m i ω := by
    dsimp [Err]; apply Finset.sum_congr rfl
    intro i _; by_cases ha : A m i ω
    · dsimp [H,R,A,R0,Z,Δ,s] at *
      simp only [if_pos ha]; ring
    · dsimp [H,R,A,R0,Z,Δ,s] at *
      simp [ha]
  refine ⟨(fun m => (hWeightI m).congr
    (Filter.Eventually.of_forall (fun ω => by
      first | exact congrArg abs (hEq m ω) | exact (congrArg abs (hEq m ω)).symm))),?_⟩
  convert hWeightL using 1
  funext m; exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => by
      first | exact congrArg abs (hEq m ω) | exact (congrArg abs (hEq m ω)).symm))
