-- Prove2me | solution 2 for AvramDividend.Classical.avram_gfinite49_original_positive_clock_cash_mesh_error
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:48:00.830971+00:00
-- url     : https://prove2.me/submissions/f33ad314-7b5b-4117-b4cf-63b3bd7c7aae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_gfinite57_original_fixed_band_positive_excess_with_strip_drift
import Theorems.Thm_AvramDividend_Classical_avram_gfinite45_original_cash_residual_integrable
import Theorems.Thm_AvramDividend_Classical_avram_gfinite56_cap_fraction_cutoff_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_gfinite49_cofinal_positive_error_diagonal
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_corner_scalar_defect_tendsto_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0))) (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ σ k ω)
      (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω → δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      ∃ (N : ℕ → ℕ),
        let Δ : ℕ → ℝ≥0 := fun j => (n : ℝ≥0) / ((N j + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℕ → ℝ≥0 := fun j i => (i : ℝ≥0) * Δ j
        let a : ℝ := δ / 2
        let b : ℕ → ℝ := fun j => C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → ℕ → Ω → ℝ := fun j i ω => x + X.X (s j i) ω - rightLimit D (s j i) ω
        let Z : ℕ → ℕ → Ω → ℝ := fun j i ω => X.X (s j i + Δ j) ω - X.X (s j i) ω - (Δ j : ℝ) * X.c
        let G : ℕ → ℕ → Ω → ℝ := fun j i ω => if s j i < ρ ω then Real.exp (-(q * (s j i : ℝ))) * (if Y j i ω ∈ Icc a (b j) then deriv w (Y j i ω) else 1) else 0
        let H : ℕ → ℕ → Ω → ℝ := fun j i ω => if s j i < ρ ω then (1 / 2 : ℝ) * Real.exp (-(q * (s j i : ℝ))) * (if Y j i ω ∈ Icc a (b j) then iteratedDeriv 2 w (Y j i ω) else 0) else 0
        let M : ℕ → Ω → ℝ := fun j ω => (Finset.range (N j + 1)).sum
          (fun i => G j i ω * Z j i ω + H j i ω * (Z j i ω ^ 2 - (Δ j : ℝ) * X.σ ^ 2))
        let F : Ω → ℝ := fun ω => if ρ ω = 0 then w x else
          Real.exp (-(q * (ρ ω : ℝ))) * w (riskProcess X x D (ρ ω) ω) +
          (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * z))) ∂(dividendMeasure D ω)).toReal
        StrictMono N ∧
        ∃ (E : ℕ → Ω → ℝ), (∀ j, IntegrableOn (E j) A P) ∧
          Tendsto (fun j => ∫ ω in A, max (E j ω) 0 ∂P) atTop (𝓝 (0 : ℝ)) ∧
          (∀ j, ∀ᵐ ω ∂(P.restrict A), ρ ω ≠ 0 → F ω ≤ w x + M j ω + E j ω) ∧ (∀ j ω, ρ ω = 0 → E j ω = 0) := by
  intro k ρ hρstop hρle δ hδ hFloor A hA
  let F : Ω → ℝ := fun ω => if ρ ω = 0 then w x else
    Real.exp (-(q * (ρ ω : ℝ))) * w (riskProcess X x D (ρ ω) ω) +
    (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * z))) ∂(dividendMeasure D ω)).toReal
  let b : ℕ → ℝ := fun j => C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let Mb : ℕ → ℕ → Ω → ℝ := fun j m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Y : ℕ → Ω → ℝ := fun i η => x + X.X (s i) η - rightLimit D (s i) η
    let Z : ℕ → Ω → ℝ := fun i η => X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
    let G : ℕ → Ω → ℝ := fun i η => if s i < ρ η then Real.exp (-(q * (s i : ℝ))) * (if Y i η ∈ Icc (δ / 2) (b j) then deriv w (Y i η) else 1) else 0
    let H : ℕ → Ω → ℝ := fun i η => if s i < ρ η then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) * (if Y i η ∈ Icc (δ / 2) (b j) then iteratedDeriv 2 w (Y i η) else 0) else 0
    (Finset.range (m + 1)).sum (fun i => G i ω * Z i ω + H i ω * (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
  obtain ⟨η, hη, hstrip⟩ := avram_gfinite57_original_fixed_band_positive_excess_with_strip_drift
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop σ hσstop hσle
      k ρ hρstop hρle δ hδ hFloor A hA
  let defect : ℕ → ℝ := fun j => (w C.toReal - w (b j)) - (C.toReal - b j)
  let theta : ℕ → ℝ := fun j => defect j + η j
  let eps : ℕ → ℝ := fun j => 1 / ((j + 1 : ℕ) : ℝ)
  have hc : 0 < C.toReal := ENNReal.toReal_pos (ne_of_gt hC) hFiniteCap
  have hb : Tendsto b atTop (𝓝 C.toReal) := by
    simpa only [b] using avram_gfinite56_cap_fraction_cutoff_tendsto C.toReal
  have hdefect : Tendsto defect atTop (𝓝 (0 : ℝ)) := avram_p3_grid4_finite_cap_corner_scalar_defect_tendsto_zero w C.toReal hc hw_cont b hb
  have htheta : Tendsto theta atTop (𝓝 (0 : ℝ)) := by simpa only [theta, zero_add] using hdefect.add hη
  have heps : Tendsto eps atTop (𝓝 (0 : ℝ)) := by simpa [eps, Nat.cast_add] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlocal : ∀ j K : ℕ, ∃ m : ℕ, K < m ∧ ∃ E : Ω → ℝ,
      IntegrableOn E A P ∧ (∀ᵐ ω ∂(P.restrict A), F ω ≤ w x + Mb j m ω + E ω) ∧
      (∫ ω in A, max (E ω) 0 ∂P) ≤ theta j + eps j := by
    intro j K
    obtain ⟨m, hm, hbound⟩ := hstrip j (eps j) (by positivity) K
    let E : Ω → ℝ := fun ω => max (F ω - w x - Mb j m ω) 0
    have hEi : IntegrableOn E A P := by
      have hi := avram_gfinite45_original_cash_residual_integrable
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
        x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop σ hσstop hσle
        k ρ hρstop hρle δ hδ hFloor A hA (fun _ => m) j
      simpa only [E, F, Mb, b] using hi
    refine ⟨m, hm, E, hEi, ?_, ?_⟩
    · exact Filter.Eventually.of_forall (fun ω => by
        have hm := le_max_left (F ω - w x - Mb j m ω) (0 : ℝ)
        dsimp only [E]; linarith)
    · simpa only [E, F, Mb, b, theta, defect, eps, max_assoc, max_self] using hbound
  obtain ⟨N, hmono, E, hEi, hmean, hpath⟩ :=
    avram_gfinite49_cofinal_positive_error_diagonal P A F (w x) Mb theta eps
      htheta heps hlocal
  have hρmeas : Measurable (fun ω => (ρ ω : WithTop ℝ≥0)) := hρstop.measurable'
  have hzero : MeasurableSet {ω : Ω | ρ ω = 0} := by
    have hpre : MeasurableSet {ω : Ω | (ρ ω : WithTop ℝ≥0) = 0} := hρmeas (measurableSet_singleton 0)
    simpa only [WithTop.coe_eq_zero] using hpre
  let E' : ℕ → Ω → ℝ := fun j ω => if ρ ω = 0 then 0 else E j ω
  have hEi' (j : ℕ) : IntegrableOn (E' j) A P := by
    have hmask : E' j = ({ω : Ω | ρ ω = 0}ᶜ).indicator (E j) := by
      funext ω; by_cases hω : ρ ω = 0 <;> simp [E', Set.indicator, hω]
    rw [hmask]; exact (hEi j).indicator hzero.compl
  have hpos (j : ℕ) : IntegrableOn (fun ω => max (E j ω) 0) A P := by
    have hI : IntegrableOn (fun ω => (E j ω + |E j ω|) / 2) A P := ((hEi j).add (hEi j).abs).div_const 2
    convert hI using 1
    funext ω
    rcases le_total 0 (E j ω) with hω | hω
    · rw [max_eq_left hω, abs_of_nonneg hω]; ring
    · rw [max_eq_right hω, abs_of_nonpos hω]; ring
  have hnonneg (j : ℕ) : 0 ≤ (∫ ω in A, max (E' j ω) 0 ∂P) :=
    integral_nonneg (fun ω => le_max_right _ _)
  have hle (j : ℕ) : (∫ ω in A, max (E' j ω) 0 ∂P) ≤
      (∫ ω in A, max (E j ω) 0 ∂P) := by
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun ω => le_max_right _ _)
    · exact hpos j
    · exact ae_of_all _ (fun ω => by dsimp [E']; split_ifs <;> simp)
  have hmean' : Tendsto (fun j => ∫ ω in A, max (E' j ω) 0 ∂P) atTop (𝓝 (0 : ℝ)) := squeeze_zero hnonneg hle hmean
  refine ⟨N, ?_⟩; dsimp only
  refine ⟨hmono, E', hEi', hmean', ?_, ?_⟩
  · intro j
    filter_upwards [hpath j] with ω hω
    intro hρ
    simpa only [F, Mb, b, E', if_neg hρ] using hω
  · intro j ω hρ; simp [E', hρ]
