-- Prove2me | solution 1 for AvramDividend.Classical.avram_b29_BV_finitecap_infinite_activity_strict_signed_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T17:59:42.689398+00:00
-- url     : https://prove2.me/submissions/7d6dcaa1-1530-4225-bfb1-17b9ea077673
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva43_original_BV_physical_signed_two_error_mesh_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (hwpos : 0 < w x)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hFinite : C ≠ ⊤)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let S : ℝ≥0 := ⟨T, hT⟩
    ∃ u : ℕ → ℝ,
      Monotone u ∧
      (∀ n, 0 ≤ u n) ∧
      (∀ n, u n < T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < u n) ∧
      ∃ R J Err : ℕ → Ω → ℝ,
        (∀ n, Integrable (fun ω => R n ω + J n ω) P ∧
          (∫ ω, R n ω + J n ω ∂P) ≤ 0) ∧
        (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
        Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P)
          atTop (𝓝 (0 : ℝ)) ∧
        (∀ n, ∀ᵐ ω ∂P,
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
           else 0) ≤
            w x + (R n ω + J n ω) + max (Err n ω) 0) := by
  classical
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let u : ℕ → ℝ := fun n => T - δ n
  obtain ⟨hδpos, hδle, hδanti, hδlim⟩ :=
    avram_p3_grid3_strict_prefix_margin_sequence T hTpos
  obtain ⟨N, A, B, hNI, hAI, hBI, hBudget, hA0, hB0⟩ :=
    avram_bva43_original_BV_physical_signed_two_error_mesh_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump T hTpos hInfinite
  have huMono : Monotone u := by
    intro i j hij; exact sub_le_sub_left (hδanti hij) T
  have huNonneg : ∀ n, 0 ≤ u n := by
    intro n; exact sub_nonneg.mpr (hδle n)
  have huLt : ∀ n, u n < T := by
    intro n; exact sub_lt_self T (hδpos n)
  have huLim : Tendsto u atTop (𝓝 T) := by
    simpa only [u, sub_zero] using tendsto_const_nhds.sub hδlim
  have huCofinal : ∀ s : ℝ, s < T → ∃ n, s < u n := by
    intro s hs
    have he : ∀ᶠ n in atTop, u n ∈ Ioi s :=
      huLim.eventually (isOpen_Ioi.mem_nhds hs)
    exact he.exists
  let Err : ℕ → Ω → ℝ := fun n ω => max (A n ω) 0 + max (B n ω) 0
  have hErrNonneg : ∀ n ω, 0 ≤ Err n ω := by
    intro n ω; exact add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hErrEq : ∀ n ω, max (Err n ω) 0 = Err n ω := by
    intro n ω; exact max_eq_left (hErrNonneg n ω)
  have hErrI : ∀ n, Integrable (fun ω => max (Err n ω) 0) P := by
    intro n
    have hSum : Integrable (Err n) P := (hAI n).add (hBI n)
    apply hSum.congr
    filter_upwards [] with ω
    exact (hErrEq n ω).symm
  have hEqInt : ∀ n, (∫ ω, Err n ω ∂P) =
      (∫ ω, max (A n ω) 0 ∂P) + (∫ ω, max (B n ω) 0 ∂P) :=
    fun n => integral_add (hAI n) (hBI n)
  have hELim0 : Tendsto (fun n => ∫ ω, Err n ω ∂P) atTop (𝓝 0) := by
    simpa only [hEqInt, zero_add] using hA0.add hB0
  have hELim : Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (𝓝 0) := by
    simpa only [hErrEq] using hELim0
  refine ⟨u, huMono, huNonneg, huLt, huCofinal,
    N, (fun _ _ => 0), Err, ?_, hErrI, hELim, ?_⟩
  · intro n; simpa only [add_zero] using hNI n
  · intro n
    filter_upwards [hBudget n] with ω hω
    have hEq := hErrEq n ω
    convert hω using 1 <;> simp [u, δ, Err, NNReal.coe_mk, hEq, add_assoc] <;> rfl
