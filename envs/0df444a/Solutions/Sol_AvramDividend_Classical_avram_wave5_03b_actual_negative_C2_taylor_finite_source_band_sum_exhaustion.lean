-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_negative_C2_taylor_finite_source_band_sum_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:09:16.33591+00:00
-- url     : https://prove2.me/submissions/60f29213-0ae4-434c-a7f9-1ed52c432976

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_separated_band_absolute_taylor_intrinsic_eq_finite_source_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_absolute_taylor_source_jump_band_exhaustion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The genuinely original stopped nonlinear jump Taylor correction is the
supremum of increasing finite sums over its own separated source jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (B : ℕ → Set ℝ) (hBmeas : ∀ n, MeasurableSet (B n))
    (hBmono : Monotone B)
    (hBcover : ∀ z : ℝ, z < 0 ↔ ∃ n : ℕ, z ∈ B n)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hBsep : ∀ n z, z ∈ B n → ε n ≤ dist z 0)
    (s t : ℝ≥0) (ω : Ω) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let J : ℝ≥0 → Ω → ℝ := fun r η =>
      X.X r η - Function.leftLim (fun z : ℝ≥0 => X.X z η) r
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun η =>
      ((Measure.count.restrict {r : ℝ≥0 | 0 < r ∧ J r η ≠ 0}).map
        (fun r : ℝ≥0 => (r, J r η)))
    ∃ T : ℕ → Finset ℝ≥0,
      (∀ (n : ℕ) (r : ℝ≥0), r ∈ T n ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B n) ∧
      (∀ n : ℕ, T n ⊆ T (n + 1)) ∧
      (⨆ n : ℕ, ∑ r ∈ T n, ENNReal.ofReal (|HS ((r,ω),J r ω)|)) =
      (∫⁻ p : ℝ≥0 × ℝ,
        (if s < p.1 ∧ p.1 ≤ t ∧ p.2 < 0 then
          ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω) := by
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0) else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  let J : ℝ≥0 → Ω → ℝ := fun r η =>
    X.X r η - Function.leftLim (fun z : ℝ≥0 => X.X z η) r
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun η =>
    ((Measure.count.restrict {r : ℝ≥0 | 0 < r ∧ J r η ≠ 0}).map
      (fun r : ℝ≥0 => (r, J r η)))
  change ∃ T : ℕ → Finset ℝ≥0,
      (∀ (n : ℕ) (r : ℝ≥0), r ∈ T n ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B n) ∧
      (∀ n : ℕ, T n ⊆ T (n + 1)) ∧
      (⨆ n : ℕ, ∑ r ∈ T n, ENNReal.ofReal (|HS ((r,ω),J r ω)|)) =
      (∫⁻ p : ℝ≥0 × ℝ,
        (if s < p.1 ∧ p.1 ≤ t ∧ p.2 < 0 then
          ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω)
  have hBneg (n : ℕ) : B n ⊆ Iio (0 : ℝ) := by
    intro z hz
    exact (hBcover z).2 ⟨n, hz⟩
  have hFinite (n : ℕ) :
      ∃ F : Finset ℝ≥0,
        (∀ r : ℝ≥0, r ∈ F ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B n) ∧
        (∫⁻ p : ℝ≥0 × ℝ,
          (if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B n then
            ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω) =
        ∑ r ∈ F, ENNReal.ofReal (|HS ((r,ω),J r ω)|) := by
    simpa only [Y, H, HS, J, NX] using
      (avram_wave5_03b_actual_separated_band_absolute_taylor_intrinsic_eq_finite_source_sum
        X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
        s t ω (B n) (hBmeas n) (hBneg n) (ε n) (hε n)
        (hBsep n))
  choose T hT hEq using hFinite
  refine ⟨T, hT, ?_, ?_⟩
  · intro n r hr
    obtain ⟨hrs, hrt, hrB⟩ := (hT n r).mp hr
    exact (hT (n+1) r).mpr ⟨hrs, hrt, hBmono (Nat.le_succ n) hrB⟩
  · have hlim :
        (⨆ n : ℕ,
          (∫⁻ p : ℝ≥0 × ℝ,
            (if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B n then
              ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω)) =
        (∫⁻ p : ℝ≥0 × ℝ,
          (if s < p.1 ∧ p.1 ≤ t ∧ p.2 < 0 then
            ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω) := by
        simpa only [Y, H, HS, J, NX] using
          (avram_wave5_03b_actual_ruin_stopped_absolute_taylor_source_jump_band_exhaustion
            X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
            B hBmeas hBmono hBcover s t ω)
    calc
      (⨆ n : ℕ, ∑ r ∈ T n, ENNReal.ofReal (|HS ((r,ω),J r ω)|)) =
        (⨆ n : ℕ, (∫⁻ p : ℝ≥0 × ℝ,
          (if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B n then
            ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω)) := by
          apply iSup_congr
          intro n
          exact (hEq n).symm
      _ = _ := hlim
