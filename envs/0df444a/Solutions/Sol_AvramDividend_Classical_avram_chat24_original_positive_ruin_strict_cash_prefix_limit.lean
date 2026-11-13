-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_original_positive_ruin_strict_cash_prefix_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:39:09.924324+00:00
-- url     : https://prove2.me/submissions/d2e7f26b-741b-4467-a416-57506f0c5c9b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_real_cash_prefix_direct_limit
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) (hTop : C = ⊤) (δ : ℝ) (hδ : 0 < δ) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let a : ℝ := min δ 1 / 2
    let b : ℝ := x + δ + T * X.drift + 1
    let τ : Ω → ℝ≥0 := fun ω => (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim (fun s : ℝ≥0 => (x + δ) + X.X s p.2 - rightLimit D s p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0 then Real.exp (-(q * (p.1.1 : ℝ))) * (w (Y p.1 + p.2) - w (Y p.1)) else 0
    let μ : Measure ℝ≥0 := (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    let K : Ω → ℝ≥0 → ℝ := fun ω B => (∫⁻ t in Ico (0 : ℝ) (B : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let V : Ω → ℝ≥0 → ℝ := fun ω B => Real.exp (-(q * (B : ℝ))) * w (riskProcess X x D B ω + δ)
    let R : Ω → ℝ≥0 → ℝ := fun ω B => (∫ p, if (p.1 : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y (p.1, ω) ∈ Icc a b ∧ p.2 < 0 then Real.exp (-(q * (p.1 : ℝ))) * (w (Y (p.1, ω) + p.2) - w (Y (p.1, ω))) else 0 ∂(NX ω)) + (∫ t, if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y (t, ω) ∈ Icc a b then Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Y (t, ω)) - q * w (Y (t, ω))) else 0 ∂μ)
    let Kstop : Ω → ℝ := fun ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T, ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let J : Ω → ℝ := fun ω =>
      let z : ℝ := X.X (τ ω) ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) (τ ω)
      if Y (τ ω, ω) ∈ Icc a b ∧ z < 0 then Real.exp (-(q * (τ ω : ℝ))) * (w (Y (τ ω, ω) + z) - w (Y (τ ω, ω))) else 0
    ∀ᵐ ω ∂P, 0 < ruinTime X x D ω → ruinTime X x D ω ≤ (S : ℝ≥0∞) → ∀ u : ℕ → ℝ≥0, (∀ n, 0 < u n ∧ u n ≤ S ∧ (u n : ℝ≥0∞) < ruinTime X x D ω) → Monotone u → Tendsto u atTop (nhds (τ ω)) → Tendsto (fun n => K ω (u n)) atTop (nhds (Kstop ω)):= by

  classical
  let S : ℝ≥0 := ⟨T,hT⟩
  let τ : Ω → ℝ≥0 := fun ω => (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
  let K : Ω → ℝ≥0 → ℝ := fun ω B => (∫⁻ t in Ico (0 : ℝ) (B : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let Kstop : Ω → ℝ := fun ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T, ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  change ∀ᵐ ω ∂P, 0 < ruinTime X x D ω → ruinTime X x D ω ≤ (S : ℝ≥0∞) → ∀ u : ℕ → ℝ≥0, (∀ n, 0 < u n ∧ u n ≤ S ∧ (u n : ℝ≥0∞) < ruinTime X x D ω) → Monotone u → Tendsto u atTop (nhds (τ ω)) → Tendsto (fun n => K ω (u n)) atTop (nhds (Kstop ω))
  apply Filter.Eventually.of_forall
  intro ω hpos hle u hu hmono hlim
  have hfinite : ruinTime X x D ω ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hle ENNReal.coe_lt_top)
  let r : ℝ≥0 := (ruinTime X x D ω).toNNReal
  have hr : (r : ℝ≥0∞) = ruinTime X x D ω := ENNReal.coe_toNNReal hfinite
  have hrpos : 0 < r := by
    have hpos' : (0 : ℝ≥0∞) < (r : ℝ≥0∞) := by
      rw [hr]
      exact hpos
    exact_mod_cast hpos'
  have hrposR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrpos
  have hrleR : (r : ℝ) ≤ T := by
    have hle' : (r : ℝ≥0∞) ≤ (S : ℝ≥0∞) := by
      rw [hr]
      exact hle
    exact_mod_cast hle'
  have hτeq : τ ω = r := by
    simp only [τ, min_eq_left hle]
    exact rfl
  have huR (n : ℕ) : u n < r := by
    have h := (hu n).2.2
    rw [← hr] at h
    exact_mod_cast h
  let δ : ℕ → ℝ := fun n => (r : ℝ) - (u n : ℝ)
  have hδpos (n : ℕ) : 0 < δ n := by dsimp only [δ]; exact sub_pos.mpr (by exact_mod_cast huR n)
  have hδanti : Antitone δ := by intro i j hij; dsimp only [δ]; exact sub_le_sub_left (by exact_mod_cast hmono hij) (r : ℝ)
  have hlimr : Tendsto u atTop (nhds r) := by simpa only [hτeq] using hlim
  have hlimReal : Tendsto (fun n => (u n : ℝ)) atTop (nhds (r : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp hlimr
  have hδlim : Tendsto δ atTop (nhds (0 : ℝ)) := by
    have hd := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (r : ℝ))
      atTop (nhds (r : ℝ))).sub hlimReal
    simpa only [sub_self] using hd
  have hprefix (n : ℕ) : paymentTimes (ruinTime X x D ω) ∩ Iio (u n : ℝ) = Ico (0 : ℝ) (u n : ℝ) := by
    ext y
    rw [paymentTimes_eq_strict_of_pos _ hpos]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iio,
      Set.mem_Ico]
    constructor
    · rintro ⟨⟨hy0, -⟩, hyu⟩
      exact ⟨hy0, hyu⟩
    · rintro ⟨hy0, hyu⟩
      have hyr : y < (r : ℝ) := lt_trans hyu (by exact_mod_cast huR n)
      have hr' : ENNReal.ofReal y < (r : ℝ≥0∞) := by
        simpa using (ENNReal.ofReal_lt_ofReal_iff hrposR).2 hyr
      exact ⟨⟨hy0, by simpa only [hr] using hr'⟩, hyu⟩
  have hterminal : paymentTimes (ruinTime X x D ω) ∩ Iio (r : ℝ) = paymentTimes (ruinTime X x D ω) ∩ Iio T := by
    ext y
    rw [paymentTimes_eq_strict_of_pos _ hpos]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iio]
    constructor
    · rintro ⟨⟨hy0, hyrE⟩, hyr⟩
      exact ⟨⟨hy0, hyrE⟩, lt_of_lt_of_le hyr hrleR⟩
    · rintro ⟨⟨hy0, hyrE⟩, hyT⟩
      have hyrE' : ENNReal.ofReal y < (r : ℝ≥0∞) := by
        simpa only [hr] using hyrE
      exact ⟨⟨hy0, hyrE⟩,
        (ENNReal.ofReal_lt_ofReal_iff hrposR).1 (by simpa using hyrE')⟩
  have hCash := avram_p3_grid4_original_strict_real_cash_prefix_direct_limit X x C D hD ω q (le_of_lt hq) (r : ℝ) hrposR δ hδpos hδanti hδlim
  have hclock (n : ℕ) : (r : ℝ) - δ n = (u n : ℝ) := by simp only [δ]; ring
  change Tendsto (fun n => (∫⁻ y in Ico (0 : ℝ) (u n : ℝ), ENNReal.ofReal (Real.exp (-(q * y))) ∂(dividendMeasure D ω)).toReal) atTop (nhds ((∫⁻ y in paymentTimes (ruinTime X x D ω) ∩ Iio T, ENNReal.ofReal (Real.exp (-(q * y))) ∂(dividendMeasure D ω)).toReal))
  convert hCash using 1
  · funext n
    rw [hclock, hprefix]
  · rw [hterminal]

