-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb81b_original_topcap_negative_mark_kernel_antitone_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:22:11.843068+00:00
-- url     : https://prove2.me/submissions/febc3d7d-1124-4967-a5f9-449c2e210a0b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys128_original_stopped_compensator_negative_mark_kernel_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/- Nonpositive original negative-mark kernel grows more negative as its
   deterministic physical prefix window T-T/(n+2) widens. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hIntensityPositive : 0 < X.ν (Iio (0 : ℝ)))
    (hCapTop : C = ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let J : ℕ → Ω → ℝ := fun n ω =>
      ∫ p, H n ((p.1, ω), p.2) ∂(NX ω)
    let V : ℕ → Ω → ℝ := fun n ω =>
      ∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    ∀ n m : ℕ, n ≤ m → ∀ t : ℝ≥0, ∀ ω : Ω, ∀ z : ℝ,
      H m ((t, ω), z) ≤ H n ((t, ω), z) := by
  classical
  intro δ U H NX J V n m hnm t ω z
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hDen : (n : ℝ) + 2 ≤ (m : ℝ) + 2 := by linarith
  have hδ : δ m ≤ δ n := by
    change T / ((m : ℝ) + 2) ≤ T / ((n : ℝ) + 2)
    exact div_le_div_of_nonneg_left hT.le (by positivity) hDen
  have hCut : T - δ n ≤ T - δ m := sub_le_sub_left hδ T
  have hmNeg : H m ((t, ω), z) ≤ 0 := by
    have h :=
      avram_bvb_phys128_original_stopped_compensator_negative_mark_kernel_nonpos
        C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
        q (T - δ m) t (U t ω) z (ruinTime X x D ω)
    simpa only [H] using h
  by_cases hn :
      0 < t ∧ (t : ℝ) < T - δ n ∧
      (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
      0 ≤ U t ω ∧ ENNReal.ofReal (U t ω) ≤ C ∧ z < 0
  · have hnCopy := hn
    rcases hn with ⟨ht0, htcut, htRu, htU, htC, htz⟩
    have hm :
        0 < t ∧ (t : ℝ) < T - δ m ∧
        (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
        0 ≤ U t ω ∧ ENNReal.ofReal (U t ω) ≤ C ∧ z < 0 :=
      ⟨ht0, lt_of_lt_of_le htcut hCut, htRu, htU, htC, htz⟩
    simp only [H, if_pos hnCopy, if_pos hm, le_refl]
  · have hZero : H n ((t, ω), z) = 0 := by
      simp only [H, if_neg hn]
    rw [hZero]
    exact hmNeg
