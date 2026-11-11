-- Prove2me | solution 2 for AvramDividend.Classical.avram_bvb_phys50_original_fullmask_jump_count_integrable_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T15:20:25.298962+00:00
-- url     : https://prove2.me/submissions/6d92255e-1e97-4acc-bb70-d8371629207a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys51_original_actual_negative_count_L1
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys52_original_fullmask_jump_integral_count_domination
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Separate the finite-activity fullmask count moment from the pathwise
domination of the original stopped marked-jump reward integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
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
    let N : Ω → ℝ := fun ω =>
      ((NX ω) (Ioc (0 : ℝ≥0) (Real.toNNReal T) ×ˢ Iio (0 : ℝ))).toReal
    ∃ K : ℝ, 0 ≤ K ∧ Integrable N P ∧
      ∀ n : ℕ, ∀ᵐ ω ∂P, ‖J n ω‖ ≤ K * N ω := by
  intro δ U H NX J N
  obtain ⟨K, hK, hMajorant⟩ :=
    avram_bvb_phys52_original_fullmask_jump_integral_count_domination
      X hBV q hq w C hC hFinite hw_cont hw_neg x D hD T hT hActivity
  refine ⟨K, hK, ?_, hMajorant⟩
  simpa only [N, NX] using
    (avram_bvb_phys51_original_actual_negative_count_L1
      X hBV (Real.toNNReal T) hActivity)
