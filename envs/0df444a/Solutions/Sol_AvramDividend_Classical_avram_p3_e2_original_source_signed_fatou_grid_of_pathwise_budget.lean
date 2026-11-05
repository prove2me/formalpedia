-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e2_original_source_signed_fatou_grid_of_pathwise_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:08:34.959571+00:00
-- url     : https://prove2.me/submissions/21999108-31d8-4485-a200-c3b478c4d956

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_measurable_version
import Theorems.Thm_AvramDividend_Classical_avram_p3_e2_original_signed_budget_real_horizon_bridge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

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

(τ : ℕ → Ω → ℝ≥0)
(hτBound : ∀ n ω, τ n ω ≤ (⟨T, hT⟩ : ℝ≥0))
(hτ : ∀ n, IsStoppingTime 𝓕.rightCont
  (fun ω => (τ n ω : WithTop ℝ≥0)))
(a b L R : ℕ → ℝ)
(ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
(hab : ∀ n, a n ≤ b n)
(hL : ∀ n, 0 ≤ L n) (hR : ∀ n, 0 ≤ R n)
(hLip : ∀ n, ∀ u ∈ Icc ((a n) / 2) (b n),
  ∀ v ∈ Icc ((a n) / 2) (b n), |w u - w v| ≤ L n * |u - v|)
(hWbound : ∀ n (v : ℝ), v ≤ b n → |w v| ≤ R n)
(hBand : ∀ n, Icc (a n) (b n) ⊆
  {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
(E : ℕ → Set (ℝ≥0 × Ω))
(hEm : ∀ n, MeasurableSet[𝓕.rightCont.predictable] (E n))
(hEregion : ∀ n, ∀ p ∈ E n,
  Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈
      Icc (a n) (b n))
(hEcap : ∀ n, ∀ p ∈ E n, ENNReal.ofReal
  (Function.leftLim (fun v : ℝ≥0 =>
    x + X.X v p.2 - rightLimit D v p.2) p.1) < C)
(Mmesh Bmesh : ℕ → Ω → ℝ)
(hSource : ∀ n, let Upre : ℝ≥0 × Ω → ℝ := (fun p : ℝ≥0 × Ω => Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1);
  let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := (fun p : (ℝ≥0 × Ω) × ℝ => if p.1 ∈ E n ∧ p.2 < 0 then Real.exp (-(q * (p.1.1 : ℝ))) * (w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) else 0);
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ n p.1.2 : ℝ≥0∞) then G p else 0;
  let F : ℝ≥0 × Ω → ℝ := (fun p : ℝ≥0 × Ω => if p ∈ E n then Real.exp (-(q * (p.1 : ℝ))) * (X.drift * deriv w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) + (∫ z in Iio (0 : ℝ), w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 + z) - w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) - q * w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)) else 0);
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)));
  let M : Ω → ℝ := fun ω => (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal));
  let B : Ω → ℝ := fun ω => (∫ t, F (t, ω) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)); Mmesh n = M ∧ Bmesh n = B)
(hPath : ∀ n, ∀ᵐ ω ∂P,
  let S : ℝ≥0 := ⟨T, hT⟩
  (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
    ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0) ≤ w x + Mmesh n ω + Bmesh n ω) :
    ∃ F M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ w x + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        ENNReal.ofReal (
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop)  := by
  have hq0 : 0 ≤ q := le_of_lt hq
  obtain ⟨F0, hFm, hFi, hFn, hFeq⟩ :=
    avram_p3_bv_original_strict_reward_measurable_version
      X hBV x C D hD w hw_cont hw_neg q hq0 T hT hTpos hw_nonneg
  refine ⟨fun _ => F0, Mmesh, Bmesh,
    (fun _ => hFm), (fun _ => hFi), (fun _ => hFn), ?_, ?_, ?_⟩
  · intro n
    have hBandWide : Icc ((a n) / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
      have hb : ENNReal.ofReal (b n) < C :=
        (hBand n ⟨hab n, le_rfl⟩).2
      intro y hy
      constructor
      · linarith [ha n, hy.1]
      · exact lt_of_le_of_lt (ENNReal.ofReal_mono hy.2) hb
    have hSigned :=
      avram_p3_e2_original_signed_budget_real_horizon_bridge
        X hBV T hT (τ n) (hτBound n) (hτ n)
        x C D hD w hw_cont hw_neg q hq0
        (a n) (b n) (ha n) (ha2 n) (hab n)
        (E n) (hEm n) (hEregion n)
        hw_smooth hBandWide hw_gen
    have hSrc := hSource n
    dsimp only at hSrc hSigned
    rcases hSrc with ⟨hM, hB⟩
    rcases hSigned with ⟨hMI, hMB⟩
    constructor
    · simpa [hM, hB] using hMI
    · simpa [hM, hB] using hMB
  · intro n
    filter_upwards [hFeq, hPath n] with ω heq hp
    dsimp only at heq hp
    rw [heq]
    calc
      _ ≤ w x + Mmesh n ω + Bmesh n ω := hp
      _ = w x + (Mmesh n ω + Bmesh n ω) := by rw [add_assoc]
  · filter_upwards [hFeq] with ω heq
    rw [heq]
    simp