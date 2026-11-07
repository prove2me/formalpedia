-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_original_stopped_signed_single_residual_mesh
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:29:31.951221+00:00
-- url     : https://prove2.me/submissions/8fbca591-84c8-45c9-9025-4558fc458a47
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_avram_redux3_bv_finite_cap_stopped_triple_mesh_source
import Theorems.Thm_AvramDividend_Classical_avram_redux3_bv_top_cap_stopped_triple_mesh_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

private theorem single_signed_of_triple
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Ymesh Mmesh Bmesh : ℕ → Ω → ℝ)
    (Y M B DM DB : Ω → ℝ) (K : ℝ)
    (hMm : ∀ n, AEStronglyMeasurable (Mmesh n) P)
    (hBm : ∀ n, AEStronglyMeasurable (Bmesh n) P)
    (hDM : Integrable DM P) (hDB : Integrable DB P)
    (hMd : ∀ n, ∀ᵐ ω ∂P, |Mmesh n ω| ≤ DM ω)
    (hBd : ∀ n, ∀ᵐ ω ∂P, |Bmesh n ω| ≤ DB ω)
    (hY : ∀ᵐ ω ∂P, Tendsto (fun n => Ymesh n ω) atTop (nhds (Y ω)))
    (hM : ∀ᵐ ω ∂P, Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω)))
    (hB : ∀ᵐ ω ∂P, Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω)))
    (hMzero : ∀ n, (∫ ω, Mmesh n ω ∂P) = 0)
    (hBneg : ∀ n, (∫ ω, Bmesh n ω ∂P) ≤ 0)
    (hPath : ∀ᵐ ω ∂P, ∀ n, Ymesh n ω ≤ K + Mmesh n ω + Bmesh n ω) :
    ∃ Y' Z' : ℕ → Ω → ℝ, ∃ Z DZ : Ω → ℝ,
      (∀ n, AEStronglyMeasurable (Z' n) P) ∧ Integrable DZ P ∧
      (∀ n, ∀ᵐ ω ∂P, |Z' n ω| ≤ DZ ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => Y' n ω) atTop (nhds (Y ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => Z' n ω) atTop (nhds (Z ω))) ∧
      (∀ n, (∫ ω, Z' n ω ∂P) ≤ 0) ∧
      (∀ᵐ ω ∂P, ∀ n, Y' n ω ≤ K + Z' n ω) := by
  refine ⟨Ymesh, (fun n ω => Mmesh n ω + Bmesh n ω),
    (fun ω => M ω + B ω), (fun ω => DM ω + DB ω), ?_,
    hDM.add hDB, ?_, hY, ?_, ?_, ?_⟩
  · intro n
    exact (hMm n).add (hBm n)
  · intro n
    filter_upwards [hMd n, hBd n] with ω hm hb
    exact (abs_add_le _ _).trans (add_le_add hm hb)
  · filter_upwards [hM, hB] with ω hm hb
    exact hm.add hb
  · intro n
    have hm : Integrable (Mmesh n) P := hDM.mono' (hMm n) (by
      filter_upwards [hMd n] with ω hw
      simpa only [Real.norm_eq_abs] using hw)
    have hb : Integrable (Bmesh n) P := hDB.mono' (hBm n) (by
      filter_upwards [hBd n] with ω hw
      simpa only [Real.norm_eq_abs] using hw)
    rw [integral_add hm hb, hMzero n, zero_add]
    exact hBneg n
  · filter_upwards [hPath] with ω hw
    intro n
    linarith [hw n]

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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let Y : Ω → ℝ := fun ω =>
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0)
    ∃ Ymesh Zmesh : ℕ → Ω → ℝ,
      ∃ Z DZ : Ω → ℝ,
        (∀ n, AEStronglyMeasurable (Zmesh n) P) ∧
        Integrable DZ P ∧
        (∀ n, ∀ᵐ ω ∂P, |Zmesh n ω| ≤ DZ ω) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Ymesh n ω) atTop (nhds (Y ω))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Zmesh n ω) atTop (nhds (Z ω))) ∧
        (∀ n, (∫ ω, Zmesh n ω ∂P) ≤ 0) ∧
        (∀ᵐ ω ∂P, ∀ n, Ymesh n ω ≤ w x + Zmesh n ω) := by
  classical
  by_cases hTop : C = ⊤
  · obtain ⟨Ym, Mm, Bm, M, B, DM, DB, hmm, hbm, hdm, hdb,
      hmd, hbd, hym, hm, hb, hmzero, hbneg, hpath⟩ :=
        avram_redux3_bv_top_cap_stopped_triple_mesh_source
          X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
          x hx hxc D hD hw_nonneg hjump T hT hTpos hTop
    exact single_signed_of_triple P Ym Mm Bm _ M B DM DB (w x)
      hmm hbm hdm hdb hmd hbd hym hm hb hmzero hbneg hpath
  · obtain ⟨Ym, Mm, Bm, M, B, DM, DB, hmm, hbm, hdm, hdb,
      hmd, hbd, hym, hm, hb, hmzero, hbneg, hpath⟩ :=
        avram_redux3_bv_finite_cap_stopped_triple_mesh_source
          X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
          x hx hxc D hD hw_nonneg hjump T hT hTpos hTop
    exact single_signed_of_triple P Ym Mm Bm _ M B DM DB (w x)
      hmm hbm hdm hdb hmd hbd hym hm hb hmzero hbneg hpath