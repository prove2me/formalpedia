-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_Taylor_component_to_signed_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:08:18.430809+00:00
-- url     : https://prove2.me/submissions/ebc48217-8ee1-487e-b334-fc43f889353f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_Taylor_compensated_mean_zero_from_P2
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_three_source_martingales
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ)) := fun ω =>
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω)
    ∀ (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hST : S = {p | p.1.1 ≤ T})
    (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (q : ℝ) (hq : 0 ≤ q),
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let J : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * J p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    let η : Measure ℝ≥0 := (((volume : Measure ℝ).restrict
      (Icc 0 (T : ℝ))).map Real.toNNReal)
    let Comp : Ω → ℝ := fun ω =>
      ∫ t, ∫ z, GW ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂η
    let Jump : Ω → ℝ := fun ω =>
      ∫ p, GW ((p.1, ω), p.2) ∂(NX ω)
    ∀ (Term Cash Mc Ml Gr Hr : Ω → ℝ)
      (hMc : Integrable Mc P) (hMl : Integrable Ml P)
      (hGr : Integrable Gr P) (hHr : Integrable Hr P)
      (hMc0 : (∫ ω, Mc ω ∂P) = 0)
      (hMl0 : (∫ ω, Ml ω ∂P) = 0)
      (hres : ∀ᵐ ω ∂P, Gr ω + Hr ω ≤ 0)
      (hIto : ∀ᵐ ω ∂P,
        Term ω + Cash ω ≤ w x + Mc ω +
          (Jump ω - Comp ω) + Ml ω + Gr ω + Hr ω),
      ∃ Mb Gb Hb : Ω → ℝ,
        Integrable Mb P ∧ Integrable Gb P ∧ Integrable Hb P ∧
        (∫ ω, Mb ω ∂P) = 0 ∧
        (∀ᵐ ω ∂P, Gb ω + Hb ω ≤ 0) ∧
        (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + Mb ω + Gb ω + Hb ω)) := by
  classical
  obtain ⟨μ, hμfin, hμclock, hMain⟩ :=
    avram_p4_f_assembly_original_Taylor_compensated_mean_zero_from_P2
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv T
  refine ⟨μ, hμfin, hμclock, ?_⟩
  intro NX K M hM S hST MT N hMT hN q hq
    a Y J HS GW η Comp Jump
    Term Cash Mc Ml Gr Hr hMc hMl hGr hHr hMc0 hMl0 hres hIto
  obtain ⟨hMsI, hMs0⟩ := hMain M hM S hST MT N hMT hN q hq
  exact avram_p4_f_assembly_three_source_martingales
    w x Term Cash Mc (fun ω => Jump ω - Comp ω) Ml Gr Hr
    hMc hMsI hMl hGr hHr hMc0 hMs0 hMl0 hres hIto
