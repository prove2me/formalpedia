-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_original_ruinclip_fullnu_joint_Taylor_finite_annuli_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T10:31:22.458812+00:00
-- url     : https://prove2.me/submissions/021f66f2-5e72-4751-a89d-d9e941e1992f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward26_original_stopped_Taylor_initial_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_canonical_Taylor_initial_event_centered
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_fullnu_finite_annular_stopped_martingale_L1_centered
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (Cband u v δ : ℝ)
    (hwCb : ContDiffOn ℝ 2 w (Ioo 0 Cband))
    (hu : 0 < u) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (huv : u + δ < v) (hv : v < Cband)
    (S : Finset ℕ) (η : ℕ → ℝ)
    (hη : ∀ i, 0 < η i ∧ η i < 1) :
    let T : ℝ≥0 := (n : ℝ≥0)
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then
        (1 : ℝ) else 0) * H p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let J : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
      (∫ p, (if p.1 ≤ ρ ω then GW ((p.1, ω), p.2) else 0) ∂(NX ω)) -
      (∫ t, ∫ z,
        (if t ≤ ρ ω then GW ((t, ω), z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    let K : ℕ → Ω → (ℝ≥0 × ℝ) → ℝ := fun i ω p =>
      if p.1 ≤ T ∧ p.2 ∈ Ioo (-1 : ℝ) (-(η i)) then
        Real.exp (-(q * (p.1 : ℝ))) *
          (if Y (p.1, ω) ∈ Icc (u + δ) v then
            deriv w (Y (p.1, ω)) * p.2 else 0) else 0
    let L : ℕ → Ω → ℝ := fun i ω =>
      (∫ p, (if p.1 ≤ τ ω then K i ω p else 0) ∂(NX ω)) -
      (∫ t, ∫ z, (if t ≤ τ ω then K i ω (t,z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    Integrable (fun ω => J τ ω + ∑ i ∈ S, L i ω) P ∧
      (∫ ω, J τ ω + ∑ i ∈ S, L i ω ∂P) = 0 := by
  classical
  have hJdata :=
    avram_pj_reward26_original_stopped_Taylor_initial_condexp_zero
      X x D hD w Cband u v δ hwCb hw_cont hw_neg
      hu hδ hδ1 huv hv q hq (n : ℝ≥0) τ hτstop
  have hJmean :=
    avram_ubv_jump12_original_canonical_Taylor_initial_event_centered
      X x D hD w Cband u v δ hwCb hw_cont hw_neg
      hu hδ hδ1 huv hv q hq (n : ℝ≥0)
      τ hτstop (Set.univ : Set Ω) (by simp)
  have hLdata :=
    avram_twoagentA_original_fullnu_finite_annular_stopped_martingale_L1_centered
      X x D hD w q hq n Cband u v δ
      (by linarith) huv hv hwCb S η hη τ hτstop
  simp only [Measure.restrict_univ] at hJmean
  have hSum (F G : Ω → ℝ) (hF : Integrable F P) (hG : Integrable G P)
      (hFzero : (∫ ω, F ω ∂P) = 0)
      (hGzero : (∫ ω, G ω ∂P) = 0) :
      Integrable (fun ω => F ω + G ω) P ∧
        (∫ ω, F ω + G ω ∂P) = 0 := by
    refine ⟨hF.add hG, ?_⟩
    rw [integral_add hF hG, hFzero, hGzero]
    norm_num
  exact hSum _ _ hJdata.1 hLdata.1 (by simpa using hJmean) hLdata.2

