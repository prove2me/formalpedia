-- Prove2me | solution 1 for AvramDividend.Classical.avram_b57_original_gaussian_negative_mark_finite_grid_initial_event_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:32:14.478053+00:00
-- url     : https://prove2.me/submissions/15aaca8d-2403-44a3-bb03-3faf1299d9c0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
import Theorems.Thm_AvramDividend_Classical_avram_b55_original_predictable_mark_cell_initial_event_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_jb21_original_initial_condexp_finite_predictable_gain
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Mixed same-X predictable Gaussian and original marked negative jump finite-grid gain is centred on initial events. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Finset ℕ) (cut : ℕ → ℕ) (s t : ℕ → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i) (htT : ∀ i ∈ S, t i ≤ T)
    (ε : ℕ → ℝ) (hε : ∀ i ∈ S, 0 < ε i)
    (B : ℕ → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (hBand : ∀ i ∈ S, B i ⊆ Ioo (-1 : ℝ) (-(ε i)))
    (hCut : ∀ i ∈ S, B i ⊆ Iic (-(1 / ((cut i : ℝ) + 1))))
    (HG HJ : ℕ → Ω → ℝ)
    (hHG : ∀ i ∈ S, StronglyMeasurable[𝓕.rightCont (s i)] (HG i))
    (hHJ : ∀ i ∈ S, StronglyMeasurable[𝓕 (s i)] (HJ i)) (hHJ2 : ∀ i ∈ S, MemLp (HJ i) 2 P)
    (A : Set Ω) (hA0 : MeasurableSet[𝓕.rightCont 0] A) (hAJ : ∀ i ∈ S, MeasurableSet[𝓕 (s i)] A) :
    ∃ R : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
          atTop (𝓝 (R u ω))) ∧
      ((∀ i ∈ S, Integrable (fun ω =>
        HG i ω * (R (t i) ω - R (s i) ω)) P) →
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
        NX ω (Ioc (s i) (t i) ×ˢ B i)
      let r : ℕ → ℝ := fun i =>
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal
      let F : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (HG i ω * (R (t i) ω - R (s i) ω) +
          HJ i ω * ((N i ω).toReal - r i))
      Integrable F P ∧ (∫ ω in A, F ω ∂P) = 0) := by 
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨R, hRsrc, hRmeas, hRI, hRM⟩ :=
    avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists X hX hFinite
  refine ⟨R, ?_, ?_⟩
  · filter_upwards [hRsrc] with ω hw u
    exact hw.1 u
  intro hGI
  dsimp only
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let N : ℕ → Ω → ℝ≥0∞ := fun i ω => NX ω (Ioc (s i) (t i) ×ˢ B i)
  let r : ℕ → ℝ := fun i => (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal
  let Q : ℕ → Ω → ℝ := fun i ω => R (t i) ω - R (s i) ω
  let G : Ω → ℝ := fun ω => ∑ i ∈ S, HG i ω * Q i ω
  let J : Ω → ℝ := fun ω => ∑ i ∈ S, HJ i ω * ((N i ω).toReal - r i)
  have hQI (i : ℕ) (hi : i ∈ S) : Integrable (Q i) P := (hRI (t i)).sub (hRI (s i))
  have hQzero (i : ℕ) (hi : i ∈ S) :
      P[Q i | 𝓕.rightCont (s i)] =ᵐ[P] (fun _ => (0 : ℝ)) := by
    have hs := condExp_sub (hRI (t i)) (hRI (s i)) (𝓕.rightCont (s i))
    filter_upwards [hs, hRM (s i) (t i) (hst i hi),
      hRM (s i) (s i) le_rfl] with ω hsub ht hs'
    change (condExp (𝓕.rightCont (s i)) P (R (t i) - R (s i))) ω = 0
    rw [hsub, Pi.sub_apply, ht, hs', sub_self]
  have hG :=
    avram_jb21_original_initial_condexp_finite_predictable_gain S
      (𝓕.rightCont 0) (fun i => 𝓕.rightCont (s i))
      (fun i hi => (𝓕.rightCont).mono (by exact zero_le))
      (fun i hi => (𝓕.rightCont).le (s i)) HG Q hHG hQI hGI hQzero
  have hJcell (i : ℕ) (hi : i ∈ S) :
      Integrable (fun ω => HJ i ω * ((N i ω).toReal - r i)) P ∧
      (∫ ω in A, HJ i ω * ((N i ω).toReal - r i) ∂P) = 0 :=
    avram_b55_original_predictable_mark_cell_initial_event_mean_zero
      X T (cut i) (s i) (t i) (hst i hi) (htT i hi)
      (ε i) (hε i hi) (B i) (hB i hi)
      (hBand i hi) (hCut i hi) (HJ i) (hHJ i hi) (hHJ2 i hi) A (hAJ i hi)
  have hJI : Integrable J P := integrable_finset_sum S (fun i hi => (hJcell i hi).1)
  have hJzero : (∫ ω in A, J ω ∂P) = 0 := by
    rw [integral_finset_sum S (fun i hi => (hJcell i hi).1.integrableOn)]
    exact Finset.sum_eq_zero (fun i hi => (hJcell i hi).2)
  have hGzero : (∫ ω in A, G ω ∂P) = 0 := by
    calc
      (∫ ω in A, G ω ∂P) =
          ∫ ω in A, condExp (𝓕.rightCont 0) P G ω ∂P :=
        (setIntegral_condExp ((𝓕.rightCont).le 0) hG.1 hA0).symm
      _ = 0 := integral_eq_zero_of_ae (ae_restrict_of_ae hG.2)
  have hF : (fun ω => ∑ i ∈ S, (HG i ω * Q i ω + HJ i ω * ((N i ω).toReal - r i))) =
      (fun ω => G ω + J ω) := by
    funext ω
    simp only [G, J, Finset.sum_add_distrib]
  rw [hF]
  refine ⟨hG.1.add hJI, ?_⟩
  rw [integral_add hG.1.integrableOn hJI.integrableOn, hGzero, hJzero]
  ring
