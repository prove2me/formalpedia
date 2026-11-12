-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb21_original_two_channel_masked_initial_condexp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T21:47:51.740161+00:00
-- url     : https://prove2.me/submissions/4209b174-8284-4fae-9660-ea78e1000c5c

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_jb21_original_initial_condexp_finite_predictable_gain
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original stop-masked Gaussian and jump mesh noises are initially centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*} (S : Finset ι)
    (R J : ℝ≥0 → Ω → ℝ)
    (hRint : ∀ u : ℝ≥0, Integrable (R u) P)
    (hRmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont u) P (R v) ω = R u ω)
    (hJint : ∀ u : ℝ≥0, Integrable (J u) P)
    (hJmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont u) P (J v) ω = J u ω)
    (a b : ι → ℝ≥0) (WG WJ : ι → Ω → ℝ)
    (hab : ∀ i ∈ S, a i ≤ b i)
    (hWG : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i))
    (hWJ : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i))
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hGprod : ∀ i ∈ S, Integrable
      (fun ω => (if τ ω ≤ a i then 0 else WG i ω) *
        (R (b i) ω - R (a i) ω)) P)
    (hJprod : ∀ i ∈ S, Integrable
      (fun ω => (if τ ω ≤ a i then 0 else WJ i ω) *
        (J (b i) ω - J (a i) ω)) P) :
    let MG : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (if τ ω ≤ a i then 0 else WG i ω) *
        (R (b i) ω - R (a i) ω)
    let MJ : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (if τ ω ≤ a i then 0 else WJ i ω) *
        (J (b i) ω - J (a i) ω)
    Integrable MG P ∧
    P[MG | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
    Integrable MJ P ∧
    P[MJ | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) := by
  classical
  let HG : ι → Ω → ℝ := fun i ω =>
    if τ ω ≤ a i then 0 else WG i ω
  let HJ : ι → Ω → ℝ := fun i ω =>
    if τ ω ≤ a i then 0 else WJ i ω
  let QR : ι → Ω → ℝ := fun i ω =>
    R (b i) ω - R (a i) ω
  let QJ : ι → Ω → ℝ := fun i ω =>
    J (b i) ω - J (a i) ω
  have h01 (i : ι) (hi : i ∈ S) :
      𝓕.rightCont 0 ≤ 𝓕.rightCont (a i) :=
    (𝓕.rightCont).mono (show (0 : ℝ≥0) ≤ a i from zero_le)
  have hS (i : ι) (hi : i ∈ S) :
      𝓕.rightCont (a i) ≤ mΩ := (𝓕.rightCont).le (a i)
  have hMeas (i : ι) (hi : i ∈ S) :
      MeasurableSet[𝓕.rightCont (a i)] {ω | τ ω ≤ a i} := by
    simpa only [WithTop.coe_le_coe] using hτstop (a i)
  have hHG (i : ι) (hi : i ∈ S) :
      StronglyMeasurable[𝓕.rightCont (a i)] (HG i) := by
    exact (Measurable.ite (hMeas i hi) measurable_const (hWG i hi)).stronglyMeasurable
  have hHJ (i : ι) (hi : i ∈ S) :
      StronglyMeasurable[𝓕.rightCont (a i)] (HJ i) := by
    exact (Measurable.ite (hMeas i hi) measurable_const (hWJ i hi)).stronglyMeasurable
  have hQRint (i : ι) (hi : i ∈ S) :
      Integrable (QR i) P := (hRint (b i)).sub (hRint (a i))
  have hQJint (i : ι) (hi : i ∈ S) :
      Integrable (QJ i) P := (hJint (b i)).sub (hJint (a i))
  have hQRzero (i : ι) (hi : i ∈ S) :
      P[QR i | 𝓕.rightCont (a i)] =ᵐ[P] (fun _ => (0 : ℝ)) := by
    have hs := condExp_sub (hRint (b i)) (hRint (a i)) (𝓕.rightCont (a i))
    filter_upwards [hs, hRmart (a i) (b i) (hab i hi),
      hRmart (a i) (a i) (le_refl (a i))] with ω he hb ha
    change (condExp (𝓕.rightCont (a i)) P
      (R (b i) - R (a i))) ω = 0
    rw [he, Pi.sub_apply, hb, ha, sub_self]
  have hQJzero (i : ι) (hi : i ∈ S) :
      P[QJ i | 𝓕.rightCont (a i)] =ᵐ[P] (fun _ => (0 : ℝ)) := by
    have hs := condExp_sub (hJint (b i)) (hJint (a i)) (𝓕.rightCont (a i))
    filter_upwards [hs, hJmart (a i) (b i) (hab i hi),
      hJmart (a i) (a i) (le_refl (a i))] with ω he hb ha
    change (condExp (𝓕.rightCont (a i)) P
      (J (b i) - J (a i))) ω = 0
    rw [he, Pi.sub_apply, hb, ha, sub_self]
  have hG :=
    avram_jb21_original_initial_condexp_finite_predictable_gain
      S (𝓕.rightCont 0) (fun i => 𝓕.rightCont (a i))
      h01 hS HG QR hHG hQRint
      (by intro i hi; exact hGprod i hi) hQRzero
  have hJ :=
    avram_jb21_original_initial_condexp_finite_predictable_gain
      S (𝓕.rightCont 0) (fun i => 𝓕.rightCont (a i))
      h01 hS HJ QJ hHJ hQJint
      (by intro i hi; exact hJprod i hi) hQJzero
  simpa only [HG, HJ, QR, QJ] using
    (show Integrable (fun ω => ∑ i ∈ S, HG i ω * QR i ω) P ∧
      P[(fun ω => ∑ i ∈ S, HG i ω * QR i ω) |
          𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
      Integrable (fun ω => ∑ i ∈ S, HJ i ω * QJ i ω) P ∧
      P[(fun ω => ∑ i ∈ S, HJ i ω * QJ i ω) |
          𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ))
      from ⟨hG.1, hG.2, hJ.1, hJ.2⟩)
