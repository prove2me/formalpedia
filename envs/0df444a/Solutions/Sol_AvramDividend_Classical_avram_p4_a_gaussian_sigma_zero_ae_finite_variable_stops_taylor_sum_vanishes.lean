-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_sigma_zero_ae_finite_variable_stops_taylor_sum_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:32:18.174814+00:00
-- url     : https://prove2.me/submissions/5b8a190f-0c34-4d75-a433-005573025f05

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_sigma_zero_ae_original_stopped_residual_vanishes
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Pure-jump sigma-zero original Lévy source: a finite random-clock
Gaussian Taylor mesh is a.e. zero and L¹ with arbitrary weights. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [DecidableEq ι]
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (hσ : X.σ = 0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S,
      IsStoppingTime 𝓕.rightCont (fun ω => (τ i ω : WithTop ℝ≥0)))
    (T : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ T i)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ) :
    let M : ι → Ω → ℝ := fun i ω =>
      (X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
        Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
      (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
        Jsmall (τ i ω) ω - Jlarge (τ i ω) ω)
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * M i ω +
        (H i ω * M i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
      (fun ω => ∑ i ∈ S, F i ω) =ᵐ[P] (fun _ => (0 : ℝ)) := by
  let M : ι → Ω → ℝ := fun i ω =>
    (X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
      Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
    (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
      Jsmall (τ i ω) ω - Jlarge (τ i ω) ω)
  let F : ι → Ω → ℝ := fun i ω =>
    G i ω * M i ω +
      (H i ω * M i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
  have hCell (i : ι) (hi : i ∈ S) : ∀ᵐ ω ∂P, M i ω = 0 := by
    exact avram_p4_a_gaussian_sigma_zero_ae_original_stopped_residual_vanishes
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp hσ
      (τ i) (hτ i hi) (T i) (hbounded i hi) (h i)
  have hForall : ∀ (S' : Finset ι), S' ⊆ S →
      ∀ᵐ ω ∂P, ∀ i ∈ S', M i ω = 0 := by
    intro S'
    induction S' using Finset.induction_on with
    | empty =>
        intro hsub
        filter_upwards [] with ω
        intro i hi
        simp at hi
    | @insert a s ha ih =>
        intro hsub
        have haS : a ∈ S := hsub (Finset.mem_insert_self a s)
        have hsS : s ⊆ S := by
          intro i hi
          exact hsub (Finset.mem_insert_of_mem hi)
        filter_upwards [hCell a haS, ih hsS] with ω haω hsω
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | his
        · exact haω
        · exact hsω i his
  have hZero : (fun ω => ∑ i ∈ S, F i ω) =ᵐ[P]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hForall S (by intro i hi; exact hi)] with ω hω
    apply Finset.sum_eq_zero
    intro i hi
    change G i ω * M i ω +
      (H i ω * M i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω) = 0
    rw [hω i hi, hσ]
    ring
  change Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
    (fun ω => ∑ i ∈ S, F i ω) =ᵐ[P] (fun _ => (0 : ℝ))
  exact ⟨(integrable_zero Ω ℝ P).congr hZero.symm, hZero⟩
