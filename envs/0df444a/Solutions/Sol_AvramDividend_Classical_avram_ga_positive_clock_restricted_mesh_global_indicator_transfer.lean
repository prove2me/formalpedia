-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_positive_clock_restricted_mesh_global_indicator_transfer
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T04:45:26.429795+00:00
-- url     : https://prove2.me/submissions/dab017ea-02ae-4fee-bc14-556fb847b7fb

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (hA : MeasurableSet A) (M : ℕ → Ω → ℝ)
    (hMI : ∀ m, Integrable (M m) P)
    (hSource : ∃ Z : Ω → ℝ,
      (∀ m, Integrable (fun ω => |Z ω - M m ω|) (P.restrict A)) ∧
      Tendsto (fun m => ∫ ω in A, |Z ω - M m ω| ∂P)
        atTop (𝓝 (0 : ℝ))) :
    ∃ N : Ω → ℝ, Integrable N P ∧
      Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  classical
  obtain ⟨Z, hZ, hconv⟩ := hSource
  let μ := P.restrict A
  have hM (m : ℕ) : Integrable (M m) μ := (hMI m).integrableOn
  let F (m : ℕ) := (hM m).toL1 (M m)
  have hrep (m : ℕ) : (F m : Ω → ℝ) =ᵐ[μ] M m := (hM m).coeFn_toL1
  have hc : CauchySeq F := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := eventually_atTop.1 (hconv.eventually_lt_const (half_pos hε))
    refine ⟨k, fun m hm n hn => ?_⟩
    have hdom : ∀ ω, |M m ω - M n ω| ≤ |Z ω - M m ω| + |Z ω - M n ω| := by
      intro ω
      simpa only [abs_sub_comm (M m ω) (Z ω)] using abs_sub_le (M m ω) (Z ω) (M n ω)
    calc
      dist (F m) (F n) = ∫ ω, |M m ω - M n ω| ∂μ := by
        rw [L1.dist_eq_integral_dist]
        apply integral_congr_ae
        filter_upwards [hrep m, hrep n] with ω hm' hn'
        simp only [hm', hn', Real.dist_eq]
      _ ≤ ∫ ω, (|Z ω - M m ω| + |Z ω - M n ω|) ∂μ :=
        integral_mono_ae ((hM m).sub (hM n)).abs ((hZ m).add (hZ n)) (Eventually.of_forall hdom)
      _ = (∫ ω, |Z ω - M m ω| ∂μ) + ∫ ω, |Z ω - M n ω| ∂μ :=
        integral_add (hZ m) (hZ n)
      _ < ε := (add_lt_add (hk m hm) (hk n hn)).trans_eq (add_halves ε)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨A.indicator (L : Ω → ℝ), (integrable_indicator_iff hA).2 (L1.integrable_coeFn L), ?_⟩
  apply (tendsto_iff_dist_tendsto_zero.mp hL).congr'
  apply Eventually.of_forall
  intro m
  change dist (F m) L = ∫ ω, |A.indicator (L : Ω → ℝ) ω - M m ω| ∂μ
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [hrep m, indicator_ae_eq_restrict (μ := P) (f := (L : Ω → ℝ)) hA] with ω hm hmask
  rw [hm, hmask, Real.dist_eq, abs_sub_comm]
