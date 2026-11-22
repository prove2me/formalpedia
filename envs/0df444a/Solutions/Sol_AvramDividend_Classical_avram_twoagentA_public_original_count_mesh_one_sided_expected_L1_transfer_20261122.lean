-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_original_count_mesh_one_sided_expected_L1_transfer_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:06:34.412252+00:00
-- url     : https://prove2.me/submissions/4d728bc7-87f9-4f98-a4be-65d615647a45

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Finset ι) (N : ι → Ω → ℝ) (r δ : ι → ℝ)
    (hIntN : ∀ i ∈ S, Integrable (N i) P)
    (hMean : ∀ i ∈ S, (∫ ω, N i ω ∂P) = r i)
    (J Q : Ω → ℝ) (hJ : Integrable J P) (hQ : Integrable Q P)
    (hBound : ∀ᵐ ω ∂P, |J ω - Q ω| ≤
      ∑ i ∈ S, δ i * (N i ω + r i)) :
    (∫ ω, |J ω - Q ω| ∂P) ≤
      2 * (∑ i ∈ S, δ i * r i) := by
  classical
  have hEach : ∀ i ∈ S,
      Integrable (fun ω => δ i * (N i ω + r i)) P := by
    intro i hi
    exact ((hIntN i hi).add (integrable_const (r i))).const_mul (δ i)
  have hSum : Integrable (fun ω =>
      ∑ i ∈ S, δ i * (N i ω + r i)) P :=
    integrable_finset_sum S hEach
  have hAbs : Integrable (fun ω => |J ω - Q ω|) P :=
    (hJ.sub hQ).abs
  calc
    (∫ ω, |J ω - Q ω| ∂P) ≤
        (∫ ω, ∑ i ∈ S, δ i * (N i ω + r i) ∂P) :=
      integral_mono_ae hAbs hSum hBound
    _ = ∑ i ∈ S, (∫ ω, δ i * (N i ω + r i) ∂P) :=
      integral_finset_sum S hEach
    _ = ∑ i ∈ S, 2 * (δ i * r i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul]
      rw [integral_add (hIntN i hi) (integrable_const (r i))]
      simp [hMean i hi, mul_assoc, mul_comm, mul_left_comm]
      ring
    _ = 2 * (∑ i ∈ S, δ i * r i) := by
      rw [Finset.mul_sum]
