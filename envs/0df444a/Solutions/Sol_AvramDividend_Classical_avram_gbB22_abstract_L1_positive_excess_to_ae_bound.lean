-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB22_abstract_L1_positive_excess_to_ae_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:37:45.089702+00:00
-- url     : https://prove2.me/submissions/b504fa42-e050-43b5-8ef9-6ebac6003830

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (F N B : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (hI : IntegrableOn (fun ω => max (F ω - N ω - B ω) 0) A P)
    (hMI : ∀ m, IntegrableOn
      (fun ω => max (F ω - M m ω - B ω) 0) A P)
    (hDI : ∀ m, IntegrableOn (fun ω => |N ω - M m ω|) A P)
    (hEL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hR : Tendsto (fun m =>
      ∫ ω in A, max (F ω - M m ω - B ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), F ω ≤ N ω + B ω := by
  classical
  have hp (m : ℕ) (ω : Ω) :
      max (F ω - N ω - B ω) 0 ≤
        max (F ω - M m ω - B ω) 0 + |N ω - M m ω| := by
    have hn := neg_le_abs (N ω - M m ω)
    have hm := le_max_left (F ω - M m ω - B ω) (0 : ℝ)
    have hz := le_max_right (F ω - M m ω - B ω) (0 : ℝ)
    apply max_le
    · linarith
    · linarith [abs_nonneg (N ω - M m ω)]
  have hb (m : ℕ) :
      (∫ ω in A, max (F ω - N ω - B ω) 0 ∂P) ≤
      (∫ ω in A, max (F ω - M m ω - B ω) 0 ∂P) +
      (∫ ω in A, |N ω - M m ω| ∂P) := by
    calc
      _ ≤ ∫ ω in A,
          max (F ω - M m ω - B ω) 0 + |N ω - M m ω| ∂P :=
        integral_mono_ae hI ((hMI m).add (hDI m))
          (Filter.Eventually.of_forall (hp m))
      _ = _ := integral_add (hMI m) (hDI m)
  have hl : Tendsto (fun m =>
      (∫ ω in A, max (F ω - M m ω - B ω) 0 ∂P) +
      (∫ ω in A, |N ω - M m ω| ∂P)) atTop (𝓝 (0 : ℝ)) := by
    convert hR.add hEL1 using 1 <;> simp
  have hNegLimit := hl.neg
  have hNegBound : -(0 : ℝ) ≤
      - (∫ ω in A, max (F ω - N ω - B ω) 0 ∂P) :=
    le_of_tendsto hNegLimit
      (Filter.Eventually.of_forall (fun m => neg_le_neg (hb m)))
  have hle : (∫ ω in A, max (F ω - N ω - B ω) 0 ∂P) ≤ 0 := by linarith
  have hn : ∀ᵐ ω ∂(P.restrict A),
      0 ≤ max (F ω - N ω - B ω) 0 :=
    Filter.Eventually.of_forall (fun ω => le_max_right _ _)
  have heq : (∫ ω in A, max (F ω - N ω - B ω) 0 ∂P) = 0 :=
    le_antisymm hle (integral_nonneg_of_ae hn)
  have hzero : ∀ᵐ ω ∂(P.restrict A),
      max (F ω - N ω - B ω) 0 = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hn hI).mp heq
  filter_upwards [hzero] with ω hω
  have hx := le_max_left (F ω - N ω - B ω) (0 : ℝ)
  rw [hω] at hx
  linarith
