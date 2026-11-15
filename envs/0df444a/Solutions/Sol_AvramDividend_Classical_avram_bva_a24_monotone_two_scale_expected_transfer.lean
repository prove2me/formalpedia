-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a24_monotone_two_scale_expected_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:57:41.599478+00:00
-- url     : https://prove2.me/submissions/47860849-7983-4003-9ace-d8629d9e4644

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
/- General two-scale expectation transfer. Monotone cash lets us use a
   later physical-grid source while retaining the original earlier cash. -/

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : ℕ → Ω → ℝ)
    (M E C : ℕ → ℕ → Ω → ℝ) (η : ℕ → ℝ) (w : ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hFM : ∀ n m, n ≤ m → ∀ ω, F n ω ≤ F m ω)
    (hη : Tendsto η atTop (nhds (0 : ℝ)))
    (hMI : ∀ n k, Integrable (M n k) P ∧ (∫ ω, M n k ω ∂P) = 0)
    (hEI : ∀ n k, Integrable (fun ω => max (E n k ω) 0) P)
    (hCI : ∀ n k, Integrable (fun ω => max (C n k ω) 0) P)
    (hBound : ∀ n k, ∀ᵐ ω ∂P,
      F n ω ≤ w + M n k ω + (max (E n k ω) 0 + max (C n k ω) 0))
    (hApprox : ∀ n (ε : ℝ), 0 < ε →
      ∃ k, (∫ ω, max (E n k ω) 0 ∂P) +
        (∫ ω, max (C n k ω) 0 ∂P) ≤ η n + ε) :
    ∀ n, (∫ ω, F n ω ∂P) ≤ w := by
  classical
  intro n
  apply le_of_forall_pos_le_add
  intro ε hε
  have hHalf : 0 < ε / 2 := by linarith
  have hηsmall : ∀ᶠ m : ℕ in atTop, η m < ε / 2 :=
    (tendsto_order.1 hη).2 (ε / 2) hHalf
  obtain ⟨m, hnm, hm⟩ :=
    ((Filter.eventually_ge_atTop n).and hηsmall).exists
  obtain ⟨k, hErr⟩ := hApprox m (ε / 2) hHalf
  have hM := (hMI m k).1
  have hE := hEI m k
  have hC := hCI m k
  have hConst : Integrable (fun _ : Ω => w) P := integrable_const _
  have hW : Integrable (fun ω : Ω => w + M m k ω) P :=
    hConst.add hM
  have hErrInt : Integrable
      (fun ω : Ω => max (E m k ω) 0 + max (C m k ω) 0) P :=
    hE.add hC
  have hTotal : Integrable
      (fun ω : Ω => w + M m k ω +
        (max (E m k ω) 0 + max (C m k ω) 0)) P :=
    hW.add hErrInt
  have hIntegral : (∫ ω, F m ω ∂P) ≤
      (∫ ω, w + M m k ω +
        (max (E m k ω) 0 + max (C m k ω) 0) ∂P) :=
    integral_mono_ae (hFI m) hTotal (hBound m k)
  have hSplit : (∫ ω, w + M m k ω +
        (max (E m k ω) 0 + max (C m k ω) 0) ∂P) =
      w + (∫ ω, max (E m k ω) 0 ∂P) +
        (∫ ω, max (C m k ω) 0 ∂P) := by
    rw [integral_add hW hErrInt]
    rw [integral_add hConst hM]
    rw [integral_add hE hC]
    simp [((hMI m k).2), add_assoc]
  have hMon := integral_mono (hFI n) (hFI m) (hFM n m hnm)
  rw [hSplit] at hIntegral
  linarith
