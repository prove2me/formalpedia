-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_physical_martingale_Taylor_cash_three_channel_uniform_L2_assembly
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:49:01.591164+00:00
-- url     : https://prove2.me/submissions/7d5c2b1b-31b7-4beb-a65a-2df4ff113a32

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section

/-- Full true-grid controlled residual has a uniform second moment
when its centred negative-mark martingale, nonlinear Taylor error and
Stieltjes/contact correction admit separate uniform square budgets. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (M R S : ℕ → Ω → ℝ)
    (hM : ∀ k, Measurable (M k))
    (hR : ∀ k, Measurable (R k))
    (hS : ∀ k, Measurable (S k))
    (hMI : ∀ k, Integrable (fun ω => (M k ω)^2) P)
    (hRI : ∀ k, Integrable (fun ω => (R k ω)^2) P)
    (hSI : ∀ k, Integrable (fun ω => (S k ω)^2) P)
    (A B C : ℝ)
    (hA : ∀ k, (∫ ω, (M k ω)^2 ∂P) ≤ A)
    (hB : ∀ k, (∫ ω, (R k ω)^2 ∂P) ≤ B)
    (hC : ∀ k, (∫ ω, (S k ω)^2 ∂P) ≤ C) :
    ∀ k,
      Integrable (fun ω =>
        (|M k ω + R k ω + S k ω|)^2) P ∧
      (∫ ω, (|M k ω + R k ω + S k ω|)^2 ∂P) ≤
        3 * (A + B + C) := by
  intro k
  let E : Ω → ℝ := fun ω => M k ω + R k ω + S k ω
  have hEmeas : Measurable E := (hM k |>.add (hR k)).add (hS k)
  have hMajor : Integrable (fun ω =>
      3 * ((M k ω)^2 + (R k ω)^2 + (S k ω)^2)) P :=
    (((hMI k).add (hRI k)).add (hSI k)).const_mul 3
  have hSquare : ∀ ω,
      (|E ω|)^2 ≤
        3 * ((M k ω)^2 + (R k ω)^2 + (S k ω)^2) := by
    intro ω
    dsimp [E]
    rw [sq_abs]
    nlinarith [sq_nonneg (M k ω - R k ω),
      sq_nonneg (M k ω - S k ω),
      sq_nonneg (R k ω - S k ω)]
  have hIntegrable : Integrable (fun ω => (|E ω|)^2) P := by
    apply Integrable.mono' hMajor
      ((hEmeas.abs.pow_const 2).aestronglyMeasurable)
    filter_upwards [] with ω
    have h0 : 0 ≤ (|E ω|)^2 := sq_nonneg _
    have hMajNonneg : 0 ≤
        3 * ((M k ω)^2 + (R k ω)^2 + (S k ω)^2) := by
      positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0,
      abs_of_nonneg hMajNonneg] using hSquare ω
  constructor
  · simpa only [E] using hIntegrable
  · calc
      (∫ ω, (|E ω|)^2 ∂P) ≤
          ∫ ω, 3 * ((M k ω)^2 + (R k ω)^2 + (S k ω)^2) ∂P :=
        integral_mono_ae hIntegrable hMajor
          (Filter.Eventually.of_forall hSquare)
      _ = 3 * ((∫ ω, (M k ω)^2 ∂P) +
          (∫ ω, (R k ω)^2 ∂P) +
          (∫ ω, (S k ω)^2 ∂P)) := by
        rw [integral_const_mul]
        congr 1
        calc
          (∫ ω, (M k ω)^2 + (R k ω)^2 +
              (S k ω)^2 ∂P) =
            (∫ ω, (M k ω)^2 + (R k ω)^2 ∂P) +
            (∫ ω, (S k ω)^2 ∂P) :=
              integral_add ((hMI k).add (hRI k)) (hSI k)
          _ = (∫ ω, (M k ω)^2 ∂P) +
              (∫ ω, (R k ω)^2 ∂P) +
              (∫ ω, (S k ω)^2 ∂P) := by
                rw [integral_add (hMI k) (hRI k)]
      _ ≤ 3 * (A + B + C) := by
        gcongr
        · exact hA k
        · exact hB k
        · exact hC k
