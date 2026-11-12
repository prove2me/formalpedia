-- Prove2me | solution 2 for AvramDividend.Classical.avram_a06_random_count_fourier_mixing_given_fixed_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:46:09.778795+00:00
-- url     : https://prove2.me/submissions/221342dd-1de3-4d05-ad66-8c8caeac2850

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_conditional_fourier_representation_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory Finset
open scoped NNReal ENNReal
noncomputable section

/-- Independent count increments turn conditional Fourier products into products. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω))
    (hNmono : ∀ ω, Monotone (fun i => N i ω))
    (hCount : iIndepFun (fun (i : Fin n) ω =>
      N i.succ ω - N i.castSucc ω) P)
    (hSameLaw : ∀ j k, IdentDistrib (Y j) (Y k) P P)
    (hSeparate : IndepFun (fun ω => fun i => N i ω)
      (fun ω => fun j => Y j ω) P)
    (hFixed : ∀ (m : Fin (n + 1) → ℕ), Monotone m →
      ∀ t : WithLp 2 (Fin n → ℝ),
        MeasureTheory.charFun
          (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
            ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
          ∏ i : Fin n, MeasureTheory.charFun
            (Measure.map (fun ω : Ω =>
              ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P)
            (t.ofLp i)) :
    ∀ t : WithLp 2 (Fin n → ℝ),
      MeasureTheory.charFun
        (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
          ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω)) P) t =
        ∏ i : Fin n, MeasureTheory.charFun
          (Measure.map (fun ω : Ω =>
            ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) P)
          (t.ofLp i) := by
  intro t
  obtain ⟨φ, hJoint, hMarg⟩ :=
    AvramDividend.Classical.avram_a06_conditional_fourier_representation_20261111
      P n N Y hN hY hNmono hSameLaw hSeparate hFixed t
  let D : Fin n → Ω → ℕ := fun i ω => N i.succ ω - N i.castSucc ω
  have hNcoord (i : Fin (n + 1)) : Measurable (N i) :=
    measurable_pi_iff.mp hN i
  have hD (i : Fin n) : AEMeasurable (D i) P := by
    exact ((hNcoord i.succ).sub (hNcoord i.castSucc)).aemeasurable
  have hφ (i : Fin n) : AEStronglyMeasurable (φ i) (Measure.map (D i) P) := by
    exact (measurable_of_countable (φ i)).aestronglyMeasurable
  have hFactor :
      (∫ ω, ∏ i : Fin n, φ i (D i ω) ∂P) =
      ∏ i : Fin n, ∫ ω, φ i (D i ω) ∂P := by
    exact hCount.integral_fun_prod_comp hD hφ
  rw [hJoint, hFactor]
  apply Finset.prod_congr rfl
  intro i _
  exact (hMarg i).symm
