-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_one_grid_conditional_fourier_case_split_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:17:53.413709+00:00
-- url     : https://prove2.me/submissions/552f568d-db3d-444f-b10f-e6e03f3cf516

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_single_grid_constant_fourier_factor_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_measurable_random_mark_interval_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Fin 2 → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω)) :
    ∀ t : WithLp 2 (Fin 1 → ℝ), ∃ φ : Fin 1 → ℕ → ℂ,
      MeasureTheory.charFun
        (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin 1 =>
          ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω)) P) t =
        ∫ ω, ∏ i : Fin 1, φ i (N i.succ ω - N i.castSucc ω) ∂P
      ∧ ∀ i : Fin 1, MeasureTheory.charFun
          (Measure.map (fun ω : Ω =>
            ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) P)
            (t.ofLp i) =
          ∫ ω, φ i (N i.succ ω - N i.castSucc ω) ∂P := by
  intro t
  let Z : Ω → ℝ := fun ω =>
    ∑ j ∈ Finset.Ico (N (Fin.castSucc 0) ω) (N (Fin.succ 0) ω), Y j ω
  let D : Ω → ℕ := fun ω => N (Fin.succ 0) ω - N (Fin.castSucc 0) ω
  have hZ : Measurable Z :=
    AvramDividend.Classical.avram_a06_measurable_random_mark_interval_20261111
      (N (Fin.castSucc 0)) (N (Fin.succ 0)) Y
      ((measurable_pi_apply (Fin.castSucc 0)).comp hN)
      ((measurable_pi_apply (Fin.succ 0)).comp hN)
      (fun j => (measurable_pi_apply j).comp hY)
  rcases
    AvramDividend.Classical.avram_a06_single_grid_constant_fourier_factor_20261111
      P D Z hZ t with ⟨φ, hJoint, hMarg⟩
  have hVec : (fun ω : Ω => WithLp.toLp 2 (fun i : Fin 1 =>
      ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω)) =
      (fun ω => WithLp.toLp 2 (fun _ : Fin 1 => Z ω)) := by
    funext ω
    congr 1
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    rfl
  have hProd : (fun ω : Ω => ∏ i : Fin 1,
      φ i (N i.succ ω - N i.castSucc ω)) =
      (fun ω => ∏ i : Fin 1, φ i (D ω)) := by
    funext ω
    apply Finset.prod_congr rfl
    intro i hiMem
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    rfl
  refine ⟨φ, ?_, ?_⟩
  · simpa only [hVec, hProd] using hJoint
  · intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    simpa only [] using hMarg 0
