-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_generic_indep_count_dependent_mark_shift_joint_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:57:43.714859+00:00
-- url     : https://prove2.me/submissions/e4f83083-2433-4d2f-a6d2-946b84f685c9

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- The fixed-shift laws of an independent mark stream imply preservation
    of the joint count/stream law under a count-dependent skew product. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → Fin 2 → ℕ) (M : Ω → ℕ → ℝ)
    (hN : AEMeasurable N P) (hM : AEMeasurable M P)
    (hNM : IndepFun N M P)
    (hshift : ∀ m : ℕ,
      IdentDistrib (fun ω j => M ω (m + j)) M P P) :
    IdentDistrib
      (fun ω => (N ω, fun j => M ω (N ω 0 + j)))
      (fun ω => (N ω, M ω)) P P := by
  let μN : Measure (Fin 2 → ℕ) := P.map N
  let μM : Measure (ℕ → ℝ) := P.map M
  let S : (Fin 2 → ℕ) → (ℕ → ℝ) → (ℕ → ℝ) :=
    fun n v j => v (n 0 + j)
  let T : ((Fin 2 → ℕ) × (ℕ → ℝ)) →
      ((Fin 2 → ℕ) × (ℕ → ℝ)) := fun p => (p.1, S p.1 p.2)
  have hSm : Measurable (Function.uncurry S) := by
    refine measurable_pi_iff.2 ?_
    intro j
    refine measurable_from_prod_countable_right ?_
    intro n
    exact measurable_pi_apply (n 0 + j)
  have hShift (n : Fin 2 → ℕ) : Measure.map (S n) μM = μM := by
    have hm : Measurable (S n) := by
      refine measurable_pi_iff.2 ?_
      intro j
      exact measurable_pi_apply (n 0 + j)
    change Measure.map (S n) (P.map M) = P.map M
    rw [AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hM]
    exact (hshift (n 0)).map_eq
  have hSkew : MeasurePreserving T (μN.prod μM) (μN.prod μM) := by
    exact (MeasurePreserving.id μN).skew_product hSm
      (Filter.Eventually.of_forall hShift)
  have hPair : P.map (fun ω => (N ω, M ω)) = μN.prod μM :=
    hNM.map_prod_eq_prod_map_map hN hM
  have hPairAE : AEMeasurable (fun ω => (N ω, M ω)) P :=
    hN.prodMk hM
  have hMap : P.map (fun ω => (N ω, fun j => M ω (N ω 0 + j))) =
      P.map (fun ω => (N ω, M ω)) := by
    have hComp := AEMeasurable.map_map_of_aemeasurable
      hSkew.measurable.aemeasurable hPairAE
    calc
      P.map (fun ω => (N ω, fun j => M ω (N ω 0 + j))) =
          (P.map (fun ω => (N ω, M ω))).map T := by
            exact hComp.symm
      _ = (μN.prod μM).map T := by rw [hPair]
      _ = μN.prod μM := hSkew.map_eq
      _ = P.map (fun ω => (N ω, M ω)) := hPair.symm
  refine ⟨?_, hPairAE, hMap⟩
  exact hSkew.measurable.comp_aemeasurable hPairAE
