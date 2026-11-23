-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A77_finite_Nat_joint_atoms_imply_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T17:37:40.872842+00:00
-- url     : https://prove2.me/submissions/5367a41f-dfcb-4425-972c-0e6c1b0e061c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (K : Fin n → Ω → ℕ)
    (hMeas : ∀ i, Measurable (K i))
    (hAtoms : ∀ counts : Fin n → ℕ,
      P {ω : Ω | ∀ i, K i ω = counts i} =
        ∏ i : Fin n, P {ω : Ω | K i ω = counts i}) :
    iIndepFun K P := by
  classical
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (hMeas i).aemeasurable)).2
  apply Measure.ext_of_singleton
  intro counts
  have hm : Measurable (fun ω : Ω => fun i : Fin n => K i ω) :=
    measurable_pi_lambda _ hMeas
  rw [Measure.map_apply hm (measurableSet_singleton counts),
    Measure.pi_singleton]
  have hEq :
      (fun ω : Ω => (fun i : Fin n => K i ω)) ⁻¹' {counts} =
        {ω : Ω | ∀ i, K i ω = counts i} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, funext_iff]
  rw [hEq, hAtoms counts]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Measure.map_apply (hMeas i) (measurableSet_singleton (counts i))]
  rfl
