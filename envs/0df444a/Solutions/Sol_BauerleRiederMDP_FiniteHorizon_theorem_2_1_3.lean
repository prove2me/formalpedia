-- Prove2me | solution 1 for BauerleRiederMDP.FiniteHorizon.theorem_2_1_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:24:16.713618+00:00
-- url     : https://prove2.me/submissions/93c047f0-cf14-4d7c-9770-aa86f277553e

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_DisturbanceModel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_Represents

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel)

universe u v w

open BauerleRiederMDP.FiniteHorizon in
theorem solution {E : Type u} {A : Type v} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ} :
    (∀ M : MarkovDecisionModel E A N, ∃ (Z : Type u) (_ : MeasurableSpace Z)
      (DM : DisturbanceModel E A Z N), Represents DM M) ∧
    (∀ (Z : Type w) [MeasurableSpace Z] (DM : DisturbanceModel E A Z N),
      ∃ M : MarkovDecisionModel E A N, Represents DM M) := by
  refine ⟨fun M => ?_, fun Z _ DM => ?_⟩
  · refine ⟨E, inferInstance,
      { D := M.D, hD_meas := M.hD_meas, hD_sel := M.hD_sel, QZ := M.Q, hQZ_prob := M.hQ_prob,
        Tr := fun _ p => p.2, hTr_meas := fun _ _ => measurable_snd, r := M.r,
        hr_meas := M.hr_meas, g := M.g, hg_meas := M.hg_meas }, ?_⟩
    exact ⟨fun n _ => rfl, fun n _ xa _ => rfl, fun x => rfl, fun n _ xa _ B _ => rfl⟩
  · let Qn : ℕ → Kernel (E × A) E := fun n =>
      if h : n < N then
        haveI : IsMarkovKernel (DM.QZ n) := ⟨DM.hQZ_prob n h⟩
        (Kernel.deterministic id measurable_id ×ₖ DM.QZ n).map (DM.Tr n)
      else 0
    have hQ : ∀ n (h : n < N) (xa : E × A) (B : Set E), MeasurableSet B →
        Qn n xa B = DM.QZ n xa {z | DM.Tr n (xa, z) ∈ B} := by
      intro n h xa B hB
      haveI : IsMarkovKernel (DM.QZ n) := ⟨DM.hQZ_prob n h⟩
      simp only [Qn, dif_pos h]
      rw [Kernel.map_apply' _ (DM.hTr_meas n h) _ hB, Kernel.prod_apply,
        Kernel.deterministic_apply, Measure.dirac_prod,
        Measure.map_apply measurable_prodMk_left ((DM.hTr_meas n h) hB)]
      rfl
    have hprob : ∀ n < N, ∀ xa, IsProbabilityMeasure (Qn n xa) := by
      intro n h xa
      haveI : IsMarkovKernel (DM.QZ n) := ⟨DM.hQZ_prob n h⟩
      constructor
      rw [hQ n h xa Set.univ MeasurableSet.univ]
      simp
    let M : MarkovDecisionModel E A N :=
      { D := DM.D
        hD_meas := DM.hD_meas
        hD_sel := DM.hD_sel
        Q := Qn
        hQ_prob := hprob
        r := DM.r
        hr_meas := DM.hr_meas
        g := DM.g
        hg_meas := DM.hg_meas }
    exact ⟨M, fun n _ => rfl, fun n _ xa _ => rfl, fun x => rfl,
      fun n h xa _ B hB => hQ n h xa B hB⟩
