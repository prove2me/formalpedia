-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_generic_indep_same_count_law_prefix_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:01:03.919118+00:00
-- url     : https://prove2.me/submissions/c4c74e47-e692-498f-b95d-067fb7b74f67

import Mathlib.Probability.IdentDistrib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Independence allows two random prefix sums to be coupled through the
    common product measure of their count laws and full mark-stream law. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N N' : Ω → ℕ) (M : Ω → ℕ → ℝ)
    (hN : AEMeasurable N P) (hN' : AEMeasurable N' P)
    (hM : AEMeasurable M P)
    (hInd : IndepFun N M P) (hInd' : IndepFun N' M P)
    (hLaw : IdentDistrib N N' P P) :
    IdentDistrib
      (fun ω => ∑ j ∈ Finset.range (N ω), M ω j)
      (fun ω => ∑ j ∈ Finset.range (N' ω), M ω j) P P := by
  let F : ℕ × (ℕ → ℝ) → ℝ :=
    fun p => ∑ j ∈ Finset.range p.1, p.2 j
  have hF : Measurable F := by
    exact measurable_from_prod_countable_right (fun n =>
      Finset.measurable_sum (Finset.range n)
        (fun j hj => measurable_pi_apply j))
  have hmap : P.map (fun ω => (N ω, M ω)) =
      P.map (fun ω => (N' ω, M ω)) := by
    have hprod := hInd.map_prod_eq_prod_map_map hN hM
    have hprod' := hInd'.map_prod_eq_prod_map_map hN' hM
    rw [hprod, hprod', hLaw.map_eq]
  have hPair : IdentDistrib
      (fun ω => (N ω, M ω))
      (fun ω => (N' ω, M ω)) P P :=
    ⟨hN.prodMk hM, hN'.prodMk hM, hmap⟩
  have hResult := hPair.comp hF
  change IdentDistrib
    (fun ω => ∑ j ∈ Finset.range (N ω), M ω j)
    (fun ω => ∑ j ∈ Finset.range (N' ω), M ω j) P P at hResult
  exact hResult
