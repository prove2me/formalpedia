-- Prove2me | solution 1 for FarhiQAOA.Concentration.eq_28
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:06:05.602601+00:00
-- url     : https://prove2.me/submissions/218531a0-3c20-4dc6-9df9-412a8fd8c2f0

import Mathlib
import Definitions.Def_FarhiQAOA_Concentration_Setting

namespace Aux_FQ_eq28

open FarhiQAOA.Concentration

lemma hcut {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z : QAlgorithms.Qubits n) :
    FarhiQAOA.Cubic.cutValue G z =
      ∑ e ∈ edgePairs G, FarhiQAOA.Cubic.edgeCut e.1 e.2 z := by
  unfold FarhiQAOA.Cubic.cutValue edgePairs
  rw [Finset.sum_filter, Fintype.sum_prod_type]

end Aux_FQ_eq28

open FarhiQAOA.Concentration in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℕ)
    (γ β : Fin p → ℝ) :
    cutVariance G p γ β =
      ∑ e ∈ edgePairs G, ∑ e' ∈ edgePairs G, edgeCov G p γ β e.1 e.2 e'.1 e'.2 := by
  set P := fun z => QAlgorithms.prob (FarhiQAOA.Cubic.qaoaState G p γ β) z with hP
  have h1 : ∑ z, QAlgorithms.prob (FarhiQAOA.Cubic.qaoaState G p γ β) z *
      FarhiQAOA.Cubic.cutValue G z ^ 2 =
      ∑ e ∈ edgePairs G, ∑ e' ∈ edgePairs G,
        edgePairTerm G p γ β e.1 e.2 e'.1 e'.2 := by
    unfold edgePairTerm
    simp_rw [Aux_FQ_eq28.hcut, sq, Finset.sum_mul_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun e _ => Finset.sum_comm)
  have h2 : FarhiQAOA.Cubic.expectCut G p γ β =
      ∑ e ∈ edgePairs G, FarhiQAOA.Cubic.edgeTerm G p γ β e.1 e.2 := by
    unfold FarhiQAOA.Cubic.expectCut FarhiQAOA.Cubic.edgeTerm
    simp_rw [Aux_FQ_eq28.hcut, Finset.mul_sum]
    rw [Finset.sum_comm]
  unfold cutVariance edgeCov
  simp only [Finset.sum_sub_distrib]
  rw [h1, h2, sq, Finset.sum_mul_sum]
