-- Prove2me | solution 1 for FarhiQAOA.Cubic.k4_case
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:51:51.092446+00:00
-- url     : https://prove2.me/submissions/41c6127f-6618-4855-a335-12982cb5ccec

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_FarhiQAOA_Cubic_Types

namespace FarhiQAOA.Cubic.K4Aux

open QAlgorithms FarhiQAOA.Cubic

lemma k4_adj_iff_ne (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (u v : Fin 4) :
    G.Adj u v ↔ u ≠ v := by
  refine ⟨G.ne_of_adj, fun huv => ?_⟩
  have hsub : G.neighborFinset u ⊆ Finset.univ.erase u := by
    intro x hx
    rw [SimpleGraph.mem_neighborFinset] at hx
    rw [Finset.mem_erase]
    exact ⟨(G.ne_of_adj hx).symm, Finset.mem_univ x⟩
  have hcard : (Finset.univ.erase u).card ≤ (G.neighborFinset u).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, h3 u]
    simp [Finset.card_erase_of_mem]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hv : v ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩
  rw [← heq, SimpleGraph.mem_neighborFinset] at hv
  exact hv

lemma cutValue_k4_eq (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (z : Qubits 4) :
    cutValue G z = ∑ u : Fin 4, ∑ v : Fin 4, if u < v then edgeCut u v z else 0 := by
  simp only [cutValue]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  by_cases huv : u < v
  · rw [if_pos ⟨huv, (k4_adj_iff_ne G h3 u v).mpr (ne_of_lt huv)⟩, if_pos huv]
  · have hnot : ¬(u < v ∧ G.Adj u v) := fun h => huv h.1
    rw [if_neg hnot, if_neg huv]

lemma cutValue_k4_le_four (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (z : Qubits 4) :
    cutValue G z ≤ 4 := by
  rw [cutValue_k4_eq G h3 z]
  simp only [Fin.sum_univ_four, edgeCut]
  have h10 : ¬((1 : Fin 4) < 0) := by decide
  have h20 : ¬((2 : Fin 4) < 0) := by decide
  have h21 : ¬((2 : Fin 4) < 1) := by decide
  have h30 : ¬((3 : Fin 4) < 0) := by decide
  have h31 : ¬((3 : Fin 4) < 1) := by decide
  have h32 : ¬((3 : Fin 4) < 2) := by decide
  have h01' : (0 : Fin 4) < 1 := by decide
  have h02' : (0 : Fin 4) < 2 := by decide
  have h03' : (0 : Fin 4) < 3 := by decide
  have h12' : (1 : Fin 4) < 2 := by decide
  have h13' : (1 : Fin 4) < 3 := by decide
  have h23' : (2 : Fin 4) < 3 := by decide
  cases z 0 <;> cases z 1 <;> cases z 2 <;> cases z 3 <;>
    simp [h10, h20, h21, h30, h31, h32, h01', h02', h03', h12', h13', h23'] <;> norm_num

lemma sum_edgeCut_qubits4 {u v : Fin 4} (huv : u ≠ v) :
    ∑ z : Qubits 4, edgeCut u v z = 8 := by
  have hcard : Fintype.card (Qubits 4) = 16 := by decide
  have h1 : ∀ z : Qubits 4, edgeCut u v z =
      (1 / 2 : ℝ) - (1 / 2 : ℝ) * ∏ i : Fin 4, if i = u ∨ i = v then (if z i then (-1 : ℝ) else 1) else 1 := by
    intro z
    have hsub : (∏ i : Fin 4, if i = u ∨ i = v then (if z i then (-1 : ℝ) else 1) else 1) =
        (if z u then (-1 : ℝ) else 1) * (if z v then (-1 : ℝ) else 1) := by
      have hpair : (Finset.univ.filter fun i : Fin 4 => i = u ∨ i = v) = {u, v} := by
        ext i; simp
      rw [← Finset.prod_filter, hpair, Finset.prod_pair huv]
    rw [hsub]
    simp only [edgeCut]
    cases z u <;> cases z v <;> norm_num
  simp_rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hps := (Fintype.prod_sum (fun (i : Fin 4) (b : Bool) =>
    if i = u ∨ i = v then (if b then (-1 : ℝ) else 1) else 1)).symm
  rw [hps]
  have hzero : (∏ i : Fin 4, ∑ b : Bool, if i = u ∨ i = v then (if b then (-1 : ℝ) else 1) else 1) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ u) ?_
    rw [Fintype.sum_bool]
    simp
  rw [hzero, Finset.sum_const, Finset.card_univ, hcard]
  norm_num

lemma sum_cutValue_k4 (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) :
    ∑ z : Qubits 4, cutValue G z = 48 := by
  simp_rw [cutValue_k4_eq G h3]
  rw [Finset.sum_comm]
  trans ∑ u : Fin 4, ∑ v : Fin 4, if u < v then (8 : ℝ) else 0
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases huv : u < v
    · simp only [if_pos huv]
      exact sum_edgeCut_qubits4 (ne_of_lt huv)
    · simp [if_neg huv]
  · have h32 : ¬((3 : Fin 4) < 2) := by decide
    have h02' : (0 : Fin 4) < 2 := by decide
    have h03' : (0 : Fin 4) < 3 := by decide
    have h12' : (1 : Fin 4) < 2 := by decide
    have h13' : (1 : Fin 4) < 3 := by decide
    have h23' : (2 : Fin 4) < 3 := by decide
    simp [Fin.sum_univ_four, h32, h02', h03', h12', h13', h23']
    norm_num

lemma qaoaUnitary_zero (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] :
    qaoaUnitary (cutValue G) 1 (fun _ => 0) (fun _ => 0) = 1 := by
  simp [qaoaUnitary, orderedProd, NormedSpace.exp_zero]

lemma qaoaState_zero (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] :
    qaoaState G 1 (fun _ => 0) (fun _ => 0) = uniformState (Qubits 4) := by
  simp [qaoaState, qaoaUnitary_zero, act]

lemma prob_uniformState_qubits4 (z : Qubits 4) :
    prob (uniformState (Qubits 4)) z = (1 / 16 : ℝ) := by
  have hcard : Fintype.card (Qubits 4) = 16 := by decide
  have hsqrt : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [prob, ket, EuclideanSpace.inner_single_left, starRingEnd_apply, star_one,
    one_mul, uniformState, hcard, Nat.cast_ofNat, hsqrt]
  norm_num

lemma F1_zero_eq_three (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) :
    F1 G 0 0 = 3 := by
  simp only [F1, expectCut, qaoaState_zero, prob_uniformState_qubits4]
  rw [← Finset.mul_sum, sum_cutValue_k4 G h3]
  norm_num

end FarhiQAOA.Cubic.K4Aux

open QAlgorithms FarhiQAOA.Cubic FarhiQAOA.Cubic.K4Aux in
theorem solution (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] (h3 : G.IsRegularOfDegree 3) :
    ∃ γ β : ℝ, γ ∈ Set.Icc 0 (2 * Real.pi) ∧ β ∈ Set.Icc 0 Real.pi ∧
      ∀ z : Qubits 4, (1731 / 2500 : ℝ) * cutValue G z < F1 G γ β := by
  refine ⟨0, 0, ⟨le_rfl, by positivity⟩, ⟨le_rfl, Real.pi_pos.le⟩, fun z => ?_⟩
  rw [F1_zero_eq_three G h3]
  have hle := cutValue_k4_le_four G h3 z
  linarith
