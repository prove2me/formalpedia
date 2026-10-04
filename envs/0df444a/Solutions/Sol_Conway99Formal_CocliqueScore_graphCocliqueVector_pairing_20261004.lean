-- Prove2me | solution 1 for Conway99Formal.CocliqueScore.graphCocliqueVector_pairing_20261004
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T02:00:08.89168+00:00
-- url     : https://prove2.me/submissions/9d48bf7e-0c9c-424c-a02a-4713cb819c6c

import Definitions.Def_Conway99_Coclique_Overlap_20261004

set_option autoImplicit false

namespace Conway99Formal.CocliqueScore

open Matrix

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [AddCommGroup E] [Module ℝ E]

private theorem sum_edge_scores (p : V → Prop) [DecidablePred p] (C : Finset V) :
    (∑ v ∈ C, if p v then (-8 : ℝ) else 1) =
      (C.card : ℝ) - 9 * ((C.filter p).card : ℝ) := by
  induction C using Finset.induction_on with
  | empty => simp
  | @insert v C hv ih =>
      by_cases hp : p v
      · simp [Finset.filter_insert, hp, hv, ih, Nat.cast_add, Nat.cast_one] <;> ring
      · simp [Finset.filter_insert, hp, hv, ih, Nat.cast_add, Nat.cast_one] <;> ring

private theorem pair_cocliqueVector (point : V → E)
    (pair : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (C : Finset V) (u : V) :
    pair (cocliqueVector point C) (point u) =
      (1 / 7 : ℝ) * ∑ v ∈ C, pair (point v) (point u) := by
  simp [cocliqueVector, map_sum, map_smul, smul_eq_mul]

private theorem pair_cocliqueVector_right (point : V → E)
    (pair : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z : E) (D : Finset V) :
    pair z (cocliqueVector point D) =
      (1 / 7 : ℝ) * ∑ u ∈ D, pair z (point u) := by
  simp [cocliqueVector, map_sum, map_smul, smul_eq_mul]

private theorem sum_overlap_scores (C D : Finset V) :
    (∑ u ∈ D, if u ∈ C then (7 : ℝ) else -2) =
      9 * ((D ∩ C).card : ℝ) - 2 * (D.card : ℝ) := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert u D hu ih =>
      by_cases hC : u ∈ C
      · simp [Finset.insert_inter_of_mem, hC, hu, ih, Nat.cast_add, Nat.cast_one]
        <;> ring
      · simp [Finset.insert_inter_of_notMem, hC, hu, ih, Nat.cast_add, Nat.cast_one]
        <;> ring

private theorem abstract_cocliqueVector_point_score (G : SimpleGraph V) [DecidableRel G.Adj]
    (point : V → E) (pair : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (C : Finset V) (hcard : C.card = 22)
    (hind : ∀ v ∈ C, ∀ u ∈ C, ¬ G.Adj v u)
    (hfour : ∀ u ∉ C, (C.filter fun v => G.Adj v u).card = 4)
    (hgram : ∀ v u, pair (point v) (point u) =
      if v = u then 28 else if G.Adj v u then -8 else 1)
    (u : V) :
    pair (cocliqueVector point C) (point u) =
      if u ∈ C then 7 else -2 := by
  rw [pair_cocliqueVector]
  by_cases hu : u ∈ C
  · have hcardErase : (C.erase u).card = 21 := by
      simp [Finset.card_erase_of_mem hu, hcard]
    have hother : (∑ v ∈ C.erase u, pair (point v) (point u)) = 21 := by
      calc
        _ = ∑ v ∈ C.erase u, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro v hv
          have hne : v ≠ u := (Finset.mem_erase.mp hv).1
          have hvC : v ∈ C := (Finset.mem_erase.mp hv).2
          rw [hgram]
          simp [hne, hind v hvC u hu]
        _ = 21 := by simp [hcardErase]
    have hdiag : pair (point u) (point u) = 28 := by
      simpa using hgram u u
    have hsplit :
        (∑ v ∈ C.erase u, pair (point v) (point u)) +
          pair (point u) (point u) =
          ∑ v ∈ C, pair (point v) (point u) :=
      Finset.sum_erase_add _ _ hu
    rw [← hsplit, hother, hdiag]
    norm_num [hu]
  · have hsum : (∑ v ∈ C, pair (point v) (point u)) = -14 := by
      calc
        _ = ∑ v ∈ C, (if G.Adj v u then (-8 : ℝ) else 1) := by
          apply Finset.sum_congr rfl
          intro v hv
          have hne : v ≠ u := by
            intro heq
            exact hu (heq ▸ hv)
          rw [hgram]
          simp [hne]
        _ = (C.card : ℝ) -
              9 * ((C.filter fun v => G.Adj v u).card : ℝ) :=
          sum_edge_scores (fun v => G.Adj v u) C
        _ = -14 := by rw [hcard, hfour u hu]; norm_num
    rw [hsum]
    norm_num [hu]

private def graphQ (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  (27 : ℝ) • (1 : Matrix V V ℝ) -
    (9 : ℝ) • G.adjMatrix ℝ + Matrix.of 1

private theorem graphQ_apply (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) :
    graphQ G v u =
      (if v = u then 27 else 0) - (if G.Adj v u then 9 else 0) + 1 := by
  simp only [graphQ, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.of_apply, SimpleGraph.adjMatrix_apply]
  split_ifs <;> norm_num

private theorem graphQ_score (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) :
    graphQ G v u = if v = u then 28 else if G.Adj v u then -8 else 1 := by
  rw [graphQ_apply]
  by_cases h : v = u
  · subst u
    simp <;> norm_num
  · by_cases ha : G.Adj v u <;> simp [h, ha] <;> norm_num

private theorem pointVector_pairing (G : SimpleGraph V) [DecidableRel G.Adj]
    (Pi : Matrix (Fin 44) V ℝ)
    (hgram : Piᵀ * Pi = graphQ G) (v u : V) :
    dotProduct (pointVector Pi v) (pointVector Pi u) = graphQ G v u := by
  have h := congrArg (fun M : Matrix V V ℝ => M v u) hgram
  simpa [pointVector, Matrix.mul_apply, dotProduct] using h

theorem graphCocliqueVector_point_score (G : SimpleGraph V) [DecidableRel G.Adj]
    (Pi : Matrix (Fin 44) V ℝ)
    (hgram : Piᵀ * Pi =
      (27 : ℝ) • (1 : Matrix V V ℝ) -
        (9 : ℝ) • G.adjMatrix ℝ + Matrix.of 1)
    (C : Finset V) (hcard : C.card = 22)
    (hind : ∀ v ∈ C, ∀ u ∈ C, ¬ G.Adj v u)
    (hfour : ∀ u ∉ C, (C.filter fun v => G.Adj v u).card = 4)
    (u : V) :
    dotProduct (graphCocliqueVector Pi C) (pointVector Pi u) =
      if u ∈ C then 7 else -2 := by
  have hmatrix : Piᵀ * Pi = graphQ G := hgram
  have hpointGram : ∀ v u, (dotProductBilin ℝ ℝ)
      (pointVector Pi v) (pointVector Pi u) =
        if v = u then 28 else if G.Adj v u then -8 else 1 := by
    intro v u
    change dotProduct (pointVector Pi v) (pointVector Pi u) = _
    rw [pointVector_pairing G Pi hmatrix, graphQ_score]
  have h := abstract_cocliqueVector_point_score G (pointVector Pi)
    (dotProductBilin ℝ ℝ) C hcard hind hfour hpointGram u
  change dotProduct (graphCocliqueVector Pi C) (pointVector Pi u) = _ at h
  exact h

theorem graphCocliqueVector_pairing (G : SimpleGraph V) [DecidableRel G.Adj]
    (Pi : Matrix (Fin 44) V ℝ)
    (hgram : Piᵀ * Pi =
      (27 : ℝ) • (1 : Matrix V V ℝ) -
        (9 : ℝ) • G.adjMatrix ℝ + Matrix.of 1)
    (C D : Finset V) (hCcard : C.card = 22)
    (hCind : ∀ v ∈ C, ∀ u ∈ C, ¬ G.Adj v u)
    (hCfour : ∀ u ∉ C, (C.filter fun v => G.Adj v u).card = 4)
    (hDcard : D.card = 22) :
    dotProduct (graphCocliqueVector Pi C) (graphCocliqueVector Pi D) =
      (9 * ((C ∩ D).card : ℝ) - 44) / 7 := by
  let z := graphCocliqueVector Pi C
  have hlinear : dotProduct z (graphCocliqueVector Pi D) =
      (1 / 7 : ℝ) * ∑ u ∈ D, dotProduct z (pointVector Pi u) := by
    have h := pair_cocliqueVector_right (pointVector Pi)
      (dotProductBilin ℝ ℝ) z D
    change dotProduct z (graphCocliqueVector Pi D) = _ at h
    exact h
  calc
    dotProduct z (graphCocliqueVector Pi D) =
        (1 / 7 : ℝ) * ∑ u ∈ D, dotProduct z (pointVector Pi u) := hlinear
    _ = (1 / 7 : ℝ) * ∑ u ∈ D, (if u ∈ C then 7 else -2) := by
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      exact graphCocliqueVector_point_score G Pi hgram C hCcard hCind hCfour u
    _ = (9 * ((C ∩ D).card : ℝ) - 44) / 7 := by
      rw [sum_overlap_scores, hDcard]
      rw [Finset.inter_comm D C]
      ring

end Conway99Formal.CocliqueScore

open Matrix
open Conway99Formal.CocliqueScore

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Pi : Matrix (Fin 44) V ℝ)
    (hgram : Piᵀ * Pi =
      (27 : ℝ) • (1 : Matrix V V ℝ) -
        (9 : ℝ) • G.adjMatrix ℝ + Matrix.of 1)
    (C D : Finset V) (hCcard : C.card = 22)
    (hCind : ∀ v ∈ C, ∀ u ∈ C, ¬ G.Adj v u)
    (hCfour : ∀ u ∉ C, (C.filter fun v => G.Adj v u).card = 4)
    (hDcard : D.card = 22) :
    dotProduct (graphCocliqueVector Pi C) (graphCocliqueVector Pi D) =
      (9 * ((C ∩ D).card : ℝ) - 44) / 7 := by
  exact graphCocliqueVector_pairing G Pi hgram C D hCcard hCind hCfour hDcard

#print axioms solution
