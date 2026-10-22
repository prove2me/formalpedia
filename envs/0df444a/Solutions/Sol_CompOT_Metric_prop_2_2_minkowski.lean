-- Prove2me | solution 1 for CompOT.Metric.prop_2_2_minkowski
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:08:35.483021+00:00
-- url     : https://prove2.me/submissions/7996f0f4-d36e-45d9-9326-ac5af76f91d2

import Mathlib
import Definitions.Def_CompOT_Metric_Defs

set_option autoImplicit false
open CompOT.Metric Matrix

theorem solution {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (p : ℝ) (hp : 1 ≤ p)
    (hD_nonneg : ∀ i j, 0 ≤ D i j)
    (hD_symm : ∀ i j, D i j = D j i)
    (hD_zero : ∀ i j, D i j = 0 ↔ i = j)
    (hD_tri : ∀ i j k, D i k ≤ D i j + D j k)
    (a b c : Fin n → ℝ) (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin n))
    (hc : c ∈ stdSimplex ℝ (Fin n))
    (P Q : Matrix (Fin n) (Fin n) ℝ) (hP : P ∈ CompOT.Assignment.couplings a b) (hQ : Q ∈ CompOT.Assignment.couplings b c) :
    CompOT.Assignment.frob (powCost D p) (glue b P Q) ^ (1 / p) ≤
      CompOT.Assignment.frob (powCost D p) P ^ (1 / p) + CompOT.Assignment.frob (powCost D p) Q ^ (1 / p) := by
  obtain ⟨hP0, hProw, hPcol⟩ := hP
  obtain ⟨hQ0, hQrow, hQcol⟩ := hQ
  have hb0 : ∀ j, 0 ≤ b j := hb.1
  have hp0 : 0 < p := by linarith
  have hbt : ∀ j, 0 < btilde b j := by
    intro j; unfold btilde; split_ifs with h
    · exact h
    · exact one_pos
  set d : Fin n → ℝ := fun j => 1 / btilde b j with hd
  have hd0 : ∀ j, 0 ≤ d j := fun j => (one_div_pos.2 (hbt j)).le
  have hPz : ∀ i j, P i j * (d j * b j) = P i j := by
    intro i j
    by_cases hj : 0 < b j
    · have : btilde b j = b j := by simp [btilde, hj]
      simp only [hd, this]
      field_simp
    · have hbj : b j = 0 := le_antisymm (not_lt.mp hj) (hb0 j)
      have h1 : P i j ≤ ∑ i', P i' j :=
        Finset.single_le_sum (f := fun i' => P i' j) (fun i' _ => hP0 i' j) (Finset.mem_univ i)
      rw [hPcol j, hbj] at h1
      have : P i j = 0 := le_antisymm h1 (hP0 i j)
      simp [this]
  have hQz : ∀ j k, Q j k * (d j * b j) = Q j k := by
    intro j k
    by_cases hj : 0 < b j
    · have : btilde b j = b j := by simp [btilde, hj]
      simp only [hd, this]
      field_simp
    · have hbj : b j = 0 := le_antisymm (not_lt.mp hj) (hb0 j)
      have h1 : Q j k ≤ ∑ k', Q j k' :=
        Finset.single_le_sum (f := fun k' => Q j k') (fun k' _ => hQ0 j k') (Finset.mem_univ k)
      rw [hQrow j, hbj] at h1
      have : Q j k = 0 := le_antisymm h1 (hQ0 j k)
      simp [this]
  let w : Fin n × Fin n × Fin n → ℝ := fun t => P t.1 t.2.1 * d t.2.1 * Q t.2.1 t.2.2
  have hw0 : ∀ t, 0 ≤ w t := fun t =>
    mul_nonneg (mul_nonneg (hP0 _ _) (hd0 _)) (hQ0 _ _)
  have hS : ∀ i k, (glue b P Q) i k = ∑ j, P i j * d j * Q j k := by
    intro i k
    unfold glue
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.mul_diagonal]
  have hT : CompOT.Assignment.frob (powCost D p) (glue b P Q) =
      ∑ t : Fin n × Fin n × Fin n, D t.1 t.2.2 ^ p * w t := by
    simp only [Fintype.sum_prod_type]
    unfold CompOT.Assignment.frob powCost
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hS, Finset.mul_sum, w]
    rw [Finset.sum_comm]
  have hX : ∑ t : Fin n × Fin n × Fin n, D t.1 t.2.1 ^ p * w t =
      CompOT.Assignment.frob (powCost D p) P := by
    simp only [Fintype.sum_prod_type]
    unfold CompOT.Assignment.frob powCost
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    have : ∑ k, D i j ^ p * w (i, j, k) = D i j ^ p * (P i j * d j * ∑ k, Q j k) := by
      simp only [w, Finset.mul_sum]
      try (refine Finset.sum_congr rfl (fun k _ => by ring))
    rw [this, hQrow j]
    have := hPz i j
    calc D i j ^ p * (P i j * d j * b j) = D i j ^ p * (P i j * (d j * b j)) := by ring
      _ = _ := by rw [this]
  have hY : ∑ t : Fin n × Fin n × Fin n, D t.2.1 t.2.2 ^ p * w t =
      CompOT.Assignment.frob (powCost D p) Q := by
    simp only [Fintype.sum_prod_type]
    unfold CompOT.Assignment.frob powCost
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have : ∑ i, ∑ k, D j k ^ p * w (i, j, k) = ∑ k, D j k ^ p * (Q j k * d j * ∑ i, P i j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [w, Finset.mul_sum]
      try (refine Finset.sum_congr rfl (fun i _ => by ring))
    rw [this, hPcol j]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have := hQz j k
    calc D j k ^ p * (Q j k * d j * b j) = D j k ^ p * (Q j k * (d j * b j)) := by ring
      _ = _ := by rw [this]
  -- termwise bound by the triangle inequality of D
  have hle : ∑ t : Fin n × Fin n × Fin n, D t.1 t.2.2 ^ p * w t ≤
      ∑ t : Fin n × Fin n × Fin n, (D t.1 t.2.1 + D t.2.1 t.2.2) ^ p * w t := by
    refine Finset.sum_le_sum (fun t _ => ?_)
    refine mul_le_mul_of_nonneg_right ?_ (hw0 t)
    exact Real.rpow_le_rpow (hD_nonneg _ _) (hD_tri _ _ _) hp0.le
  -- Minkowski with weights
  let f : Fin n × Fin n × Fin n → ℝ := fun t => w t ^ (1 / p) * D t.1 t.2.1
  let g : Fin n × Fin n × Fin n → ℝ := fun t => w t ^ (1 / p) * D t.2.1 t.2.2
  have hwp : ∀ t, (w t ^ (1 / p)) ^ p = w t := by
    intro t
    rw [← Real.rpow_mul (hw0 t)]
    rw [one_div, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  have hfp : ∀ t, (f t) ^ p = w t * D t.1 t.2.1 ^ p := by
    intro t
    simp only [f]
    rw [Real.mul_rpow (Real.rpow_nonneg (hw0 t) _) (hD_nonneg _ _), hwp]
  have hgp : ∀ t, (g t) ^ p = w t * D t.2.1 t.2.2 ^ p := by
    intro t
    simp only [g]
    rw [Real.mul_rpow (Real.rpow_nonneg (hw0 t) _) (hD_nonneg _ _), hwp]
  have hfgp : ∀ t, (f t + g t) ^ p = w t * (D t.1 t.2.1 + D t.2.1 t.2.2) ^ p := by
    intro t
    have : f t + g t = w t ^ (1 / p) * (D t.1 t.2.1 + D t.2.1 t.2.2) := by simp only [f, g]; ring
    rw [this, Real.mul_rpow (Real.rpow_nonneg (hw0 t) _) (add_nonneg (hD_nonneg _ _) (hD_nonneg _ _)), hwp]
  have hmink := Real.Lp_add_le_of_nonneg (s := Finset.univ) (f := f) (g := g) hp
    (fun t _ => mul_nonneg (Real.rpow_nonneg (hw0 t) _) (hD_nonneg _ _))
    (fun t _ => mul_nonneg (Real.rpow_nonneg (hw0 t) _) (hD_nonneg _ _))
  simp only [Pi.add_apply, hfgp, hfp, hgp] at hmink
  calc CompOT.Assignment.frob (powCost D p) (glue b P Q) ^ (1 / p)
      ≤ (∑ t : Fin n × Fin n × Fin n, (D t.1 t.2.1 + D t.2.1 t.2.2) ^ p * w t) ^ (1 / p) := by
        rw [hT]
        refine Real.rpow_le_rpow (Finset.sum_nonneg (fun t _ => mul_nonneg (Real.rpow_nonneg (hD_nonneg _ _) _) (hw0 t))) hle
          (by positivity)
    _ = (∑ t : Fin n × Fin n × Fin n, w t * (D t.1 t.2.1 + D t.2.1 t.2.2) ^ p) ^ (1 / p) := by
        congr 1
        exact Finset.sum_congr rfl (fun t _ => by ring)
    _ ≤ (∑ t : Fin n × Fin n × Fin n, w t * D t.1 t.2.1 ^ p) ^ (1 / p) +
          (∑ t : Fin n × Fin n × Fin n, w t * D t.2.1 t.2.2 ^ p) ^ (1 / p) := hmink
    _ = _ := by
        rw [← hX, ← hY]
        congr 2 <;> exact Finset.sum_congr rfl (fun t _ => by ring)
