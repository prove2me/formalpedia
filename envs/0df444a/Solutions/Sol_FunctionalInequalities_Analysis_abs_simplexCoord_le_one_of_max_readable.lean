-- Prove2me | solution 1 for FunctionalInequalities.Analysis.abs_simplexCoord_le_one_of_max_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:16.316857+00:00
-- url     : https://prove2.me/submissions/1d0a99d4-e9c8-4c0d-92be-37336f724151

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Normalization

noncomputable section
open Set Matrix
section LT11D2MaxSimplexBox
private lemma FunctionalInequalities.Analysis.simplexEdgeMatrix_update_succ
    {n : ℕ} (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n))
    (j : Fin n) (y : EuclideanSpace ℝ (Fin n)) :
    simplexEdgeMatrix (Function.update v j.succ y) =
      (simplexEdgeMatrix v).updateCol j
        ((y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp) := by
  ext i k
  by_cases h : k = j
  · subst k
    have hzero : (0 : Fin (n + 1)) ≠ j.succ :=
      (Fin.succ_ne_zero j).symm
    simp [simplexEdgeMatrix, Matrix.updateCol, Function.update, hzero]
  · have hzero : (0 : Fin (n + 1)) ≠ j.succ :=
      (Fin.succ_ne_zero j).symm
    simp [simplexEdgeMatrix, Matrix.updateCol, Function.update, h, hzero]
private lemma FunctionalInequalities.Analysis.simplexEdgeMatrix_update_zero
    {n : ℕ} (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) :
    simplexEdgeMatrix (Function.update v 0 y) =
      simplexEdgeMatrix v -
        Matrix.of fun i _ => (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp i := by
  ext i j
  simp [simplexEdgeMatrix, Matrix.sub_apply, Function.update, Fin.succ_ne_zero]
private lemma FunctionalInequalities.Analysis.simplexEdgeMatrix_update_succ_det
    {n : ℕ} (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n))
    (j : Fin n) (y : EuclideanSpace ℝ (Fin n))
    (c : Fin n → ℝ)
    (hc :
      (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp =
        fun i => ∑ k, c k • (simplexEdgeMatrix v) i k) :
    (simplexEdgeMatrix (Function.update v j.succ y)).det =
      c j * (simplexEdgeMatrix v).det := by
  rw [simplexEdgeMatrix_update_succ]
  rw [hc]
  simpa [smul_eq_mul] using
    Matrix.det_updateCol_sum (simplexEdgeMatrix v) j c
/-- **Maximality of the simplex confines the body to a box in simplex coordinates** (weak Letwin
route, Caffarelli's argument): if `v` is a nondegenerate simplex of maximal volume in `K`,
then every `y ∈ K` has simplex coordinates `c = (M v)⁻¹ (y − v 0)` with `|cⱼ| ≤ 1` and
`|1 − ∑ cⱼ| ≤ 1`. -/
theorem solution {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {v : Fin (n + 1) → EuclideanSpace ℝ (Fin n)} (hv : ∀ i, v i ∈ K)
    (hdet : (FunctionalInequalities.Analysis.simplexEdgeMatrix v).det ≠ 0)
    (hmax : ∀ w : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, w i ∈ K) →
      |(FunctionalInequalities.Analysis.simplexEdgeMatrix w).det| ≤ |(FunctionalInequalities.Analysis.simplexEdgeMatrix v).det|)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ K) :
    (∀ j, |((FunctionalInequalities.Analysis.simplexEdgeMatrix v)⁻¹ *ᵥ (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp) j| ≤ 1) ∧
      |1 - ∑ j, ((FunctionalInequalities.Analysis.simplexEdgeMatrix v)⁻¹ *ᵥ (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp) j| ≤ 1 := by
  let M : Matrix (Fin n) (Fin n) ℝ := FunctionalInequalities.Analysis.simplexEdgeMatrix v
  let u : Fin n → ℝ := (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp
  let c : Fin n → ℝ := M⁻¹ *ᵥ u
  have hunit : IsUnit M.det :=
    isUnit_iff_ne_zero.mpr (by simpa [M] using hdet)
  have hMu : M *ᵥ c = u := by
    dsimp [c]
    rw [Matrix.mulVec_mulVec]
    rw [Matrix.mul_nonsing_inv M hunit]
    simp
  have hc :
      u = fun i => ∑ k, c k * M i k := by
    funext i
    calc
      u i = (M *ᵥ c) i := (congrFun hMu i).symm
      _ = ∑ k, M i k * c k := by
        simp only [Matrix.mulVec, dotProduct]
      _ = ∑ k, c k * M i k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [mul_comm]
  have hcoord : ∀ j, |c j| ≤ 1 := by
    intro j
    let w := Function.update v j.succ y
    have hw : ∀ i, w i ∈ K := by
      intro i
      by_cases h : i = j.succ
      · subst i
        simpa [w] using hy
      · have hi : w i = v i := by
          simp [w, h]
        rw [hi]
        exact hv i
    have hdetw : |(FunctionalInequalities.Analysis.simplexEdgeMatrix w).det| ≤ |M.det| := by
      simpa [w, M] using hmax w hw
    have hformula : (FunctionalInequalities.Analysis.simplexEdgeMatrix w).det = c j * M.det := by
      change
        (FunctionalInequalities.Analysis.simplexEdgeMatrix (Function.update v j.succ y)).det =
          c j * M.det
      apply FunctionalInequalities.Analysis.simplexEdgeMatrix_update_succ_det v j y c
      simpa [M, u] using hc
    rw [hformula] at hdetw
    have hmul : |c j| * |M.det| ≤ |M.det| := by
      simpa [abs_mul] using hdetw
    have hpos : 0 < |M.det| := abs_pos.mpr (by simpa [M] using hdet)
    nlinarith
  have hsum : |1 - ∑ j, c j| ≤ 1 := by
    let w := Function.update v 0 y
    have hw : ∀ i, w i ∈ K := by
      intro i
      by_cases h : i = 0
      · subst i
        simpa [w] using hy
      · have hi : w i = v i := by
          simp [w, h]
        rw [hi]
        exact hv i
    have hdetw : |(FunctionalInequalities.Analysis.simplexEdgeMatrix w).det| ≤ |M.det| := by
      simpa [w, M] using hmax w hw
    have hc_coord : ∀ z, c z = ∑ x, (M⁻¹) z x * u x := by
      intro z
      simp [c, Matrix.mulVec, dotProduct]
    have hsum' :
        (∑ x, (∑ z, (M⁻¹) z x) * u x) = ∑ z, c z := by
      calc
        (∑ x, (∑ z, (M⁻¹) z x) * u x) =
            ∑ x, ∑ z, (M⁻¹) z x * u x := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.sum_mul]
        _ = ∑ z, ∑ x, (M⁻¹) z x * u x := by
              rw [Finset.sum_comm]
        _ = ∑ z, c z := by
              apply Finset.sum_congr rfl
              intro z hz
              exact (hc_coord z).symm
    have hsecond :
        (FunctionalInequalities.Analysis.simplexEdgeMatrix w).det = M.det * (1 - ∑ j, c j) := by
      change
        (FunctionalInequalities.Analysis.simplexEdgeMatrix (Function.update v 0 y)).det =
          M.det * (1 - ∑ j, c j)
      rw [FunctionalInequalities.Analysis.simplexEdgeMatrix_update_zero]
      let U : Matrix (Fin n) (Fin 1) ℝ := Matrix.of fun i _ => -u i
      let V : Matrix (Fin 1) (Fin n) ℝ := Matrix.of fun _ _ => 1
      have hUV :
          M - Matrix.of (fun i _ => u i) = M + U * V := by
        ext i j
        simp [U, V, Matrix.mul_apply]
        ring
      rw [hUV]
      rw [Matrix.det_add_mul U V hunit]
      have hscalar :
          (V * M⁻¹ * U).det = -∑ j, c j := by
        rw [Matrix.det_fin_one]
        simp only [Matrix.mul_apply, V, U, Matrix.of_apply, one_mul, mul_neg,
          Finset.sum_neg_distrib]
        rw [hsum']
      have hplus :
          (1 + V * M⁻¹ * U).det = 1 - ∑ j, c j := by
        rw [Matrix.det_fin_one]
        rw [Matrix.add_apply]
        have hentry :
            (V * M⁻¹ * U) 0 0 = -∑ j, c j := by
          simpa only [Matrix.det_fin_one] using hscalar
        rw [hentry]
        simp [sub_eq_add_neg]
      rw [hplus]
    rw [hsecond] at hdetw
    have hmul : |M.det| * |1 - ∑ j, c j| ≤ |M.det| := by
      simpa [abs_mul, mul_comm] using hdetw
    have hpos : 0 < |M.det| := abs_pos.mpr (by simpa [M] using hdet)
    nlinarith
  simpa [M, c, u] using ⟨hcoord, hsum⟩
