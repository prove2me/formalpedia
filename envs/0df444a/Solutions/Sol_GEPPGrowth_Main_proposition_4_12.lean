-- Prove2me | solution 1 for GEPPGrowth.Main.proposition_4_12
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T21:56:44.765987+00:00
-- url     : https://prove2.me/submissions/e0980201-023d-499a-90d9-94a8a8ea8ef9

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GEPPGrowth.Main

/-- Rayleigh bound: `xᵀ M x ≤ ‖M‖ |x|²` for the l2 operator norm. -/
private lemma dot_mulVec_le_specNorm {d : ℕ} (M : Mat d) (x : Vec d) :
    x ⬝ᵥ (M *ᵥ x) ≤ GaussianMatrix.specNorm M * (x ⬝ᵥ x) := by
  have h := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 x)
  have hin := real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))
    ((EuclideanSpace.equiv (Fin d) ℝ).symm (M *ᵥ x))
  have hxx : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]; simp [dotProduct, sq]
  have hin' : x ⬝ᵥ (M *ᵥ x) = inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))
      ((EuclideanSpace.equiv (Fin d) ℝ).symm (M *ᵥ x)) := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hn0 := norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))
  simp only at h
  rw [hin', ← hxx]
  show _ ≤ ‖M‖ * _
  nlinarith

/-- For symmetric PSD `S` with `S v = λ v`, `|v| = 1`: `uᵀ S u ≥ λ (u·v)²`. -/
private lemma quad_ge_of_eig {d : ℕ} (S : Mat d) (hS : S.PosSemidef) (v : Vec d)
    (hv : v ⬝ᵥ v = 1) (lam : ℝ) (heig : S *ᵥ v = lam • v) (u : Vec d) :
    lam * (u ⬝ᵥ v) ^ 2 ≤ u ⬝ᵥ (S *ᵥ u) := by
  set a := u ⬝ᵥ v
  set u' := u - a • v with hu'
  have hu'v : u' ⬝ᵥ v = 0 := by
    simp [hu', sub_dotProduct, smul_dotProduct, hv, a]
  have hsymm : S.transpose = S := hS.1
  have hSu : S *ᵥ u = S *ᵥ u' + (a * lam) • v := by
    rw [show u = u' + a • v by simp [hu'], Matrix.mulVec_add, Matrix.mulVec_smul, heig, smul_smul]
  have hvS : v ⬝ᵥ (S *ᵥ u') = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, heig, smul_dotProduct,
      dotProduct_comm, hu'v, smul_zero]
  have key : u ⬝ᵥ (S *ᵥ u) = u' ⬝ᵥ (S *ᵥ u') + lam * a ^ 2 := by
    rw [hSu]
    conv_lhs => rw [show u = u' + a • v by simp [hu']]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, hvS, hu'v, hv,
      smul_eq_mul]
    ring
  have := hS.dotProduct_mulVec_nonneg u'
  simp at this
  nlinarith

/-- The squared length of the compressed top eigenvector. -/
private lemma compress_sq {d : ℕ} (v y : Vec (d+1)) (i : Fin (d+1)) (hyi : y i ≠ 0) :
    (compressionAt y i *ᵥ v) ⬝ᵥ (compressionAt y i *ᵥ v) =
      sqLength v - 2 * v i * deletedInner i v (ratiosAt y i) - 2 * v i ^ 2
        + v i ^ 2 * sqLength (ratiosAt y i) := by
  set r := ratiosAt y i with hr
  have hri : r i = 1 := by simp [hr, ratiosAt, hyi]
  set z : Vec (d+1) := fun j => v j - r j * v i with hz
  have hE : eliminationAt y i *ᵥ v = z := by
    ext j
    simp [eliminationAt, Matrix.vecMulVec, basisVector, Matrix.mulVec,
      dotProduct, hz, hr]
    simp [sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, ite_mul]
  have hD : ∀ w : Vec (d+1), deletion i *ᵥ w = fun a => w (Equiv.swap 0 i a.succ) := by
    intro w; ext a
    simp [deletion, Matrix.mulVec, dotProduct]
  have hzi : z i = 0 := by simp [hz, hri]
  have hsum : (∑ a : Fin d, z (Equiv.swap 0 i a.succ) ^ 2) = ∑ j, z j ^ 2 := by
    have := Equiv.sum_comp (Equiv.swap (0 : Fin (d+1)) i) (fun j => z j ^ 2)
    rw [Fin.sum_univ_succ] at this
    simp [hzi] at this
    simpa using this
  rw [compressionAt, ← Matrix.mulVec_mulVec, hE, hD]
  simp only [dotProduct]
  rw [show (∑ a : Fin d, z (Equiv.swap 0 i a.succ) * z (Equiv.swap 0 i a.succ)) =
    ∑ a : Fin d, z (Equiv.swap 0 i a.succ) ^ 2 by simp [sq], hsum]
  have hdel : deletedInner i v r = ∑ j, v j * r j - v i := by
    simp only [deletedInner]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j = i) (fun j => v j * r j)]
    simp [Finset.filter_eq', hri]
  rw [hdel]
  simp only [sqLength, hz]
  have : ∀ j, (v j - r j * v i) ^ 2 = v j ^ 2 - 2 * v i * (v j * r j) + v i ^ 2 * r j ^ 2 := by
    intro j; ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end GEPPGrowth.Main

open GEPPGrowth.Main

theorem solution (d : ℕ) (hd : 1 ≤ d) (S : Mat (d+1)) (hS : S.PosDef)
    (v : Vec (d+1)) (hv : sqLength v = 1)
    (heig : S *ᵥ v = GaussianMatrix.specNorm S • v)
    (y : Vec (d+1)) (hy : y ≠ 0) (i : Fin (d+1)) (hi : IsMaxPivot y i)
    (C : ℝ) (hC : 1 ≤ C)
    (hcoord : 1/((d+1:ℕ):ℝ) ≤ v i^2)
    (hlen : ((d+1:ℕ):ℝ)/C ≤ sqLength (ratiosAt y i))
    (hlarge : 2 ≤ ((d+1:ℕ):ℝ)/C)
    (hsign : v i * deletedInner i v (ratiosAt y i) ≤ 0) :
    (1 + 1/C - 2/((d+1:ℕ):ℝ)) * GaussianMatrix.specNorm S ≤
      GaussianMatrix.specNorm (updateAt S y i) := by
  set K := compressionAt y i with hK
  set lam := GaussianMatrix.specNorm S with hlam
  have hlam0 : 0 ≤ lam := by
    show 0 ≤ ‖S‖
    exact norm_nonneg _
  have hyi : y i ≠ 0 := by
    intro h0
    have : sqLength (ratiosAt y i) = 0 := by simp [sqLength, ratiosAt, h0]
    linarith
  have hvv : v ⬝ᵥ v = 1 := by rw [← hv]; simp [sqLength, dotProduct, sq]
  set w := K *ᵥ v with hw
  set u := K.transpose *ᵥ w with hu
  have hquad : w ⬝ᵥ (updateAt S y i *ᵥ w) = u ⬝ᵥ (S *ᵥ u) := by
    rw [updateAt, ← hK, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, ← hu]
  have huv : u ⬝ᵥ v = w ⬝ᵥ w := by
    rw [hu, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  have hn : (2:ℝ) ≤ ((d+1:ℕ):ℝ) := by push_cast; exact_mod_cast (by omega : 2 ≤ d + 1)
  have hn0 : (0:ℝ) < ((d+1:ℕ):ℝ) := by linarith
  have hC0 : 0 < C := by linarith
  have hww : 1 + 1/C - 2/((d+1:ℕ):ℝ) ≤ w ⬝ᵥ w := by
    rw [hw, compress_sq v y i hyi, hv]
    have hr2 : 0 ≤ sqLength (ratiosAt y i) - 2 := by linarith
    have h1 : 1/((d+1:ℕ):ℝ) * (sqLength (ratiosAt y i) - 2) ≤
        v i ^ 2 * (sqLength (ratiosAt y i) - 2) := mul_le_mul_of_nonneg_right hcoord hr2
    have h2 : 1/((d+1:ℕ):ℝ) * (((d+1:ℕ):ℝ)/C - 2) ≤
        1/((d+1:ℕ):ℝ) * (sqLength (ratiosAt y i) - 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 : 1/((d+1:ℕ):ℝ) * (((d+1:ℕ):ℝ)/C - 2) = 1/C - 2/((d+1:ℕ):ℝ) := by
      field_simp
    nlinarith
  have hc0 : 0 < 1 + 1/C - 2/((d+1:ℕ):ℝ) := by
    have : 2/((d+1:ℕ):ℝ) ≤ 1 := by rw [div_le_one hn0]; exact hn
    have : 0 < 1/C := by positivity
    linarith
  have hwpos : 0 < w ⬝ᵥ w := lt_of_lt_of_le hc0 hww
  have h1 := quad_ge_of_eig S hS.posSemidef v hvv lam heig u
  have h2 := dot_mulVec_le_specNorm (updateAt S y i) w
  rw [hquad] at h2
  rw [huv] at h1
  -- lam * |w|^4 ≤ ‖M‖ |w|^2
  have h3 : lam * (w ⬝ᵥ w) ≤ GaussianMatrix.specNorm (updateAt S y i) := by
    have := h1.trans h2
    nlinarith
  nlinarith
