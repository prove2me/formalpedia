-- Prove2me | solution 1 for FatkhullinPolyak.Discrete.lyapunov_eigen_lower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:49:27.793205+00:00
-- url     : https://prove2.me/submissions/6a88f28f-c941-412f-b024-ad5d838046e6

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix

namespace FatkhullinPolyak.Discrete

open Matrix

/-- Conjugating a nonnegative real diagonal by the eigenvector unitary. -/
lemma aux_lyeb_psd {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (N : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) (hEq : N = U * diagonal d * star U) :
    N.PosSemidef := by
  rw [hEq, star_eq_conjTranspose]
  exact (PosSemidef.diagonal (fun i => hd i)).mul_mul_conjTranspose_same _

lemma aux_lyeb_decomp {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) (c : ℝ) :
    M - c • (1 : Matrix (Fin n) (Fin n) ℝ) =
      (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) * diagonal (fun i => hM.eigenvalues i - c) *
        star (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
  set U := (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hUdef
  have hU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec := hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have h1 : diagonal (fun i => hM.eigenvalues i - c) =
      diagonal (RCLike.ofReal ∘ hM.eigenvalues) - c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  rw [h1, mul_sub, sub_mul, ← hspec, mul_smul_comm, mul_one, smul_mul_assoc, hU]

lemma aux_lyeb_lo {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) (c : ℝ)
    (hc : ∀ i, c ≤ hM.eigenvalues i) (x : Fin n → ℝ) :
    c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (M *ᵥ x) := by
  have hps := aux_lyeb_psd _ _ _ (fun i => sub_nonneg.2 (hc i)) (aux_lyeb_decomp M hM c)
  have h := hps.dotProduct_mulVec_nonneg x
  simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul] at h
  linarith

lemma aux_lyeb_hi {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) (c : ℝ)
    (hc : ∀ i, hM.eigenvalues i ≤ c) (x : Fin n → ℝ) :
    x ⬝ᵥ (M *ᵥ x) ≤ c * (x ⬝ᵥ x) := by
  have hEq : -(M - c • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
        diagonal (fun i => c - hM.eigenvalues i) *
        star (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
    rw [aux_lyeb_decomp M hM c]
    have : diagonal (fun i => c - hM.eigenvalues i) = - diagonal (fun i => hM.eigenvalues i - c) := by
      rw [diagonal_neg]; congr 1; funext i; ring
    rw [this, mul_neg, neg_mul]
  have hps := aux_lyeb_psd _ _ _ (fun i => sub_nonneg.2 (hc i)) hEq
  have h := hps.dotProduct_mulVec_nonneg x
  simp only [star_trivial, neg_mulVec, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
    dotProduct_neg, dotProduct_smul, smul_eq_mul] at h
  linarith

lemma aux_lyeb_sym {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (hXs : Xᵀ = X) (y z : Fin n → ℝ) :
    y ⬝ᵥ (X *ᵥ z) = z ⬝ᵥ (X *ᵥ y) := by
  have h : y ᵥ* X = X *ᵥ y := by
    conv_lhs => rw [← hXs]
    exact vecMul_transpose X y
  rw [dotProduct_mulVec, h, dotProduct_comm]

lemma aux_lyeb_quad {n : ℕ} (A X Q : Matrix (Fin n) (Fin n) ℝ) (hXs : Xᵀ = X)
    (hLyap : A.transpose * X + X * A + Q = 0) (x : Fin n → ℝ) :
    x ⬝ᵥ (Q *ᵥ x) = -2 * (x ⬝ᵥ (X *ᵥ (A *ᵥ x))) := by
  have hQ : Q = -(A.transpose * X + X * A) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hLyap
  rw [hQ, neg_mulVec, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_neg,
    dotProduct_add, dotProduct_mulVec x Aᵀ, vecMul_transpose, aux_lyeb_sym X hXs (A *ᵥ x) x]
  ring

lemma aux_lyeb_eigvec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (hz : z ∈ spectrum ℂ M) :
    ∃ v : Fin n → ℂ, v ≠ 0 ∧ M *ᵥ v = z • v := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hz
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hz
  refine ⟨v, hv0, ?_⟩
  rw [sub_mulVec, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec, sub_eq_zero] at hv
  exact hv.symm

lemma aux_lyeb_split {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (z : ℂ) (v : Fin n → ℂ)
    (hv : A.map (algebraMap ℝ ℂ) *ᵥ v = z • v) :
    A *ᵥ (fun j => (v j).re) = z.re • (fun j => (v j).re) - z.im • (fun j => (v j).im) ∧
    A *ᵥ (fun j => (v j).im) = z.im • (fun j => (v j).re) + z.re • (fun j => (v j).im) := by
  constructor
  · funext i
    have h := congrArg Complex.re (congrFun hv i)
    simp [mulVec, dotProduct, Complex.re_sum] at h
    simp [mulVec, dotProduct, h]
  · funext i
    have h := congrArg Complex.im (congrFun hv i)
    simp [mulVec, dotProduct, Complex.im_sum] at h
    simp [mulVec, dotProduct, h]
    ring

lemma aux_lyeb_pos {n : ℕ} (v : Fin n → ℂ) (hv : v ≠ 0) :
    0 < (fun j => (v j).re) ⬝ᵥ (fun j => (v j).re) + (fun j => (v j).im) ⬝ᵥ (fun j => (v j).im) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  have : (fun j => (v j).re) ⬝ᵥ (fun j => (v j).re) + (fun j => (v j).im) ⬝ᵥ (fun j => (v j).im)
      = ∑ j, Complex.normSq (v j) := by
    simp [dotProduct, Complex.normSq_apply, Finset.sum_add_distrib]
  rw [this]
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩

open scoped Matrix.Norms.L2Operator in
lemma aux_lyeb_opn {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (e : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖ = 1) : |(WithLp.ofLp e) ⬝ᵥ (A *ᵥ WithLp.ofLp e)| ≤ specNorm A := by
  have h1 := Matrix.l2_opNorm_mulVec A e
  have h2 := abs_real_inner_le_norm e ((EuclideanSpace.equiv (Fin n) ℝ).symm (A *ᵥ e))
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h2
  simp at h2
  have h3 : ‖WithLp.toLp 2 (A *ᵥ WithLp.ofLp e)‖ ≤ ‖A‖ * ‖e‖ := h1
  rw [he] at h2 h3
  rw [dotProduct_comm]
  show _ ≤ ‖A‖
  linarith

end FatkhullinPolyak.Discrete

open FatkhullinPolyak.Discrete
open Matrix

theorem solution {n : ℕ} (A X Q : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsHurwitz A) (hQ : Q.PosDef) (hX : X.PosDef)
    (hLyap : A.transpose * X + X * A + Q = 0) :
    lamMin Q / (2 * stabDegree A) ≤ lamMax X ∧
      lamMin Q / (2 * specNorm A) ≤ lamMin X := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [lamMin, lamMax]
  have hXs : X.transpose = X := by
    have h := hX.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hlamQ : ∀ i, lamMin Q ≤ hQ.1.eigenvalues i := by
    intro i
    rw [lamMin, dif_pos hQ.1, dif_pos hn]
    exact Finset.inf'_le _ (Finset.mem_univ i)
  have hlamX : ∀ i, hX.1.eigenvalues i ≤ lamMax X := by
    intro i
    rw [lamMax, dif_pos hX.1, dif_pos hn]
    exact Finset.le_sup' _ (Finset.mem_univ i)
  constructor
  · set M := A.map (algebraMap ℝ ℂ) with hM
    have hne : (spectrum ℂ M).Nonempty := by
      have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      exact spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ M
    have hfin := Matrix.finite_spectrum M
    obtain ⟨z, hz, hzre⟩ := (hne.image Complex.re).csSup_mem (hfin.image _)
    have hstab : stabDegree A = -z.re := by
      simp only [stabDegree, maxRe]
      rw [← hM, hzre]
    have hzneg : z.re < 0 := hA z hz
    obtain ⟨v, hv0, hv⟩ := aux_lyeb_eigvec M z hz
    obtain ⟨ha, hb⟩ := aux_lyeb_split A z v hv
    have hpos := aux_lyeb_pos v hv0
    set a : Fin n → ℝ := fun j => (v j).re with hadef
    set b : Fin n → ℝ := fun j => (v j).im with hbdef
    have hqa := aux_lyeb_quad A X Q hXs hLyap a
    have hqb := aux_lyeb_quad A X Q hXs hLyap b
    have key : a ⬝ᵥ (Q *ᵥ a) + b ⬝ᵥ (Q *ᵥ b) =
        -2 * z.re * (a ⬝ᵥ (X *ᵥ a) + b ⬝ᵥ (X *ᵥ b)) := by
      rw [hqa, hqb, ha, hb, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_sub, dotProduct_add,
        dotProduct_smul, dotProduct_smul, dotProduct_smul, dotProduct_smul, smul_eq_mul,
        smul_eq_mul, smul_eq_mul, smul_eq_mul, aux_lyeb_sym X hXs b a]
      ring
    have loa := aux_lyeb_lo Q hQ.1 _ hlamQ a
    have lob := aux_lyeb_lo Q hQ.1 _ hlamQ b
    have hia := aux_lyeb_hi X hX.1 _ hlamX a
    have hib := aux_lyeb_hi X hX.1 _ hlamX b
    rw [hstab, div_le_iff₀ (by linarith)]
    have hc : 0 ≤ -2 * z.re := by linarith
    have h1 : -2 * z.re * (a ⬝ᵥ (X *ᵥ a) + b ⬝ᵥ (X *ᵥ b)) ≤
        -2 * z.re * (lamMax X * (a ⬝ᵥ a + b ⬝ᵥ b)) :=
      mul_le_mul_of_nonneg_left (by linarith) hc
    have h2 : lamMin Q * (a ⬝ᵥ a + b ⬝ᵥ b) ≤ (lamMax X * (2 * -z.re)) * (a ⬝ᵥ a + b ⬝ᵥ b) := by
      nlinarith
    exact le_of_mul_le_mul_right h2 hpos
  · obtain ⟨i0, _, hi0⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty_iff.2 ⟨⟨0, hn⟩⟩)
      hX.1.eigenvalues
    have hlamX0 : lamMin X = hX.1.eigenvalues i0 := by
      rw [lamMin, dif_pos hX.1, dif_pos hn]
      exact hi0
    set e := hX.1.eigenvectorBasis i0 with hedef
    have he : ‖e‖ = 1 := hX.1.eigenvectorBasis.orthonormal.1 i0
    set u : Fin n → ℝ := WithLp.ofLp e with hudef
    have hXu : X *ᵥ u = hX.1.eigenvalues i0 • u := hX.1.mulVec_eigenvectorBasis i0
    have hu1 : u ⬝ᵥ u = 1 := by
      have h := real_inner_self_eq_norm_sq e
      rw [EuclideanSpace.inner_eq_star_dotProduct, he] at h
      simpa using h
    have hq := aux_lyeb_quad A X Q hXs hLyap u
    rw [aux_lyeb_sym X hXs u (A *ᵥ u), hXu, dotProduct_smul, smul_eq_mul,
      dotProduct_comm (A *ᵥ u) u] at hq
    have lo := aux_lyeb_lo Q hQ.1 _ hlamQ u
    have hop := aux_lyeb_opn A e he
    rw [← hudef] at hop
    have hlpos : 0 < hX.1.eigenvalues i0 := hX.eigenvalues_pos i0
    have hsn : 0 ≤ specNorm A := le_trans (abs_nonneg _) hop
    rw [hlamX0]
    rcases hsn.eq_or_lt with h0 | h0
    · rw [← h0]; simp; exact hlpos.le
    rw [div_le_iff₀ (by linarith)]
    rw [hu1] at lo
    have habs := neg_abs_le (u ⬝ᵥ (A *ᵥ u))
    nlinarith
