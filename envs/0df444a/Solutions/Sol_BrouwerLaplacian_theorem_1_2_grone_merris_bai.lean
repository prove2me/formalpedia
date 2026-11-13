-- Prove2me | solution 1 for BrouwerLaplacian.theorem_1_2_grone_merris_bai
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T18:12:30.777962+00:00
-- url     : https://prove2.me/submissions/0657aed4-e21e-42b8-863b-67e87d2cb10e

import Mathlib
import Definitions.Def_BrouwerLaplacian_conjDeg
import Definitions.Def_BrouwerLaplacian_IsSplitWith
section
namespace BrouwerLaplacian.Dev.Common

open Matrix

end BrouwerLaplacian.Dev.Common
end

section
namespace BrouwerLaplacian.Dev.TopK

open Finset Matrix BrouwerLaplacian

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

/-- the eigenvalues, sorted decreasingly -/
noncomputable def ev (hA : A.IsHermitian) : Fin (Fintype.card (Fin n)) → ℝ := hA.eigenvalues₀

/-- eigenvector -/
noncomputable def bv (hA : A.IsHermitian) (i : Fin (Fintype.card (Fin n))) : Fin n → ℝ :=
  ((isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace i).ofLp

theorem bv_dot (hA : A.IsHermitian) (i j : Fin (Fintype.card (Fin n))) :
    bv hA i ⬝ᵥ bv hA j = if i = j then 1 else 0 := by
  have := orthonormal_iff_ite.1
    ((isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace).orthonormal i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at this
  simpa [bv, dotProduct_comm] using this

theorem mulVec_bv (hA : A.IsHermitian) (i : Fin (Fintype.card (Fin n))) :
    A *ᵥ bv hA i = ev hA i • bv hA i := by
  have := (isSymmetric_toEuclideanLin_iff.mpr hA).apply_eigenvectorBasis finrank_euclideanSpace i
  have h2 := congrArg WithLp.ofLp this
  rw [Matrix.piLp_ofLp_toEuclideanLin, Matrix.toLin'_apply] at h2
  exact h2

/-- projection onto the span of the eigenvectors indexed by `S` -/
noncomputable def projS (hA : A.IsHermitian) (S : Finset (Fin (Fintype.card (Fin n)))) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ i ∈ S, vecMulVec (bv hA i) (bv hA i)

theorem projS_symm (hA : A.IsHermitian) (S : Finset (Fin (Fintype.card (Fin n)))) :
    (projS hA S)ᵀ = projS hA S := by
  ext a b
  simp [projS, Matrix.transpose_apply, Matrix.sum_apply, vecMulVec_apply, mul_comm]

theorem projS_idem (hA : A.IsHermitian) (S : Finset (Fin (Fintype.card (Fin n)))) :
    projS hA S * projS hA S = projS hA S := by
  unfold projS
  rw [Finset.sum_mul]
  refine sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum]
  have : ∀ j ∈ S, vecMulVec (bv hA i) (bv hA i) * vecMulVec (bv hA j) (bv hA j)
      = if i = j then vecMulVec (bv hA i) (bv hA i) else 0 := by
    intro j _
    rw [vecMulVec_mul_vecMulVec, bv_dot]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [sum_congr rfl this]
  simp [hi]

theorem projS_mulVec (hA : A.IsHermitian) (S : Finset (Fin (Fintype.card (Fin n))))
    (j : Fin (Fintype.card (Fin n))) :
    projS hA S *ᵥ bv hA j = if j ∈ S then bv hA j else 0 := by
  unfold projS
  rw [Matrix.sum_mulVec]
  have : ∀ i ∈ S, vecMulVec (bv hA i) (bv hA i) *ᵥ bv hA j
      = if i = j then bv hA j else 0 := by
    intro i _
    rw [vecMulVec_mulVec, bv_dot]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [sum_congr rfl this]
  simp [Finset.sum_ite_eq]

theorem projS_trace (hA : A.IsHermitian) (S : Finset (Fin (Fintype.card (Fin n)))) :
    (projS hA S).trace = S.card := by
  unfold projS
  rw [Matrix.trace_sum]
  simp [bv_dot]

theorem projS_trace_A (hA : A.IsHermitian) (S : Finset (Fin (Fintype.card (Fin n)))) :
    (projS hA S * A).trace = ∑ i ∈ S, ev hA i := by
  unfold projS
  rw [Finset.sum_mul, Matrix.trace_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [vecMulVec_mul, Matrix.trace_vecMulVec]
  have : bv hA i ᵥ* A = ev hA i • bv hA i := by
    have hAT : Aᵀ = A := by
      have := hA.eq
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
    have := Matrix.vecMul_transpose A (bv hA i)
    rw [hAT] at this
    rw [this]
    exact mulVec_bv hA i
  rw [this, dotProduct_smul, bv_dot]
  simp

end BrouwerLaplacian.Dev.TopK
end

section
namespace BrouwerLaplacian.Dev.Transfer

open Finset Matrix

theorem eig_sum_transfer {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {A : Matrix V V ℝ} {B : Matrix W W ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hch : A.charpoly = B.charpoly) (k : ℕ) :
    ∑ i : Fin (Fintype.card V) with i.val < k, hA.eigenvalues₀ i
      = ∑ i : Fin (Fintype.card W) with i.val < k, hB.eigenvalues₀ i := by
  rw [← List.sum_take_ofFn, ← List.sum_take_ofFn, ← hA.sort_roots_charpoly_eq_eigenvalues₀,
    ← hB.sort_roots_charpoly_eq_eigenvalues₀, hch]

theorem lap_comap {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (e : Fin n ≃ V) :
    (G.comap e).lapMatrix ℝ = Matrix.reindex e.symm e.symm (G.lapMatrix ℝ) := by
  ext a b
  have hdeg : (G.comap e).degree a = G.degree (e a) :=
    ((SimpleGraph.Iso.comap e G).degree_eq a).symm
  by_cases hab : a = b
  · subst hab
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, hdeg]
  · simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, hab, SimpleGraph.adjMatrix_apply,
      e.injective.ne hab]

theorem eig_sum_graph {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (e : Fin n ≃ V) (k : ℕ) :
    ∑ i : Fin (Fintype.card V) with i.val < k, (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i
      = ∑ i : Fin (Fintype.card (Fin n)) with i.val < k,
          ((G.comap e).isHermitian_lapMatrix ℝ).eigenvalues₀ i := by
  apply eig_sum_transfer
  rw [lap_comap G e, Matrix.charpoly_reindex]

end BrouwerLaplacian.Dev.Transfer
end

section
namespace BrouwerLaplacian.Dev.Split32

open Finset

variable {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]

theorem conj_sum (k : ℕ) :
    ∑ j ∈ Icc 1 k, (BrouwerLaplacian.conjDeg H j : ℝ) = ((∑ v, min (H.degree v) k : ℕ) : ℝ) := by
  have h1 : ∀ j, BrouwerLaplacian.conjDeg H j = ∑ v, if j ≤ H.degree v then 1 else 0 := by
    intro j; unfold BrouwerLaplacian.conjDeg; rw [Finset.card_filter]
  have h2 : ∀ v, ((Icc 1 k).filter (fun j => j ≤ H.degree v)).card = min (H.degree v) k := by
    intro v
    have : (Icc 1 k).filter (fun j => j ≤ H.degree v) = Icc 1 (min (H.degree v) k) := by
      ext j; simp only [mem_filter, mem_Icc]; omega
    rw [this]; simp
  have : ∑ j ∈ Icc 1 k, BrouwerLaplacian.conjDeg H j = ∑ v, min (H.degree v) k := by
    simp only [h1]
    rw [sum_comm]
    refine sum_congr rfl fun v _ => ?_
    rw [← sum_filter, sum_const, smul_eq_mul, mul_one, h2]
  rw [← this]; push_cast; rfl

end BrouwerLaplacian.Dev.Split32
end

section
namespace BrouwerLaplacian.Dev.GMB
open Finset Matrix BrouwerLaplacian
variable {n : ℕ}
/-!
Blueprint for the Grone–Merris–Bai theorem (H. Bai, *The Grone–Merris conjecture*,
Trans. AMS 363 (2011), arXiv:0911.2172v4).

Interfaces, each proved in its Part below:
* Part A (spectral toolkit): `trace_mul_le_topSum` (Ky Fan), `topProj_*`, `le_eigenvalue_of_subspace`,
  `eigenvalue_le_of_subspace` (Courant–Fischer bounds), `eigenvalue_mono`.
* Part B: `topProj_continuousOn` (continuity of the top-`k` spectral projection under a gap).
* Part C: `prop5_upper`, `prop5_lower`, `lemma6` (Bai's Proposition 5 and Lemma 6, homotopy).
* Part D: `gm_fin` (Bai §4, minimal counterexample), from A, C.
-/
/-- The sum of the `k` largest eigenvalues of a symmetric matrix. -/
noncomputable def topSum {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : ℕ) : ℝ :=
  ∑ i : Fin (Fintype.card (Fin n)) with i.val < k, hA.eigenvalues₀ i

/-- The orthogonal projection onto the span of the eigenvectors of the `k` largest eigenvalues. -/
noncomputable def topProj {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Dev.TopK.projS hA (univ.filter (fun i : Fin (Fintype.card (Fin n)) => i.val < k))

end BrouwerLaplacian.Dev.GMB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartA
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB BrouwerLaplacian.Dev.TopK
variable {n : ℕ}
variable {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
/-! Part A: spectral toolkit (Ky Fan, top projections, Courant–Fischer, Weyl). -/
omit hA in
theorem transpose_eq (hA : A.IsHermitian) : Aᵀ = A := by
  have := hA.eq
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

omit hA in
theorem dot_mulVec_symm (hA : A.IsHermitian) (x y : Fin n → ℝ) : x ⬝ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, transpose_eq hA]

theorem dot_self_nonneg (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x := by
  simp only [dotProduct]; exact sum_nonneg fun i _ => mul_self_nonneg _

theorem dot_self_pos {x : Fin n → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  rcases (dot_self_nonneg x).lt_or_eq with h | h
  · exact h
  · exact absurd (dotProduct_self_eq_zero.1 h.symm) hx

/-- completeness of the eigenbasis -/
theorem expand (x : Fin n → ℝ) : ∑ i, (bv hA i ⬝ᵥ x) • bv hA i = x := by
  set B := (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace
  have h := B.sum_repr' (WithLp.toLp 2 x)
  have h2 := congrArg WithLp.ofLp h
  rw [WithLp.ofLp_sum] at h2
  simp only [WithLp.ofLp_smul, EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h2
  convert h2 using 2 with i
  simp [bv, B, dotProduct_comm]

theorem dot_expand (x y : Fin n → ℝ) : x ⬝ᵥ y = ∑ i, (bv hA i ⬝ᵥ x) * (bv hA i ⬝ᵥ y) := by
  conv_lhs => rw [← expand hA x]
  rw [sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul]

theorem dot_self_expand (x : Fin n → ℝ) : x ⬝ᵥ x = ∑ i, (bv hA i ⬝ᵥ x) ^ 2 := by
  rw [dot_expand hA x x]; simp [sq]

theorem bv_dot_mulVec (i : Fin (Fintype.card (Fin n))) (x : Fin n → ℝ) :
    bv hA i ⬝ᵥ (A *ᵥ x) = ev hA i * (bv hA i ⬝ᵥ x) := by
  rw [dot_mulVec_symm hA, mulVec_bv, smul_dotProduct, smul_eq_mul]

theorem quad_expand (x : Fin n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ i, ev hA i * (bv hA i ⬝ᵥ x) ^ 2 := by
  rw [dot_expand hA x (A *ᵥ x)]
  refine sum_congr rfl fun i _ => ?_
  rw [bv_dot_mulVec]; ring

theorem sum_vecMulVec : ∑ i, vecMulVec (bv hA i) (bv hA i) = 1 := by
  ext a b
  have := congrFun (expand hA (Pi.single b 1)) a
  rw [Finset.sum_apply] at this
  rw [Matrix.sum_apply]
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, dotProduct_single, mul_one] at this ⊢
  rw [Matrix.one_apply]
  simp only [Pi.single_apply] at this
  rw [← this]
  refine sum_congr rfl fun i _ => by ring

theorem projS_mulVec' (S : Finset (Fin (Fintype.card (Fin n)))) (x : Fin n → ℝ) :
    projS hA S *ᵥ x = ∑ i ∈ S, (bv hA i ⬝ᵥ x) • bv hA i := by
  unfold projS
  rw [Matrix.sum_mulVec]
  refine sum_congr rfl fun i _ => ?_
  rw [vecMulVec_mulVec, op_smul_eq_smul]

theorem bv_dot_projS (S : Finset (Fin (Fintype.card (Fin n)))) (x : Fin n → ℝ)
    (j : Fin (Fintype.card (Fin n))) :
    bv hA j ⬝ᵥ (projS hA S *ᵥ x) = if j ∈ S then bv hA j ⬝ᵥ x else 0 := by
  rw [projS_mulVec', dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul, bv_dot]
  simp [Finset.sum_ite_eq']

theorem quad_le_of_low (i : Fin (Fintype.card (Fin n))) (x : Fin n → ℝ)
    (hx : ∀ j : Fin (Fintype.card (Fin n)), j < i → bv hA j ⬝ᵥ x = 0) :
    x ⬝ᵥ (A *ᵥ x) ≤ ev hA i * (x ⬝ᵥ x) := by
  rw [quad_expand hA, dot_self_expand hA, mul_sum]
  refine sum_le_sum fun j _ => ?_
  rcases lt_or_ge j i with h | h
  · rw [hx j h]; simp
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone h) (sq_nonneg _)

theorem quad_ge_of_high (i : Fin (Fintype.card (Fin n))) (x : Fin n → ℝ)
    (hx : ∀ j : Fin (Fintype.card (Fin n)), i < j → bv hA j ⬝ᵥ x = 0) :
    ev hA i * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  rw [quad_expand hA, dot_self_expand hA, mul_sum]
  refine sum_le_sum fun j _ => ?_
  rcases lt_or_ge i j with h | h
  · rw [hx j h]; simp
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone h) (sq_nonneg _)

/-- the subspace orthogonal to the eigenvectors indexed by `T` -/
noncomputable def kerT (T : Finset (Fin (Fintype.card (Fin n)))) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (Matrix.mulVecLin (Matrix.of fun (j : T) => bv hA j.1))

theorem mem_kerT (T : Finset (Fin (Fintype.card (Fin n)))) (x : Fin n → ℝ) :
    x ∈ kerT hA T ↔ ∀ j ∈ T, bv hA j ⬝ᵥ x = 0 := by
  unfold kerT
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro h j hj
    have := congrFun h ⟨j, hj⟩
    simpa [mulVec] using this
  · intro h
    funext j
    simpa [mulVec] using h j.1 j.2

theorem finrank_kerT (T : Finset (Fin (Fintype.card (Fin n)))) :
    n ≤ Module.finrank ℝ (kerT hA T) + #T := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (Matrix.mulVecLin (Matrix.of fun (j : T) => bv hA j.1))
  have h2 := Submodule.finrank_le (LinearMap.range (Matrix.mulVecLin (Matrix.of fun (j : T) => bv hA j.1)))
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_fin] at h h2
  unfold kerT
  omega

theorem exists_inter (W : Submodule ℝ (Fin n → ℝ)) (T : Finset (Fin (Fintype.card (Fin n))))
    (h : #T < Module.finrank ℝ W) :
    ∃ x ∈ W, x ≠ 0 ∧ ∀ j ∈ T, bv hA j ⬝ᵥ x = 0 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (kerT hA T)
  have h2 := Submodule.finrank_le (W ⊔ kerT hA T)
  have h3 := finrank_kerT hA T
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
  have hne : W ⊓ kerT hA T ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at h1
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Submodule.mem_inf] at hx
  exact ⟨x, hx.1, hx0, (mem_kerT hA T x).1 hx.2⟩

end BrouwerLaplacian.Dev.GMB.PartA
end

section
namespace BrouwerLaplacian.Dev.GMB.PartA
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB BrouwerLaplacian.Dev.TopK
variable {n : ℕ}
/-! ### Ky Fan -/
theorem kyfan_real {m : ℕ} (e w : Fin m → ℝ) (he : Antitone e) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∀ i, w i ≤ 1) (k : ℕ) (hs : ∑ i, w i = k) :
    ∑ i, e i * w i ≤ ∑ i with i.val < k, e i := by
  have hkm : k ≤ m := by
    have : ∑ i, w i ≤ ∑ _i : Fin m, (1 : ℝ) := sum_le_sum fun i _ => hw1 i
    simp at this
    exact_mod_cast hs ▸ this
  have hcard : (#(univ.filter fun i : Fin m => i.val < k) : ℝ) = k := by
    have := Fin.card_filter_val_lt (n := m) (m := k)
    rw [this, min_eq_right hkm]
  obtain ⟨c, hc1, hc2⟩ : ∃ c : ℝ, (∀ i : Fin m, i.val < k → c ≤ e i) ∧
      (∀ i : Fin m, k ≤ i.val → e i ≤ c) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rcases Nat.eq_zero_or_pos m with hm | hm
      · exact ⟨0, fun i => absurd i.2 (by omega), fun i => absurd i.2 (by omega)⟩
      · exact ⟨e ⟨0, hm⟩, fun i hi => absurd hi (by omega),
          fun i _ => he (Fin.mk_le_mk.2 (Nat.zero_le _) : (⟨0, hm⟩ : Fin m) ≤ i)⟩
    · refine ⟨e ⟨k - 1, by omega⟩, fun i hi => he ?_, fun i hi => he ?_⟩
      · show i.val ≤ k - 1; omega
      · show k - 1 ≤ i.val; omega
  have key : ∀ i : Fin m, c * ((if i.val < k then 1 else 0) - w i)
      ≤ (if i.val < k then e i else 0) - e i * w i := by
    intro i
    split_ifs with h
    · have := hc1 i h; nlinarith [hw1 i]
    · have := hc2 i (by omega); nlinarith [hw0 i]
  have hsum := sum_le_sum fun i (_ : i ∈ univ) => key i
  rw [← mul_sum, sum_sub_distrib, sum_sub_distrib, ← sum_filter, ← sum_filter] at hsum
  simp only [sum_const, nsmul_eq_mul, mul_one] at hsum
  rw [hcard, hs, sub_self, mul_zero] at hsum
  linarith

end BrouwerLaplacian.Dev.GMB.PartA
end

section
namespace BrouwerLaplacian.Dev.GMB.PartA
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB BrouwerLaplacian.Dev.TopK
variable {n : ℕ}
variable {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
theorem proj_quad_le {P : Matrix (Fin n) (Fin n) ℝ} (hPs : Pᵀ = P) (hPP : P * P = P)
    (w : Fin n → ℝ) : w ⬝ᵥ (P *ᵥ w) ≤ w ⬝ᵥ w := by
  set y := P *ᵥ w with hy
  have h1 : w ⬝ᵥ y = y ⬝ᵥ y := by
    have : y = P *ᵥ y := by rw [hy, mulVec_mulVec, hPP]
    conv_lhs => rw [this]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hPs]
  have h2 : 0 ≤ (w - y) ⬝ᵥ (w - y) := dot_self_nonneg _
  have h3 : (w - y) ⬝ᵥ (w - y) = w ⬝ᵥ w - 2 * (w ⬝ᵥ y) + y ⬝ᵥ y := by
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm y w]; ring
  linarith

theorem proj_quad_nonneg {P : Matrix (Fin n) (Fin n) ℝ} (hPs : Pᵀ = P) (hPP : P * P = P)
    (w : Fin n → ℝ) : 0 ≤ w ⬝ᵥ (P *ᵥ w) := by
  have : w ⬝ᵥ (P *ᵥ w) = (P *ᵥ w) ⬝ᵥ (P *ᵥ w) := by
    conv_lhs => rw [← hPP, ← mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hPs]
  rw [this]; exact dot_self_nonneg _

theorem trace_mul_vecMulVec' (P : Matrix (Fin n) (Fin n) ℝ) (hPs : Pᵀ = P) (w : Fin n → ℝ) :
    (P * vecMulVec w w).trace = w ⬝ᵥ (P *ᵥ w) := by
  rw [Matrix.trace_mul_comm, vecMulVec_mul, Matrix.trace_vecMulVec, ← Matrix.mulVec_transpose,
    hPs]

theorem spectral_sum : A = ∑ i, ev hA i • vecMulVec (bv hA i) (bv hA i) := by
  conv_lhs => rw [← Matrix.mul_one A, ← sum_vecMulVec hA]
  rw [Finset.mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_vecMulVec, mulVec_bv, smul_vecMulVec]

end BrouwerLaplacian.Dev.GMB.PartA
end

section
namespace BrouwerLaplacian.Dev.GMB.PartA
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB BrouwerLaplacian.Dev.TopK
variable {n : ℕ}
/-! ### Targets -/
theorem trace_mul_le_topSum {A P : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hPs : Pᵀ = P) (hPP : P * P = P) {k : ℕ} (hk : P.trace = k) :
    (P * A).trace ≤ topSum hA k := by
  have h1 : (P * A).trace = ∑ i, ev hA i * (bv hA i ⬝ᵥ (P *ᵥ bv hA i)) := by
    conv_lhs => rw [spectral_sum hA]
    rw [Finset.mul_sum, Matrix.trace_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_smul, Matrix.trace_smul, trace_mul_vecMulVec' P hPs, smul_eq_mul]
  have h2 : ∑ i, bv hA i ⬝ᵥ (P *ᵥ bv hA i) = k := by
    rw [← hk]
    conv_rhs => rw [← Matrix.mul_one P, ← sum_vecMulVec hA, Finset.mul_sum, Matrix.trace_sum]
    exact sum_congr rfl fun i _ => (trace_mul_vecMulVec' P hPs _).symm
  rw [h1]
  unfold topSum
  refine kyfan_real (ev hA) _ hA.eigenvalues₀_antitone (fun i => proj_quad_nonneg hPs hPP _)
    (fun i => ?_) k h2
  have := proj_quad_le hPs hPP (bv hA i)
  rwa [bv_dot, if_pos rfl] at this

end BrouwerLaplacian.Dev.GMB.PartA
end

section
namespace BrouwerLaplacian.Dev.GMB
open Finset Matrix BrouwerLaplacian
variable {n : ℕ}
/-! ### Part A: spectral toolkit -/
alias trace_mul_le_topSum := BrouwerLaplacian.Dev.GMB.PartA.trace_mul_le_topSum

end BrouwerLaplacian.Dev.GMB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartA
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB BrouwerLaplacian.Dev.TopK
variable {n : ℕ}
theorem topProj_transpose {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : ℕ) :
    (topProj hA k)ᵀ = topProj hA k := projS_symm hA _

end BrouwerLaplacian.Dev.GMB.PartA
end

section
namespace BrouwerLaplacian.Dev.GMB
open Finset Matrix BrouwerLaplacian
variable {n : ℕ}
alias topProj_transpose := BrouwerLaplacian.Dev.GMB.PartA.topProj_transpose

end BrouwerLaplacian.Dev.GMB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartA
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB BrouwerLaplacian.Dev.TopK
variable {n : ℕ}
theorem topProj_idem {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : ℕ) :
    topProj hA k * topProj hA k = topProj hA k := projS_idem hA _

end BrouwerLaplacian.Dev.GMB.PartA
end

section
namespace BrouwerLaplacian.Dev.GMB
open Finset Matrix BrouwerLaplacian
variable {n : ℕ}
alias topProj_idem := BrouwerLaplacian.Dev.GMB.PartA.topProj_idem

end BrouwerLaplacian.Dev.GMB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartA
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB BrouwerLaplacian.Dev.TopK
variable {n : ℕ}
theorem topProj_trace {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) {k : ℕ} (hk : k ≤ n) :
    (topProj hA k).trace = k := by
  unfold topProj
  rw [projS_trace, Fin.card_filter_val_lt, Fintype.card_fin, min_eq_right hk]

end BrouwerLaplacian.Dev.GMB.PartA
end

section
namespace BrouwerLaplacian.Dev.GMB
open Finset Matrix BrouwerLaplacian
variable {n : ℕ}
alias topProj_trace := BrouwerLaplacian.Dev.GMB.PartA.topProj_trace

end BrouwerLaplacian.Dev.GMB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartA
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB BrouwerLaplacian.Dev.TopK
variable {n : ℕ}
theorem topProj_trace_mul {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : ℕ) :
    (topProj hA k * A).trace = topSum hA k := by
  unfold topProj topSum
  rw [projS_trace_A]; rfl

end BrouwerLaplacian.Dev.GMB.PartA
end

section
namespace BrouwerLaplacian.Dev.GMB
open Finset Matrix BrouwerLaplacian
variable {n : ℕ}
alias topProj_trace_mul := BrouwerLaplacian.Dev.GMB.PartA.topProj_trace_mul

end BrouwerLaplacian.Dev.GMB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartA
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB BrouwerLaplacian.Dev.TopK
variable {n : ℕ}
theorem topProj_comm {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : ℕ) :
    A * topProj hA k = topProj hA k * A := by
  unfold topProj projS
  rw [Finset.mul_sum, Finset.sum_mul]
  refine sum_congr rfl fun i _ => ?_
  have : bv hA i ᵥ* A = ev hA i • bv hA i := by
    have h := Matrix.vecMul_transpose A (bv hA i)
    rw [transpose_eq hA] at h
    rw [h, mulVec_bv]
  rw [mul_vecMulVec, vecMulVec_mul, mulVec_bv, this, smul_vecMulVec, vecMulVec_smul]

end BrouwerLaplacian.Dev.GMB.PartA
end

section
namespace BrouwerLaplacian.Dev.GMB
open Finset Matrix BrouwerLaplacian
variable {n : ℕ}
alias topProj_comm := BrouwerLaplacian.Dev.GMB.PartA.topProj_comm

end BrouwerLaplacian.Dev.GMB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartA
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB BrouwerLaplacian.Dev.TopK
variable {n : ℕ}
theorem topProj_rayleigh {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : ℕ) (c : ℝ)
    (hc : ∀ i : Fin (Fintype.card (Fin n)), i.val < k → c ≤ hA.eigenvalues₀ i)
    (x : Fin n → ℝ) (hx : topProj hA k *ᵥ x = x) :
    c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  rw [quad_expand hA, dot_self_expand hA, mul_sum]
  refine sum_le_sum fun j _ => ?_
  by_cases hj : j.val < k
  · exact mul_le_mul_of_nonneg_right (hc j hj) (sq_nonneg _)
  · have : bv hA j ⬝ᵥ x = 0 := by
      have h := bv_dot_projS hA (univ.filter fun i : Fin (Fintype.card (Fin n)) => i.val < k) x j
      unfold topProj at hx
      rw [hx, if_neg (by simpa using hj)] at h
      exact h
    rw [this]; simp

end BrouwerLaplacian.Dev.GMB.PartA
end

section
namespace BrouwerLaplacian.Dev.GMB
open Finset Matrix BrouwerLaplacian
variable {n : ℕ}
alias topProj_rayleigh := BrouwerLaplacian.Dev.GMB.PartA.topProj_rayleigh

end BrouwerLaplacian.Dev.GMB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartA
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB BrouwerLaplacian.Dev.TopK
variable {n : ℕ}
theorem topProj_mulVec_one {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : ℕ)
    (h1 : A *ᵥ (fun _ => (1 : ℝ)) = 0)
    (hpos : ∀ i : Fin (Fintype.card (Fin n)), i.val < k → hA.eigenvalues₀ i ≠ 0) :
    topProj hA k *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  unfold topProj
  rw [projS_mulVec']
  refine sum_eq_zero fun i hi => ?_
  have hi' : i.val < k := by simpa using hi
  have h := bv_dot_mulVec hA i (fun _ => (1 : ℝ))
  rw [h1, dotProduct_zero] at h
  have : bv hA i ⬝ᵥ (fun _ => (1 : ℝ)) = 0 := by
    rcases mul_eq_zero.1 h.symm with h' | h'
    · exact absurd h' (hpos i hi')
    · exact h'
  rw [this, zero_smul]

end BrouwerLaplacian.Dev.GMB.PartA
end

section
namespace BrouwerLaplacian.Dev.GMB
open Finset Matrix BrouwerLaplacian
variable {n : ℕ}
alias topProj_mulVec_one := BrouwerLaplacian.Dev.GMB.PartA.topProj_mulVec_one

end BrouwerLaplacian.Dev.GMB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartA
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB BrouwerLaplacian.Dev.TopK
variable {n : ℕ}
theorem lt_eigenvalue_of_subspace {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (W : Submodule ℝ (Fin n → ℝ)) (i : Fin (Fintype.card (Fin n)))
    (hW : i.val + 1 ≤ Module.finrank ℝ W) (c : ℝ)
    (h : ∀ x ∈ W, x ≠ 0 → c * (x ⬝ᵥ x) < x ⬝ᵥ (A *ᵥ x)) :
    c < hA.eigenvalues₀ i := by
  obtain ⟨x, hxW, hx0, hxT⟩ := exists_inter hA W (Iio i) (by rw [Fin.card_Iio]; omega)
  have h1 := h x hxW hx0
  have h2 := quad_le_of_low hA i x fun j hj => hxT j (mem_Iio.2 hj)
  have h3 := dot_self_pos hx0
  have : c * (x ⬝ᵥ x) < ev hA i * (x ⬝ᵥ x) := lt_of_lt_of_le h1 h2
  exact lt_of_mul_lt_mul_right this h3.le

theorem le_eigenvalue_of_subspace {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (W : Submodule ℝ (Fin n → ℝ)) (i : Fin (Fintype.card (Fin n)))
    (hW : i.val + 1 ≤ Module.finrank ℝ W) (c : ℝ)
    (h : ∀ x ∈ W, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) :
    c ≤ hA.eigenvalues₀ i := by
  obtain ⟨x, hxW, hx0, hxT⟩ := exists_inter hA W (Iio i) (by rw [Fin.card_Iio]; omega)
  have h1 := h x hxW
  have h2 := quad_le_of_low hA i x fun j hj => hxT j (mem_Iio.2 hj)
  have h3 := dot_self_pos hx0
  have : c * (x ⬝ᵥ x) ≤ ev hA i * (x ⬝ᵥ x) := le_trans h1 h2
  exact le_of_mul_le_mul_right this h3

end BrouwerLaplacian.Dev.GMB.PartA
end

section
namespace BrouwerLaplacian.Dev.GMB
open Finset Matrix BrouwerLaplacian
variable {n : ℕ}
alias le_eigenvalue_of_subspace := BrouwerLaplacian.Dev.GMB.PartA.le_eigenvalue_of_subspace

alias lt_eigenvalue_of_subspace := BrouwerLaplacian.Dev.GMB.PartA.lt_eigenvalue_of_subspace

end BrouwerLaplacian.Dev.GMB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartA
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB BrouwerLaplacian.Dev.TopK
variable {n : ℕ}
theorem eigenvalue_le_of_subspace {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (W : Submodule ℝ (Fin n → ℝ)) (i : Fin (Fintype.card (Fin n)))
    (hW : n ≤ i.val + Module.finrank ℝ W) (c : ℝ)
    (h : ∀ x ∈ W, x ⬝ᵥ (A *ᵥ x) ≤ c * (x ⬝ᵥ x)) :
    hA.eigenvalues₀ i ≤ c := by
  have hi := i.2
  have hcard : #(Ioi i) < Module.finrank ℝ W := by
    rw [Fin.card_Ioi]; simp only [Fintype.card_fin] at hi ⊢; omega
  obtain ⟨x, hxW, hx0, hxT⟩ := exists_inter hA W (Ioi i) hcard
  have h1 := h x hxW
  have h2 := quad_ge_of_high hA i x fun j hj => hxT j (mem_Ioi.2 hj)
  have h3 := dot_self_pos hx0
  have : ev hA i * (x ⬝ᵥ x) ≤ c * (x ⬝ᵥ x) := le_trans h2 h1
  exact le_of_mul_le_mul_right this h3

end BrouwerLaplacian.Dev.GMB.PartA
end

section
namespace BrouwerLaplacian.Dev.GMB
open Finset Matrix BrouwerLaplacian
variable {n : ℕ}
alias eigenvalue_le_of_subspace := BrouwerLaplacian.Dev.GMB.PartA.eigenvalue_le_of_subspace

end BrouwerLaplacian.Dev.GMB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartA
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB BrouwerLaplacian.Dev.TopK
variable {n : ℕ}
theorem eigenvalue_mono {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (h : ∀ x, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x))
    (i : Fin (Fintype.card (Fin n))) :
    hA.eigenvalues₀ i ≤ hB.eigenvalues₀ i := by
  have hi := i.2
  refine le_eigenvalue_of_subspace hB (kerT hA (Ioi i)) i ?_ _ fun x hx => ?_
  · have := finrank_kerT hA (Ioi i)
    rw [Fin.card_Ioi] at this; simp only [Fintype.card_fin] at hi this ⊢; omega
  · exact le_trans (quad_ge_of_high hA i x fun j hj => (mem_kerT hA _ x).1 hx j (mem_Ioi.2 hj))
      (h x)

end BrouwerLaplacian.Dev.GMB.PartA
end

section
namespace BrouwerLaplacian.Dev.GMB
open Finset Matrix BrouwerLaplacian
variable {n : ℕ}
alias eigenvalue_mono := BrouwerLaplacian.Dev.GMB.PartA.eigenvalue_mono

end BrouwerLaplacian.Dev.GMB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartB
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB BrouwerLaplacian.Dev.TopK
variable {n : ℕ}
/-! Part B: continuity of the top projection under a spectral gap (a Davis–Kahan type bound
with the entrywise `ℓ¹` norm). -/
/-- entrywise `ℓ¹` size of a matrix -/
noncomputable def l1 (E : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ a, ∑ b, |E a b|

theorem l1_nonneg (E : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ l1 E := by
  unfold l1; positivity

theorem bilin_bound (E : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) (hx : ∀ a, |x a| ≤ 1)
    (hy : ∀ b, |y b| ≤ 1) : |x ⬝ᵥ (E *ᵥ y)| ≤ l1 E := by
  unfold l1
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ =>
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b _ => ?_))
  rw [abs_mul, abs_mul]
  have h1 := hx a
  have h2 := hy b
  have h3 := abs_nonneg (E a b)
  have h4 := abs_nonneg (y b)
  calc |x a| * (|E a b| * |y b|) ≤ 1 * (|E a b| * 1) := by gcongr
    _ = |E a b| := by ring

theorem sq_le_dot (x : Fin n → ℝ) (a : Fin n) : x a ^ 2 ≤ x ⬝ᵥ x := by
  simp only [dotProduct, sq]
  exact Finset.single_le_sum (f := fun i => x i * x i) (fun i _ => mul_self_nonneg _) (mem_univ a)

theorem quad_bound (E : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    |x ⬝ᵥ (E *ᵥ x)| ≤ l1 E * (x ⬝ᵥ x) := by
  have key : ∀ a b, |x a * (E a b * x b)| ≤ |E a b| * (x ⬝ᵥ x) := by
    intro a b
    have ha := sq_le_dot x a
    have hb := sq_le_dot x b
    have hab : |x a| * |x b| ≤ x ⬝ᵥ x := by
      have := two_mul_le_add_sq |x a| |x b|
      rw [sq_abs, sq_abs] at this
      nlinarith
    rw [abs_mul, abs_mul]
    calc |x a| * (|E a b| * |x b|) = |E a b| * (|x a| * |x b|) := by ring
      _ ≤ |E a b| * (x ⬝ᵥ x) := by gcongr
  calc |x ⬝ᵥ (E *ᵥ x)| = |∑ a, ∑ b, x a * (E a b * x b)| := by
        simp only [dotProduct, mulVec, Finset.mul_sum]
    _ ≤ ∑ a, ∑ b, |x a * (E a b * x b)| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a, ∑ b, |E a b| * (x ⬝ᵥ x) := sum_le_sum fun a _ => sum_le_sum fun b _ => key a b
    _ = l1 E * (x ⬝ᵥ x) := by unfold l1; simp_rw [Finset.sum_mul]

theorem bv_entry_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (i : Fin (Fintype.card (Fin n))) (a : Fin n) : |bv hA i a| ≤ 1 := by
  have h := sq_le_dot (bv hA i) a
  rw [bv_dot, if_pos rfl] at h
  exact (sq_le_one_iff_abs_le_one _).1 h

end BrouwerLaplacian.Dev.GMB.PartB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartB
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB BrouwerLaplacian.Dev.TopK
variable {n : ℕ}
variable {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
theorem quad_sub (x : Fin n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (B *ᵥ x) + x ⬝ᵥ ((A - B) *ᵥ x) := by
  rw [sub_mulVec, dotProduct_sub]; ring

include hA hB in
/-- Weyl's perturbation bound, lower side. -/
theorem weyl_lower (i : Fin (Fintype.card (Fin n))) :
    ev hB i - l1 (A - B) ≤ ev hA i := by
  have hi := i.2
  refine PartA.le_eigenvalue_of_subspace hA (PartA.kerT hB (Ioi i)) i ?_ _ fun x hx => ?_
  · have := PartA.finrank_kerT hB (Ioi i)
    rw [Fin.card_Ioi] at this; simp only [Fintype.card_fin] at hi this ⊢; omega
  · have h1 := PartA.quad_ge_of_high hB i x fun j hj => (PartA.mem_kerT hB _ x).1 hx j (mem_Ioi.2 hj)
    have h2 := quad_bound (A - B) x
    rw [quad_sub (B := B)]
    have h3 := neg_abs_le (x ⬝ᵥ ((A - B) *ᵥ x))
    unfold ev at h1 ⊢
    nlinarith

include hA hB in
/-- Weyl's perturbation bound, upper side. -/
theorem weyl_upper (i : Fin (Fintype.card (Fin n))) :
    ev hA i ≤ ev hB i + l1 (A - B) := by
  have hi := i.2
  refine PartA.eigenvalue_le_of_subspace hA (PartA.kerT hB (Iio i)) i ?_ _ fun x hx => ?_
  · have := PartA.finrank_kerT hB (Iio i)
    rw [Fin.card_Iio] at this; omega
  · have h1 := PartA.quad_le_of_low hB i x fun j hj => (PartA.mem_kerT hB _ x).1 hx j (mem_Iio.2 hj)
    have h2 := quad_bound (A - B) x
    rw [quad_sub (B := B)]
    have h3 := le_abs_self (x ⬝ᵥ ((A - B) *ᵥ x))
    unfold ev at h1 ⊢
    nlinarith

include hA hB in
theorem cross_identity (i j : Fin (Fintype.card (Fin n))) :
    bv hA i ⬝ᵥ ((A - B) *ᵥ bv hB j) = (ev hA i - ev hB j) * (bv hA i ⬝ᵥ bv hB j) := by
  rw [sub_mulVec, dotProduct_sub, PartA.dot_mulVec_symm hA, mulVec_bv, mulVec_bv,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

include hA hB in
theorem cross_bound (i j : Fin (Fintype.card (Fin n))) :
    |ev hA i - ev hB j| * |bv hA i ⬝ᵥ bv hB j| ≤ l1 (A - B) := by
  rw [← abs_mul, ← cross_identity hA hB]
  exact bilin_bound _ _ _ (bv_entry_le hA i) (bv_entry_le hB j)

/-- indicator of the top block -/
noncomputable def ind (k : ℕ) (i : Fin (Fintype.card (Fin n))) : ℝ := if i.val < k then 1 else 0

theorem diff_mulVec (k : ℕ) (j : Fin (Fintype.card (Fin n))) :
    (topProj hA k - topProj hB k) *ᵥ bv hB j
      = ∑ i, ((ind k i - ind k j) * (bv hA i ⬝ᵥ bv hB j)) • bv hA i := by
  rw [sub_mulVec]
  unfold topProj
  rw [PartA.projS_mulVec' hA, projS_mulVec, sum_filter]
  have : (if j ∈ univ.filter (fun i : Fin (Fintype.card (Fin n)) => i.val < k) then bv hB j else 0)
      = ind k j • ∑ i, (bv hA i ⬝ᵥ bv hB j) • bv hA i := by
    rw [PartA.expand hA]
    unfold ind
    by_cases h : j.val < k <;> simp [h]
  rw [this, smul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  unfold ind
  by_cases h : i.val < k <;> by_cases h' : j.val < k <;> simp [h, h', sub_smul]

theorem entry_formula (M : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    M a b = ∑ j, bv hB j b * (M *ᵥ bv hB j) a := by
  have h := congrArg (fun v => (M *ᵥ v) a) (PartA.expand hB (Pi.single b 1))
  simp only [mulVec_single_one, Matrix.col_apply, Matrix.mulVec_sum, Matrix.mulVec_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct_single, mul_one] at h
  rw [← h]

include hA hB in
/-- The static estimate. -/
theorem static_bound (k : ℕ) (c g : ℝ) (hg : 0 < g)
    (h1 : ∀ i : Fin (Fintype.card (Fin n)), i.val < k → c + g ≤ ev hB i)
    (h2 : ∀ i : Fin (Fintype.card (Fin n)), k ≤ i.val → ev hB i ≤ c - g)
    (hη : l1 (A - B) ≤ g) (a b : Fin n) :
    |topProj hA k a b - topProj hB k a b|
      ≤ (Fintype.card (Fin n) : ℝ) ^ 2 * (l1 (A - B) / g) := by
  set η := l1 (A - B)
  have hηg : 0 ≤ η / g := div_nonneg (l1_nonneg _) hg.le
  -- coefficient bound
  have hcoef : ∀ i j : Fin (Fintype.card (Fin n)),
      |(ind k i - ind k j) * (bv hA i ⬝ᵥ bv hB j)| ≤ η / g := by
    intro i j
    rw [le_div_iff₀ hg]
    have hcb := cross_bound hA hB i j
    have hl := weyl_lower hA hB i
    have hu := weyl_upper hA hB i
    unfold ind
    by_cases hi : i.val < k <;> by_cases hj : j.val < k <;> simp only [hi, hj, if_true, if_false]
    · simpa using l1_nonneg (A - B)
    · have e1 := h1 i hi
      have e2 := h2 j (by omega)
      have hgap : g ≤ |ev hA i - ev hB j| := by
        rw [abs_of_nonneg (by linarith)]; linarith
      rw [sub_zero, one_mul]
      nlinarith [abs_nonneg (bv hA i ⬝ᵥ bv hB j)]
    · have e1 := h2 i (by omega)
      have e2 := h1 j hj
      have hgap : g ≤ |ev hA i - ev hB j| := by
        rw [abs_of_nonpos (by linarith)]; linarith
      rw [zero_sub, neg_one_mul, abs_neg]
      nlinarith [abs_nonneg (bv hA i ⬝ᵥ bv hB j)]
    · simpa using l1_nonneg (A - B)
  have hef := entry_formula hB (topProj hA k - topProj hB k) a b
  rw [Matrix.sub_apply] at hef
  rw [hef]
  have hterm : ∀ j : Fin (Fintype.card (Fin n)),
      |bv hB j b * ((topProj hA k - topProj hB k) *ᵥ bv hB j) a|
        ≤ (Fintype.card (Fin n) : ℝ) * (η / g) := by
    intro j
    rw [diff_mulVec hA hB k j, abs_mul]
    have hb := bv_entry_le hB j b
    have hs : |(∑ i, ((ind k i - ind k j) * (bv hA i ⬝ᵥ bv hB j)) • bv hA i) a|
        ≤ (Fintype.card (Fin n) : ℝ) * (η / g) := by
      rw [Finset.sum_apply]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ i ∈ (univ : Finset (Fin (Fintype.card (Fin n)))),
          |(((ind k i - ind k j) * (bv hA i ⬝ᵥ bv hB j)) • bv hA i) a| ≤ η / g := by
        intro i _
        rw [Pi.smul_apply, smul_eq_mul, abs_mul]
        have := hcoef i j
        have := bv_entry_le hA i a
        calc _ ≤ η / g * 1 := by gcongr
          _ = η / g := mul_one _
      refine (sum_le_sum this).trans ?_
      simp
    calc _ ≤ 1 * ((Fintype.card (Fin n) : ℝ) * (η / g)) := by gcongr
      _ = _ := one_mul _
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun j _ => hterm j).trans ?_)
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_of_eq (by ring)

end BrouwerLaplacian.Dev.GMB.PartB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartB
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB BrouwerLaplacian.Dev.TopK
variable {n : ℕ}
theorem exists_pos_le {m : ℕ} (f : Fin m → ℝ) (hf : ∀ i, 0 < f i) : ∃ g > 0, ∀ i, g ≤ f i := by
  by_cases h : (univ : Finset (Fin m)).Nonempty
  · exact ⟨univ.inf' h f, (Finset.lt_inf'_iff h).2 fun i _ => hf i,
      fun i => Finset.inf'_le f (mem_univ i)⟩
  · exact ⟨1, one_pos, fun i => absurd ⟨i, mem_univ i⟩ h⟩

theorem l1_zero : l1 (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  unfold l1; simp

theorem topProj_continuousOn (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ t, (A t).IsHermitian) (hcont : Continuous A) (s : Set ℝ) (k : ℕ)
    (hgap : ∀ t ∈ s, ∃ c : ℝ,
      (∀ i : Fin (Fintype.card (Fin n)), i.val < k → c < (hA t).eigenvalues₀ i) ∧
      (∀ i : Fin (Fintype.card (Fin n)), k ≤ i.val → (hA t).eigenvalues₀ i < c)) :
    ContinuousOn (fun t => topProj (hA t) k) s := by
  intro t₀ ht₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨c, hc1, hc2⟩ := hgap t₀ ht₀
  obtain ⟨g, hg, hgi⟩ := exists_pos_le (fun i => |ev (hA t₀) i - c|) fun i => by
    rcases lt_or_ge i.val k with h | h
    · have := hc1 i h; unfold ev; exact abs_pos.2 (by linarith)
    · have := hc2 i h; unfold ev; exact abs_pos.2 (by linarith)
  have h1 : ∀ i : Fin (Fintype.card (Fin n)), i.val < k → c + g ≤ ev (hA t₀) i := by
    intro i hi
    have := hgi i
    have h' := hc1 i hi
    unfold ev at this ⊢
    rw [abs_of_pos (by linarith)] at this; linarith
  have h2 : ∀ i : Fin (Fintype.card (Fin n)), k ≤ i.val → ev (hA t₀) i ≤ c - g := by
    intro i hi
    have := hgi i
    have h' := hc2 i hi
    unfold ev at this ⊢
    rw [abs_of_neg (by linarith)] at this; linarith
  have hηc : Continuous (fun t => l1 (A t - A t₀)) := by
    unfold l1
    refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
    exact ((hcont.matrix_elem a b).sub continuous_const).abs
  refine continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set M : ℝ := (Fintype.card (Fin n) : ℝ) ^ 2
  have hM : 0 ≤ M := by positivity
  have hδ : 0 < min g (ε * g / (M + 1)) := lt_min hg (by positivity)
  have hev : ∀ᶠ t in nhds t₀, l1 (A t - A t₀) < min g (ε * g / (M + 1)) := by
    have h0 : l1 (A t₀ - A t₀) < min g (ε * g / (M + 1)) := by rw [sub_self, l1_zero]; exact hδ
    exact (hηc.tendsto t₀).eventually (eventually_lt_nhds h0)
  filter_upwards [hev] with t ht
  rw [Real.dist_eq]
  have hη1 : l1 (A t - A t₀) ≤ g := le_of_lt (lt_of_lt_of_le ht (min_le_left _ _))
  have hη2 : l1 (A t - A t₀) < ε * g / (M + 1) := lt_of_lt_of_le ht (min_le_right _ _)
  have hsb := static_bound (hA t) (hA t₀) k c g hg h1 h2 hη1 a b
  have hq : l1 (A t - A t₀) / g < ε / (M + 1) := by
    rw [div_lt_div_iff₀ hg (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at hη2
    linarith
  calc |topProj (hA t) k a b - topProj (hA t₀) k a b|
      ≤ M * (l1 (A t - A t₀) / g) := hsb
    _ ≤ M * (ε / (M + 1)) := by gcongr
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

end BrouwerLaplacian.Dev.GMB.PartB
end

section
namespace BrouwerLaplacian.Dev.GMB
open Finset Matrix BrouwerLaplacian
variable {n : ℕ}
/-! ### Part B: continuity of the top projection under a spectral gap -/
alias topProj_continuousOn := BrouwerLaplacian.Dev.GMB.PartB.topProj_continuousOn

end BrouwerLaplacian.Dev.GMB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartD
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
/-! Part D: the minimal counterexample argument (Bai §4) and `gm_fin`. -/
/-- `G` plus all edges inside `C`. -/
def addClique (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj a b := G.Adj a b ∨ (a ≠ b ∧ a ∈ C ∧ b ∈ C)
  symm := ⟨fun a b h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.1.symm, h.2.2, h.2.1⟩)⟩
  loopless := ⟨fun a h => h.elim (fun h => G.irrefl h) (fun h => h.1 rfl)⟩

instance addClique_dec (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) :
    DecidableRel (addClique G C).Adj := fun a b =>
  inferInstanceAs (Decidable (G.Adj a b ∨ (a ≠ b ∧ a ∈ C ∧ b ∈ C)))

theorem addClique_adj (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) (a b : Fin n) :
    (addClique G C).Adj a b ↔ G.Adj a b ∨ (a ≠ b ∧ a ∈ C ∧ b ∈ C) := Iff.rfl

end BrouwerLaplacian.Dev.GMB.PartD
end

section
namespace BrouwerLaplacian.Dev.GMB.PartD
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
/-- the set of vertices of degree at least `k` -/
def bigC : Finset (Fin n) := univ.filter (fun v => k ≤ G.degree v)

theorem mem_bigC (v : Fin n) : v ∈ bigC G k ↔ k ≤ G.degree v := by simp [bigC]

end BrouwerLaplacian.Dev.GMB.PartD
end

section
namespace BrouwerLaplacian.Dev.GMB.PartD
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
variable (hstar : ∀ u v, G.Adj u v → G.degree u < k → k ≤ G.degree v)
include hstar
theorem addClique_split : IsSplitWith (addClique G (bigC G k)) (bigC G k) := by
  constructor
  · intro a ha b hb hab
    exact Or.inr ⟨hab, ha, hb⟩
  · intro a ha b hb hab h
    simp only [coe_compl, Set.mem_compl_iff, mem_coe] at ha hb
    rcases h with h | h
    · rw [mem_bigC] at ha hb
      exact hb (hstar a b h (by omega))
    · exact ha h.2.1

end BrouwerLaplacian.Dev.GMB.PartD
end

section
namespace BrouwerLaplacian.Dev.GMB.PartC
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
/-! Part C, file 1: quadratic forms of Laplacians, coordinate subspaces, Bai's Proposition 5. -/
theorem quad_lap (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℝ) :
    x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) =
      (∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 := by
  rw [← SimpleGraph.lapMatrix_toLinearMap₂', Matrix.toLinearMap₂'_apply']

theorem sum_sq_diff (T : Finset (Fin n)) (x : Fin n → ℝ) :
    ∑ i ∈ T, ∑ j ∈ T, (x i - x j) ^ 2 = 2 * (#T * ∑ i ∈ T, x i ^ 2 - (∑ i ∈ T, x i) ^ 2) := by
  have : ∀ i ∈ T, ∑ j ∈ T, (x i - x j) ^ 2
      = #T * x i ^ 2 - 2 * x i * ∑ j ∈ T, x j + ∑ j ∈ T, x j ^ 2 := by
    intro i _
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_sum]
  rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum,
    ← sum_mul, ← mul_sum]
  ring

theorem nbr_mem {G : SimpleGraph (Fin n)} {C : Finset (Fin n)} (hs : IsSplitWith G C)
    {s u : Fin n} (hsC : s ∉ C) (h : G.Adj s u) : u ∈ C := by
  by_contra hu
  exact hs.2 (by simpa using hsC) (by simpa using hu) (G.ne_of_adj h) h

theorem adj_of_mem {G : SimpleGraph (Fin n)} {C : Finset (Fin n)} (hs : IsSplitWith G C)
    {a b : Fin n} (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) : G.Adj a b :=
  hs.1 (by simpa using ha) (by simpa using hb) hab

theorem degree_le (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (hs : IsSplitWith G C) (s : Fin n) (hsC : s ∉ C) : G.degree s ≤ #C := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact card_le_card fun v hv => nbr_mem hs hsC ((G.mem_neighborFinset s v).1 hv)

/-- The Laplacian quadratic form on vectors vanishing on the clique. -/
theorem quad_lap_Q (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (hs : IsSplitWith G C) (x : Fin n → ℝ) (hx : ∀ c ∈ C, x c = 0) :
    x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) = ∑ s ∈ Cᶜ, (G.degree s : ℝ) * x s ^ 2 := by
  rw [dotProduct]
  have : ∀ v, x v * (G.lapMatrix ℝ *ᵥ x) v
      = if v ∈ Cᶜ then (G.degree v : ℝ) * x v ^ 2 else 0 := by
    intro v
    rw [SimpleGraph.lapMatrix_mulVec_apply]
    by_cases hv : v ∈ C
    · simp [hv, hx v hv]
    · have h0 : ∑ u ∈ G.neighborFinset v, x u = 0 :=
        sum_eq_zero fun u hu => hx u (nbr_mem hs hv ((G.mem_neighborFinset v u).1 hu))
      simp [hv, h0]; ring
  rw [sum_congr rfl fun v _ => this v, sum_ite_mem, univ_inter]

/-- vectors vanishing on `C` -/
def Qsub (C : Finset (Fin n)) : Submodule ℝ (Fin n → ℝ) where
  carrier := {x | ∀ c ∈ C, x c = 0}
  add_mem' := by
    intro a b ha hb c hc
    simp [ha c hc, hb c hc]
  zero_mem' := by intro c _; rfl
  smul_mem' := by
    intro r a ha c hc
    simp [ha c hc]

theorem mem_Qsub {C : Finset (Fin n)} {x : Fin n → ℝ} : x ∈ Qsub C ↔ ∀ c ∈ C, x c = 0 :=
  Iff.rfl

theorem finrank_Qsub (C : Finset (Fin n)) : n - #C ≤ Module.finrank ℝ (Qsub C) := by
  let f : (↥(Cᶜ) : Type) → (Fin n → ℝ) := fun s => Pi.single s.1 1
  have hli : LinearIndependent ℝ f := by
    have := (Pi.basisFun ℝ (Fin n)).linearIndependent.comp (fun s : (↥(Cᶜ) : Type) => s.1)
      Subtype.val_injective
    convert this using 1
    ext s
    simp [f, Pi.basisFun_apply]
  have hle : Submodule.span ℝ (Set.range f) ≤ Qsub C := by
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩ c hc
    have : (s : Fin n) ≠ c := by
      intro h; have := s.2; rw [h] at this; simp [hc] at this
    simp [f, this.symm]
  have h1 := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli, Fintype.card_coe, card_compl, Fintype.card_fin] at h1
  exact h1

theorem dot_self_Q {C : Finset (Fin n)} {x : Fin n → ℝ} (hx : ∀ c ∈ C, x c = 0) :
    x ⬝ᵥ x = ∑ s ∈ Cᶜ, x s ^ 2 := by
  rw [dotProduct, ← sum_add_sum_compl C]
  rw [sum_eq_zero fun c hc => by simp [hx c hc], zero_add]
  exact sum_congr rfl fun s _ => by ring

/-- the sum functional -/
def sumL : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [sum_add_distrib]
  map_smul' r x := by simp [mul_sum]

theorem finrank_ker_sumL : n ≤ Module.finrank ℝ (LinearMap.ker (sumL (n := n))) + 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (sumL (n := n))
  have h2 : Module.finrank ℝ (LinearMap.range (sumL (n := n))) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (sumL (n := n)))
    simpa using this
  rw [Module.finrank_fin_fun] at h
  omega

/-! ### Proposition 5 -/
theorem prop5_upper_aux (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (hsplit : IsSplitWith G C) (δ : ℝ) (hδ : ∀ s ∉ C, (G.degree s : ℝ) ≤ δ)
    (i : Fin (Fintype.card (Fin n))) (hi : #C ≤ i.val) :
    (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i ≤ δ := by
  refine eigenvalue_le_of_subspace _ (Qsub C) i ?_ δ ?_
  · have := finrank_Qsub C
    omega
  · intro x hx
    rw [quad_lap_Q G C hsplit x hx, dot_self_Q hx, mul_sum]
    refine sum_le_sum fun s hs => ?_
    have := hδ s (by simpa using hs)
    have : 0 ≤ x s ^ 2 := sq_nonneg _
    nlinarith

/-! Part C: Bai's Proposition 5 and Lemma 6 (targets restated from the Blueprint). -/
/-- Bai, Proposition 5, upper half: `λ_{N+1} ≤ δ`. -/
theorem prop5_upper (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (hsplit : IsSplitWith G C) (δ : ℝ) (hδ : ∀ s ∉ C, (G.degree s : ℝ) ≤ δ)
    (i : Fin (Fintype.card (Fin n))) (hi : #C ≤ i.val) :
    (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i ≤ δ :=
  prop5_upper_aux G C hsplit δ hδ i hi

end BrouwerLaplacian.Dev.GMB.PartC
end

section
namespace BrouwerLaplacian.Dev.GMB
open Finset Matrix BrouwerLaplacian
variable {n : ℕ}
/-! ### Part C: split graphs (Bai, Proposition 5 and Lemma 6) -/
alias prop5_upper := BrouwerLaplacian.Dev.GMB.PartC.prop5_upper

end BrouwerLaplacian.Dev.GMB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartC
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
theorem prop5_lower_aux (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (hsplit : IsSplitWith G C)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val + 2 ≤ #C) :
    (#C : ℝ) ≤ (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i := by
  refine le_eigenvalue_of_subspace _ (Qsub Cᶜ ⊓ LinearMap.ker (sumL (n := n))) i ?_ _ ?_
  · have h1 := finrank_Qsub (n := n) Cᶜ
    have h2 := finrank_ker_sumL (n := n)
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq (Qsub Cᶜ) (LinearMap.ker (sumL (n := n)))
    have h4 := Submodule.finrank_le (Qsub Cᶜ ⊔ LinearMap.ker (sumL (n := n)))
    rw [Module.finrank_fin_fun] at h4
    rw [card_compl, Fintype.card_fin] at h1
    have h5 := card_le_univ C
    rw [Fintype.card_fin] at h5
    omega
  · intro x hx
    rw [Submodule.mem_inf, mem_Qsub, LinearMap.mem_ker] at hx
    obtain ⟨hxS, hsum⟩ := hx
    have hxS' : ∀ s ∉ C, x s = 0 := fun s hs => hxS s (by simpa using hs)
    have hsumC : ∑ c ∈ C, x c = 0 := by
      rw [← hsum]
      change _ = ∑ i, x i
      rw [← sum_add_sum_compl C, sum_eq_zero (s := Cᶜ) fun s hs => hxS' s (by simpa using hs),
        add_zero]
    have hxx : x ⬝ᵥ x = ∑ c ∈ C, x c ^ 2 := by
      have := dot_self_Q (C := Cᶜ) hxS
      rwa [compl_compl] at this
    rw [quad_lap, hxx]
    have hkey : ∑ i ∈ C, ∑ j ∈ C, (x i - x j) ^ 2 ≤
        ∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0 := by
      calc ∑ i ∈ C, ∑ j ∈ C, (x i - x j) ^ 2
          = ∑ i ∈ C, ∑ j ∈ C, if G.Adj i j then (x i - x j) ^ 2 else 0 := by
            refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => ?_
            by_cases hab : a = b
            · subst hab; simp
            · simp [adj_of_mem hsplit ha hb hab]
        _ ≤ ∑ i ∈ C, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0 :=
            sum_le_sum fun a _ => sum_le_sum_of_subset_of_nonneg (subset_univ _)
              fun b _ _ => by split_ifs <;> positivity
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _)
              fun a _ _ => sum_nonneg fun b _ => by split_ifs <;> positivity
    rw [sum_sq_diff, hsumC] at hkey
    linarith

/-- Bai, Proposition 5, lower half: `λ_{N-1} ≥ N`. -/
theorem prop5_lower (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (hsplit : IsSplitWith G C)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val + 2 ≤ #C) :
    (#C : ℝ) ≤ (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i :=
  prop5_lower_aux G C hsplit i hi

end BrouwerLaplacian.Dev.GMB.PartC
end

section
namespace BrouwerLaplacian.Dev.GMB
open Finset Matrix BrouwerLaplacian
variable {n : ℕ}
alias prop5_lower := BrouwerLaplacian.Dev.GMB.PartC.prop5_lower

end BrouwerLaplacian.Dev.GMB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartC
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
/-! Part C, file 2: the graph-of-a-map description of an `N`-dimensional invariant subspace
transversal to `{x_C = 0}` (abstract matrix algebra). -/
/-- the coordinate projection onto `C` -/
def Emat (C : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun i => if i ∈ C then 1 else 0

theorem Emat_mul_self (C : Finset (Fin n)) : Emat C * Emat C = Emat C := by
  simp only [Emat, diagonal_mul_diagonal]
  congr 1; funext i; split_ifs <;> simp

theorem Emat_mulVec (C : Finset (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    (Emat C *ᵥ x) i = if i ∈ C then x i else 0 := by
  simp [Emat, mulVec_diagonal]

theorem Emat_mul_apply (C : Finset (Fin n)) (Y : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (Emat C * Y) i j = if i ∈ C then Y i j else 0 := by
  simp [Emat, diagonal_mul]

theorem mul_Emat_apply (C : Finset (Fin n)) (Y : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (Y * Emat C) i j = if j ∈ C then Y i j else 0 := by
  simp [Emat, mul_diagonal]

/-- the `C × C` block of `P`, completed by the identity on `S` -/
def Kmat (C : Finset (Fin n)) (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Emat C * P * Emat C + (1 - Emat C)

/-- `W = P K⁻¹`; its `S × C` block is Bai's `V`, its `C × C` block the identity. -/
noncomputable def Wmat (C : Finset (Fin n)) (P : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  P * (Kmat C P)⁻¹

theorem mulVec_col (P Y : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    P *ᵥ (fun k => Y k j) = fun i => (P * Y) i j := by
  funext i; simp [mulVec, dotProduct, mul_apply]

end BrouwerLaplacian.Dev.GMB.PartC
end

section
namespace BrouwerLaplacian.Dev.GMB.PartC
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
variable (C : Finset (Fin n)) (P : Matrix (Fin n) (Fin n) ℝ)
/-- transversality, matrix form -/
theorem UQ_mat (hUQ : ∀ y : Fin n → ℝ, P *ᵥ y = y → (∀ c ∈ C, y c = 0) → y = 0)
    (Y : Matrix (Fin n) (Fin n) ℝ) (h1 : P * Y = Y) (h2 : Emat C * Y = 0) : Y = 0 := by
  ext i j
  have := hUQ (fun k => Y k j) (by rw [mulVec_col, h1]) (by
    intro c hc
    have := congrFun (congrFun h2 c) j
    rwa [Emat_mul_apply, if_pos hc] at this)
  exact congrFun this i

/-- From transversality and the dimension count: `U + Q = ℝⁿ`, so a vector supported on `C`
orthogonal to `U` vanishes. -/
theorem span_aux (hPT : Pᵀ = P) (hPP : P * P = P)
    (hUQ : ∀ y : Fin n → ℝ, P *ᵥ y = y → (∀ c ∈ C, y c = 0) → y = 0)
    (hrank : #C ≤ Module.finrank ℝ (LinearMap.range (Matrix.toLin' P)))
    (x : Fin n → ℝ) (hx : ∀ s ∉ C, x s = 0) (hPx : P *ᵥ x = 0) : x = 0 := by
  set U := LinearMap.range (Matrix.toLin' P)
  have hinf : U ⊓ Qsub C = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_inf] at hy
    obtain ⟨⟨z, rfl⟩, hq⟩ := hy
    rw [Submodule.mem_bot]
    apply hUQ _ _ hq
    rw [Matrix.toLin'_apply, mulVec_mulVec, hPP]
  have hsup : U ⊔ Qsub C = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (Qsub C)
    rw [hinf, finrank_bot] at h1
    have h2 := finrank_Qsub (n := n) C
    have h3 := Submodule.finrank_le (U ⊔ Qsub C)
    have h5 := card_le_univ C
    rw [Fintype.card_fin] at h5
    rw [Module.finrank_fin_fun] at h3 ⊢
    omega
  have hmem : x ∈ U ⊔ Qsub C := by rw [hsup]; trivial
  obtain ⟨u, hu, q, hq, hxuq⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨z, rfl⟩ := hu
  have h1 : x ⬝ᵥ (Matrix.toLin' P z) = 0 := by
    rw [Matrix.toLin'_apply, dotProduct_mulVec, ← mulVec_transpose, hPT, hPx, zero_dotProduct]
  have h2 : x ⬝ᵥ q = 0 := by
    refine sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ C
    · rw [(mem_Qsub.1 hq) i hi, mul_zero]
    · rw [hx i hi, zero_mul]
  have : x ⬝ᵥ x = 0 := by
    conv_lhs => arg 2; rw [← hxuq]
    rw [dotProduct_add, h1, h2, add_zero]
  exact dotProduct_self_eq_zero.1 this

theorem Kmat_mulVec (x : Fin n → ℝ) (i : Fin n) :
    (Kmat C P *ᵥ x) i = if i ∈ C then (P *ᵥ (Emat C *ᵥ x)) i else x i := by
  simp only [Kmat, add_mulVec, sub_mulVec, one_mulVec, ← mulVec_mulVec, Pi.add_apply,
    Pi.sub_apply, Emat_mulVec]
  split_ifs <;> ring

theorem Kmat_isUnit (hPT : Pᵀ = P) (hPP : P * P = P)
    (hUQ : ∀ y : Fin n → ℝ, P *ᵥ y = y → (∀ c ∈ C, y c = 0) → y = 0)
    (hrank : #C ≤ Module.finrank ℝ (LinearMap.range (Matrix.toLin' P))) :
    IsUnit (Kmat C P).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  suffices key : ∀ x, Kmat C P *ᵥ x = 0 → x = 0 by
    intro x y hxy
    exact sub_eq_zero.1 (key _ (by rw [mulVec_sub, hxy, sub_self]))
  intro x hx
  have hxS : ∀ s ∉ C, x s = 0 := by
    intro s hs
    have := congrFun hx s
    rwa [Kmat_mulVec, if_neg hs] at this
  have hEx : Emat C *ᵥ x = x := by
    funext i; rw [Emat_mulVec]; split_ifs with h
    · rfl
    · exact (hxS i h).symm
  have hPx : P *ᵥ x = 0 := by
    apply hUQ
    · rw [mulVec_mulVec, hPP]
    · intro c hc
      have := congrFun hx c
      rwa [Kmat_mulVec, if_pos hc, hEx] at this
  exact span_aux C P hPT hPP hUQ hrank x hxS hPx

end BrouwerLaplacian.Dev.GMB.PartC
end

section
namespace BrouwerLaplacian.Dev.GMB.PartC
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
variable (C : Finset (Fin n)) (P : Matrix (Fin n) (Fin n) ℝ)
variable (hPT : Pᵀ = P) (hPP : P * P = P)
  (hUQ : ∀ y : Fin n → ℝ, P *ᵥ y = y → (∀ c ∈ C, y c = 0) → y = 0)
  (hrank : #C ≤ Module.finrank ℝ (LinearMap.range (Matrix.toLin' P)))
include hPT hPP hUQ hrank
theorem Kinv_comm : (Kmat C P)⁻¹ * Emat C = Emat C * (Kmat C P)⁻¹ := by
  have hu := Kmat_isUnit C P hPT hPP hUQ hrank
  set K := Kmat C P
  set E := Emat C
  have hEE := Emat_mul_self C
  have hKE : K * E = E * K := by
    simp only [K, Kmat, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc E E, hEE]
  calc K⁻¹ * E = K⁻¹ * (E * K) * K⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = K⁻¹ * (K * E) * K⁻¹ := by rw [hKE]
    _ = E * K⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]

theorem EWE : Emat C * Wmat C P * Emat C = Emat C := by
  have hu := Kmat_isUnit C P hPT hPP hUQ hrank
  have hc := Kinv_comm C P hPT hPP hUQ hrank
  have hEE := Emat_mul_self C
  set K := Kmat C P with hKdef
  set E := Emat C
  have h1 : E * P * E * K⁻¹ = 1 - K⁻¹ + E * K⁻¹ := by
    have : E * P * E = K - (1 - E) := by rw [hKdef, Kmat]; abel
    rw [this, sub_mul, mul_nonsing_inv _ hu, sub_mul, Matrix.one_mul]; abel
  calc E * Wmat C P * E = E * (E * P * E * K⁻¹) := by
        simp only [Wmat, Matrix.mul_assoc]
        rw [hc, ← Matrix.mul_assoc E E, hEE]
    _ = E := by
        rw [h1, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hEE]; abel

theorem PW : P * Wmat C P = Wmat C P := by
  rw [Wmat, ← Matrix.mul_assoc, hPP]

theorem P_eq_WEP : P = Wmat C P * Emat C * P := by
  have h := EWE C P hPT hPP hUQ hrank
  have hPW := PW C P hPT hPP hUQ hrank
  have := UQ_mat C P hUQ (P - Wmat C P * Emat C * P) (by
      rw [Matrix.mul_sub, hPP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPW])
    (by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, sub_self])
  exact (sub_eq_zero.1 this)

theorem AW_eq (A : Matrix (Fin n) (Fin n) ℝ) (hAP : A * P = P * A) :
    A * Wmat C P = Wmat C P * Emat C * (A * Wmat C P) := by
  have hPW := PW C P hPT hPP hUQ hrank
  have hY : P * (A * Wmat C P) = A * Wmat C P := by
    rw [← Matrix.mul_assoc, ← hAP, Matrix.mul_assoc, hPW]
  calc A * Wmat C P = P * (A * Wmat C P) := hY.symm
    _ = Wmat C P * Emat C * P * (A * Wmat C P) := by
        rw [← P_eq_WEP C P hPT hPP hUQ hrank]
    _ = _ := by rw [Matrix.mul_assoc _ P, hY]

theorem trace_eq (A : Matrix (Fin n) (Fin n) ℝ) (hAP : A * P = P * A) :
    (P * A).trace = (Emat C * (A * Wmat C P)).trace := by
  have hPW := PW C P hPT hPP hUQ hrank
  conv_lhs => rw [P_eq_WEP C P hPT hPP hUQ hrank]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, ← Matrix.mul_assoc P, ← hAP, Matrix.mul_assoc, hPW]

theorem colsum_W (h1 : P *ᵥ (fun _ => (1 : ℝ)) = 0) (c : Fin n) :
    ∑ k, Wmat C P k c = 0 := by
  have : (fun _ => (1 : ℝ)) ᵥ* Wmat C P = 0 := by
    have h2 : (fun _ => (1 : ℝ)) ᵥ* P = 0 := by rw [← mulVec_transpose, hPT, h1]
    rw [Wmat, ← vecMul_vecMul, h2, zero_vecMul]
  have := congrFun this c
  simpa [vecMul, dotProduct] using this

theorem W_CC (c' c : Fin n) (hc' : c' ∈ C) (hc : c ∈ C) :
    Wmat C P c' c = if c' = c then 1 else 0 := by
  have := congrFun (congrFun (EWE C P hPT hPP hUQ hrank) c') c
  rw [mul_Emat_apply, Emat_mul_apply, if_pos hc, if_pos hc'] at this
  rw [this]
  simp [Emat, diagonal_apply, hc']

end BrouwerLaplacian.Dev.GMB.PartC
end

section
namespace BrouwerLaplacian.Dev.GMB.PartC
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
/-- the top-`k` eigenvectors lie in the range of `topProj`, so its rank is at least `k`. -/
theorem finrank_range_topProj {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : ℕ)
    (hk : k ≤ n) : k ≤ Module.finrank ℝ (LinearMap.range (Matrix.toLin' (topProj hA k))) := by
  have hkn : ∀ j : Fin k, (j : ℕ) < Fintype.card (Fin n) := fun j => by
    rw [Fintype.card_fin]; omega
  let f : Fin k → (Fin n → ℝ) := fun j => TopK.bv hA ⟨j, hkn j⟩
  have hli : LinearIndependent ℝ f := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have := congrArg (fun v => v ⬝ᵥ f i) hg
    simp only [sum_dotProduct, smul_dotProduct, zero_dotProduct, f, TopK.bv_dot] at this
    rw [sum_eq_single i] at this
    · simpa using this
    · intro j _ hji
      have : (⟨j, hkn j⟩ : Fin (Fintype.card (Fin n))) ≠ ⟨i, hkn i⟩ := by
        intro h; apply hji; ext; simpa using congrArg Fin.val h
      simp [this]
    · intro h; exact absurd hi h
  have hle : Submodule.span ℝ (Set.range f) ≤ LinearMap.range (Matrix.toLin' (topProj hA k)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨f j, ?_⟩
    rw [Matrix.toLin'_apply, topProj, TopK.projS_mulVec, if_pos (by simp)]
  have := Submodule.finrank_mono hle
  rwa [finrank_span_eq_card hli, Fintype.card_fin] at this

/-! Part C, file 3: the homotopy `L_t = (1-t) L₀ + t L` from the complete split graph, and the
spectral gap between the `N`-th and `(N+1)`-st eigenvalues along it. -/
/-- the complete split graph with clique `C` -/
def G0 (C : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (u ∈ C ∨ v ∈ C)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance G0dec (C : Finset (Fin n)) : DecidableRel (G0 C).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (u ∈ C ∨ v ∈ C)))

theorem G0_adj (C : Finset (Fin n)) (u v : Fin n) :
    (G0 C).Adj u v ↔ u ≠ v ∧ (u ∈ C ∨ v ∈ C) := Iff.rfl

theorem G0_split (C : Finset (Fin n)) : IsSplitWith (G0 C) C := by
  constructor
  · intro a ha b _ hab
    exact ⟨hab, Or.inl (by simpa using ha)⟩
  · intro a ha b hb _ h
    simp only [Set.mem_compl_iff, mem_coe] at ha hb
    rcases h.2 with h | h
    · exact ha h
    · exact hb h

theorem G0_degree_S (C : Finset (Fin n)) (s : Fin n) (hs : s ∉ C) :
    ((G0 C).degree s : ℝ) = #C := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 2
  ext u
  rw [SimpleGraph.mem_neighborFinset, G0_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact absurd h hs
    · exact h
  · intro hu
    exact ⟨fun h => hs (h ▸ hu), Or.inr hu⟩

theorem G0_degree_C (C : Finset (Fin n)) (c : Fin n) (hc : c ∈ C) :
    ((G0 C).degree c : ℝ) = n - 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (G0 C).neighborFinset c = univ.erase c := by
    ext u
    rw [SimpleGraph.mem_neighborFinset, G0_adj, mem_erase]
    constructor
    · rintro ⟨h, _⟩; exact ⟨fun h' => h h'.symm, mem_univ _⟩
    · rintro ⟨h, _⟩; exact ⟨fun h' => h h'.symm, Or.inl hc⟩
  rw [this, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  have : 1 ≤ n := by
    have := c.2; omega
  push_cast [this]
  ring

/-- the homotopy -/
noncomputable def Lt (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 - t) • (G0 C).lapMatrix ℝ + t • G.lapMatrix ℝ

end BrouwerLaplacian.Dev.GMB.PartC
end

section
namespace BrouwerLaplacian.Dev.GMB.PartC
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
theorem Lt_herm (t : ℝ) : (Lt G C t).IsHermitian := by
  unfold IsHermitian Lt
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul,
    ((G0 C).isHermitian_lapMatrix ℝ).eq, (G.isHermitian_lapMatrix ℝ).eq]
  simp

theorem Lt_quad (t : ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (Lt G C t *ᵥ x) =
      (1 - t) * (x ⬝ᵥ ((G0 C).lapMatrix ℝ *ᵥ x)) + t * (x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x)) := by
  simp [Lt, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul]

theorem Lt_one_vec (t : ℝ) : Lt G C t *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  simp [Lt, add_mulVec, smul_mulVec, SimpleGraph.lapMatrix_mulVec_const_eq_zero]

theorem Lt_cont : Continuous (Lt G C) := by
  unfold Lt
  fun_prop

theorem Lt_at_one : Lt G C 1 = G.lapMatrix ℝ := by
  simp [Lt]

/-- On vectors vanishing on `C`, `x⬝L_t x ≤ ((1-t)N + tδ)|x|²`. -/
theorem quad_Lt_Q (hs : IsSplitWith G C) (δ : ℝ) (hδ : ∀ s ∉ C, (G.degree s : ℝ) ≤ δ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Fin n → ℝ) (hx : x ∈ Qsub C) :
    x ⬝ᵥ (Lt G C t *ᵥ x) ≤ ((1 - t) * #C + t * δ) * (x ⬝ᵥ x) := by
  rw [Lt_quad, quad_lap_Q (G0 C) C (G0_split C) x hx, quad_lap_Q G C hs x hx, dot_self_Q hx,
    mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun s hsC => ?_
  have hsC' : s ∉ C := by simpa using hsC
  rw [G0_degree_S C s hsC']
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hδ s hsC') ht0)
    (sq_nonneg (x s))
  nlinarith

/-- For `Σ x = 0`: `x⬝L₀x ≥ n|x|² - |S| Σ_S x²`. -/
theorem quad_L0_lower (x : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    n * (x ⬝ᵥ x) - #Cᶜ * ∑ s ∈ Cᶜ, x s ^ 2 ≤ x ⬝ᵥ ((G0 C).lapMatrix ℝ *ᵥ x) := by
  rw [quad_lap]
  have hpt : ∀ i j, (if (G0 C).Adj i j then (x i - x j) ^ 2 else 0) =
      (x i - x j) ^ 2 - if i ∈ Cᶜ then (if j ∈ Cᶜ then (x i - x j) ^ 2 else 0) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    by_cases hi : i ∈ C <;> by_cases hj : j ∈ C <;> simp [G0_adj, hij, hi, hj]
  have hb : ∀ i, ∑ j, (if i ∈ Cᶜ then (if j ∈ Cᶜ then (x i - x j) ^ 2 else 0) else 0) =
      if i ∈ Cᶜ then ∑ j ∈ Cᶜ, (x i - x j) ^ 2 else 0 := by
    intro i
    split_ifs with h
    · rw [sum_ite_mem, univ_inter]
    · simp
  simp only [hpt, sum_sub_distrib, hb]
  rw [sum_ite_mem, univ_inter]
  have h1 := sum_sq_diff (univ : Finset (Fin n)) x
  have h2 := sum_sq_diff Cᶜ x
  rw [h1, h2, hx, card_univ, Fintype.card_fin]
  have hxx : x ⬝ᵥ x = ∑ i, x i ^ 2 := by
    simp [dotProduct, sq]
  rw [hxx]
  nlinarith [sq_nonneg (∑ i ∈ Cᶜ, x i)]

end BrouwerLaplacian.Dev.GMB.PartC
end

section
namespace BrouwerLaplacian.Dev.GMB.PartC
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
  (hs : IsSplitWith G C) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : ∀ s ∉ C, (G.degree s : ℝ) ≤ δ)
  (hM : #C + 1 ≤ n)
  (i₀ : Fin (Fintype.card (Fin n))) (hi₀ : i₀.val + 1 = #C)
  (he : δ < (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i₀)
include hi₀ in
theorem ev_ge_i0 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val < #C) :
    hA.eigenvalues₀ i₀ ≤ hA.eigenvalues₀ i :=
  hA.eigenvalues₀_antitone (show i ≤ i₀ by rw [Fin.le_def]; omega)

include hs hδ0 hδ hM hi₀ he in
/-- On the top-`N` eigenspace of `L`, `x⬝L_t x > ((1-t)N + tδ)|x|²`. -/
theorem W1_lower (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Fin n → ℝ)
    (hx : topProj (G.isHermitian_lapMatrix ℝ) #C *ᵥ x = x) (hx0 : x ≠ 0) :
    ((1 - t) * #C + t * δ) * (x ⬝ᵥ x) < x ⬝ᵥ (Lt G C t *ᵥ x) := by
  set hL := G.isHermitian_lapMatrix ℝ
  set e := hL.eigenvalues₀ i₀
  have hray : e * (x ⬝ᵥ x) ≤ x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) :=
    topProj_rayleigh hL #C e (fun i hi => ev_ge_i0 C i₀ hi₀ hL i hi) x hx
  have hP1 : topProj hL #C *ᵥ (fun _ => (1 : ℝ)) = 0 := by
    apply topProj_mulVec_one hL #C (SimpleGraph.lapMatrix_mulVec_const_eq_zero _)
    intro i hi
    have := ev_ge_i0 C i₀ hi₀ hL i hi
    linarith
  have hsum : ∑ i, x i = 0 := by
    have : (fun _ => (1 : ℝ)) ⬝ᵥ x = 0 := by
      rw [← hx, dotProduct_mulVec, ← mulVec_transpose, topProj_transpose, hP1, zero_dotProduct]
    simpa [dotProduct] using this
  have hxx : 0 < x ⬝ᵥ x := by
    exact lt_of_le_of_ne (sum_nonneg fun i _ => mul_self_nonneg (x i))
      (fun h => hx0 (dotProduct_self_eq_zero.1 h.symm))
  have hsplit : x ⬝ᵥ x = ∑ c ∈ C, x c ^ 2 + ∑ s ∈ Cᶜ, x s ^ 2 := by
    rw [sum_add_sum_compl]; simp [dotProduct, sq]
  have ha : 0 < ∑ c ∈ C, x c ^ 2 := by
    rcases (sum_nonneg fun c (_ : c ∈ C) => sq_nonneg (x c)).lt_or_eq with h | h
    · exact h
    · exfalso
      have hQ : x ∈ Qsub C := by
        intro c hc
        have := (sum_eq_zero_iff_of_nonneg fun c (_ : c ∈ C) => sq_nonneg (x c)).1 h.symm c hc
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      have := quad_Lt_Q G C hs δ hδ 1 zero_le_one le_rfl x hQ
      rw [Lt_at_one] at this
      have : e * (x ⬝ᵥ x) ≤ δ * (x ⬝ᵥ x) := by linarith
      have := (mul_le_mul_iff_left₀ hxx).1 this
      linarith
  have hL0 := quad_L0_lower C x hsum
  rw [Lt_quad]
  have hcard : (#Cᶜ : ℝ) = n - #C := by
    rw [card_compl, Fintype.card_fin, Nat.cast_sub (by omega)]
  rw [hcard] at hL0
  have hMr : (#C : ℝ) + 1 ≤ n := by exact_mod_cast hM
  rcases ht1.lt_or_eq with ht1' | ht1'
  · -- t < 1: the `M Σ_C x²` term is strictly positive
    have h1 : 0 < (1 - t) * ((n - #C) * ∑ c ∈ C, x c ^ 2) := by
      apply mul_pos (by linarith); apply mul_pos (by linarith) ha
    have h2 : t * (δ * (x ⬝ᵥ x)) ≤ t * (e * (x ⬝ᵥ x)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) ht0
    have h3 : t * (e * (x ⬝ᵥ x)) ≤ t * (x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x)) :=
      mul_le_mul_of_nonneg_left hray ht0
    have h4 : (1 - t) * (n * (x ⬝ᵥ x) - (n - #C) * ∑ s ∈ Cᶜ, x s ^ 2) ≤
        (1 - t) * (x ⬝ᵥ ((G0 C).lapMatrix ℝ *ᵥ x)) :=
      mul_le_mul_of_nonneg_left hL0 (by linarith)
    rw [hsplit] at h2 h3 h4 ⊢
    nlinarith
  · subst ht1'
    have : δ * (x ⬝ᵥ x) < e * (x ⬝ᵥ x) := mul_lt_mul_of_pos_right he hxx
    simp only [sub_self, zero_mul, one_mul, zero_add]
    linarith

include hs hδ0 hδ hM hi₀ he in
/-- the strict lower bound `e_{N-1}(L_t) > (1-t)N + tδ` -/
theorem gap_lower (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * #C + t * δ < (Lt_herm G C t).eigenvalues₀ i₀ := by
  refine lt_eigenvalue_of_subspace _
    (LinearMap.range (Matrix.toLin' (topProj (G.isHermitian_lapMatrix ℝ) #C))) i₀ ?_ _ ?_
  · rw [hi₀]; exact finrank_range_topProj _ _ (by omega)
  · rintro x ⟨z, rfl⟩ hx0
    apply W1_lower G C hs δ hδ0 hδ hM i₀ hi₀ he t ht0 ht1 _ _ hx0
    rw [Matrix.toLin'_apply, mulVec_mulVec, topProj_idem]

include hs hδ in
theorem gap_upper (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin (Fintype.card (Fin n)))
    (hi : #C ≤ i.val) :
    (Lt_herm G C t).eigenvalues₀ i ≤ (1 - t) * #C + t * δ := by
  refine eigenvalue_le_of_subspace _ (Qsub C) i ?_ _ ?_
  · have := finrank_Qsub C; omega
  · exact fun x hx => quad_Lt_Q G C hs δ hδ t ht0 ht1 x hx

end BrouwerLaplacian.Dev.GMB.PartC
end

section
namespace BrouwerLaplacian.Dev.GMB.PartC
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
/-! Part C, file 4: Bai's entrywise identity for `V` (step 4 of Lemma 6) and the sign step. -/
theorem lap_mul_apply (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (W : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (G.lapMatrix ℝ * W) i j = G.degree i * W i j - ∑ k, if G.Adj i k then W k j else 0 := by
  rw [SimpleGraph.lapMatrix, Matrix.sub_mul, Matrix.sub_apply, SimpleGraph.degMatrix,
    diagonal_mul, SimpleGraph.adjMatrix_mul_apply, SimpleGraph.neighborFinset_eq_filter,
    sum_filter]

theorem Lt_mul_apply (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (t : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (Lt G C t * W) i j = (1 - t) * ((G0 C).lapMatrix ℝ * W) i j + t * (G.lapMatrix ℝ * W) i j := by
  simp [Lt, Matrix.add_mul, Matrix.smul_mul]

theorem deg_C_ge (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (hs : IsSplitWith G C) (c : Fin n) (hc : c ∈ C) : (#C : ℝ) - 1 ≤ G.degree c := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : C.erase c ⊆ G.neighborFinset c := by
    intro u hu
    rw [mem_erase] at hu
    rw [SimpleGraph.mem_neighborFinset]
    exact adj_of_mem hs hc hu.2 (Ne.symm hu.1)
  have h := card_le_card this
  rw [card_erase_of_mem hc] at h
  have : 1 ≤ #C := card_pos.2 ⟨c, hc⟩
  have : ((#C - 1 : ℕ) : ℝ) = #C - 1 := by push_cast [this]; ring
  rw [← this]; exact_mod_cast h

end BrouwerLaplacian.Dev.GMB.PartC
end

section
namespace BrouwerLaplacian.Dev.GMB.PartC
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
  (hs : IsSplitWith G C) (t : ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
  (hF1 : ∀ c' ∈ C, ∀ c ∈ C, W c' c = if c' = c then 1 else 0)
  (hF2 : ∀ c ∈ C, ∑ k, W k c = 0)
/-- `T c' = Σ_{k ∈ S, k ∼ c'} W k c` -/
def Tsum (W : Matrix (Fin n) (Fin n) ℝ) (c' c : Fin n) : ℝ :=
  ∑ k ∈ Cᶜ, if G.Adj c' k then W k c else 0

include hF1 hF2 in
theorem colsum_S (c : Fin n) (hc : c ∈ C) : ∑ k ∈ Cᶜ, W k c = -1 := by
  have h := hF2 c hc
  rw [← sum_add_sum_compl C] at h
  have h1 : ∑ k ∈ C, W k c = 1 := by
    rw [sum_congr rfl fun k hk => hF1 k hk c hc, sum_ite_eq' C c, if_pos hc]
  linarith

include hs hF1 in
theorem AW_S (s : Fin n) (hsC : s ∉ C) (c : Fin n) (hc : c ∈ C) :
    (Lt G C t * W) s c = (1 - t) * (#C * W s c - 1) +
      t * (G.degree s * W s c - if G.Adj s c then 1 else 0) := by
  rw [Lt_mul_apply, lap_mul_apply, lap_mul_apply, G0_degree_S C s hsC]
  have h0 : (∑ k, if (G0 C).Adj s k then W k c else 0) = 1 := by
    have : ∀ k, (if (G0 C).Adj s k then W k c else 0) = if k ∈ C then W k c else 0 := by
      intro k
      have : (G0 C).Adj s k ↔ k ∈ C := by
        rw [G0_adj]
        constructor
        · rintro ⟨_, h | h⟩
          · exact absurd h hsC
          · exact h
        · intro hk; exact ⟨fun h => hsC (h ▸ hk), Or.inr hk⟩
      simp only [this]
    rw [sum_congr rfl fun k _ => this k, sum_ite_mem, univ_inter,
      sum_congr rfl fun k hk => hF1 k hk c hc, sum_ite_eq' C c, if_pos hc]
  have h1 : (∑ k, if G.Adj s k then W k c else 0) = if G.Adj s c then 1 else 0 := by
    rw [sum_eq_single c]
    · split_ifs <;> simp [hF1 c hc c hc]
    · intro k _ hkc
      split_ifs with h
      · rw [hF1 k (nbr_mem hs hsC h) c hc, if_neg hkc]
      · rfl
    · simp
  rw [h0, h1]

include hs hF1 hF2 in
theorem AW_C (c' : Fin n) (hc' : c' ∈ C) (c : Fin n) (hc : c ∈ C) :
    (Lt G C t * W) c' c = (if c' = c then (1 - t) * n + t * G.degree c + t else 0) - t
      - t * Tsum G C W c' c := by
  rw [Lt_mul_apply, lap_mul_apply, lap_mul_apply, G0_degree_C C c' hc']
  have h0 : (∑ k, if (G0 C).Adj c' k then W k c else 0) = - W c' c := by
    have : ∀ k, (if (G0 C).Adj c' k then W k c else 0) = W k c - if k = c' then W k c else 0 := by
      intro k
      by_cases hk : k = c'
      · subst hk; simp [G0_adj]
      · have : (G0 C).Adj c' k := ⟨Ne.symm hk, Or.inl hc'⟩
        simp [this, hk]
    rw [sum_congr rfl fun k _ => this k, sum_sub_distrib, hF2 c hc, sum_ite_eq']
    simp
  have h1 : (∑ k, if G.Adj c' k then W k c else 0) =
      (if c' = c then 0 else 1) + Tsum G C W c' c := by
    rw [Tsum, ← sum_add_sum_compl C]
    congr 1
    rw [sum_eq_single c]
    · rw [hF1 c hc c hc, if_pos rfl]
      by_cases h : c' = c
      · subst h; simp
      · simp [h, adj_of_mem hs hc' hc h]
    · intro k hk hkc
      rw [hF1 k hk c hc, if_neg hkc]; simp
    · intro h; exact absurd hc h
  rw [h0, h1, hF1 c' hc' c hc]
  by_cases h : c' = c
  · subst h; simp only [if_true]; ring
  · simp only [h, if_false]; ring

theorem WEAW (s c : Fin n) (X : Matrix (Fin n) (Fin n) ℝ) :
    (W * Emat C * X) s c = ∑ c' ∈ C, W s c' * X c' c := by
  rw [Matrix.mul_assoc, mul_apply]
  simp only [Emat_mul_apply, mul_ite, mul_zero]
  rw [sum_ite_mem, univ_inter]

include hs hF1 hF2 in
/-- Bai's identity, entry `(s, c)`. -/
theorem key_identity (hF3 : Lt G C t * W = W * Emat C * (Lt G C t * W))
    (s : Fin n) (hsC : s ∉ C) (c : Fin n) (hc : c ∈ C) :
    W s c * ((1 - t) * #C + t * G.degree s - ((1 - t) * n + t * G.degree c + t)) =
      (1 - t) + t * (if G.Adj s c then 1 else 0) +
        t * ∑ c' ∈ C, W s c' * (-1 - Tsum G C W c' c) := by
  have h := congrFun (congrFun hF3 s) c
  rw [AW_S G C hs t W hF1 s hsC c hc, WEAW] at h
  rw [sum_congr rfl fun c' hc' => by rw [AW_C G C hs t W hF1 hF2 c' hc' c hc]] at h
  have h2 : ∑ c' ∈ C, W s c' * ((if c' = c then (1 - t) * n + t * G.degree c + t else 0) - t
      - t * Tsum G C W c' c) = W s c * ((1 - t) * n + t * G.degree c + t) +
        t * ∑ c' ∈ C, W s c' * (-1 - Tsum G C W c' c) := by
    have : ∀ c' ∈ C, W s c' * ((if c' = c then (1 - t) * n + t * G.degree c + t else 0) - t
        - t * Tsum G C W c' c) = (if c' = c then W s c' * ((1 - t) * n + t * G.degree c + t)
          else 0) + t * (W s c' * (-1 - Tsum G C W c' c)) := by
      intro c' _
      split_ifs <;> ring
    rw [sum_congr rfl this, sum_add_distrib, sum_ite_eq' C c, if_pos hc, mul_sum]
  rw [h2] at h
  linarith

include hF1 hF2 in
theorem Tsum_ge (hneg : ∀ s ∉ C, ∀ c ∈ C, W s c ≤ 0) (c' c : Fin n) (hc : c ∈ C) :
    -1 ≤ Tsum G C W c' c := by
  rw [← colsum_S C W hF1 hF2 c hc, Tsum]
  refine sum_le_sum fun k hk => ?_
  split_ifs
  · exact le_rfl
  · exact hneg k (by simpa using hk) c hc

include hs hF1 hF2 in
/-- The sign step: for `t < 1`, if `V ≤ 0` (or `t = 0`), then `V < 0`. -/
theorem sign_step (hF3 : Lt G C t * W = W * Emat C * (Lt G C t * W))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hNn : #C ≤ n)
    (hpre : t = 0 ∨ ∀ s ∉ C, ∀ c ∈ C, W s c ≤ 0) :
    ∀ s ∉ C, ∀ c ∈ C, W s c < 0 := by
  intro s hsC c hc
  have hid := key_identity G C hs t W hF1 hF2 hF3 s hsC c hc
  have hZ : 0 ≤ t * ∑ c' ∈ C, W s c' * (-1 - Tsum G C W c' c) := by
    rcases hpre with h | hneg
    · rw [h, zero_mul]
    · refine mul_nonneg ht0 (sum_nonneg fun c' hc' => ?_)
      have := Tsum_ge G C W hF1 hF2 hneg c' c hc
      exact mul_nonneg_of_nonpos_of_nonpos (hneg s hsC c' hc') (by linarith)
  have ha : 0 ≤ t * (if G.Adj s c then (1 : ℝ) else 0) :=
    mul_nonneg ht0 (by split_ifs <;> norm_num)
  have hf : (G.degree s : ℝ) ≤ #C := by exact_mod_cast degree_le G C hs s hsC
  have hd := deg_C_ge G C hs c hc
  have hn : (#C : ℝ) ≤ n := by exact_mod_cast hNn
  have hcoef : (1 - t) * #C + t * G.degree s - ((1 - t) * n + t * G.degree c + t) ≤ 0 := by
    nlinarith
  by_contra hpos
  push Not at hpos
  have : W s c * ((1 - t) * #C + t * G.degree s - ((1 - t) * n + t * G.degree c + t)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hpos hcoef
  linarith

include hs hF1 hF2 in
/-- the diagonal entries at `t = 1` -/
theorem AW_diag_one (c : Fin n) (hc : c ∈ C) :
    (Lt G C 1 * W) c c = G.degree c - Tsum G C W c c := by
  rw [AW_C G C hs 1 W hF1 hF2 c hc c hc, if_pos rfl]
  ring

end BrouwerLaplacian.Dev.GMB.PartC
end

section
namespace BrouwerLaplacian.Dev.GMB.PartC
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB Topology Filter Set
variable {n : ℕ}
/-! Part C, file 5: continuity of `V(t)`, the continuous induction `V ≤ 0` on `[0,1]`, and the
trace bound at `t = 1` (Bai, Lemma 6). -/
theorem topSum_congr {A B : Matrix (Fin n) (Fin n) ℝ} (h : A = B) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (k : ℕ) : topSum hA k = topSum hB k := by
  subst h; rfl

theorem trace_Emat_mul (C : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ) :
    (Emat C * X).trace = ∑ c ∈ C, X c c := by
  simp only [Matrix.trace, Matrix.diag, Emat_mul_apply]
  rw [sum_ite_mem, Finset.univ_inter]

theorem deg_sum (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : Fin n) :
    (G.degree c : ℝ) = ∑ k, if G.Adj c k then (1 : ℝ) else 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.sum_boole]

/-- The combinatorial end of Lemma 6. -/
theorem final_count (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (hs : IsSplitWith G C) (T : Fin n → ℝ) (hT1 : ∀ c ∈ C, -1 ≤ T c)
    (hT0 : ∀ c ∈ C, (∀ k ∉ C, ¬ G.Adj c k) → T c = 0) :
    ∑ c ∈ C, ((G.degree c : ℝ) - T c) ≤ ∑ v, ((min (G.degree v) #C : ℕ) : ℝ) := by
  set m : Fin n → ℝ := fun c => ∑ k ∈ Cᶜ, if G.Adj c k then (1 : ℝ) else 0
  have hdeg : ∀ c ∈ C, (G.degree c : ℝ) = (#C - 1) + m c := by
    intro c hc
    rw [deg_sum G, ← sum_add_sum_compl C]
    congr 1
    have : ∀ k ∈ C, (if G.Adj c k then (1 : ℝ) else 0) = 1 - if k = c then 1 else 0 := by
      intro k hk
      by_cases h : k = c
      · subst h; simp
      · simp [h, adj_of_mem hs hc hk (Ne.symm h)]
    rw [sum_congr rfl this, sum_sub_distrib, sum_ite_eq' C c, if_pos hc]
    simp
  have hm : ∑ c ∈ C, m c = ∑ s ∈ Cᶜ, (G.degree s : ℝ) := by
    simp only [m]
    rw [sum_comm]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ∉ C := by simpa using hk
    rw [deg_sum G, ← sum_add_sum_compl C]
    rw [sum_eq_zero (s := Cᶜ) fun j hj => by
      rw [if_neg]; intro h; exact (by simpa using hj : j ∉ C) (nbr_mem hs hk' h)]
    rw [add_zero]
    exact sum_congr rfl fun c _ => by simp only [G.adj_comm]
  have hRHS : ∑ v, ((min (G.degree v) #C : ℕ) : ℝ) =
      ∑ c ∈ C, ((min (G.degree c) #C : ℕ) : ℝ) + ∑ s ∈ Cᶜ, (G.degree s : ℝ) := by
    rw [← sum_add_sum_compl C]
    congr 1
    refine sum_congr rfl fun s hs' => ?_
    rw [min_eq_left (degree_le G C hs s (by simpa using hs'))]
  rw [hRHS, ← hm, ← sum_add_distrib]
  refine sum_le_sum fun c hc => ?_
  have hmc : 0 ≤ m c := sum_nonneg fun k _ => by split_ifs <;> norm_num
  rw [Nat.cast_min]
  by_cases h : ∃ k ∉ C, G.Adj c k
  · obtain ⟨k, hk, hadj⟩ := h
    have : 1 ≤ m c := by
      have h := single_le_sum (s := Cᶜ) (f := fun k => if G.Adj c k then (1 : ℝ) else 0)
        (fun k _ => by split_ifs <;> norm_num) (by simpa using hk : k ∈ Cᶜ)
      simp only [hadj, if_true] at h
      exact h
    rw [min_eq_right (by rw [hdeg c hc]; linarith)]
    have := hT1 c hc
    rw [hdeg c hc]; linarith
  · push Not at h
    rw [hT0 c hc h]
    have hm0 : m c = 0 := sum_eq_zero fun k hk => by rw [if_neg (h k (by simpa using hk))]
    rw [min_eq_left (by rw [hdeg c hc, hm0]; linarith)]
    linarith

end BrouwerLaplacian.Dev.GMB.PartC
end

section
namespace BrouwerLaplacian.Dev.GMB.PartC
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB Topology Filter Set
variable {n : ℕ}
variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
  (hs : IsSplitWith G C) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : ∀ s ∉ C, (G.degree s : ℝ) ≤ δ)
  (hM : #C + 1 ≤ n)
  (i₀ : Fin (Fintype.card (Fin n))) (hi₀ : i₀.val + 1 = #C)
  (he : δ < (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i₀)
/-- the projection along the homotopy -/
noncomputable abbrev Pt (t : ℝ) : Matrix (Fin n) (Fin n) ℝ := topProj (Lt_herm G C t) #C

end BrouwerLaplacian.Dev.GMB.PartC
end

section
namespace BrouwerLaplacian.Dev.GMB.PartC
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB Topology Filter Set
variable {n : ℕ}
variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
  (hs : IsSplitWith G C) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : ∀ s ∉ C, (G.degree s : ℝ) ≤ δ)
  (hM : #C + 1 ≤ n)
  (i₀ : Fin (Fintype.card (Fin n))) (hi₀ : i₀.val + 1 = #C)
  (he : δ < (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i₀)
include hs hδ0 hδ hM hi₀ he
theorem Pt_UQ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ y : Fin n → ℝ, Pt G C t *ᵥ y = y → (∀ c ∈ C, y c = 0) → y = 0 := by
  intro y hy hQ
  have hg := gap_lower G C hs δ hδ0 hδ hM i₀ hi₀ he t ht0 ht1
  have h1 := topProj_rayleigh (Lt_herm G C t) #C _
    (fun i hi => ev_ge_i0 C i₀ hi₀ (Lt_herm G C t) i hi) y hy
  have h2 := quad_Lt_Q G C hs δ hδ t ht0 ht1 y hQ
  have hnn : 0 ≤ y ⬝ᵥ y := sum_nonneg fun i _ => mul_self_nonneg (y i)
  have : y ⬝ᵥ y = 0 := by
    by_contra hne
    have hpos : 0 < y ⬝ᵥ y := lt_of_le_of_ne hnn (Ne.symm hne)
    nlinarith
  exact dotProduct_self_eq_zero.1 this

theorem Pt_one (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Pt G C t *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  apply topProj_mulVec_one _ _ (Lt_one_vec G C t)
  intro i hi
  have hg := gap_lower G C hs δ hδ0 hδ hM i₀ hi₀ he t ht0 ht1
  have := ev_ge_i0 C i₀ hi₀ (Lt_herm G C t) i hi
  have : 0 ≤ (1 - t) * #C + t * δ := by
    have : (0 : ℝ) ≤ #C := Nat.cast_nonneg _
    nlinarith
  linarith

theorem Pt_rank (t : ℝ) : #C ≤ Module.finrank ℝ (LinearMap.range (Matrix.toLin' (Pt G C t))) :=
  finrank_range_topProj _ _ (by omega)

theorem Pt_cont : ContinuousOn (Pt G C) (Icc 0 1) := by
  apply topProj_continuousOn (Lt G C) (Lt_herm G C) (Lt_cont G C) (Icc 0 1) #C
  rintro t ⟨ht0, ht1⟩
  have hg := gap_lower G C hs δ hδ0 hδ hM i₀ hi₀ he t ht0 ht1
  refine ⟨((1 - t) * #C + t * δ + (Lt_herm G C t).eigenvalues₀ i₀) / 2, ?_, ?_⟩
  · intro i hi
    have := ev_ge_i0 C i₀ hi₀ (Lt_herm G C t) i hi
    linarith
  · intro i hi
    have := gap_upper G C hs δ hδ t ht0 ht1 i hi
    linarith

/-- the hypotheses of the abstract matrix algebra, at `t ∈ [0,1]` -/
theorem Pt_facts (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∀ c' ∈ C, ∀ c ∈ C, Wmat C (Pt G C t) c' c = if c' = c then 1 else 0) ∧
    (∀ c ∈ C, ∑ k, Wmat C (Pt G C t) k c = 0) ∧
    (Lt G C t * Wmat C (Pt G C t) = Wmat C (Pt G C t) * Emat C * (Lt G C t * Wmat C (Pt G C t))) ∧
    IsUnit (Kmat C (Pt G C t)).det := by
  have hPT := topProj_transpose (Lt_herm G C t) #C
  have hPP := topProj_idem (Lt_herm G C t) #C
  have hUQ := Pt_UQ G C hs δ hδ0 hδ hM i₀ hi₀ he t ht0 ht1
  have hrank := Pt_rank G C hs δ hδ0 hδ hM i₀ hi₀ he t
  refine ⟨fun c' hc' c hc => W_CC C _ hPT hPP hUQ hrank c' c hc' hc,
    fun c _ => colsum_W C _ hPT hPP hUQ hrank (Pt_one G C hs δ hδ0 hδ hM i₀ hi₀ he t ht0 ht1) c,
    AW_eq C _ hPT hPP hUQ hrank _ (topProj_comm _ _),
    Kmat_isUnit C _ hPT hPP hUQ hrank⟩

theorem W_cont : ContinuousOn (fun t => Wmat C (Pt G C t)) (Icc 0 1) := by
  have hP := Pt_cont G C hs δ hδ0 hδ hM i₀ hi₀ he
  have hK : ContinuousOn (fun t => Kmat C (Pt G C t)) (Icc 0 1) := by
    unfold Kmat
    exact ((continuousOn_const.mul hP).mul continuousOn_const).add continuousOn_const
  have hKi : ContinuousOn (fun t => (Kmat C (Pt G C t))⁻¹) (Icc 0 1) := by
    intro t ht
    obtain ⟨u, hu⟩ := (Pt_facts G C hs δ hδ0 hδ hM i₀ hi₀ he t ht.1 ht.2).2.2.2
    have : ContinuousAt Ring.inverse (Kmat C (Pt G C t)).det := by
      rw [← hu]; exact NormedRing.inverse_continuousAt u
    exact ContinuousAt.comp_continuousWithinAt (g := fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹)
      (f := fun t => Kmat C (Pt G C t)) (continuousAt_matrix_inv _ this) (hK t ht)
  unfold Wmat
  exact hP.mul hKi

theorem W_nonpos : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∉ C, ∀ c ∈ C, Wmat C (Pt G C t) s c ≤ 0 := by
  have hNn : #C ≤ n := by omega
  set S : Set ℝ := {t | ∀ s ∉ C, ∀ c ∈ C, Wmat C (Pt G C t) s c ≤ 0}
  have hWc := W_cont G C hs δ hδ0 hδ hM i₀ hi₀ he
  have hent : ∀ s c, ContinuousOn (fun t => Wmat C (Pt G C t) s c) (Icc 0 1) := fun s c =>
    (continuous_id.matrix_elem s c).comp_continuousOn hWc
  have hclosed : IsClosed (S ∩ Icc 0 1) := by
    have hT : IsClosed {M : Matrix (Fin n) (Fin n) ℝ | ∀ s ∉ C, ∀ c ∈ C, M s c ≤ 0} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun s => isClosed_iInter fun _ => isClosed_iInter fun c =>
        isClosed_iInter fun _ => isClosed_le (continuous_id.matrix_elem s c) continuous_const
    have := hWc.preimage_isClosed_of_isClosed isClosed_Icc hT
    rwa [Set.inter_comm] at this
  have hstep : ∀ t, 0 ≤ t → t < 1 → (t = 0 ∨ t ∈ S) →
      ∀ s ∉ C, ∀ c ∈ C, Wmat C (Pt G C t) s c < 0 := by
    intro t ht0 ht1 hpre
    obtain ⟨hF1, hF2, hF3, -⟩ := Pt_facts G C hs δ hδ0 hδ hM i₀ hi₀ he t ht0 ht1.le
    exact sign_step G C hs t _ hF1 hF2 hF3 ht0 ht1 hNn hpre
  have h0 : (0 : ℝ) ∈ S := fun s hsC c hc =>
    (hstep 0 le_rfl zero_lt_one (Or.inl rfl) s hsC c hc).le
  have hsub := hclosed.Icc_subset_of_forall_mem_nhdsWithin h0 (by
    rintro x ⟨hxS, hx0, hx1⟩
    have hneg := hstep x hx0 hx1 (Or.inr hxS)
    have hev : ∀ s c, ∀ᶠ y in 𝓝[Icc 0 1] x, s ∉ C → c ∈ C → Wmat C (Pt G C y) s c ≤ 0 := by
      intro s c
      by_cases hsc : s ∉ C ∧ c ∈ C
      · have := (hent s c x ⟨hx0, hx1.le⟩).eventually (gt_mem_nhds (hneg s hsc.1 c hsc.2))
        exact this.mono fun y hy _ _ => hy.le
      · exact Eventually.of_forall fun y h1 h2 => absurd ⟨h1, h2⟩ hsc
    have hall : ∀ᶠ y in 𝓝[Icc 0 1] x, y ∈ S := by
      have := eventually_all.2 fun s => eventually_all.2 (hev s)
      exact this.mono fun y hy s hsC c hc => hy s c hsC hc
    have hIcc : Icc (0 : ℝ) 1 ∈ 𝓝[>] x :=
      mem_of_superset (Ioo_mem_nhdsGT hx1) fun y hy => ⟨by linarith [hy.1], hy.2.le⟩
    exact nhdsWithin_le_of_mem hIcc hall)
  intro t ht
  exact hsub ht

theorem main_bound :
    topSum (G.isHermitian_lapMatrix ℝ) #C ≤ ∑ v, ((min (G.degree v) #C : ℕ) : ℝ) := by
  obtain ⟨hF1, hF2, hF3, -⟩ := Pt_facts G C hs δ hδ0 hδ hM i₀ hi₀ he 1 zero_le_one le_rfl
  have hneg := W_nonpos G C hs δ hδ0 hδ hM i₀ hi₀ he 1 ⟨zero_le_one, le_rfl⟩
  have hPT := topProj_transpose (Lt_herm G C 1) #C
  have hPP := topProj_idem (Lt_herm G C 1) #C
  have hUQ := Pt_UQ G C hs δ hδ0 hδ hM i₀ hi₀ he 1 zero_le_one le_rfl
  have hrank := Pt_rank G C hs δ hδ0 hδ hM i₀ hi₀ he 1
  rw [topSum_congr (Lt_at_one G C).symm _ (Lt_herm G C 1), ← topProj_trace_mul,
    trace_eq C _ hPT hPP hUQ hrank _ (topProj_comm _ _), trace_Emat_mul]
  rw [sum_congr rfl fun c hc => AW_diag_one G C hs _ hF1 hF2 c hc]
  refine final_count G C hs (fun c => Tsum G C (Wmat C (Pt G C 1)) c c) ?_ ?_
  · intro c hc
    exact Tsum_ge G C _ hF1 hF2 hneg c c hc
  · intro c _ hno
    exact sum_eq_zero fun k hk => by rw [if_neg (hno k (by simpa using hk))]

end BrouwerLaplacian.Dev.GMB.PartC
end

section
namespace BrouwerLaplacian.Dev.GMB.PartC
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
/-- Bai, Lemma 6. -/
theorem lemma6 (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (hsplit : IsSplitWith G C)
    (hyp : ∀ i : Fin (Fintype.card (Fin n)), i.val + 1 = #C →
      ((#C : ℝ) < (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i ∨
        ((G.isHermitian_lapMatrix ℝ).eigenvalues₀ i = #C ∧ ∀ s ∉ C, G.degree s < #C))) :
    topSum (G.isHermitian_lapMatrix ℝ) #C ≤ ∑ v, ((min (G.degree v) #C : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos #C with hN0 | hN1
  · rw [hN0]
    have : topSum (G.isHermitian_lapMatrix ℝ) 0 = 0 := by simp [topSum]
    rw [this]
    exact sum_nonneg fun v _ => Nat.cast_nonneg _
  have hNn : #C ≤ n := by simpa using card_le_univ C
  have hlt : #C - 1 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  set i₀ : Fin (Fintype.card (Fin n)) := ⟨#C - 1, hlt⟩
  have hi₀ : i₀.val + 1 = #C := by simp only [i₀]; omega
  have hN1r : (1 : ℝ) ≤ #C := by exact_mod_cast hN1
  obtain ⟨δ, hδ0, hδ, he⟩ : ∃ δ : ℝ, 0 ≤ δ ∧ (∀ s ∉ C, (G.degree s : ℝ) ≤ δ) ∧
      δ < (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i₀ := by
    rcases hyp i₀ hi₀ with h | ⟨h1, h2⟩
    · exact ⟨#C, Nat.cast_nonneg _, fun s hs => by exact_mod_cast degree_le G C hsplit s hs, h⟩
    · refine ⟨(#C : ℝ) - 1, by linarith, fun s hs => ?_, by rw [h1]; linarith⟩
      have : G.degree s + 1 ≤ #C := h2 s hs
      have : (G.degree s : ℝ) + 1 ≤ #C := by exact_mod_cast this
      linarith
  have hM : #C + 1 ≤ n := by
    by_contra hcon
    have hNeq : #C = n := by omega
    have hne : (fun _ => (1 : ℝ)) ≠ (0 : Fin n → ℝ) := by
      intro h
      have := congrFun h ⟨0, by omega⟩
      simp at this
    have : (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i₀ ≤ 0 := by
      refine eigenvalue_le_of_subspace _ (Submodule.span ℝ {fun _ => (1 : ℝ)}) i₀ ?_ 0 ?_
      · rw [finrank_span_singleton hne]; omega
      · intro x hx
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
        rw [mulVec_smul, SimpleGraph.lapMatrix_mulVec_const_eq_zero]
        simp
    linarith
  exact main_bound G C hsplit δ hδ0 hδ hM i₀ hi₀ he

end BrouwerLaplacian.Dev.GMB.PartC
end

section
namespace BrouwerLaplacian.Dev.GMB
open Finset Matrix BrouwerLaplacian
variable {n : ℕ}
alias lemma6 := BrouwerLaplacian.Dev.GMB.PartC.lemma6

end BrouwerLaplacian.Dev.GMB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartD
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
/-! Part D, generic helpers: quadratic forms of Laplacians, `topSum`/`D` increments,
projections, split graphs. -/
/-- `D_k(G) = Σ_v min(deg v, k)`. -/
noncomputable def Dk (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) : ℝ :=
  ∑ v, ((min (G.degree v) k : ℕ) : ℝ)

theorem degree_eq_card (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    G.degree v = #(univ.filter (G.Adj v)) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]

end BrouwerLaplacian.Dev.GMB.PartD
end

section
namespace BrouwerLaplacian.Dev.GMB.PartD
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
variable (hstar : ∀ u v, G.Adj u v → G.degree u < k → k ≤ G.degree v)
include hstar
theorem addClique_degree_out (s : Fin n) (hs : s ∉ bigC G k) :
    (addClique G (bigC G k)).degree s = G.degree s := by
  rw [degree_eq_card, degree_eq_card]
  congr 1
  ext j
  simp only [mem_filter, mem_univ, true_and, addClique_adj]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h.2.1 hs
  · exact Or.inl

end BrouwerLaplacian.Dev.GMB.PartD
end

section
namespace BrouwerLaplacian.Dev.GMB.PartD
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
theorem addClique_degree_ge (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (v : Fin n) : G.degree v ≤ (addClique G C).degree v := by
  rw [degree_eq_card, degree_eq_card]
  refine card_le_card fun j hj => ?_
  simp only [mem_filter, mem_univ, true_and, addClique_adj] at hj ⊢
  exact Or.inl hj

theorem addClique_Dk (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (hstar : ∀ u v, G.Adj u v → G.degree u < k → k ≤ G.degree v) :
    Dk (addClique G (bigC G k)) k = Dk G k := by
  unfold Dk
  refine sum_congr rfl fun v _ => ?_
  by_cases hv : v ∈ bigC G k
  · have h1 := (mem_bigC G k v).1 hv
    have h2 := addClique_degree_ge G (bigC G k) v
    rw [min_eq_right h1, min_eq_right (le_trans h1 h2)]
  · rw [addClique_degree_out G k hstar v hv]

theorem quad_lap (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℝ) :
    x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) =
      (∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 := by
  rw [← SimpleGraph.lapMatrix_toLinearMap₂', Matrix.toLinearMap₂'_apply']

theorem quad_lap_mono (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : ∀ a b, G.Adj a b → H.Adj a b) (x : Fin n → ℝ) :
    x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) ≤ x ⬝ᵥ (H.lapMatrix ℝ *ᵥ x) := by
  rw [quad_lap, quad_lap]
  gcongr with i _ j _
  by_cases h : G.Adj i j
  · simp [h, hGH i j h]
  · simp only [h, if_false]; split_ifs <;> positivity

theorem topSum_mono {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ i, hA.eigenvalues₀ i ≤ hB.eigenvalues₀ i) (k : ℕ) :
    topSum hA k ≤ topSum hB k := by
  unfold topSum
  exact sum_le_sum fun i _ => h i

theorem topSum_zero {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) : topSum hA 0 = 0 := by
  unfold topSum; simp

theorem topSum_succ {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (j : ℕ)
    (hj : j < Fintype.card (Fin n)) :
    topSum hA (j + 1) = topSum hA j + hA.eigenvalues₀ ⟨j, hj⟩ := by
  unfold topSum
  have : (univ.filter (fun i : Fin (Fintype.card (Fin n)) => i.val < j + 1))
      = insert ⟨j, hj⟩ (univ.filter (fun i : Fin (Fintype.card (Fin n)) => i.val < j)) := by
    ext i; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega
  rw [this, sum_insert (by simp), add_comm]

theorem Dk_succ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (j : ℕ) :
    Dk G (j + 1) = Dk G j + (#(univ.filter (fun v => j + 1 ≤ G.degree v)) : ℝ) := by
  unfold Dk
  rw [card_filter]
  have : ∑ v, min (G.degree v) (j + 1) = ∑ v, min (G.degree v) j
      + ∑ v, (if j + 1 ≤ G.degree v then 1 else 0) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun v _ => ?_
    split_ifs <;> omega
  rw [← Nat.cast_sum, ← Nat.cast_sum, this, Nat.cast_add]

theorem Dk_nonneg (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (j : ℕ) : 0 ≤ Dk G j := by
  unfold Dk; positivity

/-- For a symmetric idempotent `P`, `w ⬝ P w ≤ w ⬝ w`. -/
theorem proj_quad_le {P : Matrix (Fin n) (Fin n) ℝ} (hPs : Pᵀ = P) (hPP : P * P = P)
    (w : Fin n → ℝ) : w ⬝ᵥ (P *ᵥ w) ≤ w ⬝ᵥ w := by
  set y := P *ᵥ w with hy
  have h1 : w ⬝ᵥ y = y ⬝ᵥ y := by
    have : y = P *ᵥ y := by rw [hy, mulVec_mulVec, hPP]
    conv_lhs => rw [this]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hPs]
  have h2 : 0 ≤ (w - y) ⬝ᵥ (w - y) := by
    simp only [dotProduct]; exact sum_nonneg fun i _ => mul_self_nonneg _
  have h3 : (w - y) ⬝ᵥ (w - y) = w ⬝ᵥ w - 2 * (w ⬝ᵥ y) + y ⬝ᵥ y := by
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm y w]; ring
  linarith

theorem trace_mul_vecMulVec (P : Matrix (Fin n) (Fin n) ℝ) (hPs : Pᵀ = P) (w : Fin n → ℝ) :
    (P * vecMulVec w w).trace = w ⬝ᵥ (P *ᵥ w) := by
  rw [Matrix.trace_mul_comm, vecMulVec_mul, Matrix.trace_vecMulVec, ← Matrix.mulVec_transpose,
    hPs]

/-- In a split graph, a vertex outside the clique has degree at most the clique size. -/
theorem degree_le_of_split (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (hs : IsSplitWith G C) (s : Fin n) (hsC : s ∉ C) : G.degree s ≤ #C := by
  rw [degree_eq_card]
  refine card_le_card fun v hv => ?_
  simp only [mem_filter, mem_univ, true_and] at hv
  by_contra hvC
  exact hs.2 (by simpa using hsC) (by simpa using hvC) (G.ne_of_adj hv) hv

theorem split_compl (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) (hs : IsSplitWith G C) :
    IsSplitWith Gᶜ Cᶜ := by
  constructor
  · intro a ha b hb hab
    simp only [coe_compl, Set.mem_compl_iff, mem_coe] at ha hb
    rw [SimpleGraph.compl_adj]
    exact ⟨hab, fun h => hs.2 (by simpa using ha) (by simpa using hb) hab h⟩
  · intro a ha b hb hab h
    simp only [coe_compl, compl_compl, mem_coe] at ha hb
    rw [SimpleGraph.compl_adj] at h
    exact h.2 (hs.1 ha hb hab)

/-! Part D: Bai's Lemma 13 (edge deletion). -/
/-- `G` with the edge `uv` deleted. -/
def delE (G : SimpleGraph (Fin n)) (u v : Fin n) : SimpleGraph (Fin n) where
  Adj a b := G.Adj a b ∧ ¬ (a = u ∧ b = v) ∧ ¬ (a = v ∧ b = u)
  symm := ⟨fun a b h => ⟨h.1.symm, fun h' => h.2.2 ⟨h'.2, h'.1⟩, fun h' => h.2.1 ⟨h'.2, h'.1⟩⟩⟩
  loopless := ⟨fun a h => G.irrefl h.1⟩

instance delE_dec (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    DecidableRel (delE G u v).Adj := fun a b =>
  inferInstanceAs (Decidable (G.Adj a b ∧ ¬ (a = u ∧ b = v) ∧ ¬ (a = v ∧ b = u)))

theorem delE_adj (G : SimpleGraph (Fin n)) (u v a b : Fin n) :
    (delE G u v).Adj a b ↔ G.Adj a b ∧ ¬ (a = u ∧ b = v) ∧ ¬ (a = v ∧ b = u) := Iff.rfl

end BrouwerLaplacian.Dev.GMB.PartD
end

section
namespace BrouwerLaplacian.Dev.GMB.PartD
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {u v : Fin n} (huv : G.Adj u v)
include huv
theorem delE_degree_real (w : Fin n) :
    ((delE G u v).degree w : ℝ) =
      (G.degree w : ℝ) - (if w = u then 1 else 0) - (if w = v then 1 else 0) := by
  have hne : u ≠ v := G.ne_of_adj huv
  rw [SimpleGraph.degree_eq_sum_if_adj, SimpleGraph.degree_eq_sum_if_adj]
  have h1 : ∀ j, (if (delE G u v).Adj w j then (1 : ℝ) else 0) =
      (if G.Adj w j then 1 else 0) - (if w = u ∧ j = v then 1 else 0)
        - (if w = v ∧ j = u then 1 else 0) := by
    intro j
    simp only [delE_adj]
    by_cases h2 : w = u ∧ j = v
    · obtain ⟨rfl, rfl⟩ := h2
      simp [huv, hne]
    · by_cases h3 : w = v ∧ j = u
      · obtain ⟨rfl, rfl⟩ := h3
        simp [huv.symm, hne.symm]
      · simp [h2, h3]
  rw [sum_congr rfl fun j _ => h1 j, sum_sub_distrib, sum_sub_distrib]
  congr 2
  · by_cases h : w = u <;> simp [h]
  · by_cases h : w = v <;> simp [h]

theorem delE_degree (w : Fin n) :
    (delE G u v).degree w + (if w = u then 1 else 0) + (if w = v then 1 else 0) = G.degree w := by
  have := delE_degree_real G huv w
  have h : ((delE G u v).degree w : ℝ) + (if w = u then 1 else 0) + (if w = v then 1 else 0)
      = G.degree w := by rw [this]; ring
  exact_mod_cast h

theorem delE_lap :
    G.lapMatrix ℝ = (delE G u v).lapMatrix ℝ +
      vecMulVec (Pi.single u 1 - Pi.single v 1) (Pi.single u 1 - Pi.single v 1) := by
  have hne : u ≠ v := G.ne_of_adj huv
  ext i j
  simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply, Matrix.add_apply, diagonal_apply,
    SimpleGraph.adjMatrix_apply, vecMulVec_apply, Pi.sub_apply, Pi.single_apply,
    delE_degree_real G huv, delE_adj]
  by_cases hij : i = j
  · subst hij
    simp only [if_true, G.irrefl, false_and, if_false]
    by_cases hiu : i = u
    · subst hiu; simp [hne]
    · by_cases hiv : i = v
      · subst hiv; simp [hiu]
      · simp [hiu, hiv]
  · simp only [hij, if_false]
    by_cases hiu : i = u
    · subst hiu
      by_cases hjv : j = v
      · subst hjv; simp [huv, hne, Ne.symm hij]
      · simp [hjv, Ne.symm hij, hne]
    · by_cases hiv : i = v
      · subst hiv
        by_cases hju : j = u
        · subst hju; simp [huv.symm, hne, hij]
        · simp [hju, Ne.symm hij, hiu]
      · simp [hiu, hiv]

end BrouwerLaplacian.Dev.GMB.PartD
end

section
namespace BrouwerLaplacian.Dev.GMB.PartD
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
variable {n : ℕ}
theorem single_sub_dot {u v : Fin n} (hne : u ≠ v) :
    (Pi.single u 1 - Pi.single v 1 : Fin n → ℝ) ⬝ᵥ (Pi.single u 1 - Pi.single v 1) = 2 := by
  simp only [dotProduct, Pi.sub_apply, Pi.single_apply]
  have : ∀ i : Fin n, ((if i = u then (1 : ℝ) else 0) - (if i = v then 1 else 0)) *
      ((if i = u then 1 else 0) - (if i = v then 1 else 0))
      = (if i = u then 1 else 0) + (if i = v then 1 else 0) := by
    intro i
    by_cases hiu : i = u
    · subst hiu; simp [hne]
    · by_cases hiv : i = v
      · subst hiv; simp [hne.symm]
      · simp [hiu, hiv]
  rw [sum_congr rfl fun i _ => this i, sum_add_distrib]
  simp; norm_num

theorem min_add_aux (a b k e : ℕ) (h : a + e = b) (hb : e = 0 ∨ b ≤ k) :
    min b k = min a k + e := by omega

/-- Bai's Lemma 13, as an induction step: an edge with both endpoint degrees `≤ k` can be
deleted. -/
theorem lemma13 (k : ℕ) (hk : k ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {u v : Fin n} (huv : G.Adj u v) (hu : G.degree u ≤ k) (hv : G.degree v ≤ k)
    (IH : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj],
      ∑ w, G'.degree w < ∑ w, G.degree w →
        topSum (G'.isHermitian_lapMatrix ℝ) k ≤ Dk G' k) :
    topSum (G.isHermitian_lapMatrix ℝ) k ≤ Dk G k := by
  have hne : u ≠ v := G.ne_of_adj huv
  set G' := delE G u v
  have hdeg := delE_degree G huv
  -- degree sum drops
  have hsum : ∑ w, G'.degree w + 2 = ∑ w, G.degree w := by
    rw [← sum_congr rfl fun w _ => hdeg w, sum_add_distrib, sum_add_distrib]
    simp; rfl
  have hD : Dk G' k + 2 = Dk G k := by
    unfold Dk
    have : ∑ w, min (G'.degree w) k + 2 = ∑ w, min (G.degree w) k := by
      have h1 : ∀ w, min (G.degree w) k
          = min (G'.degree w) k + (if w = u then 1 else 0) + (if w = v then 1 else 0) := by
        intro w
        rw [add_assoc]
        refine min_add_aux _ _ _ _ (by rw [← add_assoc]; exact hdeg w) ?_
        by_cases hwu : w = u
        · exact Or.inr (hwu ▸ hu)
        · by_cases hwv : w = v
          · exact Or.inr (hwv ▸ hv)
          · left; simp [hwu, hwv]
      rw [sum_congr rfl fun w _ => h1 w, sum_add_distrib, sum_add_distrib]
      simp
    rw [← Nat.cast_sum, ← Nat.cast_sum, ← this]; push_cast; ring
  have hIH := IH G' (by omega)
  set P := topProj (G.isHermitian_lapMatrix ℝ) k
  have hPs := topProj_transpose (G.isHermitian_lapMatrix ℝ) k
  have hPP := topProj_idem (G.isHermitian_lapMatrix ℝ) k
  have hPt : P.trace = k := topProj_trace (G.isHermitian_lapMatrix ℝ) (by simpa using hk)
  have hKF := trace_mul_le_topSum (G'.isHermitian_lapMatrix ℝ) hPs hPP hPt
  have h1 : topSum (G.isHermitian_lapMatrix ℝ) k
      = (P * G'.lapMatrix ℝ).trace + (P * vecMulVec (Pi.single u 1 - Pi.single v 1)
          (Pi.single u 1 - Pi.single v 1)).trace := by
    rw [← topProj_trace_mul, ← trace_add, ← mul_add, ← delE_lap G huv]
  rw [trace_mul_vecMulVec P hPs] at h1
  have h2 := proj_quad_le hPs hPP (Pi.single u 1 - Pi.single v 1 : Fin n → ℝ)
  rw [single_sub_dot hne] at h2
  linarith

/-! Part D: the complement step (Bai §4, the case `λ_N < N`). -/
/-- the all-ones vector -/
def one : Fin n → ℝ := fun _ => 1

theorem lap_apply (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i j : Fin n) :
    G.lapMatrix ℝ i j = (if i = j then (G.degree i : ℝ) else 0) - (if G.Adj i j then 1 else 0) := by
  simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply, diagonal_apply]

theorem degree_compl_real (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    (Gᶜ.degree v : ℝ) = n - 1 - G.degree v := by
  rw [Gᶜ.degree_eq_sum_if_adj (R := ℝ) v, G.degree_eq_sum_if_adj (R := ℝ) v]
  have : ∀ j, (if Gᶜ.Adj v j then (1 : ℝ) else 0) =
      1 - (if v = j then 1 else 0) - (if G.Adj v j then 1 else 0) := by
    intro j
    by_cases h1 : v = j
    · subst h1; simp
    · by_cases h2 : G.Adj v j <;> simp [h1, h2, SimpleGraph.compl_adj]
  rw [sum_congr rfl fun j _ => this j, sum_sub_distrib, sum_sub_distrib]
  simp

theorem lap_compl (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Gᶜ.lapMatrix ℝ = (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) - vecMulVec one one - G.lapMatrix ℝ := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply]
  rw [lap_apply, lap_apply, degree_compl_real]
  simp only [Matrix.one_apply, vecMulVec_apply, one, SimpleGraph.compl_adj, smul_eq_mul]
  by_cases h : i = j
  · subst h; simp
  · by_cases h2 : G.Adj i j <;> simp [h, h2]

theorem trace_lap (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (G.lapMatrix ℝ).trace = ∑ v, (G.degree v : ℝ) := by
  simp [Matrix.trace, lap_apply]

theorem topSum_full (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) (hk : n ≤ k) :
    topSum (G.isHermitian_lapMatrix ℝ) k = ∑ v, (G.degree v : ℝ) := by
  rw [← topProj_trace_mul, ← trace_lap]
  have : topProj (G.isHermitian_lapMatrix ℝ) k = 1 := by
    unfold topProj TopK.projS
    rw [← PartA.sum_vecMulVec (G.isHermitian_lapMatrix ℝ)]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, iff_true]
    have := i.2; simp only [Fintype.card_fin] at this; omega
  rw [this, Matrix.one_mul]

theorem Dk_full (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) (hk : n ≤ k) :
    Dk G k = ∑ v, (G.degree v : ℝ) := by
  unfold Dk
  refine sum_congr rfl fun v _ => ?_
  have := G.degree_lt_card_verts v
  simp only [Fintype.card_fin] at this
  rw [min_eq_left (by omega)]

theorem lap_mulVec_one (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    G.lapMatrix ℝ *ᵥ one = 0 := SimpleGraph.lapMatrix_mulVec_const_eq_zero G

theorem one_vecMul_lap (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    one ᵥ* G.lapMatrix ℝ = 0 := by
  rw [← Matrix.mulVec_transpose, (G.isSymm_lapMatrix (R := ℝ)).eq, lap_mulVec_one]

theorem one_dot_one : (one : Fin n → ℝ) ⬝ᵥ one = n := by simp [one, dotProduct]

/-- the main trace identity: for `Q` symmetric with `Q 𝟙 = 0`, the projection
`1 - Q - J/n` against `L(Gᶜ)`. -/
theorem trace_compl (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ1 : Q *ᵥ one = 0) :
    ((1 - Q - ((1 : ℝ) / n) • vecMulVec one one) * Gᶜ.lapMatrix ℝ).trace
      = ∑ v, (Gᶜ.degree v : ℝ) - n * Q.trace + (Q * G.lapMatrix ℝ).trace := by
  have hK : vecMulVec one one * Gᶜ.lapMatrix ℝ = 0 := by
    rw [vecMulVec_mul, one_vecMul_lap]; ext; simp [vecMulVec_apply]
  have hQJ : Q * vecMulVec one one = 0 := by
    rw [mul_vecMulVec, hQ1]; ext; simp [vecMulVec_apply]
  have hQL : Q * Gᶜ.lapMatrix ℝ = (n : ℝ) • Q - Q * G.lapMatrix ℝ := by
    rw [lap_compl, mul_sub, mul_sub, hQJ, Matrix.mul_smul, Matrix.mul_one, sub_zero]
  rw [sub_mul, sub_mul, Matrix.one_mul, Matrix.smul_mul, hK, smul_zero, sub_zero, hQL,
    trace_sub, trace_sub, trace_smul, trace_lap, smul_eq_mul]
  ring

theorem proj_compl_symm (Q : Matrix (Fin n) (Fin n) ℝ) (hQs : Qᵀ = Q) :
    (1 - Q - ((1 : ℝ) / n) • vecMulVec one one)ᵀ = 1 - Q - ((1 : ℝ) / n) • vecMulVec one one := by
  rw [transpose_sub, transpose_sub, transpose_one, hQs, transpose_smul, transpose_vecMulVec]

theorem proj_compl_idem (hn : n ≠ 0) (Q : Matrix (Fin n) (Fin n) ℝ) (hQs : Qᵀ = Q)
    (hQQ : Q * Q = Q) (hQ1 : Q *ᵥ one = 0) :
    (1 - Q - ((1 : ℝ) / n) • vecMulVec one one) * (1 - Q - ((1 : ℝ) / n) • vecMulVec one one)
      = 1 - Q - ((1 : ℝ) / n) • vecMulVec one one := by
  set K := ((1 : ℝ) / n) • vecMulVec (one : Fin n → ℝ) one
  have hQK : Q * K = 0 := by
    simp only [K, Matrix.mul_smul, mul_vecMulVec, hQ1]; ext; simp [vecMulVec_apply]
  have hKQ : K * Q = 0 := by
    have : one ᵥ* Q = 0 := by rw [← Matrix.mulVec_transpose, hQs, hQ1]
    simp only [K, Matrix.smul_mul, vecMulVec_mul, this]; ext; simp [vecMulVec_apply]
  have hKK : K * K = K := by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    ext i j
    simp [K, Matrix.mul_apply, vecMulVec_apply, one]
    field_simp
  have : (1 - Q - K) * (1 - Q - K) = 1 - Q - K - Q + Q * Q + Q * K - K + K * Q + K * K := by
    noncomm_ring
  rw [this, hQQ, hQK, hKQ, hKK]; abel

theorem proj_compl_trace (hn : n ≠ 0) (Q : Matrix (Fin n) (Fin n) ℝ) :
    (1 - Q - ((1 : ℝ) / n) • vecMulVec one one).trace = n - Q.trace - 1 := by
  rw [trace_sub, trace_sub, trace_one, trace_smul, trace_vecMulVec, one_dot_one]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [Fintype.card_fin, smul_eq_mul]
  field_simp

/-! Part D: the split-graph contradiction (Bai §4, the cases `N < k`, `N = k`, `N > k`). -/
/-- an index into the eigenvalue list -/
def idx (j : ℕ) (hj : j < n) : Fin (Fintype.card (Fin n)) := ⟨j, by simpa using hj⟩

@[simp] theorem idx_val (j : ℕ) (hj : j < n) : (idx j hj).val = j := rfl

theorem kerOne_mem (x : Fin n → ℝ) :
    x ∈ LinearMap.ker (Matrix.mulVecLin (Matrix.of fun (_ : Fin 1) (_ : Fin n) => (1 : ℝ))) ↔
      one ⬝ᵥ x = 0 := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro h
    have := congrFun h 0
    exact (by simpa [mulVec] using this : (fun _ => (1 : ℝ)) ⬝ᵥ x = 0)
  · intro h
    funext j
    have h' : (fun _ => (1 : ℝ)) ⬝ᵥ x = 0 := h
    simpa [mulVec] using h'

theorem kerOne_finrank :
    n ≤ Module.finrank ℝ
      (LinearMap.ker (Matrix.mulVecLin (Matrix.of fun (_ : Fin 1) (_ : Fin n) => (1 : ℝ)))) + 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (Matrix.mulVecLin (Matrix.of fun (_ : Fin 1) (_ : Fin n) => (1 : ℝ)))
  have h2 := Submodule.finrank_le (LinearMap.range
    (Matrix.mulVecLin (Matrix.of fun (_ : Fin 1) (_ : Fin n) => (1 : ℝ))))
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h h2
  omega

theorem finrank_inf_ge (W W' : Submodule ℝ (Fin n → ℝ)) :
    Module.finrank ℝ W + Module.finrank ℝ W' ≤ Module.finrank ℝ (W ⊓ W' : Submodule ℝ _) + n := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W W'
  have h2 := Submodule.finrank_le (W ⊔ W')
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
  omega

/-- the eigenvalue estimate for the complement -/
theorem compl_eig (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (j i : Fin (Fintype.card (Fin n))) (hji : j.val + i.val + 2 = n) :
    (n : ℝ) - (H.isHermitian_lapMatrix ℝ).eigenvalues₀ j
      ≤ (Hᶜ.isHermitian_lapMatrix ℝ).eigenvalues₀ i := by
  set hL := H.isHermitian_lapMatrix ℝ
  refine PartA.le_eigenvalue_of_subspace _ (PartA.kerT hL (Iio j) ⊓ LinearMap.ker
    (Matrix.mulVecLin (Matrix.of fun (_ : Fin 1) (_ : Fin n) => (1 : ℝ)))) i ?_ _ fun x hx => ?_
  · have h1 := PartA.finrank_kerT hL (Iio j)
    have h2 := kerOne_finrank (n := n)
    have h3 := finrank_inf_ge (PartA.kerT hL (Iio j)) (LinearMap.ker
      (Matrix.mulVecLin (Matrix.of fun (_ : Fin 1) (_ : Fin n) => (1 : ℝ))))
    rw [Fin.card_Iio] at h1
    omega
  · rw [Submodule.mem_inf] at hx
    have hx1 := (PartA.mem_kerT hL _ x).1 hx.1
    have hx2 := (kerOne_mem x).1 hx.2
    have hq := PartA.quad_le_of_low hL j x fun l hl => hx1 l (mem_Iio.2 hl)
    rw [lap_compl, sub_mulVec, sub_mulVec, dotProduct_sub, dotProduct_sub, smul_mulVec,
      one_mulVec, dotProduct_smul, vecMulVec_mulVec, hx2]
    simp only [MulOpposite.op_zero, zero_smul, dotProduct_zero, sub_zero, smul_eq_mul]
    unfold TopK.ev at hq
    linarith

theorem filter_deg_sub (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (C : Finset (Fin n))
    (j : ℕ) (hS : ∀ s ∉ C, H.degree s < j) :
    (#(univ.filter (fun v => j ≤ H.degree v)) : ℝ) ≤ #C := by
  have : univ.filter (fun v => j ≤ H.degree v) ⊆ C := by
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    by_contra h
    have := hS v h; omega
  exact_mod_cast card_le_card this

theorem Dk_compl (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (N : ℕ) (hN1 : 1 ≤ N)
    (hNn : N ≤ n) :
    Dk Hᶜ (n - N) = ∑ v, (Hᶜ.degree v : ℝ) - n * (N - 1) + Dk H (N - 1) := by
  unfold Dk
  have hc1 : ((n - N : ℕ) : ℝ) = n - N := by push_cast [hNn]; ring
  have hc2 : ((N - 1 : ℕ) : ℝ) = N - 1 := by push_cast [hN1]; ring
  have key : ∀ v, (((min (Hᶜ.degree v) (n - N)) : ℕ) : ℝ)
      = (Hᶜ.degree v : ℝ) - (N - 1) + ((min (H.degree v) (N - 1) : ℕ) : ℝ) := by
    intro v
    rw [Nat.cast_min, Nat.cast_min, hc1, hc2, degree_compl_real]
    rcases le_total (H.degree v : ℝ) (N - 1) with h | h
    · rw [min_eq_right (by linarith), min_eq_left h]; ring
    · rw [min_eq_left (by linarith), min_eq_right h]; ring
  rw [sum_congr rfl fun v _ => key v, sum_add_distrib, sum_sub_distrib]
  simp; ring

/-- the complement step: the excess at `N - 1` transfers to the complement at `n - N`. -/
theorem compl_excess (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (N : ℕ) (hN1 : 1 ≤ N)
    (hNn : N ≤ n)
    (hpos : ∀ i : Fin (Fintype.card (Fin n)), i.val < N - 1 →
      (H.isHermitian_lapMatrix ℝ).eigenvalues₀ i ≠ 0) :
    topSum (H.isHermitian_lapMatrix ℝ) (N - 1) - Dk H (N - 1)
      ≤ topSum (Hᶜ.isHermitian_lapMatrix ℝ) (n - N) - Dk Hᶜ (n - N) := by
  have hn : n ≠ 0 := by omega
  set hL := H.isHermitian_lapMatrix ℝ
  set Q := topProj hL (N - 1)
  have hQs := topProj_transpose hL (N - 1)
  have hQQ := topProj_idem hL (N - 1)
  have hQt : Q.trace = ((N - 1 : ℕ) : ℝ) := topProj_trace hL (by omega)
  have hQ1 : Q *ᵥ one = 0 := topProj_mulVec_one hL (N - 1) (lap_mulVec_one H) hpos
  have hPt : (1 - Q - ((1 : ℝ) / n) • vecMulVec one one).trace = ((n - N : ℕ) : ℝ) := by
    rw [proj_compl_trace hn, hQt]
    push_cast [hNn, hN1]; ring
  have hKF := trace_mul_le_topSum (Hᶜ.isHermitian_lapMatrix ℝ) (proj_compl_symm Q hQs)
    (proj_compl_idem hn Q hQs hQQ hQ1) hPt
  rw [trace_compl H Q hQ1, hQt, topProj_trace_mul] at hKF
  rw [Dk_compl H N hN1 hNn]
  have hc2 : ((N - 1 : ℕ) : ℝ) = N - 1 := by push_cast [hN1]; ring
  rw [hc2] at hKF
  linarith

/-! Part D: a split graph cannot be a minimal counterexample (Bai §4). -/
theorem split_contra (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (C : Finset (Fin n))
    (hs : IsSplitWith H C) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n)
    (hS : ∀ s ∉ C, H.degree s < k)
    (hT : Dk H k < topSum (H.isHermitian_lapMatrix ℝ) k)
    (he : ∀ i : Fin (Fintype.card (Fin n)), i.val + 1 = k →
      (#C : ℝ) < (H.isHermitian_lapMatrix ℝ).eigenvalues₀ i) : False := by
  have hNn : #C ≤ n := by simpa using card_le_univ C
  rcases lt_trichotomy #C k with hlt | heq | hgt
  · -- `N < k`
    have h1 := prop5_upper H C hs (#C) (fun s hs' => by exact_mod_cast degree_le_of_split H C hs s hs')
      ⟨k - 1, by simp; omega⟩ (by simp; omega)
    have h2 := he ⟨k - 1, by simp; omega⟩ (by simp; omega)
    linarith
  · -- `N = k`
    have h1 := lemma6 H C hs (fun i hi => Or.inl (he i (by omega)))
    rw [heq] at h1
    unfold Dk at hT
    linarith
  · -- `N > k`
    have hlow : ∀ j (hj : j + 2 ≤ #C),
        (#C : ℝ) ≤ (H.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨j, by simp; omega⟩ :=
      fun j hj => prop5_lower H C hs ⟨j, by simp; omega⟩ hj
    have step : ∀ d, k + d ≤ #C - 1 →
        Dk H (k + d) < topSum (H.isHermitian_lapMatrix ℝ) (k + d) := by
      intro d
      induction d with
      | zero => intro _; simpa using hT
      | succ d ih =>
        intro hd
        have h0 := ih (by omega)
        rw [← add_assoc, topSum_succ _ (k + d) (by simp; omega), Dk_succ]
        have h1 := hlow (k + d) (by omega)
        have h2 := filter_deg_sub H C (k + d + 1) (fun s hs' => by have := hS s hs'; omega)
        linarith
    have hN1 : Dk H (#C - 1) < topSum (H.isHermitian_lapMatrix ℝ) (#C - 1) := by
      have := step (#C - 1 - k) (by omega)
      rwa [show k + (#C - 1 - k) = #C - 1 by omega] at this
    rcases le_or_gt (#C : ℝ) ((H.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨#C - 1, by simp; omega⟩)
      with hge | hlt'
    · have h1 : topSum (H.isHermitian_lapMatrix ℝ) #C = topSum (H.isHermitian_lapMatrix ℝ) (#C - 1)
          + (H.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨#C - 1, by simp; omega⟩ := by
        rw [← topSum_succ _ (#C - 1) (by simp; omega), Nat.sub_add_cancel (by omega)]
      have h2 : Dk H #C ≤ Dk H (#C - 1) + #C := by
        have := Dk_succ H (#C - 1)
        rw [Nat.sub_add_cancel (by omega)] at this
        have h3 := filter_deg_sub H C #C (fun s hs' => by have := hS s hs'; omega)
        linarith
      have h3 := lemma6 H C hs (fun i hi => by
        have hi' : i = ⟨#C - 1, by simp; omega⟩ := Fin.ext (by simp; omega)
        rw [hi']
        rcases hge.lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.symm, fun s hs' => by have := hS s hs'; omega⟩)
      unfold Dk at h2 hN1
      linarith
    · -- the complement
      have hpos : ∀ i : Fin (Fintype.card (Fin n)), i.val < #C - 1 →
          (H.isHermitian_lapMatrix ℝ).eigenvalues₀ i ≠ 0 := by
        intro i hi
        have := hlow i.val (by omega)
        have hC : (0 : ℝ) < #C := by exact_mod_cast (show 0 < #C by omega)
        exact ne_of_gt (lt_of_lt_of_le hC this)
      have hx := compl_excess H #C (by omega) hNn hpos
      have hcC : #Cᶜ = n - #C := by rw [card_compl, Fintype.card_fin]
      have h3 := lemma6 Hᶜ Cᶜ (split_compl H C hs) (fun i hi => Or.inl (by
        rw [hcC] at hi ⊢
        have := compl_eig H ⟨#C - 1, by simp; omega⟩ i (by simp; omega)
        have hc : ((n - #C : ℕ) : ℝ) = n - #C := by push_cast [hNn]; ring
        rw [hc]
        linarith))
      rw [hcC] at h3
      unfold Dk at hx hN1
      linarith

theorem gm_main (k : ℕ) : ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    topSum (G.isHermitian_lapMatrix ℝ) k ≤ Dk G k := by
  induction k using Nat.strong_induction_on with
  | _ k IHk =>
  suffices h : ∀ s, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∑ w, G.degree w = s →
      topSum (G.isHermitian_lapMatrix ℝ) k ≤ Dk G k by
    intro G _; exact h _ G rfl
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IHs =>
  intro G _ hGs
  have IHe : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj],
      ∑ w, G'.degree w < ∑ w, G.degree w → topSum (G'.isHermitian_lapMatrix ℝ) k ≤ Dk G' k :=
    fun G' _ h => IHs _ (hGs ▸ h) G' rfl
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0; rw [topSum_zero]; exact Dk_nonneg G 0
  rcases le_or_gt n k with hkn | hkn
  · rw [topSum_full G k hkn, Dk_full G k hkn]
  by_contra hcon
  push_neg at hcon
  -- the step from `k - 1`
  have hprev := IHk (k - 1) (by omega) G
  have hts := topSum_succ (G.isHermitian_lapMatrix ℝ) (k - 1) (by simp; omega)
  have hds := Dk_succ G (k - 1)
  rw [Nat.sub_add_cancel hk1] at hts hds
  -- Lemma 13
  have hstar : ∀ u v, G.Adj u v → G.degree u < k → k ≤ G.degree v := by
    intro u v huv hu
    by_contra hv
    push_neg at hv
    have := lemma13 k hkn.le G huv hu.le hv.le IHe
    linarith
  set C := bigC G k with hC
  have hsplit := addClique_split G k hstar
  have hmono : ∀ x, x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) ≤ x ⬝ᵥ ((addClique G C).lapMatrix ℝ *ᵥ x) :=
    quad_lap_mono G (addClique G C) (fun a b h => Or.inl h)
  have hev := eigenvalue_mono (G.isHermitian_lapMatrix ℝ)
    ((addClique G C).isHermitian_lapMatrix ℝ) hmono
  have hcard : (#C : ℝ) = (#(univ.filter (fun v => k ≤ G.degree v)) : ℝ) := rfl
  refine split_contra (addClique G C) C hsplit k hk1 hkn ?_ ?_ ?_
  · intro s hs
    rw [addClique_degree_out G k hstar s hs]
    rw [hC, mem_bigC] at hs; omega
  · rw [addClique_Dk G k hstar]
    exact lt_of_lt_of_le hcon (topSum_mono _ _ hev k)
  · intro i hi
    have hi' : i = ⟨k - 1, by simp; omega⟩ := Fin.ext (by simp; omega)
    rw [hi']
    refine lt_of_lt_of_le ?_ (hev _)
    rw [hcard]
    linarith

theorem gm_fin (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    topSum (G.isHermitian_lapMatrix ℝ) k ≤ ∑ v, ((min (G.degree v) k : ℕ) : ℝ) :=
  gm_main k G

end BrouwerLaplacian.Dev.GMB.PartD
end

section
namespace BrouwerLaplacian.Dev.GMB
open Finset Matrix BrouwerLaplacian
variable {n : ℕ}
/-! ### Part D: the Grone–Merris inequality (Bai §4) -/
alias gm_fin := BrouwerLaplacian.Dev.GMB.PartD.gm_fin

end BrouwerLaplacian.Dev.GMB
end

section
namespace BrouwerLaplacian.Dev.GMB.PartZ
open Finset Matrix BrouwerLaplacian BrouwerLaplacian.Dev.GMB
/-! Transfer of `gm_fin` (graphs on `Fin n`, `Σ min(deg, k)`) to the published statement. -/
theorem conjDeg_comap {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (e : Fin n ≃ V) (j : ℕ) :
    conjDeg (G.comap e) j = conjDeg G j := by
  unfold conjDeg
  have hdeg : ∀ a, (G.comap e).degree a = G.degree (e a) := fun a =>
    ((SimpleGraph.Iso.comap e G).degree_eq a).symm
  simp only [hdeg]
  exact Finset.card_bij (fun a _ => e a) (by simp) (fun a _ b _ h => e.injective h)
    (fun b hb => ⟨e.symm b, by
      have h := e.apply_symm_apply b
      simp only [mem_filter, mem_univ, true_and] at hb ⊢
      rw [h]; exact hb, by simp⟩)

theorem main {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    ∑ i : Fin (Fintype.card V) with i.val < k, (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i
      ≤ ∑ j ∈ Icc 1 k, (conjDeg G j : ℝ) := by
  set e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  rw [Transfer.eig_sum_graph G e k]
  have h1 : ∑ j ∈ Icc 1 k, (conjDeg G j : ℝ) = ∑ j ∈ Icc 1 k, (conjDeg (G.comap e) j : ℝ) := by
    refine sum_congr rfl fun j _ => ?_
    rw [conjDeg_comap]
  rw [h1, Split32.conj_sum]
  have := gm_fin (G.comap e) k
  unfold topSum at this
  push_cast at this ⊢
  exact this

end BrouwerLaplacian.Dev.GMB.PartZ
end

section
namespace BrouwerLaplacian
open Finset
theorem chk_theorem_1_2_grone_merris_bai {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    ∑ i : Fin (Fintype.card V) with i.val < k, (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i
      ≤ ∑ j ∈ Icc 1 k, (conjDeg G j : ℝ) :=
  Dev.GMB.PartZ.main G k

end BrouwerLaplacian
end

theorem solution : type_of% @BrouwerLaplacian.chk_theorem_1_2_grone_merris_bai := @BrouwerLaplacian.chk_theorem_1_2_grone_merris_bai
