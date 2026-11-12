-- Prove2me | solution 1 for BrouwerLaplacian.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:07:53.293068+00:00
-- url     : https://prove2.me/submissions/2759c90c-7928-4108-ae1a-e3db44326f4d

import Mathlib
import Definitions.Def_BrouwerLaplacian_IsOrthProj
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_BrouwerLaplacian_centering
import Definitions.Def_BrouwerLaplacian_routingM
import Definitions.Def_BrouwerLaplacian_splitGraphOf

section
namespace BrouwerLaplacian.Dev.Common

open Matrix

theorem trace_eq_rank {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P * P = P) (hk : P.rank = k) :
    P.trace = k := by
  have hproj : LinearMap.IsProj (LinearMap.range (Matrix.toLin' P)) (Matrix.toLin' P) := by
    have : IsIdempotentElem (Matrix.toLin' P) := by
      show Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
    exact (LinearMap.isProj_range_iff_isIdempotentElem _).2 this
  have h := hproj.trace
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin n)), LinearMap.toMatrix_eq_toMatrix'] at h
  rw [LinearMap.toMatrix'_toLin'] at h
  rw [h]
  have : P.rank = Module.finrank ℝ (LinearMap.range (Matrix.toLin' P)) := by
    rw [Matrix.rank]; rfl
  rw [← this, hk]

end BrouwerLaplacian.Dev.Common
end

section
namespace BrouwerLaplacian.Dev.L52

open Finset Matrix

end BrouwerLaplacian.Dev.L52

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.OpN

open Matrix WainwrightHDS.NucNorm

end BrouwerLaplacian.Dev.OpN
end

section
namespace BrouwerLaplacian.Dev.NLem

open Finset Matrix BrouwerLaplacian

end BrouwerLaplacian.Dev.NLem

namespace BrouwerLaplacian
open Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.L56

open Finset Matrix BrouwerLaplacian

theorem sum_ne {n : ℕ} (g : Fin n → Fin n → ℝ) (h : ∀ i, g i i = 0) :
    ∑ i, ∑ j with i ≠ j, g i j = ∑ i, ∑ j, g i j := by
  refine sum_congr rfl fun i _ => ?_
  rw [sum_filter]
  refine sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · subst hij; simp [h]
  · simp [hij]

end BrouwerLaplacian.Dev.L56

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.L53

open Finset Matrix BrouwerLaplacian

theorem half_sum {n : ℕ} (g : Fin n → Fin n → ℝ) (hg : ∀ i j, g i j = g j i) :
    ∑ i, ∑ j with i ≠ j, g i j = 2 * ∑ i, ∑ j with i < j, g i j := by
  have h1 : ∀ i, ∑ j with i ≠ j, g i j
      = ∑ j with i < j, g i j + ∑ j with j < i, g i j := by
    intro i
    have : (univ.filter fun j => i ≠ j) = (univ.filter fun j => i < j) ∪ (univ.filter fun j => j < i) := by
      ext j
      simp only [mem_filter, mem_union, mem_univ, true_and]
      constructor
      · intro h; exact lt_or_gt_of_ne h
      · rintro (h | h)
        · exact ne_of_lt h
        · exact ne_of_gt h
    rw [this, sum_union]
    rw [disjoint_filter]; intro j _ h1 h2; exact absurd h1 (not_lt.2 h2.le)
  simp only [h1, sum_add_distrib]
  have h2 : ∑ i, ∑ j with j < i, g i j = ∑ i, ∑ j with i < j, g i j := by
    simp only [sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [hg]
  rw [h2]; ring

end BrouwerLaplacian.Dev.L53

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.E53

open Finset Matrix BrouwerLaplacian

theorem trace_mul_sum {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A * B).trace = ∑ i, ∑ j, A i j * B j i := by
  simp [Matrix.trace, Matrix.mul_apply]

end BrouwerLaplacian.Dev.E53

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.Reflect

open Finset Matrix BrouwerLaplacian

/-- the Householder reflection `H = 1 - (2/(w⬝w)) w wᵀ` -/
noncomputable def hh {n : ℕ} (w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - (2 / (w ⬝ᵥ w)) • vecMulVec w w

theorem hh_symm {n : ℕ} (w : Fin n → ℝ) : (hh w)ᵀ = hh w := by
  ext i j
  simp [hh, Matrix.transpose_apply, Matrix.one_apply, vecMulVec_apply, eq_comm, mul_comm]

theorem vv_sq {n : ℕ} (w : Fin n → ℝ) :
    vecMulVec w w * vecMulVec w w = (w ⬝ᵥ w) • vecMulVec w w := by
  ext i j
  simp [Matrix.mul_apply, vecMulVec_apply, dotProduct, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => by ring

theorem hh_mul_self {n : ℕ} (w : Fin n → ℝ) (hw : w ⬝ᵥ w ≠ 0) : hh w * hh w = 1 := by
  unfold hh
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, vv_sq]
  ext i j
  simp [Matrix.sub_apply, Matrix.smul_apply]
  field_simp
  ring

theorem hh_mulVec {n : ℕ} (w x : Fin n → ℝ) :
    hh w *ᵥ x = x - ((2 / (w ⬝ᵥ w)) * (w ⬝ᵥ x)) • w := by
  simp only [hh, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec]
  ext i
  simp [mul_assoc]

theorem hh_mul_of_mulVec_zero {n : ℕ} (w : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Aᵀ = A) (hw : A *ᵥ w = 0) : hh w * A = A ∧ A * hh w = A := by
  constructor
  · unfold hh
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, vecMulVec_mul]
    have : w ᵥ* A = 0 := by
      have := Matrix.vecMul_transpose A w
      rw [hA] at this; rw [this]; exact hw
    simp [this]
  · unfold hh
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, mul_vecMulVec, hw]
    simp

theorem reflect {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (z u : Fin n → ℝ) (hz : z ⬝ᵥ z = 1)
    (hu : u ⬝ᵥ u = 1) (hPz : P *ᵥ z = 0) (hAz : A *ᵥ z = 0) (hAu : A *ᵥ u = 0) :
    ∃ P' : Matrix (Fin n) (Fin n) ℝ, IsOrthProj P' k ∧ P' *ᵥ u = 0 ∧ (P' * A).trace = (P * A).trace := by
  by_cases hw : (z - u) ⬝ᵥ (z - u) = 0
  · have : z = u := by
      have := (dotProduct_self_eq_zero (v := z - u)).1 hw
      exact sub_eq_zero.1 this
    subst this
    exact ⟨P, hP, hPz, rfl⟩
  set w := z - u with hwdef
  set H := hh w with hHdef
  have hHs : Hᵀ = H := hh_symm w
  have hHH : H * H = 1 := hh_mul_self w hw
  have hAw : A *ᵥ w = 0 := by rw [hwdef, Matrix.mulVec_sub, hAz, hAu, sub_zero]
  obtain ⟨hHA, hAH⟩ := hh_mul_of_mulVec_zero w A hA hAw
  have hPt : Pᵀ = P := by
    have := hP.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hHu : H *ᵥ u = z := by
    rw [hHdef, hh_mulVec]
    have h1 : w ⬝ᵥ u = z ⬝ᵥ u - 1 := by rw [hwdef, sub_dotProduct, hu]
    have h2 : w ⬝ᵥ w = 2 - 2 * (z ⬝ᵥ u) := by
      rw [hwdef, dotProduct_sub, sub_dotProduct, sub_dotProduct, hz, hu, dotProduct_comm u z]; ring
    have h4 : (2 - 2 * (z ⬝ᵥ u)) ≠ 0 := by rw [← h2]; exact hw
    have h3 : (2 / (w ⬝ᵥ w)) * (w ⬝ᵥ u) = -1 := by
      have h5 : 1 - z ⬝ᵥ u ≠ 0 := fun h => h4 (by linarith)
      rw [h1, h2]
      field_simp
      ring
    rw [h3, hwdef]; ext i; simp
  have hunit : IsUnit H.det := Matrix.isUnit_det_of_right_inverse hHH
  refine ⟨H * P * H, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    simp only [Matrix.transpose_mul, hHs, hPt, Matrix.mul_assoc]
  · calc H * P * H * (H * P * H) = H * (P * (H * H) * P) * H := by simp only [Matrix.mul_assoc]
      _ = H * P * H := by rw [hHH, Matrix.mul_one, hP.2.1, Matrix.mul_assoc]
  · rw [Matrix.rank_mul_eq_left_of_isUnit_det H (H * P) hunit,
      Matrix.rank_mul_eq_right_of_isUnit_det H P hunit]
    exact hP.2.2
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hHu, hPz, Matrix.mulVec_zero]
  · have : H * P * H * A = H * P * (H * A) := by simp only [Matrix.mul_assoc]
    rw [this, hHA, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hAH, Matrix.trace_mul_comm]

end BrouwerLaplacian.Dev.Reflect
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

theorem projS_isOrthProj (hA : A.IsHermitian) (S : Finset (Fin (Fintype.card (Fin n)))) :
    IsOrthProj (projS hA S) S.card := by
  have hidem := projS_idem hA S
  refine ⟨?_, hidem, ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact projS_symm hA S
  · have h := Common.trace_eq_rank (projS hA S) hidem rfl
    rw [projS_trace] at h
    exact_mod_cast h.symm

end BrouwerLaplacian.Dev.TopK
end

section
namespace BrouwerLaplacian.Dev.L51a

open Finset Matrix BrouwerLaplacian

theorem lap_trace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Matrix (Fin n) (Fin n) ℝ) (hs : ∀ i j, P j i = P i j) :
    (P * G.lapMatrix ℝ).trace
      = ∑ i, ∑ j with i < j ∧ G.Adj i j, (P i i + P j j - 2 * P i j) := by
  rw [E53.trace_mul_sum]
  have hdeg : ∀ i, (G.degree i : ℝ) = ∑ j, if G.Adj i j then (1 : ℝ) else 0 := by
    intro i
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    simp [sum_boole]
  have h1 : ∑ i, ∑ j, P i j * G.lapMatrix ℝ j i
      = ∑ i, ∑ j, (if G.Adj i j then (P i i - P i j) else 0) := by
    have : ∀ i j, P i j * G.lapMatrix ℝ j i
        = (if j = i then P i j * (G.degree j : ℝ) else 0) - (if G.Adj i j then P i j else 0) := by
      intro i j
      by_cases hij : j = i
      · subst hij; simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix]
      · have : ¬ i = j := fun h => hij h.symm
        simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, hij, this, G.adj_comm]
    have h2 : ∀ i, ∑ j, (if G.Adj i j then (P i i - P i j) else 0)
        = P i i * (G.degree i : ℝ) - ∑ j, (if G.Adj i j then P i j else 0) := by
      intro i
      rw [hdeg i, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    simp only [this, h2, sum_sub_distrib, sum_ite_eq', mem_univ, if_true]
  set f : Fin n → Fin n → ℝ := fun i j => if G.Adj i j then (P i i + P j j - 2 * P i j) else 0
    with hf
  have hfs : ∀ i j, f i j = f j i := by
    intro i j
    simp only [hf, G.adj_comm i j, hs i j]
    split_ifs <;> ring
  have hfd : ∀ i, f i i = 0 := fun i => by simp [hf]
  have h3 : ∑ i, ∑ j, f i j = 2 * ∑ i, ∑ j, (if G.Adj i j then (P i i - P i j) else 0) := by
    have : ∀ i j, f i j = (if G.Adj i j then (P i i - P i j) else 0)
        + (if G.Adj j i then (P j j - P j i) else 0) := by
      intro i j
      simp only [hf, G.adj_comm j i, hs i j]
      split_ifs <;> ring
    simp only [this, sum_add_distrib]
    rw [sum_comm (f := fun i j => if G.Adj j i then (P j j - P j i) else 0)]
    ring
  have h4 := L53.half_sum f hfs
  rw [L56.sum_ne f hfd] at h4
  rw [h1]
  have h5 : ∀ i, ∑ j with i < j, f i j = ∑ j with i < j ∧ G.Adj i j, (P i i + P j j - 2 * P i j) := by
    intro i
    rw [sum_filter, sum_filter]
    refine sum_congr rfl fun j _ => ?_
    simp only [hf]
    by_cases h1 : i < j <;> by_cases h2 : G.Adj i j <;> simp [h1, h2]
  simp only [h5] at h4
  linarith

theorem edge_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (#G.edgeFinset : ℝ) = ∑ i, ∑ j with i < j ∧ G.Adj i j, (1 : ℝ) := by
  have hdeg : ∀ i, (G.degree i : ℝ) = ∑ j, if G.Adj i j then (1 : ℝ) else 0 := by
    intro i
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    simp [sum_boole]
  have h1 : ∑ i, (G.degree i : ℝ) = 2 * (#G.edgeFinset : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  set g : Fin n → Fin n → ℝ := fun i j => if G.Adj i j then (1 : ℝ) else 0 with hg
  have hgs : ∀ i j, g i j = g j i := fun i j => by simp only [hg, G.adj_comm i j]
  have hgd : ∀ i, g i i = 0 := fun i => by simp [hg]
  have h4 := L53.half_sum g hgs
  rw [L56.sum_ne g hgd] at h4
  have hgi : ∀ i, ∑ j, g i j = (G.degree i : ℝ) := fun i => (hdeg i).symm
  simp only [hgi] at h4
  have h5 : ∀ i, ∑ j with i < j, g i j = ∑ j with i < j ∧ G.Adj i j, (1 : ℝ) := by
    intro i
    rw [sum_filter, sum_filter]
    refine sum_congr rfl fun j _ => ?_
    simp only [hg]
    by_cases h1 : i < j <;> by_cases h2 : G.Adj i j <;> simp [h1, h2]
  simp only [h5] at h4
  linarith

end BrouwerLaplacian.Dev.L51a
end

section
namespace BrouwerLaplacian.Dev.L51

open Finset Matrix BrouwerLaplacian

theorem lap_ev_last {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hn : 1 ≤ n)
    (j : Fin (Fintype.card (Fin n))) (hj : j.val + 1 = Fintype.card (Fin n)) :
    TopK.ev (G.isHermitian_lapMatrix ℝ) j = 0 := by
  set hA := G.isHermitian_lapMatrix ℝ with hAdef
  have hpsd := G.posSemidef_lapMatrix ℝ
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  have hnn : ∀ i : Fin (Fintype.card (Fin n)), 0 ≤ TopK.ev hA i := by
    intro i
    have := hpsd.eigenvalues_nonneg (e i)
    simpa [Matrix.IsHermitian.eigenvalues, TopK.ev, e] using this
  have hex : ∃ i : Fin (Fintype.card (Fin n)), TopK.ev hA i = 0 := by
    have hdet : (G.lapMatrix ℝ).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨fun _ => 1, ?_, G.lapMatrix_mulVec_const_eq_zero⟩
      intro h
      have := congrFun h ⟨0, by omega⟩
      simp at this
    rw [hA.det_eq_prod_eigenvalues] at hdet
    simp only [RCLike.ofReal_real_eq_id, id] at hdet
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 hdet
    refine ⟨e.symm i, ?_⟩
    simpa [Matrix.IsHermitian.eigenvalues, TopK.ev, e] using hi
  obtain ⟨i, hi⟩ := hex
  have hle : TopK.ev hA j ≤ TopK.ev hA i := by
    apply hA.eigenvalues₀_antitone
    rw [Fin.le_def]; omega
  linarith [hnn j]

theorem main {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (hk1 : 1 ≤ k) (hkn : k ≤ n - 1)
    (hproj : ∀ P : Matrix (Fin n) (Fin n) ℝ, IsOrthProj P k → P *ᵥ (fun _ => 1) = 0 →
      ∑ i, ∑ j with i < j ∧ G.Adj i j, (P i i + P j j - 2 * P i j - 1)
        ≤ ((k + 1).choose 2 : ℕ)) :
    ∑ i : Fin (Fintype.card (Fin n)) with i.val < k, (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i
      ≤ (#G.edgeFinset : ℝ) + ((k + 1).choose 2 : ℕ) := by
  set hA := G.isHermitian_lapMatrix ℝ with hAdef
  have hn2 : 2 ≤ n := by omega
  have hm : Fintype.card (Fin n) = n := Fintype.card_fin n
  set S : Finset (Fin (Fintype.card (Fin n))) := univ.filter (fun i => i.val < k) with hS
  have hScard : S.card = k := by
    rw [hS, Fin.card_filter_val_lt]; omega
  have hP0 : IsOrthProj (TopK.projS hA S) k := hScard ▸ TopK.projS_isOrthProj hA S
  let idx : Fin (Fintype.card (Fin n)) := ⟨n - 1, by omega⟩
  have hidx : idx.val + 1 = Fintype.card (Fin n) := by simp [idx]; omega
  have hz0 : G.lapMatrix ℝ *ᵥ TopK.bv hA idx = 0 := by
    rw [TopK.mulVec_bv, lap_ev_last G (by omega) idx hidx]; simp
  have hzz : TopK.bv hA idx ⬝ᵥ TopK.bv hA idx = 1 := by rw [TopK.bv_dot]; simp
  have hPz : TopK.projS hA S *ᵥ TopK.bv hA idx = 0 := by
    rw [TopK.projS_mulVec]
    have : idx ∉ S := by simp [hS, idx]; omega
    simp [this]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set c : ℝ := 1 / Real.sqrt n with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact one_div_ne_zero (Real.sqrt_ne_zero'.2 hnR)
  have hu : (fun _ : Fin n => c) ⬝ᵥ (fun _ : Fin n => c) = 1 := by
    simp [dotProduct, hc]
    field_simp
    exact (Real.sq_sqrt hnR.le).symm
  have hAu : G.lapMatrix ℝ *ᵥ (fun _ : Fin n => c) = 0 := by
    have : (fun _ : Fin n => c) = c • (fun _ : Fin n => (1 : ℝ)) := by ext; simp
    rw [this, Matrix.mulVec_smul, G.lapMatrix_mulVec_const_eq_zero, smul_zero]
  have hAT : (G.lapMatrix ℝ)ᵀ = G.lapMatrix ℝ := G.isSymm_lapMatrix ℝ
  obtain ⟨P', hP', hP'u, htr⟩ := Reflect.reflect (TopK.projS hA S) hP0 (G.lapMatrix ℝ) hAT _ _ hzz hu
    hPz hz0 hAu
  have hP'1 : P' *ᵥ (fun _ => 1) = 0 := by
    have : (fun _ : Fin n => c) = c • (fun _ : Fin n => (1 : ℝ)) := by ext; simp
    rw [this, Matrix.mulVec_smul] at hP'u
    exact (smul_eq_zero.1 hP'u).resolve_left hc0
  have hP's : ∀ i j, P' j i = P' i j := by
    intro i j
    have := hP'.1.apply i j
    simpa using this
  have hb := hproj P' hP' hP'1
  have h1 := L51a.lap_trace G P' hP's
  have h2 := L51a.edge_count G
  have h3 : ∑ i, ∑ j with i < j ∧ G.Adj i j, (P' i i + P' j j - 2 * P' i j - 1)
      = ∑ i, ∑ j with i < j ∧ G.Adj i j, (P' i i + P' j j - 2 * P' i j)
        - ∑ i, ∑ j with i < j ∧ G.Adj i j, (1 : ℝ) := by
    simp only [← sum_sub_distrib]
  rw [h3, ← h1, ← h2, htr, TopK.projS_trace_A] at hb
  have : ∑ i : Fin (Fintype.card (Fin n)) with i.val < k, hA.eigenvalues₀ i
      = ∑ i ∈ S, TopK.ev hA i := rfl
  rw [this]
  linarith

end BrouwerLaplacian.Dev.L51

namespace BrouwerLaplacian
open Finset Matrix
theorem chk_lemma_5_1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (hk1 : 1 ≤ k) (hkn : k ≤ n - 1)
    (hproj : ∀ P : Matrix (Fin n) (Fin n) ℝ, IsOrthProj P k → P *ᵥ (fun _ => 1) = 0 →
      ∑ i, ∑ j with i < j ∧ G.Adj i j, (P i i + P j j - 2 * P i j - 1)
        ≤ ((k + 1).choose 2 : ℕ)) :
    ∑ i : Fin (Fintype.card (Fin n)) with i.val < k, (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i
      ≤ (#G.edgeFinset : ℝ) + ((k + 1).choose 2 : ℕ) := Dev.L51.main G k hk1 hkn hproj
end BrouwerLaplacian
end

theorem solution : type_of% @BrouwerLaplacian.chk_lemma_5_1 := @BrouwerLaplacian.chk_lemma_5_1
