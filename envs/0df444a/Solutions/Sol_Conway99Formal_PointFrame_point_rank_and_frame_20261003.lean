-- Prove2me | solution 1 for Conway99Formal.PointFrame.point_rank_and_frame_20261003
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T01:24:59.266871+00:00
-- url     : https://prove2.me/submissions/3dbf8831-c631-4c31-b8c9-a4b6130d82b2

import Definitions.Def_Conway99_Point_Gram_20261003

set_option autoImplicit false

/-! A necessary real 44-row point frame for one hypothetical SRG(99,14,1,2),
following `Core.lean` Point.Delta and `FOUNDATIONS.md` §1. -/

namespace Conway99Formal.PointFrame

open Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem complement_matrix (G : SimpleGraph V) [DecidableRel G.Adj] :
    Gᶜ.adjMatrix ℝ = (of 1 : Matrix V V ℝ) - 1 - G.adjMatrix ℝ := by
  have h := G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := ℝ)
  rw [G.compl_adjMatrix_eq_adjMatrix_compl ℝ] at h
  linear_combination (norm := module) h

private theorem adjacency_square {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    G.adjMatrix ℝ * G.adjMatrix ℝ =
      12 • (1 : Matrix V V ℝ) - G.adjMatrix ℝ + 2 • of 1 := by
  have hm := h.matrix_eq (α := ℝ)
  rw [complement_matrix G] at hm
  have hs : G.adjMatrix ℝ * G.adjMatrix ℝ = (G.adjMatrix ℝ) ^ 2 := by rw [sq]
  rw [hs, hm]
  module

private theorem adjacency_mul_ones {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    G.adjMatrix ℝ * (of 1 : Matrix V V ℝ) = 14 • of 1 := by
  ext i j
  have key := G.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := 1) h.regular (v := i)
  simp only [Matrix.mulVec, dotProduct, Function.const, mul_one] at key
  simp only [Matrix.mul_apply, Matrix.of_apply, Pi.one_apply, mul_one, Matrix.smul_apply]
  simpa using key

private theorem ones_mul_adjacency {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (of 1 : Matrix V V ℝ) * G.adjMatrix ℝ = 14 • of 1 := by
  have hJ : ((of 1 : Matrix V V ℝ))ᵀ = of 1 := by ext i j; rfl
  have ht := congrArg Matrix.transpose (adjacency_mul_ones h)
  rw [Matrix.transpose_mul, hJ, SimpleGraph.transpose_adjMatrix,
    Matrix.transpose_smul, hJ] at ht
  exact ht

private theorem ones_square (hcard : Fintype.card V = 99) :
    (of 1 : Matrix V V ℝ) * (of 1 : Matrix V V ℝ) = 99 • of 1 := by
  ext i j
  simp [Matrix.mul_apply, Matrix.of_apply, hcard]

/-- The point Gram matrix is 63 times a real idempotent. -/
theorem Q_square {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) : Q G * Q G = 63 • Q G := by
  simp only [Q, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one, smul_smul,
    adjacency_square h, adjacency_mul_ones h, ones_mul_adjacency h,
    ones_square h.card, smul_add, smul_sub]
  abel

/-- The graph-owned Gram is symmetric. -/
theorem Q_transpose (G : SimpleGraph V) [DecidableRel G.Adj] : (Q G)ᵀ = Q G := by
  have hJ : ((of 1 : Matrix V V ℝ))ᵀ = of 1 := by ext i j; rfl
  simp only [Q, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, SimpleGraph.transpose_adjMatrix, hJ]

/-- The Gram is zero on the all-ones direction. -/
theorem Q_mul_ones {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    Q G * (of 1 : Matrix V V ℝ) = 0 := by
  simp only [Q, add_mul, sub_mul, smul_mul_assoc, one_mul,
    adjacency_mul_ones h, ones_square h.card, smul_smul]
  module

/-- The point Gram lies in the minus-four eigenspace of the same adjacency matrix. -/
theorem adjacency_mul_Q {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    G.adjMatrix ℝ * Q G = -(4 • Q G) := by
  simp only [Q, mul_add, mul_sub, mul_smul_comm, mul_one,
    adjacency_square h, adjacency_mul_ones h, smul_add, smul_sub]
  module

theorem Q_mul_adjacency {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    Q G * G.adjMatrix ℝ = -(4 • Q G) := by
  have ht := congrArg Matrix.transpose (adjacency_mul_Q h)
  rw [Matrix.transpose_mul, Q_transpose,
    SimpleGraph.transpose_adjMatrix, Matrix.transpose_neg,
    Matrix.transpose_smul, Q_transpose] at ht
  exact ht

theorem trace_Q {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) : (Q G).trace = 2772 := by
  simp only [Q, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul]
  have ha : (G.adjMatrix ℝ).trace = 0 := by simp [Matrix.trace, Matrix.diag]
  have hj : (of 1 : Matrix V V ℝ).trace = 99 := by
    simp [Matrix.trace, Matrix.diag, h.card]
  have hi : (1 : Matrix V V ℝ).trace = 99 := by
    rw [Matrix.trace_one, h.card]
    norm_num
  rw [ha, hj, hi]
  norm_num

theorem P_idempotent {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) : P G * P G = P G := by
  simp only [P, Matrix.smul_mul, Matrix.mul_smul, Q_square h,
    ← Nat.cast_smul_eq_nsmul, smul_smul]
  module

theorem P_transpose (G : SimpleGraph V) [DecidableRel G.Adj] : (P G)ᵀ = P G := by
  simp only [P, Matrix.transpose_smul, Q_transpose]

theorem trace_P {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) : (P G).trace = 44 := by
  rw [P, Matrix.trace_smul, trace_Q h, smul_eq_mul]
  norm_num

private theorem idempotent_rank_eq_trace {K n : Type*} [Field K]
    [Fintype n] [DecidableEq n]
    (E : Matrix n n K) (hE : E * E = E) : (E.rank : K) = E.trace := by
  have hidem : IsIdempotentElem E.mulVecLin := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hE]
  have htr := ((LinearMap.isProj_range_iff_isIdempotentElem E.mulVecLin).mpr hidem).trace
  rw [Matrix.rank, ← htr, LinearMap.trace_eq_matrix_trace K (Pi.basisFun K n)]
  congr 1
  ext i j
  simp [Matrix.mulVec_single]

/-- The graph-owned projector has the rank given by its trace. -/
theorem rank_P {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) : (P G).rank = 44 := by
  have hr := idempotent_rank_eq_trace (P G) (P_idempotent h)
  rw [trace_P h] at hr
  exact_mod_cast hr

/-- The point Gram of an actual graph has real rank 44. -/
theorem rank_Q {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) : (Q G).rank = 44 := by
  have hscale : (P G).rank = (Q G).rank := by
    unfold P
    exact Matrix.rank_smul_of_mem_nonZeroDivisors (Q G)
      (mem_nonZeroDivisors_of_ne_zero (by norm_num : (63 : ℝ)⁻¹ ≠ 0))
  exact hscale.symm.trans (rank_P h)

namespace Factor

noncomputable def E (P : Matrix V V ℝ) : Submodule ℝ (EuclideanSpace ℝ V) :=
  LinearMap.range P.toEuclideanLin

private theorem finrank_E (P : Matrix V V ℝ) (hrank : P.rank = 44) :
    Module.finrank ℝ (E P) = 44 := by
  have hr := P.rank_eq_finrank_range_toLin
    (EuclideanSpace.basisFun V ℝ).toBasis
    (EuclideanSpace.basisFun V ℝ).toBasis
  change Module.finrank ℝ (LinearMap.range P.toEuclideanLin) = 44
  exact hr.symm.trans hrank

noncomputable def b (P : Matrix V V ℝ) (hrank : P.rank = 44) :
    OrthonormalBasis (Fin 44) ℝ (E P) :=
  (stdOrthonormalBasis ℝ (E P)).reindex (finCongr (finrank_E P hrank))

noncomputable def W (P : Matrix V V ℝ) (hrank : P.rank = 44) :
    Matrix V (Fin 44) ℝ :=
  LinearMap.toMatrix (b P hrank).toBasis (EuclideanSpace.basisFun V ℝ).toBasis
    (E P).subtypeₗᵢ.toLinearMap

private theorem W_transpose_mul_self (P : Matrix V V ℝ) (hrank : P.rank = 44) :
    (W P hrank)ᵀ * W P hrank = 1 := by
  let i := (E P).subtypeₗᵢ
  let bb := b P hrank
  let c := EuclideanSpace.basisFun V ℝ
  have ht : (W P hrank)ᵀ =
      LinearMap.toMatrix c.toBasis bb.toBasis i.adjoint := by
    simpa only [W, i, bb, c, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (LinearMap.toMatrix_adjoint bb c i.toLinearMap).symm
  rw [ht, W, ← LinearMap.toMatrix_comp bb.toBasis c.toBasis bb.toBasis]
  rw [i.adjoint_comp_self']
  exact LinearMap.toMatrix_id bb.toBasis

private theorem W_mul_transpose (P : Matrix V V ℝ)
    (hsq : P * P = P) (hsym : Pᵀ = P) (hrank : P.rank = 44) :
    W P hrank * (W P hrank)ᵀ = P := by
  let i := (E P).subtypeₗᵢ
  let bb := b P hrank
  let c := EuclideanSpace.basisFun V ℝ
  have ht : (W P hrank)ᵀ =
      LinearMap.toMatrix c.toBasis bb.toBasis i.adjoint := by
    simpa only [W, i, bb, c, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (LinearMap.toMatrix_adjoint bb c i.toLinearMap).symm
  have hP : P.toEuclideanLin.IsSymmetricProjection := by
    constructor
    · change IsIdempotentElem (P.toLin c.toBasis c.toBasis)
      change (P.toLin c.toBasis c.toBasis) *
        (P.toLin c.toBasis c.toBasis) = P.toLin c.toBasis c.toBasis
      rw [Module.End.mul_eq_comp, ← Matrix.toLin_mul, hsq]
    · apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      exact hsym
  have hU : (i.toLinearMap.comp i.adjoint).IsSymmetricProjection := by
    constructor
    · change (i.toLinearMap.comp i.adjoint) *
        (i.toLinearMap.comp i.adjoint) = i.toLinearMap.comp i.adjoint
      rw [Module.End.mul_eq_comp]
      calc
        (i.toLinearMap.comp i.adjoint).comp
            (i.toLinearMap.comp i.adjoint) =
            i.toLinearMap.comp
              ((i.adjoint.comp i.toLinearMap).comp i.adjoint) := rfl
        _ = i.toLinearMap.comp (LinearMap.id.comp i.adjoint) := by
              rw [i.adjoint_comp_self']
        _ = i.toLinearMap.comp i.adjoint := by rw [LinearMap.id_comp]
    · exact LinearMap.isSymmetric_self_comp_adjoint i.toLinearMap
  have hEq : i.toLinearMap.comp i.adjoint = P.toEuclideanLin := by
    apply hU.ext hP
    rw [LinearMap.range_self_comp_adjoint]
    change (E P).subtype.range = E P
    exact (E P).range_subtype
  calc
    W P hrank * (W P hrank)ᵀ =
        LinearMap.toMatrix c.toBasis c.toBasis (i.toLinearMap.comp i.adjoint) := by
      rw [ht, W, ← LinearMap.toMatrix_comp c.toBasis bb.toBasis c.toBasis]
    _ = LinearMap.toMatrix c.toBasis c.toBasis P.toEuclideanLin := by rw [hEq]
    _ = P := by
      change LinearMap.toMatrix c.toBasis c.toBasis
        (P.toLin c.toBasis c.toBasis) = P
      exact LinearMap.toMatrix_toLin c.toBasis c.toBasis P

theorem exists_tight_factor (P : Matrix V V ℝ)
    (hsq : P * P = P) (hsym : Pᵀ = P) (hrank : P.rank = 44) :
    ∃ Pi : Matrix (Fin 44) V ℝ,
      Piᵀ * Pi = (63 : ℝ) • P ∧
      Pi * Piᵀ = (63 : ℝ) • (1 : Matrix (Fin 44) (Fin 44) ℝ) := by
  let Pi : Matrix (Fin 44) V ℝ := Real.sqrt 63 • (W P hrank)ᵀ
  refine ⟨Pi, ?_, ?_⟩
  · simp only [Pi, Matrix.transpose_smul, Matrix.transpose_transpose,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, W_mul_transpose P hsq hsym hrank]
    rw [← pow_two, Real.sq_sqrt (by norm_num)]
  · simp only [Pi, Matrix.transpose_smul, Matrix.transpose_transpose,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, W_transpose_mul_self P hrank]
    rw [← pow_two, Real.sq_sqrt (by norm_num)]

theorem frame_actions (Pi : Matrix (Fin 44) V ℝ) (Q A J : Matrix V V ℝ)
    (hgram : Piᵀ * Pi = Q)
    (htight : Pi * Piᵀ = (63 : ℝ) • (1 : Matrix (Fin 44) (Fin 44) ℝ))
    (hcenter : Q * J = 0) (heigen : Q * A = -((4 : ℝ) • Q)) :
    Pi * J = 0 ∧ Pi * A = -((4 : ℝ) • Pi) := by
  have hPiQ : Pi * Q = (63 : ℝ) • Pi := by
    calc
      Pi * Q = Pi * (Piᵀ * Pi) := by rw [hgram]
      _ = (Pi * Piᵀ) * Pi := by rw [Matrix.mul_assoc]
      _ = ((63 : ℝ) • (1 : Matrix (Fin 44) (Fin 44) ℝ)) * Pi := by rw [htight]
      _ = (63 : ℝ) • Pi := by simp only [Matrix.smul_mul, Matrix.one_mul]
  constructor
  · have hz : (63 : ℝ) • (Pi * J) = 0 := by
      calc
        _ = (Pi * Q) * J := by rw [hPiQ, Matrix.smul_mul]
        _ = Pi * (Q * J) := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [hcenter, Matrix.mul_zero]
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  · have he : (63 : ℝ) • (Pi * A) = -((4 : ℝ) • ((63 : ℝ) • Pi)) := by
      calc
        _ = (Pi * Q) * A := by rw [hPiQ, Matrix.smul_mul]
        _ = Pi * (Q * A) := by rw [Matrix.mul_assoc]
        _ = Pi * (-((4 : ℝ) • Q)) := by rw [heigen]
        _ = -((4 : ℝ) • (Pi * Q)) := by simp only [Matrix.mul_neg, Matrix.mul_smul]
        _ = -((4 : ℝ) • ((63 : ℝ) • Pi)) := by rw [hPiQ]
    have he' : (63 : ℝ) • (Pi * A) = (63 : ℝ) • (-((4 : ℝ) • Pi)) := by
      calc
        _ = -((4 : ℝ) • ((63 : ℝ) • Pi)) := he
        _ = (63 : ℝ) • (-((4 : ℝ) • Pi)) := by
          simp only [smul_neg, smul_smul, mul_comm]
    exact smul_right_injective (Matrix (Fin 44) V ℝ)
      (by norm_num : (63 : ℝ) ≠ 0) he'

end Factor

/-- Scaling the normalized projector does not change its real matrix rank. -/
theorem rank_P_of_rank_Q (G : SimpleGraph V) [DecidableRel G.Adj]
    (hrank : (Q G).rank = 44) : (P G).rank = 44 := by
  unfold P
  rw [Matrix.rank_smul_of_mem_nonZeroDivisors (Q G)
    (mem_nonZeroDivisors_of_ne_zero (by norm_num : (63 : ℝ)⁻¹ ≠ 0))]
  exact hrank

/-- The actual 44-row point frame, conditional only on the independent real-rank theorem. -/
theorem exists_point_frame_of_rank_Q {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (hrank : (Q G).rank = 44) :
    ∃ Pi : Matrix (Fin 44) V ℝ,
      Piᵀ * Pi = Q G ∧
      Pi * Piᵀ = (63 : ℝ) • (1 : Matrix (Fin 44) (Fin 44) ℝ) ∧
      Pi.mulVec (fun _ => 1) = 0 ∧
      Pi * G.adjMatrix ℝ = -((4 : ℝ) • Pi) := by
  obtain ⟨Pi, hg, ht⟩ :=
    Factor.exists_tight_factor (P G) (P_idempotent h) (P_transpose G)
      (rank_P_of_rank_Q G hrank)
  have hq : (63 : ℝ) • P G = Q G := by
    simp only [P, smul_smul]
    module
  rw [hq] at hg
  have heigen : Q G * G.adjMatrix ℝ = -((4 : ℝ) • Q G) := by
    have hcast : (4 : ℝ) • Q G = (4 : ℕ) • Q G := by
      simpa only [Nat.cast_ofNat] using (Nat.cast_smul_eq_nsmul ℝ 4 (Q G))
    rw [hcast]
    exact Q_mul_adjacency h
  obtain ⟨hc, he⟩ := Factor.frame_actions Pi (Q G) (G.adjMatrix ℝ)
    (of 1 : Matrix V V ℝ) hg ht (Q_mul_ones h) heigen
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by rw [h.card]; norm_num)
  obtain ⟨v⟩ := hne
  have hsum : Pi.mulVec (fun _ => 1) = 0 := by
    ext i
    have hi := congrArg (fun M : Matrix (Fin 44) V ℝ => M i v) hc
    simpa [Matrix.mulVec, Matrix.mul_apply, dotProduct] using hi
  exact ⟨Pi, hg, ht, hsum, he⟩

/-- Every hypothetical Conway graph supplies a literal 44-row real point frame. -/
theorem graph_has_actual_point_frame {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    ∃ Pi : Matrix (Fin 44) V ℝ,
      Piᵀ * Pi = Q G ∧
      Pi * Piᵀ = (63 : ℝ) • (1 : Matrix (Fin 44) (Fin 44) ℝ) ∧
      Pi.mulVec (fun _ => 1) = 0 ∧
      Pi * G.adjMatrix ℝ = -((4 : ℝ) • Pi) :=
  exists_point_frame_of_rank_Q h (rank_Q h)

/-- Real rank and the literal 44-row frame of one hypothetical Conway graph. -/
theorem point_rank_and_frame_20261003 {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (P G).rank = 44 ∧ (Q G).rank = 44 ∧
    ∃ Pi : Matrix (Fin 44) V ℝ,
      Piᵀ * Pi = Q G ∧
      Pi * Piᵀ = (63 : ℝ) • (1 : Matrix (Fin 44) (Fin 44) ℝ) ∧
      Pi.mulVec (fun _ => 1) = 0 ∧
      Pi * G.adjMatrix ℝ = -((4 : ℝ) • Pi) :=
  ⟨rank_P h, rank_Q h, graph_has_actual_point_frame h⟩

#print axioms Conway99Formal.PointFrame.point_rank_and_frame_20261003

end Conway99Formal.PointFrame

open Matrix SimpleGraph

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (Conway99Formal.PointFrame.P G).rank = 44 ∧
    (Conway99Formal.PointFrame.Q G).rank = 44 ∧
    ∃ Pi : Matrix (Fin 44) V ℝ,
      Piᵀ * Pi = Conway99Formal.PointFrame.Q G ∧
      Pi * Piᵀ = (63 : ℝ) • (1 : Matrix (Fin 44) (Fin 44) ℝ) ∧
      Pi.mulVec (fun _ => 1) = 0 ∧
      Pi * G.adjMatrix ℝ = -((4 : ℝ) • Pi) :=
  Conway99Formal.PointFrame.point_rank_and_frame_20261003 h

#print axioms solution
