-- Prove2me | solution 1 for FatkhullinPolyak.Flow.flow_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-25T04:24:19.435455+00:00
-- url     : https://prove2.me/submissions/5231f095-2e60-4121-80c9-5ac5502d6d53

import Init
import Mathlib
import Definitions.Def_FatkhullinPolyak_Flow_LQR
import Definitions.Def_FatkhullinPolyak_Flow_GradientFlow

namespace Queelius.LQRTrace
open Matrix

variable {n m r : ℕ}

theorem lyapunov_trace_adjoint
    (M X Y : Matrix (Fin n) (Fin n) ℝ) :
    trace ((Mᵀ * X + X * M) * Y) =
      trace (X * (M * Y + Y * Mᵀ)) := by
  simp only [add_mul, mul_add, trace_add, ← mul_assoc]
  rw [← trace_mul_cycle X Y Mᵀ]
  exact add_comm _ _

theorem lyapunov_trace_duality
    (M X Y U V : Matrix (Fin n) (Fin n) ℝ)
    (hX : Mᵀ * X + X * M + U = 0)
    (hY : M * Y + Y * Mᵀ + V = 0) :
    trace (X * V) = trace (U * Y) := by
  have hx : Mᵀ * X + X * M = -U := eq_neg_of_add_eq_zero_left hX
  have hy : M * Y + Y * Mᵀ = -V := eq_neg_of_add_eq_zero_left hY
  have ht := lyapunov_trace_adjoint M X Y
  rw [hx, hy, neg_mul, mul_neg, trace_neg, trace_neg] at ht
  linarith

theorem transpose_lyapunov_solution
    (M X U : Matrix (Fin n) (Fin n) ℝ)
    (hU : Uᵀ = U) (hX : Mᵀ * X + X * M + U = 0) :
    Mᵀ * Xᵀ + Xᵀ * M + U = 0 := by
  have ht := congrArg Matrix.transpose hX
  simpa only [transpose_add, transpose_mul, transpose_transpose,
    transpose_zero, hU, add_comm (Xᵀ * M) (Mᵀ * Xᵀ)] using ht

theorem unique_lyapunov_solution_symmetric
    (M X U : Matrix (Fin n) (Fin n) ℝ)
    (hU : Uᵀ = U) (hX : Mᵀ * X + X * M + U = 0)
    (hUnique : ∀ Z, Mᵀ * Z + Z * M + U = 0 → Z = X) :
    Xᵀ = X :=
  hUnique Xᵀ (transpose_lyapunov_solution M X U hU hX)

theorem gradient_trace_algebra
    (C : Matrix (Fin r) (Fin n) ℝ)
    (F : Matrix (Fin m) (Fin n) ℝ)
    (Y : Matrix (Fin n) (Fin n) ℝ)
    (E : Matrix (Fin m) (Fin r) ℝ)
    (hY : Yᵀ = Y) :
    trace (((E * C)ᵀ * F + Fᵀ * (E * C)) * Y) =
      trace (((2 : ℝ) • (F * Y * Cᵀ))ᵀ * E) := by
  have ht : trace ((E * C)ᵀ * F * Y) = trace (Fᵀ * (E * C) * Y) := by
    rw [← trace_transpose ((E * C)ᵀ * F * Y)]
    simp only [transpose_mul, transpose_transpose, hY]
    exact trace_mul_comm Y (Fᵀ * (E * C))
  have hc : trace (Fᵀ * (E * C) * Y) = trace ((F * Y * Cᵀ)ᵀ * E) := by
    simp only [transpose_mul, transpose_transpose, hY]
    rw [← Matrix.mul_assoc Fᵀ E C]
    rw [trace_mul_cycle (Fᵀ * E) C Y]
    rw [trace_mul_comm (Y * (Fᵀ * E)) C]
    simp only [Matrix.mul_assoc]
  simp only [add_mul, trace_add, ht, hc, transpose_smul, smul_mul, trace_smul]
  ring

theorem linearized_cost_trace
    (M dX Y Sig : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ)
    (F : Matrix (Fin m) (Fin n) ℝ)
    (E : Matrix (Fin m) (Fin r) ℝ)
    (hY : Yᵀ = Y)
    (hdX : Mᵀ * dX + dX * M + (E * C)ᵀ * F + Fᵀ * (E * C) = 0)
    (hDual : M * Y + Y * Mᵀ + Sig = 0) :
    trace (dX * Sig) = trace (((2 : ℝ) • (F * Y * Cᵀ))ᵀ * E) := by
  have hdX' : Mᵀ * dX + dX * M + ((E * C)ᵀ * F + Fᵀ * (E * C)) = 0 := by
    simpa only [add_assoc] using hdX
  exact (lyapunov_trace_duality M dX Y _ Sig hdX' hDual).trans
    (gradient_trace_algebra C F Y E hY)

end Queelius.LQRTrace

namespace Queelius.LQRTrace
open Matrix FatkhullinPolyak.Flow
variable {n m r : ℕ}

theorem lyapX_spec
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin m) (Fin r) ℝ)
    (h : ∃! X : Matrix (Fin n) (Fin n) ℝ,
      (closedLoop A B C K)ᵀ * X + X * closedLoop A B C K +
      Cᵀ * Kᵀ * R * K * C + Q = 0) :
    (closedLoop A B C K)ᵀ * lyapX A B C Q R K +
      lyapX A B C Q R K * closedLoop A B C K + Cᵀ * Kᵀ * R * K * C + Q = 0 := by
  classical
  unfold lyapX
  rw [dif_pos h]
  exact h.exists.choose_spec

theorem lyapY_spec
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (K : Matrix (Fin m) (Fin r) ℝ)
    (h : ∃! Y : Matrix (Fin n) (Fin n) ℝ,
      closedLoop A B C K * Y + Y * (closedLoop A B C K)ᵀ + Sig = 0) :
    closedLoop A B C K * lyapY A B C Sig K +
      lyapY A B C Sig K * (closedLoop A B C K)ᵀ + Sig = 0 := by
  classical
  unfold lyapY
  rw [dif_pos h]
  exact h.exists.choose_spec

theorem lyapY_symmetric
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (K : Matrix (Fin m) (Fin r) ℝ) (hSig : Sigᵀ = Sig)
    (h : ∃! Y : Matrix (Fin n) (Fin n) ℝ,
      closedLoop A B C K * Y + Y * (closedLoop A B C K)ᵀ + Sig = 0) :
    (lyapY A B C Sig K)ᵀ = lyapY A B C Sig K := by
  have hY := lyapY_spec A B C Sig K h
  have hT := transpose_lyapunov_solution (closedLoop A B C K)ᵀ
    (lyapY A B C Sig K) Sig hSig (by simpa using hY)
  rcases h with ⟨Y₀, _, hu⟩
  exact (hu _ (by simpa using hT)).trans (hu _ hY).symm

theorem lyapX_symmetric
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin m) (Fin r) ℝ)
    (hQ : Qᵀ = Q) (hR : Rᵀ = R)
    (h : ∃! X : Matrix (Fin n) (Fin n) ℝ,
      (closedLoop A B C K)ᵀ * X + X * closedLoop A B C K +
      Cᵀ * Kᵀ * R * K * C + Q = 0) :
    (lyapX A B C Q R K)ᵀ = lyapX A B C Q R K := by
  have hX := lyapX_spec A B C Q R K h
  have hU : (Cᵀ * Kᵀ * R * K * C + Q)ᵀ = Cᵀ * Kᵀ * R * K * C + Q := by
    simp only [transpose_add, transpose_mul, transpose_transpose, hQ, hR, Matrix.mul_assoc]
  have hT := transpose_lyapunov_solution (closedLoop A B C K)
    (lyapX A B C Q R K) (Cᵀ * Kᵀ * R * K * C + Q) hU
    (by simpa only [add_assoc] using hX)
  rcases h with ⟨X₀, _, hu⟩
  exact (hu _ (by simpa only [add_assoc] using hT)).trans (hu _ hX).symm

theorem platform_linearized_gradient
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q Sig : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (K E : Matrix (Fin m) (Fin r) ℝ)
    (dX : Matrix (Fin n) (Fin n) ℝ) (hSig : Sigᵀ = Sig)
    (hY : ∃! Y : Matrix (Fin n) (Fin n) ℝ,
      closedLoop A B C K * Y + Y * (closedLoop A B C K)ᵀ + Sig = 0)
    (hdX : (closedLoop A B C K)ᵀ * dX + dX * closedLoop A B C K +
      (E * C)ᵀ * (R * K * C - Bᵀ * lyapX A B C Q R K) +
      (R * K * C - Bᵀ * lyapX A B C Q R K)ᵀ * (E * C) = 0) :
    trace (dX * Sig) = trace ((grad A B C Q R Sig K)ᵀ * E) := by
  exact linearized_cost_trace (closedLoop A B C K) dX (lyapY A B C Sig K) Sig C
    (R * K * C - Bᵀ * lyapX A B C Q R K) E
    (lyapY_symmetric A B C Sig K hSig hY) hdX (lyapY_spec A B C Sig K hY)

end Queelius.LQRTrace

namespace Queelius.LQRTrace
open Matrix FatkhullinPolyak.Flow
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
variable {n m r : ℕ}

noncomputable def costFunctional (Sig : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun X => trace (X * Sig)
    map_add' := by intro X Y; simp only [add_mul, trace_add]
    map_smul' := by intro a X; simp only [smul_mul, trace_smul, RingHom.id_apply]
  }

theorem gradient_of_lyapunov_derivative
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q Sig : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin m) (Fin r) ℝ)
    (hSig : Sig.PosDef)
    (hY : ∃! Y : Matrix (Fin n) (Fin n) ℝ,
      closedLoop A B C K * Y + Y * (closedLoop A B C K)ᵀ + Sig = 0)
    (DX : Matrix (Fin m) (Fin r) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ)
    (hDX : HasFDerivAt (fun K' => lyapX A B C Q R K') DX K)
    (hLin : ∀ E : Matrix (Fin m) (Fin r) ℝ,
      (closedLoop A B C K)ᵀ * DX E + DX E * closedLoop A B C K +
      (E * C)ᵀ * (R * K * C - Bᵀ * lyapX A B C Q R K) +
      (R * K * C - Bᵀ * lyapX A B C Q R K)ᵀ * (E * C) = 0) :
    ∃ f' : Matrix (Fin m) (Fin r) ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun K' => cost A B C Q R Sig K') f' K ∧
      ∀ E : Matrix (Fin m) (Fin r) ℝ,
        f' E = trace ((grad A B C Q R Sig K)ᵀ * E) := by
  have hs : Sigᵀ = Sig := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hSig.isHermitian
  refine ⟨(costFunctional Sig).comp DX, ?_, ?_⟩
  · exact (costFunctional Sig).hasFDerivAt.comp K hDX
  · intro E
    exact platform_linearized_gradient A B C Q Sig R K E (DX E) hs hY (hLin E)

end Queelius.LQRTrace

namespace Queelius.LQRTrace
open Matrix FatkhullinPolyak.Flow
open scoped Matrix.Norms.Frobenius
variable {n m r : ℕ}

/-- Explicit operator-norm instance bridges the reducibility boundary of Matrix's
product topology and its Frobenius norm; the underlying instance is Mathlib's. -/
@[instance_reducible] noncomputable def matrixCLMNorm (p q a b : ℕ) :
    NormedAddCommGroup (Matrix (Fin p) (Fin q) ℝ →L[ℝ] Matrix (Fin a) (Fin b) ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
attribute [local instance] matrixCLMNorm
@[instance_reducible] noncomputable def matrixCLMSpace (p q a b : ℕ) :
    NormedSpace ℝ (Matrix (Fin p) (Fin q) ℝ →L[ℝ] Matrix (Fin a) (Fin b) ℝ) :=
  ContinuousLinearMap.toNormedSpace
attribute [local instance] matrixCLMSpace
@[instance_reducible] noncomputable def matrixEndNormedRing (p q : ℕ) :
    NormedRing (Matrix (Fin p) (Fin q) ℝ →L[ℝ] Matrix (Fin p) (Fin q) ℝ) :=
  ContinuousLinearMap.toNormedRing
attribute [local instance] matrixEndNormedRing
instance matrixCLMComplete (p q a b : ℕ) :
    CompleteSpace (Matrix (Fin p) (Fin q) ℝ →L[ℝ] Matrix (Fin a) (Fin b) ℝ) :=
  FiniteDimensional.complete ℝ _
theorem matrixEndSummable (p q : ℕ) :
    HasSummableGeomSeries (Matrix (Fin p) (Fin q) ℝ →L[ℝ] Matrix (Fin p) (Fin q) ℝ) :=
  @instHasSummableGeomSeriesOfCompleteSpace _ (matrixEndNormedRing p q)
    (matrixCLMComplete p q p q)
attribute [local instance] matrixEndSummable

noncomputable def lyapOp (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun X => Mᵀ * X + X * M
    map_add' := by intro X Y; simp only [Matrix.mul_add,Matrix.add_mul]; abel
    map_smul' := by intro a X; simp only [Matrix.mul_smul,Matrix.smul_mul,smul_add,RingHom.id_apply]
  }

noncomputable def lyapOpLinear : Matrix (Fin n) (Fin n) ℝ →L[ℝ]
    (Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := lyapOp
    map_add' := by intro M N; ext X i j; simp [lyapOp,transpose_add,Matrix.add_mul,Matrix.mul_add]; ring
    map_smul' := by intro a M; ext X i j; simp [lyapOp,transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_add]; ring
  }

noncomputable def feedbackLinear
    (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin r) (Fin n) ℝ) :
    Matrix (Fin m) (Fin r) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun K => B * K * C
    map_add' := by intro K L; simp only [Matrix.mul_add,Matrix.add_mul]
    map_smul' := by intro a K; simp only [Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply]
  }

noncomputable def forcingBilin (C : Matrix (Fin r) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin r) ℝ →L[ℝ]
    (Matrix (Fin m) (Fin r) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun K => LinearMap.toContinuousLinearMap {
      toFun := fun E => Cᵀ * Kᵀ * R * E * C
      map_add' := by intro E F; simp only [Matrix.mul_add,Matrix.add_mul]
      map_smul' := by intro a E; simp only [Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply]
    }
    map_add' := by intro K L; ext E i j; simp [transpose_add,Matrix.mul_add,Matrix.add_mul]
    map_smul' := by intro a K; ext E i j; simp [transpose_smul,Matrix.mul_smul,Matrix.smul_mul]
  }

@[simp] theorem lyapOp_apply (M X : Matrix (Fin n) (Fin n) ℝ) :
    lyapOp M X = Mᵀ * X + X * M := rfl
@[simp] theorem lyapOpLinear_apply (M : Matrix (Fin n) (Fin n) ℝ) :
    lyapOpLinear M = lyapOp M := rfl
@[simp] theorem feedbackLinear_apply (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (K : Matrix (Fin m) (Fin r) ℝ) :
    feedbackLinear B C K = B * K * C := rfl
@[simp] theorem forcingBilin_apply (C : Matrix (Fin r) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (K E : Matrix (Fin m) (Fin r) ℝ) :
    forcingBilin C R K E = Cᵀ * Kᵀ * R * E * C := rfl

end Queelius.LQRTrace

namespace Queelius.LQRTrace
open Matrix FatkhullinPolyak.Flow
open scoped Topology
open scoped Matrix.Norms.Frobenius
attribute [local instance] matrixCLMNorm matrixCLMSpace matrixEndNormedRing matrixEndSummable
variable {n m r : ℕ}

theorem lyap_invertible_of_unit (M : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (lyapOp M)) : (lyapOp M).IsInvertible := by
  rcases h with ⟨u,hu⟩
  exact ⟨ContinuousLinearEquiv.ofUnit u,hu⟩

theorem lyap_unique_of_unit (M U : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (lyapOp M)) : ∃! X : Matrix (Fin n) (Fin n) ℝ,
      Mᵀ * X + X * M + U = 0 := by
  have hi := lyap_invertible_of_unit M h
  refine ⟨(lyapOp M).inverse (-U),?_,?_⟩
  · have hh := hi.self_apply_inverse (-U)
    change lyapOp M ((lyapOp M).inverse (-U)) + U = 0
    rw [hh,neg_add_cancel]
  · intro X hX
    apply hi.injective
    rw [hi.self_apply_inverse]
    exact eq_neg_of_add_eq_zero_left hX

theorem lyapX_eq_inverse
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin m) (Fin r) ℝ)
    (hu : IsUnit (lyapOp (closedLoop A B C K))) :
    lyapX A B C Q R K = (lyapOp (closedLoop A B C K)).inverse
      (-(Cᵀ * Kᵀ * R * K * C + Q)) := by
  have he : ∃! X : Matrix (Fin n) (Fin n) ℝ,
      (closedLoop A B C K)ᵀ * X + X * closedLoop A B C K + Cᵀ * Kᵀ * R * K * C + Q = 0 := by
    simpa only [add_assoc] using lyap_unique_of_unit (closedLoop A B C K)
      (Cᵀ * Kᵀ * R * K * C + Q) hu
  have hx := lyapX_spec A B C Q R K he
  have hi := lyap_invertible_of_unit (closedLoop A B C K) hu
  apply hi.injective
  rw [hi.self_apply_inverse]
  apply eq_neg_of_add_eq_zero_left
  simpa only [lyapOp_apply,add_assoc] using hx

theorem contDiff_operator (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin r) (Fin n) ℝ)
    (d : WithTop ℕ∞) : ContDiff ℝ d (fun K => lyapOp (closedLoop A B C K)) := by
  exact (lyapOpLinear (n := n)).contDiff.comp (contDiff_const.sub (feedbackLinear B C).contDiff)

theorem contDiff_forcing (C : Matrix (Fin r) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (d : WithTop ℕ∞) : ContDiff ℝ d
      (fun K : Matrix (Fin m) (Fin r) ℝ => Cᵀ * Kᵀ * R * K * C + Q) := by
  exact ((forcingBilin C R).contDiff.clm_apply contDiff_id).add contDiff_const

theorem eventually_lyap_unit (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin r) (Fin n) ℝ)
    (K : Matrix (Fin m) (Fin r) ℝ)
    (hu : IsUnit (lyapOp (closedLoop A B C K))) :
    ∀ᶠ L in 𝓝 K, IsUnit (lyapOp (closedLoop A B C L)) := by
  exact (contDiff_operator A B C 0).continuous.continuousAt.eventually
    (Units.isOpen.mem_nhds hu)

theorem contDiffAt_lyapX_of_unit
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin m) (Fin r) ℝ)
    (hu : IsUnit (lyapOp (closedLoop A B C K))) (d : WithTop ℕ∞) :
    ContDiffAt ℝ d (fun L => lyapX A B C Q R L) K := by
  have hi : ContDiffAt ℝ d ContinuousLinearMap.inverse (lyapOp (closedLoop A B C K)) :=
    (lyap_invertible_of_unit _ hu).contDiffAt_map_inverse
  have hL := (contDiff_operator A B C d).contDiffAt (x := K)
  have hU := ((contDiff_forcing C Q R d).contDiffAt (x := K)).neg
  have hh := (hi.comp K hL).clm_apply hU
  apply hh.congr_of_eventuallyEq
  filter_upwards [eventually_lyap_unit A B C K hu] with L hL
  exact lyapX_eq_inverse A B C Q R L hL

#print axioms contDiffAt_lyapX_of_unit
end Queelius.LQRTrace

namespace Queelius.LQRTrace
open Matrix FatkhullinPolyak.Flow
open scoped Topology Matrix.Norms.Frobenius
attribute [local instance] matrixCLMNorm matrixCLMSpace matrixEndNormedRing matrixEndSummable
variable {n m r : ℕ}

/-- Differentiate the exact choice-defined Lyapunov equation on the open set
where its operator is invertible. No derivative premise is assumed. -/
theorem lyapX_derivative_equation
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin m) (Fin r) ℝ)
    (hu : IsUnit (lyapOp (closedLoop A B C K))) :
    ∃ DX : Matrix (Fin m) (Fin r) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ,
      HasFDerivAt (fun L => lyapX A B C Q R L) DX K ∧
      ∀ E : Matrix (Fin m) (Fin r) ℝ,
        lyapOp (closedLoop A B C K) (DX E) +
        lyapOp (-(B * E * C)) (lyapX A B C Q R K) +
        (Cᵀ * Eᵀ * R * K * C + Cᵀ * Kᵀ * R * E * C) = 0 := by
  have hdiff := (contDiffAt_lyapX_of_unit A B C Q R K hu 1).differentiableAt (by norm_num)
  let DX := fderiv ℝ (fun L => lyapX A B C Q R L) K
  have hDX : HasFDerivAt (fun L => lyapX A B C Q R L) DX K := hdiff.hasFDerivAt
  refine ⟨DX,hDX,?_⟩
  have hM := (hasFDerivAt_const A K).sub (feedbackLinear B C).hasFDerivAt
  have hL := (lyapOpLinear (n := n)).hasFDerivAt.comp K hM
  have hU := ((forcingBilin C R).hasFDerivAt.clm_apply (hasFDerivAt_id K)).add_const Q
  have hres := (hL.clm_apply hDX).add hU
  have he : (fun _ : Matrix (Fin m) (Fin r) ℝ => (0 : Matrix (Fin n) (Fin n) ℝ)) =ᶠ[𝓝 K]
      (fun L => lyapOp (closedLoop A B C L) (lyapX A B C Q R L) +
        (Cᵀ * Lᵀ * R * L * C + Q)) := by
    filter_upwards [eventually_lyap_unit A B C K hu] with L hL
    rw [lyapX_eq_inverse A B C Q R L hL,
      (lyap_invertible_of_unit _ hL).self_apply_inverse,neg_add_cancel]
  have hz := (hres.congr_of_eventuallyEq he).unique (hasFDerivAt_const 0 K)
  intro E
  have hh := DFunLike.congr_fun hz E
  change lyapOp (closedLoop A B C K) (DX E) +
    lyapOp (0 - B * E * C) (lyapX A B C Q R K) +
    (Cᵀ * Kᵀ * R * E * C + Cᵀ * Eᵀ * R * K * C) = 0 at hh
  simpa only [zero_sub,add_comm] using hh

/-- The standard symmetric linearized equation follows by expanding the
operator derivative and the quadratic forcing. -/
theorem lyapX_linearized
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin m) (Fin r) ℝ)
    (hQ : Qᵀ = Q) (hR : Rᵀ = R)
    (hu : IsUnit (lyapOp (closedLoop A B C K))) :
    ∃ DX : Matrix (Fin m) (Fin r) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ,
      HasFDerivAt (fun L => lyapX A B C Q R L) DX K ∧
      ∀ E : Matrix (Fin m) (Fin r) ℝ,
        (closedLoop A B C K)ᵀ * DX E + DX E * closedLoop A B C K +
        (E * C)ᵀ * (R * K * C - Bᵀ * lyapX A B C Q R K) +
        (R * K * C - Bᵀ * lyapX A B C Q R K)ᵀ * (E * C) = 0 := by
  obtain ⟨DX,hDX,hlin⟩ := lyapX_derivative_equation A B C Q R K hu
  have he : ∃! X : Matrix (Fin n) (Fin n) ℝ,
      (closedLoop A B C K)ᵀ * X + X * closedLoop A B C K + Cᵀ * Kᵀ * R * K * C + Q = 0 := by
    simpa only [add_assoc] using lyap_unique_of_unit (closedLoop A B C K)
      (Cᵀ * Kᵀ * R * K * C + Q) hu
  have hX := lyapX_symmetric A B C Q R K hQ hR he
  refine ⟨DX,hDX,?_⟩
  intro E
  have hh := hlin E
  simp only [lyapOp_apply,transpose_neg,transpose_mul,transpose_transpose,
    Matrix.neg_mul,Matrix.mul_neg,Matrix.mul_assoc] at hh
  simp only [transpose_mul,transpose_sub,transpose_transpose,hR,hX,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
  abel_nf at hh ⊢
  exact hh

#print axioms lyapX_linearized
end Queelius.LQRTrace

namespace Queelius.LQRTrace
open Matrix FatkhullinPolyak.Flow
open scoped Matrix.Norms.Frobenius
attribute [local instance] matrixCLMNorm matrixCLMSpace matrixEndNormedRing matrixEndSummable
variable {n m r : ℕ}

/-- The exact platform gradient conclusion needs only nonsingularity of the two
Lyapunov operators. Solvability, smoothness and the linearized equation follow. -/
theorem gradient_of_lyapunov_units
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef)
    (K : Matrix (Fin m) (Fin r) ℝ)
    (hX : IsUnit (lyapOp (closedLoop A B C K)))
    (hY : IsUnit (lyapOp (closedLoop A B C K)ᵀ)) :
    ∃ f' : Matrix (Fin m) (Fin r) ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun L => cost A B C Q R Sig L) f' K ∧
      ∀ E : Matrix (Fin m) (Fin r) ℝ,
        f' E = trace ((grad A B C Q R Sig K)ᵀ * E) := by
  have hsQ : Qᵀ = Q := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.isHermitian
  have hsR : Rᵀ = R := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hR.isHermitian
  obtain ⟨DX,hDX,hLin⟩ := lyapX_linearized A B C Q R K hsQ hsR hX
  have hYu : ∃! Y : Matrix (Fin n) (Fin n) ℝ,
      closedLoop A B C K * Y + Y * (closedLoop A B C K)ᵀ + Sig = 0 := by
    simpa only [transpose_transpose] using lyap_unique_of_unit (closedLoop A B C K)ᵀ Sig hY
  exact gradient_of_lyapunov_derivative A B C Q Sig R K hSig hYu DX hDX hLin

#print axioms gradient_of_lyapunov_units

/-- Trace nondegeneracy and finite dimension transfer invertibility to the dual
Lyapunov operator. No symmetry or definiteness of M is required. -/
theorem lyap_unit_transpose (M : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (lyapOp M)) : IsUnit (lyapOp Mᵀ) := by
  have hi := (lyap_invertible_of_unit M h).surjective
  have hinj : Function.Injective (lyapOp Mᵀ) := by
    intro Y Z hYZ
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro W
    obtain ⟨X,hX⟩ := hi W
    rw [← hX]
    change trace ((Mᵀ * X + X * M) * Y) = trace ((Mᵀ * X + X * M) * Z)
    rw [lyapunov_trace_adjoint,lyapunov_trace_adjoint]
    have he : M * Y + Y * Mᵀ = M * Z + Z * Mᵀ := by
      simpa only [lyapOp_apply,transpose_transpose] using hYZ
    rw [he]
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  exact ⟨hinj,(LinearMap.injective_iff_surjective (f := (lyapOp Mᵀ).toLinearMap)).mp hinj⟩

/-- The exact LQR gradient conclusion reduced to one finite-dimensional
nonsingularity premise. This theorem assumes no derivative or solution existence. -/
theorem gradient_of_lyapunov_unit
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef)
    (K : Matrix (Fin m) (Fin r) ℝ)
    (hX : IsUnit (lyapOp (closedLoop A B C K))) :
    ∃ f' : Matrix (Fin m) (Fin r) ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun L => cost A B C Q R Sig L) f' K ∧
      ∀ E : Matrix (Fin m) (Fin r) ℝ,
        f' E = trace ((grad A B C Q R Sig K)ᵀ * E) := by
  exact gradient_of_lyapunov_units A B C Q R Sig hQ hR hSig K hX
    (lyap_unit_transpose _ hX)

#print axioms gradient_of_lyapunov_unit
end Queelius.LQRTrace

namespace Queelius.LQRTrace
open Matrix Polynomial
variable {n : ℕ}

/-- Polynomial functional calculus preserves matrix intertwiners. -/
theorem intertwines_aeval {K : Type*} [CommRing K]
    (A B X : Matrix (Fin n) (Fin n) K) (h : A * X = X * B)
    (p : K[X]) : aeval A p * X = X * aeval B p := by
  induction p using Polynomial.induction_on with
  | C c =>
    simpa only [aeval_C] using Algebra.commutes (R := K) (A := Matrix (Fin n) (Fin n) K) c X
  | add p q hp hq => simp only [map_add, add_mul, mul_add, hp, hq]
  | monomial k c hp =>
    let p : K[X] := C c * Polynomial.X ^ k
    change aeval A (C c * Polynomial.X ^ (k + 1)) * X = X * aeval B (C c * Polynomial.X ^ (k + 1))
    rw [show C c * Polynomial.X ^ (k + 1) = p * Polynomial.X from by simp [p, pow_succ, mul_assoc]]
    simp only [map_mul, aeval_X]
    calc
      (aeval A p * A) * X = aeval A p * (A * X) := mul_assoc _ _ _
      _ = aeval A p * (X * B) := by rw [h]
      _ = (X * aeval B p) * B := by rw [← mul_assoc, hp]
      _ = X * (aeval B p * B) := mul_assoc _ _ _

/-- Disjoint characteristic roots force an intertwining matrix to vanish. -/
theorem intertwiner_zero_of_coprime_charpoly {K : Type*} [Field K]
    (A B X : Matrix (Fin n) (Fin n) K)
    (h : A * X = X * B) (hc : IsCoprime A.charpoly B.charpoly) : X = 0 := by
  obtain ⟨p,q,hpq⟩ := hc
  have hz : X * aeval B A.charpoly = 0 := by
    rw [← intertwines_aeval A B X h, Matrix.aeval_self_charpoly, zero_mul]
  rw [mul_comm p A.charpoly] at hpq
  have hh := congrArg (fun s : K[X] => X * aeval B s) hpq
  simpa only [map_add, map_mul, map_one, mul_one, mul_add,
    ← mul_assoc, hz, Matrix.aeval_self_charpoly, mul_zero, zero_mul, add_zero] using hh.symm

#print axioms intertwiner_zero_of_coprime_charpoly
end Queelius.LQRTrace

namespace Queelius.LQRTrace
open Matrix Polynomial FatkhullinPolyak.Flow
variable {n : ℕ}

/-- The Hurwitz half-plane separates the characteristic roots of Mᵀ and -M. -/
theorem hurwitz_coprime_charpoly (M : Matrix (Fin n) (Fin n) ℝ)
    (h : IsHurwitz M) :
    IsCoprime (M.map (algebraMap ℝ ℂ))ᵀ.charpoly
      (-(M.map (algebraMap ℝ ℂ))).charpoly := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ _ _).mpr
  intro z
  rw [Matrix.charpoly_transpose]
  by_contra hz
  push_neg at hz
  have hzM : z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) := by
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    simpa only [Polynomial.IsRoot, Polynomial.coe_aeval_eq_eval] using hz.1
  have hzN : z ∈ spectrum ℂ (-(M.map (algebraMap ℝ ℂ))) := by
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    simpa only [Polynomial.IsRoot, Polynomial.coe_aeval_eq_eval] using hz.2
  have hn : -z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) := by
    simpa only [← spectrum.neg_eq, Set.mem_neg] using hzN
  have hpos := h z hzM
  have hneg := h (-z) hn
  simp only [Complex.neg_re] at hneg
  linarith

#print axioms hurwitz_coprime_charpoly
end Queelius.LQRTrace

namespace Queelius.LQRTrace
open Matrix Polynomial FatkhullinPolyak.Flow
open scoped Matrix.Norms.Frobenius
attribute [local instance] matrixCLMNorm matrixCLMSpace matrixEndNormedRing matrixEndSummable
variable {n : ℕ}

/-- A homogeneous Lyapunov equation at a Hurwitz matrix has only the zero solution. -/
theorem lyapunov_kernel_zero (M X : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsHurwitz M) (hX : Mᵀ * X + X * M = 0) : X = 0 := by
  let f := algebraMap ℝ ℂ
  have hc : (M.map f)ᵀ * X.map f = X.map f * (-(M.map f)) := by
    have he : Mᵀ * X = -(X * M) := eq_neg_of_add_eq_zero_left hX
    have hm := congrArg (fun Y : Matrix (Fin n) (Fin n) ℝ => Y.map f) he
    simpa only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_neg f (map_neg f), mul_neg] using hm
  have hz := intertwiner_zero_of_coprime_charpoly (M.map f)ᵀ (-(M.map f))
    (X.map f) hc (hurwitz_coprime_charpoly M hM)
  ext i j
  have he := congrFun (congrFun hz i) j
  change (X i j : ℂ) = 0 at he
  exact_mod_cast he

/-- Hurwitz stability makes the real Lyapunov operator invertible. -/
theorem lyap_unit_of_hurwitz (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsHurwitz M) : IsUnit (lyapOp M) := by
  have hi : Function.Injective (lyapOp M) := by
    intro X Y hXY
    apply sub_eq_zero.mp
    apply lyapunov_kernel_zero M (X-Y) hM
    change lyapOp M (X-Y) = 0
    rw [map_sub, hXY, sub_self]
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  exact ⟨hi, (LinearMap.injective_iff_surjective (f := (lyapOp M).toLinearMap)).mp hi⟩

#print axioms lyap_unit_of_hurwitz
end Queelius.LQRTrace

namespace Queelius.LQREnergy
open Matrix FatkhullinPolyak.Flow
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
set_option maxHeartbeats 1000000

theorem matrix_derivative_of_entries {m r : ℕ} (K : ℝ → Matrix (Fin m) (Fin r) ℝ)
    (V : Matrix (Fin m) (Fin r) ℝ) (S : Set ℝ) (t : ℝ)
    (h : ∀ i j, HasDerivWithinAt (fun s => K s i j) (V i j) S t) :
    HasDerivWithinAt K V S t := by
  exact hasDerivWithinAt_pi.mpr (fun i => hasDerivWithinAt_pi.mpr (h i))

theorem trace_transpose_self {m r : ℕ} (G : Matrix (Fin m) (Fin r) ℝ) :
    trace (Gᵀ * G) = frobNorm G ^ 2 := by
  unfold frobNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (G i j))))]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [pow_two]

#print axioms matrix_derivative_of_entries
#print axioms trace_transpose_self
end Queelius.LQREnergy

open Matrix FatkhullinPolyak.Flow
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
set_option maxHeartbeats 1000000

/-- Fatkhullin–Polyak §4.1: the exact choice-defined cost dissipates Frobenius gradient energy. -/
theorem Queelius.LQREnergy.flow_energy_identity {n m r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin r) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef)
    (K₀ : Matrix (Fin m) (Fin r) ℝ) (K : ℝ → Matrix (Fin m) (Fin r) ℝ)
    (hK : IsGradFlow A B C Q R Sig K₀ K) :
    ∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt (fun s => cost A B C Q R Sig (K s))
        (-(frobNorm (grad A B C Q R Sig (K t)) ^ 2)) (Set.Ici 0) t := by
  intro t ht
  obtain ⟨hstab,hentries⟩ := hK.2 t ht
  obtain ⟨D,hD,htrace⟩ := Queelius.LQRTrace.gradient_of_lyapunov_unit
    A B C Q R Sig hQ hR hSig (K t)
    (Queelius.LQRTrace.lyap_unit_of_hurwitz (closedLoop A B C (K t)) hstab)
  have hcurve := Queelius.LQREnergy.matrix_derivative_of_entries K
    (-(grad A B C Q R Sig (K t))) (Set.Ici 0) t hentries
  have hc := hD.comp_hasDerivWithinAt t hcurve
  have he : D (-(grad A B C Q R Sig (K t))) = -(frobNorm (grad A B C Q R Sig (K t)) ^ 2) := by
    calc
      _ = trace ((grad A B C Q R Sig (K t))ᵀ * (-(grad A B C Q R Sig (K t)))) := htrace _
      _ = _ := by rw [Matrix.mul_neg,Matrix.trace_neg,Queelius.LQREnergy.trace_transpose_self]
  convert hc using 1 <;> first | rfl | exact he.symm
#print axioms Queelius.LQREnergy.flow_energy_identity

namespace Queelius.LQREnergy
open Matrix FatkhullinPolyak.Flow
set_option maxHeartbeats 1000000

theorem flow_cost_antitone {n m r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin r) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef)
    (K₀ : Matrix (Fin m) (Fin r) ℝ) (K : ℝ → Matrix (Fin m) (Fin r) ℝ)
    (hK : IsGradFlow A B C Q R Sig K₀ K) :
    AntitoneOn (fun t => cost A B C Q R Sig (K t)) (Set.Ici 0) := by
  have hd := flow_energy_identity A B C Q R Sig hQ hR hSig K₀ K hK
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0:ℝ))
  · intro t ht
    exact (hd t ht).continuousWithinAt
  · intro t ht
    exact (hd t (interior_subset ht)).mono interior_subset
  · intro t _
    exact neg_nonpos.mpr (sq_nonneg _)

#print axioms flow_cost_antitone
end Queelius.LQREnergy

namespace Prove2Me.Mrfancypants.LyapunovPositivity
open Filter Topology Matrix FatkhullinPolyak.Flow
lemma aux_lcb_mem_spec {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    z ∈ spectrum ℂ N ↔ (Matrix.scalar (Fin n) z - N).det = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  rfl

lemma aux_lcb_hurwitz_transpose {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    IsHurwitz M.transpose := by
  intro z hz
  apply hM z
  rw [aux_lcb_mem_spec] at hz ⊢
  rw [← Matrix.det_transpose]
  convert hz using 2
  rw [Matrix.transpose_sub, Matrix.transpose_map]
  simp

lemma aux_lcb_det_map {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (M.map (algebraMap ℝ ℂ)).det = (M.det : ℂ) := by
  rw [show M.map (algebraMap ℝ ℂ) = (algebraMap ℝ ℂ).mapMatrix M from rfl, ← RingHom.map_det]
  rfl

lemma aux_lcb_one_sub_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    (1 - M).det ≠ 0 := by
  intro h
  have h1 : (1 : ℂ) ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) := by
    rw [aux_lcb_mem_spec]
    have : Matrix.scalar (Fin n) (1 : ℂ) - M.map (algebraMap ℝ ℂ) = (1 - M).map (algebraMap ℝ ℂ) := by
      rw [Matrix.map_sub _ (fun a b => map_sub _ a b)]
      simp
    rw [this, aux_lcb_det_map, h]
    simp
  have := hM 1 h1
  norm_num at this


lemma aux_lcb_mem_spec' {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    z ∈ spectrum ℂ N ↔ (z • (1 : Matrix (Fin n) (Fin n) ℂ) - N).det = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    Algebra.algebraMap_eq_smul_one]

lemma aux_lcb_re_div (z : ℂ) (hz : 1 ≤ ‖z‖) (hz1 : z + 1 ≠ 0) :
    0 ≤ ((z - 1) / (z + 1)).re := by
  rw [Complex.div_re]
  have hN : 0 < Complex.normSq (z + 1) := Complex.normSq_pos.mpr hz1
  have h2 : 1 ≤ z.re * z.re + z.im * z.im := by
    have := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg z]
  rw [← add_div]
  apply div_nonneg _ hN.le
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.sub_im, Complex.one_im,
    Complex.add_im]
  nlinarith

lemma aux_lcb_T_spec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    ∀ z ∈ spectrum ℂ (((1 + M) * (1 - M)⁻¹).map (algebraMap ℝ ℂ)), ‖z‖ < 1 := by
  intro z hz
  have hG := aux_lcb_one_sub_det M hM
  have hGu : IsUnit (1 - M).det := isUnit_iff_ne_zero.mpr hG
  have hTG : (1 + M) * (1 - M)⁻¹ * (1 - M) = 1 + M := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hGu, Matrix.mul_one]
  set f := algebraMap ℝ ℂ
  set T := (1 + M) * (1 - M)⁻¹
  set M' := M.map f
  have hmap : ∀ A B : Matrix (Fin n) (Fin n) ℝ, (A * B).map f = A.map f * B.map f :=
    fun A B => Matrix.map_mul
  have hTG' : T.map f * (1 - M') = 1 + M' := by
    have h1 : (1 - M).map f = 1 - M' := by
      rw [Matrix.map_sub _ (fun a b => map_sub _ a b)]; simp [M']
    have h2 : (1 + M).map f = 1 + M' := by
      rw [Matrix.map_add _ (fun a b => map_add _ a b)]; simp [M']
    rw [← h1, ← h2, ← hmap, hTG]
  rw [aux_lcb_mem_spec'] at hz
  have hdet : ((z - 1) • (1 : Matrix (Fin n) (Fin n) ℂ) - (z + 1) • M').det = 0 := by
    have : (z • (1 : Matrix (Fin n) (Fin n) ℂ) - T.map f) * (1 - M')
        = (z - 1) • (1 : Matrix (Fin n) (Fin n) ℂ) - (z + 1) • M' := by
      rw [Matrix.sub_mul, hTG', Matrix.smul_mul, Matrix.one_mul, smul_sub, sub_smul, add_smul,
        one_smul, one_smul]
      abel
    rw [← this, Matrix.det_mul, hz, zero_mul]
  by_contra hlt
  push Not at hlt
  by_cases hz1 : z + 1 = 0
  · have hz' : z = -1 := by linear_combination hz1
    rw [hz1, zero_smul, sub_zero, Matrix.det_smul, Matrix.det_one, mul_one, hz'] at hdet
    norm_num at hdet
  · set μ := (z - 1) / (z + 1)
    have hμ : μ ∈ spectrum ℂ M' := by
      rw [aux_lcb_mem_spec']
      have : (z - 1) • (1 : Matrix (Fin n) (Fin n) ℂ) - (z + 1) • M'
          = (z + 1) • (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - M') := by
        rw [smul_sub, smul_smul]
        congr 2
        simp only [μ]
        field_simp
      rw [this, Matrix.det_smul] at hdet
      exact (mul_eq_zero.mp hdet).resolve_left (pow_ne_zero _ hz1)
    have := hM μ hμ
    have := aux_lcb_re_div z hlt hz1
    linarith


section gelfand
open scoped Matrix.Norms.L2Operator NNReal ENNReal

lemma aux_lcb_cplx_pow_tendsto {n : ℕ} [NeZero n] (N' : Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ z ∈ spectrum ℂ N', ‖z‖ < 1) :
    Tendsto (fun k : ℕ => ‖N' ^ k‖) atTop (𝓝 0) := by
  have hsr : spectralRadius ℂ N' < ((1 : ℝ≥0) : ℝ≥0∞) :=
    spectrum.spectralRadius_lt_of_forall_lt N' (fun z hz => by
      have := hN z hz
      exact_mod_cast this)
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hsr
  have hg := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius N'
  have hev := hg.eventually (gt_mem_nhds hr1)
  have hr2' : (r : ℝ) < 1 := by exact_mod_cast hr2
  apply squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) _
    (tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg hr2')
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have h1 : ((‖N' ^ k‖₊ : ℝ≥0∞) ^ (1 / (k : ℝ))) ^ (k : ℝ) < (r : ℝ≥0∞) ^ (k : ℝ) :=
    ENNReal.rpow_lt_rpow hk hkpos
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hkpos.ne', ENNReal.rpow_one,
    ENNReal.rpow_natCast] at h1
  have h2 : ‖N' ^ k‖₊ < r ^ k := by exact_mod_cast h1
  have h3 : (‖N' ^ k‖₊ : ℝ) < ((r ^ k : ℝ≥0) : ℝ) := by exact_mod_cast h2
  simpa using h3.le


lemma aux_lcb_cplx_pow_tendsto' {n : ℕ} [NeZero n] (N' : Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ z ∈ spectrum ℂ N', ‖z‖ < 1) (i j : Fin n) :
    Tendsto (fun k : ℕ => (N' ^ k) i j) atTop (𝓝 0) := by
  have h := tendsto_zero_iff_norm_tendsto_zero.mpr (aux_lcb_cplx_pow_tendsto N' hN)
  have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) :=
    (continuous_apply j).comp (continuous_apply i)
  have := (hc.tendsto 0).comp h
  exact this

end gelfand


lemma aux_lcb_pow_tendsto {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ z ∈ spectrum ℂ (N.map (algebraMap ℝ ℂ)), ‖z‖ < 1) :
    Tendsto (fun k : ℕ => N ^ k) atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (fun k : ℕ => N ^ k) = fun _ => 0 := funext fun _ => Subsingleton.elim _ _
    rw [this]; exact tendsto_const_nhds
  have : NeZero n := ⟨hn.ne'⟩
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  have h := aux_lcb_cplx_pow_tendsto' (N.map (algebraMap ℝ ℂ)) hN i j
  have h2 := (Complex.continuous_re.tendsto 0).comp h
  have hk : ∀ k : ℕ, ((N.map (algebraMap ℝ ℂ)) ^ k) i j = (((N ^ k) i j : ℝ) : ℂ) := by
    intro k
    have : (N.map (algebraMap ℝ ℂ)) ^ k = (N ^ k).map (algebraMap ℝ ℂ) := by
      change ((algebraMap ℝ ℂ).mapMatrix N) ^ k = (algebraMap ℝ ℂ).mapMatrix (N ^ k)
      rw [map_pow]
    rw [this]; rfl
  simp only [Function.comp_def, hk, Complex.ofReal_re, Complex.zero_re] at h2
  exact h2

lemma aux_lcb_stein {n : ℕ} (M Y W : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M)
    (hY : M.transpose * Y + Y * M + W = 0) :
    Y - ((1 + M) * (1 - M)⁻¹).transpose * Y * ((1 + M) * (1 - M)⁻¹)
      = (2 : ℝ) • (((1 - M)⁻¹).transpose * W * (1 - M)⁻¹) := by
  have hGu : IsUnit (1 - M).det := isUnit_iff_ne_zero.mpr (aux_lcb_one_sub_det M hM)
  have hGGi : (1 - M) * (1 - M)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hGu
  set Gi := (1 - M)⁻¹
  have hW : W = -(M.transpose * Y + Y * M) := eq_neg_of_add_eq_zero_right hY
  have e1 : (1 - M).transpose * Y * (1 - M) - (1 + M).transpose * Y * (1 + M) = (2 : ℝ) • W := by
    rw [hW, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one, two_smul]
    noncomm_ring
  have e2 : Y = Gi.transpose * ((1 - M).transpose * Y * (1 - M)) * Gi := by
    have : Gi.transpose * (1 - M).transpose = 1 := by
      rw [← Matrix.transpose_mul, hGGi, Matrix.transpose_one]
    calc Y = (Gi.transpose * (1 - M).transpose) * Y * ((1 - M) * Gi) := by
            rw [this, hGGi, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have e3 : ((1 + M) * Gi).transpose * Y * ((1 + M) * Gi)
      = Gi.transpose * ((1 + M).transpose * Y * (1 + M)) * Gi := by
    rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  rw [e3, ← Matrix.smul_mul, ← Matrix.mul_smul, ← e1, Matrix.mul_sub, Matrix.sub_mul, ← e2]

lemma aux_lcb_quad {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    u ⬝ᵥ (A.transpose * B * A) *ᵥ u = (A *ᵥ u) ⬝ᵥ B *ᵥ (A *ᵥ u) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

lemma aux_lcb_lyap_psd {n : ℕ} (M Y W : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M)
    (hW : ∀ v, 0 ≤ v ⬝ᵥ W *ᵥ v) (hY : M.transpose * Y + Y * M + W = 0) :
    ∀ v, 0 ≤ v ⬝ᵥ Y *ᵥ v := by
  intro v
  set T := (1 + M) * (1 - M)⁻¹ with hT
  set Gi := (1 - M)⁻¹
  have hs := aux_lcb_stein M Y W hM hY
  have hs' : T.transpose * Y * T = Y - (2 : ℝ) • (Gi.transpose * W * Gi) := by
    rw [← hs]; abel
  have hq : ∀ u, (T *ᵥ u) ⬝ᵥ Y *ᵥ (T *ᵥ u) ≤ u ⬝ᵥ Y *ᵥ u := by
    intro u
    rw [← aux_lcb_quad, hs', Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, aux_lcb_quad]
    have := hW (Gi *ᵥ u)
    simp only [smul_eq_mul]
    linarith
  let q : ℕ → ℝ := fun k => (T ^ k *ᵥ v) ⬝ᵥ Y *ᵥ (T ^ k *ᵥ v)
  have hanti : Antitone q := by
    apply antitone_nat_of_succ_le
    intro k
    simp only [q]
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact hq _
  have htend := aux_lcb_pow_tendsto T (aux_lcb_T_spec M hM)
  have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => (A *ᵥ v) ⬝ᵥ Y *ᵥ (A *ᵥ v)) := by
    fun_prop
  have h1 := (hc.tendsto 0).comp htend
  simp only [Matrix.zero_mulVec, Matrix.mulVec_zero, dotProduct_zero] at h1
  have := hanti.le_of_tendsto h1 0
  simpa [q] using this


end Prove2Me.Mrfancypants.LyapunovPositivity

namespace Queelius.LQRIntegral
open Matrix FatkhullinPolyak.Flow Queelius.LQRTrace
open Prove2Me.Mrfancypants.LyapunovPositivity
set_option maxHeartbeats 1500000
variable {n m r : ℕ}

theorem lyapX_posSemidef
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosSemidef) (hR : R.PosSemidef)
    (K : Matrix (Fin m) (Fin r) ℝ) (hK : K ∈ stabSet A B C) :
    (lyapX A B C Q R K).PosSemidef := by
  have hu := lyap_unit_of_hurwitz (closedLoop A B C K) hK
  have he : ∃! X : Matrix (Fin n) (Fin n) ℝ,
      (closedLoop A B C K)ᵀ * X + X * closedLoop A B C K + Cᵀ*Kᵀ*R*K*C+Q=0 := by
    simpa only [add_assoc] using lyap_unique_of_unit (closedLoop A B C K) (Cᵀ*Kᵀ*R*K*C+Q) hu
  have hX := lyapX_spec A B C Q R K he
  have hKC : (Cᵀ*Kᵀ*R*K*C).PosSemidef := by
    have hh := hR.conjTranspose_mul_mul_same (K*C)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_mul] at hh
    simpa only [Matrix.mul_assoc] using hh
  have hW := hKC.add hQ
  have hsym := lyapX_symmetric A B C Q R K
    (by simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.isHermitian)
    (by simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using hR.isHermitian) he
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using hsym
  · intro x
    exact aux_lcb_lyap_psd (closedLoop A B C K) (lyapX A B C Q R K) (Cᵀ*Kᵀ*R*K*C+Q)
      hK (fun v => by simpa using hW.dotProduct_mulVec_nonneg v)
      (by simpa only [add_assoc] using hX) x

theorem trace_mul_nonneg (X S : Matrix (Fin n) (Fin n) ℝ)
    (hX : X.PosSemidef) (hS : S.PosSemidef) : 0 ≤ trace (X*S) := by
  obtain ⟨k,v,hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hS
  rw [hv,Matrix.mul_sum,Matrix.trace_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [Matrix.mul_vecMulVec,Matrix.trace_vecMulVec]
  simpa only [star_trivial,dotProduct_comm] using hX.dotProduct_mulVec_nonneg (v i)

theorem cost_nonneg
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q Sig : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosSemidef) (hR : R.PosSemidef)
    (hSig : Sig.PosSemidef) (K : Matrix (Fin m) (Fin r) ℝ) (hK : K ∈ stabSet A B C) :
    0 ≤ cost A B C Q R Sig K := by
  exact trace_mul_nonneg _ _ (lyapX_posSemidef A B C Q R hQ hR K hK) hSig

end Queelius.LQRIntegral

namespace Queelius.LQRIntegral
open Matrix FatkhullinPolyak.Flow Queelius.LQRTrace Filter Topology
open scoped Matrix.Norms.Frobenius
attribute [local instance] matrixCLMNorm matrixCLMSpace matrixEndNormedRing matrixEndSummable
set_option maxHeartbeats 1500000
variable {n m r : ℕ}

theorem lyapY_eq_inverse
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (K : Matrix (Fin m) (Fin r) ℝ)
    (hu : IsUnit (lyapOp (closedLoop A B C K)ᵀ)) :
    lyapY A B C Sig K = (lyapOp (closedLoop A B C K)ᵀ).inverse (-Sig) := by
  have he : ∃! Y : Matrix (Fin n) (Fin n) ℝ,
      closedLoop A B C K * Y + Y * (closedLoop A B C K)ᵀ + Sig=0 := by
    simpa only [transpose_transpose] using lyap_unique_of_unit (closedLoop A B C K)ᵀ Sig hu
  have hY := lyapY_spec A B C Sig K he
  have hi := lyap_invertible_of_unit (closedLoop A B C K)ᵀ hu
  apply hi.injective
  rw [hi.self_apply_inverse]
  apply eq_neg_of_add_eq_zero_left
  simpa only [lyapOp_apply,transpose_transpose] using hY

theorem continuousAt_lyapY_of_unit
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (K : Matrix (Fin m) (Fin r) ℝ)
    (hu : IsUnit (lyapOp (closedLoop A B C K)ᵀ)) :
    ContinuousAt (lyapY A B C Sig) K := by
  have hL : Continuous (fun L => lyapOp (closedLoop A B C L)ᵀ) := by
    apply (lyapOpLinear (n:=n)).continuous.comp
    unfold closedLoop
    fun_prop
  have hi := (lyap_invertible_of_unit (closedLoop A B C K)ᵀ hu).contDiffAt_map_inverse (n:=0)
  have hh : ContinuousAt (fun L => (lyapOp (closedLoop A B C L)ᵀ).inverse (-Sig)) K :=
    (hi.continuousAt.comp (x:=K) hL.continuousAt).clm_apply continuousAt_const
  apply hh.congr_of_eventuallyEq
  filter_upwards [hL.continuousAt.eventually (Units.isOpen.mem_nhds hu)] with L hLu
  exact lyapY_eq_inverse A B C Sig L hLu

theorem continuousAt_grad_of_stable
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q Sig : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin m) (Fin r) ℝ)
    (hK : K ∈ stabSet A B C) : ContinuousAt (grad A B C Q R Sig) K := by
  have hu := lyap_unit_of_hurwitz (closedLoop A B C K) hK
  have hX := (contDiffAt_lyapX_of_unit A B C Q R K hu 0).continuousAt
  have hY := continuousAt_lyapY_of_unit A B C Sig K (lyap_unit_transpose _ hu)
  unfold grad
  fun_prop

theorem continuous_frobNorm {p q : ℕ} :
    Continuous (frobNorm (p:=p) (q:=q)) := by
  unfold frobNorm
  fun_prop

end Queelius.LQRIntegral

namespace Queelius.LQRIntegral
open Matrix FatkhullinPolyak.Flow Queelius.LQREnergy
open Set MeasureTheory
open scoped Matrix.Norms.Frobenius
set_option maxHeartbeats 1500000
variable {n m r : ℕ}

theorem flow_continuous
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q Sig : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (K₀ : Matrix (Fin m) (Fin r) ℝ)
    (K : ℝ → Matrix (Fin m) (Fin r) ℝ) (hK : IsGradFlow A B C Q R Sig K₀ K) :
    ContinuousOn K (Ici 0) := by
  intro t ht
  exact (matrix_derivative_of_entries K (-(grad A B C Q R Sig (K t))) (Ici 0) t (hK.2 t ht).2).continuousWithinAt

theorem flow_squared_gradient_continuous
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q Sig : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (K₀ : Matrix (Fin m) (Fin r) ℝ)
    (K : ℝ → Matrix (Fin m) (Fin r) ℝ) (hK : IsGradFlow A B C Q R Sig K₀ K) :
    ContinuousOn (fun t => frobNorm (grad A B C Q R Sig (K t))^2) (Ici 0) := by
  intro t ht
  have hKC := flow_continuous A B C Q Sig R K₀ K hK t ht
  have hg := (continuousAt_grad_of_stable A B C Q Sig R (K t) (hK.2 t ht).1).comp_continuousWithinAt hKC
  exact (continuous_frobNorm.continuousAt.comp_continuousWithinAt hg).pow 2

theorem flow_integral_identity
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef)
    (K₀ : Matrix (Fin m) (Fin r) ℝ) (K : ℝ → Matrix (Fin m) (Fin r) ℝ)
    (hK : IsGradFlow A B C Q R Sig K₀ K) (T : ℝ) (hT : 0 ≤ T) :
    cost A B C Q R Sig K₀ - cost A B C Q R Sig (K T) =
      ∫ t in (0:ℝ)..T, frobNorm (grad A B C Q R Sig (K t))^2 := by
  have hd := flow_energy_identity A B C Q R Sig hQ hR hSig K₀ K hK
  have hc : ContinuousOn (fun t => cost A B C Q R Sig (K t)) (Icc 0 T) := by
    intro t ht
    exact (hd t ht.1).continuousWithinAt.mono (fun _ hh => hh.1)
  have hg : ContinuousOn (fun t => frobNorm (grad A B C Q R Sig (K t))^2) (Icc 0 T) :=
    (flow_squared_gradient_continuous A B C Q Sig R K₀ K hK).mono (fun _ hh => hh.1)
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT hc
    (fun t ht => (hd t ht.1.le).mono (fun x hx => le_trans ht.1.le hx.le))
    (ContinuousOn.intervalIntegrable_of_Icc hT hg.neg)
  rw [intervalIntegral.integral_neg,hK.1] at he
  linarith

theorem exists_energy_le_average
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q Sig : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (K₀ : Matrix (Fin m) (Fin r) ℝ)
    (K : ℝ → Matrix (Fin m) (Fin r) ℝ) (hK : IsGradFlow A B C Q R Sig K₀ K)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ t ∈ Icc (0:ℝ) T, T*frobNorm (grad A B C Q R Sig (K t))^2 ≤
      ∫ s in (0:ℝ)..T, frobNorm (grad A B C Q R Sig (K s))^2 := by
  have hc : ContinuousOn (fun t => frobNorm (grad A B C Q R Sig (K t))^2) (uIcc 0 T) := by
    rw [uIcc_of_le hT]
    exact (flow_squared_gradient_continuous A B C Q Sig R K₀ K hK).mono (fun _ hh => hh.1)
  obtain ⟨t,ht,he⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg hc
    (intervalIntegrable_const (μ:=volume) (a:=0) (b:=T) (c:=(1:ℝ))) (fun _ _ => zero_le_one)
  refine ⟨t,by simpa [uIcc_of_le hT] using ht,?_⟩
  simpa only [mul_one,one_mul,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm] using he.symm.le

end Queelius.LQRIntegral

open FatkhullinPolyak.Flow Queelius.LQRIntegral

open Matrix

theorem solution {n m r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin r) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef)
    (K₀ : Matrix (Fin m) (Fin r) ℝ) (K : ℝ → Matrix (Fin m) (Fin r) ℝ)
    (hK : IsGradFlow A B C Q R Sig K₀ K) (T : ℝ) (hT : 0 ≤ T) :
    cost A B C Q R Sig K₀ - cost A B C Q R Sig (K T) ≤ cost A B C Q R Sig K₀ ∧
      cost A B C Q R Sig K₀ - cost A B C Q R Sig (K T) =
        ∫ t in (0 : ℝ)..T, frobNorm (grad A B C Q R Sig (K t)) ^ 2 ∧
      ∃ t ∈ Set.Icc (0 : ℝ) T,
        T * frobNorm (grad A B C Q R Sig (K t)) ^ 2 ≤
          ∫ s in (0 : ℝ)..T, frobNorm (grad A B C Q R Sig (K s)) ^ 2 := by
  refine ⟨?_, flow_integral_identity A B C Q R Sig hQ hR hSig K₀ K hK T hT,
    exists_energy_le_average A B C Q Sig R K₀ K hK T hT⟩
  have hh := cost_nonneg A B C Q Sig R hQ.posSemidef hR.posSemidef hSig.posSemidef
    (K T) (hK.2 T hT).1
  linarith


