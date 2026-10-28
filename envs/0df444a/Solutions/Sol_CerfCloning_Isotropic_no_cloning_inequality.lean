-- Prove2me | solution 1 for CerfCloning.Isotropic.no_cloning_inequality
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:32:13.361597+00:00
-- url     : https://prove2.me/submissions/043d26f1-1ca5-4d92-acc1-72ca44fcae77

import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QAlgorithms_Defs_Search
import Definitions.Def_QAlgorithms_Defs_Adversary
import Definitions.Def_QAlgorithms_Defs_Polynomial
import Definitions.Def_QAlgorithms_Defs_CompressedOracle
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Defs_Walk
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_LinearSystems
import Definitions.Def_QAlgorithms_Defs_SchurShapes
import Definitions.Def_QAlgorithms_Defs_Stabilizer
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QAlgorithms_Defs_SDP
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_QAlgorithms_Defs_Learning
import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QECC
import Definitions.Def_QAlgorithms_Defs_BinaryStabilizer
import Definitions.Def_QAlgorithms_Defs_LocCircuit
import Definitions.Def_QAlgorithms_Defs_FaultTolerance
import Definitions.Def_QAlgorithms_Defs_FTCircuit
import Definitions.Def_QAlgorithms_Defs_CircuitResources
import Definitions.Def_QAlgorithms_Defs_PhaseOracles
import Definitions.Def_QAlgorithms_Defs_ConvexOpt
import Definitions.Def_QAlgorithms_Defs_QAOA
import Definitions.Def_QAlgorithms_Defs_AdaptiveQuery
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_LearningSeparation
import Definitions.Def_QAlgorithms_Defs_PACSampleComplexity
import Definitions.Def_QAlgorithms_Defs_TensorCode
import Definitions.Def_QAlgorithms_Defs_LeftRightComplex
import Definitions.Def_QAlgorithms_Defs_TannerDecoder
import Definitions.Def_QAlgorithms_Defs_SpectralFilter
import Definitions.Def_QAlgorithms_Defs_LaurentQSP
import Definitions.Def_QAlgorithms_Defs_DQI
import Definitions.Def_QAlgorithms_Defs_ApproxCounting
import Definitions.Def_QAlgorithms_Defs_IQAE
import Definitions.Def_QAlgorithms_Defs_StabilizerLearning
import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_CerfCloning_Isotropic_Model
import Init
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Complex.Basic
import Mathlib
import Mathlib.Combinatorics.Young.YoungDiagram




section
noncomputable section
open scoped InnerProductSpace
namespace Queelius.QuantumCloning

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Two isometric ranges meeting at a constant angle, with an orthogonal remainder. -/
theorem isoclinic_sum_norm (U V : E→ₗ[ℝ] F) (r : ℝ)
    (hU : ∀x y,⟪U x,U y⟫_ℝ=⟪x,y⟫_ℝ) (hV : ∀x y,⟪V x,V y⟫_ℝ=⟪x,y⟫_ℝ)
    (hUV : ∀x y,⟪U x,V y⟫_ℝ=r*⟪x,y⟫_ℝ)
    (u v : E) (w : F) (hUw : ∀x,⟪U x,w⟫_ℝ=0) (hVw : ∀x,⟪V x,w⟫_ℝ=0) :
    ‖U u+V v+w‖^2=‖u‖^2+‖v‖^2+2*r*⟪u,v⟫_ℝ+‖w‖^2 := by
  have hu : ‖U u‖^2=‖u‖^2 := by rw [←real_inner_self_eq_norm_sq,hU,real_inner_self_eq_norm_sq]
  have hv : ‖V v‖^2=‖v‖^2 := by rw [←real_inner_self_eq_norm_sq,hV,real_inner_self_eq_norm_sq]
  simp only [norm_add_sq_real,inner_add_left,hUV,hUw,hVw,hu,hv]
  ring

theorem isoclinic_residual_norm (U V : E→ₗ[ℝ] F) (r : ℝ)
    (hU : ∀x y,⟪U x,U y⟫_ℝ=⟪x,y⟫_ℝ) (hV : ∀x y,⟪V x,V y⟫_ℝ=⟪x,y⟫_ℝ)
    (hUV : ∀x y,⟪U x,V y⟫_ℝ=r*⟪x,y⟫_ℝ)
    (v : E) (w : F) (hUw : ∀x,⟪U x,w⟫_ℝ=0) (hVw : ∀x,⟪V x,w⟫_ℝ=0) :
    ‖V v-r • U v+w‖^2=(1-r^2)*‖v‖^2+‖w‖^2 := by
  have hVU : ⟪V v,U v⟫_ℝ=r*⟪v,v⟫_ℝ := by rw [real_inner_comm,hUV]
  rw [←real_inner_self_eq_norm_sq]
  simp only [inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,hU,hV,hUV,hVU,hUw,hVw]
  have hwU : ⟪w,U v⟫_ℝ=0 := by rw [real_inner_comm,hUw]
  have hwV : ⟪w,V v⟫_ℝ=0 := by rw [real_inner_comm,hVw]
  rw [hwU,hwV,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  ring

/-- A geometric tradeoff for the two projection errors, independent of a channel ansatz. -/
theorem isoclinic_error_tradeoff (U V : E→ₗ[ℝ] F) (r : ℝ) (hr : 0≤r) (hr1 : r<1)
    (hU : ∀x y,⟪U x,U y⟫_ℝ=⟪x,y⟫_ℝ) (hV : ∀x y,⟪V x,V y⟫_ℝ=⟪x,y⟫_ℝ)
    (hUV : ∀x y,⟪U x,V y⟫_ℝ=r*⟪x,y⟫_ℝ)
    (u v : E) (w : F) (hUw : ∀x,⟪U x,w⟫_ℝ=0) (hVw : ∀x,⟪V x,w⟫_ℝ=0) :
    (1-r^2)*‖U u+V v+w‖^2≤
      ‖V v-r • U v+w‖^2+‖U u-r • V u+w‖^2+
        2*r*‖V v-r • U v+w‖*‖U u-r • V u+w‖ := by
  have ha : 0<1-r^2 := by nlinarith
  have hVU (x y : E) : ⟪V x,U y⟫_ℝ=r*⟪x,y⟫_ℝ := by
    rw [real_inner_comm,hUV,real_inner_comm x y]
  have hsum:=isoclinic_sum_norm U V r hU hV hUV u v w hUw hVw
  have heA:=isoclinic_residual_norm U V r hU hV hUV v w hUw hVw
  have heB:=isoclinic_residual_norm V U r hV hU hVU u w hVw hUw
  let ea := ‖V v-r • U v+w‖
  let eb := ‖U u-r • V u+w‖
  have hA : (1-r^2)*‖v‖^2≤ea^2 := by dsimp [ea]; nlinarith [sq_nonneg ‖w‖]
  have hB : (1-r^2)*‖u‖^2≤eb^2 := by dsimp [eb]; nlinarith [sq_nonneg ‖w‖]
  have hprod:=mul_le_mul hA hB (by positivity : 0≤(1-r^2)*‖u‖^2) (sq_nonneg ea)
  have hnorm : (1-r^2)*‖u‖*‖v‖≤ea*eb := by
    have ha0 : 0≤ea := norm_nonneg _
    have hb0 : 0≤eb := norm_nonneg _
    have hp0 : 0≤(1-r^2)*‖u‖*‖v‖ := by positivity
    nlinarith [mul_nonneg ha0 hb0]
  have hinner : (1-r^2)*⟪u,v⟫_ℝ≤ea*eb :=
    (mul_le_mul_of_nonneg_left (real_inner_le_norm u v) ha.le).trans (by nlinarith [hnorm])
  have hcross:=mul_le_mul_of_nonneg_left hinner (by positivity : 0≤2*r)
  change (1-r^2)*‖U u+V v+w‖^2≤ea^2+eb^2+2*r*ea*eb
  change ea^2=_ at heA
  change eb^2=_ at heB
  rw [hsum]
  nlinarith [sq_nonneg ‖w‖,mul_nonneg (sq_nonneg r) (sq_nonneg ‖w‖)]
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped InnerProductSpace
namespace Queelius.QuantumCloning

theorem euclidean_real_inner {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℂ ι) :
    ⟪x,y⟫_ℝ=(⟪x,y⟫_ℂ).re := by
  simp [PiLp.inner_apply,real_inner_eq_re_inner ℂ]
end Queelius.QuantumCloning

end



section
noncomputable section
open scoped InnerProductSpace
namespace Queelius.QuantumCloning
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem gram_pair_solve (r : ℝ) (hr : 1-r^2≠0) (a b : E) :
    (1-r^2)⁻¹ • (a-r • b)+r • ((1-r^2)⁻¹ • (b-r • a))=a := by
  calc
    _ = ((1-r^2)⁻¹*(1-r^2)) • a := by module
    _ = a := by rw [inv_mul_cancel₀ hr,one_smul]

theorem isoclinic_projection_tradeoff (U V : E→ₗ[ℝ] F) (A B : F→ₗ[ℝ] E)
    (r : ℝ) (hr : 0≤r) (hr1 : r<1)
    (hU : ∀x y,⟪U x,U y⟫_ℝ=⟪x,y⟫_ℝ) (hV : ∀x y,⟪V x,V y⟫_ℝ=⟪x,y⟫_ℝ)
    (hUV : ∀x y,⟪U x,V y⟫_ℝ=r*⟪x,y⟫_ℝ)
    (hA : ∀x y,⟪U x,y⟫_ℝ=⟪x,A y⟫_ℝ)
    (hB : ∀x y,⟪V x,y⟫_ℝ=⟪x,B y⟫_ℝ)
    (hAU : ∀x,A (U x)=x) (hBV : ∀x,B (V x)=x)
    (hAV : ∀x,A (V x)=r • x) (hBU : ∀x,B (U x)=r • x) (x : F) :
    (1-r^2)*‖x‖^2≤‖x-U (A x)‖^2+‖x-V (B x)‖^2+
      2*r*‖x-U (A x)‖*‖x-V (B x)‖ := by
  have hden : 1-r^2≠0 := by nlinarith
  let u := (1-r^2)⁻¹ • (A x-r • B x)
  let v := (1-r^2)⁻¹ • (B x-r • A x)
  let w := x-U u-V v
  have hu : u+r • v=A x := gram_pair_solve r hden (A x) (B x)
  have hv : v+r • u=B x := gram_pair_solve r hden (B x) (A x)
  have hAw : A w=0 := by
    dsimp [w]
    rw [map_sub,map_sub,hAU,hAV,←hu]
    abel
  have hBw : B w=0 := by
    dsimp [w]
    rw [map_sub,map_sub,hBU,hBV,←hv]
    abel
  have hUw (z:E) : ⟪U z,w⟫_ℝ=0 := by rw [hA,hAw,inner_zero_right]
  have hVw (z:E) : ⟪V z,w⟫_ℝ=0 := by rw [hB,hBw,inner_zero_right]
  have hx : U u+V v+w=x := by dsimp [w]; abel
  have heA : V v-r • U v+w=x-U (A x) := by
    rw [←hu,map_add,U.map_smul r v]
    dsimp [w]
    abel
  have heB : U u-r • V u+w=x-V (B x) := by
    rw [←hv,map_add,V.map_smul r u]
    dsimp [w]
    abel
  simpa only [hx,heA,heB] using
    isoclinic_error_tradeoff U V r hr hr1 hU hV hUV u v w hUw hVw
end Queelius.QuantumCloning

end





















































section
noncomputable section
open scoped BigOperators

namespace Queelius.QuantumCloning
open CerfCloning.Isotropic

theorem norm_add_real_div_sq (z w : ℂ) (r : ℝ) (hr : r ≠ 0) :
    ‖z + w / (r : ℂ)‖^2 = ‖z‖^2 + 2/r*(z*star w).re + ‖w‖^2/r^2 := by
  simp [Complex.sq_norm,Complex.normSq_apply,Complex.div_re,Complex.div_im,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  field_simp
  <;> ring

theorem iso_sq_piece (N : ℕ) [NeZero N] (ahat a : ℂ) (m n : Fin N) :
    ‖isoAmplitude N ahat a m n‖^2 =
      (if m=0 ∧ n=0 then ‖ahat‖^2 + 2/(N:ℝ)*(ahat*star a).re else 0) +
        ‖a‖^2/(N:ℝ)^2 := by
  have hN : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  by_cases h : m=0 ∧ n=0
  · simpa [isoAmplitude,h] using norm_add_real_div_sq ahat a (N:ℝ) hN
  · simp [isoAmplitude,h,norm_div,Complex.norm_natCast,div_pow]

theorem isotropic_normalization (N : ℕ) [NeZero N] (ahat a : ℂ) :
    ∑ m, ∑ n, ‖isoAmplitude N ahat a m n‖^2 =
      ‖ahat‖^2 + 2/(N:ℝ)*(ahat*star a).re + ‖a‖^2 := by
  have hN : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simp_rw [iso_sq_piece,Finset.sum_add_distrib,ite_and]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',
    Finset.mem_univ,if_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp
  <;> ring

end Queelius.QuantumCloning

open CerfCloning.Isotropic in
theorem normalization_solution (N : ℕ) [NeZero N] (ahat a : ℂ) :
    ∑ m, ∑ n, ‖isoAmplitude N ahat a m n‖^2 =
      ‖ahat‖^2 + 2/(N:ℝ)*(ahat*star a).re + ‖a‖^2 :=
  Queelius.QuantumCloning.isotropic_normalization N ahat a

end

section
noncomputable section
open scoped Matrix ComplexOrder BigOperators

namespace Queelius.QuantumCloning
open CerfCloning.Isotropic

theorem root_zero (N : ℕ) : rootOfUnity N 0 = 1 := by
  simp [rootOfUnity]

theorem weyl_reference_action (N : ℕ) [NeZero N] (m n : Fin N) :
    (Matrix.kronecker (1 : Matrix (Fin N) (Fin N) ℂ) (weyl N m n)) *ᵥ
        (meState N 0 0 : Fin N × Fin N → ℂ) =
      (meState N m n : Fin N × Fin N → ℂ) := by
  funext p
  rcases p with ⟨r,s⟩
  simp [Matrix.mulVec,dotProduct,Matrix.kronecker_apply,Fintype.sum_prod_type,
    Matrix.one_apply,meState,weyl,root_zero,ite_mul,mul_ite,div_eq_mul_inv]
  rw [Finset.sum_eq_single r]
  · simp
  · intro x hx hxr
    simp [Ne.symm hxr]
  · simp

end Queelius.QuantumCloning

end

section
noncomputable section
open scoped Matrix ComplexOrder BigOperators

namespace Queelius.QuantumCloning
open CerfCloning.Isotropic

theorem root_norm (N k : ℕ) : ‖rootOfUnity N k‖ = 1 := by
  simp [rootOfUnity,Complex.norm_exp,Complex.div_re,Complex.mul_re,Complex.mul_im]

theorem entangled_norm_sq (N : ℕ) [NeZero N] (m n : Fin N) :
    ‖meState N m n‖^2 = 1 := by
  have hN : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type]
  simp [meState,apply_ite,norm_div,root_norm,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),div_pow,
    Real.sq_sqrt (Nat.cast_nonneg N),hN]

theorem entangled_norm (N : ℕ) [NeZero N] (m n : Fin N) :
    ‖meState N m n‖ = 1 := by
  have h := entangled_norm_sq N m n
  have hp := norm_nonneg (meState N m n)
  nlinarith

theorem different_shift_orthogonal (N : ℕ) [NeZero N] (m n m' n' : Fin N)
    (hm : m ≠ m') : inner ℂ (meState N m n) (meState N m' n') = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro p hp
  by_cases h : p.2 = p.1 + m
  · have hn : p.2 ≠ p.1 + m' := by
      intro h'
      exact hm (add_left_cancel (h.symm.trans h'))
    simp [meState,h,hn,hm]
  · simp [meState,h]

end Queelius.QuantumCloning

end

section
noncomputable section
open scoped BigOperators

namespace Queelius.QuantumCloning
open CerfCloning.Isotropic

/-- The ellipse bound for normalized amplitudes in the explicit isotropic ansatz. -/
theorem normalized_amplitude_ellipse (N : ℕ) [NeZero N] (ahat a : ℂ)
    (h : ∑ m, ∑ n, ‖isoAmplitude N ahat a m n‖^2 = 1) :
    1 ≤ ‖ahat‖^2 + 2/(N:ℝ)*‖ahat‖*‖a‖ + ‖a‖^2 := by
  rw [isotropic_normalization] at h
  have hc : (ahat * star a).re ≤ ‖ahat‖*‖a‖ := by
    simpa using Complex.re_le_norm (ahat * star a)
  have hp : 0 ≤ 2/(N:ℝ) := by positivity
  have hb := mul_le_mul_of_nonneg_left hc hp
  nlinarith

theorem normalized_amplitude_squared_ellipse (N : ℕ) [NeZero N] (ahat a : ℂ)
    (h : ∑ m, ∑ n, ‖isoAmplitude N ahat a m n‖^2 = 1) :
    1 ≤ ‖a‖^2 + 2/(N:ℝ)*Real.sqrt (‖a‖^2)*Real.sqrt (‖ahat‖^2) + ‖ahat‖^2 := by
  simpa [Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),mul_comm,mul_left_comm,
    add_comm,add_left_comm,add_assoc] using normalized_amplitude_ellipse N ahat a h

namespace Controls

theorem peak_normalization (N : ℕ) [NeZero N] (ahat : ℂ) :
    ∑ m, ∑ n, ‖isoAmplitude N ahat 0 m n‖^2 = ‖ahat‖^2 := by
  rw [isotropic_normalization]
  simp

theorem flat_normalization (N : ℕ) [NeZero N] (a : ℂ) :
    ∑ m, ∑ n, ‖isoAmplitude N 0 a m n‖^2 = ‖a‖^2 := by
  rw [isotropic_normalization]
  simp

theorem same_phase (N : ℕ) [NeZero N] :
    ∑ m, ∑ n, ‖isoAmplitude N 1 1 m n‖^2 = 2 + 2/(N:ℝ) := by
  rw [isotropic_normalization]
  norm_num
  ring

theorem opposite_phase (N : ℕ) [NeZero N] :
    ∑ m, ∑ n, ‖isoAmplitude N (-1) 1 m n‖^2 = 2 - 2/(N:ℝ) := by
  rw [isotropic_normalization]
  norm_num
  ring

theorem quarter_phase (N : ℕ) [NeZero N] :
    ∑ m, ∑ n, ‖isoAmplitude N Complex.I 1 m n‖^2 = 2 := by
  rw [isotropic_normalization]
  norm_num

theorem dimension_one_cancellation (a : ℂ) :
    ∑ m, ∑ n, ‖isoAmplitude 1 (-a) a m n‖^2 = 0 := by
  simp [isoAmplitude]

end Controls
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped Matrix ComplexOrder BigOperators
namespace Queelius.QuantumCloning
open CerfCloning.Isotropic

theorem root_nat_power (N a b : ℕ) : rootOfUnity N (a*b) = rootOfUnity N a ^ b := by
  unfold rootOfUnity
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem root_primitive (N : ℕ) [NeZero N] : IsPrimitiveRoot (rootOfUnity N 1) N := by
  simpa [rootOfUnity] using Complex.isPrimitiveRoot_exp N (NeZero.ne N)

theorem star_root_eq_inv (N a : ℕ) : star (rootOfUnity N a) = (rootOfUnity N a)⁻¹ := by
  have hn : Complex.normSq (rootOfUnity N a)=1 := by
    rw [Complex.normSq_eq_norm_sq, root_norm]
    norm_num
  simp [Complex.inv_def, hn, Complex.star_def]

theorem root_ne_zero (N a : ℕ) : rootOfUnity N a ≠ 0 := Complex.exp_ne_zero _

theorem phase_correlation (N : ℕ) [NeZero N] (n n' : Fin N) :
    (∑ j : Fin N, star (rootOfUnity N (j.val*n.val))*rootOfUnity N (j.val*n'.val)) =
      if n=n' then (N:ℂ) else 0 := by
  have hp (a : ℕ) : rootOfUnity N a = rootOfUnity N 1 ^ a := by
    simpa using root_nat_power N 1 a
  have hj (j : Fin N) (a : Fin N) :
      rootOfUnity N (j.val*a.val)=rootOfUnity N a.val ^ j.val := by
    rw [Nat.mul_comm]
    exact root_nat_power N a.val j.val
  simp_rw [star_root_eq_inv, hj, inv_mul_eq_div,← div_pow]
  by_cases hnn : n=n'
  · subst n'
    simp [root_ne_zero]
  · rw [if_neg hnn]
    let q := rootOfUnity N n'.val / rootOfUnity N n.val
    have hq : q ≠ 1 := by
      intro h
      have he : rootOfUnity N n'.val=rootOfUnity N n.val :=
        (div_eq_one_iff_eq (root_ne_zero N n.val)).mp h
      rw [hp n'.val,hp n.val] at he
      have hh := (root_primitive N).pow_inj n'.isLt n.isLt he
      exact hnn (Fin.ext hh.symm)
    have hpN (a : ℕ) : rootOfUnity N a ^ N=1 := by
      rw [hp,← pow_mul,Nat.mul_comm,pow_mul,(root_primitive N).pow_eq_one,one_pow]
    have hqN : q^N=1 := by dsimp [q]; rw [div_pow,hpN,hpN,div_self one_ne_zero]
    change (∑ j : Fin N, q^j.val)=0
    rw [Fin.sum_univ_eq_sum_range,geom_sum_eq hq,hqN]
    simp

end Queelius.QuantumCloning

end

section
noncomputable section
open scoped Matrix ComplexOrder BigOperators
namespace Queelius.QuantumCloning
open CerfCloning.Isotropic QAlgorithms

theorem same_shift_inner (N : ℕ) [NeZero N] (m n n' : Fin N) :
    inner ℂ (meState N m n) (meState N m n') =
      (∑ j : Fin N, star (rootOfUnity N (j.val*n.val))*rootOfUnity N (j.val*n'.val))/(N:ℂ) := by
  have hs : ((Real.sqrt N:ℝ):ℂ)*((Real.sqrt N:ℝ):ℂ)=(N:ℂ) := by
    rw [← Complex.ofReal_mul,← pow_two,Real.sq_sqrt (Nat.cast_nonneg N)]
    simp
  rw [PiLp.inner_apply,Fintype.sum_prod_type]
  simp [meState,RCLike.inner_apply,star_div,← Finset.sum_div,hs,Complex.star_def,mul_comm,div_mul_div_comm]

theorem bell_inner (N : ℕ) [NeZero N] (m n m' n' : Fin N) :
    inner ℂ (meState N m n) (meState N m' n') = if m=m' ∧ n=n' then 1 else 0 := by
  by_cases hm : m=m'
  · subst m'
    rw [same_shift_inner,phase_correlation]
    by_cases hn : n=n' <;> simp [hn,Nat.cast_ne_zero.mpr (NeZero.ne N)]
  · rw [different_shift_orthogonal N m n m' n' hm]
    simp [hm]

/-- A square family of orthonormal columns resolves the identity matrix. -/
theorem projector_resolution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → EuclideanSpace ℂ ι)
    (hv : ∀ i j, inner ℂ (v i) (v j) = if i=j then 1 else 0) :
    ∑ i, pureDensity (v i) = (1 : Matrix ι ι ℂ) := by
  let B : Matrix ι ι ℂ := fun r c => v c r
  have hcol : Bᴴ * B = 1 := by
    ext i j
    change (∑ k, star (v i k) * v j k) = if i=j then 1 else 0
    simpa [PiLp.inner_apply,RCLike.inner_apply,mul_comm,Complex.star_def] using hv i j
  have hrow : B*Bᴴ=1 := mul_eq_one_comm.mp hcol
  ext i j
  have h := congrArg (fun M : Matrix ι ι ℂ => M i j) hrow
  change (∑ k, v k i * star (v k j)) = _ at h
  simpa only [Matrix.sum_apply,pureDensity,Matrix.of_apply,Complex.star_def] using h

theorem bell_resolution (N : ℕ) [NeZero N] :
    ∑ m, ∑ n, pureDensity (meState N m n) = 1 := by
  have h := projector_resolution (fun p : Fin N × Fin N => meState N p.1 p.2) (by
    intro p q
    rcases p with ⟨m,n⟩
    rcases q with ⟨m',n'⟩
    simpa only [Prod.mk.injEq] using bell_inner N m n m' n')
  simpa only [Fintype.sum_prod_type] using h

end Queelius.QuantumCloning

theorem bell_solution (N : ℕ) [NeZero N] :
    (∀ m n m' n' : Fin N, inner ℂ (CerfCloning.Isotropic.meState N m n)
      (CerfCloning.Isotropic.meState N m' n') = if m=m' ∧ n=n' then 1 else 0) ∧
    ∑ m, ∑ n, QAlgorithms.pureDensity (CerfCloning.Isotropic.meState N m n) = 1 :=
  ⟨Queelius.QuantumCloning.bell_inner N,Queelius.QuantumCloning.bell_resolution N⟩

end

section
noncomputable section
open scoped Matrix ComplexOrder BigOperators
namespace Queelius.QuantumCloning
open CerfCloning.Isotropic

theorem fourier_kernel (N : ℕ) (m n x y : Fin N) :
    Complex.exp (2*Real.pi*Complex.I*(((n.val*x.val:ℕ):ℂ)-((m.val*y.val:ℕ):ℂ))/(N:ℂ)) =
      rootOfUnity N (x.val*n.val)*star (rootOfUnity N (y.val*m.val)) := by
  rw [star_root_eq_inv,←div_eq_mul_inv]
  unfold rootOfUnity
  rw [←Complex.exp_sub]
  congr 1
  push_cast
  ring

theorem phase_sum (N : ℕ) [NeZero N] (n : Fin N) :
    (∑ x : Fin N,rootOfUnity N (x.val*n.val))=if n=0 then (N:ℂ) else 0 := by
  simpa [root_zero,eq_comm] using phase_correlation N 0 n

theorem phase_star_sum (N : ℕ) [NeZero N] (m : Fin N) :
    (∑ y : Fin N,star (rootOfUnity N (y.val*m.val)))=if m=0 then (N:ℂ) else 0 := by
  have h:=congrArg star (phase_sum N m)
  simpa [map_sum,apply_ite] using h

theorem fourier_add (N : ℕ) (a b : Fin N → Fin N → ℂ) :
    fourierDual N (fun m n=>a m n+b m n)=fun m n=>fourierDual N a m n+fourierDual N b m n := by
  funext m n
  simp [fourierDual,mul_add,Finset.sum_add_distrib]

theorem fourier_peak (N : ℕ) [NeZero N] (a : ℂ) :
    fourierDual N (fun m n=>if m=0 ∧ n=0 then a else 0)=fun _ _=>a/(N:ℂ) := by
  funext m n
  simp [fourierDual,ite_and,mul_ite,div_eq_mul_inv,mul_comm]

theorem fourier_flat (N : ℕ) [NeZero N] (a : ℂ) :
    fourierDual N (fun _ _=>a/(N:ℂ))=fun m n=>if m=0 ∧ n=0 then a else 0 := by
  funext m n
  simp only [fourierDual,fourier_kernel]
  have he : (∑ x : Fin N, ∑ y : Fin N,
      rootOfUnity N (x.val*n.val)*star (rootOfUnity N (y.val*m.val))*(a/(N:ℂ))) =
      (∑ x : Fin N,rootOfUnity N (x.val*n.val)) *
      (∑ y : Fin N,star (rootOfUnity N (y.val*m.val))) * (a/(N:ℂ)) := by
    simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc]
    rw [Finset.sum_comm]
  rw [he,phase_sum,phase_star_sum]
  have hN : (N:ℂ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  by_cases hm : m=0 <;> by_cases hn : n=0 <;> simp [hm,hn]
  field_simp
  <;> ring

theorem fourier_isotropic (N : ℕ) [NeZero N] (ahat a : ℂ) :
    fourierDual N (isoAmplitude N ahat a)=isoAmplitude N a ahat := by
  unfold isoAmplitude
  rw [fourier_add,fourier_peak,fourier_flat]
  funext m n
  exact add_comm _ _
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped BigOperators
namespace Queelius.QuantumCloning
open CerfCloning.Isotropic

def phase (N : ℕ) (a b : Fin N) : ℂ := rootOfUnity N (a.val*b.val)

theorem phase_comm (N : ℕ) (a b : Fin N) : phase N a b=phase N b a := by
  simp [phase,Nat.mul_comm]

theorem root_order_power (N : ℕ) [NeZero N] (k : ℕ) : rootOfUnity N k ^ N=1 := by
  have hp : rootOfUnity N k=rootOfUnity N 1 ^ k := by simpa using root_nat_power N 1 k
  rw [hp,←pow_mul,Nat.mul_comm,pow_mul,(root_primitive N).pow_eq_one,one_pow]

@[simp] theorem phase_zero_right (N : ℕ) [NeZero N] (a : Fin N) : phase N a 0=1 := by
  simp [phase,root_zero]
@[simp] theorem phase_zero_left (N : ℕ) [NeZero N] (a : Fin N) : phase N 0 a=1 := by
  simp [phase,root_zero]

theorem phase_add_right (N : ℕ) [NeZero N] (a b c : Fin N) :
    phase N a (b+c)=phase N a b*phase N a c := by
  simp only [phase,root_nat_power,Fin.val_add]
  rw [←pow_eq_pow_mod (b.val+c.val) (root_order_power N a.val),pow_add]

theorem phase_add_left (N : ℕ) [NeZero N] (a b c : Fin N) :
    phase N (a+b) c=phase N a c*phase N b c := by
  rw [phase_comm N (a+b) c,phase_add_right,phase_comm N c a,phase_comm N c b]

theorem phase_neg_right (N : ℕ) [NeZero N] (a b : Fin N) :
    phase N a (-b)=star (phase N a b) := by
  have h := phase_add_right N a b (-b)
  rw [add_neg_cancel,phase_zero_right] at h
  have hi : phase N a (-b)=(phase N a b)⁻¹ := eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using h.symm)
  simpa only [phase,star_root_eq_inv] using hi

theorem phase_neg_left (N : ℕ) [NeZero N] (a b : Fin N) :
    phase N (-a) b=star (phase N a b) := by
  rw [phase_comm,phase_neg_right,phase_comm N b a]

theorem phase_sub_left (N : ℕ) [NeZero N] (a b c : Fin N) :
    phase N (a-b) c=phase N a c*star (phase N b c) := by
  rw [sub_eq_add_neg,phase_add_left,phase_neg_left]

theorem phase_correlation_rows (N : ℕ) [NeZero N] (a b : Fin N) :
    (∑ k : Fin N,star (phase N a k)*phase N b k)=if a=b then (N:ℂ) else 0 := by
  simp_rw [phase_comm N a,phase_comm N b]
  exact phase_correlation N a b
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped Matrix ComplexOrder BigOperators
namespace Queelius.QuantumCloning
open CerfCloning.Isotropic QAlgorithms

/-- Tracing an orthonormal second factor removes every cross term. -/
theorem trace_orthonormal {ι κ ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype ν]
    (A : ι → κ → ℂ) (B : ι → EuclideanSpace ℂ ν)
    (hB : ∀ i j, inner ℂ (B i) (B j) = if i=j then 1 else 0) (x y : κ) :
    (∑ z : ν, (∑ i, A i x * B i z) * star (∑ j, A j y * B j z)) =
      ∑ i, A i x * star (A i y) := by
  have hc (i j : ι) : (∑ z : ν, B i z * star (B j z)) = if i=j then 1 else 0 := by
    simpa [PiLp.inner_apply,RCLike.inner_apply,eq_comm] using hB j i
  simp only [Complex.star_def] at hc
  simp only [Complex.star_def,map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  calc
    _ = ∑ j, (A j x * star (A i y)) * ∑ z : ν, B j z * star (B i z) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      simp only [Complex.star_def]
      ring
    _ = _ := by simp [Complex.star_def,hc]

theorem reduced_bell_mixture (N : ℕ) [NeZero N] (a : Fin N → Fin N → ℂ) :
    reducedRA (hcmState N a) =
      ∑ m, ∑ n, ((‖a m n‖^2 : ℝ):ℂ) • pureDensity (meState N m n) := by
  ext x y
  have h := trace_orthonormal
    (fun p : Fin N × Fin N => fun z => a p.1 p.2 * meState N p.1 p.2 z)
    (fun p : Fin N × Fin N => meState N p.1 (-p.2))
    (by
      intro p q
      rcases p with ⟨m,n⟩
      rcases q with ⟨m',n'⟩
      simpa only [Prod.mk.injEq,neg_inj] using bell_inner N m (-n) m' (-n')) x y
  simp only [Fintype.sum_prod_type] at h
  have heval : (∑ m, ∑ n, ((‖a m n‖^2:ℝ):ℂ) • pureDensity (meState N m n)) x y =
      ∑ m, ∑ n, ((‖a m n‖^2:ℝ):ℂ) * (meState N m n x * star (meState N m n y)) := by
    calc
      _ = ∑ m, (∑ n, ((‖a m n‖^2:ℝ):ℂ) • pureDensity (meState N m n)) x y :=
        Matrix.sum_apply x y Finset.univ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Matrix.sum_apply]
        apply Finset.sum_congr rfl
        intro n hn
        rfl
  rw [heval]
  change (∑ z, (∑ m, ∑ n, a m n * meState N m n x * meState N m (-n) z) *
    star (∑ m, ∑ n, a m n * meState N m n y * meState N m (-n) z)) = _
  simp only [Fintype.sum_prod_type]
  rw [h]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [star_mul]
  have ha : a m n * star (a m n) = ((‖a m n‖^2:ℝ):ℂ) := by
    simpa [Complex.normSq_eq_norm_sq] using Complex.mul_conj (a m n)
  calc
    _ = (a m n * star (a m n))*(meState N m n x * star (meState N m n y)) := by ring
    _ = _ := by rw [ha]

end Queelius.QuantumCloning

end

section
noncomputable section
open scoped Matrix ComplexOrder BigOperators
namespace Queelius.QuantumCloning
open CerfCloning.Isotropic QAlgorithms

/-- Applying a matrix to the second register transports a rank-one density. -/
theorem tensor_conjugation_pure {R ι κ : Type*} [Fintype R] [DecidableEq R]
    [Fintype ι] [Fintype κ] (A : Matrix κ ι ℂ) (v : EuclideanSpace ℂ (R×ι)) :
    idTensorSuperop (R:=R) (conjSuperop A) (pureDensity v)=
      pureDensity (WithLp.toLp 2 ((Matrix.kronecker (1:Matrix R R ℂ) A)*ᵥ(v:R×ι→ℂ))) := by
  have heval (p : R×κ) :
      ((Matrix.kronecker (1:Matrix R R ℂ) A)*ᵥ(v:R×ι→ℂ)) p =
        ∑ i,A p.2 i*v (p.1,i) := by
    simp [Matrix.mulVec,dotProduct,Matrix.kronecker_apply,Fintype.sum_prod_type,
      Matrix.one_apply,ite_mul]
  ext p q
  change (∑ j,(∑ i,A p.2 i*(v (p.1,i)*star (v (q.1,j))))*star (A q.2 j)) =
    (((Matrix.kronecker (1:Matrix R R ℂ) A)*ᵥ(v:R×ι→ℂ)) p)*
      star (((Matrix.kronecker (1:Matrix R R ℂ) A)*ᵥ(v:R×ι→ℂ)) q)
  rw [heval,heval]
  simp only [map_sum,map_mul,Finset.mul_sum,Finset.sum_mul,Complex.star_def]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem weyl_reference_density (N : ℕ) [NeZero N] (m n : Fin N) :
    idTensorSuperop (R:=Fin N) (conjSuperop (weyl N m n)) (pureDensity (meState N 0 0))=
      pureDensity (meState N m n) := by
  rw [tensor_conjugation_pure,weyl_reference_action]

theorem heisenberg_reference_mixture (N : ℕ) [NeZero N] (p : Fin N→Fin N→ℝ) :
    idTensorSuperop (R:=Fin N) (heisenbergChannel N p) (pureDensity (meState N 0 0))=
      ∑ m,∑ n,((p m n:ℝ):ℂ) • pureDensity (meState N m n) := by
  ext x y
  have h (m n : Fin N) := congrArg (fun M : Matrix (Fin N×Fin N) (Fin N×Fin N) ℂ=>M x y)
    (weyl_reference_density N m n)
  simp only [idTensorSuperop,heisenbergChannel,Matrix.of_apply,Matrix.sum_apply,Matrix.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [←h m n]
  rfl
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped BigOperators
namespace Queelius.QuantumCloning
open CerfCloning.Isotropic

theorem bell_entry (N : ℕ) (m n r a : Fin N) :
    meState N m n (r,a)=if a=r+m then phase N r n/(Real.sqrt N:ℂ) else 0 := rfl

theorem hcm_coordinates (N : ℕ) [NeZero N] (α : Fin N→Fin N→ℂ) (r a b c : Fin N) :
    hcmState N α ((r,a),(b,c))=
      if c=b+(a-r) then (1/(N:ℂ))*∑ n,α (a-r) n*phase N (r-b) n else 0 := by
  have hs : (Real.sqrt N:ℂ)*(Real.sqrt N:ℂ)=(N:ℂ) := by
    rw [←Complex.ofReal_mul,←pow_two,Real.sq_sqrt (Nat.cast_nonneg N)]
    simp
  have ha : a=r+(a-r) := by abel
  unfold hcmState
  rw [Finset.sum_eq_single (a-r)]
  · by_cases hc : c=b+(a-r)
    · rw [if_pos hc,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [bell_entry,bell_entry,if_pos ha,if_pos hc,phase_neg_right,phase_sub_left]
      calc
        _ = (1/((Real.sqrt N:ℂ)*(Real.sqrt N:ℂ)))*
            (α (a-r) n*(phase N r n*star (phase N b n))) := by
          simp only [div_eq_mul_inv,mul_inv_rev]
          ring
        _ = _ := by rw [hs]
    · simp only [bell_entry,if_pos ha,if_neg hc,mul_zero,Finset.sum_const_zero]
  · intro m hm hne
    have hbad : a≠r+m := by
      intro he
      apply hne
      calc
        m=(r+m)-r := by abel
        _=a-r := by rw [he]
    simp [bell_entry,hbad]
  · simp
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped Matrix ComplexOrder BigOperators
namespace Queelius.QuantumCloning.Controls
open CerfCloning.Isotropic QAlgorithms Queelius.QuantumCloning

theorem one_bell_vector_not_complete :
    pureDensity (meState 2 0 0) ≠ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  intro h
  have hh := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ => M (0,1) (0,1)) h
  norm_num [pureDensity,meState,Matrix.one_apply] at hh

theorem dimension_one_resolution : pureDensity (meState 1 0 0) = 1 := by
  simpa using bell_resolution 1

theorem nonzero_phase_cancels (N : ℕ) [NeZero N] (n : Fin N) (hn : n ≠ 0) :
    (∑ j : Fin N, rootOfUnity N (j.val*n.val)) = 0 := by
  have h := phase_correlation N 0 n
  simpa [root_zero,Ne.symm hn] using h

end Queelius.QuantumCloning.Controls

end

section
noncomputable section
open scoped Matrix ComplexOrder BigOperators
namespace Queelius.QuantumCloning
open CerfCloning.Isotropic QAlgorithms

theorem isotropic_reduced_state (N : ℕ) [NeZero N] (ahat a : ℂ) :
    reducedRA (hcmState N (isoAmplitude N ahat a)) =
      (((‖ahat‖^2+2/(N:ℝ)*(ahat*star a).re:ℝ)):ℂ) • pureDensity (meState N 0 0) +
        ((‖a‖^2/(N:ℝ)^2:ℝ):ℂ) • (1:Matrix (Fin N×Fin N) (Fin N×Fin N) ℂ) := by
  rw [reduced_bell_mixture]
  simp_rw [iso_sq_piece,Complex.ofReal_add,add_smul,Finset.sum_add_distrib]
  have hdelta : (∑ m : Fin N, ∑ n : Fin N,
      ((if m=0 ∧ n=0 then ‖ahat‖^2+2/(N:ℝ)*(ahat*star a).re else 0:ℝ):ℂ) •
        pureDensity (meState N m n)) =
      ((‖ahat‖^2+2/(N:ℝ)*(ahat*star a).re:ℝ):ℂ) • pureDensity (meState N 0 0) := by
    simp [ite_and,apply_ite,ite_smul]
  rw [hdelta]
  simp_rw [←Finset.smul_sum]
  rw [bell_resolution]
  simp only [Complex.ofReal_add,add_smul]
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped Matrix ComplexOrder BigOperators
namespace Queelius.QuantumCloning
open CerfCloning.Isotropic QAlgorithms

/-- Finite Kraus maps are complex linear, independently of normalization. -/
noncomputable def krausLinear {K ι κ : Type*} [Fintype K] [Fintype ι]
    (E : K→Matrix κ ι ℂ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ where
  toFun := krausApply E
  map_add' := by intro X Y; simp [krausApply,Matrix.mul_add,Matrix.add_mul,Finset.sum_add_distrib]
  map_smul' := by intro c X; simp [krausApply,Matrix.mul_smul,Matrix.smul_mul,Finset.smul_sum]

noncomputable def depolarizingLinear (N : ℕ) [NeZero N] (p : ℝ) :
    Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ where
  toFun := QuditFidelity.depolarizingMap N (Nat.pos_of_neZero N) p
  map_add' := by intro X Y; simp [QuditFidelity.depolarizingMap,Matrix.trace_add,mul_add,add_smul,smul_add]; abel
  map_smul' := by
    intro c X
    simp [QuditFidelity.depolarizingMap,Matrix.trace_smul,smul_eq_mul,smul_add,smul_smul,
      mul_comm,mul_left_comm,mul_assoc]

theorem reference_block (N : ℕ) [NeZero N] (r s : Fin N) :
    (Matrix.of fun i j => pureDensity (meState N 0 0) (r,i) (s,j)) =
      (1/(N:ℂ)) • Matrix.single r s 1 := by
  have hs : ((Real.sqrt N:ℝ):ℂ)*((Real.sqrt N:ℝ):ℂ)=(N:ℂ) := by
    rw [←Complex.ofReal_mul,←pow_two,Real.sq_sqrt (Nat.cast_nonneg N)]; simp
  have hs' : ((Real.sqrt N:ℝ):ℂ)⁻¹*((Real.sqrt N:ℝ):ℂ)⁻¹=(N:ℂ)⁻¹ := by rw [←mul_inv,hs]
  ext i j
  by_cases hir : i=r
  · subst i
    by_cases hjs : j=s
    · subst j
      simp [pureDensity,meState,root_zero,Matrix.single_apply,Matrix.smul_apply,hs']
    · have hsj : s≠j := Ne.symm hjs
      simp [pureDensity,meState,root_zero,Matrix.single_apply,Matrix.smul_apply,hjs,hsj]
  · have hri : r≠i := Ne.symm hir
    simp [pureDensity,meState,root_zero,Matrix.single_apply,Matrix.smul_apply,hir,hri]

theorem reference_linear_entry (N : ℕ) [NeZero N] {κ : Type*}
    (L : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix κ κ ℂ) (r s : Fin N) (i j : κ) :
    idTensorSuperop (R:=Fin N) L (pureDensity (meState N 0 0)) (r,i) (s,j) =
      (1/(N:ℂ))*L (Matrix.single r s 1) i j := by
  change L (Matrix.of fun a b=>pureDensity (meState N 0 0) (r,a) (s,b)) i j = _
  rw [reference_block,map_smul]
  rfl

theorem reference_injective (N : ℕ) [NeZero N] {κ : Type*}
    (L M : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (h : idTensorSuperop (R:=Fin N) L (pureDensity (meState N 0 0))=
      idTensorSuperop (R:=Fin N) M (pureDensity (meState N 0 0))) : L=M := by
  have hu (r s : Fin N) : L (Matrix.single r s 1)=M (Matrix.single r s 1) := by
    ext i j
    have hh:=congrArg (fun X : Matrix (Fin N×κ) (Fin N×κ) ℂ=>X (r,i) (s,j)) h
    rw [reference_linear_entry,reference_linear_entry] at hh
    exact mul_left_cancel₀ (one_div_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N))) hh
  ext X i j
  have hx : X=∑ r : Fin N,∑ s : Fin N,X r s • Matrix.single r s 1 := by
    ext r s
    simp [Matrix.sum_apply,Matrix.smul_apply,Matrix.single_apply,ite_and]
  rw [hx]
  simp only [map_sum,map_smul,hu]
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped BigOperators
namespace Queelius.QuantumCloning
open CerfCloning.Isotropic QAlgorithms

theorem phase_sum_opposite (N : ℕ) [NeZero N] (x d : Fin N) :
    (∑ n : Fin N,phase N x n*phase N d n)=if x= -d then (N:ℂ) else 0 := by
  have h:=phase_correlation_rows N (-d) x
  simpa [phase_neg_left,mul_comm,eq_comm] using h

theorem fourier_row_contraction (N : ℕ) [NeZero N] (α : Fin N→Fin N→ℂ) (m d : Fin N) :
    (∑ n,fourierDual N α m n*phase N d n)=
      ∑ y,α (-d) y*star (phase N m y) := by
  simp only [fourierDual,fourier_kernel]
  change (∑ n,((1/(N:ℂ))*∑ x,∑ y,(phase N x n*star (phase N y m))*α x y)*phase N d n)=_
  have he : (∑ n,((1/(N:ℂ))*∑ x,∑ y,(phase N x n*star (phase N y m))*α x y)*phase N d n)=
      (1/(N:ℂ))*∑ x,∑ y,(α x y*star (phase N m y))*(∑ n,phase N x n*phase N d n) := by
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro n hn
    rw [phase_comm N y m]
    ring
  rw [he]
  simp_rw [phase_sum_opposite]
  have hN : (N:ℂ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simp [mul_ite,←Finset.sum_mul,←Finset.mul_sum,hN,mul_comm,mul_left_comm]

theorem fourier_exchange (N : ℕ) [NeZero N] (α : Fin N→Fin N→ℂ) :
    swapAB (hcmState N α)=hcmState N (fourierDual N α) := by
  funext p
  rcases p with ⟨⟨r,a⟩,⟨b,c⟩⟩
  change hcmState N α ((r,b),(a,c))=hcmState N (fourierDual N α) ((r,a),(b,c))
  rw [hcm_coordinates,hcm_coordinates]
  have he : a+(b-r)=b+(a-r) := by abel
  rw [he]
  split_ifs
  · rw [fourier_row_contraction]
    have hneg : -(r-b)=b-r := by abel
    rw [hneg]
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    have hr : r-a= -(a-r) := by abel
    rw [hr,phase_neg_left]
  · rfl

theorem reduced_second_bell_mixture (N : ℕ) [NeZero N] (α : Fin N→Fin N→ℂ) :
    reducedRB (hcmState N α)=
      ∑ m,∑ n,((‖fourierDual N α m n‖^2:ℝ):ℂ) • pureDensity (meState N m n) := by
  unfold reducedRB
  rw [fourier_exchange,reduced_bell_mixture]
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped Matrix ComplexOrder BigOperators
namespace Queelius.QuantumCloning
open CerfCloning.Isotropic QAlgorithms

theorem depolarizing_reference (N : ℕ) [NeZero N] (p : ℝ) :
    idTensorSuperop (R:=Fin N) (QuditFidelity.depolarizingMap N (Nat.pos_of_neZero N) p)
      (pureDensity (meState N 0 0)) =
      ((1-p:ℝ):ℂ) • pureDensity (meState N 0 0)+((p/(N:ℝ)^2:ℝ):ℂ) • 1 := by
  ext x y
  rcases x with ⟨r,i⟩
  rcases y with ⟨s,j⟩
  change idTensorSuperop (R:=Fin N) (depolarizingLinear N p) _ (r,i) (s,j)=_
  rw [reference_linear_entry]
  have hb := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ=>M i j) (reference_block N r s)
  change pureDensity (meState N 0 0) (r,i) (s,j)=(1/(N:ℂ))*Matrix.single r s 1 i j at hb
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,hb]
  change (1/(N:ℂ))*
      ((((p/(N:ℝ):ℝ):ℂ)*(Matrix.single r s (1:ℂ)).trace) • (1:Matrix (Fin N) (Fin N) ℂ)+
        ((1-p:ℝ):ℂ) • Matrix.single r s 1 : Matrix (Fin N) (Fin N) ℂ) i j = _
  by_cases hrs : r=s
  · subst s
    simp only [Matrix.trace_single_eq_same,mul_one,Matrix.add_apply,Matrix.smul_apply,
      smul_eq_mul,Matrix.one_apply,Matrix.single_apply,Prod.mk.injEq,true_and]
    by_cases hij : i=j <;> by_cases hri : r=i <;> by_cases hrj : r=j <;>
      simp [hij,hri,hrj,Complex.ofReal_div,Complex.ofReal_pow] <;> ring
  · simp only [Matrix.trace_single_eq_of_ne r s (1:ℂ) hrs,mul_zero,zero_smul,zero_add,
      Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Prod.mk.injEq,hrs,false_and,if_false,mul_zero,add_zero]
    ring

theorem depolarizing_determined_by_reference (N : ℕ) [NeZero N] (p : ℝ)
    (Φ : Superop (Fin N) (Fin N)) (hΦ : IsChannel Φ)
    (h : idTensorSuperop (R:=Fin N) Φ (pureDensity (meState N 0 0))=
      ((1-p:ℝ):ℂ) • pureDensity (meState N 0 0)+((p/(N:ℝ)^2:ℝ):ℂ) • 1) :
    Φ=QuditFidelity.depolarizingMap N (Nat.pos_of_neZero N) p := by
  obtain ⟨m,E,_,hE⟩:=hΦ
  have he : Φ=krausApply E:=funext hE
  rw [he,←depolarizing_reference] at h
  have hl := reference_injective N (krausLinear E) (depolarizingLinear N p) h
  exact he.trans (congrArg DFunLike.coe hl)
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped BigOperators
namespace Queelius.QuantumCloning
open CerfCloning.Isotropic

theorem hcm_amplitude_recovery (N : ℕ) [NeZero N] (α : Fin N→Fin N→ℂ) (m n : Fin N) :
    (∑ r,hcmState N α ((r,r+m),(0,m))*star (phase N r n))=α m n := by
  have he (r : Fin N) : hcmState N α ((r,r+m),(0,m))=
      (1/(N:ℂ))*∑ k,α m k*phase N r k := by
    rw [hcm_coordinates]
    simp
  simp_rw [he]
  have hsum : (∑ r,((1/(N:ℂ))*∑ k,α m k*phase N r k)*star (phase N r n))=
      (1/(N:ℂ))*∑ k,α m k*(∑ r,star (phase N r n)*phase N r k) := by
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [hsum]
  have hc (k : Fin N) : (∑ r,star (phase N r n)*phase N r k)=if n=k then (N:ℂ) else 0 :=
    phase_correlation N n k
  simp_rw [hc]
  simp [mul_ite,←Finset.sum_mul,Nat.cast_ne_zero.mpr (NeZero.ne N),mul_comm,mul_left_comm]

theorem hcm_injective (N : ℕ) [NeZero N] : Function.Injective (hcmState N) := by
  intro α β h
  funext m n
  rw [←hcm_amplitude_recovery N α m n,←hcm_amplitude_recovery N β m n,h]

@[simp] theorem swapAB_involution {N : ℕ} (Ψ : (Fin N×Fin N)×(Fin N×Fin N)→ℂ) :
    swapAB (swapAB Ψ)=Ψ := rfl

theorem fourier_involution (N : ℕ) [NeZero N] (α : Fin N→Fin N→ℂ) :
    fourierDual N (fourierDual N α)=α := by
  apply hcm_injective N
  rw [←fourier_exchange,←fourier_exchange,swapAB_involution]
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped Matrix ComplexOrder BigOperators
namespace Queelius.QuantumCloning.Controls
open CerfCloning.Isotropic QAlgorithms

theorem perfect_limit (N : ℕ) [NeZero N] :
    reducedRA (hcmState N (isoAmplitude N 1 0))=pureDensity (meState N 0 0) := by
  rw [isotropic_reduced_state]
  simp

theorem fully_mixed_limit (N : ℕ) [NeZero N] :
    reducedRA (hcmState N (isoAmplitude N 0 1))=
      ((1/(N:ℝ)^2:ℝ):ℂ) • (1:Matrix (Fin N×Fin N) (Fin N×Fin N) ℂ) := by
  rw [isotropic_reduced_state]
  simp

theorem peak_is_not_self_dual : fourierDual 2 (isoAmplitude 2 1 0)≠isoAmplitude 2 1 0 := by
  rw [fourier_isotropic]
  intro h
  have he:=congrArg (fun f : Fin 2→Fin 2→ℂ=>f 1 1) h
  norm_num [isoAmplitude] at he

/-- Reference-state equality alone does not identify an arbitrary nonlinear function. -/
def nonlinearImpostor : Superop (Fin 1) (Fin 1) := by
  classical
  exact fun X=>if X=1 then 1 else 0

theorem nonlinear_same_reference :
    idTensorSuperop (R:=Fin 1) nonlinearImpostor (pureDensity (meState 1 0 0))=
      idTensorSuperop (R:=Fin 1) (fun X=>X) (pureDensity (meState 1 0 0)) := by
  have hblock (r s : Fin 1) :
      (Matrix.of fun i j=>pureDensity (meState 1 0 0) (r,i) (s,j))=(1:Matrix (Fin 1) (Fin 1) ℂ) := by
    rw [reference_block]
    ext i j
    have hr : r=0:=Subsingleton.elim _ _
    have hs : s=0:=Subsingleton.elim _ _
    have hi : i=0:=Subsingleton.elim _ _
    have hj : j=0:=Subsingleton.elim _ _
    simp [hr,hs,hi,hj,Matrix.one_apply]
  ext x y
  change nonlinearImpostor (Matrix.of fun i j=>pureDensity (meState 1 0 0) (x.1,i) (y.1,j)) x.2 y.2 = _
  rw [hblock]
  simp only [nonlinearImpostor,if_pos rfl]
  change (1:Matrix (Fin 1) (Fin 1) ℂ) x.2 y.2 =
    (Matrix.of fun i j=>pureDensity (meState 1 0 0) (x.1,i) (y.1,j)) x.2 y.2
  rw [hblock]

theorem nonlinear_not_identity : nonlinearImpostor≠(fun X : Matrix (Fin 1) (Fin 1) ℂ=>X) := by
  intro h
  have hh:=congrArg (fun F : Superop (Fin 1) (Fin 1)=>F (2 • (1:Matrix (Fin 1) (Fin 1) ℂ)) 0 0) h
  have hn : (2 • (1:Matrix (Fin 1) (Fin 1) ℂ))≠1 := by
    intro he
    have hp:=congrArg (fun X : Matrix (Fin 1) (Fin 1) ℂ=>X 0 0) he
    norm_num at hp
  change (if 2 • (1:Matrix (Fin 1) (Fin 1) ℂ)=1 then (1:Matrix (Fin 1) (Fin 1) ℂ) else 0) 0 0=
    (2 • (1:Matrix (Fin 1) (Fin 1) ℂ)) 0 0 at hh
  rw [if_neg hn] at hh
  norm_num at hh
end Queelius.QuantumCloning.Controls

end

section
noncomputable section
open scoped BigOperators
namespace Queelius.QuantumCloning
open CerfCloning.Isotropic

theorem fourier_kernel_product (N : ℕ) (α : Fin N→Fin N→ℂ) (m n : Fin N) :
    fourierDual N α m n=(1/(N:ℂ))*∑ p : Fin N×Fin N,
      (phase N p.1 n*star (phase N p.2 m))*α p.1 p.2 := by
  simp only [fourierDual,fourier_kernel,Fintype.sum_prod_type,phase]

theorem fourier_self_adjoint (N : ℕ) (α β : Fin N→Fin N→ℂ) :
    (∑ p : Fin N×Fin N,star (α p.1 p.2)*fourierDual N β p.1 p.2)=
      ∑ p : Fin N×Fin N,star (fourierDual N α p.1 p.2)*β p.1 p.2 := by
  simp only [fourier_kernel_product,Complex.star_def,map_sum,map_mul,map_div,map_one,map_natCast,Complex.conj_conj,
    Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [phase_comm N q.2 p.1,phase_comm N p.2 q.1]
  simp [Complex.star_def]
  <;> ring

theorem fourier_inner_preserving (N : ℕ) [NeZero N] (α β : Fin N→Fin N→ℂ) :
    (∑ p : Fin N×Fin N,star (fourierDual N α p.1 p.2)*fourierDual N β p.1 p.2)=
      ∑ p : Fin N×Fin N,star (α p.1 p.2)*β p.1 p.2 := by
  rw [←fourier_self_adjoint,fourier_involution]

theorem fourier_norm_preserving (N : ℕ) [NeZero N] (α : Fin N→Fin N→ℂ) :
    (∑ m,∑ n,‖fourierDual N α m n‖^2)=∑ m,∑ n,‖α m n‖^2 := by
  have h:=fourier_inner_preserving N α α
  have hc (z : ℂ) : star z*z=((‖z‖^2:ℝ):ℂ) := by
    simpa [mul_comm,Complex.normSq_eq_norm_sq] using Complex.mul_conj z
  simp_rw [hc] at h
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type] at h
  exact_mod_cast h
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace Queelius.QuantumCloning
open CerfCloning.Isotropic QAlgorithms

theorem conj_conditional (p : Prop) [Decidable p] (u v : ℂ) :
    (starRingEnd ℂ) (if p then u else v)=if p then (starRingEnd ℂ) u else (starRingEnd ℂ) v := by
  split_ifs <;> rfl

def clonerKraus (N : ℕ) (u v : ℂ) (c : Fin N) : Matrix (Fin N×Fin N) (Fin N) ℂ :=
  fun p i=>(if p.1=i ∧ p.2=c then u else 0)+(if p.1=c ∧ p.2=i then v else 0)

theorem cloner_kraus_sum (N : ℕ) (u v : ℂ) :
    (∑ c,(clonerKraus N u v c)ᴴ*clonerKraus N u v c)=
      ((N:ℂ)*(star u*u+star v*v)+(star u*v+star v*u)) • (1:Matrix (Fin N) (Fin N) ℂ) := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,clonerKraus]
  simp [conj_conditional,map_add,add_mul,mul_add,Finset.sum_add_distrib,
    ite_and,ite_mul,mul_ite,Matrix.one_apply]
  <;> split_ifs <;> simp_all <;> ring

theorem cloner_apply_entry (N : ℕ) (u v : ℂ) (ρ : Matrix (Fin N) (Fin N) ℂ)
    (a b a' b' : Fin N) :
    krausApply (clonerKraus N u v) ρ (a,b) (a',b')=
      (u*star u)*ρ a a'*(if b=b' then 1 else 0)+
      (v*star v)*(if a=a' then 1 else 0)*ρ b b'+
      (u*star v)*ρ a b'*(if b=a' then 1 else 0)+
      (v*star u)*ρ b a'*(if a=b' then 1 else 0) := by
  simp only [krausApply,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,clonerKraus]
  simp [conj_conditional,map_add,add_mul,mul_add,Finset.sum_add_distrib,ite_and,ite_mul,mul_ite]
  <;> split_ifs <;> simp_all <;> ring
end Queelius.QuantumCloning

end

section
open scoped Matrix ComplexOrder BigOperators
open QAlgorithms CerfCloning.Isotropic

open CerfCloning.Isotropic

theorem isotropic_solution (N : ℕ) [NeZero N] (pa : ℝ) :
    idTensorSuperop (R := Fin N) (QuditFidelity.depolarizingMap N (Nat.pos_of_neZero N) pa)
        (pureDensity (meState N 0 0)) =
      ((1 - pa : ℝ) : ℂ) • pureDensity (meState N 0 0) + ((pa / (N : ℝ) ^ 2 : ℝ) : ℂ) • 1 ∧
    ∀ Φ : Superop (Fin N) (Fin N), IsChannel Φ →
      idTensorSuperop (R := Fin N) Φ (pureDensity (meState N 0 0)) =
        ((1 - pa : ℝ) : ℂ) • pureDensity (meState N 0 0) + ((pa / (N : ℝ) ^ 2 : ℝ) : ℂ) • 1 →
      Φ = QuditFidelity.depolarizingMap N (Nat.pos_of_neZero N) pa := by
  exact ⟨Queelius.QuantumCloning.depolarizing_reference N pa, Queelius.QuantumCloning.depolarizing_determined_by_reference N pa⟩



namespace CerfCloning.Isotropic

theorem eq_3_6 (N : ℕ) [NeZero N] (p : Fin N → Fin N → ℝ) :
    idTensorSuperop (R := Fin N) (heisenbergChannel N p) (pureDensity (meState N 0 0)) =
      ∑ m, ∑ n, ((p m n : ℝ) : ℂ) • pureDensity (meState N m n) := by
  exact Queelius.QuantumCloning.heisenberg_reference_mixture N p
end CerfCloning.Isotropic


namespace CerfCloning.Isotropic

theorem eq_3_18 (N : ℕ) [NeZero N] (ahat a : ℂ) :
    reducedRA (hcmState N (isoAmplitude N ahat a)) =
      (((‖ahat‖ ^ 2 + 2 / (N : ℝ) * (ahat * star a).re : ℝ)) : ℂ) • pureDensity (meState N 0 0) +
        ((‖a‖ ^ 2 / (N : ℝ) ^ 2 : ℝ) : ℂ) • 1 := by
  exact Queelius.QuantumCloning.isotropic_reduced_state N ahat a
end CerfCloning.Isotropic


namespace CerfCloning.Isotropic

theorem eq_3_19 (N : ℕ) [NeZero N] (ahat a : ℂ) :
    fourierDual N (isoAmplitude N ahat a) = isoAmplitude N a ahat := by
  exact Queelius.QuantumCloning.fourier_isotropic N ahat a
end CerfCloning.Isotropic


end

section
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace Queelius.QuantumCloning
open CerfCloning.Isotropic QAlgorithms

theorem cloner_output_A (N : ℕ) (u v : ℂ) (ρ : Matrix (Fin N) (Fin N) ℂ) :
    outputA (krausApply (clonerKraus N u v)) ρ=
      ((N:ℂ)*(u*star u)+u*star v+v*star u) • ρ +
      ((v*star v)*ρ.trace) • (1:Matrix (Fin N) (Fin N) ℂ) := by
  ext a a'
  change (∑ b,krausApply (clonerKraus N u v) ρ (a,b) (a',b))=_
  simp_rw [cloner_apply_entry]
  simp [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul,Matrix.trace,
    Matrix.one_apply,mul_ite,ite_mul]
  <;> split_ifs <;> simp_all <;> ring

theorem cloner_output_B (N : ℕ) (u v : ℂ) (ρ : Matrix (Fin N) (Fin N) ℂ) :
    outputB (krausApply (clonerKraus N u v)) ρ=
      ((N:ℂ)*(v*star v)+u*star v+v*star u) • ρ +
      ((u*star u)*ρ.trace) • (1:Matrix (Fin N) (Fin N) ℂ) := by
  ext b b'
  change (∑ a,krausApply (clonerKraus N u v) ρ (a,b) (a,b'))=_
  simp_rw [cloner_apply_entry]
  simp [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul,Matrix.trace,
    Matrix.one_apply,mul_ite,ite_mul]
  <;> split_ifs <;> simp_all <;> ring

theorem real_cloner_isotropic (N : ℕ) [NeZero N] (a b : ℝ)
    (hn : (N:ℝ)*(a^2+b^2)+2*a*b=1) :
    IsIsotropicCloner N (krausApply (clonerKraus N (a:ℂ) (b:ℂ))) ((N:ℝ)*b^2) ((N:ℝ)*a^2) := by
  have hN : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hc : (N:ℂ)*((a:ℂ)^2+(b:ℂ)^2)+2*(a:ℂ)*(b:ℂ)=1 := by exact_mod_cast hn
  refine ⟨⟨N,clonerKraus N (a:ℂ) (b:ℂ),?_,fun _=>rfl⟩,?_,?_⟩
  · unfold IsKrausFamily
    rw [cloner_kraus_sum]
    have he : (N:ℂ)*(star (a:ℂ)*(a:ℂ)+star (b:ℂ)*(b:ℂ))+
        (star (a:ℂ)*(b:ℂ)+star (b:ℂ)*(a:ℂ))=1 := by
      simp only [Complex.star_def,Complex.conj_ofReal]
      linear_combination hc
    rw [he,one_smul]
  · intro ρ
    rw [cloner_output_A]
    unfold QuditFidelity.depolarizingMap
    have hnoise : (N:ℝ)*b^2/(N:ℝ)=b^2 := by field_simp [hN]
    rw [hnoise]
    have hm : (N:ℂ)*((a:ℂ)*star (a:ℂ))+(a:ℂ)*star (b:ℂ)+(b:ℂ)*star (a:ℂ)=
        ((1-(N:ℝ)*b^2:ℝ):ℂ) := by
      push_cast
      simp only [Complex.star_def,Complex.conj_ofReal]
      linear_combination hc
    rw [hm]
    simp only [Complex.star_def,Complex.conj_ofReal,Complex.ofReal_pow,pow_two,Complex.ofReal_mul]
    exact add_comm _ _
  · intro ρ
    rw [cloner_output_B]
    unfold QuditFidelity.depolarizingMap
    have hnoise : (N:ℝ)*a^2/(N:ℝ)=a^2 := by field_simp [hN]
    rw [hnoise]
    have hm : (N:ℂ)*((b:ℂ)*star (b:ℂ))+(a:ℂ)*star (b:ℂ)+(b:ℂ)*star (a:ℂ)=
        ((1-(N:ℝ)*a^2:ℝ):ℂ) := by
      push_cast
      simp only [Complex.star_def,Complex.conj_ofReal]
      linear_combination hc
    rw [hm]
    simp only [Complex.star_def,Complex.conj_ofReal,Complex.ofReal_pow,pow_two,Complex.ofReal_mul]
    exact add_comm _ _
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace Queelius.QuantumCloning
open CerfCloning.Isotropic QAlgorithms

theorem boundary_scaled_normalization (N : ℕ) [NeZero N] (pa pb : ℝ)
    (ha : 0≤pa) (hb : 0≤pb)
    (he : pa+2/(N:ℝ)*(Real.sqrt pa*Real.sqrt pb)+pb=1) :
    (N:ℝ)*((Real.sqrt pb/Real.sqrt N)^2+(Real.sqrt pa/Real.sqrt N)^2)+
      2*(Real.sqrt pb/Real.sqrt N)*(Real.sqrt pa/Real.sqrt N)=1 := by
  have hN : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hs : Real.sqrt (N:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_neZero N)))
  have hsq := Real.sq_sqrt (Nat.cast_nonneg N)
  have hpa := Real.sq_sqrt ha
  have hpb := Real.sq_sqrt hb
  field_simp [hs,hN] at he ⊢
  nlinarith

theorem boundary_fraction (N : ℕ) [NeZero N] (p : ℝ) (hp : 0≤p) :
    (N:ℝ)*(Real.sqrt p/Real.sqrt N)^2=p := by
  rw [div_pow,Real.sq_sqrt hp,Real.sq_sqrt (Nat.cast_nonneg N)]
  exact mul_div_cancel₀ p (Nat.cast_ne_zero.mpr (NeZero.ne N))

theorem boundary_achievable (N : ℕ) [NeZero N] (pa pb : ℝ) (ha : 0≤pa) (hb : 0≤pb)
    (he : pa+2/(N:ℝ)*(Real.sqrt pa*Real.sqrt pb)+pb=1) :
    ∃ T : Superop (Fin N) (Fin N×Fin N),IsIsotropicCloner N T pa pb := by
  have h:=real_cloner_isotropic N (Real.sqrt pb/Real.sqrt N) (Real.sqrt pa/Real.sqrt N)
    (boundary_scaled_normalization N pa pb ha hb he)
  rw [boundary_fraction N pa ha,boundary_fraction N pb hb] at h
  exact ⟨_,h⟩
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace Queelius.QuantumCloning.Controls
open CerfCloning.Isotropic QAlgorithms

theorem zero_kraus_not_normalized (N : ℕ) [NeZero N] :
    ¬IsKrausFamily (clonerKraus N 0 0) := by
  intro h
  unfold IsKrausFamily at h
  rw [cloner_kraus_sum] at h
  have he:=congrArg (fun M : Matrix (Fin N) (Fin N) ℂ=>M 0 0) h
  norm_num at he

theorem boundary_alone_allows_negative_noise (N : ℕ) :
    (-1:ℝ)+2/(N:ℝ)*(Real.sqrt (-1)*Real.sqrt 2)+2=1 ∧ ¬0≤(-1:ℝ) := by
  norm_num

theorem perfect_first_output_exists (N : ℕ) [NeZero N] :
    ∃ T : Superop (Fin N) (Fin N×Fin N),IsIsotropicCloner N T 0 1 :=
  boundary_achievable N 0 1 (by norm_num) (by norm_num) (by norm_num)

theorem perfect_second_output_exists (N : ℕ) [NeZero N] :
    ∃ T : Superop (Fin N) (Fin N×Fin N),IsIsotropicCloner N T 1 0 :=
  boundary_achievable N 1 0 (by norm_num) (by norm_num) (by norm_num)
end Queelius.QuantumCloning.Controls

end

section
open CerfCloning.Isotropic QAlgorithms

theorem fourier_solution (N : ℕ) [NeZero N] (α : Fin N→Fin N→ℂ) :
    swapAB (hcmState N α)=hcmState N (fourierDual N α) :=
  Queelius.QuantumCloning.fourier_exchange N α

theorem boundary_clause (N : ℕ) [NeZero N] (_hN : 2≤N) :
    ∀ pa pb : ℝ, 0≤pa → 0≤pb → pa+2/(N:ℝ)*(Real.sqrt pa*Real.sqrt pb)+pb=1 →
      ∃ T : Superop (Fin N) (Fin N×Fin N),IsIsotropicCloner N T pa pb :=
  Queelius.QuantumCloning.boundary_achievable N

end

section
noncomputable section
open scoped InnerProductSpace BigOperators Matrix ComplexOrder
namespace Queelius.QuantumCloning
open CerfCloning.Isotropic QAlgorithms

abbrev CloneSpace (N m : ℕ) := EuclideanSpace ℂ (Fin m × (Fin N × Fin N) × Fin N)
abbrev BellCoeff (N m : ℕ) := EuclideanSpace ℂ (Fin m × Fin N)

def bellLiftA (N m : ℕ) : BellCoeff N m→ₗ[ℂ] CloneSpace N m where
  toFun v := WithLp.toLp 2 fun p=>if p.2.1.1=p.2.2 then v (p.1,p.2.1.2)/(Real.sqrt N:ℂ) else 0
  map_add' := by intro x y; ext p; by_cases h:p.2.1.1=p.2.2 <;> simp [h,add_div]
  map_smul' := by intro c x; ext p; by_cases h:p.2.1.1=p.2.2 <;> simp [h,mul_div_assoc]

def bellLiftB (N m : ℕ) : BellCoeff N m→ₗ[ℂ] CloneSpace N m where
  toFun v := WithLp.toLp 2 fun p=>if p.2.1.2=p.2.2 then v (p.1,p.2.1.1)/(Real.sqrt N:ℂ) else 0
  map_add' := by intro x y; ext p; by_cases h:p.2.1.2=p.2.2 <;> simp [h,add_div]
  map_smul' := by intro c x; ext p; by_cases h:p.2.1.2=p.2.2 <;> simp [h,mul_div_assoc]

def bellContractA (N m : ℕ) (x : CloneSpace N m) : BellCoeff N m :=
  WithLp.toLp 2 fun p=>(∑i : Fin N,x (p.1,(i,p.2),i))/(Real.sqrt N:ℂ)
def bellContractB (N m : ℕ) (x : CloneSpace N m) : BellCoeff N m :=
  WithLp.toLp 2 fun p=>(∑i : Fin N,x (p.1,(p.2,i),i))/(Real.sqrt N:ℂ)

@[simp] theorem bellLiftA_apply (N m : ℕ) (v : BellCoeff N m) (j : Fin m) (a b i : Fin N) :
    bellLiftA N m v (j,(a,b),i)=(if a=i then v (j,b)/(Real.sqrt N:ℂ) else 0) := rfl
@[simp] theorem bellLiftB_apply (N m : ℕ) (v : BellCoeff N m) (j : Fin m) (a b i : Fin N) :
    bellLiftB N m v (j,(a,b),i)=(if b=i then v (j,a)/(Real.sqrt N:ℂ) else 0) := rfl

theorem bellContractA_liftA (N m : ℕ) [NeZero N] (v : BellCoeff N m) :
    bellContractA N m (bellLiftA N m v)=v := by
  have hn : (N:ℂ)≠0 := by exact_mod_cast NeZero.ne N
  have hs : (Real.sqrt N:ℂ)^2=(N:ℂ) := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg N)
  ext p
  simp [bellContractA, div_div]
  field_simp [show (Real.sqrt N:ℂ)≠0 by exact_mod_cast Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (NeZero.pos N))]
  rw [hs]
  ring

theorem bellContractB_liftB (N m : ℕ) [NeZero N] (v : BellCoeff N m) :
    bellContractB N m (bellLiftB N m v)=v := by
  have hn : (N:ℂ)≠0 := by exact_mod_cast NeZero.ne N
  have hs : (Real.sqrt N:ℂ)^2=(N:ℂ) := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg N)
  ext p
  simp [bellContractB, div_div]
  field_simp [show (Real.sqrt N:ℂ)≠0 by exact_mod_cast Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (NeZero.pos N))]
  rw [hs]
  ring

theorem bellContractA_liftB (N m : ℕ) (v : BellCoeff N m) :
    bellContractA N m (bellLiftB N m v)=(1/(N:ℂ)) • v := by
  have hs : (Real.sqrt N:ℂ)*(Real.sqrt N:ℂ)=(N:ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (Nat.cast_nonneg N)
  ext p
  simp [bellContractA,div_div,hs]
  ring

theorem bellContractB_liftA (N m : ℕ) (v : BellCoeff N m) :
    bellContractB N m (bellLiftA N m v)=(1/(N:ℂ)) • v := by
  have hs : (Real.sqrt N:ℂ)*(Real.sqrt N:ℂ)=(N:ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (Nat.cast_nonneg N)
  ext p
  simp [bellContractB,div_div,hs]
  ring

end Queelius.QuantumCloning

end

section
noncomputable section
open scoped InnerProductSpace BigOperators
namespace Queelius.QuantumCloning

theorem bellLiftA_adjoint (N m : ℕ) (u : BellCoeff N m) (x : CloneSpace N m) :
    ⟪bellLiftA N m u,x⟫_ℂ=⟪u,bellContractA N m x⟫_ℂ := by
  simp [PiLp.inner_apply,RCLike.inner_apply,Fintype.sum_prod_type,
    bellLiftA,bellContractA,Finset.sum_mul,Finset.mul_sum,Finset.sum_div,apply_ite,mul_ite]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

theorem bellLiftB_adjoint (N m : ℕ) (u : BellCoeff N m) (x : CloneSpace N m) :
    ⟪bellLiftB N m u,x⟫_ℂ=⟪u,bellContractB N m x⟫_ℂ := by
  simp [PiLp.inner_apply,RCLike.inner_apply,Fintype.sum_prod_type,
    bellLiftB,bellContractB,Finset.sum_mul,Finset.mul_sum,Finset.sum_div,apply_ite,mul_ite]

  simp only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

end Queelius.QuantumCloning

end

section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProductSpace BigOperators
namespace Queelius.QuantumCloning

def bellAdjointA (N m : ℕ) : CloneSpace N m→ₗ[ℂ] BellCoeff N m where
  toFun := bellContractA N m
  map_add' := by intro x y; ext p; simp [bellContractA,Finset.sum_add_distrib,add_div]
  map_smul' := by intro c x; ext p; simp [bellContractA,←Finset.mul_sum,mul_div_assoc]
def bellAdjointB (N m : ℕ) : CloneSpace N m→ₗ[ℂ] BellCoeff N m where
  toFun := bellContractB N m
  map_add' := by intro x y; ext p; simp [bellContractB,Finset.sum_add_distrib,add_div]
  map_smul' := by intro c x; ext p; simp [bellContractB,←Finset.mul_sum,mul_div_assoc]

theorem bell_projection_tradeoff (N m : ℕ) [NeZero N] (hN : 2≤N) (x : CloneSpace N m) :
    (1-(1/(N:ℝ))^2)*‖x‖^2 ≤
      ‖x-bellLiftA N m (bellContractA N m x)‖^2+
      ‖x-bellLiftB N m (bellContractB N m x)‖^2+
      2/(N:ℝ)*‖x-bellLiftA N m (bellContractA N m x)‖*
        ‖x-bellLiftB N m (bellContractB N m x)‖ := by
  let U := (bellLiftA N m).restrictScalars ℝ
  let V := (bellLiftB N m).restrictScalars ℝ
  let A := (bellAdjointA N m).restrictScalars ℝ
  let B := (bellAdjointB N m).restrictScalars ℝ
  have hA (u : BellCoeff N m) (y : CloneSpace N m) : ⟪U u,y⟫_ℝ=⟪u,A y⟫_ℝ := by
    simp only [euclidean_real_inner]
    exact congrArg Complex.re (bellLiftA_adjoint N m u y)
  have hB (u : BellCoeff N m) (y : CloneSpace N m) : ⟪V u,y⟫_ℝ=⟪u,B y⟫_ℝ := by
    simp only [euclidean_real_inner]
    exact congrArg Complex.re (bellLiftB_adjoint N m u y)
  have hAU (u : BellCoeff N m) : A (U u)=u := bellContractA_liftA N m u
  have hBV (u : BellCoeff N m) : B (V u)=u := bellContractB_liftB N m u
  have hAV (u : BellCoeff N m) : A (V u)=(1/(N:ℝ)) • u := by
    change bellContractA N m (bellLiftB N m u)=_
    rw [bellContractA_liftB]
    ext p
    simp [Complex.real_smul]
  have hBU (u : BellCoeff N m) : B (U u)=(1/(N:ℝ)) • u := by
    change bellContractB N m (bellLiftA N m u)=_
    rw [bellContractB_liftA]
    ext p
    simp [Complex.real_smul]
  have hU (u v : BellCoeff N m) : ⟪U u,U v⟫_ℝ=⟪u,v⟫_ℝ := by rw [hA,hAU]
  have hV (u v : BellCoeff N m) : ⟪V u,V v⟫_ℝ=⟪u,v⟫_ℝ := by rw [hB,hBV]
  have hUV (u v : BellCoeff N m) : ⟪U u,V v⟫_ℝ=(1/(N:ℝ))*⟪u,v⟫_ℝ := by
    rw [hA,hAV,real_inner_smul_right]
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hr : 0≤1/(N:ℝ) := by positivity
  have hr1 : 1/(N:ℝ)<1 := (div_lt_one (by positivity)).mpr hn
  simpa only [U,V,A,B,LinearMap.restrictScalars_apply,bellAdjointA,bellAdjointB,
    LinearMap.coe_mk,AddHom.coe_mk,mul_one_div] using
    isoclinic_projection_tradeoff U V A B (1/N) hr hr1 hU hV hUV hA hB hAU hBV hAV hBU x
end Queelius.QuantumCloning

end

section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProductSpace BigOperators Matrix
namespace Queelius.QuantumCloning
open QAlgorithms CerfCloning.Isotropic

def krausVector {N m : ℕ} (K : Fin m→Matrix (Fin N × Fin N) (Fin N) ℂ) : CloneSpace N m :=
  WithLp.toLp 2 fun p=>K p.1 p.2.1 p.2.2

theorem kraus_vector_inner {N m : ℕ} (K : Fin m→Matrix (Fin N × Fin N) (Fin N) ℂ)
    (hK : IsKrausFamily K) : ⟪krausVector K,krausVector K⟫_ℂ=(N:ℂ) := by
  have hd (i : Fin N) : (∑j,∑p : Fin N×Fin N,K j p i*star (K j p i))=1 := by
    have hh := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ=>M i i) hK
    simpa [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,mul_comm] using hh
  simp only [PiLp.inner_apply,RCLike.inner_apply,krausVector,WithLp.ofLp_toLp,Fintype.sum_prod_type]
  have hs (j : Fin m) :
      (∑a : Fin N,∑b : Fin N,∑i : Fin N,K j (a,b) i*star (K j (a,b) i))=
      ∑i : Fin N,∑p : Fin N×Fin N,K j p i*star (K j p i) := by
    calc
      _ = ∑a : Fin N,∑i : Fin N,∑b : Fin N,K j (a,b) i*star (K j (a,b) i) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_comm
      _ = ∑i : Fin N,∑a : Fin N,∑b : Fin N,K j (a,b) i*star (K j (a,b) i) := Finset.sum_comm
      _ = _ := by simp only [Fintype.sum_prod_type]
  change (∑j : Fin m,∑a : Fin N,∑b : Fin N,∑i : Fin N,K j (a,b) i*star (K j (a,b) i))=(N:ℂ)
  simp_rw [hs]
  rw [Finset.sum_comm]
  calc
    _ = ∑_i : Fin N,(1:ℂ) := Finset.sum_congr rfl (fun i _=>hd i)
    _ = (N:ℂ) := by simp

theorem kraus_vector_norm {N m : ℕ} (K : Fin m→Matrix (Fin N × Fin N) (Fin N) ℂ)
    (hK : IsKrausFamily K) : ‖krausVector K‖^2=(N:ℝ) := by
  rw [←real_inner_self_eq_norm_sq,euclidean_real_inner,kraus_vector_inner K hK]
  simp
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped InnerProductSpace BigOperators Matrix
namespace Queelius.QuantumCloning
open QAlgorithms CerfCloning.Isotropic

theorem kraus_single_entry {N m : ℕ} (K : Fin m→Matrix (Fin N×Fin N) (Fin N) ℂ)
    (i k : Fin N) (a b : Fin N×Fin N) :
    krausApply K (Matrix.single i k 1) a b=∑j,K j a i*star (K j b k) := by
  simp [krausApply,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.single_apply,ite_mul,mul_ite,ite_and]

theorem outputA_single_bell {N m : ℕ} (K : Fin m→Matrix (Fin N×Fin N) (Fin N) ℂ)
    (i k : Fin N) :
    outputA (krausApply K) (Matrix.single i k 1) i k=∑b,∑j,K j (i,b) i*star (K j (k,b) k) := by
  change (∑b,krausApply K (Matrix.single i k 1) (i,b) (k,b))=_
  simp only [kraus_single_entry]

theorem outputB_single_bell {N m : ℕ} (K : Fin m→Matrix (Fin N×Fin N) (Fin N) ℂ)
    (i k : Fin N) :
    outputB (krausApply K) (Matrix.single i k 1) i k=∑a,∑j,K j (a,i) i*star (K j (a,k) k) := by
  change (∑a,krausApply K (Matrix.single i k 1) (a,i) (a,k))=_
  simp only [kraus_single_entry]
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped InnerProductSpace
namespace Queelius.QuantumCloning

theorem bellA_residual_sq (N m : ℕ) [NeZero N] (x : CloneSpace N m) :
    ‖x-bellLiftA N m (bellContractA N m x)‖^2=‖x‖^2-‖bellContractA N m x‖^2 := by
  have hi : ⟪bellLiftA N m (bellContractA N m x),x⟫_ℝ=‖bellContractA N m x‖^2 := by
    rw [euclidean_real_inner,bellLiftA_adjoint,←euclidean_real_inner,real_inner_self_eq_norm_sq]
  have hu : ‖bellLiftA N m (bellContractA N m x)‖^2=‖bellContractA N m x‖^2 := by
    rw [←real_inner_self_eq_norm_sq,euclidean_real_inner,bellLiftA_adjoint,bellContractA_liftA,
      ←euclidean_real_inner,real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real,real_inner_comm,hi,hu]
  ring

theorem bellB_residual_sq (N m : ℕ) [NeZero N] (x : CloneSpace N m) :
    ‖x-bellLiftB N m (bellContractB N m x)‖^2=‖x‖^2-‖bellContractB N m x‖^2 := by
  have hi : ⟪bellLiftB N m (bellContractB N m x),x⟫_ℝ=‖bellContractB N m x‖^2 := by
    rw [euclidean_real_inner,bellLiftB_adjoint,←euclidean_real_inner,real_inner_self_eq_norm_sq]
  have hu : ‖bellLiftB N m (bellContractB N m x)‖^2=‖bellContractB N m x‖^2 := by
    rw [←real_inner_self_eq_norm_sq,euclidean_real_inner,bellLiftB_adjoint,bellContractB_liftB,
      ←euclidean_real_inner,real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real,real_inner_comm,hi,hu]
  ring
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped InnerProductSpace BigOperators Matrix
namespace Queelius.QuantumCloning
open QAlgorithms CerfCloning.Isotropic

theorem sum_four_shuffle {J B I : Type*} [Fintype J] [Fintype B] [Fintype I]
    (f : J→B→I→I→ℂ) : (∑j,∑b,∑i,∑k,f j b i k)=∑i,∑k,∑b,∑j,f j b i k := by
  let e : (J×B×I×I)≃(I×I×B×J) :=
    { toFun := fun p=>(p.2.2.1,p.2.2.2,p.2.1,p.1)
      invFun := fun p=>(p.2.2.2,p.2.2.1,p.1,p.2.1)
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  simpa only [Fintype.sum_prod_type] using
    Fintype.sum_equiv e (fun p=>f p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun p=>f p.2.2.2 p.2.2.1 p.1 p.2.1) (fun _=>rfl)

theorem bellContractA_inner {N m : ℕ} (K : Fin m→Matrix (Fin N×Fin N) (Fin N) ℂ) :
    ⟪bellContractA N m (krausVector K),bellContractA N m (krausVector K)⟫_ℂ=
      (∑i,∑k,outputA (krausApply K) (Matrix.single i k 1) i k)/(N:ℂ) := by
  have hs : (Real.sqrt N:ℂ)*(Real.sqrt N:ℂ)=(N:ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (Nat.cast_nonneg N)
  have he (a b : ℂ) : a/(Real.sqrt N:ℂ)*star (b/(Real.sqrt N:ℂ))=(a*star b)/(N:ℂ) := by
    change a/(Real.sqrt N:ℂ)*(starRingEnd ℂ) (b/(Real.sqrt N:ℂ))=_
    rw [map_div₀,Complex.conj_ofReal,div_mul_div_comm,hs]
    rfl
  simp only [PiLp.inner_apply,RCLike.inner_apply,Fintype.sum_prod_type,bellContractA]
  change (∑j,∑b,((∑i,K j (i,b) i)/(Real.sqrt N:ℂ))*star ((∑k,K j (k,b) k)/(Real.sqrt N:ℂ)))=_
  simp_rw [he]
  simp only [star_sum,Finset.mul_sum,Finset.sum_mul,Finset.sum_div,outputA_single_bell]
  calc
    _ = ∑j,∑b,∑i,∑k,K j (i,b) i*star (K j (k,b) k)/(N:ℂ) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = _ := sum_four_shuffle (fun j b i k=>K j (i,b) i*star (K j (k,b) k)/(N:ℂ))

theorem bellContractB_inner {N m : ℕ} (K : Fin m→Matrix (Fin N×Fin N) (Fin N) ℂ) :
    ⟪bellContractB N m (krausVector K),bellContractB N m (krausVector K)⟫_ℂ=
      (∑i,∑k,outputB (krausApply K) (Matrix.single i k 1) i k)/(N:ℂ) := by
  have hs : (Real.sqrt N:ℂ)*(Real.sqrt N:ℂ)=(N:ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (Nat.cast_nonneg N)
  have he (a b : ℂ) : a/(Real.sqrt N:ℂ)*star (b/(Real.sqrt N:ℂ))=(a*star b)/(N:ℂ) := by
    change a/(Real.sqrt N:ℂ)*(starRingEnd ℂ) (b/(Real.sqrt N:ℂ))=_
    rw [map_div₀,Complex.conj_ofReal,div_mul_div_comm,hs]
    rfl
  simp only [PiLp.inner_apply,RCLike.inner_apply,Fintype.sum_prod_type,bellContractB]
  change (∑j,∑b,((∑i,K j (b,i) i)/(Real.sqrt N:ℂ))*star ((∑k,K j (b,k) k)/(Real.sqrt N:ℂ)))=_
  simp_rw [he]
  simp only [star_sum,Finset.mul_sum,Finset.sum_mul,Finset.sum_div,outputB_single_bell]
  calc
    _ = ∑j,∑b,∑i,∑k,K j (b,i) i*star (K j (b,k) k)/(N:ℂ) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = _ := sum_four_shuffle (fun j b i k=>K j (b,i) i*star (K j (b,k) k)/(N:ℂ))

end Queelius.QuantumCloning

end

section
noncomputable section
open scoped BigOperators Matrix
namespace Queelius.QuantumCloning
open QAlgorithms

theorem depolarizing_bell_entry (N : ℕ) [NeZero N] (p : ℝ) (i k : Fin N) :
    QuditFidelity.depolarizingMap N (Nat.pos_of_neZero N) p (Matrix.single i k 1) i k=
      ((1-p:ℝ):ℂ)+(if i=k then (p/(N:ℝ):ℝ) else 0) := by
  by_cases h : i=k
  · subst k
    simp [QuditFidelity.depolarizingMap,Matrix.trace_single_eq_same]
    ring
  · simp [QuditFidelity.depolarizingMap,Matrix.trace_single_eq_of_ne i k (1:ℂ) h,h]

theorem depolarizing_bell_sum (N : ℕ) [NeZero N] (p : ℝ) :
    (∑i : Fin N,∑k : Fin N,
      QuditFidelity.depolarizingMap N (Nat.pos_of_neZero N) p (Matrix.single i k 1) i k)=
      (N:ℂ)^2*((1-p:ℝ):ℂ)+(p:ℂ) := by
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simp only [depolarizing_bell_entry,Finset.sum_add_distrib]
  simp [apply_ite]
  push_cast
  field_simp [show (N:ℂ)≠0 by exact_mod_cast NeZero.ne N]
  <;> ring
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped InnerProductSpace BigOperators Matrix
namespace Queelius.QuantumCloning
open QAlgorithms CerfCloning.Isotropic

theorem isotropic_A_error {N m : ℕ} [NeZero N]
    (K : Fin m→Matrix (Fin N×Fin N) (Fin N) ℂ) (hK : IsKrausFamily K) (p : ℝ)
    (h : ∀ρ,outputA (krausApply K) ρ=QuditFidelity.depolarizingMap N (Nat.pos_of_neZero N) p ρ) :
    ‖krausVector K-bellLiftA N m (bellContractA N m (krausVector K))‖^2=
      (N:ℝ)*(1-(1/(N:ℝ))^2)*p := by
  have hi : ⟪bellContractA N m (krausVector K),bellContractA N m (krausVector K)⟫_ℂ=
      (((N:ℝ)^2*(1-p)+p)/(N:ℝ):ℝ) := by
    rw [bellContractA_inner]
    simp_rw [h]
    rw [depolarizing_bell_sum]
    push_cast
    rfl
  have hn : ‖bellContractA N m (krausVector K)‖^2=((N:ℝ)^2*(1-p)+p)/(N:ℝ) := by
    rw [←real_inner_self_eq_norm_sq,euclidean_real_inner,hi]
    rfl
  rw [bellA_residual_sq,kraus_vector_norm K hK,hn]
  field_simp [show (N:ℝ)≠0 by exact_mod_cast NeZero.ne N]
  <;> ring

theorem isotropic_B_error {N m : ℕ} [NeZero N]
    (K : Fin m→Matrix (Fin N×Fin N) (Fin N) ℂ) (hK : IsKrausFamily K) (p : ℝ)
    (h : ∀ρ,outputB (krausApply K) ρ=QuditFidelity.depolarizingMap N (Nat.pos_of_neZero N) p ρ) :
    ‖krausVector K-bellLiftB N m (bellContractB N m (krausVector K))‖^2=
      (N:ℝ)*(1-(1/(N:ℝ))^2)*p := by
  have hi : ⟪bellContractB N m (krausVector K),bellContractB N m (krausVector K)⟫_ℂ=
      (((N:ℝ)^2*(1-p)+p)/(N:ℝ):ℝ) := by
    rw [bellContractB_inner]
    simp_rw [h]
    rw [depolarizing_bell_sum]
    push_cast
    rfl
  have hn : ‖bellContractB N m (krausVector K)‖^2=((N:ℝ)^2*(1-p)+p)/(N:ℝ) := by
    rw [←real_inner_self_eq_norm_sq,euclidean_real_inner,hi]
    rfl
  rw [bellB_residual_sq,kraus_vector_norm K hK,hn]
  field_simp [show (N:ℝ)≠0 by exact_mod_cast NeZero.ne N]
  <;> ring
end Queelius.QuantumCloning

end

section
noncomputable section
open scoped InnerProductSpace
namespace Queelius.QuantumCloning
open QAlgorithms CerfCloning.Isotropic

theorem normalize_error_tradeoff (c r ea eb pa pb : ℝ) (hc : 0<c)
    (hea : 0≤ea) (heb : 0≤eb) (ha : ea^2=c*pa) (hb : eb^2=c*pb)
    (h : c≤ea^2+eb^2+2*r*ea*eb) :
    0≤pa ∧ 0≤pb ∧ 1≤pa+2*r*(Real.sqrt pa*Real.sqrt pb)+pb := by
  have hpa : 0≤pa := nonneg_of_mul_nonneg_right (ha ▸ sq_nonneg ea) hc
  have hpb : 0≤pb := nonneg_of_mul_nonneg_right (hb ▸ sq_nonneg eb) hc
  have hs : (ea*eb)^2=(c*(Real.sqrt pa*Real.sqrt pb))^2 := by
    rw [mul_pow,ha,hb,mul_pow,mul_pow,Real.sq_sqrt hpa,Real.sq_sqrt hpb]
    ring
  have hp : ea*eb=c*(Real.sqrt pa*Real.sqrt pb) := by
    have hl : 0≤ea*eb := mul_nonneg hea heb
    have hr : 0≤c*(Real.sqrt pa*Real.sqrt pb) := by positivity
    nlinarith only [hs,hl,hr]
  refine ⟨hpa,hpb,?_⟩
  apply (mul_le_mul_iff_right₀ hc).mp
  rw [ha,hb] at h
  have he : 2*r*ea*eb=2*r*(ea*eb) := by ring
  rw [he,hp] at h
  nlinarith only [h]

theorem universal_no_cloning (N : ℕ) [NeZero N] (hN : 2≤N)
    (T : Superop (Fin N) (Fin N×Fin N)) (pa pb : ℝ)
    (h : IsIsotropicCloner N T pa pb) :
    1≤pa+2/(N:ℝ)*(Real.sqrt pa*Real.sqrt pb)+pb := by
  obtain ⟨⟨m,K,hK,hT⟩,hA,hB⟩ := h
  have he : T=krausApply K := funext hT
  subst T
  have ha:=isotropic_A_error K hK pa hA
  have hb:=isotropic_B_error K hK pb hB
  have ht:=bell_projection_tradeoff N m hN (krausVector K)
  rw [kraus_vector_norm K hK] at ht
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hr : 0≤1/(N:ℝ) := by positivity
  have hr1 : 1/(N:ℝ)<1 := (div_lt_one (by positivity)).mpr hn
  have hc : 0<(N:ℝ)*(1-(1/(N:ℝ))^2) := mul_pos (by positivity) (by nlinarith)
  have htr : (N:ℝ)*(1-(1/(N:ℝ))^2)≤
      ‖krausVector K-bellLiftA N m (bellContractA N m (krausVector K))‖^2+
      ‖krausVector K-bellLiftB N m (bellContractB N m (krausVector K))‖^2+
      2*(1/(N:ℝ))*‖krausVector K-bellLiftA N m (bellContractA N m (krausVector K))‖*
        ‖krausVector K-bellLiftB N m (bellContractB N m (krausVector K))‖ := by
    simpa only [mul_comm (1-(1/(N:ℝ))^2) (N:ℝ),mul_one_div] using ht
  have hh:=normalize_error_tradeoff _ _ _ _ _ _ hc (norm_nonneg _) (norm_nonneg _) ha hb htr
  simpa only [mul_one_div] using hh.2.2
end Queelius.QuantumCloning

end

section
theorem solution :
∀ (N : Nat) [inst : @NeZero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) N],
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N →
    And
      (∀ (T : QAlgorithms.Superop (Fin N) (Prod (Fin N) (Fin N))) (pa pb : Real),
        @CerfCloning.Isotropic.IsIsotropicCloner N inst T pa pb →
          @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
            (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
              (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) pa
                (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                    (@OfNat.ofNat Real (nat_lit 2)
                      (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (@Nat.cast Real Real.instNatCast N))
                  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt pa) (Real.sqrt pb))))
              pb))
      (∀ (pa pb : Real),
        @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) pa →
          @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) pb →
            @Eq Real
                (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) pa
                    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                      (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                        (@OfNat.ofNat Real (nat_lit 2)
                          (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        (@Nat.cast Real Real.instNatCast N))
                      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt pa) (Real.sqrt pb))))
                  pb)
                (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) →
              @Exists (QAlgorithms.Superop (Fin N) (Prod (Fin N) (Fin N)))
                fun (T : QAlgorithms.Superop (Fin N) (Prod (Fin N) (Fin N))) =>
                @CerfCloning.Isotropic.IsIsotropicCloner N inst T pa pb) := by
  intro N inst hN
  exact ⟨Queelius.QuantumCloning.universal_no_cloning N hN, Queelius.QuantumCloning.boundary_achievable N⟩

end
