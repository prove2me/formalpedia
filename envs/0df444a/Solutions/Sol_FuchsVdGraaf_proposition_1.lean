-- Prove2me | solution 1 for FuchsVdGraaf.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-19T21:55:53.823182+00:00
-- url     : https://prove2.me/submissions/468240bc-07db-4122-907a-0cf3dc2fc94c

import Definitions.Def_FuchsVdGraaf_qErrorProb
import Definitions.Def_FuchsVdGraaf_qKolmogorov
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceDist
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceDist
import Definitions.Def_WildeQIT_traceNorm
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_WildeQIT_Purification_exists_unitary_eq_mul_of_mul_conjTranspose_eq

noncomputable section
open Matrix Unitary
open scoped ComplexOrder ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QValue20Support.RecoveryMatrixSVD
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Square SVD tied to the exact Gram spectral calculus; no rank assumption. -/
theorem gram_svd (A : Matrix n n ℂ) :
    ∃ (U V : unitary (Matrix n n ℂ)) (s : n → ℝ),
      (∀ i, 0 ≤ s i) ∧
      A=(U : Matrix n n ℂ)*diagonal (fun i => (s i : ℂ))*(V : Matrix n n ℂ) ∧
      (∀ f : ℝ → ℝ, cfc f (Aᴴ*A) =
        (V : Matrix n n ℂ)ᴴ*diagonal (fun i => (f (s i^2) : ℂ))*(V : Matrix n n ℂ)) := by
  classical
  let hG := posSemidef_conjTranspose_mul_self A
  let Q := hG.isHermitian.eigenvectorUnitary
  let s : n → ℝ := fun i => Real.sqrt (hG.isHermitian.eigenvalues i)
  have hs (i : n) : 0 ≤ s i := Real.sqrt_nonneg _
  have hsq (i : n) : s i^2 = hG.isHermitian.eigenvalues i := Real.sq_sqrt (hG.eigenvalues_nonneg i)
  let D : Matrix n n ℂ := diagonal (fun i => (s i : ℂ))
  let B : Matrix n n ℂ := D*(Q : Matrix n n ℂ)ᴴ
  have hD : Dᴴ=D := by simp [D,diagonal_conjTranspose]
  have hB : Bᴴ*B=Aᴴ*A := by
    dsimp [B]
    rw [conjTranspose_mul,conjTranspose_conjTranspose,hD]
    rw [Matrix.mul_assoc,← Matrix.mul_assoc D D]
    have hd : D*D=diagonal (fun i => (hG.isHermitian.eigenvalues i : ℂ)) := by
      dsimp [D]
      rw [diagonal_mul_diagonal]
      congr 1
      funext i
      exact_mod_cast (show s i*s i=hG.isHermitian.eigenvalues i by simpa only [pow_two] using hsq i)
    rw [hd]
    rw [← Matrix.mul_assoc]
    exact hG.isHermitian.spectral_theorem.symm
  obtain ⟨W,hW,hh⟩ := WildeQIT.Purification.exists_unitary_eq_mul_of_mul_conjTranspose_eq Aᴴ Bᴴ
    (by simpa only [conjTranspose_conjTranspose] using hB.symm)
  let U : unitary (Matrix n n ℂ) := star ⟨W,hW⟩
  let V : unitary (Matrix n n ℂ) := star Q
  refine ⟨U,V,s,hs,?_,?_⟩
  · have hh' := congrArg conjTranspose hh
    simpa only [U,V,B,conjTranspose_conjTranspose,conjTranspose_mul,
      Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.mul_assoc] using hh'
  · intro f
    rw [hG.isHermitian.cfc_eq,Matrix.IsHermitian.cfc,conjStarAlgAut_apply]
    dsimp [V,Q]
    simp only [Unitary.coe_star,Matrix.star_eq_conjTranspose,conjTranspose_conjTranspose]
    congr 2
    ext i j
    simp [diagonal_apply,hsq]

end QValue20Support.RecoveryMatrixSVD

end

noncomputable section
open Matrix Unitary
open QAlgorithms.Papers.Independent.Information100.P50
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QValue20Support.RecoverySchatten
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma trace_gram_cfc (A : Matrix n n ℂ) (V : unitary (Matrix n n ℂ)) (s : n → ℝ)
    (hcalc : ∀ f : ℝ → ℝ, cfc f (Aᴴ*A) =
      (V : Matrix n n ℂ)ᴴ*diagonal (fun i => (f (s i^2) : ℂ))*(V : Matrix n n ℂ))
    (f : ℝ → ℝ) : (cfc f (Aᴴ*A)).trace.re=∑ i, f (s i^2) := by
  rw [hcalc,trace_mul_cycle]
  have hVV : (V : Matrix n n ℂ)*(V : Matrix n n ℂ)ᴴ=1 := Unitary.coe_mul_star_self V
  rw [hVV,Matrix.one_mul,trace_diagonal]
  simp

lemma schatten_finite (A : Matrix n n ℂ) (V : unitary (Matrix n n ℂ)) (s : n → ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hcalc : ∀ f : ℝ → ℝ, cfc f (Aᴴ*A) =
      (V : Matrix n n ℂ)ᴴ*diagonal (fun i => (f (s i^2) : ℂ))*(V : Matrix n n ℂ))
    (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    schattenNorm p A = (∑ i, (s i)^p.toReal)^(1/p.toReal) := by
  rw [schattenNorm,if_neg hp,trace_gram_cfc A V s hcalc]
  simp only [Real.rpow_eq_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Real.rpow_natCast,← Real.rpow_mul (hs i)]
  congr 1
  ring

lemma schatten_two (A : Matrix n n ℂ) :
    schattenNorm 2 A = Real.sqrt ((Aᴴ*A).trace.re) := by
  rw [schattenNorm,if_neg (by simp),ENNReal.toReal_ofNat]
  simp only [Real.rpow_eq_pow]
  norm_num only [show (2 : ℝ)/2=1 by norm_num,Real.rpow_one]
  change (cfc id (Aᴴ*A)).trace.re^(1/2 : ℝ)=Real.sqrt ((Aᴴ*A).trace.re)
  have hG : IsSelfAdjoint (Aᴴ*A) := (posSemidef_conjTranspose_mul_self A).isHermitian
  rw [cfc_id ℝ (Aᴴ*A)]
  exact (Real.sqrt_eq_rpow _).symm

lemma schatten_one_svd (A : Matrix n n ℂ) (V : unitary (Matrix n n ℂ)) (s : n → ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hcalc : ∀ f : ℝ → ℝ, cfc f (Aᴴ*A) =
      (V : Matrix n n ℂ)ᴴ*diagonal (fun i => (f (s i^2) : ℂ))*(V : Matrix n n ℂ)) :
    schattenNorm 1 A = ∑ i, s i := by
  rw [schatten_finite A V s hs hcalc 1 (by simp)]
  simp

lemma schatten_one_nonneg (A : Matrix n n ℂ) : 0 ≤ schattenNorm 1 A := by
  obtain ⟨U,V,s,hs,_,hcalc⟩ := QValue20Support.RecoveryMatrixSVD.gram_svd A
  rw [schatten_one_svd A V s hs hcalc]
  exact Finset.sum_nonneg fun i _ => hs i

end QValue20Support.RecoverySchatten

end

noncomputable section
open Matrix Unitary
open QAlgorithms.Papers.Independent.Information100.P50
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QValue20Support.RecoveryTraceBounds
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma entry_le_opNorm (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ n := EuclideanSpace.single j 1
  have hh := (PiLp.norm_apply_le ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A) e) i).trans
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A).le_opNorm e)
  have he : ‖e‖=1 := by simp [e]
  have hval : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A) e) i = A i j := by
    change (A *ᵥ Pi.single j (1 : ℂ)) i = A i j
    simp
  rw [hval,Matrix.l2_opNorm_toEuclideanCLM,he,mul_one] at hh
  exact hh

lemma gram_trace (A : Matrix n n ℂ) : (Aᴴ*A).trace.re=∑ i, ∑ j, ‖A i j‖^2 := by
  change (∑ i, ∑ j, star (A j i)*A j i).re=∑ i, ∑ j, ‖A i j‖^2
  simp only [Complex.re_sum]
  have hterm (z : ℂ) : (star z*z).re=‖z‖^2 := by
    change (conj z*z).re=‖z‖^2
    rw [← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  simp_rw [hterm]
  exact Finset.sum_comm

lemma trace_diagonal_mul (X : Matrix n n ℂ) (s : n → ℂ) :
    (X*diagonal s).trace=∑ i, X i i*s i := by
  simp [Matrix.trace,Matrix.diag]

lemma trace_op_trace_bound (X A : Matrix n n ℂ) :
    ‖(X*A).trace‖ ≤ ‖X‖*schattenNorm 1 A := by
  obtain ⟨U,V,s,hs,hA,hcalc⟩ := QValue20Support.RecoveryMatrixSVD.gram_svd A
  rw [QValue20Support.RecoverySchatten.schatten_one_svd A V s hs hcalc]
  have ht : (X*A).trace = ((V : Matrix n n ℂ)*X*(U : Matrix n n ℂ)*diagonal (fun i => (s i : ℂ))).trace := by
    rw [hA,← Matrix.mul_assoc,trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  rw [ht,trace_diagonal_mul]
  calc
    _ ≤ ∑ i, ‖((V : Matrix n n ℂ)*X*(U : Matrix n n ℂ)) i i*(s i : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖X‖*s i := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hs i)]
      apply mul_le_mul_of_nonneg_right _ (hs i)
      exact (entry_le_opNorm _ i i).trans_eq (by
        rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul])
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma trace_hilbert_schmidt_bound (X A : Matrix n n ℂ) :
    ‖(X*A).trace‖ ≤ schattenNorm 2 X*schattenNorm 2 A := by
  rw [QValue20Support.RecoverySchatten.schatten_two,QValue20Support.RecoverySchatten.schatten_two,gram_trace,gram_trace]
  have ht : (X*A).trace = ∑ p : n×n, X p.1 p.2*A p.2 p.1 := by
    simp [Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_prod_type]
  rw [ht]
  calc
    _ ≤ ∑ p : n×n, ‖X p.1 p.2*A p.2 p.1‖ := norm_sum_le _ _
    _ = ∑ p : n×n, ‖X p.1 p.2‖*‖A p.2 p.1‖ := by simp only [norm_mul]
    _ ≤ Real.sqrt (∑ p : n×n, ‖X p.1 p.2‖^2)*Real.sqrt (∑ p : n×n, ‖A p.2 p.1‖^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by simp only [Fintype.sum_prod_type]; rw [Finset.sum_comm (f := fun i j => ‖A j i‖^2)]

end QValue20Support.RecoveryTraceBounds

end

noncomputable section
open Matrix Unitary WildeQIT
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QValue20Support.QuantumValueTrace
variable {n : Type} [Fintype n] [DecidableEq n]

lemma schatten_bridge (A : Matrix n n ℂ) :
    QAlgorithms.Papers.Independent.Information100.P50.schattenNorm 1 A=traceNorm A := by
  rw [QAlgorithms.Papers.Independent.Information100.P50.schattenNorm,
    if_neg (by simp),ENNReal.toReal_one,div_one]
  simp only [Real.rpow_eq_pow,Real.rpow_one]
  unfold traceNorm
  rw [CFC.sqrt_eq_rpow,CFC.rpow_eq_cfc_real (posSemidef_conjTranspose_mul_self A).nonneg]

lemma trace_bound (A B : Matrix n n ℂ) : ‖(A*B).trace‖ ≤ ‖A‖*traceNorm B := by
  simpa only [schatten_bridge] using
    QValue20Support.RecoveryTraceBounds.trace_op_trace_bound A B

lemma traceNorm_nonneg (A : Matrix n n ℂ) : 0 ≤ traceNorm A := by
  rw [← schatten_bridge]
  exact QValue20Support.RecoverySchatten.schatten_one_nonneg A

lemma traceNorm_svd (A : Matrix n n ℂ) (V : unitary (Matrix n n ℂ)) (s : n → ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hc : ∀ f : ℝ → ℝ, cfc f (Aᴴ*A)=
      (V : Matrix n n ℂ)ᴴ*diagonal (fun i => (f (s i^2) : ℂ))*(V : Matrix n n ℂ)) :
    traceNorm A=∑ i, s i := by
  rw [← schatten_bridge]
  exact QValue20Support.RecoverySchatten.schatten_one_svd A V s hs hc

lemma norm_unitary_le_one (U : unitary (Matrix n n ℂ)) : ‖(U : Matrix n n ℂ)‖ ≤ 1 := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    haveI := hn
    have hU : (U : Matrix n n ℂ)=0 := Subsingleton.elim _ _
    rw [hU,norm_zero]
    exact zero_le_one
  | inr hn =>
    haveI := hn
    exact (CStarRing.norm_coe_unitary U).le

lemma trace_unitary_bound (A : Matrix n n ℂ) (U : unitary (Matrix n n ℂ)) :
    ‖(A*(U : Matrix n n ℂ)).trace‖ ≤ traceNorm A := by
  rw [trace_mul_comm]
  exact (trace_bound _ A).trans ((mul_le_mul_of_nonneg_right
    (norm_unitary_le_one U) (traceNorm_nonneg A)).trans_eq (one_mul _))

lemma variational (A : Matrix n n ℂ) :
    IsGreatest {x : ℝ | ∃ U ∈ Matrix.unitaryGroup n ℂ, x=‖(A*U).trace‖} (traceNorm A) := by
  classical
  obtain ⟨U,V,s,hs,hA,hc⟩ := QValue20Support.RecoveryMatrixSVD.gram_svd A
  let W : unitary (Matrix n n ℂ) := star V*star U
  have hVV : (V : Matrix n n ℂ)*(V : Matrix n n ℂ)ᴴ=1 := Unitary.coe_mul_star_self V
  have hUU : (U : Matrix n n ℂ)ᴴ*(U : Matrix n n ℂ)=1 := Unitary.coe_star_mul_self U
  have hw : (A*(W : Matrix n n ℂ)).trace=(∑ i, s i : ℝ) := by
    rw [hA]
    change (((U : Matrix n n ℂ)*diagonal (fun i => (s i : ℂ))*(V : Matrix n n ℂ))*
      ((V : Matrix n n ℂ)ᴴ*(U : Matrix n n ℂ)ᴴ)).trace=_
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (V : Matrix n n ℂ),hVV,Matrix.one_mul]
    rw [← Matrix.mul_assoc,trace_mul_cycle,hUU,Matrix.one_mul,trace_diagonal]
    simp
  refine ⟨?_,?_⟩
  · refine ⟨W,W.property,?_⟩
    rw [hw,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun i _ => hs i))]
    exact traceNorm_svd A V s hs hc
  · rintro x ⟨W,hW,rfl⟩
    exact trace_unitary_bound A ⟨W,hW⟩

lemma triangle (A B : Matrix n n ℂ) : traceNorm (A+B) ≤ traceNorm A+traceNorm B := by
  obtain ⟨W,hW,h⟩ := (variational (A+B)).1
  rw [h,Matrix.add_mul,trace_add]
  exact (norm_add_le _ _).trans (add_le_add (trace_unitary_bound A ⟨W,hW⟩)
    (trace_unitary_bound B ⟨W,hW⟩))

lemma contraction_norm (A : Matrix n n ℂ) (hA : Aᴴ*A ≤ 1) : ‖A‖ ≤ 1 := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    haveI := hn
    have hz : A=0 := Subsingleton.elim _ _
    rw [hz,norm_zero]
    exact zero_le_one
  | inr hn =>
    haveI := hn
    have hg := (CStarAlgebra.norm_le_one_iff_of_nonneg (Aᴴ*A)
      (posSemidef_conjTranspose_mul_self A).nonneg).mpr hA
    have he : ‖Aᴴ*A‖=‖A‖*‖A‖ := CStarRing.norm_star_mul_self
    rw [he] at hg
    nlinarith [norm_nonneg A]

lemma contraction_trace (X A : Matrix n n ℂ) (hA : Aᴴ*A ≤ 1) :
    ‖(X*A).trace‖ ≤ traceNorm X := by
  rw [trace_mul_comm]
  exact (trace_bound A X).trans ((mul_le_mul_of_nonneg_right (contraction_norm A hA)
    (traceNorm_nonneg X)).trans_eq (one_mul _))

end QValue20Support.QuantumValueTrace

end

open Matrix WildeQIT
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

noncomputable section
open Matrix Unitary WildeQIT
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace QValue20Support.QuantumValueHelstrom
variable {n : Type} [Fintype n] [DecidableEq n]

lemma trace_cfc (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace.re=∑ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq,Matrix.IsHermitian.cfc,conjStarAlgAut_apply,trace_mul_cycle]
  simp only [Matrix.star_eq_conjTranspose]
  rw [show (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ*(hA.eigenvectorUnitary : Matrix n n ℂ)=1 from Unitary.coe_star_mul_self _,Matrix.one_mul,trace_diagonal]
  simp

lemma traceNorm_hermitian (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    traceNorm A=∑ i, |hA.eigenvalues i| := by
  change (CFC.abs A).trace.re=_
  rw [CFC.abs_eq_cfc_norm A (show IsSelfAdjoint A from hA),trace_cfc A hA]
  simp only [Real.norm_eq_abs]

lemma spectral_product (A P : Matrix n n ℂ) (hA : A.IsHermitian) :
    (P*A).trace.re=∑ i, (((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ*P*
      (hA.eigenvectorUnitary : Matrix n n ℂ)) i i).re * hA.eigenvalues i := by
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  let D : Matrix n n ℂ := diagonal (fun i => (hA.eigenvalues i : ℂ))
  have hspec : A=U*D*Uᴴ := hA.spectral_theorem
  have ht : (P*A).trace=((Uᴴ*P*U)*diagonal (fun i => (hA.eigenvalues i : ℂ))).trace := by
    calc
      (P*A).trace=(P*(U*D*Uᴴ)).trace := by rw [hspec]
      _=(((P*U)*D)*Uᴴ).trace := by simp only [Matrix.mul_assoc]
      _=((Uᴴ*(P*U))*D).trace := trace_mul_cycle (P*U) D Uᴴ
      _=((Uᴴ*P*U)*D).trace := by simp only [Matrix.mul_assoc]
  rw [ht,QValue20Support.RecoveryTraceBounds.trace_diagonal_mul]
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rfl

lemma effect_diagonal (P : Matrix n n ℂ) (hP : P.PosSemidef) (hPI : (1-P).PosSemidef)
    (V : unitary (Matrix n n ℂ)) (i : n) :
    0 ≤ (((V : Matrix n n ℂ)ᴴ*P*(V : Matrix n n ℂ)) i i).re ∧
      (((V : Matrix n n ℂ)ᴴ*P*(V : Matrix n n ℂ)) i i).re ≤ 1 := by
  let U : Matrix n n ℂ := V
  have hU : Uᴴ*U=1 := Unitary.coe_star_mul_self V
  have hD0 := hP.mul_mul_conjTranspose_same Uᴴ
  have hD1 := hPI.mul_mul_conjTranspose_same Uᴴ
  simp only [conjTranspose_conjTranspose] at hD0 hD1
  have he : Uᴴ*(1-P)*U=1-Uᴴ*P*U := by rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hU]
  rw [he] at hD1
  have h0 := (Complex.nonneg_iff.mp (hD0.diag_nonneg (i := i))).1
  have h1 := (Complex.nonneg_iff.mp (hD1.diag_nonneg (i := i))).1
  simp only [Matrix.sub_apply,Matrix.one_apply_eq,Complex.sub_re,Complex.one_re] at h1
  exact ⟨h0,by linarith⟩

lemma max_sum (A : Matrix n n ℂ) (hA : A.IsHermitian) (ht : A.trace=0) :
    (∑ i, max 0 (hA.eigenvalues i))=(1/2 : ℝ)*traceNorm A := by
  rw [traceNorm_hermitian A hA]
  have hs : (∑ i, hA.eigenvalues i)=0 := by
    have hh := congrArg Complex.re hA.trace_eq_sum_eigenvalues
    simpa [ht] using hh.symm
  have hp (x : ℝ) : max 0 x=(|x|+x)/2 := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_right hx,abs_of_nonneg hx]; ring
    · rw [max_eq_left (le_of_not_ge hx),abs_of_neg (lt_of_not_ge hx)]; ring
  simp_rw [hp]
  rw [← Finset.sum_div,Finset.sum_add_distrib,hs,add_zero]
  ring

lemma effect_bound (A P : Matrix n n ℂ) (hA : A.IsHermitian) (ht : A.trace=0)
    (hP : P.PosSemidef) (hPI : (1-P).PosSemidef) :
    (P*A).trace.re ≤ (1/2 : ℝ)*traceNorm A := by
  rw [spectral_product A P hA,← max_sum A hA ht]
  apply Finset.sum_le_sum
  intro i _
  have hd := effect_diagonal P hP hPI hA.eigenvectorUnitary i
  by_cases hlam : 0 ≤ hA.eigenvalues i
  · rw [max_eq_right hlam]; nlinarith
  · rw [max_eq_left (le_of_not_ge hlam)]; nlinarith

lemma maximizing_effect (A : Matrix n n ℂ) (hA : A.IsHermitian) (ht : A.trace=0) :
    ∃ P : Matrix n n ℂ, P.PosSemidef ∧ (1-P).PosSemidef ∧
      (P*A).trace.re=(1/2 : ℝ)*traceNorm A := by
  classical
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  let d : n → ℂ := fun i => if 0 ≤ hA.eigenvalues i then 1 else 0
  let D := diagonal d
  let P := U*D*Uᴴ
  have hUU : Uᴴ*U=1 := Unitary.coe_star_mul_self _
  have hUU' : U*Uᴴ=1 := Unitary.coe_mul_star_self _
  have hD : D.PosSemidef := posSemidef_diagonal_iff.mpr (fun i => by dsimp [d]; split_ifs <;> norm_num)
  have hD' : (1-D).PosSemidef := by
    have he : 1-D=diagonal (fun i => 1-d i) := by
      ext i j
      by_cases hij : i=j
      · subst j; simp [D]
      · simp [D,Matrix.diagonal_apply,Matrix.one_apply,hij]
    rw [he]
    exact posSemidef_diagonal_iff.mpr (fun i => by dsimp [d]; split_ifs <;> norm_num)
  have hP : P.PosSemidef := hD.mul_mul_conjTranspose_same U
  have he : U*(1-D)*Uᴴ=1-P := by rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hUU']
  have hPI : (1-P).PosSemidef := by rw [← he]; exact hD'.mul_mul_conjTranspose_same U
  have hDiag : Uᴴ*P*U=D := by
    dsimp [P]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U,hUU,Matrix.one_mul,Matrix.mul_one]
  refine ⟨P,hP,hPI,?_⟩
  rw [spectral_product A P hA,← max_sum A hA ht]
  change (∑ i, ((Uᴴ*P*U) i i).re*hA.eigenvalues i)=_
  rw [hDiag]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [D,d]
  by_cases hi : 0 ≤ hA.eigenvalues i
  · simp [hi,max_eq_right hi]
  · simp [hi,max_eq_left (le_of_not_ge hi)]

lemma helstrom (ρ σ : Matrix n n ℂ) (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    IsGreatest {x : ℝ | ∃ P : Matrix n n ℂ, P.PosSemidef ∧ (1-P).PosSemidef ∧
      x=(P*(ρ-σ)).trace.re} ((1/2 : ℝ)*traceDist ρ σ) := by
  have hh : (ρ-σ).IsHermitian := hρ.1.isHermitian.sub hσ.1.isHermitian
  have ht : (ρ-σ).trace=0 := by rw [trace_sub,hρ.2,hσ.2,sub_self]
  obtain ⟨P,hP,hPI,h⟩ := maximizing_effect (ρ-σ) hh ht
  refine ⟨⟨P,hP,hPI,h.symm⟩,?_⟩
  rintro x ⟨Q,hQ,hQI,rfl⟩
  exact effect_bound _ _ hh ht hQ hQI

lemma close_measurement (ρ σ P : Matrix n n ℂ) (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) (hP : P.PosSemidef) (hPI : (1-P).PosSemidef) :
    (P*σ).trace.re-(1/2 : ℝ)*traceDist ρ σ ≤ (P*ρ).trace.re ∧
      (P*σ).trace.re-traceDist ρ σ ≤ (P*σ).trace.re-(1/2 : ℝ)*traceDist ρ σ := by
  have ht : (ρ-σ).trace=0 := by rw [trace_sub,hρ.2,hσ.2,sub_self]
  have hpp : (1-(1-P)).PosSemidef := by simpa using hP
  have hh := effect_bound (ρ-σ) (1-P) (hρ.1.isHermitian.sub hσ.1.isHermitian) ht hPI hpp
  rw [Matrix.sub_mul,Matrix.one_mul,trace_sub,ht,Complex.sub_re,Complex.zero_re,
    Matrix.mul_sub,trace_sub,Complex.sub_re] at hh
  change 0-((P*ρ).trace.re-(P*σ).trace.re) ≤ (1/2 : ℝ)*traceDist ρ σ at hh
  have hn : 0 ≤ traceDist ρ σ := QValue20Support.QuantumValueTrace.traceNorm_nonneg _
  constructor <;> linarith

end QValue20Support.QuantumValueHelstrom

end

noncomputable section
open Matrix WildeQIT FuchsVdGraaf
open scoped MatrixOrder ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace QValue20Support.QuantumValueOperational
variable {n : Type} [Fintype n] [DecidableEq n]

lemma sum_outcomes (ρ : Matrix n n ℂ) {m : ℕ} (E : Fin m → Matrix n n ℂ)
    (hE : IsPOVM E) : ∑ x, outcomeDist ρ E x=ρ.trace.re := by
  simp only [outcomeDist,← Complex.re_sum,← Matrix.trace_sum,← Matrix.mul_sum,hE.2,
    Matrix.mul_one]

lemma kolmogorov_bound (ρ σ : Matrix n n ℂ) (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) {m : ℕ} (E : Fin m → Matrix n n ℂ) (hE : IsPOVM E) :
    kolmogorov (outcomeDist ρ E) (outcomeDist σ E) ≤ (1/2 : ℝ)*traceNorm (ρ-σ) := by
  classical
  let d : Fin m → ℝ := fun x => (E x*(ρ-σ)).trace.re
  let s := Finset.univ.filter (fun x => 0 ≤ d x)
  let P : Matrix n n ℂ := ∑ x ∈ s, E x
  have hp : P.PosSemidef := posSemidef_sum _ (fun x _ => hE.1 x)
  have he : 1-P=∑ x ∈ Finset.univ.filter (fun x => ¬ 0 ≤ d x), E x := by
    have hh := Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => 0 ≤ d x) E
    rw [hE.2] at hh
    exact (sub_eq_iff_eq_add).mpr (by simpa [add_comm] using hh.symm)
  have hpi : (1-P).PosSemidef := by
    rw [he]; exact posSemidef_sum _ (fun x _ => hE.1 x)
  have ht : (ρ-σ).trace=0 := by simp [Matrix.trace_sub,hρ.2,hσ.2]
  have hd : ∑ x, d x=0 := by
    simp only [d,← Complex.re_sum,← Matrix.trace_sum,← Matrix.sum_mul,hE.2,
      Matrix.one_mul,ht,Complex.zero_re]
  have hsum : ∑ x, |d x|=2*∑ x ∈ s, d x := by
    have ha (x : Fin m) : |d x|=2*(if 0 ≤ d x then d x else 0)-d x := by
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · rw [abs_of_neg (lt_of_not_ge h)]; ring
    simp_rw [ha]
    rw [Finset.sum_sub_distrib,hd,sub_zero,← Finset.mul_sum]
    simp [s,Finset.sum_filter]
  have htr : (P*(ρ-σ)).trace.re=∑ x ∈ s, d x := by
    simp [P,d,Matrix.sum_mul,Matrix.trace_sum,Complex.re_sum]
  have hb := QValue20Support.QuantumValueHelstrom.effect_bound (ρ-σ) P
    (hρ.1.isHermitian.sub hσ.1.isHermitian) ht hp hpi
  rw [htr] at hb
  have hdif (x : Fin m) : outcomeDist ρ E x-outcomeDist σ E x=d x := by
    dsimp [outcomeDist,d]
    rw [Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re,Matrix.trace_mul_comm (E x) ρ,
      Matrix.trace_mul_comm (E x) σ]
  unfold kolmogorov
  simp_rw [hdif]
  rw [hsum]
  linarith

lemma binary_attains (ρ σ : Matrix n n ℂ) (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : ∃ E : Fin 2 → Matrix n n ℂ, IsPOVM E ∧
      kolmogorov (outcomeDist ρ E) (outcomeDist σ E)=(1/2 : ℝ)*traceNorm (ρ-σ) := by
  have ht : (ρ-σ).trace=0 := by simp [Matrix.trace_sub,hρ.2,hσ.2]
  obtain ⟨P,hP,hPI,hval⟩ := QValue20Support.QuantumValueHelstrom.maximizing_effect (ρ-σ)
    (hρ.1.isHermitian.sub hσ.1.isHermitian) ht
  let E : Fin 2 → Matrix n n ℂ := ![P,1-P]
  have hE : IsPOVM E := by
    constructor
    · intro x; fin_cases x <;> simp [E,hP,hPI]
    · simp [E,Fin.sum_univ_two]
  refine ⟨E,hE,?_⟩
  have hneg : ((1-P)*(ρ-σ)).trace.re= -(P*(ρ-σ)).trace.re := by
    simp [Matrix.sub_mul,Matrix.one_mul,Matrix.trace_sub,ht]
  have hdif (Q : Matrix n n ℂ) : (ρ*Q).trace.re-(σ*Q).trace.re=(Q*(ρ-σ)).trace.re := by
    rw [Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re,Matrix.trace_mul_comm Q ρ,
      Matrix.trace_mul_comm Q σ]
  simp only [kolmogorov,outcomeDist,Fin.sum_univ_two]
  change (1/2 : ℝ)*(|(ρ*P).trace.re-(σ*P).trace.re|+
    |(ρ*(1-P)).trace.re-(σ*(1-P)).trace.re|)=_
  rw [hdif,hdif,hneg,abs_neg,hval,abs_of_nonneg (mul_nonneg (by norm_num)
    (QValue20Support.QuantumValueTrace.traceNorm_nonneg _))]
  ring

lemma quantum_kolmogorov (ρ σ : Matrix n n ℂ) (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : qKolmogorov ρ σ=(1/2 : ℝ)*traceNorm (ρ-σ) := by
  obtain ⟨E,hE,hval⟩ := binary_attains ρ σ hρ hσ
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨2,E,hE,hval.symm⟩
  · rintro x ⟨m,F,hF,rfl⟩
    exact kolmogorov_bound ρ σ hρ hσ F hF

lemma error_kolmogorov (ρ σ : Matrix n n ℂ) (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) {m : ℕ} (E : Fin m → Matrix n n ℂ) (hE : IsPOVM E) :
    errorProb (outcomeDist ρ E) (outcomeDist σ E)=
      (1/2 : ℝ)-(1/2 : ℝ)*kolmogorov (outcomeDist ρ E) (outcomeDist σ E) := by
  have ha (a b : ℝ) : min a b=(a+b-|a-b|)/2 := by
    rcases le_total a b with h|h
    · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
  unfold errorProb kolmogorov
  simp_rw [ha]
  rw [← Finset.sum_div,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    sum_outcomes ρ E hE,sum_outcomes σ E hE,hρ.2,hσ.2]
  norm_num
  ring

lemma quantum_error (ρ σ : Matrix n n ℂ) (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : qErrorProb ρ σ=(1/2 : ℝ)-(1/4 : ℝ)*traceNorm (ρ-σ) := by
  obtain ⟨E,hE,hval⟩ := binary_attains ρ σ hρ hσ
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨2,E,hE,?_⟩
    rw [error_kolmogorov ρ σ hρ hσ E hE,hval]
    ring
  · rintro x ⟨m,F,hF,rfl⟩
    rw [error_kolmogorov ρ σ hρ hσ F hF]
    have hb := kolmogorov_bound ρ σ hρ hσ F hF
    linarith
end QValue20Support.QuantumValueOperational

end

open Matrix WildeQIT FuchsVdGraaf
open scoped MatrixOrder ComplexOrder ComplexConjugate Kronecker




/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, Proposition 1, eq. (17), p.11: for two
arbitrary density matrices `ρ₀`, `ρ₁`, the (quantum) probability of error equals
`PE(ρ₀, ρ₁) = ½ − ¼ ∑_{j=1}^{N} |λ_j| = ½ − ¼ Tr|ρ₀ − ρ₁|`, where the `λ_j` are the eigenvalues
of `ρ₀ − ρ₁`.

**Formalization Note.** `PE(ρ₀, ρ₁)` is `qErrorProb`, the infimum over all POVMs with any finite
number of outcomes. The eigenvalues are those of the Hermitian matrix `ρ₀ − ρ₁`
(`Matrix.IsHermitian.eigenvalues`, listed with multiplicity), the Hermitian proof being derived
from the two density-matrix hypotheses. `Tr|ρ₀ − ρ₁|` is the published `WildeQIT.traceNorm`. -/
theorem solution {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1) :
    qErrorProb ρ0 ρ1 =
        1 / 2 - 1 / 4 * ∑ j, |(h0.1.isHermitian.sub h1.1.isHermitian).eigenvalues j| ∧
      qErrorProb ρ0 ρ1 = 1 / 2 - 1 / 4 * WildeQIT.traceNorm (ρ0 - ρ1) := by
  have h := QValue20Support.QuantumValueOperational.quantum_error ρ0 ρ1 h0 h1
  exact ⟨by simpa only [QValue20Support.QuantumValueHelstrom.traceNorm_hermitian (ρ0-ρ1) (h0.1.isHermitian.sub h1.1.isHermitian)] using h,h⟩