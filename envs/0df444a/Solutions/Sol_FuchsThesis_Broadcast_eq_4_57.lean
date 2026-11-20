-- Prove2me | solution 1 for FuchsThesis.Broadcast.eq_4_57
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-19T22:06:16.703666+00:00
-- url     : https://prove2.me/submissions/837d86fd-688d-427c-9758-d2b359969bd9

import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_fidelity
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing
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
open Matrix WildeQIT
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QValue20Support.QuantumValueIsometry

lemma sqrt_isometry {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (B : Matrix n n ℂ) (hB : B.PosSemidef) (V : Matrix m n ℂ) (hV : Vᴴ*V=1) :
    CFC.sqrt (V*B*Vᴴ)=V*CFC.sqrt B*Vᴴ := by
  have hY := (show (CFC.sqrt B).PosSemidef from (CFC.sqrt_nonneg B).posSemidef).mul_mul_conjTranspose_same V
  apply (CFC.sqrt_eq_iff _ _ (hB.mul_mul_conjTranspose_same V).nonneg hY.nonneg).mpr
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᴴ V,hV,Matrix.one_mul,
    ← Matrix.mul_assoc (CFC.sqrt B) (CFC.sqrt B),CFC.sqrt_mul_sqrt_self B hB.nonneg]

lemma isometric {m n m' n' : Type} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    [DecidableEq m] [DecidableEq n] [DecidableEq n']
    (M : Matrix m n ℂ) (U : Matrix m' m ℂ) (V : Matrix n' n ℂ)
    (hU : Uᴴ*U=1) (hV : Vᴴ*V=1) : traceNorm (U*M*Vᴴ)=traceNorm M := by
  have hG : (U*M*Vᴴ)ᴴ*(U*M*Vᴴ)=V*(Mᴴ*M)*Vᴴ := by
    simp only [conjTranspose_mul,conjTranspose_conjTranspose,Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U,hU,Matrix.one_mul]
  unfold traceNorm
  rw [hG,sqrt_isometry _ (posSemidef_conjTranspose_mul_self M) V hV,
    trace_mul_cycle,hV,Matrix.one_mul]

end QValue20Support.QuantumValueIsometry

end

noncomputable section
open Matrix Unitary WildeQIT
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QValue20Support.QuantumValueAdjoint
variable {n : Type} [Fintype n] [DecidableEq n]
lemma sqrt_eq_cfc_real (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    CFC.sqrt A=cfc Real.sqrt A := by
  rw [CFC.sqrt_eq_rpow,CFC.rpow_eq_cfc_real hA.nonneg]
  congr 1
  funext x
  exact (Real.sqrt_eq_rpow x).symm

lemma cfc_trace_conj (A : Matrix n n ℂ) (hA : A.IsHermitian) (U : unitary (Matrix n n ℂ))
    (f : ℝ → ℝ) (hf : Continuous f) :
    (cfc f ((U : Matrix n n ℂ)*A*(U : Matrix n n ℂ)ᴴ)).trace=(cfc f A).trace := by
  let φ := (conjStarAlgAut ℂ (Matrix n n ℂ) U).toStarAlgHom
  have hφ : Continuous φ := φ.toLinearMap.toContinuousLinearMap.continuous
  have hφA : IsSelfAdjoint (φ A) := (show IsSelfAdjoint A from hA).map φ
  have he := φ.map_cfc f A hf.continuousOn hφ hA hφA
  change (cfc f (φ A)).trace=(cfc f A).trace
  rw [← he]
  change ((U : Matrix n n ℂ)*(cfc f A)*(U : Matrix n n ℂ)ᴴ).trace=(cfc f A).trace
  have hU : (U : Matrix n n ℂ)ᴴ*(U : Matrix n n ℂ)=1 := Unitary.coe_star_mul_self U
  rw [trace_mul_cycle,hU,Matrix.one_mul]

lemma traceNorm_adjoint (A : Matrix n n ℂ) : traceNorm Aᴴ=traceNorm A := by
  obtain ⟨U,V,s,hs,hA,hcalc⟩ := QValue20Support.RecoveryMatrixSVD.gram_svd A
  let D : Matrix n n ℂ := diagonal (fun i => (s i : ℂ))
  have hD : Dᴴ=D := by simp [D,diagonal_conjTranspose]
  have hG : A*Aᴴ=(U : Matrix n n ℂ)*(D*D)*(U : Matrix n n ℂ)ᴴ := by
    rw [hA]
    change (((U : Matrix n n ℂ)*D*(V : Matrix n n ℂ))*
      ((U : Matrix n n ℂ)*D*(V : Matrix n n ℂ))ᴴ) = _
    simp only [conjTranspose_mul,hD,Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (V : Matrix n n ℂ) (V : Matrix n n ℂ)ᴴ,show (V : Matrix n n ℂ)*(V : Matrix n n ℂ)ᴴ=1 from Unitary.coe_mul_star_self V,Matrix.one_mul]
  have hG' : Aᴴ*A=(V : Matrix n n ℂ)ᴴ*(D*D)*(V : Matrix n n ℂ) := by
    rw [hA]
    change (((U : Matrix n n ℂ)*D*(V : Matrix n n ℂ))ᴴ*
      ((U : Matrix n n ℂ)*D*(V : Matrix n n ℂ))) = _
    simp only [conjTranspose_mul,hD,Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix n n ℂ)ᴴ (U : Matrix n n ℂ),show (U : Matrix n n ℂ)ᴴ*(U : Matrix n n ℂ)=1 from Unitary.coe_star_mul_self U,Matrix.one_mul]
  have hDD : (D*D).IsHermitian := by
    change (D*D)ᴴ=D*D
    rw [conjTranspose_mul,hD]
  unfold traceNorm
  rw [conjTranspose_conjTranspose,sqrt_eq_cfc_real _ (show (A*Aᴴ).PosSemidef by simpa using posSemidef_conjTranspose_mul_self Aᴴ),
    sqrt_eq_cfc_real _ (posSemidef_conjTranspose_mul_self A),hG,hG']
  have hh := cfc_trace_conj (D*D) hDD (star V) Real.sqrt Real.continuous_sqrt
  simp only [Unitary.coe_star,Matrix.star_eq_conjTranspose,conjTranspose_conjTranspose] at hh
  rw [cfc_trace_conj (D*D) hDD U Real.sqrt Real.continuous_sqrt,hh]

lemma rectangular {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m n ℂ) :
    traceNorm Aᴴ=traceNorm A := by
  let U : Matrix (m ⊕ n) m ℂ := fromRows 1 0
  let V : Matrix (m ⊕ n) n ℂ := fromRows 0 1
  have hU : Uᴴ*U=1 := by simp [U,conjTranspose_fromRows_eq_fromCols_conjTranspose,fromCols_mul_fromRows]
  have hV : Vᴴ*V=1 := by simp [V,conjTranspose_fromRows_eq_fromCols_conjTranspose,fromCols_mul_fromRows]
  calc
    traceNorm Aᴴ=traceNorm (V*Aᴴ*Uᴴ) := (QValue20Support.QuantumValueIsometry.isometric Aᴴ V U hV hU).symm
    _=traceNorm (U*A*Vᴴ)ᴴ := by simp only [conjTranspose_mul,conjTranspose_conjTranspose,Matrix.mul_assoc]
    _=traceNorm (U*A*Vᴴ) := traceNorm_adjoint _
    _=traceNorm A := QValue20Support.QuantumValueIsometry.isometric A U V hU hV
end QValue20Support.QuantumValueAdjoint

end

noncomputable section
open Matrix Unitary WildeQIT QValue20Support.QuantumValueTrace
open QAlgorithms.Papers.Independent.Information100.P50
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace QValue20Support.QuantumValueGentle
variable {n : Type} [Fintype n] [DecidableEq n]

lemma sqrt_star (A : Matrix n n ℂ) : (CFC.sqrt A)ᴴ=CFC.sqrt A := by
  change star (CFC.sqrt A)=CFC.sqrt A
  exact (CFC.sqrt_nonneg A).star_eq

lemma hs_unitary (U : unitary (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    schattenNorm 2 ((U : Matrix n n ℂ)*A)=schattenNorm 2 A := by
  have hU : (U : Matrix n n ℂ)ᴴ*(U : Matrix n n ℂ)=1 := Unitary.coe_star_mul_self U
  rw [QValue20Support.RecoverySchatten.schatten_two,QValue20Support.RecoverySchatten.schatten_two]
  congr 2
  rw [conjTranspose_mul,Matrix.mul_assoc,← Matrix.mul_assoc (U : Matrix n n ℂ)ᴴ (U : Matrix n n ℂ),hU,Matrix.one_mul]

lemma product_bound (X Y : Matrix n n ℂ) :
    traceNorm (X*Y) ≤ schattenNorm 2 X*schattenNorm 2 Y := by
  obtain ⟨U,hU,hu⟩ := (variational (X*Y)).1
  rw [hu]
  have ht : ((X*Y)*U).trace=((U*X)*Y).trace := trace_mul_cycle X Y U
  rw [ht]
  exact (QValue20Support.RecoveryTraceBounds.trace_hilbert_schmidt_bound (U*X) Y).trans_eq
    (by rw [hs_unitary ⟨U,hU⟩ X])

lemma hs_adjoint (A : Matrix n n ℂ) : schattenNorm 2 Aᴴ=schattenNorm 2 A := by
  rw [QValue20Support.RecoverySchatten.schatten_two,QValue20Support.RecoverySchatten.schatten_two,
    conjTranspose_conjTranspose,trace_mul_comm A Aᴴ]

lemma positive_product_trace (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A*B).trace.re := by
  have hh := (hB.mul_mul_conjTranspose_same (CFC.sqrt A)).trace_nonneg
  rw [sqrt_star,trace_mul_cycle,CFC.sqrt_mul_sqrt_self A hA.nonneg] at hh
  exact (Complex.nonneg_iff.mp hh).1

lemma gentle (ρ L : Matrix n n ℂ) (hρ : IsDensityOperator ρ)
    (hL : L.PosSemidef) (hLI : (1-L).PosSemidef) (ε : ℝ) (hε : 0 ≤ ε)
    (hdet : 1-ε ≤ (L*ρ).trace.re) :
    traceNorm (ρ-CFC.sqrt L*ρ*CFC.sqrt L) ≤ 2*Real.sqrt ε := by
  let S := CFC.sqrt L
  let T := CFC.sqrt ρ
  have hS : Sᴴ=S := sqrt_star L
  have hT : Tᴴ=T := sqrt_star ρ
  have hS2 : S*S=L := CFC.sqrt_mul_sqrt_self L hL.nonneg
  have hT2 : T*T=ρ := CFC.sqrt_mul_sqrt_self ρ hρ.1.nonneg
  have hS0 : 0 ≤ S := CFC.sqrt_nonneg L
  have hS1 : S ≤ 1 := by
    have hh := CFC.sqrt_le_sqrt L 1 (sub_nonneg.mp hLI.nonneg)
    simpa only [CFC.sqrt_one] using hh
  have hc : Commute S (1-S) := (Commute.one_right S).sub_right (Commute.refl S)
  have hSL : (S-L).PosSemidef := by
    have hh := hc.mul_nonneg hS0 (sub_nonneg.mpr hS1)
    rw [Matrix.mul_sub,Matrix.mul_one,hS2] at hh
    exact hh.posSemidef
  let p : ℝ := (S*ρ*S).trace.re
  let s : ℝ := (S*ρ).trace.re
  let d : ℝ := ((1-S)*ρ*(1-S)).trace.re
  have hp : p=(L*ρ).trace.re := by dsimp [p]; rw [trace_mul_cycle,hS2]
  have hp0 : 0 ≤ p := by
    have hh := (hρ.1.mul_mul_conjTranspose_same S).trace_nonneg
    rw [hS] at hh
    exact (Complex.nonneg_iff.mp hh).1
  have hp1 : p ≤ 1 := by
    have hh := positive_product_trace (1-L) ρ hLI hρ.1
    rw [Matrix.sub_mul,Matrix.one_mul,trace_sub,hρ.2,Complex.sub_re,Complex.one_re,← hp] at hh
    linarith
  have hsp : p ≤ s := by
    have hh := positive_product_trace (S-L) ρ hSL hρ.1
    rw [Matrix.sub_mul,trace_sub,Complex.sub_re,← hp] at hh
    exact sub_nonneg.mp hh
  have hd0 : 0 ≤ d := by
    have hh := (hρ.1.mul_mul_conjTranspose_same (1-S)).trace_nonneg
    rw [conjTranspose_sub,conjTranspose_one,hS] at hh
    exact (Complex.nonneg_iff.mp hh).1
  have hd : d=1-2*s+p := by
    have he : (1-S)*ρ*(1-S)=ρ-S*ρ-ρ*S+S*ρ*S := by noncomm_ring
    have hc' : (ρ*S).trace=(S*ρ).trace := trace_mul_comm _ _
    dsimp [d,p,s]
    rw [he,trace_add,trace_sub,trace_sub,hρ.2,hc']
    simp only [Complex.add_re,Complex.sub_re,Complex.one_re]
    ring
  have hdε : d ≤ ε := by rw [← hp] at hdet; linarith
  let X := (1-S)*T
  let Y := T
  let Z := S*T
  have hXX : X*Xᴴ=(1-S)*ρ*(1-S) := by
    dsimp [X]
    rw [conjTranspose_mul,hT,conjTranspose_sub,conjTranspose_one,hS]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc T T,hT2]
  have hZZ : Z*Zᴴ=S*ρ*S := by
    dsimp [Z]
    rw [conjTranspose_mul,hT,hS]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc T T,hT2]
  have hx : schattenNorm 2 X=Real.sqrt d := by
    rw [← hs_adjoint X,QValue20Support.RecoverySchatten.schatten_two,conjTranspose_conjTranspose,hXX]
  have hxa : schattenNorm 2 Xᴴ=Real.sqrt d := by rw [hs_adjoint,hx]
  have hy : schattenNorm 2 Y=1 := by
    rw [QValue20Support.RecoverySchatten.schatten_two,hT,hT2,hρ.2]
    norm_num
  have hz : schattenNorm 2 Z=Real.sqrt p := by
    rw [← hs_adjoint Z,QValue20Support.RecoverySchatten.schatten_two,conjTranspose_conjTranspose,hZZ]
  have hf : ρ-S*ρ*S=X*Y+Z*Xᴴ := by
    calc
      ρ-S*ρ*S=T*T-S*(T*T)*S := by rw [hT2]
      _=X*Y+Z*Xᴴ := by
        dsimp [X,Y,Z]
        rw [conjTranspose_mul,hT,conjTranspose_sub,conjTranspose_one,hS]
        noncomm_ring
  have hb := (triangle (X*Y) (Z*Xᴴ)).trans (add_le_add (product_bound X Y) (product_bound Z Xᴴ))
  rw [hx,hxa,hy,hz,mul_one] at hb
  have hpR : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp1
  have hmul := mul_le_mul_of_nonneg_right hpR (Real.sqrt_nonneg d)
  have hdR := Real.sqrt_le_sqrt hdε
  change traceNorm (ρ-S*ρ*S) ≤ _
  rw [hf]
  nlinarith

end QValue20Support.QuantumValueGentle

end

noncomputable section
open Matrix WildeQIT QValue20Support.QuantumValueGentle
open scoped MatrixOrder ComplexOrder ComplexConjugate Kronecker Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace QValue20Support.QuantumValueFidelity
variable {n : Type} [Fintype n] [DecidableEq n]

lemma root_eq_traceNorm (ρ σ : Matrix n n ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    QAlgorithms.rootFidelity ρ σ=traceNorm (CFC.sqrt σ*CFC.sqrt ρ) := by
  unfold QAlgorithms.rootFidelity traceNorm
  rw [conjTranspose_mul,sqrt_star,sqrt_star]
  have he : CFC.sqrt ρ*CFC.sqrt σ*(CFC.sqrt σ*CFC.sqrt ρ)=CFC.sqrt ρ*σ*CFC.sqrt ρ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (CFC.sqrt σ) (CFC.sqrt σ),CFC.sqrt_mul_sqrt_self σ hσ.nonneg]
  have hg : (CFC.sqrt ρ*σ*CFC.sqrt ρ).PosSemidef := by
    simpa only [sqrt_star] using hσ.mul_mul_conjTranspose_same (CFC.sqrt ρ)
  rw [he,QValue20Support.QuantumValueAdjoint.sqrt_eq_cfc_real _ hg,QValue20Support.QuantumValueAdjoint.sqrt_eq_cfc_real ρ hρ]

lemma symmetry (ρ σ : Matrix n n ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    QAlgorithms.rootFidelity σ ρ=QAlgorithms.rootFidelity ρ σ := by
  rw [root_eq_traceNorm ρ σ hρ hσ,root_eq_traceNorm σ ρ hσ hρ,
    ← QValue20Support.QuantumValueAdjoint.traceNorm_adjoint (CFC.sqrt σ*CFC.sqrt ρ)]
  simp only [conjTranspose_mul,sqrt_star]

lemma unitary_invariance (ρ σ U : Matrix n n ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    QAlgorithms.rootFidelity (U*ρ*Uᴴ) (U*σ*Uᴴ)=QAlgorithms.rootFidelity ρ σ := by
  have hUU : Uᴴ*U=1 := Unitary.coe_star_mul_self ⟨U,hU⟩
  rw [root_eq_traceNorm _ _ (hρ.mul_mul_conjTranspose_same U) (hσ.mul_mul_conjTranspose_same U),
    root_eq_traceNorm ρ σ hρ hσ,QValue20Support.QuantumValueIsometry.sqrt_isometry σ hσ U hUU,
    QValue20Support.QuantumValueIsometry.sqrt_isometry ρ hρ U hUU]
  have he : U*CFC.sqrt σ*Uᴴ*(U*CFC.sqrt ρ*Uᴴ)=U*(CFC.sqrt σ*CFC.sqrt ρ)*Uᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U,hUU,Matrix.one_mul]
  rw [he,QValue20Support.QuantumValueIsometry.isometric _ U U hUU hUU]

lemma sqrt_kronecker {m : Type} [Fintype m] [DecidableEq m]
    (A : Matrix n n ℂ) (B : Matrix m m ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    CFC.sqrt (A ⊗ₖ B)=CFC.sqrt A ⊗ₖ CFC.sqrt B := by
  apply (CFC.sqrt_eq_iff _ _ (hA.kronecker hB).nonneg
    ((CFC.sqrt_nonneg A).posSemidef.kronecker (CFC.sqrt_nonneg B).posSemidef).nonneg).mpr
  rw [← mul_kronecker_mul,CFC.sqrt_mul_sqrt_self A hA.nonneg,
    CFC.sqrt_mul_sqrt_self B hB.nonneg]

lemma traceNorm_kronecker {m : Type} [Fintype m] [DecidableEq m]
    (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    traceNorm (A ⊗ₖ B)=traceNorm A*traceNorm B := by
  unfold traceNorm
  rw [conjTranspose_kronecker,← mul_kronecker_mul,
    sqrt_kronecker _ _ (posSemidef_conjTranspose_mul_self A) (posSemidef_conjTranspose_mul_self B),
    trace_kronecker]
  have ha := (Complex.nonneg_iff.mp (CFC.sqrt_nonneg (Aᴴ*A)).posSemidef.trace_nonneg).2
  simp only [Complex.mul_re,← ha,zero_mul,sub_zero]

lemma product {m : Type} [Fintype m] [DecidableEq m]
    (ρ σ : Matrix n n ℂ) (τ υ : Matrix m m ℂ)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hτ : τ.PosSemidef) (hυ : υ.PosSemidef) :
    QAlgorithms.rootFidelity (ρ ⊗ₖ τ) (σ ⊗ₖ υ)=
      QAlgorithms.rootFidelity ρ σ*QAlgorithms.rootFidelity τ υ := by
  rw [root_eq_traceNorm _ _ (hρ.kronecker hτ) (hσ.kronecker hυ),
    sqrt_kronecker _ _ hσ hυ,sqrt_kronecker _ _ hρ hτ,← mul_kronecker_mul,
    traceNorm_kronecker,root_eq_traceNorm _ _ hρ hσ,root_eq_traceNorm _ _ hτ hυ]
end QValue20Support.QuantumValueFidelity

end

open Matrix WildeQIT
open scoped MatrixOrder ComplexOrder ComplexConjugate Kronecker




/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3, eq. (4.57), p.115 (PDF p.124): the fidelity
`F(ρ₀, ρ₁) = tr √(ρ₀^{1/2} ρ₁ ρ₀^{1/2})` (4.56) is invariant under the interchange `0 ↔ 1` and
under `ρ₀ → U ρ₀ U†`, `ρ₁ → U ρ₁ U†` for any unitary `U`.

**Formalization Note.** `F` is `QAlgorithms.rootFidelity`, which is (4.56) verbatim with square
roots `cfc Real.sqrt` (the positive square root on positive semidefinite matrices). The states are
positive semidefinite matrices on an arbitrary finite index type; the source states it for density
operators (trace one is not needed). -/
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (ρ0 ρ1 : Matrix ι ι ℂ)
    (hρ0 : ρ0.PosSemidef) (hρ1 : ρ1.PosSemidef) (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    QAlgorithms.rootFidelity ρ1 ρ0 = QAlgorithms.rootFidelity ρ0 ρ1 ∧
    QAlgorithms.rootFidelity (U * ρ0 * Uᴴ) (U * ρ1 * Uᴴ) = QAlgorithms.rootFidelity ρ0 ρ1 := by
  exact ⟨QValue20Support.QuantumValueFidelity.symmetry ρ0 ρ1 hρ0 hρ1,QValue20Support.QuantumValueFidelity.unitary_invariance ρ0 ρ1 U hρ0 hρ1 hU⟩