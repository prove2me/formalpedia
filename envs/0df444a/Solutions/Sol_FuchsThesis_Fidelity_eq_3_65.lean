-- Prove2me | solution 1 for FuchsThesis.Fidelity.eq_3_65
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T20:20:00.327899+00:00
-- url     : https://prove2.me/submissions/9abd83c3-7700-4d7b-8732-52174616e3bc

import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsVdGraaf_bhattacharyya
import Definitions.Def_FuchsVdGraaf_outcomeDist
import Definitions.Def_WildeQIT_IsDensityOperator
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Tactic.NoncommRing
import Theorems.Thm_FuchsThesis_Fidelity_eq_3_58
import Theorems.Thm_FuchsThesis_Fidelity_polar_attainer

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
namespace QNext_optimal_lower_bound.RecoveryMatrixSVD
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

end QNext_optimal_lower_bound.RecoveryMatrixSVD

end

noncomputable section
open Matrix Unitary
open QAlgorithms.Papers.Independent.Information100.P50
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QNext_optimal_lower_bound.RecoverySchatten
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
  obtain ⟨U,V,s,hs,_,hcalc⟩ := QNext_optimal_lower_bound.RecoveryMatrixSVD.gram_svd A
  rw [schatten_one_svd A V s hs hcalc]
  exact Finset.sum_nonneg fun i _ => hs i

end QNext_optimal_lower_bound.RecoverySchatten

end

noncomputable section
open Matrix Unitary
open QAlgorithms.Papers.Independent.Information100.P50
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QNext_optimal_lower_bound.RecoveryTraceBounds
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
  obtain ⟨U,V,s,hs,hA,hcalc⟩ := QNext_optimal_lower_bound.RecoveryMatrixSVD.gram_svd A
  rw [QNext_optimal_lower_bound.RecoverySchatten.schatten_one_svd A V s hs hcalc]
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
  rw [QNext_optimal_lower_bound.RecoverySchatten.schatten_two,QNext_optimal_lower_bound.RecoverySchatten.schatten_two,gram_trace,gram_trace]
  have ht : (X*A).trace = ∑ p : n×n, X p.1 p.2*A p.2 p.1 := by
    simp [Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_prod_type]
  rw [ht]
  calc
    _ ≤ ∑ p : n×n, ‖X p.1 p.2*A p.2 p.1‖ := norm_sum_le _ _
    _ = ∑ p : n×n, ‖X p.1 p.2‖*‖A p.2 p.1‖ := by simp only [norm_mul]
    _ ≤ Real.sqrt (∑ p : n×n, ‖X p.1 p.2‖^2)*Real.sqrt (∑ p : n×n, ‖A p.2 p.1‖^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by simp only [Fintype.sum_prod_type]; rw [Finset.sum_comm (f := fun i j => ‖A j i‖^2)]

end QNext_optimal_lower_bound.RecoveryTraceBounds

end

noncomputable section
open Matrix Unitary WildeQIT
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QNext_optimal_lower_bound.QuantumValueTrace
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
    QNext_optimal_lower_bound.RecoveryTraceBounds.trace_op_trace_bound A B

lemma traceNorm_nonneg (A : Matrix n n ℂ) : 0 ≤ traceNorm A := by
  rw [← schatten_bridge]
  exact QNext_optimal_lower_bound.RecoverySchatten.schatten_one_nonneg A

lemma traceNorm_svd (A : Matrix n n ℂ) (V : unitary (Matrix n n ℂ)) (s : n → ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hc : ∀ f : ℝ → ℝ, cfc f (Aᴴ*A)=
      (V : Matrix n n ℂ)ᴴ*diagonal (fun i => (f (s i^2) : ℂ))*(V : Matrix n n ℂ)) :
    traceNorm A=∑ i, s i := by
  rw [← schatten_bridge]
  exact QNext_optimal_lower_bound.RecoverySchatten.schatten_one_svd A V s hs hc

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
  obtain ⟨U,V,s,hs,hA,hc⟩ := QNext_optimal_lower_bound.RecoveryMatrixSVD.gram_svd A
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

end QNext_optimal_lower_bound.QuantumValueTrace

end

open Matrix WildeQIT
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

noncomputable section
open Matrix Unitary WildeQIT QNext_optimal_lower_bound.QuantumValueTrace
open QAlgorithms.Papers.Independent.Information100.P50
open scoped MatrixOrder ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace QNext_optimal_lower_bound.QuantumValueGentle
variable {n : Type} [Fintype n] [DecidableEq n]

lemma sqrt_star (A : Matrix n n ℂ) : (CFC.sqrt A)ᴴ=CFC.sqrt A := by
  change star (CFC.sqrt A)=CFC.sqrt A
  exact (CFC.sqrt_nonneg A).star_eq

lemma hs_unitary (U : unitary (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    schattenNorm 2 ((U : Matrix n n ℂ)*A)=schattenNorm 2 A := by
  have hU : (U : Matrix n n ℂ)ᴴ*(U : Matrix n n ℂ)=1 := Unitary.coe_star_mul_self U
  rw [QNext_optimal_lower_bound.RecoverySchatten.schatten_two,QNext_optimal_lower_bound.RecoverySchatten.schatten_two]
  congr 2
  rw [conjTranspose_mul,Matrix.mul_assoc,← Matrix.mul_assoc (U : Matrix n n ℂ)ᴴ (U : Matrix n n ℂ),hU,Matrix.one_mul]

lemma product_bound (X Y : Matrix n n ℂ) :
    traceNorm (X*Y) ≤ schattenNorm 2 X*schattenNorm 2 Y := by
  obtain ⟨U,hU,hu⟩ := (variational (X*Y)).1
  rw [hu]
  have ht : ((X*Y)*U).trace=((U*X)*Y).trace := trace_mul_cycle X Y U
  rw [ht]
  exact (QNext_optimal_lower_bound.RecoveryTraceBounds.trace_hilbert_schmidt_bound (U*X) Y).trans_eq
    (by rw [hs_unitary ⟨U,hU⟩ X])

lemma hs_adjoint (A : Matrix n n ℂ) : schattenNorm 2 Aᴴ=schattenNorm 2 A := by
  rw [QNext_optimal_lower_bound.RecoverySchatten.schatten_two,QNext_optimal_lower_bound.RecoverySchatten.schatten_two,
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
    rw [← hs_adjoint X,QNext_optimal_lower_bound.RecoverySchatten.schatten_two,conjTranspose_conjTranspose,hXX]
  have hxa : schattenNorm 2 Xᴴ=Real.sqrt d := by rw [hs_adjoint,hx]
  have hy : schattenNorm 2 Y=1 := by
    rw [QNext_optimal_lower_bound.RecoverySchatten.schatten_two,hT,hT2,hρ.2]
    norm_num
  have hz : schattenNorm 2 Z=Real.sqrt p := by
    rw [← hs_adjoint Z,QNext_optimal_lower_bound.RecoverySchatten.schatten_two,conjTranspose_conjTranspose,hZZ]
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

end QNext_optimal_lower_bound.QuantumValueGentle

end

noncomputable section
open Matrix Unitary WildeQIT FuchsVdGraaf QNext_optimal_lower_bound.QuantumValueGentle
open QAlgorithms.Papers.Independent.Information100.P50
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace QNext_optimal_lower_bound.QuantumNextFidelity
variable {n : Type} [Fintype n] [DecidableEq n]

theorem optimal_lower_bound (ρ0 ρ1 : Matrix n n ℂ) (h0 : IsDensityOperator ρ0)
    (h1 : IsDensityOperator ρ1) :
    ∃ Uc ∈ unitaryGroup n ℂ,
      Uc*CFC.sqrt ρ0*CFC.sqrt ρ1=CFC.sqrt (CFC.sqrt ρ1*ρ0*CFC.sqrt ρ1) ∧
      ‖(Uc*CFC.sqrt ρ0*CFC.sqrt ρ1).trace‖=
        (CFC.sqrt (CFC.sqrt ρ1*ρ0*CFC.sqrt ρ1)).trace.re ∧
      ∀ (m : ℕ) (E : Fin m → Matrix n n ℂ), IsPOVM E →
        ‖(Uc*CFC.sqrt ρ0*CFC.sqrt ρ1).trace‖ ≤
          bhattacharyya (outcomeDist ρ0 E) (outcomeDist ρ1 E) := by
  obtain ⟨U,hU,hu⟩ := FuchsThesis.Fidelity.polar_attainer (CFC.sqrt ρ0*CFC.sqrt ρ1)
  have hg : (CFC.sqrt ρ0*CFC.sqrt ρ1)ᴴ*(CFC.sqrt ρ0*CFC.sqrt ρ1)=
      CFC.sqrt ρ1*ρ0*CFC.sqrt ρ1 := by
    rw [conjTranspose_mul,sqrt_star,sqrt_star]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (CFC.sqrt ρ0) (CFC.sqrt ρ0),CFC.sqrt_mul_sqrt_self ρ0 h0.1.nonneg]
  rw [hg,← Matrix.mul_assoc] at hu
  refine ⟨U,hU,hu,?_,fun m E hE => FuchsThesis.Fidelity.eq_3_58 ρ0 ρ1 h0 h1 E hE U hU⟩
  rw [hu]
  have hp := (CFC.sqrt_nonneg (CFC.sqrt ρ1*ρ0*CFC.sqrt ρ1)).posSemidef.trace_nonneg
  have hc := Complex.nonneg_iff.mp hp
  rw [Complex.norm_def,Complex.normSq_apply,← hc.2]
  simp only [← pow_two,zero_pow (by decide : (2 : ℕ) ≠ 0),add_zero,Real.sqrt_sq hc.1]

end QNext_optimal_lower_bound.QuantumNextFidelity

end

open Matrix WildeQIT
open scoped MatrixOrder ComplexOrder ComplexConjugate

open FuchsVdGraaf

set_option autoImplicit false



/-- Fuchs, arXiv:quant-ph/9601020v1, eqs. (3.63) and (3.65), p.53 (PDF p.62): there is a unitary
`Û_c` with `Û_c ρ̂₀^{1/2} ρ̂₁^{1/2} = √(ρ̂₁^{1/2} ρ̂₀ ρ̂₁^{1/2})`, and for it, for every POVM,
`∑_b √p₀(b) √p₁(b) ≥ |tr(Û_c ρ̂₀^{1/2} ρ̂₁^{1/2})| = tr √(ρ̂₁^{1/2} ρ̂₀ ρ̂₁^{1/2})`.

**Formalization Note.** No invertibility is assumed. (3.63) uses `(ρ̂₀^{1/2} ρ̂₁^{1/2})†(ρ̂₀^{1/2}
ρ̂₁^{1/2}) = ρ̂₁^{1/2} ρ̂₀ ρ̂₁^{1/2}`. `Û_c` is chosen once, before the POVM, as in the source. The
left side is `FuchsVdGraaf.bhattacharyya`, equal to `∑_b √p₀(b) √p₁(b)` because `p_k(b) ≥ 0`. -/
theorem solution {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : IsDensityOperator ρ0) (h1 : IsDensityOperator ρ1) :
    ∃ Uc ∈ unitaryGroup n ℂ,
      Uc * CFC.sqrt ρ0 * CFC.sqrt ρ1 = CFC.sqrt (CFC.sqrt ρ1 * ρ0 * CFC.sqrt ρ1) ∧
      ‖Matrix.trace (Uc * CFC.sqrt ρ0 * CFC.sqrt ρ1)‖ =
        (Matrix.trace (CFC.sqrt (CFC.sqrt ρ1 * ρ0 * CFC.sqrt ρ1))).re ∧
      ∀ (m : ℕ) (E : Fin m → Matrix n n ℂ), IsPOVM E →
        bhattacharyya (outcomeDist ρ0 E) (outcomeDist ρ1 E) ≥
          ‖Matrix.trace (Uc * CFC.sqrt ρ0 * CFC.sqrt ρ1)‖ := by
 exact QNext_optimal_lower_bound.QuantumNextFidelity.optimal_lower_bound ρ0 ρ1 h0 h1