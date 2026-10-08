-- Prove2me | solution 1 for BookProof.ChapterA3x.projMixed_idem
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:56:13.890371+00:00
-- url     : https://prove2.me/submissions/7efa9e3f-1290-4df6-b6b7-45c4ddc070e9

-- Generated from ChapterA3x.lean — theorem BookProof.ChapterA3x.projMixed_idem
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3p
import Mathlib
import Definitions.Def_ChapterA3x
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3n
open BookProof.ChapterA3o
open BookProof.ChapterA3x


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open BookProof.ChapterA3p

namespace LocalChapterA3n
open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
theorem permMat_mul {N : ℕ} (σ τ : Equiv.Perm (Fin N)) :
    permMat σ * permMat τ = permMat (σ * τ) := by
  ext a c; simp only [mul_apply] ;
  unfold permMat; simp [ Finset.sum_ite ] ;
  rfl

theorem sum_permMat_sq {N : ℕ} :
    (∑ σ : Equiv.Perm (Fin N), permMat σ) * (∑ σ : Equiv.Perm (Fin N), permMat σ)
      = (Nat.factorial N : ℂ) • ∑ σ : Equiv.Perm (Fin N), permMat σ := by
  have h_sum : ∀ σ : Equiv.Perm (Fin N),
      ∑ τ : Equiv.Perm (Fin N), permMat (σ * τ) = ∑ τ : Equiv.Perm (Fin N), permMat τ :=
    fun σ => Equiv.sum_comp (Equiv.mulLeft σ) fun τ => permMat τ
  convert Finset.sum_congr rfl fun σ _ => h_sum σ using 1
  any_goals exact Finset.univ
  · simp [ Finset.sum_mul _ _ _, Finset.mul_sum, permMat_mul ]
  · simp [ Fintype.card_perm ]
    norm_num [ Algebra.smul_def ]

theorem projSym_idem {N : ℕ} : projSym N * projSym N = projSym N := by
  have h : (Nat.factorial N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  unfold projSym
  rw [Matrix.smul_mul, Matrix.mul_smul, sum_permMat_sq, smul_smul, smul_smul,
    mul_assoc, inv_mul_cancel₀ h, mul_one]
end LocalChapterA3n

namespace LocalChapterA3o
open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open LocalChapterA3n
theorem sum_signed_permMat_sq {N : ℕ} :
    (∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ) *
        (∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ)
      = (Nat.factorial N : ℂ) • ∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ := by
  
  have h_expand :
      (∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ) *
          (∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ)
        = ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
            (signC σ * signC τ) • permMat (σ * τ) := by
    simp only [Finset.sum_mul_sum]
    simp [mul_comm, smul_smul, permMat_mul]
  
  
  have h_inner_sum : ∀ σ : Equiv.Perm (Fin N),
      ∑ τ : Equiv.Perm (Fin N), (signC σ * signC τ) • permMat (σ * τ)
        = ∑ ρ : Equiv.Perm (Fin N), signC ρ • permMat ρ := by
    intro σ
    apply Finset.sum_bij (fun τ _ => σ * τ)
    · simp
    · aesop
    · exact fun b _ => ⟨σ⁻¹ * b, Finset.mem_univ _, by simp⟩
    · simp [signC]
  simp_all [Finset.card_univ, Fintype.card_perm]
  norm_num [Algebra.smul_def]

theorem projAnti_idem {N : ℕ} : projAnti N * projAnti N = projAnti N := by
  have h : (Nat.factorial N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  unfold projAnti
  rw [Matrix.smul_mul, Matrix.mul_smul, sum_signed_permMat_sq, smul_smul, smul_smul,
    mul_assoc, inv_mul_cancel₀ h, mul_one]
end LocalChapterA3o

namespace LocalChapterA3p
open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open LocalChapterA3n
theorem sum_signC_eq_zero {N : ℕ} (hN : 2 ≤ N) :
    ∑ σ : Equiv.Perm (Fin N), signC σ = 0 := by
  have h_transposition : ∃ t : Equiv.Perm (Fin N), Equiv.Perm.sign t = -1 := by
    exact ⟨ Equiv.swap ⟨ 0, by linarith ⟩ ⟨ 1, by linarith ⟩, by simp ⟩;
  obtain ⟨ t, ht ⟩ := h_transposition;    have := Equiv.sum_comp ( Equiv.mulLeft t ) ( fun x =>
      signC x ) ; simp_all only [signC, Equiv.coe_mulLeft, Equiv.Perm.sign_mul, neg_mul, one_mul,
          Units.val_neg, Int.cast_neg, Finset.sum_neg_distrib] ;
  linear_combination' -this / 2

theorem projAnti_mul_projSym {N : ℕ} (hN : 2 ≤ N) :
    projAnti N * projSym N = 0 := by
  unfold projAnti; unfold projSym;
  have h_sum_zero : ∑ σ : Equiv.Perm (Fin N),    ∑ τ : Equiv.Perm (Fin N),    signC σ • permMat (σ *
      τ) = ∑ σ : Equiv.Perm (Fin N),    ∑ τ : Equiv.Perm (Fin N), signC σ • permMat τ := by
    exact Finset.sum_congr rfl fun σ _ => Equiv.sum_comp ( Equiv.mulLeft σ ) fun τ => signC σ •
        permMat τ;
  convert congr_arg ( fun x : MN N => ( N.factorial : ℂ ) ⁻¹ • ( N.factorial : ℂ ) ⁻¹ • x )
      h_sum_zero using 1;
  · simp [ Finset.sum_mul _ _ _, Finset.mul_sum, smul_smul, Finset.smul_sum,
      LocalChapterA3n.permMat_mul ];
  · simp [ ← Finset.smul_sum, ← Finset.sum_smul, sum_signC_eq_zero hN ]

theorem projSym_mul_projAnti {N : ℕ} (hN : 2 ≤ N) :
    projSym N * projAnti N = 0 := by
  unfold projSym projAnti;
  
  have h_fubini : ∑ σ : Equiv.Perm (Fin N),    ∑ τ : Equiv.Perm (Fin N),    (signC τ • permMat (σ *
      τ)) = ∑ ρ : Equiv.Perm (Fin N),    (∑ σ : Equiv.Perm (Fin N), signC (σ * ρ)) • permMat ρ := by
    have h_fubini : ∀ σ : Equiv.Perm (Fin N),      ∑ τ : Equiv.Perm (Fin N),      (signC τ • permMat
        (σ * τ)) = ∑ ρ : Equiv.Perm (Fin N), (signC (σ * ρ) • permMat ρ) := by
      intro σ;
      apply Finset.sum_bij (fun τ _ => σ * τ);
      · simp;
      · aesop;
      · exact fun b _ => ⟨ σ⁻¹ * b, Finset.mem_univ _, by simp ⟩;
      · simp [ ← mul_assoc, signC ];
    rw [ Finset.sum_congr rfl fun σ _ => h_fubini σ, Finset.sum_comm ];
    simp only [Finset.sum_smul];
  convert congr_arg ( fun x : MN N => ( N.factorial : ℂ ) ⁻¹ ^ 2 • x ) h_fubini using 1;
  · simp [ sq, smul_smul, Finset.smul_sum, Finset.sum_mul ];
    simp [ Finset.mul_sum _ _ _, mul_assoc, Finset.smul_sum, smul_smul,
        LocalChapterA3n.permMat_mul ];
  · 
    
    have h_signC_sum : ∀ ρ : Equiv.Perm (Fin N),      ∑ σ : Equiv.Perm (Fin N), signC (σ * ρ) = ∑ σ
        : Equiv.Perm (Fin N), signC σ := by
      exact fun ρ => Equiv.sum_comp ( Equiv.mulRight ρ ) fun σ => signC σ;
    simp [ h_signC_sum, sum_signC_eq_zero hN ]
end LocalChapterA3p

open LocalChapterA3n LocalChapterA3o LocalChapterA3p

theorem projMixed_mul_projSym {N : ℕ} (hN : 2 ≤ N) :
    projMixed N * projSym N = 0 := by
  simp only [projMixed, sub_mul, one_mul, projSym_idem, projAnti_mul_projSym hN]
  abel

theorem projMixed_mul_projAnti {N : ℕ} (hN : 2 ≤ N) :
    projMixed N * projAnti N = 0 := by
  simp only [projMixed, sub_mul, one_mul, projAnti_idem, projSym_mul_projAnti hN]
  abel

theorem solution {N : ℕ} (hN : 2 ≤ N) :
    projMixed N * projMixed N = projMixed N := by
  conv_lhs => rw [show projMixed N * projMixed N
      = projMixed N * 1 - projMixed N * projSym N - projMixed N * projAnti N by
    simp only [projMixed, mul_sub, mul_one]]
  rw [projMixed_mul_projSym hN, projMixed_mul_projAnti hN, mul_one]
  abel

#print axioms solution
