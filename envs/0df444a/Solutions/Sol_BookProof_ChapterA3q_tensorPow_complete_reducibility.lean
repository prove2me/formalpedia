-- Prove2me | solution 1 for BookProof.ChapterA3q.tensorPow_complete_reducibility
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:50:42.318326+00:00
-- url     : https://prove2.me/submissions/5c7e313e-0b8c-453a-8d9c-36004a633249

-- Generated from ChapterA3q.lean — theorem BookProof.ChapterA3q.tensorPow_complete_reducibility
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3p
import Mathlib
import Definitions.Def_ChapterA3q
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3n
open BookProof.ChapterA3o
open BookProof.ChapterA3q


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open BookProof.ChapterA3p
set_option autoImplicit false
open Matrix
open scoped BigOperators

namespace BookProof.ChapterA3n
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
end BookProof.ChapterA3n

namespace BookProof.ChapterA3o
open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
theorem sum_signed_permMat_sq {N : ℕ} :
    (∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ) *
        (∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ)
      = (Nat.factorial N : ℂ) • ∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ := by
  -- Expand the product of the two sums into a double sum over `σ`, `τ`.
  have h_expand :
      (∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ) *
          (∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ)
        = ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
            (signC σ * signC τ) • permMat (σ * τ) := by
    simp only [Finset.sum_mul_sum]
    simp [mul_comm, smul_smul, permMat_mul]
  -- For each fixed `σ`, reindex the inner sum by `ρ = σ * τ`; the signed scalar
  -- collapses to `signC ρ`, independent of `σ`.
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
end BookProof.ChapterA3o

namespace BookProof.ChapterA3p
open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
theorem sum_signC_eq_zero {N : ℕ} (hN : 2 ≤ N) :
    ∑ σ : Equiv.Perm (Fin N), signC σ = 0 := by
  have h_transposition : ∃ t : Equiv.Perm (Fin N), Equiv.Perm.sign t = -1 := by
    exact ⟨ Equiv.swap ⟨ 0, by linarith ⟩ ⟨ 1, by linarith ⟩, by simp ⟩;
  obtain ⟨ t, ht ⟩ := h_transposition;    have := Equiv.sum_comp ( Equiv.mulLeft t ) ( fun x =>
      signC x ) ; simp_all only [signC, Equiv.coe_mulLeft, Equiv.Perm.sign_mul, neg_mul, one_mul,
          Units.val_neg, Int.cast_neg, Finset.sum_neg_distrib] ;
  linear_combination' -this / 2

theorem projSym_mul_projAnti {N : ℕ} (hN : 2 ≤ N) :
    projSym N * projAnti N = 0 := by
  unfold projSym projAnti;
  -- By Fubini's theorem, we can interchange the order of summation.
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
        BookProof.ChapterA3n.permMat_mul ];
  · -- By definition of $signC$, we know that $\sum_{\sigma} signC(\sigma \rho) = \sum_{\sigma}
    -- signC(\sigma)$ for any $\rho$.
    have h_signC_sum : ∀ ρ : Equiv.Perm (Fin N),      ∑ σ : Equiv.Perm (Fin N), signC (σ * ρ) = ∑ σ
        : Equiv.Perm (Fin N), signC σ := by
      exact fun ρ => Equiv.sum_comp ( Equiv.mulRight ρ ) fun σ => signC σ;
    simp [ h_signC_sum, sum_signC_eq_zero hN ]

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
      BookProof.ChapterA3n.permMat_mul ];
  · simp [ ← Finset.smul_sum, ← Finset.sum_smul, sum_signC_eq_zero hN ]
end BookProof.ChapterA3p

open BookProof.ChapterA3 BookProof.ChapterA3n BookProof.ChapterA3o BookProof.ChapterA3q
open BookProof.ChapterA3p

theorem solution {N : ℕ} (hN : 2 ≤ N) :
    projSym N + projAnti N + projMixed N = 1 ∧
    projSym N * projSym N = projSym N ∧
    projAnti N * projAnti N = projAnti N ∧
    projMixed N * projMixed N = projMixed N ∧
    projSym N * projAnti N = 0 ∧ projAnti N * projSym N = 0 ∧
    projSym N * projMixed N = 0 ∧ projMixed N * projSym N = 0 ∧
    projAnti N * projMixed N = 0 ∧ projMixed N * projAnti N = 0 := by
  have hS := @projSym_idem N
  have hA := @projAnti_idem N
  have hSA := @projSym_mul_projAnti N hN
  have hAS := @projAnti_mul_projSym N hN
  refine ⟨?_, hS, hA, ?_, hSA, hAS, ?_, ?_, ?_, ?_⟩ <;>
    unfold projMixed <;>
    (try simp only [sub_mul, mul_sub, one_mul, mul_one, hS, hA, hSA, hAS]) <;> abel
#print axioms solution
