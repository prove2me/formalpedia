-- Prove2me | solution 1 for BookProof.FarisLavine.mulHamiltonian_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:42:54.158354+00:00
-- url     : https://prove2.me/submissions/510fad43-6220-4c69-913b-b15a969cc295

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
open scoped ENNReal
namespace BookProof.FarisLavine
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem inner_im_swap (a b : F) : (inner ℂ b a : ℂ).im = -(inner ℂ a b : ℂ).im := by
  rw [← inner_conj_symm (𝕜 := ℂ) a b, Complex.conj_im, neg_neg]

theorem commForm_eq (H N : D →ₗ[ℂ] F) (x : D) :
    commForm H N x = -2 * (inner ℂ (H x) (N x) : ℂ).im := by
  rw [commForm, Complex.mul_re]
  simp [Complex.sub_im, inner_im_swap (H x) (N x)]
  ring

@[simp] theorem mulSymbolOp_coe (lam s : ℕ → ℝ) (hs : ∀ n, |s n| ≤ |lam n|)
    (f : mulSymbolDomain lam) :
    ((mulSymbolOp lam s hs f : L2Nat) : ℕ → ℂ) = mulSymbolFun s ((f : L2Nat) : ℕ → ℂ) := rfl

theorem conj_mul_ofReal₂ (a b : ℝ) (z : ℂ) :
    (b : ℂ) * z * (starRingEnd ℂ) ((a : ℂ) * z) = ((a * b * Complex.normSq z : ℝ) : ℂ) := by
  rw [map_mul, Complex.conj_ofReal,
    show (b : ℂ) * z * ((a : ℂ) * (starRingEnd ℂ) z)
      = (a : ℂ) * (b : ℂ) * ((starRingEnd ℂ) z * z) by ring,
    ← Complex.normSq_eq_conj_mul_self]
  push_cast
  ring

theorem mulHamiltonian_commForm (lam : ℕ → ℝ) (x : mulSymbolDomain lam) :
    commForm (mulHamiltonian lam) (mulComparison lam) x = 0 := by
  rw [commForm_eq, lp.inner_eq_tsum, Complex.im_tsum (lp.summable_inner _ _)]
  have hterm : ∀ n : ℕ, (inner ℂ (((mulHamiltonian lam x : L2Nat) : ℕ → ℂ) n)
      (((mulComparison lam x : L2Nat) : ℕ → ℂ) n) : ℂ).im = 0 := by
    intro n
    have hn : (inner ℂ (((mulHamiltonian lam x : L2Nat) : ℕ → ℂ) n)
        (((mulComparison lam x : L2Nat) : ℕ → ℂ) n) : ℂ)
        = ((lam n * |lam n| * Complex.normSq (((x : L2Nat) : ℕ → ℂ) n) : ℝ) : ℂ) := by
      simpa only [mulHamiltonian, mulComparison, mulSymbolOp_coe, mulSymbolFun,
        RCLike.inner_apply] using conj_mul_ofReal₂ (lam n) (|lam n|) (((x : L2Nat) : ℕ → ℂ) n)
    rw [hn, Complex.ofReal_im]
  have hsum : ∑' n : ℕ, (inner ℂ (((mulHamiltonian lam x : L2Nat) : ℕ → ℂ) n)
      (((mulComparison lam x : L2Nat) : ℕ → ℂ) n) : ℂ).im = 0 := by
    calc ∑' n : ℕ, (inner ℂ (((mulHamiltonian lam x : L2Nat) : ℕ → ℂ) n)
          (((mulComparison lam x : L2Nat) : ℕ → ℂ) n) : ℂ).im
        = ∑' _ : ℕ, (0 : ℝ) := tsum_congr hterm
      _ = 0 := tsum_zero
  rw [hsum]
  ring

theorem mulHamiltonian_not_bounded (lam : ℕ → ℝ) (hlam : ∀ C : ℝ, ∃ n, C < |lam n|) :
    ¬ ∃ C : ℝ, ∀ f : mulSymbolDomain lam, ‖mulHamiltonian lam f‖ ≤ C * ‖(f : L2Nat)‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := hlam C
  have hb := hC (mulBasis lam n)
  have hval : (mulHamiltonian lam (mulBasis lam n) : L2Nat)
      = (lam n : ℂ) • lp.single 2 n (1 : ℂ) := by
    classical
    ext m
    change (lam m : ℂ) * (Pi.single n (1 : ℂ) : ℕ → ℂ) m = (lam n : ℂ) * (Pi.single n (1 : ℂ) : ℕ → ℂ) m
    by_cases hmn : m = n
    · subst hmn
      rfl
    · simp [Pi.single_eq_of_ne hmn]
  have hnorm : ‖(lp.single 2 n (1 : ℂ) : L2Nat)‖ = 1 := by
    simp
  rw [hval, norm_smul] at hb
  have hb' : |lam n| ≤ C := by
    have hcoe : ‖(mulBasis lam n : L2Nat)‖ = 1 := hnorm
    rw [hcoe] at hb
    simpa [hnorm] using hb
  exact absurd hn (not_lt.mpr hb')

theorem setup_mulBasis_value (lam : ℕ → ℝ) (n : ℕ) :
    (mulHamiltonian lam (mulBasis lam n) : L2Nat)
      = (lam n : ℂ) • lp.single 2 n (1 : ℂ) := by
  classical
  ext m
  change (lam m : ℂ) * (Pi.single n (1 : ℂ) : ℕ → ℂ) m = (lam n : ℂ) * (Pi.single n (1 : ℂ) : ℕ → ℂ) m
  by_cases hmn : m = n
  · subst hmn
    rfl
  · simp [Pi.single_eq_of_ne hmn]

theorem mulHamiltonian_essentiallySelfAdjoint (lam : ℕ → ℝ) :
    EssentiallySelfAdjointOn (mulSymbolDomain lam) (mulHamiltonian lam) := by
  have key (z : ℂ) (hz : z.im ≠ 0) :
      DeficiencyTrivialAt (mulSymbolDomain lam) (mulHamiltonian lam) z := by
    intro w hw
    ext n
    have h := hw (mulBasis lam n)
    rw [setup_mulBasis_value, inner_smul_left] at h
    simp only [mulBasis, lp.inner_single_left, RCLike.inner_apply, map_one,
      mul_one, one_mul, Complex.conj_ofReal] at h
    change (lam n : ℂ) * ((w : ℕ → ℂ) n) = z * ((w : ℕ → ℂ) n) at h
    have hp : ((lam n : ℂ) - z) * ((w : ℕ → ℂ) n) = 0 := by linear_combination h
    have hn : (lam n : ℂ) - z ≠ 0 := by
      apply sub_ne_zero.mpr
      intro hEq
      apply hz
      have hi := congrArg Complex.im hEq
      simpa using hi.symm
    exact (mul_eq_zero.mp hp).resolve_left hn
  exact ⟨key Complex.I (by simp), key (-Complex.I) (by simp)⟩

end BookProof.FarisLavine

open BookProof.FarisLavine
open scoped ENNReal

theorem solution (lam : ℕ → ℝ) :
    EssentiallySelfAdjointOn (mulSymbolDomain lam) (mulHamiltonian lam) := by
  exact BookProof.FarisLavine.mulHamiltonian_essentiallySelfAdjoint lam

#print axioms solution
