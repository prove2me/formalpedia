-- Prove2me | solution 1 for BookProof.NavierStokesFlow.Carleman.tridiag_hasZeroDeficiencyOn_of_carleman
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:06:34.541627+00:00
-- url     : https://prove2.me/submissions/7c9713bc-091e-4184-8e14-cc204ab529fd

-- Generated from ChapterNavierStokesCarleman.lean — solution of BookProof.NavierStokesFlow.Carleman.tridiag_hasZeroDeficiencyOn_of_carleman
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_tridiag_recursion_of_deficiency
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_sum_normSq_le
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_summable_mul_shift
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman



open scoped ENNReal



open LpNat DiagonalEsa FullEsa

set_option maxHeartbeats 1000000 in
theorem solution (c : ℕ → ℂ)
    (hcar : ¬ Summable fun n => 1 / ‖c n‖) :
    HasZeroDeficiencyOn (lpFiniteModes ℕ) (tridiagOp c) := by

  have key : ∀ (z : ℂ), z = Complex.I ∨ z = -Complex.I → ∀ w : L2N,
      (∀ v : lpFiniteModes ℕ, (inner ℂ ((tridiagOp c v : lpFiniteModes ℕ) : L2N) w : ℂ)
        = inner ℂ ((v : lpFiniteModes ℕ) : L2N) (z • w)) → w = 0 := by
    intro z hz w hw
    by_contra hne
    -- the recursion, normalized to the `+i` case by conjugating the state if necessary
    have hrec : ∀ n, tridiagFun c ((w : L2N) : ℕ → ℂ) n = z * ((w : L2N) : ℕ → ℂ) n :=
      tridiag_recursion_of_deficiency c z w hw
    have hkey : ∀ N, ∑ n ∈ Finset.range (N + 1), ‖((w : L2N) : ℕ → ℂ) n‖ ^ 2
        ≤ ‖c N‖ * (‖((w : L2N) : ℕ → ℂ) (N + 1)‖ * ‖((w : L2N) : ℕ → ℂ) N‖) := by
      intro N
      rcases hz with hz | hz
      · exact sum_normSq_le c _ (by simpa [hz] using hrec) N
      · -- for `z = -i` the conjugate state solves the `+i` recursion
        have hconj : ∀ n, tridiagFun (fun k => starRingEnd ℂ (c k))
            (fun k => starRingEnd ℂ (((w : L2N) : ℕ → ℂ) k)) n
              = Complex.I * starRingEnd ℂ (((w : L2N) : ℕ → ℂ) n) := by
          intro n
          have h := congrArg (starRingEnd ℂ) (hrec n)
          cases n with
          | zero =>
            simpa [tridiagFun, hz, map_mul, Complex.conj_I] using h
          | succ m =>
            simpa [tridiagFun, hz, map_add, map_mul, Complex.conj_I] using h
        have := sum_normSq_le (fun k => starRingEnd ℂ (c k))
          (fun k => starRingEnd ℂ (((w : L2N) : ℕ → ℂ) k)) hconj N
        simpa using this
    -- some coefficient is nonzero
    obtain ⟨n₀, hn₀⟩ : ∃ n₀, ((w : L2N) : ℕ → ℂ) n₀ ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hne (by ext n; simpa using hall n)
    set S := ∑ n ∈ Finset.range (n₀ + 1), ‖((w : L2N) : ℕ → ℂ) n‖ ^ 2 with hS
    have hSpos : 0 < S := by
      refine Finset.sum_pos' (fun n _ => sq_nonneg _) ⟨n₀, Finset.self_mem_range_succ n₀, ?_⟩
      have : ‖((w : L2N) : ℕ → ℂ) n₀‖ ≠ 0 := norm_ne_zero_iff.2 hn₀
      positivity
    -- Carleman's sum converges — contradiction
    refine hcar ?_
    have hmono : ∀ N, n₀ ≤ N → S ≤ ‖c N‖ * (‖((w : L2N) : ℕ → ℂ) (N + 1)‖
        * ‖((w : L2N) : ℕ → ℂ) N‖) := by
      intro N hN
      refine le_trans ?_ (hkey N)
      rw [hS]
      have hsub : Finset.range (n₀ + 1) ⊆ Finset.range (N + 1) :=
        Finset.range_subset_range.2 (by omega)
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => sq_nonneg _)
    have hbound : ∀ N, n₀ ≤ N → 1 / ‖c N‖
        ≤ (1 / S) * (‖((w : L2N) : ℕ → ℂ) N‖ * ‖((w : L2N) : ℕ → ℂ) (N + 1)‖) := by
      intro N hN
      have h := hmono N hN
      have hcN : 0 < ‖c N‖ := by
        rcases (norm_nonneg (c N)).lt_or_eq with h' | h'
        · exact h'
        · exfalso
          rw [← h'] at h
          nlinarith [hSpos]
      rw [div_le_iff₀ hcN]
      rw [one_div, inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hSpos]
      nlinarith [h, norm_nonneg (c N)]
    have hshift : Summable fun n : ℕ => 1 / ‖c (n + n₀)‖ := by
      have hmul : Summable fun n : ℕ =>
          ‖((w : L2N) : ℕ → ℂ) (n + n₀)‖ * ‖((w : L2N) : ℕ → ℂ) (n + n₀ + 1)‖ :=
        (summable_nat_add_iff n₀).2 (summable_mul_shift w)
      refine Summable.of_nonneg_of_le (fun n => by positivity)
        (fun n => hbound (n + n₀) (Nat.le_add_left _ _)) (hmul.mul_left (1 / S))
    exact (summable_nat_add_iff n₀).1 hshift
  exact ⟨key Complex.I (Or.inl rfl), fun w hw =>
    key (-Complex.I) (Or.inr rfl) w (by simpa using hw)⟩
