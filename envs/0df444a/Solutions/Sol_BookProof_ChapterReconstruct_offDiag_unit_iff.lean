-- Prove2me | solution 1 for BookProof.ChapterReconstruct.offDiag_unit_iff
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:51:54.477982+00:00
-- url     : https://prove2.me/submissions/f16697f3-4a68-4da7-ad54-7f4b1b64c25e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterReconstruct.lean — solution of BookProof.ChapterReconstruct.offDiag_unit_iff
import Mathlib
import Definitions.Def_ChapterReconstruct
import Theorems.Thm_BookProof_ChapterReconstruct_offDiag_of_isDeterministicCol
import Theorems.Thm_BookProof_ChapterReconstruct_isDeterministicCol_of_offDiag
open BookProof.ChapterReconstruct



open scoped BigOperators
open Finset


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U : Fin n → Fin n → ℂ) :
    (∀ (a : Fin n) (Ψ : Fin n → ℂ), (∑ k : Fin n, ‖Ψ k‖ ^ 2) = 1 →
        offDiag U a Ψ = 0) ↔ IsDeterministic U := by

  refine ⟨ fun hU => ?_, ?_ ⟩;
  · refine fun a => isDeterministicCol_of_offDiag U a ?_;
    intro Ψ
    by_cases hΨ : Ψ = 0;
    · simp [hΨ, BookProof.ChapterReconstruct.offDiag];
    · -- Let $c = \sqrt{\sum_{k} \| \Psi_k \|^2}$.
      set c := Real.sqrt (∑ k, ‖Ψ k‖ ^ 2) with hc_def
      have hc_pos : 0 < c := by
        exact Real.sqrt_pos.mpr
          ( lt_of_lt_of_le
            ( sq_pos_of_pos
              ( norm_pos_iff.mpr ( Classical.choose_spec ( Function.ne_iff.mp hΨ ) ) ) )
            ( Finset.single_le_sum ( fun k _ => sq_nonneg ( ‖Ψ k‖ ) )
              ( Finset.mem_univ ( Classical.choose ( Function.ne_iff.mp hΨ ) ) ) ) )
      have hc_unit : ∑ k, ‖(1 / c : ℂ) * Ψ k‖ ^ 2 = 1 := by
        simp only [one_div, Complex.norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
            mul_pow, inv_pow, sq_abs, ← Finset.mul_sum _ _ _];
        rw [ Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _, inv_mul_cancel₀ <| ne_of_gt
            <| lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) <| Ne.symm <|
                by contrapose! hΨ; ext i; simp_all  ]
      have hc_offDiag : offDiag U a ((1 / c : ℂ) • Ψ) = 0 := by
        exact hU a _ hc_unit
      have hc_offDiag_zero : offDiag U a Ψ = 0 := by
        convert congr_arg (fun x : ℂ => x * c ^ 2) hc_offDiag using 1 <;>
          norm_num [BookProof.ChapterReconstruct.offDiag, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, mul_comm] ;
          ring_nf ; norm_num [hc_pos.ne']
      exact hc_offDiag_zero
  · exact fun h a Ψ _ => offDiag_of_isDeterministicCol U a (h a) Ψ
