-- Prove2me | solution 1 for Formalism.G0.TypeIIUpP.arith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:34.375429+00:00
-- url     : https://prove2.me/submissions/9871e7cd-8cbb-4e1d-b7b5-7a8bacdcb2b5

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIUp
import Theorems.Thm_Formalism_G0_TypeIIUpP_gb_symm
import Theorems.Thm_Formalism_G0_qVandermondeIdentity


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.TypeIIUpP
namespace Formalism.G0.TypeIIUpP
theorem _root_.solution (q N g j ρ : ℕ) (hρ : ρ ≤ N) :
    (if ρ ≤ j then gaussBinom q (N + g - ρ) (j - ρ) else 0) =
      ∑ l ∈ Finset.range (j + 1), q ^ (l * (N + l - j)) * gaussBinom q g l *
        (if j - l ≤ N then gaussBinom q (N - ρ) (N - (j - l)) else 0) := by
  have hV := (qVandermondeIdentity q (N - ρ) g (j - ρ)).1
  have hz : ∀ n k : ℕ, n < k → gaussBinom q n k = 0 := by
    intro n
    induction n with
    | zero =>
      intro k hk
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp [gaussBinom]
    | succ n ih =>
      intro k hk
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hg : gaussBinom q (n + 1) (k + 1) =
          gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1) := by simp [gaussBinom]
      rw [hg, ih k (by omega), ih (k + 1) (by omega)]
      simp
  have key : ∀ l, ρ ≤ j → l ≤ j - ρ →
      q ^ (l * (N - ρ + l - (j - ρ))) * gaussBinom q (N - ρ) (j - ρ - l) * gaussBinom q g l =
        (q ^ (l * (N + l - j)) * gaussBinom q g l *
          if j - l ≤ N then gaussBinom q (N - ρ) (N - (j - l)) else 0) := by
    intro l hρj hl
    rw [show N - ρ + l - (j - ρ) = N + l - j by omega]
    split_ifs with hjl
    · rw [gb_symm q (N - ρ) (j - ρ - l) (by omega), show N - ρ - (j - ρ - l) = N - (j - l) by omega]
      ring
    · rw [hz (N - ρ) (j - ρ - l) (by omega)]
      ring
  have hzero : ∀ l, l ≤ j → j - l < ρ →
      (q ^ (l * (N + l - j)) * gaussBinom q g l *
        if j - l ≤ N then gaussBinom q (N - ρ) (N - (j - l)) else 0) = 0 := by
    intro l hl1 hl2
    split_ifs with hjl
    · rw [hz (N - ρ) (N - (j - l)) (by omega)]
      ring
    · ring
  split_ifs with hρj
  · rw [show N + g - ρ = N - ρ + g by omega, hV]
    calc _ = ∑ l ∈ Finset.range (j - ρ + 1), (q ^ (l * (N + l - j)) * gaussBinom q g l *
            if j - l ≤ N then gaussBinom q (N - ρ) (N - (j - l)) else 0) :=
          Finset.sum_congr rfl (fun l hl => key l hρj (by rw [Finset.mem_range] at hl; omega))
      _ = _ := Finset.sum_subset
          (by intro l hl; simp only [Finset.mem_range] at hl ⊢; omega)
          (fun l hl hl' => hzero l (by simp only [Finset.mem_range] at hl; omega)
            (by simp only [Finset.mem_range] at hl hl'; omega))
  · symm
    apply Finset.sum_eq_zero
    intro l hl
    rw [Finset.mem_range] at hl
    exact hzero l (by omega) (by omega)
end Formalism.G0.TypeIIUpP
