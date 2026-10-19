-- Prove2me | solution 2 for BookProof.NavierStokesFlow.HermiteFarisLavine.commForm_ne_zero_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:51:44.289007+00:00
-- url     : https://prove2.me/submissions/40670aa4-2733-4f80-a8d1-d8749b7ed530

import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.commForm_ne_zero_of_pos
open BookProof.NavierStokesFlow.FockManyMode
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}


theorem solution (hκ : 0 < κ) :
    commForm (nsH κ (le_of_lt hκ)) (diagMax (oscSymbol κ)) (testState κ) ≠ 0 := by
  have hX : ∀ m, ((testState κ : L2I ℕ) : ℕ → ℂ) m = if m = 0 then 1 else if m = 2 then 1 else 0 := by
    intro m
    show ((lp.single 2 0 (1 : ℂ) + lp.single 2 2 (1 : ℂ) : L2I ℕ) : ℕ → ℂ) m = _
    rw [lp.coeFn_add, Pi.add_apply, lp.single_apply, lp.single_apply, Pi.single_apply, Pi.single_apply]
    rcases m with _ | _ | _ | m <;> simp
  have hH : ∀ m, ((nsH κ (le_of_lt hκ) (testState κ) : L2I ℕ) : ℕ → ℂ) m
      = hFun κ ((testState κ : L2I ℕ) : ℕ → ℂ) m := fun m => rfl
  have hN : ∀ m, ((diagMax (oscSymbol κ) (testState κ) : L2I ℕ) : ℕ → ℂ) m
      = (oscSymbol κ m : ℂ) * ((testState κ : L2I ℕ) : ℕ → ℂ) m := fun m => rfl
  have hNz : ∀ m, 5 ≤ m → ((diagMax (oscSymbol κ) (testState κ) : L2I ℕ) : ℕ → ℂ) m = 0 := by
    intro m hm
    rw [hN, hX]
    have h0 : m ≠ 0 := by omega
    have h2 : m ≠ 2 := by omega
    simp [h0, h2]
  have i1 : (inner ℂ (nsH κ (le_of_lt hκ) (testState κ) : L2I ℕ)
      (diagMax (oscSymbol κ) (testState κ) : L2I ℕ) : ℂ)
      = ∑ m ∈ Finset.range 5, (inner ℂ (hFun κ ((testState κ : L2I ℕ) : ℕ → ℂ) m)
          ((oscSymbol κ m : ℂ) * ((testState κ : L2I ℕ) : ℕ → ℂ) m) : ℂ) := by
    rw [lp.inner_eq_tsum, tsum_eq_sum (s := Finset.range 5)]
    · rfl
    · intro m hm
      simp only [Finset.mem_range, not_lt] at hm
      show (inner ℂ _ (((diagMax (oscSymbol κ) (testState κ) : L2I ℕ) : ℕ → ℂ) m) : ℂ) = 0
      rw [hNz m hm, inner_zero_right]
  have i2 : (inner ℂ (diagMax (oscSymbol κ) (testState κ) : L2I ℕ)
      (nsH κ (le_of_lt hκ) (testState κ) : L2I ℕ) : ℂ)
      = ∑ m ∈ Finset.range 5, (inner ℂ ((oscSymbol κ m : ℂ) * ((testState κ : L2I ℕ) : ℕ → ℂ) m)
          (hFun κ ((testState κ : L2I ℕ) : ℕ → ℂ) m) : ℂ) := by
    rw [lp.inner_eq_tsum, tsum_eq_sum (s := Finset.range 5)]
    · rfl
    · intro m hm
      simp only [Finset.mem_range, not_lt] at hm
      show (inner ℂ (((diagMax (oscSymbol κ) (testState κ) : L2I ℕ) : ℕ → ℂ) m) _ : ℂ) = 0
      rw [hNz m hm, inner_zero_left]
  unfold commForm
  rw [i1, i2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hFun, shift2, hX, RCLike.inner_apply]
  norm_num [oscSymbol]
  have ha : 0 < amp κ 0 := by
    unfold amp; norm_num; positivity
  intro h
  ring_nf at h
  nlinarith [mul_pos hκ ha]

