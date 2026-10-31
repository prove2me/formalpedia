-- Prove2me | solution 1 for Erdos624.palette_size_from_mean_error
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-30T14:11:02.579269+00:00
-- url     : https://prove2.me/submissions/4e38ecb0-7636-4b8e-a291-0f7698eb3603

import Mathlib
open Finset
namespace E624R17P
open Finset

/-- (PE) Each colour with non-positive mean contributes at least `2` to `Σ|μ-2|`, hence
`#J ≥ card C - E/2` when `J = {u | 0 < μ u}` and `Σ|μ-2| ≤ E`. -/
theorem palette_size_from_mean_error {C : Type*} [Fintype C]
    (μ : C → ℝ) (E : ℝ)
    (hE : ∑ u : C, |μ u - 2| ≤ E)
    (J : Finset C) (hJ : ∀ u : C, u ∈ J ↔ 0 < μ u) :
    (Fintype.card C : ℝ) - E / 2 ≤ (#J : ℝ) := by
  classical
  have hnon : ∀ u : C, u ∉ J → (2 : ℝ) ≤ |μ u - 2| := by
    intro u hu
    have hμ : μ u ≤ 0 := le_of_not_gt fun hpos => hu ((hJ u).2 hpos)
    have habs : |μ u - 2| = 2 - μ u := by
      rw [abs_of_nonpos]
      · ring
      · linarith
    linarith [habs]
  have hJsub : J ⊆ univ := subset_univ J
  have hcard : #((univ : Finset C) \ J) = Fintype.card C - #J := by
    rw [card_sdiff_of_subset hJsub, card_univ]
  have hsum : (2 : ℝ) * (#((univ : Finset C) \ J) : ℝ) ≤ ∑ u : C, |μ u - 2| := by
    calc (2 : ℝ) * (#((univ : Finset C) \ J) : ℝ)
        = ∑ _u ∈ (univ : Finset C) \ J, (2 : ℝ) := by
            simp [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ u ∈ (univ : Finset C) \ J, |μ u - 2| :=
            sum_le_sum fun u hu => hnon u (mem_sdiff.1 hu).2
      _ ≤ ∑ u : C, |μ u - 2| :=
            sum_le_sum_of_subset_of_nonneg sdiff_subset fun _ _ _ => abs_nonneg _
  have h2E : (2 : ℝ) * ((Fintype.card C - #J : ℕ) : ℝ) ≤ E := by
    simpa [hcard] using (le_trans hsum hE)
  have hcast : ((Fintype.card C - #J : ℕ) : ℝ) = (Fintype.card C : ℝ) - (#J : ℝ) :=
    Nat.cast_sub (card_le_univ J)
  linarith [hcast, h2E]

end E624R17P

namespace Erdos624

theorem palette_size_from_mean_error {C : Type*} [Fintype C]
    (μ : C → ℝ) (E : ℝ)
    (hE : ∑ u : C, |μ u - 2| ≤ E)
    (J : Finset C) (hJ : ∀ u : C, u ∈ J ↔ 0 < μ u) :
    (Fintype.card C : ℝ) - E / 2 ≤ (#J : ℝ) := by
  exact E624R17P.palette_size_from_mean_error μ E hE J hJ

end Erdos624

open Finset

theorem solution {C : Type*} [Fintype C]
    (μ : C → ℝ) (E : ℝ)
    (hE : ∑ u : C, |μ u - 2| ≤ E)
    (J : Finset C) (hJ : ∀ u : C, u ∈ J ↔ 0 < μ u) :
    (Fintype.card C : ℝ) - E / 2 ≤ (#J : ℝ) :=
  Erdos624.palette_size_from_mean_error μ E hE J hJ
