-- Prove2me | solution 1 for BookProof.ComputableScarcity.exists_not_eventually_eq_computable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:41:27.519524+00:00
-- url     : https://prove2.me/submissions/bffee34b-b271-4cae-bcf3-ed8c9a379ecf

-- Generated from ChapterComputableScarcity.lean — solution of BookProof.ComputableScarcity.exists_not_eventually_eq_computable
import Mathlib
import Definitions.Def_ChapterComputableScarcity
import Theorems.Thm_BookProof_ComputableScarcity_exists_differs_infinitely_often_from_all_computable
open BookProof.ComputableScarcity




open Nat.Partrec

open Classical

set_option maxHeartbeats 1000000 in
theorem solution :
    ∃ f : ℕ → ℕ, ∀ g : ℕ → ℕ, Computable g → ¬ (∀ᶠ n in Filter.atTop, f n = g n) := by

  obtain ⟨f, hf⟩ := exists_differs_infinitely_often_from_all_computable
  refine ⟨f, fun g hg hev => ?_⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine (hf g hg) (Set.Finite.subset (Set.finite_Iio N) ?_)
  intro n hn
  by_contra hlt
  exact hn (hN n (by simpa [Set.mem_Iio] using not_lt.mp hlt))
