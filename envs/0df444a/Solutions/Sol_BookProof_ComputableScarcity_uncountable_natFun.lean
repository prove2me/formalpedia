-- Prove2me | solution 1 for BookProof.ComputableScarcity.uncountable_natFun
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:41:13.09482+00:00
-- url     : https://prove2.me/submissions/afd9b58c-bf6e-4c18-967b-4fbe6089154b

-- Generated from ChapterComputableScarcity.lean — solution of BookProof.ComputableScarcity.uncountable_natFun
import Mathlib
import Definitions.Def_ChapterComputableScarcity
import Theorems.Thm_BookProof_ComputableScarcity_exists_infinitely_often_ne
open BookProof.ComputableScarcity




open Nat.Partrec

open Classical

set_option maxHeartbeats 1000000 in
theorem solution : ¬ Countable (ℕ → ℕ) := by

  intro hc
  obtain ⟨g, hg⟩ := hc.exists_injective_nat
  obtain ⟨f, hf⟩ := exists_infinitely_often_ne (Function.invFun g)
  have hfe : Function.invFun g (g f) = f := Function.leftInverse_invFun hg f
  have := hf (g f)
  rw [hfe] at this
  simp at this
