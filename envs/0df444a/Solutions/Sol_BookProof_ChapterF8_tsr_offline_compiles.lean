-- Prove2me | solution 1 for BookProof.ChapterF8.tsr_offline_compiles
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:11:23.722674+00:00
-- url     : https://prove2.me/submissions/911e7764-c2c6-43ee-af51-ebfe2cb8eb0e

-- Generated from ChapterF8.lean — solution of BookProof.ChapterF8.tsr_offline_compiles
import Mathlib
import Definitions.Def_ChapterF8
import Theorems.Thm_BookProof_ChapterF8_twoLevelHash_total
import Theorems.Thm_BookProof_ChapterF8_twoLevelHash_decodes
import Theorems.Thm_BookProof_ChapterF8_offline_operatorBasis
import Theorems.Thm_BookProof_ChapterF8_online_cost_independent_of_M
open BookProof.ChapterF8



noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution {d k K₂ m : ℕ} (h : Fin d → Fin k) (g : Fin k → Fin K₂)
    (hg : Function.Injective g) :
    (∀ x : Fin d → ℝ, twoLevelHash h g x ∈ singleExcitation K₂) ∧
    (∀ (x : Fin d → ℝ) (j : Fin k),
      twoLevelHash h g x (Finsupp.single (g j) 1) = ((featureHash h x j : ℝ) : ℂ)) ∧
    Submodule.span ℂ (operatorBasis m) = ⊤ ∧
    (∀ M M' : ℕ, totalCost M d m K₂ k + offlineCost M' d k
      = totalCost M' d m K₂ k + offlineCost M d k) :=
  ⟨fun x => twoLevelHash_total h g x,
     fun x j => twoLevelHash_decodes h g hg x j,
     offline_operatorBasis m,
     fun M M' => online_cost_independent_of_M M M' d m K₂ k⟩
