-- Prove2me | solution 1 for BookProof.FockWeightedSchur.sum_pair_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T10:00:39.346953+00:00
-- url     : https://prove2.me/submissions/39f64c30-d345-4c57-9d8c-0985cf0c811c

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.sum_pair_le
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.FockWeightedSchur




open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {w : ℕ → ℝ}
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

set_option maxHeartbeats 1000000 in

theorem solution {f : ℕ → ℝ} {S : Finset ℕ} {a b : ℕ} {C : ℝ} (hS : S ⊆ {a, b})
    (hf : ∀ j, 0 ≤ f j) (hC : ∀ j, f j ≤ C) (hC0 : 0 ≤ C) : ∑ j ∈ S, f j ≤ 2 * C := by
  classical
  have hcard : ((({a, b} : Finset ℕ)).card : ℝ) ≤ 2 := by
    have : (({a, b} : Finset ℕ)).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    exact_mod_cast this
  calc ∑ j ∈ S, f j ≤ ∑ j ∈ ({a, b} : Finset ℕ), f j :=
        Finset.sum_le_sum_of_subset_of_nonneg hS fun j _ _ => hf j
    _ ≤ ∑ _j ∈ ({a, b} : Finset ℕ), C := Finset.sum_le_sum fun j _ => hC j
    _ ≤ 2 * C := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        nlinarith [hC0, hcard]
