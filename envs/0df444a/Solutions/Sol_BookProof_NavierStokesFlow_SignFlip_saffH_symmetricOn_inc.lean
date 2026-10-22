-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SignFlip.saffH_symmetricOn_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T08:19:48.279077+00:00
-- url     : https://prove2.me/submissions/8bc41ef6-712b-4907-8f26-bcc016aed7db

-- Generated from ChapterNavierStokesSignFlip.lean — solution of BookProof.NavierStokesFlow.SignFlip.saffH_symmetricOn_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Theorems.Thm_BookProof_NavierStokesFlow_ShiftHamiltonian_ShiftData_shiftH_symmetricOn
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber
open BookProof.NavierStokesFlow.AffineFiber.PairShift
open BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {κ : ℝ} (hκ : 0 ≤ κ) (c : ℝ) :
    SymmetricOn (maxDom (oscSymbol (affMu κ |c|))) (saffH hκ c) := by

  intro x y
  have h₁ := ShiftData.shiftH_symmetricOn (affData hκ (abs_nonneg c)).fst x y
  have h₂ := ShiftData.shiftH_symmetricOn (affData hκ (abs_nonneg c)).snd x y
  change (inner ℂ (saffH hκ c x : L2I ℕ) (y : L2I ℕ) : ℂ)
    = inner ℂ (x : L2I ℕ) (saffH hκ c y : L2I ℕ)
  change (inner ℂ ((affData hκ (abs_nonneg c)).fst.shiftH x
      + esgn c • (affData hκ (abs_nonneg c)).snd.shiftH x) (y : L2I ℕ) : ℂ)
    = inner ℂ (x : L2I ℕ) ((affData hκ (abs_nonneg c)).fst.shiftH y
      + esgn c • (affData hκ (abs_nonneg c)).snd.shiftH y)
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, conj_esgn]
  first | linear_combination h₁ + esgn c * h₂ | trace_state
