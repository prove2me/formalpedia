-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_shift_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:49.254875+00:00
-- url     : https://prove2.me/submissions/4b3ccc0c-b6e3-4be8-ab41-dc8b7fb5fa42

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — solution of BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_shift_le
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

set_option maxHeartbeats 1000000 in
theorem solution {f : ℕ → ℝ} (hf : Summable f) (hnn : ∀ n, 0 ≤ f n) :
    (∑' n, f (n + 2)) ≤ ∑' n, f n := by

  have h := hf.sum_add_tsum_nat_add 2
  have h0 : 0 ≤ ∑ i ∈ Finset.range 2, f i := Finset.sum_nonneg fun i _ => hnn i
  linarith [h]
