-- Prove2me | solution 1 for BookProof.FockQuadratic.pairOp_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:45:13.285801+00:00
-- url     : https://prove2.me/submissions/af623242-0dd1-47b2-8662-a93f50bdce16

-- Generated from ChapterFockQuadraticEsa.lean — solution of BookProof.FockQuadratic.pairOp_symmetricOn
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Theorems.Thm_BookProof_FockQuadratic_hopOp_pairing
open BookProof.FockQuadratic



open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

variable {ι : Type*}

variable {ι : Type*}
variable {ω : ι → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hω : ∀ i, 0 ≤ ω i) (g : ℂ) (P Q : Idx ι)
    (hPQ : deg P + deg Q ≤ 2) : SymmetricOn (maxDom (sig ω)) (pairOp hω g P Q hPQ) := by

  intro x y
  simp only [pairOp, LinearMap.add_apply, LinearMap.smul_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  rw [hopOp_pairing hω hPQ (by omega) x y, hopOp_pairing hω (by omega : deg Q + deg P ≤ 2) hPQ x y]
  simp [RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring
