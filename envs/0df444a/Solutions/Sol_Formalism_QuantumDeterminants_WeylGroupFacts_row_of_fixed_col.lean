-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.row_of_fixed_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:53.197353+00:00
-- url     : https://prove2.me/submissions/ea9c72d5-43cc-4aad-b701-e74a908cebc1

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_row
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_sgn_mul_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.WeylGroupFacts
theorem _root_.solution {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : h ∈ UH (Hpk k r)) (c : Fin (2 * r + k + 1))
    (hc : ∀ p, h p c = if p = c then 1 else 0) (j : Fin (2 * r + k + 1)) :
    h (tau k r c) j = if tau k r c = j then 1 else 0 := by
  have h1 : hᴴ * Hpk k r * h = Hpk k r := hU
  have h2 := congrFun (congrFun h1 c) j
  have h3 : ∀ q, (hᴴ * Hpk k r) c q = Hpk k r c q := by
    intro q
    rw [Matrix.mul_apply, Fintype.sum_eq_single c]
    · rw [Matrix.conjTranspose_apply, hc c, if_pos rfl, star_one, one_mul]
    · intro p hp
      rw [Matrix.conjTranspose_apply, hc p, if_neg hp, star_zero, zero_mul]
  rw [Matrix.mul_apply] at h2
  simp only [h3] at h2
  rw [Fintype.sum_eq_single (tau k r c)] at h2
  · rw [hpk_row, if_pos rfl, hpk_row] at h2
    have hs : sgn k r c * sgn k r c = 1 := sgn_mul_self c
    calc h (tau k r c) j = (sgn k r c * sgn k r c) * h (tau k r c) j := by rw [hs, one_mul]
      _ = sgn k r c * (sgn k r c * h (tau k r c) j) := by ring
      _ = sgn k r c * (if j = tau k r c then sgn k r c else 0) := by rw [h2]
      _ = if tau k r c = j then 1 else 0 := by
          by_cases hj : j = tau k r c
          · rw [if_pos hj, if_pos hj.symm, hs]
          · rw [if_neg hj, if_neg (Ne.symm hj), mul_zero]
  · intro q hq
    rw [hpk_row, if_neg hq, zero_mul]
end Formalism.QuantumDeterminants.WeylGroupFacts
