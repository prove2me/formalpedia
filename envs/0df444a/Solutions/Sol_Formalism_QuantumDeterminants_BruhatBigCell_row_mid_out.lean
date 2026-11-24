-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BruhatBigCell.row_mid_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:12:33.895143+00:00
-- url     : https://prove2.me/submissions/41a8a383-6e76-42f8-a370-4be0316a7840

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_col_lo
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_col_hi

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
open Formalism.QuantumDeterminants.BruhatBigCell
open GBasic
variable {k r : ℕ}
variable (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
namespace Formalism.QuantumDeterminants.BruhatBigCell
theorem _root_.solution (p j : Fin (2 * r + k + 1)) (h1 : r ≤ p.val) (h2 : p.val ≤ r + k)
    (hj : j.val < r ∨ r + k < j.val) : bigCell k r c μ p j = 0 := by
  have hj' := j.isLt
  rcases hj with hj | hj
  · rw [col_lo c μ p j ⟨j.val, hj⟩ rfl, if_neg (by simp only; omega)]
  · rw [col_hi c μ p j ⟨2 * r + k - j.val, by omega⟩ (by simp only; omega),
      if_neg (by simp only; omega)]
end Formalism.QuantumDeterminants.BruhatBigCell
