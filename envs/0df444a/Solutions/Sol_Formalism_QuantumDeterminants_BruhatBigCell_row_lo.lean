-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BruhatBigCell.row_lo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:12:32.862548+00:00
-- url     : https://prove2.me/submissions/b5974f88-2c1b-438c-aaf7-0a03a3ce2fd8

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_col_lo
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_col_hi
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_col_mid

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
theorem _root_.solution (p j : Fin (2 * r + k + 1)) (a : Fin r) (hp : p.val = a.val) :
    bigCell k r c μ p j = if j.val = 2 * r + k - a.val then (star (c a))⁻¹ else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  by_cases h1 : j.val < r
  · rw [col_lo c μ p j ⟨j.val, h1⟩ rfl, if_neg (by simp only; omega), if_neg (by omega)]
  · by_cases h2 : j.val ≤ r + k
    · rw [col_mid c μ p j (by omega) h2, dif_neg (by omega), if_neg (by omega)]
    · rw [col_hi c μ p j ⟨2 * r + k - j.val, by omega⟩ (by simp only; omega)]
      by_cases h3 : j.val = 2 * r + k - a.val
      · have e : (⟨2 * r + k - j.val, by omega⟩ : Fin r) = a := Fin.ext (by simp only; omega)
        rw [if_pos (by simp only; omega), if_pos h3, e]
      · rw [if_neg (by simp only; omega), if_neg h3]
end Formalism.QuantumDeterminants.BruhatBigCell
