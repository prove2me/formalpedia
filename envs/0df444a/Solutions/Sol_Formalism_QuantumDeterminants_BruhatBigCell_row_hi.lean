-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BruhatBigCell.row_hi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:02.341526+00:00
-- url     : https://prove2.me/submissions/19a7cb15-2575-44ec-87bc-9d117c3a34c0

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
theorem _root_.solution (p j : Fin (2 * r + k + 1)) (a : Fin r) (hp : p.val = 2 * r + k - a.val) :
    bigCell k r c μ p j = if j.val = a.val then c a else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  by_cases h1 : j.val < r
  · rw [col_lo c μ p j ⟨j.val, h1⟩ rfl]
    by_cases h3 : j.val = a.val
    · have e : (⟨j.val, h1⟩ : Fin r) = a := Fin.ext h3
      rw [if_pos (by simp only; omega), if_pos h3, e]
    · rw [if_neg (by simp only; omega), if_neg h3]
  · by_cases h2 : j.val ≤ r + k
    · rw [col_mid c μ p j (by omega) h2, dif_neg (by omega), if_neg (by omega)]
    · rw [col_hi c μ p j ⟨2 * r + k - j.val, by omega⟩ (by simp only; omega),
        if_neg (by simp only; omega), if_neg (by omega)]
end Formalism.QuantumDeterminants.BruhatBigCell
