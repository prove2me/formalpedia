-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BruhatBigCell.col_hi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:12.321155+00:00
-- url     : https://prove2.me/submissions/40271412-47d0-4bd0-8d27-b30e67368435

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell

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
theorem _root_.solution (i j : Fin (2 * r + k + 1)) (a : Fin r) (hj : j.val = 2 * r + k - a.val) :
    bigCell k r c μ i j = if i.val = a.val then (star (c a))⁻¹ else 0 := by
  have ha := a.isLt
  unfold bigCell
  rw [dif_neg (by omega), dif_neg (by omega)]
  have e : (⟨2 * r + k - j.val, by omega⟩ : Fin r) = a := Fin.ext (by simp only; omega)
  rw [e]
  have e2 : (i.val = 2 * r + k - j.val) ↔ i.val = a.val := by omega
  simp only [e2]
end Formalism.QuantumDeterminants.BruhatBigCell
