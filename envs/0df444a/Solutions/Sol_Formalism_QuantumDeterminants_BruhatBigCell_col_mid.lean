-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BruhatBigCell.col_mid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:22.611166+00:00
-- url     : https://prove2.me/submissions/c8d00bd8-a31e-4c95-9e24-0d2f08d4292a

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
theorem _root_.solution (i j : Fin (2 * r + k + 1)) (h1 : r ≤ j.val) (h2 : j.val ≤ r + k) :
    bigCell k r c μ i j = if hi : r ≤ i.val ∧ i.val ≤ r + k then
      μ ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ else 0 := by
  unfold bigCell
  rw [dif_neg (by omega), dif_pos h2]
end Formalism.QuantumDeterminants.BruhatBigCell
