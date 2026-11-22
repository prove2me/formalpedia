-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BruhatBigCell.col_lo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:28:54.288524+00:00
-- url     : https://prove2.me/submissions/401b7060-a18e-4539-a871-4f7543f55f2f

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
theorem _root_.solution (i j : Fin (2 * r + k + 1)) (a : Fin r) (hj : j.val = a.val) :
    bigCell k r c μ i j = if i.val = 2 * r + k - a.val then c a else 0 := by
  have hj' : j.val < r := by omega
  have ha : (⟨j.val, hj'⟩ : Fin r) = a := Fin.ext hj
  unfold bigCell
  rw [dif_pos hj', ha]
  simp only [esI, Fin.ext_iff]
end Formalism.QuantumDeterminants.BruhatBigCell
