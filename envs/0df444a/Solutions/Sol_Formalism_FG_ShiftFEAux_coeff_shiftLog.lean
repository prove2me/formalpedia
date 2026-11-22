-- Prove2me | solution 1 for Formalism.FG.ShiftFEAux.coeff_shiftLog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:22.2388+00:00
-- url     : https://prove2.me/submissions/a4cb26f6-9d0e-4d7a-9745-16b8f80f771d

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.FG
open Formalism.FG.ShiftFEAux
open MvPowerSeries
variable {K : Type*} [Field K] {l m : ℕ}
namespace Formalism.FG.ShiftFEAux
theorem _root_.solution (j : ZMod m) (n : ZMod m →₀ ℕ) :
    coeff n (shiftLog K l m j) = ∑ e ∈ Finset.range (n.degree + 1),
      if n = Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0 := by
  rw [coeff_apply]; rfl
end Formalism.FG.ShiftFEAux
