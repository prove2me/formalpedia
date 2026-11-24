-- Prove2me | solution 1 for Formalism.GM.TM.filL_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:16.24374+00:00
-- url     : https://prove2.me/submissions/6e3959bd-d610-4341-b819-6f281abf43a5

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.GM.TM
theorem _root_.solution (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) : filL L v 0 = L := by
  apply le_antisymm inf_le_left
  intro x hx
  refine Submodule.mem_inf.mpr ⟨hx, ?_⟩
  change x ∈ MvPolynomial.restrictSupport ℚ_[p] _
  rw [mem_restrictSupport_iff]
  intro m _
  exact Nat.zero_le _
end Formalism.GM.TM
