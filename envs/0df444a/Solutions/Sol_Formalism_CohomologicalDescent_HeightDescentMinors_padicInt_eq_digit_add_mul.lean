-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.padicInt_eq_digit_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:01.955894+00:00
-- url     : https://prove2.me/submissions/b05f6911-32aa-47d7-9f44-b83eeac3f133

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable (l : ℕ) [Fact l.Prime]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (d : ℤ_[l]) :
    ∃ e : ℤ_[l], d = (((PadicInt.toZMod d).val : ℕ) : ℤ_[l]) + (l : ℤ_[l]) * e := by
  have h0 : PadicInt.toZMod (d - (((PadicInt.toZMod d).val : ℕ) : ℤ_[l])) = 0 := by
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  have hmem : d - (((PadicInt.toZMod d).val : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZMod (p := l)) := h0
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hmem
  obtain ⟨e, he⟩ := hmem
  exact ⟨e, by linear_combination -he⟩
end Formalism.CohomologicalDescent.HeightDescentMinors
