-- Prove2me | solution 1 for Formalism.FG.PadicFrobeniusSquare.padicInt_norm_le_p
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:12.244021+00:00
-- url     : https://prove2.me/submissions/a2e9564f-28c6-48f7-9790-a770e78ecbee

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG
open Formalism.G
open Formalism.FG.PadicFrobeniusSquare
namespace Formalism.FG.PadicFrobeniusSquare
theorem _root_.solution {p : ℕ} [Fact p.Prime] (y : ℤ_[p]) (hy : PadicInt.toZMod y = 0) :
    ‖y‖ ≤ ‖(p : ℤ_[p])‖ := by
  have h1 : y ∈ RingHom.ker (PadicInt.toZMod (p := p)) := hy
  rw [PadicInt.ker_toZMod] at h1
  have h2 : ‖y‖ < 1 := PadicInt.mem_nonunits.1 ((IsLocalRing.mem_maximalIdeal _).1 h1)
  obtain ⟨z, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 h2
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one z)
end Formalism.FG.PadicFrobeniusSquare
