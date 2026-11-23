-- Prove2me | solution 1 for Formalism.UG.P.fSatake_cTJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:28.257218+00:00
-- url     : https://prove2.me/submissions/8d991c2c-802d-4c8d-b186-dfe17e3d115c

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Theorems.Thm_Formalism_UG_P_fSatake_rev_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (M : Matrix (Fin n) (Fin n) L) (i l : Fin n) :
    (cT σ M * antiJ L n) i l = σ (M l.rev i) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single l.rev]
  · rw [show antiJ L n l.rev l = 1 from if_pos ((fSatake_rev_iff l.rev l).2 rfl), mul_one]
    rfl
  · intro j _ hj
    rw [show antiJ L n j l = 0 from if_neg (fun h => hj ((fSatake_rev_iff j l).1 h)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.UG.P
