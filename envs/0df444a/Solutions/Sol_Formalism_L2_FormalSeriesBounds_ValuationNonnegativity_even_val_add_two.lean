-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.even_val_add_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:25:43.439863+00:00
-- url     : https://prove2.me/submissions/2e6355a1-ba43-411a-8479-d15d3a7e2e83

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
variable {C : Type} [Field C] {V : VF C}
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
namespace Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
theorem _root_.solution {d : ℕ} [NeZero d] (hd : Even d) (a : ZMod d) :
    Even (a + 2).val ↔ Even a.val := by
  have h2d : 2 ∣ d := even_iff_two_dvd.mp hd
  rw [ZMod.val_add, Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ h2d]
  have h2 : (2 : ZMod d).val % 2 = 0 := by
    rw [show (2 : ZMod d) = ((2 : ℕ) : ZMod d) by norm_num, ZMod.val_natCast, Nat.mod_mod_of_dvd _ h2d]
  omega
end Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
