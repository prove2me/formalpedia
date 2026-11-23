-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.wilson_zmod_prod_units
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:12.125652+00:00
-- url     : https://prove2.me/submissions/2df3c436-24e0-43e1-9191-00f6028ecafe

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
theorem _root_.solution : ∏ x ∈ (univ.erase (0 : ZMod l)), x = -1 := by
  rw [← ZMod.prod_Ico_one_prime l]
  symm
  refine Finset.prod_nbij (fun n : ℕ => (n : ZMod l)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro n hn
    rw [Finset.mem_Ico] at hn
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn.2, ZMod.val_zero] at this
    omega
  · intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    have := congrArg ZMod.val hab
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha.2, Nat.mod_eq_of_lt hb.2] at this
    exact this
  · intro x hx
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    simp only [Finset.coe_Ico, Set.mem_Ico]
    refine ⟨?_, ZMod.val_lt x⟩
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    exact hx0 ((ZMod.val_eq_zero x).mp h0)
end Formalism.CohomologicalDescent.HeightDescentMinors
