-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.prod_mu_toZMod_val_eq_prod_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:33.891241+00:00
-- url     : https://prove2.me/submissions/19b47d36-0066-4eee-a7ae-d87fa3afcbff

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_toZMod_ne_zero_of_mem_mu_alt

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
theorem _root_.solution (hm : MuFacts) {M : Type} [CommMonoid M] (G : ℕ → M) :
    ∏ d ∈ mu l, G (PadicInt.toZMod d).val = ∏ c ∈ Finset.Ioo 0 l, G c := by
  refine Finset.prod_nbij (fun d => (PadicInt.toZMod d).val) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro d hd
    rw [Finset.mem_Ioo]
    refine ⟨Nat.pos_of_ne_zero ?_, ZMod.val_lt _⟩
    intro h0
    exact toZMod_ne_zero_of_mem_mu_alt l hd ((ZMod.val_eq_zero _).mp h0)
  · intro x hx y hy hxy
    have h' : PadicInt.toZMod x = PadicInt.toZMod y := ZMod.val_injective _ hxy
    exact ((hm l).2.1 _ (toZMod_ne_zero_of_mem_mu_alt l hx)).unique ⟨hx, rfl⟩ ⟨hy, h'.symm⟩
  · intro c hc
    rw [Finset.coe_Ioo, Set.mem_Ioo] at hc
    have hc0 : (c : ZMod l) ≠ 0 := by
      intro h
      have := congrArg ZMod.val h
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hc.2, ZMod.val_zero] at this
      omega
    obtain ⟨d, ⟨hd, hdc⟩, _⟩ := (hm l).2.1 _ hc0
    refine ⟨d, hd, ?_⟩
    show (PadicInt.toZMod d).val = c
    rw [hdc, ZMod.val_natCast, Nat.mod_eq_of_lt hc.2]
end Formalism.CohomologicalDescent.HeightDescentMinors
