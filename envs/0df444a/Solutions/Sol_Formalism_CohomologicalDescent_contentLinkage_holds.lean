-- Prove2me | solution 1 for Formalism.CohomologicalDescent.contentLinkage_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:41:32.341803+00:00
-- url     : https://prove2.me/submissions/760138a8-4ec5-4aa6-8753-2c92dfc8d619

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ContentLinkageHolds
import Theorems.Thm_Formalism_CohomologicalDescent_comb_roots_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.CohomologicalDescent
open Classical
namespace Formalism.CohomologicalDescent
theorem _root_.solution : Linkage := by
  intro l K _ _ N U U' c hl hprod
  haveI : Fact l.Prime := ⟨hl⟩
  have hr := congrArg Polynomial.roots hprod
  have hU := comb_roots_prod (fun a => (((U a + c : ℤ)) : K))
  have hU' := comb_roots_prod (fun a => (((U' a + c : ℤ)) : K))
  rw [hU, hU'] at hr
  let ψ : ZMod l →+* K := ZMod.castHom (dvd_refl l) K
  have hψ : Function.Injective ψ := ψ.injective
  have key : ∀ V : Fin N → ℤ, Multiset.map (fun a => -(((V a + c : ℤ)) : K)) Finset.univ.val =
      Multiset.map ψ (Multiset.map (fun a => -(((V a + c : ℤ)) : ZMod l)) Finset.univ.val) := by
    intro V
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro a _
    simp [ψ, map_intCast]
  rw [key U, key U'] at hr
  have h2 := Multiset.map_injective hψ hr
  have h3 := congrArg (Multiset.map fun z : ZMod l => -z - (c : ZMod l)) h2
  simp only [Multiset.map_map] at h3
  convert h3 using 2 <;> (try simp only [Function.comp_apply]; push_cast; ring)
end Formalism.CohomologicalDescent
