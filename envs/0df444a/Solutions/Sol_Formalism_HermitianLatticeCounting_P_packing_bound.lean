-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.packing_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:13.397612+00:00
-- url     : https://prove2.me/submissions/f9280352-32e9-4379-bb5f-41dc3a813cca

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_card_separated_set_le_prod
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_finite_of_finset_card_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Packing := by
  intro E _ _ _ Λ l₀ R hl hR hΛ
  apply finite_of_finset_card_bound
  intro S hS
  classical
  let emb : E ↪ (Unit → E) := ⟨fun x _ => x, fun x y h => congrFun h ()⟩
  have := card_separated_set_le_prod (S.map emb) (fun _ => l₀ / 2) (fun _ => R) (fun _ => by positivity)
    (fun _ => hR) (by
      intro c hc v
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hc
      exact (hS hx).2) (by
      intro c hc d hd hcd
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hc
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hd
      refine ⟨(), ?_⟩
      have hxy : x - y ≠ 0 := fun h => hcd (by rw [sub_eq_zero.mp h])
      have := hΛ (x - y) (Λ.sub_mem (hS hx).1 (hS hy).1) hxy
      show 2 * (l₀ / 2) ≤ ‖x - y‖
      linarith)
  rw [Finset.card_map] at this
  refine this.trans (le_of_eq ?_)
  simp only [Finset.univ_unique, Finset.prod_singleton]
  congr 1; field_simp; ring
end Formalism.HermitianLatticeCounting.P
