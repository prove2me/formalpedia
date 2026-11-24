-- Prove2me | solution 1 for Formalism.LIFT.prod_X_sub_C_dvd_of_injOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:31:59.23983+00:00
-- url     : https://prove2.me/submissions/89fb8ff0-7187-4515-94b9-ffba1b7b90c9

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_LagrangeIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
open Polynomial
namespace Formalism.LIFT
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {ι : Type}
    (S : Finset ι) (c : ι → R) (hc : Set.InjOn c S) (G : R[X])
    (hG : ∀ a ∈ S, G.eval (c a) = 0) : (∏ a ∈ S, (X - C (c a))) ∣ G := by
  classical
  by_cases hG0 : G = 0
  · rw [hG0]
    exact dvd_zero _
  have hle : S.val.map c ≤ G.roots := by
    rw [Multiset.le_iff_subset (Multiset.Nodup.map_on (fun a ha b hb hab => hc ha hb hab) S.nodup)]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
    exact (Polynomial.mem_roots hG0).mpr (hG a ha)
  calc (∏ a ∈ S, (X - C (c a))) = ((S.val.map c).map fun x => X - C x).prod := by
        rw [Multiset.map_map]
        rfl
    _ ∣ (G.roots.map fun x => X - C x).prod :=
        Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)
    _ ∣ G := Polynomial.prod_multiset_X_sub_C_dvd G
end Formalism.LIFT
