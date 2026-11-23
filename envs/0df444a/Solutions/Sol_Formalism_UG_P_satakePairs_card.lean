-- Prove2me | solution 1 for Formalism.UG.P.satakePairs_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:07.760429+00:00
-- url     : https://prove2.me/submissions/6d4123ee-8dfb-432b-9570-d68a08a1ae44

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L] (O : Subring L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (S : Finset (Fin n)) :
    Fintype.card (satakePairs S) = satakeInv Finset.univ S := by
  unfold satakeInv
  rw [Fintype.card_subtype, Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := S) ?_]
  · refine Finset.sum_congr rfl fun a ha => ?_
    refine Eq.trans ?_ (Finset.card_image_of_injective (f := Prod.mk a) _ (fun x y h => congrArg Prod.snd h))
    congr 1
    ext ⟨b, l⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_sdiff,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hb, hl, hbl⟩, rfl⟩
      exact ⟨l, ⟨hl, hbl⟩, rfl, rfl⟩
    · rintro ⟨l', ⟨hl', hal'⟩, rfl, rfl⟩
      exact ⟨⟨ha, hl', hal'⟩, rfl⟩
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    exact Finset.mem_coe.2 hp.2.1
end Formalism.UG.P
