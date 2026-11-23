-- Prove2me | solution 1 for Formalism.UG.P.glint_princ_relIndex_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:29.278484+00:00
-- url     : https://prove2.me/submissions/d1b0a7ba-22de-4b94-b7ee-bbd0e9c18dd7

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Lemmata_NearbyExistence_ExistsNear
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (O : Subring L) (I : Ideal O) [Finite (O ⧸ I)] :
    (princ (n := n) O.subtype I).relIndex (bc (n := n) O.subtype).range ≠ 0 := by
  classical
  have : Finite (Matrix n n (O ⧸ I)) := inferInstanceAs (Finite (n → n → O ⧸ I))
  have hN : (redGL (n := n) I).ker.index ≠ 0 := by
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  have hsup : ((redGL (n := n) I).ker ⊔ (bc (n := n) O.subtype).ker).index ≠ 0 := by
    intro h
    apply hN
    have hd := Subgroup.index_dvd_of_le
      (le_sup_left : (redGL (n := n) I).ker ≤ (redGL (n := n) I).ker ⊔ (bc (n := n) O.subtype).ker)
    rw [h] at hd
    exact Nat.eq_zero_of_zero_dvd hd
  have hprinc : princ (n := n) O.subtype I = ((redGL (n := n) I).ker).map (bc (n := n) O.subtype) := by
    unfold princ congPre
    rw [MonoidHom.comap_bot]
  rw [hprinc, MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
    Subgroup.relIndex_top_right]
  exact hsup
end Formalism.UG.P
