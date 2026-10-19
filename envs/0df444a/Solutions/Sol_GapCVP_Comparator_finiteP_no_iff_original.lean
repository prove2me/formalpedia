-- Prove2me | solution 1 for GapCVP.Comparator.finiteP_no_iff_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/feef86b2-070b-4682-ae51-eb9e960adb01

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_Comparator_toOriginal_ofOriginal
import Theorems.Thm_GapCVP_Comparator_toOriginalNearest_ofOriginalNearest
import Theorems.Thm_GapCVP_Comparator_toOriginalSyndrome_ofOriginalSyndrome
import Theorems.Thm_GapCVP_Comparator_encodeInstance_eq_original
attribute [local simp] GapCVP.Comparator.toOriginal_ofOriginal
attribute [local simp] GapCVP.Comparator.toOriginalNearest_ofOriginalNearest
attribute [local simp] GapCVP.Comparator.toOriginalSyndrome_ofOriginalSyndrome

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
noncomputable section
open scoped BigOperators
open GapCVP.Comparator
namespace GapCVP.Comparator
theorem _root_.solution (p : ℚ) (hp : 1 ≤ p)
    (bits : List Bool) :
    (finitePGapCVPPromise p hp).no bits ↔
      (GapCVP.Factor400FinitePNormCorollary.finitePGapCVPPromise p hp).no bits := by
  simp only [finitePGapCVPPromise, wellFormed,
    GapCVP.Factor400FinitePNormCorollary.finitePGapCVPPromise,
    GapCVP.gapCVPWellFormed, decide_eq_true_eq]
  change (∃ _, _) ↔ ∃ _, _
  rw [(Function.RightInverse.surjective toOriginal_ofOriginal).exists]
  exact exists_congr fun _ => by
    simp only [GapCVP.binaryFinEncoding_gapCVPInstance_encode,
      encodeInstance_eq_original]
    rfl
end GapCVP.Comparator
