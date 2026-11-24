-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.probability_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:55:48.639697+00:00
-- url     : https://prove2.me/submissions/a8174362-1826-40bd-a2a1-3b5818c2658c

import Definitions.Def_Formalism_FlagUnipotentLattices_CuspidalityThreshold
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_OperatorHilbertSchmidtNorm
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory NumberField
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : PZero := by
  intro N ep X h0 hX
  ext a b
  apply hX
  unfold q0 at h0
  rcases Nat.min_eq_zero_iff.mp h0 with h | h
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    have ha := h (Finset.mem_univ a)
    have hb := h (Finset.mem_univ b)
    simp at ha hb
    rw [ha, hb]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    have ha := h (Finset.mem_univ a)
    have hb := h (Finset.mem_univ b)
    simp at ha hb
    rw [ha, hb]
end Formalism.HermitianLatticeCounting.P
