-- Prove2me | solution 1 for Formalism.HC.Der.hostCore
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:04:19.18664+00:00
-- url     : https://prove2.me/submissions/bf8c0907-1029-453f-bc51-ad9b56398243

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycAll
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_frob
import Theorems.Thm_Formalism_HC_D7_inertia_d
import Theorems.Thm_Formalism_HC_Der_art_ch
import Theorems.Thm_Formalism_HC_Der_art_surj
import Theorems.Thm_Formalism_HC_Der_cm
import Theorems.Thm_Formalism_HC_Der_conj_iff
import Theorems.Thm_Formalism_HC_Der_decomp
import Theorems.Thm_Formalism_HC_Der_decompConj
import Theorems.Thm_Formalism_HC_Der_decomp_typeI
import Theorems.Thm_Formalism_HC_Der_finrank_E
import Theorems.Thm_Formalism_HC_Der_finrank_F
import Theorems.Thm_Formalism_HC_Der_frob
import Theorems.Thm_Formalism_HC_Der_frob_any
import Theorems.Thm_Formalism_HC_Der_inertia
import Theorems.Thm_Formalism_HC_Der_inertia_d
import Theorems.Thm_Formalism_HC_Der_mem_F
import Theorems.Thm_Formalism_HC_Der_ps_d
import Theorems.Thm_Formalism_HC_Der_unramEF
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_conj_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : HostCore H where
  art_surj := art_surj H
  cm := cm H
  conj_iff := conj_iff H
  finrank_E := finrank_E H
  finrank_F := finrank_F H
  mem_F := mem_F H
  art_ch := art_ch H
  ps_d := ps_d H
  frob := frob H
  frob_any := frob_any H
  inertia := inertia H
  decomp := decomp H
  inertia_d := inertia_d H
  decomp_typeI := decomp_typeI H
  decompConj := decompConj H
  unramEF := unramEF H
end Formalism.HC.Der
