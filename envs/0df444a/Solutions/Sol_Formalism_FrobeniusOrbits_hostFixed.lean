-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostFixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:03:17.244069+00:00
-- url     : https://prove2.me/submissions/76a316c0-b722-4b08-92e2-a9d54074b320

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galMap_zeta_inversion
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galMap_eq_neg_one_one_one_iff_eq_zeta_inversion
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_hostE_eq_adjoin
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_mem_hostE_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Galois
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostFixed := by
  unfold HostFixed
  intro e q d hqd L _ _ ζ a b h
  refine ⟨hostE_eq_adjoin ζ a b, fun x => ?_⟩
  rw [mem_hostE_iff hqd h]
  constructor
  · intro hx τ hτ
    rw [(galMap_eq_neg_one_one_one_iff_eq_zeta_inversion hqd h τ).1 hτ]
    exact hx
  · intro H
    exact H _ (galMap_zeta_inversion hqd h)
end Formalism.FrobeniusOrbits
