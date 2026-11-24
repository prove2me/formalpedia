-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.galMap_eq_neg_one_one_one_iff_eq_zeta_inversion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:22:13.069138+00:00
-- url     : https://prove2.me/submissions/eba2300a-93d6-431a-90cb-120a5de2c3a1

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galMap_zeta_inversion

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
open Formalism.FrobeniusOrbits.Galois
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Galois
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (τ : Gal(L/ℚ)) :
    galMap h.1 a b τ = ((-1, 1, 1) : GalL (e + 2)) ↔ τ = tau0 hqd h := by
  constructor
  · intro hτ
    exact (layer_galois hqd h).2.2.2.1 (hτ.trans (galMap_zeta_inversion hqd h).symm)
  · rintro rfl
    exact galMap_zeta_inversion hqd h
end Formalism.FrobeniusOrbits.Galois
