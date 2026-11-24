-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.layerGalois
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:19:36.740794+00:00
-- url     : https://prove2.me/submissions/784509c9-7dc0-4b7f-85f0-6410e12ef67d

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layer_isGalois
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_galMap_injective
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_galMap_mul
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_card_galL
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layer_finrank_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Polynomial
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : LayerGalois := by
  intro n q d hn hqd L _ _ ζ a b h
  have hG := layer_isGalois h
  have hq0 : q ≠ 0 := hqd.1.ne_zero
  have hd0 : d ≠ 0 := hqd.2.1.ne_zero
  have hinj := galMap_injective h hq0 hd0
  have hcard1 : Nat.card Gal(L/ℚ) = Module.finrank ℚ L := IsGalois.card_aut_eq_finrank ℚ L
  have hle : Nat.card Gal(L/ℚ) ≤ Nat.card (GalL n) := Nat.card_le_card_of_injective _ hinj
  have hge := layer_finrank_ge h hn hqd
  rw [card_galL hn] at hle
  refine ⟨hG, by omega, galMap_mul h hq0 hd0, hinj.bijective_of_nat_card_le ?_⟩
  rw [card_galL hn]
  omega
end Formalism.TwoAdicCyclotomicDecomposition
