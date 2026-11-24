-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Decomp.mem_stab_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:17:03.301771+00:00
-- url     : https://prove2.me/submissions/37ac6cb7-a176-4ef2-9556-080f71d41a12

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp

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
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Decomp
namespace Formalism.FrobeniusOrbits.Decomp
theorem _root_.solution {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S] (g : G)
    (I : Ideal S) (h : ∀ z : S, g • z ∈ I ↔ z ∈ I) : g ∈ MulAction.stabilizer G I := by
  rw [MulAction.mem_stabilizer_iff]
  ext z
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← h (g⁻¹ • z), smul_inv_smul]
end Formalism.FrobeniusOrbits.Decomp
