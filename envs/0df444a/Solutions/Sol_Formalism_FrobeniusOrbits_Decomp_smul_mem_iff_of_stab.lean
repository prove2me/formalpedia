-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Decomp.smul_mem_iff_of_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:14:08.377437+00:00
-- url     : https://prove2.me/submissions/a5c26c47-94ad-4780-8e1f-0df03e7856a4

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
theorem _root_.solution {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S]
    (g : G) (I : Ideal S) (hg : g ∈ MulAction.stabilizer G I) (z : S) : g • z ∈ I ↔ z ∈ I := by
  rw [MulAction.mem_stabilizer_iff] at hg
  conv_lhs => rw [← hg]
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
end Formalism.FrobeniusOrbits.Decomp
