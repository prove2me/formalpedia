-- Prove2me | solution 1 for Formalism.L2.G.Triv.bc_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:01:33.049458+00:00
-- url     : https://prove2.me/submissions/ba5839e4-1ed8-4b03-9c7e-118c06b5ceca

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ClosureUpperUni
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddPowOfMulSelfEqZero
import Definitions.Def_Lemmata_GeneralBFactLeftTail_Imports
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_OneAddPowOfSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
namespace Formalism.L2.G.Triv
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (φ : A →+* B)
    (hφ : Function.Injective φ) : Function.Injective (bc (n := n) φ) := by
  intro x y hxy
  apply Units.ext
  have h := congrArg (fun z : GL n B => (z : Matrix n n B)) hxy
  exact Matrix.map_injective hφ h
end Formalism.L2.G.Triv
