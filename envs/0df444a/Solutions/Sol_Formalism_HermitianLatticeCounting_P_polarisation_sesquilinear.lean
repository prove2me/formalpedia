-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.polarisation_sesquilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:59:09.417497+00:00
-- url     : https://prove2.me/submissions/84a97176-0dba-402e-a708-e7c407cb037a

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : PolariseSesq := by
  intro K V _ _ _ σ h y₁ y₂ A₁ A₂ y₁' y₂' A₁' A₂' e1 e2 h1 h2 h3 h4
  have l : h (y₁ - A₁) (y₂ - A₂) = h y₁ y₂ + h A₁ A₂ := by
    simp only [map_sub, LinearMap.sub_apply, h1, h2]; ring
  have r : h (y₁' + A₁') (y₂' + A₂') = h y₁' y₂' + h A₁' A₂' := by
    simp only [map_add, LinearMap.add_apply, h3, h4]; ring
  rw [← l, ← r, e1, e2]
end Formalism.HermitianLatticeCounting.P
