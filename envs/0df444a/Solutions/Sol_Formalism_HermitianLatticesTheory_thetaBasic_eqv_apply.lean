-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.thetaBasic_eqv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:01.650025+00:00
-- url     : https://prove2.me/submissions/15e97789-e868-469d-870c-a87ae4c8afc5

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.K
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (g : V ≃ₗ[K] V)
    (L : Submodule (NumberField.RingOfIntegers K) V) (x : L) :
    ((thetaBasic_eqv g L x : gmap g L) : V) = g x := rfl
end Formalism.HermitianLatticesTheory
