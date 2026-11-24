-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.unimodUnramUnique_transv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:03.14015+00:00
-- url     : https://prove2.me/submissions/ea07e0bf-e5f3-4ee4-abff-a8030780f859

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementJac
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
open Polynomial IsLocalRing Matrix
variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R)
    (i j : ι) (c : R) :
    ((transvection j i c)ᴴ * A * transvection j i c) i i
      = A i i + (c * A i j + star c * A j i) + star c * c * A j j := by
  simp [transvection, Matrix.add_mul, Matrix.mul_add, conjTranspose_single,
    single_mul_apply_same, mul_single_apply_same, Matrix.mul_assoc]
  ring
end Formalism.HermitianLatticesTheory
