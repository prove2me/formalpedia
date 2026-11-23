-- Prove2me | solution 1 for Formalism.NG.gen_bigMat_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:58.439245+00:00
-- url     : https://prove2.me/submissions/b2d89ee3-8e3c-493a-8174-b2bc17641c8a

import Definitions.Def_Formalism_CharacterColumnKernels_StatementG
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenRelMapApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution {R O : Type*} [Ring R] [CommRing O] [Algebra O R] {m g d : Type*}
    [Fintype m] [Fintype d] [DecidableEq d] (ρ : R →ₐ[O] Matrix d d O) (C : Matrix g m R) (P : Matrix m g R) :
    bigMat (⇑ρ) (C * P) = bigRect (⇑ρ) C * bigRect (⇑ρ) P := by
  ext p q
  simp only [bigMat, bigRect, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply,
    Fintype.sum_prod_type]
end Formalism.NG
