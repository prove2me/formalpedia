-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.weyl_ci
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:39.271845+00:00
-- url     : https://prove2.me/submissions/5713fec0-38dd-459d-96e8-52f2d8458b83

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution {p c ci : A} (h : WeylRel p c ci) : p * ci = ci * p - ci := by
  obtain ⟨h1, h2, h3⟩ := h
  have : ci * (p * c) * ci = ci * (c * p + c) * ci := by rw [h3]
  have e1 : ci * (p * c) * ci = ci * p := by rw [mul_assoc, mul_assoc, h1, mul_one]
  have e2 : ci * (c * p + c) * ci = p * ci + ci := by
    rw [mul_add, ← mul_assoc, h2, one_mul, add_mul, one_mul]
  rw [e1, e2] at this
  rw [this]; abel
end Formalism.FourierDecayAlt.P.Wd6
