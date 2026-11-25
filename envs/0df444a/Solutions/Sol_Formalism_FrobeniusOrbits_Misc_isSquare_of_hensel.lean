-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Misc.isSquare_of_hensel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:52:05.094966+00:00
-- url     : https://prove2.me/submissions/634367c4-1efc-48a9-8a3f-17e56d07f649

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Misc
namespace Formalism.FrobeniusOrbits.Misc
theorem _root_.solution (p : ℕ) [Fact p.Prime] (c a : ℤ)
    (h : ‖((a ^ 2 + c : ℤ) : ℤ_[p])‖ < ‖((2 * a : ℤ) : ℤ_[p])‖ ^ 2) :
    IsSquare (-(c : ℤ_[p])) := by
  have h' : ‖Polynomial.aeval (a : ℤ_[p]) (Polynomial.X ^ 2 + Polynomial.C (c : ℤ_[p]))‖ <
      ‖Polynomial.aeval (a : ℤ_[p])
        (Polynomial.derivative (Polynomial.X ^ 2 + Polynomial.C (c : ℤ_[p])))‖ ^ 2 := by
    push_cast at h
    simp [Polynomial.derivative_X_pow, mul_comm] at h ⊢
    convert h using 4
    norm_num
  obtain ⟨z, hz, -⟩ := hensels_lemma h'
  refine ⟨z, ?_⟩
  simp at hz
  linear_combination -hz
end Formalism.FrobeniusOrbits.Misc
