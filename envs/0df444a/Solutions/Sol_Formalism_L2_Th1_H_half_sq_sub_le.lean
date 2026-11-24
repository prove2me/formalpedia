-- Prove2me | solution 1 for Formalism.L2.Th1.H.half_sq_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:27:23.497919+00:00
-- url     : https://prove2.me/submissions/148c3c9d-3e1b-4539-80af-e4e583b79a45

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaloisDescentSubspaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] (x z₀ : V) :
    ‖x‖ ^ 2 / 2 - ‖z₀‖ ^ 2 ≤ ‖x - z₀‖ ^ 2 := by
  have h : ‖x‖ ≤ ‖x - z₀‖ + ‖z₀‖ := by
    simpa using norm_add_le (x - z₀) z₀
  have h0 := norm_nonneg x
  have h1 := norm_nonneg (x - z₀)
  have h2 := norm_nonneg z₀
  have h3 : ‖x‖ ^ 2 ≤ (‖x - z₀‖ + ‖z₀‖) ^ 2 := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (‖x - z₀‖ - ‖z₀‖)]
end Formalism.L2.Th1.H
