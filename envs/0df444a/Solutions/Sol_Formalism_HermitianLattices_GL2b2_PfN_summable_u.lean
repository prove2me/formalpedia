-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2b2.PfN.summable_u
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:52:04.433402+00:00
-- url     : https://prove2.me/submissions/66083c1d-096f-4a6e-b0a3-0f804db66f8e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_WeightedSumIntegralFormula
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NoExceptionalOfNoRealZero
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2b2
open Formalism.HermitianLattices.GL2b2.PfN
open Complex
namespace Formalism.HermitianLattices.GL2b2.PfN
theorem _root_.solution (δ R : ℝ) (hδ : 0 < δ) :
    Summable (fun k : ℕ => 4 * R * ((k : ℝ) + 1) ^ (-1 - δ)) := by
  apply Summable.mul_left
  have h := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (show -1 - δ < -1 by linarith))
  simpa using h
end Formalism.HermitianLattices.GL2b2.PfN
