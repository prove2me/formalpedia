-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2b2.PfN.chi8_value_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:12:09.248798+00:00
-- url     : https://prove2.me/submissions/efa55aa8-a172-4856-8637-dba2f64425a0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_WeightedSumIntegralFormula
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NoExceptionalOfNoRealZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2b2
open Formalism.HermitianLattices.GL2b2.PfN
open Complex
namespace Formalism.HermitianLattices.GL2b2.PfN
theorem _root_.solution (k j : ℕ) : ZeroFreeRegionGL2.chi8 ((k * 8 + j : ℕ) : ZMod 8) = ((ZMod.χ₈ (j : ZMod 8) : ℤ) : ℂ) := by
  have : ((k * 8 + j : ℕ) : ZMod 8) = (j : ZMod 8) := by
    push_cast
    have h8 : (8 : ZMod 8) = 0 := by decide
    rw [h8]; ring
  rw [this]
  rfl
end Formalism.HermitianLattices.GL2b2.PfN
