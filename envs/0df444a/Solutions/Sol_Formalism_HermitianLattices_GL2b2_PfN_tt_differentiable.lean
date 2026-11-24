-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2b2.PfN.tt_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:12:02.163323+00:00
-- url     : https://prove2.me/submissions/87267816-f4de-450d-a49c-906ae16ac731

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
theorem _root_.solution (k : ℕ) : Differentiable ℂ (tt k) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have aux : ∀ c : ℝ, 1 ≤ c → Differentiable ℂ (fun s : ℂ => ((8 * (k : ℝ) + c : ℝ) : ℂ) ^ (-s)) := by
    intro c hc
    apply Differentiable.const_cpow differentiable_id.neg
    left
    have : (8 * (k : ℝ) + c) ≠ 0 := by positivity
    exact_mod_cast this
  unfold tt
  exact (((aux 1 le_rfl).sub (aux 3 (by norm_num))).sub (aux 5 (by norm_num))).add (aux 7 (by norm_num))
end Formalism.HermitianLattices.GL2b2.PfN
