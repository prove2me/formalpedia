-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2b2.PfN.tt_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:11:25.491036+00:00
-- url     : https://prove2.me/submissions/9ec21191-66e8-465d-a508-9122d5c1319b

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
theorem _root_.solution (k : ℕ) (σ : ℝ) : tt k (σ : ℂ) = ((tr k σ : ℝ) : ℂ) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have aux : ∀ c : ℝ, 1 ≤ c → ((8 * (k : ℝ) + c : ℝ) : ℂ) ^ (-(σ : ℂ)) = (((8 * (k : ℝ) + c) ^ (-σ) : ℝ) : ℂ) := by
    intro c hc
    rw [ofReal_cpow (by positivity), ofReal_neg]
  unfold tt tr
  rw [aux 1 le_rfl, aux 3 (by norm_num), aux 5 (by norm_num), aux 7 (by norm_num)]
  simp only [ofReal_add, ofReal_sub]
end Formalism.HermitianLattices.GL2b2.PfN
