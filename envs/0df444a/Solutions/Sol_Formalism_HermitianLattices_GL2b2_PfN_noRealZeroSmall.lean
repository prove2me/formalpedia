-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2b2.PfN.noRealZeroSmall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:54.051436+00:00
-- url     : https://prove2.me/submissions/e65af7ab-f978-43e9-94c2-b88eb6c3c430

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_WeightedSumIntegralFormula
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NoExceptionalOfNoRealZero
import Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_tt_bound
import Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_summable_u
import Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_tt_ofReal
import Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_tr_pos
import Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_L_eq
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_zetaRealNonvanish
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
theorem _root_.solution : NoRealZeroSmall := by
  refine ⟨Formalism.zetaRealNonvanish, ?_⟩
  intro σ h0 h1
  rw [L_eq σ h0 h1]
  simp_rw [tt_ofReal]
  rw [← Complex.ofReal_tsum]
  have hs : Summable (fun k => tr k σ) := by
    apply Summable.of_norm_bounded (summable_u σ 1 h0)
    intro k
    have := tt_bound k (σ : ℂ) σ 1 h0 (by simp) (by simp [abs_of_pos h0]; linarith)
    rwa [tt_ofReal, Complex.norm_real] at this
  have := hs.tsum_pos (fun k => (tr_pos k σ h0).le) 0 (tr_pos 0 σ h0)
  exact_mod_cast this.ne'
end Formalism.HermitianLattices.GL2b2.PfN
