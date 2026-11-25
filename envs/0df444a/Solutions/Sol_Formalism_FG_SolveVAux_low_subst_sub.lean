-- Prove2me | solution 1 for Formalism.FG.SolveVAux.low_subst_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:55:27.628504+00:00
-- url     : https://prove2.me/submissions/b49d4d35-2ec2-41d9-8294-60fbe5cab400

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow_sub_succ
import Theorems.Thm_Formalism_FG_SolveVAux_hasSubst_of_low

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.SolveVAux
open MvPowerSeries
variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι] {τ : Type w}
namespace Formalism.FG.SolveVAux
theorem _root_.solution {M : ℕ} {k k' : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i))
    (hk' : ∀ i, Low 1 (k' i)) (hkk : ∀ i, Low M (k i - k' i)) {g : MvPowerSeries ι R}
    (hg : Low 2 g) : Low (M + 1) (subst k g - subst k' g) := by
  intro d hd
  have hs := hasSubst_of_low hk
  have hs' := hasSubst_of_low hk'
  rw [map_sub, coeff_subst hs, coeff_subst hs', ← finsum_sub_distrib (coeff_subst_finite hs g d)
    (coeff_subst_finite hs' g d)]
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  rw [← smul_sub]
  rcases lt_or_ge e.degree 2 with he | he
  · rw [hg e he, zero_smul]
  · have := low_pow_sub_succ hk hk' hkk e he d hd
    rw [map_sub] at this
    simp only [P] at this
    rw [this, smul_zero]
end Formalism.FG.SolveVAux
