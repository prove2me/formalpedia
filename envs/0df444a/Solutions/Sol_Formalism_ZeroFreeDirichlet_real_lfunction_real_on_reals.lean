-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.real_lfunction_real_on_reals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:45:18.901536+00:00
-- url     : https://prove2.me/submissions/7ebcca6d-0fc3-4d93-9924-19d3ca3aa07e

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_TrivReal
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRealPos
import Theorems.Thm_Formalism_ZeroFreeDirichlet_real_character_lfunction_im_eq_zero
import Theorems.Thm_Formalism_ZeroFreeDirichlet_lfunction_tendsto_one_atTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution : LRealPos := by
  intro q _ χ hχ hχ1 σ₀ hnz σ hσ
  have him : ∀ t : ℝ, (DirichletCharacter.LFunction χ t).im = 0 := real_character_lfunction_im_eq_zero χ hχ hχ1
  refine ⟨him σ, ?_⟩
  by_contra hneg
  rw [not_lt] at hneg
  have hcont : Continuous fun t : ℝ => (DirichletCharacter.LFunction χ t).re :=
    Complex.continuous_re.comp
      ((DirichletCharacter.differentiable_LFunction hχ1).continuous.comp Complex.continuous_ofReal)
  obtain ⟨x, hx1, hx⟩ : ∃ x : ℝ, σ ≤ x ∧ 0 < (DirichletCharacter.LFunction χ x).re := by
    have hev : ∀ᶠ x : ℝ in atTop, 0 < (DirichletCharacter.LFunction χ x).re :=
      ((Complex.continuous_re.tendsto 1).comp (lfunction_tendsto_one_atTop χ)).eventually
        (lt_mem_nhds (by norm_num))
    obtain ⟨x, hx⟩ := (hev.and (eventually_ge_atTop σ)).exists
    exact ⟨x, hx.2, hx.1⟩
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hx1 hcont.continuousOn ⟨hneg, hx.le⟩
  apply hnz c (le_trans hσ hc.1)
  exact Complex.ext (by simpa using hc0) (by simpa using him c)
end Formalism.ZeroFreeDirichlet
