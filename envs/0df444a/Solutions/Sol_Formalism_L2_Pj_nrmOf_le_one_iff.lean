-- Prove2me | solution 1 for Formalism.L2.Pj.nrmOf_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:10:25.746703+00:00
-- url     : https://prove2.me/submissions/4b229e87-5e3a-480a-91f8-530ff3c484ca

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Theorems.Thm_Formalism_L2_Pj_one_lt_absNorm_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open scoped WithZero
open Formalism Formalism.L2 Formalism.L2.Pj
attribute [instance] CDVR.cr CDVR.dom CDVR.dvr CDVR.cpl CDVR.ch0
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
namespace Formalism.L2.Pj
theorem _root_.solution {v : EReal} (hv : v ≠ ⊥) : nrmOf la v ≤ 1 ↔ 0 ≤ v := by
  by_cases ht : v = ⊤
  · subst ht; simp [nrmOf]
  lift v to ℝ using ⟨ht, hv⟩
  simp only [nrmOf, EReal.coe_ne_top, if_false, EReal.toReal_coe, EReal.coe_nonneg]
  rw [← Real.rpow_zero (Ideal.absNorm la.asIdeal : ℝ),
    Real.rpow_le_rpow_left_iff (one_lt_absNorm_real la)]
  constructor <;> intro h <;> linarith
end Formalism.L2.Pj
