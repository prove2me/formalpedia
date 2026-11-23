-- Prove2me | solution 1 for Formalism.L2.Pj.nrmOf_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:40.272519+00:00
-- url     : https://prove2.me/submissions/7fdf3739-8970-44f1-b0cd-0a91d0470cd5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Theorems.Thm_Formalism_L2_Pj_finitePlace_eq_zpow
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
theorem _root_.solution {a : K} (ha : a ≠ 0) {v : EReal} (hv : v ≠ ⊥) :
    nrmOf la ((((vLa la a : ℤ) : ℝ) : EReal) + v) = FinitePlace.mk la a * nrmOf la v := by
  rw [finitePlace_eq_zpow la ha]
  by_cases ht : v = ⊤
  · subst ht; simp [nrmOf]
  lift v to ℝ using ⟨ht, hv⟩
  simp only [nrmOf, ← EReal.coe_add, EReal.coe_ne_top, if_false, EReal.toReal_coe]
  rw [neg_add, Real.rpow_add (by linarith [one_lt_absNorm_real la]), ← Real.rpow_intCast]
  push_cast; ring_nf
end Formalism.L2.Pj
