-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.neg_half_le_gExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:34.874808+00:00
-- url     : https://prove2.me/submissions/286a546e-e406-4573-95a5-eaa7cd174783

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffAbel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.HermitianLattices.Ext.SupplyAP
private theorem hFun_hasDerivAt (t : ℝ) : HasDerivAt hFun (1 - (1 - t) * Real.exp t) t := by
  have h1 : HasDerivAt (fun t : ℝ => 2 + t) 1 t := (hasDerivAt_id t).const_add 2
  have h2 : HasDerivAt (fun t : ℝ => 2 - t) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 2
  have h3 := h2.mul (Real.hasDerivAt_exp t)
  have h4 := h1.sub h3
  exact h4.congr_deriv (by ring)
private theorem hFun_mono : Monotone hFun := by
  refine monotone_of_deriv_nonneg (fun t => (hFun_hasDerivAt t).differentiableAt) ?_
  intro t
  rw [(hFun_hasDerivAt t).deriv]
  have h1 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  have h2 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos t).le
  linarith
end Formalism.HermitianLattices.Ext.SupplyAP
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution {t : ℝ} (ht : 0 < t) : -(1 / 2) ≤ gExp t := by
  unfold gExp
  have hE : 0 < Real.exp t - 1 := by linarith [Real.add_one_le_exp t]
  have hh : hFun 0 ≤ hFun t := hFun_mono ht.le
  have h0 : hFun 0 = 0 := by simp [hFun]
  rw [h0] at hh
  unfold hFun at hh
  rw [div_sub_div _ _ hE.ne' ht.ne', le_div_iff₀ (mul_pos hE ht)]
  nlinarith
end Formalism.HermitianLattices.Ext.SupplyAP
