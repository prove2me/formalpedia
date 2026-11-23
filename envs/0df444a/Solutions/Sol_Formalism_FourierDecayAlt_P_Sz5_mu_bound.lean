-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.mu_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:58.130302+00:00
-- url     : https://prove2.me/submissions/10b3e22d-7a2e-4f79-8d2c-bc960c8a5c3e

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_b_ge_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz5
theorem _root_.solution (c : Cfg) (h : c.Ok) (bb : ℝ) (hs : c.Small bb) :
    Real.exp (-(2 * c.m * Real.log bb / c.k)) ^ c.k * c.prodb ≤ 1 := by
  have hk : (0:ℝ) < (c.k:ℝ) := by
    have := h.hk
    exact_mod_cast (by omega : 0 < c.k)
  have hbb0 : 0 < bb := by linarith [hs.hbb]
  have e1 : Real.exp (-(2 * c.m * Real.log bb / c.k)) ^ c.k = Real.exp (-(2 * c.m * Real.log bb)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    have hk' : (c.k:ℝ) ≠ 0 := hk.ne'
    first
    | (field_simp; done)
    | (field_simp; ring)
  have e2 : Real.exp (2 * c.m * Real.log bb) = bb ^ (2 * c.m) := by
    rw [show (2 * (c.m:ℝ) * Real.log bb) = ((2 * c.m : ℕ) : ℝ) * Real.log bb by push_cast; ring]
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hp : c.prodb ≤ bb ^ (2 * c.m) := by
    unfold Cfg.prodb
    calc ∏ j ∈ Icc 1 c.m, c.b j ≤ ∏ j ∈ Icc 1 c.m, bb ^ 2 := by
          apply Finset.prod_le_prod
          · intro j hj
            rw [Finset.mem_Icc] at hj
            linarith [b_ge_one c h j hj.1 hj.2]
          · intro j hj
            rw [Finset.mem_Icc] at hj
            exact hs.hbj j hj.1 hj.2
      _ = bb ^ (2 * c.m) := by
          first
          | (rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, pow_mul])
          | (rw [Finset.prod_const, Nat.card_Icc, pow_mul])
          | (rw [Finset.prod_const, Nat.card_Icc, pow_mul]; congr 1; omega)
          | (simp [Finset.prod_const, pow_mul])
  have hpos : 0 < bb ^ (2 * c.m) := by positivity
  rw [e1, Real.exp_neg, e2]
  calc (bb ^ (2 * c.m))⁻¹ * c.prodb ≤ (bb ^ (2 * c.m))⁻¹ * bb ^ (2 * c.m) :=
        mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hpos.le)
    _ = 1 := inv_mul_cancel₀ hpos.ne'
end Formalism.FourierDecayAlt.P.Sz5
