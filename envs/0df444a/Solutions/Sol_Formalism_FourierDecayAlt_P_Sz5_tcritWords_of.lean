-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.tcritWords_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:16.737416+00:00
-- url     : https://prove2.me/submissions/9ac0df19-1047-4da2-8a30-20c091b50c9c

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound

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
theorem _root_.solution (hVW : VandWords) : TcritWords := by
  intro c de de' ka rd g VV h hvth hw hw' hka hrd hg hVV
  obtain ⟨hV, hV', hL⟩ := hVW c de de' h hvth hw hw'
  have hk4 : (4:ℝ) ≤ (c.k:ℝ) := by exact_mod_cast h.hk
  have hk0 : (0:ℝ) < (c.k:ℝ) := by linarith
  have hkne : (c.k:ℝ) ≠ 0 := hk0.ne'
  have hP1 : 0 < TcritPow c.k c.m ka rd g VV (Vand c.k (c.u de)) := by
    unfold TcritPow
    positivity
  have hP2 : 0 < TcritPow c.k c.m ka rd g VV (Vand c.k (c.u de')) := by
    unfold TcritPow
    positivity
  have hR : 0 < Vand c.k (c.u de') / Vand c.k (c.u de) := div_pos hV' hV
  refine ⟨?_, ?_⟩
  · unfold Tcrit
    rw [← Real.div_rpow hP1.le hP2.le]
    congr 1
    have key : ∀ P : ℝ, 0 < P →
        (P / Vand c.k (c.u de)) / (P / Vand c.k (c.u de')) = Vand c.k (c.u de') / Vand c.k (c.u de) := by
      intro P hP
      have h1 := hP.ne'
      have h2 := hV.ne'
      have h3 := hV'.ne'
      first
      | (field_simp; done)
      | (field_simp; ring)
      | (rw [div_div_div_cancel_left' _ _ h1])
    unfold TcritPow
    exact key _ (by positivity)
  · have hrw : (Vand c.k (c.u de') / Vand c.k (c.u de)) ^ ((1:ℝ) / (c.k:ℝ)) =
        Real.exp (Real.log (Vand c.k (c.u de') / Vand c.k (c.u de)) * (1 / (c.k:ℝ))) :=
      Real.rpow_def_of_pos hR _
    rw [hrw]
    obtain ⟨hL1, hL2⟩ := abs_le.mp hL
    have ht0 : (0:ℝ) < 1 / (c.k:ℝ) := by positivity
    have ht : (c.k:ℝ) * (1 / (c.k:ℝ)) = 1 := by
      first
      | exact mul_one_div_cancel hkne
      | field_simp
    have ht4 : (1:ℝ) / (c.k:ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hk4
    have e3 : ((c.k:ℝ) / 2 + 1) * (1 / (c.k:ℝ)) = 1 / 2 + 1 / (c.k:ℝ) := by
      linear_combination (1/2:ℝ) * ht
    have u1 := mul_le_mul_of_nonneg_right hL2 ht0.le
    have u2 := mul_le_mul_of_nonneg_right hL1 ht0.le
    constructor
    · apply Real.exp_le_exp.mpr
      nlinarith
    · apply Real.exp_le_exp.mpr
      nlinarith
end Formalism.FourierDecayAlt.P.Sz5
