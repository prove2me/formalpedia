-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz7.edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:01.067919+00:00
-- url     : https://prove2.me/submissions/5217cb01-572b-46e7-8f27-0c35f24681f5

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz7_rho_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_edgeFactorBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_positionAfter
import Theorems.Thm_Formalism_FourierDecayAlt_P_positionTop


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz7
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz7
theorem _root_.solution (c : Cfg) (de de' : ℕ → ℝ) (Y : ℝ) (l : ℕ) (h : c.Ok) (hw : IsWord c.k de)
    (hw' : IsWord c.k de') (hl : 1 ≤ l) (hlk : l + 2 ≤ c.k) (hY : Y ∈ c.cutI l) :
    0 < c.aeff ∧ c.U1 (-Y) * c.rho de de' (-Y) (c.k - 1) ≤ 8 / c.aeff := by
  obtain ⟨hU0, hU1, hU2⟩ := edgeFactorBound c Y l h hl hlk hY
  have hr0 := rho_nonneg c de de' Y l (c.k - 1) h hlk hY
  have hD : (1:ℝ) ≤ c.Del := h.hDel
  have hkR : (4:ℝ) ≤ c.k := by exact_mod_cast h.hk
  have hv1 : 0 ≤ c.v 1 := by
    unfold Cfg.v
    push_cast
    nlinarith [h.hv0, mul_nonneg (by linarith : (0:ℝ) ≤ c.Del) (by linarith : (0:ℝ) ≤ (c.k:ℝ) - 2)]
  have ha : 4 * c.k * c.Del ≤ c.a - c.v 1 := h.ha
  have h4 : 0 < 4 * (c.k:ℝ) * c.Del := mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  have hapos : 0 < c.a - c.v 1 := by linarith
  have hapos' : 0 < c.a := by linarith
  cases htop : c.top
  · have haeff : c.aeff = c.a - c.v 1 := by simp [Cfg.aeff, htop]
    rw [haeff]
    refine ⟨hapos, ?_⟩
    have hr1 := positionAfter c de de' Y l (c.k - 1) h hw hw' hl (by omega) (by omega)
      (Or.inr htop) hY
    have hx : 0 < 1 / (c.a - c.v 1) := one_div_pos.mpr hapos
    have e : 8 / (c.a - c.v 1) = 8 * (1 / (c.a - c.v 1)) := by ring
    calc c.U1 (-Y) * c.rho de de' (-Y) (c.k - 1) ≤ (1 / (c.a - c.v 1)) * 1 :=
          mul_le_mul hU1 hr1 hr0 hx.le
      _ ≤ 8 / (c.a - c.v 1) := by rw [e]; linarith
  · obtain ⟨hbp1, _⟩ := h.htop htop
    have hb1 : (1:ℝ) ≤ c.b 1 := h.hb1
    have hbp : 0 < c.bp := by linarith
    have hk0 : (c.k:ℝ) ≠ 0 := (by linarith : (0:ℝ) < c.k).ne'
    have hD0 : c.Del ≠ 0 := (by linarith : (0:ℝ) < c.Del).ne'
    have hkD : 0 < (c.k:ℝ) * c.Del := mul_pos (by linarith) (by linarith)
    have haeff : c.aeff = c.a * c.bp / (c.k * c.Del) := by simp [Cfg.aeff, htop]
    rw [haeff]
    refine ⟨div_pos (mul_pos hapos' hbp) hkD, ?_⟩
    have hr1 := positionTop c de de' Y l h htop hl hlk hY
    have ha0 := hapos'.ne'
    have hb0 := hbp.ne'
    calc c.U1 (-Y) * c.rho de de' (-Y) (c.k - 1) ≤ (2 / c.a) * (4 * c.k * c.Del / c.bp) :=
          mul_le_mul (hU1.trans hU2) hr1 hr0 (div_nonneg (by norm_num) hapos'.le)
      _ = 8 / (c.a * c.bp / (c.k * c.Del)) := by
          field_simp
          ring
end Formalism.FourierDecayAlt.P.Sz7
