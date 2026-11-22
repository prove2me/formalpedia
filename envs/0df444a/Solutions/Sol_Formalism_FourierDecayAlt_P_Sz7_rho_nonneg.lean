-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz7.rho_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:16:41.239368+00:00
-- url     : https://prove2.me/submissions/524f0956-c1cd-4300-aa00-c5b380bc2121

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary

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
theorem _root_.solution (c : Cfg) (de de' : ℕ → ℝ) (Y : ℝ) (l i : ℕ) (h : c.Ok)
    (hlk : l + 2 ≤ c.k) (hY : Y ∈ c.cutI l) : 0 ≤ c.rho de de' (-Y) i := by
  unfold Cfg.rho
  split_ifs with ht
  · obtain ⟨h1, _⟩ := h.htop ht.1
    have hY' : 5 / 2 ≤ c.v l + Y ∧ c.v l + Y ≤ c.Del / 2 := hY
    have hD : (1:ℝ) ≤ c.Del := h.hDel
    have hb1 : (1:ℝ) ≤ c.b 1 := h.hb1
    have hv : 4 * c.Del ≤ c.v l := by
      unfold Cfg.v
      have hkl : (l:ℝ) + 2 ≤ c.k := by exact_mod_cast hlk
      nlinarith [h.hv0, mul_nonneg (by linarith : (0:ℝ) ≤ c.Del) (by linarith : (0:ℝ) ≤ (c.k:ℝ) - 2 - l)]
    exact div_nonneg (Real.sqrt_nonneg _) (by linarith [hY'.2])
  · exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
end Formalism.FourierDecayAlt.P.Sz7
