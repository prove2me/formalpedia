-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz9.beta_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:55.285585+00:00
-- url     : https://prove2.me/submissions/9c091b35-b15f-4e0c-bfc3-24fafde81337

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SixteenMulLeTwoPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz9
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz9
theorem _root_.solution (hBeta : BetaOnCut) (hAZ : AZeroBound) (c : Cfg) (r : ℕ) (bb : ℝ)
    (de de' : ℕ → ℝ) (ka rd g VV T T' : ℝ) (l : ℕ)
    (hOk : c.Ok) (hm : c.m = 2 * r + 2) (hSm : c.Small bb) (hde : IsWord c.k de)
    (hde' : IsWord c.k de') (hrd : 1 ≤ rd) (hka : ka = 2 * Real.pi / rd) (hg : 2 * Real.pi ≤ g)
    (hFD : FormalDegreeLower c (1 / 2) VV) (hT : 0 < T) (hT' : 0 < T') (hl1 : 1 ≤ l)
    (hl2 : l + 2 ≤ c.k) (hdl : de l ≠ de' l) (D : ℝ) (hD : D ≤ c.Del / 2) (Y : ℝ)
    (hY1 : 5 / 2 ≤ c.v l + Y) (hY2 : c.v l + Y ≤ D) :
    0 ≤ g ^ c.m * c.be ka de de' T T' Y ∧
      g ^ c.m * c.be ka de de' T T' Y ≤
        160 * tv c de de' ka rd g VV T T' * Real.sqrt c.k * Real.sqrt (D / c.Del) := by
  have hpi := Real.pi_pos
  have hg0 : 0 < g := by linarith
  have hka0 : 0 < ka := by rw [hka]; positivity
  have hDel : 0 < c.Del := by linarith [hOk.hDel]
  constructor
  · unfold Cfg.be Cfg.core
    positivity
  · have hYI : Y ∈ c.cutI l := ⟨hY1, hY2.trans hD⟩
    have h := hBeta c r bb de de' ka rd g VV T T' Y l hOk hm hSm hde hde' hrd hka hg hFD hT hT'
      hl1 hl2 hdl hYI
    have hA := (hAZ c bb hOk hSm).2
    have ht : 0 ≤ tv c de de' ka rd g VV T T' := by unfold tv; exact Real.sqrt_nonneg _
    have hs : Real.sqrt ((c.v l + Y) / c.Del) ≤ Real.sqrt (D / c.Del) := by
      apply Real.sqrt_le_sqrt
      gcongr
    calc g ^ c.m * c.be ka de de' T T' Y
        ≤ AZero c bb * tv c de de' ka rd g VV T T' * Real.sqrt c.k *
          Real.sqrt ((c.v l + Y) / c.Del) := h
      _ ≤ 160 * tv c de de' ka rd g VV T T' * Real.sqrt c.k * Real.sqrt (D / c.Del) := by
          gcongr
end Formalism.FourierDecayAlt.P.Sz9
