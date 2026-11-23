-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx9.qC_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:41.346859+00:00
-- url     : https://prove2.me/submissions/9c3f5d63-e14c-4f44-a575-2cdb189e2b9c

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModelWordsAssemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.M
open Formalism.FourierDecayAlt.P.Mx9
namespace Formalism.FourierDecayAlt.P.Mx9
theorem _root_.solution (hR : RealPoints) (P : Par) (Y : ℝ)
    (h : 0 < I.qpoly P.k P.T P.T' P.u P.u' Y) : qC P (Y : ℂ) ≠ 0 := by
  intro h0
  rw [(hR P (ty0 P) Y).2] at h0
  have h1 : I.qpoly P.k P.T P.T' P.u P.u' Y = 0 := by exact_mod_cast h0
  rw [h1] at h
  exact lt_irrefl _ h
end Formalism.FourierDecayAlt.P.Mx9
