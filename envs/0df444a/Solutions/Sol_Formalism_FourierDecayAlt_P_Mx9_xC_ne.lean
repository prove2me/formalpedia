-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx9.xC_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:36.150555+00:00
-- url     : https://prove2.me/submissions/9f209d44-5bca-47fe-845e-db6824bd0f36

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
theorem _root_.solution (hR : RealPoints) (P : Par) (π : Ty P) (n : ℕ) (Y : ℝ)
    (h : 0 < (-1 : ℝ) ^ n * I.xpoly P.k (rho P π) Y) : xC P π (Y : ℂ) ≠ 0 := by
  intro h0
  rw [(hR P π Y).1] at h0
  have h1 : I.xpoly P.k (rho P π) Y = 0 := by exact_mod_cast h0
  rw [h1, mul_zero] at h
  exact lt_irrefl _ h
end Formalism.FourierDecayAlt.P.Mx9
