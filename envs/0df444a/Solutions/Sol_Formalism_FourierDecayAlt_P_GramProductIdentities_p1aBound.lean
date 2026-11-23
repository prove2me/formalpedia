-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramProductIdentities.p1aBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:29.838789+00:00
-- url     : https://prove2.me/submissions/3dc6006d-8df4-4318-b10c-34c336a22453

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_act_mul
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_GramProductIdentities_pair_act__bf313f925fd6
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_csPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramProductIdentities
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Formalism.FourierDecayAlt.P.GramProductIdentities
theorem _root_.solution : CauchySchwarzInvariantForm := by
  intro A S V _ _ _ _ _ _ _ _ _ ρ RR W x hP hW
  have hcs := csPos A S V ρ RR (act W x) x hP
  have hWW : frm ρ RR (act W x) (act W x) = frm ρ RR x x := by
    simp only [frm]
    rw [pair_act', ← act_mul, ← act_mul, hW]
  rw [hWW] at hcs
  have h0 := (hP x).1
  nlinarith [norm_nonneg (frm ρ RR (act W x) x)]
end Formalism.FourierDecayAlt.P.GramProductIdentities
