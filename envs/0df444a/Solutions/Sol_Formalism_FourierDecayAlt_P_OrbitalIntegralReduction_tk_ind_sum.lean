-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.tk_ind_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:17.731771+00:00
-- url     : https://prove2.me/submissions/8360e53c-ab31-4938-b7de-84373f52d827

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_out_subG
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_mk_eqG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {V : Type} [AddCommGroup V]
open Classical
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (N : AddSubgroup V) (c : V) :
    ∑ᶠ y : V ⧸ N, (if (Quotient.out y : V) - c ∈ N then (1 : ℂ) else 0) = 1 := by
  rw [finsum_eq_single _ ((c : V) : V ⧸ N)]
  · rw [if_pos (tk_out_subG N c)]
  · intro y hy
    rw [if_neg]
    intro h
    apply hy
    have := (tk_mk_eqG N _ _).2 h
    rwa [QuotientAddGroup.out_eq'] at this
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
