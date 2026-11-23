-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.tk_ind_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:07.624858+00:00
-- url     : https://prove2.me/submissions/c3f4b674-a56b-4bbd-a3e2-1e6f03a85af4

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_S_ind
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_pos


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
variable [TopologicalSpace V] [IsTopologicalAddGroup V]
open Classical
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution {V₀ N M' : AddSubgroup V} (h0 : Lat V₀) (hN : Lat N) (hM' : Lat M')
    (hle : M' ≤ N) (c : V) :
    (Function.support fun y : V ⧸ M' =>
      (if (Quotient.out y : V) - c ∈ N then (1 : ℂ) else 0)).Finite := by
  by_contra hinf
  have h1 := tk_S_ind h0 hN hM' hle c
  unfold tk_S at h1
  rw [finsum_of_infinite_support hinf, mul_zero] at h1
  have := gi_pos hN h0
  have h2 : (gi N V₀ : ℂ) ≠ 0 := by exact_mod_cast this.ne'
  exact h2 h1.symm
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
