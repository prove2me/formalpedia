-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x7.dilJacRaw_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:45:08.767011+00:00
-- url     : https://prove2.me/submissions/3c1241a2-cd11-4e45-b1aa-76b601bee01c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_sigmaFinite_of_haar
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_aDil_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_conjM_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_dil_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open B2x7
open Formalism.FourierDecayAlt.P.B2x7
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x7
theorem _root_.solution (hU : HaarUnique) (hN : ClosedN) (hR : NRecHaar) (hE : HaarNExists) : DilJacRaw := by
  intro k r
  induction r with
  | zero =>
    intro μN _ t _
    rw [aDil_zero, conjM_one, Measure.map_id]
    simp [kap]
  | succ r' ih =>
    rw [Nat.add_comm r' 1]
    intro μN hμ t ht
    obtain ⟨μ', hμ'⟩ := hE k r'
    have := sigmaFinite_of_haar hμ'
    obtain ⟨c, hc⟩ := hU k (1 + r') (Nset k (1 + r')) _ μN (hN k (1 + r')) (hR k r' μ' hμ') hμ.conc hμ.left hμ.finite_compact
    rw [hc, Measure.map_smul, dil_step μ' t ht (ih μ' hμ' t ht), smul_comm]
end Formalism.FourierDecayAlt.P.B2x7
