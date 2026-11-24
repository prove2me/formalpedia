-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.closed_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:21:24.709081+00:00
-- url     : https://prove2.me/submissions/9c481a58-680b-4a97-b6ec-cfda9d22af0c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_hpk_unit
import Theorems.Thm_Formalism_QuantumDeterminants_uHGroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution (k r : ℕ) (F : Set (Fin (2 * r + k + 1) → ℂ)) :
    IsClosedSubgroup {g : Mat k r | g ∈ GV k r ∧ ∀ v ∈ F, g *ᵥ v = v} := by
  obtain ⟨h1, hm, hi⟩ := uHGroup _ (Hpk k r) (hpk_unit k r)
  refine ⟨⟨h1, fun v _ => Matrix.one_mulVec v⟩, ?_, ?_, fun a ha => (hi a ha.1).1, ?_⟩
  · intro a ha b hb
    refine ⟨hm a ha.1 b hb.1, fun v hv => ?_⟩
    rw [← Matrix.mulVec_mulVec, hb.2 v hv, ha.2 v hv]
  · intro a ha
    refine ⟨(hi a ha.1).2, fun v hv => ?_⟩
    have h := ha.2 v hv
    calc a⁻¹ *ᵥ v = a⁻¹ *ᵥ (a *ᵥ v) := by rw [h]
      _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hi a ha.1).1, Matrix.one_mulVec]
  · have hc1 : IsClosed {g : Mat k r | g ∈ GV k r} := by
      apply isClosed_eq
      · fun_prop
      · exact continuous_const
    have hc2 : IsClosed {g : Mat k r | ∀ v ∈ F, g *ᵥ v = v} := by
      have : {g : Mat k r | ∀ v ∈ F, g *ᵥ v = v} = ⋂ v ∈ F, {g : Mat k r | g *ᵥ v = v} := by
        ext g; simp
      rw [this]
      refine isClosed_biInter fun v _ => isClosed_eq ?_ continuous_const
      exact Continuous.matrix_mulVec continuous_id continuous_const
    exact hc1.inter hc2
end Formalism.FourierDecayAlt.P.B2x3
