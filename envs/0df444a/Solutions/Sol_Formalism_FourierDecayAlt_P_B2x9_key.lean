-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:11:25.117382+00:00
-- url     : https://prove2.me/submissions/3e94b92d-e074-45b2-b66d-d77965d439dc

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_hermitian_form_base_vector_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_eta_xi
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_parametrisation_base_vector_image
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_heis_mem_P
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lev_mem_P
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_tau_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_oneStep_eq

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution (hG : ClosedG) (HA : HeisAct) (HI : HeisInv) (OM : OneStepMem) (OC : OneStepCoord) (SD : StabDecomp)
    (hP : IsClosedSubgroup (P1set k r')) (a : Mat k (1 + r')) (ha : a ∈ GV k (1 + r')) (p : ℂ × HPar k r') (hc : p.1 ≠ 0)
    (hv : (a *ᵥ xi k r' p) (iL k r') ≠ 0) :
    ∃ q ∈ P1set k r', a * (Matrix.of (tau k r' p) : Mat k (1 + r')) =
      (Matrix.of (tau k r' (eta k r' (a *ᵥ xi k r' p))) : Mat k (1 + r')) * q := by
  set g : Mat k (1 + r') := a * (Matrix.of (tau k r' p) : Mat k (1 + r')) with hg
  have hgG : g ∈ GV k (1 + r') := (hG k (1 + r')).mul_mem _ ha _ (tau_mem hG HI OM p hc)
  have hge : g *ᵥ e0 k r' = a *ᵥ xi k r' p := by
    rw [hg, ← Matrix.mulVec_mulVec, parametrisation_base_vector_image HA]
  have hc' : herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (e0 k r') ≠ 0 := by
    rw [hermitian_form_base_vector_right, hge]; exact hv
  obtain ⟨⟨x₁, g₁, x₂⟩, ⟨hg₁, hdec⟩, _⟩ := OC k r' g hgG hc'
  dsimp only at hg₁ hdec
  rw [oneStep_eq HI] at hdec
  have hq : ιLev k 1 r' g₁ * heis0 k r' x₂ ∈ P1set k r' :=
    hP.mul_mem _ (lev_mem_P SD g₁ hg₁) _ (heis_mem_P hG SD x₂)
  refine ⟨_, hq, ?_⟩
  have h2 : a *ᵥ xi k r' p = xi k r' (herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (e0 k r'), (-x₁.1, -x₁.2)) := by
    rw [← hge]
    conv_lhs => rw [hdec]
    rw [← Matrix.mulVec_mulVec, hq.2, parametrisation_base_vector_image HA]
  rw [h2, eta_xi _ hc']
  exact hdec
end Formalism.FourierDecayAlt.P.B2x9
