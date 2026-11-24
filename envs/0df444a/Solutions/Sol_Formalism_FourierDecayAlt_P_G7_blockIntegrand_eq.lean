-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.blockIntegrand_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:38.50331+00:00
-- url     : https://prove2.me/submissions/4fde12ad-9391-4ce7-ab16-0a2239f1b07d

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_strictUpper_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_cornerRelation
import Theorems.Thm_Formalism_FourierDecayAlt_P_additive_character_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_matrix_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_phase_formula


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ)
    (Φ : Mat (m + 1 + 1) → V) (t c : ℂ) (ht : t ≠ 0) (p : BlockCoord (m + 1)) :
    blockIntegrand β (m + 1) Φ t c p = Fint β m Φ t c (coordMap (m + 1) t p) := by
  have hσ : c + p.1 ⬝ᵥ (wMat (m + 1) *ᵥ (t • p.2.2)) =
      sig (c * t ^ (m + 1)) t (rhoOf t p.1 p.2.1) (strictUpper (t • p.2.1)) (t • p.2.2) := by
    unfold sig
    rw [eq_div_iff (pow_ne_zero _ ht), mul_comm, cornerRelation (m + 1) t c p.1 p.2.2 p.2.1, Xof,
      strictUpper_smul]
  unfold blockIntegrand Fint coordMap
  rw [← (additive_character_psi β _ _).1, phase_formula m t ht p, matrix_entries, hσ, Xof,
    strictUpper_smul]
end Formalism.FourierDecayAlt.P.G7
