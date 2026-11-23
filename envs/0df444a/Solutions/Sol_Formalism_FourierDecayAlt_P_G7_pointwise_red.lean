-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.pointwise_red
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:01.623933+00:00
-- url     : https://prove2.me/submissions/35314e1b-bd0f-43c7-856c-b2ebfc1cb70c

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_signature_first_coordinate

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
    (Φ : Mat (m + 1 + 1) → V) (t c : ℂ) (ht : t ≠ 0) (q : RedCoord m) :
    ((‖t ^ (m + 1) / Cof (strictUpper q.2.2.1) q.2.2.2 t‖ ^ 2 : ℝ) : ℂ) •
      Fint β m Φ t c (consMap m
        (t ^ (m + 1) / Cof (strictUpper q.2.2.1) q.2.2.2 t * q.1 +
          (-(c * t ^ (m + 1)) - R0 (strictUpper q.2.2.1) q.2.2.2 q.2.1 t) / Cof (strictUpper q.2.2.1) q.2.2.2 t,
          q.2)) =
    ((‖t‖ ^ (2 * (m + 1)) : ℝ) : ℂ) •
      ((psi β ((rho1 (c * t ^ (m + 1)) q.1 q.2.1 (strictUpper q.2.2.1) q.2.2.2 t +
                ∑ k, xOf (strictUpper q.2.2.1) q.2.2.2 k) / t) *
              (((‖Cof (strictUpper q.2.2.1) q.2.2.2 t‖ ^ 2)⁻¹ : ℝ) : ℂ)) •
            Φ (Mcoord t (strictUpper q.2.2.1) q.2.2.2
              (Fin.cons (rho1 (c * t ^ (m + 1)) q.1 q.2.1 (strictUpper q.2.2.1) q.2.2.2 t) q.2.1) q.1)) := by
  obtain ⟨σ, ρ', x, B⟩ := q
  simp only
  by_cases hC : Cof (strictUpper x) B t = 0
  · simp [hC]
  · have hr : t ^ (m + 1) / Cof (strictUpper x) B t * σ +
        (-(c * t ^ (m + 1)) - R0 (strictUpper x) B ρ' t) / Cof (strictUpper x) B t =
        rho1 (c * t ^ (m + 1)) σ ρ' (strictUpper x) B t := by
      unfold rho1; ring
    rw [hr]
    simp only [Fint, consMap, Fin.cons_zero]
    rw [signature_first_coordinate _ t σ ht ρ' _ B hC, smul_smul, smul_smul]
    congr 1
    rw [norm_div, norm_pow, div_pow, ← pow_mul, mul_comm (m + 1) 2]
    push_cast
    ring
end Formalism.FourierDecayAlt.P.G7
