-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.base_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:56:06.764798+00:00
-- url     : https://prove2.me/submissions/50cbabef-1850-4579-a3c2-46aff308dbfe

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_norm_psi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ}
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution (β t : ℂ) (g : (Fin d → ℂ) → ℂ) {S : ℝ} {a : (Fin d → ℂ) → V} (hc : HasCompactSupport a)
    (hb : ∀ x, ‖a x‖ ≤ S) :
    ‖∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d))‖ ≤ S * (muPi β (Fin d) (tsupport a)).toReal := by
  have h1 : ∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d)) =
      ∫ x in tsupport a, psi β (g x / t) • a x ∂(muPi β (Fin d)) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]
  rw [h1]
  refine norm_setIntegral_le_of_norm_le_const (IsCompact.measure_lt_top hc) ?_
  intro x _
  rw [norm_smul, norm_psi, one_mul]
  exact hb x
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
