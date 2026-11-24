-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux11.hasFDeriv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:00:41.882067+00:00
-- url     : https://prove2.me/submissions/f29f90cd-c633-4b06-9e43-d2b7a877f83a

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_Norming_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_exists_vec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux11
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ X]
namespace Formalism.FourierDecayAlt.P.Ux11
theorem _root_.solution {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {lam : I → V →L[ℝ] E} (hN : Norming lam) {Φ : X → V} {x₀ : X} {r M : ℝ} (hr : 0 < r)
    (D : I → X →L[ℝ] E)
    (hT : ∀ i, ∀ h : X, ‖h‖ < r → ‖lam i (Φ (x₀ + h)) - lam i (Φ x₀) - D i h‖ ≤ M * ‖h‖ ^ 2) :
    ∃ L : X →L[ℝ] V, HasFDerivAt Φ L x₀ ∧ ∀ i, (lam i).comp L = D i := by
  choose ℓ hℓ using exists_vec hN hr D hT
  let ℓ' : X →ₗ[ℝ] V :=
    { toFun := ℓ
      map_add' := fun a b => hN.eq (fun i => by rw [map_add, hℓ, hℓ, hℓ, map_add])
      map_smul' := fun c a => hN.eq (fun i => by rw [map_smul, hℓ, hℓ, map_smul]; rfl) }
  have hL : ∀ h, (LinearMap.toContinuousLinearMap ℓ') h = ℓ h := fun h => rfl
  refine ⟨LinearMap.toContinuousLinearMap ℓ', ?_, fun i => ?_⟩
  · rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : X => ‖h‖ ^ 2) ?_
      (Asymptotics.isLittleO_norm_pow_id one_lt_two)
    refine Asymptotics.IsBigO.of_bound M ?_
    filter_upwards [Metric.ball_mem_nhds (0 : X) hr] with h hh
    rw [mem_ball_zero_iff] at hh
    rw [Real.norm_of_nonneg (by positivity)]
    refine hN _ _ (fun i => ?_)
    have e : lam i (Φ (x₀ + h) - Φ x₀ - (LinearMap.toContinuousLinearMap ℓ') h) =
        lam i (Φ (x₀ + h)) - lam i (Φ x₀) - D i h := by
      rw [map_sub, map_sub, hL, hℓ]
    rw [e]; exact hT i h hh
  · ext h; rw [ContinuousLinearMap.comp_apply, hL, hℓ]
end Formalism.FourierDecayAlt.P.Ux11
