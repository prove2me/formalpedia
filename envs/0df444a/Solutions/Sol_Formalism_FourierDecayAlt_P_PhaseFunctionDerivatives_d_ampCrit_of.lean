-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.d_ampCrit_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:27.338116+00:00
-- url     : https://prove2.me/submissions/8293c29f-b386-4233-a8dc-6b9804550186

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_d_continuous_red
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_d_continuous_M
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_d_MXY_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_d_continuous_cutM
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_d_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_d_cutM_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_isStrictUpper_strictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_cof
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_remainder
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_isStrictUpper_strictUpper


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
theorem _root_.solution (hC : CofLowerR) (hDet : DetMXY) : AmpCritContinuous := by
  intro m β Kc hK h0 ε hε hε'
  obtain ⟨t₀, c₀, ht₀, hc₀, hlow⟩ := hC m Kc hK h0 2 (by norm_num)
  refine ⟨t₀, ht₀, ?_⟩
  intro V _ _ _ Φ bd hΦ t D z ht htt hD hz
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht
  have hτ0 : 0 < ‖t‖ ^ (-ε) := Real.rpow_pos_of_pos htn _
  have hred := d_continuous_red m (fun _ => z)
  have hcof : Continuous (fun y : UT (m + 2) → ℂ => cofXY m t (fun _ => z, y)) := by
    unfold cofXY
    exact (G7.continuous_cof m t).comp
      ((continuous_fst.comp (continuous_snd.comp (continuous_snd.comp hred))).prodMk
        (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp hred))))
  have hthr : 0 < c₀ * ‖t‖ ^ ε := mul_pos hc₀ (Real.rpow_pos_of_pos htn _)
  have hvan : ∀ y : UT (m + 2) → ℂ, ‖cofXY m t (fun _ => z, y)‖ < c₀ * ‖t‖ ^ ε →
      ampIn β m ε Φ D t (fun _ => z, y) = 0 := by
    intro y hy
    by_cases hc : cofXY m t (fun _ => z, y) = 0
    · simp [ampIn, amp, hc]
    · have hcut : cutM (‖t‖ ^ (-ε)) (MXY m D t (fun _ => z, y)) = 0 := by
        by_contra hne
        have hent := d_cutM_entries _ hτ0 _ hne
        obtain ⟨e1, e2, e3, e4, e5⟩ := d_entries t _ _ _ _ _ (2 * ‖t‖ ^ (-ε)) (by positivity) hent
        have hc' : Cof (strictUpper (redOf m (fun _ => z, y)).2.2.1) (redOf m (fun _ => z, y)).2.2.2 t ≠ 0 := hc
        have hrel : t ^ (m + 1) * (redOf m (fun _ => z, y)).1 =
            D + Cof (strictUpper (redOf m (fun _ => z, y)).2.2.1) (redOf m (fun _ => z, y)).2.2.2 t *
              rhoXY m D t (fun _ => z, y) +
              R0 (strictUpper (redOf m (fun _ => z, y)).2.2.1) (redOf m (fun _ => z, y)).2.2.2
                (redOf m (fun _ => z, y)).2.1 t := by
          rw [rhoXY, rho1, mul_div_cancel₀ _ hc']
          ring
        have := hlow ε hε hε' D hD t ht htt _ _ _ _ _ (G7.isStrictUpper_strictUpper _) e1 e2 e3 e4 e5 hrel
        exact absurd hy (not_lt.2 this)
      simp [ampIn, amp, cutPhi, hcut]
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hc : cofXY m t (fun _ => z, y) = 0
  · have hW : ∀ᶠ y' in 𝓝 y, ‖cofXY m t (fun _ => z, y')‖ < c₀ * ‖t‖ ^ ε :=
      (hcof.norm.continuousAt (x := y)).eventually_lt continuousAt_const (by simpa [hc] using hthr)
    have hE : (fun y' => ampIn β m ε Φ D t (fun _ => z, y')) =ᶠ[𝓝 y] fun _ => (0 : V) :=
      hW.mono fun y' h => hvan y' h
    exact continuousAt_const.congr hE.symm
  · have hrho : ContinuousAt (fun y' : UT (m + 2) → ℂ => rhoXY m D t (fun _ => z, y')) y := by
      unfold rhoXY rho1
      refine ContinuousAt.div ?_ hcof.continuousAt hc
      exact (((continuous_const.mul (continuous_fst.comp hred)).sub continuous_const).sub
        ((G7.continuous_remainder m t).comp (continuous_snd.comp hred))).continuousAt
    have hM : ContinuousAt (fun y' : UT (m + 2) → ℂ => MXY m D t (fun _ => z, y')) y := by
      simp only [d_MXY_eq]
      exact ContinuousAt.comp (f := fun y' : UT (m + 2) → ℂ => (rhoXY m D t (fun _ => z, y'), y'))
        (d_continuous_M m t (fun _ => z)).continuousAt (hrho.prodMk continuousAt_id)
    have hΦc : ContinuousAt Φ (MXY m D t (fun _ => z, y)) :=
      (hΦ _ ⟨D, hD, (hDet m D t _ hc).symm⟩).1.continuousAt
    have hg : ContinuousAt (fun y' : UT (m + 2) → ℂ => gRem m D t (fun _ => z, y')) y := by
      unfold gRem
      exact (hrho.sub continuousAt_const).div_const _
    have hinv : ContinuousAt (fun y' : UT (m + 2) → ℂ => (‖cofXY m t (fun _ => z, y')‖ ^ 2)⁻¹) y :=
      ContinuousAt.inv₀ (hcof.norm.pow 2).continuousAt (by simpa using hc)
    unfold ampIn amp cutPhi
    refine ContinuousAt.smul (ContinuousAt.mul ((G7.continuous_psi β).continuousAt.comp hg)
      (Complex.continuous_ofReal.continuousAt.comp hinv)) (ContinuousAt.smul ?_
        (ContinuousAt.comp (f := fun y' : UT (m + 2) → ℂ => MXY m D t (fun _ => z, y')) hΦc hM))
    exact Complex.continuous_ofReal.continuousAt.comp
      (ContinuousAt.comp (f := fun y' : UT (m + 2) → ℂ => MXY m D t (fun _ => z, y'))
        (d_continuous_cutM _).continuousAt hM)
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
