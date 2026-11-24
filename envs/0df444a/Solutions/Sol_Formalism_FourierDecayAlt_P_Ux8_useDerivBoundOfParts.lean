-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.useDerivBoundOfParts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:42:24.928367+00:00
-- url     : https://prove2.me/submissions/c6d2cf00-2736-4149-9b1f-8b69670bbf76

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_cc_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
namespace Formalism.FourierDecayAlt.P.Ux8
theorem _root_.solution : UseDerivBoundOfParts := by
  intro hC2 hEx _ hSem hComp hDBD hDBC
  intro C₁ C₂
  obtain ⟨Cc, hCc⟩ := hC2 C₁ C₂
  refine ⟨Cc, ?_⟩
  intro k p s ρ Wp Wq _ _ _ _ _ _ ι _ U hOk A₀ hA₀
  obtain ⟨h1, h2, h3, C, hC⟩ := hCc k p s ρ Wp Wq ι U hOk A₀ hA₀
  obtain ⟨_, hs1, _⟩ := hOk
  refine ⟨h1, h2, h3, max C 0, ?_⟩
  intro bet Cp hCp hPos hLB hcong f c hf
  have hc0 : 0 ≤ c := cc_nonneg hf
  have ha0 : 0 ≤ U.a C₂ A₀ := le_trans (by positivity) h2
  obtain ⟨V, indexVFirst, indexVSecond, hVc, ⟨M⟩⟩ := hEx k ρ (ι → (Wq →L[ℂ] Wp)) (U.a C₂ A₀) U.mmB U.S
  obtain ⟨Φ, hev, hbd⟩ := hC f c hf V M
  obtain ⟨pn, hpn, hpC⟩ := hSem k ρ (ι → (Wq →L[ℂ] Wp)) bet (U.a C₂ A₀) U.AB Cp U.mmB U.S h3 hCp hPos hLB V M
  obtain ⟨V', indexWFirst, indexWSecond, hW, T, hT, _⟩ := hComp V pn Cp hpC
  have hTn : ‖T‖ ≤ Cp := ContinuousLinearMap.opNorm_le_bound T hCp (fun v => by rw [hT]; exact hpC v)
  refine ⟨V', indexWFirst, indexWSecond, hW, fun Z => T (Φ Z), ?_, ?_⟩
  · intro J w hJ
    have hv : ∀ g ∈ B.GV k ρ, M.ev (∑ Z ∈ J, w Z • Φ Z) g = (∑ Z ∈ J, w Z • U.Phi f Z) g := by
      intro g hg
      rw [map_sum, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun Z hZ => ?_
      rw [map_smul, Pi.smul_apply, Pi.smul_apply, hev Z (hJ Z hZ) g hg]
    have hb := hcong _ _ _ _ hv hv
    have hsum : (∑ Z ∈ J, w Z • T (Φ Z)) = T (∑ Z ∈ J, w Z • Φ Z) := by
      rw [map_sum]
      simp only [map_smul]
    show ‖∑ Z ∈ J, w Z • T (Φ Z)‖ ^ 2 = _
    rw [hsum, hT, hpn, hb]
  · intro Kd hKd
    have hD1 : G.DerivBound (C₂ * s ^ 2) Kd (fun Z => max C 0 * c * min 1 (‖Z‖ ^ (-(U.a C₂ A₀)))) Φ := by
      refine hDBD s (C₂ * s ^ 2) V Φ (U.a C₂ A₀) (max C 0 * c) Kd hs1 ha0
        (mul_nonneg (le_max_right _ _) hc0) hKd ?_
      intro Z hZ
      obtain ⟨hcd, hb⟩ := hbd Z hZ
      refine ⟨hcd, fun q hq => le_trans (hb q hq) ?_⟩
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hc0) (by positivity)
    have hD2 := hDBC s (C₂ * s ^ 2) V V' T Φ Kd _ hD1
    intro Z hZ
    obtain ⟨hcd, hb⟩ := hD2 Z hZ
    refine ⟨hcd, fun j hj => le_trans (hb j hj) ?_⟩
    have hm : 0 ≤ max C 0 * c * min 1 (‖Z‖ ^ (-(U.a C₂ A₀))) :=
      mul_nonneg (mul_nonneg (le_max_right _ _) hc0) (le_min zero_le_one (Real.rpow_nonneg (norm_nonneg _) _))
    calc ‖T‖ * (max C 0 * c * min 1 (‖Z‖ ^ (-(U.a C₂ A₀))))
        ≤ Cp * (max C 0 * c * min 1 (‖Z‖ ^ (-(U.a C₂ A₀)))) := mul_le_mul_of_nonneg_right hTn hm
      _ = max C 0 * Cp * c * min 1 (‖Z‖ ^ (-(U.a C₂ A₀))) := by ring
end Formalism.FourierDecayAlt.P.Ux8
