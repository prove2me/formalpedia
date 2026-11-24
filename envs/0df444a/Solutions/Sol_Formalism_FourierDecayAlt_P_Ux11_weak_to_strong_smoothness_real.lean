-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux11.weak_to_strong_smoothness_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:22:50.230434+00:00
-- url     : https://prove2.me/submissions/92094b8a-b124-4a6d-bf4d-93875d396f71

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_Norming_nonempty
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_lip_ball
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_taylor2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_norm_iter_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_iter_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_norm_apply_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_loc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_hasFDeriv_of

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
theorem _root_.solution (m : ℕ) : ∀ (V I : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (lam : I → V →L[ℝ] E), Norming lam → ∀ (Ω : Set X) (Φ : X → V) (bd : X → ℝ), IsOpen Ω →
    ContinuousOn bd Ω →
    (∀ i, ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun x => lam i (Φ x)) Ω) →
    (∀ i, ∀ q ≤ m + 1, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ q (fun x => lam i (Φ x)) x‖ ≤ bd x) →
    ContDiffOn ℝ (m : WithTop ℕ∞) Φ Ω ∧ ∀ q ≤ m, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ q Φ x‖ ≤ bd x := by
  induction m with
  | zero =>
    intro V I _ _ _ lam hN Ω Φ bd hΩ hbd hcd hb
    have h0 : ∀ x ∈ Ω, ‖Φ x‖ ≤ bd x := fun x hx => hN _ _ (fun i => by
      have := hb i 0 (Nat.zero_le _) x hx
      rwa [norm_iteratedFDeriv_zero] at this)
    refine ⟨?_, fun q hq x hx => ?_⟩
    · have hc : ContinuousOn Φ Ω := by
        intro x₀ hx₀
        obtain ⟨r, hr, hball⟩ := loc hΩ hbd hx₀
        refine (continuousAt_of_locally_lipschitz hr (bd x₀ + 1) (fun y hy => ?_)).continuousWithinAt
        rw [dist_eq_norm, dist_eq_norm]
        refine hN _ _ (fun i => ?_)
        rw [map_sub]
        refine lip_ball (f := fun x => lam i (Φ x)) (fun z hz => ?_) (fun z hz => ?_) hy
        · exact ((hcd i).differentiableOn (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _))).differentiableAt
            (hΩ.mem_nhds (hball z hz).1)
        · rw [← norm_iteratedFDeriv_one]
          exact (hb i 1 (by omega) z (hball z hz).1).trans (hball z hz).2
      have := (contDiffOn_zero (𝕜 := ℝ)).2 hc
      simpa using this
    · obtain rfl : q = 0 := Nat.le_zero.1 hq
      rw [norm_iteratedFDeriv_zero]; exact h0 x hx
  | succ m ih =>
    intro V I _ _ _ lam hN Ω Φ bd hΩ hbd hcd hb
    obtain ⟨i₀⟩ := hN.nonempty
    have hf1 : ∀ i, ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ (fun x => lam i (Φ x))) Ω :=
      fun i => (hcd i).fderiv_of_isOpen hΩ (by push_cast; exact le_rfl)
    have hdiff : ∀ i, ∀ y ∈ Ω, DifferentiableAt ℝ (fun x => lam i (Φ x)) y := fun i y hy =>
      ((hcd i).differentiableOn (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _))).differentiableAt (hΩ.mem_nhds hy)
    have hdiff2 : ∀ i, ∀ y ∈ Ω, DifferentiableAt ℝ (fderiv ℝ (fun x => lam i (Φ x))) y := fun i y hy =>
      ((hf1 i).differentiableOn (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _))).differentiableAt (hΩ.mem_nhds hy)
    have hder : ∀ x₀ ∈ Ω, ∃ L : X →L[ℝ] V, HasFDerivAt Φ L x₀ ∧
        ∀ i, (lam i).comp L = fderiv ℝ (fun x => lam i (Φ x)) x₀ := by
      intro x₀ hx₀
      obtain ⟨r, hr, hball⟩ := loc hΩ hbd hx₀
      refine hasFDeriv_of hN hr (M := bd x₀ + 1) _ (fun i h hh => ?_)
      have hmem : ∀ y ∈ Metric.ball x₀ r, y ∈ Ω := fun y hy => (hball y hy).1
      exact taylor2 (f := fun x => lam i (Φ x)) (fun y hy => hdiff i y (hmem y hy))
        (fun y hy => hdiff2 i y (hmem y hy))
        (fun y hy => by
          rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
          exact (hb i 2 (by omega) y (hmem y hy)).trans (hball y hy).2) hh
    have hD : ∀ x ∈ Ω, HasFDerivAt Φ (fderiv ℝ Φ x) x ∧
        ∀ i, (lam i).comp (fderiv ℝ Φ x) = fderiv ℝ (fun x => lam i (Φ x)) x := by
      intro x hx
      obtain ⟨L, hL, hc⟩ := hder x hx
      rw [hL.fderiv]; exact ⟨hL, hc⟩
    let lam' : I × {h : X // ‖h‖ ≤ 1} → (X →L[ℝ] V) →L[ℝ] E :=
      fun j => (lam j.1).comp (ContinuousLinearMap.apply ℝ V j.2.1)
    have hlam' : ∀ j T, lam' j T = lam j.1 (T j.2.1) := fun j T => rfl
    have hN' : Norming lam' := by
      intro T c hc
      have c0 : 0 ≤ c := by
        have := hc (i₀, ⟨0, by simp⟩)
        rwa [hlam', map_zero, map_zero, norm_zero] at this
      refine ContinuousLinearMap.opNorm_le_of_unit_norm c0 (fun h hh => hN _ _ (fun i => ?_))
      have := hc (i, ⟨h, hh.le⟩)
      rwa [hlam'] at this
    have heq : ∀ j : I × {h : X // ‖h‖ ≤ 1}, ∀ y ∈ Ω, lam' j (fderiv ℝ Φ y) =
        ContinuousLinearMap.apply ℝ E j.2.1 (fderiv ℝ (fun x => lam j.1 (Φ x)) y) := by
      intro j y hy
      rw [hlam', ContinuousLinearMap.apply_apply, ← (hD y hy).2 j.1]; rfl
    have hcd' : ∀ j, ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun x => lam' j (fderiv ℝ Φ x)) Ω := by
      intro j
      exact ((ContinuousLinearMap.apply ℝ E j.2.1).contDiff.comp_contDiffOn (hf1 j.1)).congr
        (fun x hx => heq j x hx)
    have hb' : ∀ j, ∀ q ≤ m + 1, ∀ x ∈ Ω,
        ‖iteratedFDeriv ℝ q (fun x => lam' j (fderiv ℝ Φ x)) x‖ ≤ bd x := by
      intro j q hq x hx
      rw [iter_congr hΩ (heq j) hx q]
      calc _ ≤ ‖ContinuousLinearMap.apply ℝ E j.2.1‖ *
            ‖iteratedFDeriv ℝ q (fderiv ℝ (fun x => lam j.1 (Φ x))) x‖ :=
            norm_iter_comp _ (hf1 j.1) hΩ hx (by exact_mod_cast hq)
        _ ≤ 1 * bd x := by
            refine mul_le_mul (norm_apply_le _ j.2.2) ?_ (norm_nonneg _) zero_le_one
            rw [norm_iteratedFDeriv_fderiv]; exact hb j.1 (q + 1) (by omega) x hx
        _ = bd x := one_mul _
    obtain ⟨hcD, hbD⟩ := ih (X →L[ℝ] V) (I × {h : X // ‖h‖ ≤ 1}) lam' hN' Ω (fun x => fderiv ℝ Φ x) bd
      hΩ hbd hcd' hb'
    refine ⟨?_, fun q hq x hx => ?_⟩
    · rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
        contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
      refine ⟨fun x hx => (hD x hx).1.differentiableAt.differentiableWithinAt, fun h => ?_, hcD⟩
      simp at h
    · rcases q with _ | q
      · rw [norm_iteratedFDeriv_zero]
        exact hN _ _ (fun i => by
          have := hb i 0 (Nat.zero_le _) x hx
          rwa [norm_iteratedFDeriv_zero] at this)
      · rw [← norm_iteratedFDeriv_fderiv]
        exact hbD q (by omega) x hx
end Formalism.FourierDecayAlt.P.Ux11
