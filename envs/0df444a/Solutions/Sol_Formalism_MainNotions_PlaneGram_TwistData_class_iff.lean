-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.class_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:07:34.142869+00:00
-- url     : https://prove2.me/submissions/166d039a-2dbe-433a-8c38-3f9727ea0601

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_eIn_apply_mb
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_eIn_apply_mw
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_eIn_apply_mlab
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_eIn_apply_mtp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (p : ℕ) {ζ : D.EM} (hζ : D.LabLowE p ζ) (α : D.EA) :
    (D.InClass p (D.labF ζ) α ∧ D.liftE p α = eIn D.outP ζ) ↔ α = D.collapseExponent p ζ := by
  constructor
  · rintro ⟨hcl, hlift⟩
    ext ⟨i, a⟩
    rcases i with b | t
    · have h2 := congrArg (fun f => f (D.mb b, a)) hlift
      beta_reduce at h2
      rw [eIn_apply_mb] at h2
      have h1 : D.liftE p α (D.mb b, a) = α (Sum.inl b, a) := by simp [liftE, mb]
      rw [h1] at h2
      rw [h2]
      simp [collapseExponent, mb]
    · have h2 := congrArg (fun f => f (D.mw t, a)) hlift
      beta_reduce at h2
      rw [eIn_apply_mw] at h2
      have h1 : D.liftE p α (D.mw t, a) = α (Sum.inr t, a) / D.P p t := by simp [liftE, mw]
      rw [h1] at h2
      have h3 : α (Sum.inr t, a) % D.P p t = ζ (D.mlab t, a) := hcl t a
      have h4 : D.collapseExponent p ζ (Sum.inr t, a) = ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a) := by
        simp [collapseExponent, mlab, mw]
      rw [h4, ← Nat.mod_add_div (α (Sum.inr t, a)) (D.P p t), h3, h2]
  · rintro rfl
    refine ⟨fun t a => ?_, ?_⟩
    · have hP : 0 < D.P p t := (Nat.zero_le _).trans_lt (hζ t a)
      show D.collapseExponent p ζ (Sum.inr t, a) % D.P p t = ζ (D.mlab t, a)
      have h4 : D.collapseExponent p ζ (Sum.inr t, a) = ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a) := by
        simp [collapseExponent, mlab, mw]
      rw [h4, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hζ t a)]
    · ext ⟨i, a⟩
      rcases i with b | t | t | t
      · change _ = eIn D.outP ζ (D.mb b, a)
        rw [eIn_apply_mb]
        simp [liftE, collapseExponent, mb]
      · change _ = eIn D.outP ζ (D.mlab t, a)
        rw [eIn_apply_mlab]
        simp [liftE]
      · change _ = eIn D.outP ζ (D.mw t, a)
        rw [eIn_apply_mw]
        have hP : 0 < D.P p t := (Nat.zero_le _).trans_lt (hζ t a)
        have h4 : D.collapseExponent p ζ (Sum.inr t, a) = ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a) := by
          simp [collapseExponent, mlab, mw]
        have h1 : D.liftE p (D.collapseExponent p ζ) (Sum.inr (Sum.inr (Sum.inl t)), a) =
            D.collapseExponent p ζ (Sum.inr t, a) / D.P p t := by simp [liftE]
        rw [h1, h4, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt (hζ t a), zero_add]
      · change _ = eIn D.outP ζ (D.mtp t, a)
        rw [eIn_apply_mtp]
        simp [liftE]
end Formalism.MainNotions.PlaneGram.TwistData
