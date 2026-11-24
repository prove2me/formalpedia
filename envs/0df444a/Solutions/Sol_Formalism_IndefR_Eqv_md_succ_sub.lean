-- Prove2me | solution 1 for Formalism.IndefR.Eqv.md_succ_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:31.077864+00:00
-- url     : https://prove2.me/submissions/ae18ebc6-5fd5-4437-98e6-a3db88cd0f1d

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_NormIterFderivApplyLe
import Theorems.Thm_Formalism_IndefR_Eqv_hasDerivAt_md_along_line

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
open Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace Formalism.IndefR.Eqv
theorem _root_.solution (φ : V → ℂ) (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (v : Fin (n + 1) → V) {h : ℝ} (hh : 0 < h) (b : V)
    (T : ℂ) (ε : ℝ) (hε : ∀ s ∈ Set.Icc (0 : ℝ) h,
      ‖md (fun y => fderiv ℝ φ y (v 0)) n (Fin.tail v) h (b + s • v 0) - T‖ ≤ ε) :
    ‖md φ (n + 1) v h b - T‖ ≤ ε := by
  set F : ℝ → ℂ := fun s => md φ n (Fin.tail v) h (b + s • v 0) - s • T
  have hF : ∀ s, HasDerivAt F (md (fun y => fderiv ℝ φ y (v 0)) n (Fin.tail v) h (b + s • v 0) - T) s := by
    intro s
    have h1 := hasDerivAt_md_along_line hφ n (Fin.tail v) h (b + s • v 0) (v 0)
    have h1' : HasDerivAt (fun r : ℝ => md φ n (Fin.tail v) h (b + s • v 0 + r • v 0))
        (md (fun y => fderiv ℝ φ y (v 0)) n (Fin.tail v) h (b + s • v 0)) (s - s) := by
      rw [sub_self]; exact h1
    have h2 := HasDerivAt.comp_sub_const s s h1'
    have h3 : HasDerivAt (fun r : ℝ => md φ n (Fin.tail v) h (b + r • v 0))
        (md (fun y => fderiv ℝ φ y (v 0)) n (Fin.tail v) h (b + s • v 0)) s := by
      refine h2.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
      show md φ n (Fin.tail v) h (b + r • v 0) = md φ n (Fin.tail v) h (b + s • v 0 + (r - s) • v 0)
      rw [add_assoc, ← add_smul, add_sub_cancel]
    have h4 := h3.sub ((hasDerivAt_id s).smul_const T)
    rw [one_smul] at h4
    exact h4
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := F) (a := 0) (b := h) (C := ε)
    (fun s _ => (hF s).hasDerivWithinAt) (fun s hs => hε s ⟨hs.1, hs.2.le⟩)
  have hb := hmv h ⟨hh.le, le_rfl⟩
  have hFe : F h - F 0 = md φ n (Fin.tail v) h (b + h • v 0) - h • T - md φ n (Fin.tail v) h b := by
    simp only [F, zero_smul, add_zero, sub_zero]
  rw [hFe, sub_zero] at hb
  have e : md φ (n + 1) v h b - T =
      ((h : ℂ))⁻¹ * (md φ n (Fin.tail v) h (b + h • v 0) - h • T - md φ n (Fin.tail v) h b) := by
    simp only [md]
    rw [Complex.real_smul]
    have : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    field_simp
    ring
  rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hh.le]
  calc h⁻¹ * ‖md φ n (Fin.tail v) h (b + h • v 0) - h • T - md φ n (Fin.tail v) h b‖
      ≤ h⁻¹ * (ε * h) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hh.le)
    _ = ε := by field_simp
end Formalism.IndefR.Eqv
