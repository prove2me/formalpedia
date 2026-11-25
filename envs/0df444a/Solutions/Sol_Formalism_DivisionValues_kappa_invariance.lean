-- Prove2me | solution 1 for Formalism.DivisionValues.kappa_invariance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:32:02.244068+00:00
-- url     : https://prove2.me/submissions/fa250492-b80a-43fc-80b4-6e0ea1e9b6b0

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Theorems.Thm_Formalism_DivisionValues_scaleFrame_inv
import Theorems.Thm_Formalism_DivisionValues_scaleFrame_det_isUnit
import Theorems.Thm_Formalism_DivisionValues_dualFrame_scaleFrame
import Theorems.Thm_Formalism_DivisionValues_sqrt_mul_sqrt_complex
import Theorems.Thm_Formalism_DivisionValues_mean_log_sqrt
import Theorems.Thm_Formalism_DivisionValues_mean_log_sqrt_inv
import Theorems.Thm_Formalism_DivisionValues_gram_scaleFrame
import Theorems.Thm_Formalism_DivisionValues_meanLog_mul
import Theorems.Thm_Formalism_DivisionValues_opNormAt_scale_alt
import Theorems.Thm_Formalism_DivisionValues_opNormAt_pos_alt
import Theorems.Thm_Formalism_DivisionValues_lattice_fg_ne_bot
import Theorems.Thm_Formalism_DivisionValues_dual_lattice_measure
import Theorems.Thm_Formalism_HN_dual_polygon_identity
import Theorems.Thm_Formalism_HN_twist


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : KappaInvariance := by
  intro K _ _ _ _ D hD XE hXE t ht
  have hsq : ∀ v, 0 < Real.sqrt (t v) := fun v => Real.sqrt_pos.mpr (ht v)
  have hXd : ∀ v, IsUnit (Formalism.HN.dualFrame XE v).det := by
    intro v
    simp only [Formalism.HN.dualFrame]
    rw [Matrix.isUnit_nonsing_inv_det_iff, Matrix.det_transpose]
    exact hXE v

  have hdual : ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
      Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame (scaleFrame t XE))
                (Formalism.HN.dualLat R) =
        Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) +
          meanLog t := by
    intro R hR
    have hfg : R.FG := Submodule.IsLattice.fg (self := hR)
    have hspan : Submodule.span K (R : Set (Fin D → K)) = ⊤ :=
      Submodule.IsLattice.span_eq_top (self := hR)
    obtain ⟨hdfg, hdspan, -⟩ :=
      Formalism.HN.dual_polygon_identity K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) XE hXE R hfg hspan
    have hne : Formalism.HN.dualLat R ≠ ⊥ := by
      intro h
      have h2 : Submodule.span K (((⊥ : Submodule (𝓞 K) (Module.Dual K (Fin D → K)))) :
          Set (Module.Dual K (Fin D → K))) = ⊥ := by simp
      rw [h, h2] at hdspan
      have h1 : finrank K (Module.Dual K (Fin D → K)) = D := by
        simp [Subspace.dual_finrank_eq]
      have h3 := congrArg (fun U : Submodule K (Module.Dual K (Fin D → K)) => finrank K U) hdspan
      simp only [finrank_bot, finrank_top, h1] at h3
      omega
    obtain ⟨-, -, h, -⟩ := Formalism.HN.twist K (Module.Dual K (Fin D → K)) (Fin D)
      (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (fun v => Real.sqrt (t v)) hXd hsq
      (Formalism.HN.dualLat R) hdfg
    have h1 := (h hne).1
    rw [dualFrame_scaleFrame t ht XE hXE, h1, mean_log_sqrt t ht]
  refine ⟨fun v => ⟨scaleFrame_det_isUnit t ht XE hXE v, ?_⟩, ?_, fun κ hκ => meanLog_mul t κ ht hκ, ?_, ?_⟩
  · rw [scaleFrame_inv t ht XE hXE v, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Complex.star_def, Complex.conj_ofReal, sqrt_mul_sqrt_complex _ (ht v)]
  · intro d XS φ v
    simp only [detRatio, gram_scaleFrame t ht XE hXE v, Matrix.det_smul, Fintype.card_fin]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, mul_div_assoc]
  · intro R hR
    obtain ⟨hfg, hne⟩ := lattice_fg_ne_bot hD R hR
    obtain ⟨-, -, h, -⟩ := Formalism.HN.twist K (Fin D → K) (Fin D)
      (Pi.basisFun K (Fin D)) XE (fun v => (Real.sqrt (t v))⁻¹) hXE (fun v => inv_pos.mpr (hsq v))
      R hfg
    obtain ⟨h1, h2, -⟩ := h hne
    have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    refine ⟨?_, hdual R hR, ?_, ?_⟩
    · have e1 := dual_lattice_measure K D hD XE hXE R hR
      have e2 := dual_lattice_measure K D hD (scaleFrame t XE) (scaleFrame_det_isUnit t ht XE hXE) R hR
      rw [hdual R hR, e1] at e2
      field_simp at e2
      linarith
    · have : scaleFrame t XE = fun v => (((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • XE v := rfl
      rw [this, h1, mean_log_sqrt_inv t ht]; ring
    · have : scaleFrame t XE = fun v => (((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • XE v := rfl
      rw [this, h2, mean_log_sqrt_inv t ht]; ring
  · intro n XN hXN φ hφ
    have hop : ∀ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN
        (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame (scaleFrame t XE)) v φ ^ 2) =
        Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN
        (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v φ ^ 2) - Real.log (t v) := by
      intro v
      have hp := opNormAt_pos_alt XN (Formalism.HN.dualFrame XE) v (hXN v) (hXd v) φ hφ
      rw [opNormAt_scale_alt (Real.sqrt (t v)) (hsq v) XN (Formalism.HN.dualFrame XE) _ v (hXd v)
        (by rw [dualFrame_scaleFrame t ht XE hXE]) φ, mul_pow, inv_pow, Real.sq_sqrt (ht v).le,
        Real.log_mul (inv_pos.mpr (ht v)).ne' (pow_pos hp 2).ne', Real.log_inv]
      ring
    simp only [Formalism.HN.htMap, hop, Finset.sum_sub_distrib, meanLog]
    ring
end Formalism.DivisionValues
