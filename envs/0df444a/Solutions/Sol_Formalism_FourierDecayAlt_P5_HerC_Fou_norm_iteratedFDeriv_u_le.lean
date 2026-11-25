-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.HerC.Fou.norm_iteratedFDeriv_u_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:57:55.96368+00:00
-- url     : https://prove2.me/submissions/5b287058-f001-4ed0-9364-d878c21b71f6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralIteratedFDerivEqZero
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormIteratedFDerivWithinInvOneLe
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_norm_iteratedFDeriv_inner_self_le
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_norm_iteratedFDerivWithin_inv_one_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped Nat
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerC Formalism.FourierDecayAlt.P5.HerC.Fou
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
namespace Formalism.FourierDecayAlt.P5.HerC.Fou
theorem _root_.solution (k : ℕ) (x₀ : V) :
    ‖iteratedFDeriv ℝ k (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) x₀‖ ≤ (k ! * k ! * 4 ^ k) * (1 + ‖x₀‖ ^ 2)⁻¹ := by
  set q₀ : ℝ := 1 + ‖x₀‖ ^ 2 with hq₀
  have hq₀pos : 0 < q₀ := by positivity
  set f : V → ℝ := fun y => q₀⁻¹ * (1 + inner ℝ y y) with hf
  have hfpos : ∀ y, 0 < f y := fun y => by
    simp only [hf, real_inner_self_eq_norm_sq]; positivity
  have hfc : ContDiff ℝ k f :=
    contDiff_const.mul (contDiff_const.add (contDiff_id.inner ℝ contDiff_id))
  have hfx : f x₀ = 1 := by
    simp only [hf, real_inner_self_eq_norm_sq]
    rw [← hq₀]
    exact inv_mul_cancel₀ hq₀pos.ne'
  have hu : (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) = q₀⁻¹ • ((fun t : ℝ => t⁻¹) ∘ f) := by
    funext y
    simp only [hf, Pi.smul_apply, Function.comp, real_inner_self_eq_norm_sq, smul_eq_mul]
    field_simp
  have hgc : ContDiff ℝ k ((fun t : ℝ => t⁻¹) ∘ f) :=
    hfc.inv fun y => (hfpos y).ne'
  rw [hu, iteratedFDeriv_const_smul_apply (hgc.contDiffAt), norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hq₀pos), mul_comm]
  gcongr
  have hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i f x₀‖ ≤ 4 ^ i := by
    intro i hi _
    have e : f = (fun _ : V => q₀⁻¹) + q₀⁻¹ • (fun y : V => inner ℝ y y) := by
      funext y; simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hin : ContDiff ℝ i (fun y : V => inner ℝ y y) := contDiff_id.inner ℝ contDiff_id
    have hc2 : ContDiffAt ℝ i (q₀⁻¹ • (fun y : V => inner ℝ y y)) x₀ :=
      ((hin.const_smul q₀⁻¹ : ContDiff ℝ i (q₀⁻¹ • (fun y : V => inner ℝ y y)))).contDiffAt
    have hc1 : ContDiffAt ℝ i (fun _ : V => q₀⁻¹) x₀ := contDiffAt_const
    rw [e, iteratedFDeriv_add_apply hc1 hc2,
      iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, zero_add,
      iteratedFDeriv_const_smul_apply hin.contDiffAt, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.2 hq₀pos)]
    have h1 := norm_iteratedFDeriv_inner_self_le i x₀
    have h2 : (1 + ‖x₀‖) ^ 2 ≤ 2 * q₀ := by
      rw [hq₀]; nlinarith [sq_nonneg (‖x₀‖ - 1)]
    have h3 : (2 : ℝ) ^ i * 2 ≤ 4 ^ i := by
      have : (4 : ℝ) ^ i = 2 ^ i * 2 ^ i := by rw [← mul_pow]; norm_num
      rw [this]
      gcongr
      exact le_self_pow₀ (by norm_num) (by omega)
    calc q₀⁻¹ * ‖iteratedFDeriv ℝ i (fun y : V => inner ℝ y y) x₀‖ ≤ q₀⁻¹ * (2 ^ i * (2 * q₀)) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = 2 ^ i * 2 := by field_simp
      _ ≤ 4 ^ i := h3
  have hC : ∀ i, i ≤ k → ‖iteratedFDerivWithin ℝ i (fun t : ℝ => t⁻¹) (Ioi 0) (f x₀)‖ ≤ k ! := by
    intro i hi
    rw [hfx]
    exact (norm_iteratedFDerivWithin_inv_one_le i).trans (by exact_mod_cast Nat.factorial_le hi)
  have hmain := norm_iteratedFDeriv_comp_le' (N := (k : ℕ∞)) (t := Ioi (0 : ℝ))
    (by rintro _ ⟨y, rfl⟩; exact hfpos y) (uniqueDiffOn_Ioi 0)
    (ContDiffOn.mono (contDiffOn_inv (𝕜 := ℝ)) (fun t (ht : t ∈ Ioi (0 : ℝ)) => (ne_of_gt ht : t ≠ 0))) hfc le_rfl x₀ hC hD
  calc ‖iteratedFDeriv ℝ k ((fun t : ℝ => t⁻¹) ∘ f) x₀‖ ≤ k ! * k ! * 4 ^ k := hmain
    _ = k ! * k ! * 4 ^ k := rfl
end Formalism.FourierDecayAlt.P5.HerC.Fou
