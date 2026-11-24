-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.section_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:55.92279+00:00
-- url     : https://prove2.me/submissions/97fffd37-59ec-41d4-b717-901ee66ed372

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_form_of_unitary
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_transitive
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_Hb_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_nu_unitary
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_nu_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_nu_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SettingConstruction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k : ℕ)
open scoped ContDiff
namespace Formalism.FourierDecayAlt.P.SettingConstruction
theorem _root_.solution (hk : 1 ≤ k) (a b : Fin (k + 1) → ℂ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T')
    (ha : herm (Hb k) a a = -(T : ℂ)) (hb : herm (Hb k) b b = -(T' : ℂ)) :
    ∃ μ : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ,
      (∀ i j, ContDiffOn ℝ ∞ (fun ζ => μ ζ i j) {ζ : ℂ | T * T' < Complex.normSq ζ}) ∧
      ∀ ζ : ℂ, T * T' < Complex.normSq ζ →
        (μ ζ)ᴴ * Hb k * μ ζ = Hb k ∧ herm (Hb k) (μ ζ *ᵥ b) a = ζ := by
  have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  set eL : Fin (k + 1) → ℂ := Pi.single (Fin.last k) 1 with heL
  have hLL : herm (Hb k) eL eL = -1 := by
    rw [heL, herm_single]; simp [Hb]
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hsT' : 0 < Real.sqrt T' := Real.sqrt_pos.mpr hT'
  have hva : herm (Hb k) ((Real.sqrt T : ℂ) • eL) ((Real.sqrt T : ℂ) • eL) = -(T : ℂ) := by
    rw [herm_smul_left, herm_smul_right, hLL, Complex.star_def, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, Real.mul_self_sqrt hT.le]; ring
  have hvb : herm (Hb k) ((Real.sqrt T' : ℂ) • eL) ((Real.sqrt T' : ℂ) • eL) = -(T' : ℂ) := by
    rw [herm_smul_left, herm_smul_right, hLL, Complex.star_def, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, Real.mul_self_sqrt hT'.le]; ring
  obtain ⟨ga, hga, hgau⟩ := transitive (Hb k) (Hb_herm k) _ a T hT hva ha
  obtain ⟨h, hh, hhb⟩ := transitive (Hb k) (Hb_herm k) b _ T' hT' hb hvb
  set c : ℝ := Real.sqrt T * Real.sqrt T' with hc_def
  have hc : 0 < c := mul_pos hsT hsT'
  have hcc : c * c = T * T' := by
    rw [hc_def]; nlinarith [Real.mul_self_sqrt hT.le, Real.mul_self_sqrt hT'.le]
  set w : ℂ → ℂ := fun ζ => -ζ / (c : ℂ) with hw_def
  set s : ℂ → ℂ := fun ζ => ((Real.sqrt (‖w ζ‖ ^ 2 - 1) : ℝ) : ℂ) with hs_def
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hq : ∀ ζ : ℂ, T * T' < Complex.normSq ζ → 0 < ‖w ζ‖ ^ 2 - 1 := by
    intro ζ hζ
    have e : ‖w ζ‖ ^ 2 = Complex.normSq ζ / (c * c) := by
      rw [← Complex.normSq_eq_norm_sq, hw_def]
      simp only [Complex.normSq_div, Complex.normSq_neg, Complex.normSq_ofReal]
    rw [e, hcc, sub_pos, one_lt_div (mul_pos hT hT')]
    exact hζ
  have hwC : ContDiff ℝ ∞ w := contDiff_id.neg.div_const _
  have hsC : ContDiffOn ℝ ∞ s {ζ : ℂ | T * T' < Complex.normSq ζ} := by
    intro ζ hζ
    have h1 : ContDiffAt ℝ ∞ (fun ζ => ‖w ζ‖ ^ 2 - 1) ζ :=
      (((contDiff_norm_sq ℝ).comp hwC).contDiffAt).sub contDiffAt_const
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp ζ (h1.sqrt (hq ζ hζ).ne')).contDiffWithinAt
  have hsR : ∀ ζ, star (s ζ) = s ζ := fun ζ => Complex.conj_ofReal _
  have hsw : ∀ ζ : ℂ, T * T' < Complex.normSq ζ → s ζ * s ζ = w ζ * star (w ζ) - 1 := by
    intro ζ hζ
    rw [hs_def, ← Complex.ofReal_mul, Real.mul_self_sqrt (hq ζ hζ).le, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  refine ⟨fun ζ => ga * nu k (w ζ) (s ζ) * h, ?_, ?_⟩
  · intro i j
    have hN : ∀ l m, ContDiffOn ℝ ∞ (fun ζ => nu k (w ζ) (s ζ) l m) {ζ : ℂ | T * T' < Complex.normSq ζ} := by
      intro l m
      simp only [nu_apply]
      have hw' := hwC.contDiffOn (s := {ζ : ℂ | T * T' < Complex.normSq ζ})
      have hws : ContDiffOn ℝ ∞ (fun ζ => star (w ζ)) {ζ : ℂ | T * T' < Complex.normSq ζ} :=
        (Complex.conjCLE.contDiff.comp hwC).contDiffOn
      exact ((contDiffOn_const.add ((((hws.sub contDiffOn_const).mul contDiffOn_const).add
        (hsC.mul contDiffOn_const)).mul contDiffOn_const)).add
        (((hsC.mul contDiffOn_const).add ((hw'.sub contDiffOn_const).mul contDiffOn_const)).mul contDiffOn_const))
    simp only [Matrix.mul_apply]
    refine ContDiffOn.sum (fun m _ => ?_)
    refine ContDiffOn.mul ?_ contDiffOn_const
    refine ContDiffOn.sum (fun l _ => ?_)
    exact contDiffOn_const.mul (hN l m)
  · intro ζ hζ
    beta_reduce
    have hN := nu_unitary k hk (w ζ) (s ζ) (hsR ζ) (hsw ζ hζ)
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      calc hᴴ * ((nu k (w ζ) (s ζ))ᴴ * gaᴴ) * Hb k * (ga * nu k (w ζ) (s ζ) * h)
          = hᴴ * ((nu k (w ζ) (s ζ))ᴴ * (gaᴴ * Hb k * ga) * nu k (w ζ) (s ζ)) * h := by
            simp only [Matrix.mul_assoc]
        _ = Hb k := by rw [hga, hN, hh]
    · rw [← hgau, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hhb, form_of_unitary (Hb k) hga,
        Matrix.mulVec_smul, herm_smul_left, herm_smul_right, nu_last k hk, Complex.star_def, Complex.conj_ofReal]
      have hT0 : ((Real.sqrt T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsT.ne'
      have hT0' : ((Real.sqrt T' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsT'.ne'
      simp only [hw_def, hc_def]
      push_cast
      field_simp
end Formalism.FourierDecayAlt.P.SettingConstruction
