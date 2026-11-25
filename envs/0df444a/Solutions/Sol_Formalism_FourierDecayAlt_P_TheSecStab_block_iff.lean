-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TheSecStab.block_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:58:44.118893+00:00
-- url     : https://prove2.me/submissions/9e116c54-384a-43e3-b04c-df260eb14b2c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSectionStab
import Theorems.Thm_Formalism_FourierDecayAlt_P_TheSecStab_commute_nu
import Theorems.Thm_Formalism_FourierDecayAlt_P_TheSecStab_nu_last_vec
import Theorems.Thm_Formalism_FourierDecayAlt_P_TheSecStab_nu_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_TheSecStab_sZ_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_TheSec_gA_spec
import Theorems.Thm_Formalism_FourierDecayAlt_P_TheSec_gB_spec
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UHb_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UHb_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TheSecStab
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec
variable {k : ℕ}
namespace Formalism.FourierDecayAlt.P.TheSecStab
theorem _root_.solution (hk : 1 ≤ k) {a b : Fin (k + 1) → ℂ} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (ha : herm (Hb k) a a = -(T : ℂ)) (hb : herm (Hb k) b b = -(T' : ℂ)) {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ)
    {μ μ' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μ ∈ UH (Hb k)) (hμ' : μ' ∈ UH (Hb k))
    (hμa : μ *ᵥ a = a) (hμb : μ' *ᵥ b = b) :
    μ * theSecB k a b T T' ζ * μ' = theSecB k a b T T' ζ ↔
      ((gA k a T)⁻¹ * μ * gA k a T) *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
        gB k b T' * μ' * (gB k b T')⁻¹ = ((gA k a T)⁻¹ * μ * gA k a T)⁻¹ := by
  obtain ⟨hga1, hga2⟩ := gA_spec k hT ha
  obtain ⟨hgb1, hgb2⟩ := gB_spec k hT' hb
  set gA' := gA k a T with hgA'
  set gB' := gB k b T' with hgB'
  have hgAu : gA' ∈ UH (Hb k) := hga1
  have hgBu : gB' ∈ UH (Hb k) := hgb1
  have uA := (UHb_inv hgAu).1
  have uB := (UHb_inv hgBu).1
  set ν := nu k (wZ T T' ζ) (sZ T T' ζ) with hνdef
  have hνu : ν ∈ UH (Hb k) := nu_mem hk hT hT' hζ
  have uν := (UHb_inv hνu).1
  have hs := sZ_ne hT hT' hζ
  set e := (Pi.single (Fin.last k) 1 : Fin (k + 1) → ℂ) with hedef
  set e0 := (Pi.single 0 1 : Fin (k + 1) → ℂ) with he0def
  set ĥ := gA'⁻¹ * μ * gA' with hĥdef
  set ĥ' := gB' * μ' * gB'⁻¹ with hĥ'def
  have hĥu : ĥ ∈ UH (Hb k) := UHb_mul (UHb_mul (UHb_inv hgAu).2 hμ) hgAu
  have uĥ := (UHb_inv hĥu).1
  have hsT : ((Real.sqrt T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hT).ne'
  have hsT' : ((Real.sqrt T' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hT').ne'

  have hAinv : gA'⁻¹ *ᵥ a = ((Real.sqrt T : ℝ) : ℂ) • e := by
    rw [← hga2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uA, Matrix.one_mulVec]
  have hAe : gA' *ᵥ e = ((Real.sqrt T : ℝ) : ℂ)⁻¹ • a := by
    rw [← hga2, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hsT, one_smul]
  have hĥe : ĥ *ᵥ e = e := by
    rw [hĥdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAe, Matrix.mulVec_smul, hμa, Matrix.mulVec_smul,
      hAinv, smul_smul, inv_mul_cancel₀ hsT, one_smul]
  have hBinv : gB'⁻¹ *ᵥ e = ((Real.sqrt T' : ℝ) : ℂ)⁻¹ • b := by
    have : gB'⁻¹ *ᵥ (((Real.sqrt T' : ℝ) : ℂ) • e) = b := by
      rw [← hgb2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uB, Matrix.one_mulVec]
    rw [Matrix.mulVec_smul] at this
    rw [← this, smul_smul, inv_mul_cancel₀ hsT', one_smul]
  have hĥ'e : ĥ' *ᵥ e = e := by
    rw [hĥ'def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBinv, Matrix.mulVec_smul, hμb, Matrix.mulVec_smul,
      hgb2, smul_smul, inv_mul_cancel₀ hsT', one_smul]

  have hequiv : μ * theSecB k a b T T' ζ * μ' = theSecB k a b T T' ζ ↔ ĥ * ν * ĥ' = ν := by
    have hS : theSecB k a b T T' ζ = gA' * ν * gB' := rfl
    rw [hS]
    constructor
    · intro h
      calc ĥ * ν * ĥ' = gA'⁻¹ * (μ * (gA' * ν * gB') * μ') * gB'⁻¹ := by
            simp only [hĥdef, hĥ'def, Matrix.mul_assoc]
        _ = gA'⁻¹ * (gA' * ν * gB') * gB'⁻¹ := by rw [h]
        _ = ν := by
            simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ uA, Matrix.mul_nonsing_inv _ uB,
              Matrix.mul_one]
    · intro h
      calc μ * (gA' * ν * gB') * μ' = gA' * (ĥ * ν * ĥ') * gB' := by
            simp only [hĥdef, hĥ'def, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ uA,
              Matrix.nonsing_inv_mul _ uB, Matrix.mul_one]
        _ = gA' * ν * gB' := by rw [h]
  rw [hequiv]
  constructor
  · intro h

    have h1 : ĥ *ᵥ (ν *ᵥ e) = ν *ᵥ e := by
      have := congrArg (fun M => M *ᵥ e) h
      simp only [← Matrix.mulVec_mulVec, hĥ'e] at this
      exact this
    rw [hνdef, nu_last_vec hk, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hĥe] at h1
    have h0 : ĥ *ᵥ e0 = e0 := by
      have h2 : sZ T T' ζ • (ĥ *ᵥ e0) = sZ T T' ζ • e0 := add_right_cancel h1
      exact smul_right_injective _ hs h2
    refine ⟨h0, ?_⟩
    have hc := commute_nu hĥu h0 hĥe (wZ T T' ζ) (sZ T T' ζ)
    have h3 : ν * (ĥ * ĥ') = ν * 1 := by
      rw [Matrix.mul_one, ← Matrix.mul_assoc, ← hc, h]
    have h4 : ĥ * ĥ' = 1 := by
      have := congrArg (fun M => ν⁻¹ * M) h3
      simp only [Matrix.nonsing_inv_mul_cancel_left _ _ uν] at this
      exact this
    exact (Matrix.inv_eq_right_inv h4).symm
  · rintro ⟨h0, h1⟩
    have hc := commute_nu hĥu h0 hĥe (wZ T T' ζ) (sZ T T' ζ)
    rw [h1, hc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ uĥ, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.TheSecStab
