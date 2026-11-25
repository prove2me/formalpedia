-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.psiAPLowerOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:00:42.628417+00:00
-- url     : https://prove2.me/submissions/850830dc-974a-4614-8234-45e238772e3d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcTerm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffPsi
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_charSum_lowerOf
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_excSum_leOf
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_excOne
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_excTerm
import Theorems.Thm_Formalism_ZeroFreeDirichlet_psiChiBound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ZeroFreeDirichlet
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution (A : ℕ) (hA : ExcBoundAt A) : ∃ c c₀ C : ℝ, 0 < c ∧ 0 < c₀ ∧ 0 ≤ C ∧
    ∀ (m a : ℕ) (x : ℝ), 1 ≤ m → Nat.Coprime a m → 0 < x → 4 ≤ Real.log x →
      (m : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log x)) →
      c₀ * x / (m : ℝ) ^ (A + 1) - C * x * Real.exp (-c * Real.sqrt (Real.log x)) ≤ psiAP m a x := by
  obtain ⟨c₁, hc₁, hc₁', hex⟩ := excOne
  obtain ⟨c, C, hc, hPC⟩ := psiChiBound c₁ hc₁ hc₁'
  obtain ⟨cE, hcE, hEB⟩ := hA
  refine ⟨c, min 1 cE / 2, max C 0, hc, by positivity, le_max_right _ _, ?_⟩
  intro m a x hm ha hx hL hmx
  have : NeZero m := ⟨by omega⟩
  obtain ⟨B, hBexc, hBuniq, hBprop⟩ := hex m
  set e := Real.exp (-c * Real.sqrt (Real.log x)) with he
  set K := max C 0 * x * e with hKdef
  have hx2 : 2 ≤ x := by
    have h1 : (4 : ℝ) + 1 ≤ Real.exp 4 := Real.add_one_le_exp 4
    have h2 : Real.exp 4 ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hL
    rw [Real.exp_log hx] at h2
    linarith
  have hK : ∀ χ : DirichletCharacter ℂ m, ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0) +
      ∑ β ∈ B χ, (x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ K := by
    intro χ
    refine (hPC m χ (B χ) x (hBexc χ) hx2 hmx).trans ?_
    have : 0 ≤ x * e := by positivity
    rw [hKdef, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
  have hB0 : ∀ χ, ∀ β ∈ B χ, 0 ≤ β := fun χ β hβ => by
    have := (hBprop χ β hβ).2.2.1
    linarith
  have hlow := charSum_lowerOf m a ha x K hx.le B hB0 hK
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmA1 : (1 : ℝ) ≤ (m : ℝ) ^ A := one_le_pow₀ hm1
  have hminv : 0 < ((m : ℝ) ^ A)⁻¹ := by positivity
  have hminv1 : ((m : ℝ) ^ A)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hmA1
  set d := min 1 cE * ((m : ℝ) ^ A)⁻¹ / 2 with hd
  have hmin1 : min 1 cE ≤ 1 := min_le_left _ _
  have hminE : min 1 cE ≤ cE := min_le_right _ _
  have hmin0 : 0 < min 1 cE := lt_min one_pos hcE
  have hd1 : d ≤ 1 / 2 := by
    have : min 1 cE * ((m : ℝ) ^ A)⁻¹ ≤ 1 * 1 := mul_le_mul hmin1 hminv1 hminv.le zero_le_one
    rw [hd]; linarith
  have hd0 : 0 < d := by positivity
  have hS : ∑ χ : DirichletCharacter ℂ m, ∑ β ∈ B χ, x ^ β / β ≤ x * (1 - d) := by
    refine excSum_leOf B (fun β => x ^ β / β) (x * (1 - d)) (by nlinarith) (fun χ => (hBexc χ).1)
      hBuniq ?_
    intro χ β hβ
    obtain ⟨hsq, hne, hhalf, hz⟩ := hBprop χ β hβ
    have hb := hEB m χ β hsq hne hz
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast] at hb
    have hce : cE * ((m : ℝ) ^ A)⁻¹ ≥ min 1 cE * ((m : ℝ) ^ A)⁻¹ :=
      mul_le_mul_of_nonneg_right hminE hminv.le
    have hβ1 : β ≤ 1 := by nlinarith
    have h1 := excTerm x β hx hL hhalf hβ1
    refine h1.trans ?_
    apply mul_le_mul_of_nonneg_left _ hx.le
    rw [hd]
    linarith
  have hφpos : (0 : ℝ) < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφle : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hmain : x * d ≤ (m.totient : ℝ) * (psiAP m a x + K) := by
    rw [mul_add]
    nlinarith
  have hnn : 0 ≤ psiAP m a x + K := by
    have : (m.totient : ℝ) * 0 ≤ (m.totient : ℝ) * (psiAP m a x + K) := by
      rw [mul_zero]; nlinarith [mul_pos hx hd0]
    exact le_of_mul_le_mul_left this hφpos
  have hmain2 : x * d ≤ (m : ℝ) * (psiAP m a x + K) :=
    hmain.trans (mul_le_mul_of_nonneg_right hφle hnn)
  have hm0 : (0 : ℝ) < m := by linarith
  have hgoal : min 1 cE / 2 * x / (m : ℝ) ^ (A + 1) ≤ psiAP m a x + K := by
    rw [div_le_iff₀ (by positivity)]
    have hxd : min 1 cE / 2 * x = (m : ℝ) ^ A * (x * d) := by
      rw [hd]; field_simp
    rw [hxd]
    have := mul_le_mul_of_nonneg_left hmain2 (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ A)
    calc (m : ℝ) ^ A * (x * d) ≤ (m : ℝ) ^ A * ((m : ℝ) * (psiAP m a x + K)) := this
      _ = (psiAP m a x + K) * (m : ℝ) ^ (A + 1) := by ring
  linarith
end Formalism.HermitianLattices.Ext.SupplyAP
