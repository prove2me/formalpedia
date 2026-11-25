-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.deuring_heilbronn_inequality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:17:43.913711+00:00
-- url     : https://prove2.me/submissions/5f05a11b-593d-431b-8a9a-815601959e5b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqFA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqF
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhAssemble
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhFamPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhFam_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhFam_re
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhFinalArith
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhFlat
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhFlat_sum
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhLogOne
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhMemIte
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhPair
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhReBound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhfEraseSum
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhfNormArith
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhfPoles
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhfReNonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_logMulAbsAddTwoLeTwoMulLog


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution : DHIneqFOf := by
  intro hPos hLoc hDom
  obtain ⟨CL, hCL, hL⟩ := hLoc
  refine ⟨8 * CL + 1, by positivity, ?_⟩
  intro M _ χ₁ χ β₁ T η ρ hM hT hχ₁2 hχ₁1 hβ hβ1 hβ2 hρ hρre hρim hne hη hη2
  have hlog0 : Real.log ((M : ℝ) * (|(0 : ℝ)| + 2)) ≤ 2 * Real.log ((M : ℝ) * T) :=
    logMulAbsAddTwoLeTwoMulLog M T 0 hM hT (by rw [abs_zero]; linarith)
  have hlogγ := logMulAbsAddTwoLeTwoMulLog M T ρ.im hM hT hρim
  have hlog1 := dhLogOne M T hM hT
  obtain ⟨Z1, m1, hZ1, hm1, hr1, hN1, hE1⟩ := hL M 1 0 hM
  obtain ⟨Z2, m2, hZ2, hm2, hr2, hN2, hE2⟩ := hL M χ₁ 0 hM
  obtain ⟨Z3, m3, hZ3, hm3, hr3, hN3, hE3⟩ := hL M χ ρ.im hM
  obtain ⟨Z4, m4, hZ4, hm4, hr4, hN4, hE4⟩ := hL M (χ * χ₁) ρ.im hM
  obtain ⟨s₀, hs₀⟩ : ∃ s : ℂ, s = ((1 + η : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨s₁, hs₁⟩ : ∃ s : ℂ, s = ((1 + η : ℝ) : ℂ) + ρ.im * I := ⟨_, rfl⟩
  have hs₀' : s₀ = ((1 + η : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I := by rw [hs₀]; simp
  have hs₀re : s₀.re = 1 + η := by rw [hs₀]; simp
  have hs₁re : s₁.re = 1 + η := by rw [hs₁]; simp
  have hd₀ : ‖s₀ - ((26 / 25 : ℂ) + ((0 : ℝ) : ℂ) * I)‖ ≤ 1 / 25 := by
    rw [hs₀, show ((1 + η : ℝ) : ℂ) - ((26 / 25 : ℂ) + ((0 : ℝ) : ℂ) * I) = ((η - 1 / 25 : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hd₁ : ‖s₁ - ((26 / 25 : ℂ) + (ρ.im : ℂ) * I)‖ ≤ 1 / 25 := by
    rw [hs₁, show ((1 + η : ℝ) : ℂ) + ρ.im * I - ((26 / 25 : ℂ) + (ρ.im : ℂ) * I) = ((η - 1 / 25 : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h1s₀ : 1 < s₀.re := by rw [hs₀re]; linarith
  have h1s₁ : 1 < s₁.re := by rw [hs₁re]; linarith
  have hβZ : (β₁ : ℂ) ∈ Z2 := by
    refine (hZ2 β₁).2 ⟨?_, Or.inl hχ₁1, hβ⟩
    rw [show (β₁ : ℂ) - ((26 / 25 : ℂ) + ((0 : ℝ) : ℂ) * I) = ((β₁ - 26 / 25 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hρZ : ρ ∈ Z3 := by
    refine (hZ3 ρ).2 ⟨?_, hρ⟩
    rw [show ρ - ((26 / 25 : ℂ) + (ρ.im : ℂ) * I) = ((ρ.re - 26 / 25 : ℝ) : ℂ) by
        apply Complex.ext <;> simp,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    have hρ1 : ρ.re < 1 := by
      by_contra h
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hρ.1 (le_of_not_gt h) hρ.2
    constructor <;> linarith
  have hb2 : s₀ - β₁ ∈ dhFam Z2 m2 s₀ := dhFam_mem _ _ _ _ hβZ (hm2 _ hβZ)
  have hb3 : χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 → s₁ - β₁ ∈ dhFam Z3 m3 s₁ :=
    fun h => dhFam_mem _ _ _ _ h.2 (hm3 _ h.2)
  have hb4 : χ = 1 ∧ (β₁ : ℂ) ∈ Z4 → s₁ - β₁ ∈ dhFam Z4 m4 s₁ :=
    fun h => dhFam_mem _ _ _ _ h.2 (hm4 _ h.2)
  have hl0 : 0 ≤ Real.log ((M : ℝ) * T) := by linarith

  have big : ∀ k : ℕ, (((dhFam Z1 m1 s₀ + (dhFam Z2 m2 s₀).erase (s₀ - β₁)
      + (if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then (dhFam Z3 m3 s₁).erase (s₁ - β₁) else dhFam Z3 m3 s₁)
      + (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then (dhFam Z4 m4 s₁).erase (s₁ - β₁) else dhFam Z4 m4 s₁)).map
        (fun x : ℂ => 1 / x ^ (k + 1))).sum).re ≤
      2 * (((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2)) + (8 * (CL * Real.log ((M : ℝ) * T) * 25 ^ (k + 1))
        + 8 * 0 + Real.log ((M : ℝ) * T) * 25 ^ (k + 1)) := by
    intro k
    have key := dhAssemble (dhFam Z1 m1 s₀) (dhFam Z2 m2 s₀) (dhFam Z3 m3 s₁) (dhFam Z4 m4 s₁)
      (s₀ - β₁) (s₁ - β₁) (s₁ - β₁) _ _ hb2 hb3 hb4 (fun x : ℂ => 1 / x ^ (k + 1))
    rw [dhFamPow, dhFamPow, dhFamPow, dhFamPow] at key
    rw [key]
    have l1 := dhReBound _ _ _ _ (hE1 k s₀ h1s₀ hd₀)
    have l2 := dhReBound _ _ _ _ (hE2 k s₀ h1s₀ hd₀)
    have l3 := dhReBound _ _ _ _ (hE3 k s₁ h1s₁ hd₁)
    have l4 := dhReBound _ _ _ _ (hE4 k s₁ h1s₁ hd₁)
    rw [if_pos rfl] at l1
    rw [if_neg hχ₁1, Complex.zero_re] at l2
    have hp := hPos M χ₁ χ ρ.im (1 + η) k hχ₁2 (by linarith)
    rw [← hs₁, ← hs₀] at hp
    have hA : 0 ≤ ((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) s₀).re
        + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD χ₁) s₀).re
        + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD χ) s₁).re
        + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD (χ * χ₁)) s₁).re := by
      have e : ∀ a b c d : ℂ, ((-1 : ℂ) ^ k / (k.factorial : ℂ) * a).re
          + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * b).re
          + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * c).re + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * d).re
          = ((k.factorial : ℝ))⁻¹ * ((-1 : ℂ) ^ k * (a + b + c + d)).re := by
        intro a b c d
        rw [← Complex.re_ofReal_mul]
        simp only [← Complex.add_re]
        congr 1
        push_cast
        ring
      rw [e]
      exact mul_nonneg (by positivity) hp
    have hpair := dhPair η 0 β₁ hη hβ2 k s₀ hs₀'
    have hshift : ((if χ = 1 then 1 / (s₁ - 1) ^ (k + 1) else 0)
        + (if χ * χ₁ = 1 then 1 / (s₁ - 1) ^ (k + 1) else 0)
        - (if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then 1 / (s₁ - β₁) ^ (k + 1) else 0)
        - (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then 1 / (s₁ - β₁) ^ (k + 1) else 0)).re
        ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
      refine le_trans (Complex.re_le_norm _) ?_
      refine dhfPoles χ₁ χ hχ₁2 hχ₁1 η ρ.im β₁ hη hβ1 hβ2 k s₁ hs₁ (χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3) (χ = 1 ∧ (β₁ : ℂ) ∈ Z4) ?_ ?_
        (fun h => h.1) (fun h => h.1)
      · intro h2 hc hd
        apply hc
        refine ⟨h2, (hZ3 β₁).2 ⟨hd, ?_⟩⟩
        rw [h2]
        exact ⟨Or.inl hχ₁1, hβ⟩
      · intro h1 hc hd
        apply hc
        refine ⟨h1, (hZ4 β₁).2 ⟨hd, ?_⟩⟩
        rw [h1, one_mul]
        exact ⟨Or.inl hχ₁1, hβ⟩
    simp only [Complex.add_re, Complex.sub_re] at hpair hshift ⊢
    have ee0 : CL * Real.log ((M : ℝ) * (|(0 : ℝ)| + 2)) * 25 ^ k ≤ CL * (2 * Real.log ((M : ℝ) * T)) * 25 ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog0 hCL.le) (by positivity)
    have eeγ : CL * Real.log ((M : ℝ) * (|ρ.im| + 2)) * 25 ^ k ≤ CL * (2 * Real.log ((M : ℝ) * T)) * 25 ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogγ hCL.le) (by positivity)
    have h25k : (25 : ℝ) ^ k ≤ 25 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have eek := mul_le_mul_of_nonneg_left h25k (mul_nonneg hCL.le hl0)
    have h8 : (8 : ℝ) ^ (k + 1) ≤ 25 ^ (k + 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have h25 : (25 : ℝ) ^ (k + 1) ≤ Real.log ((M : ℝ) * T) * 25 ^ (k + 1) :=
      le_mul_of_one_le_left (by positivity) hlog1
    have t1 := add_le_add (add_le_add (add_le_add l1 l2) l3) l4
    have t2 : (8 : ℝ) ^ (k + 1) ≤ Real.log ((M : ℝ) * T) * 25 ^ (k + 1) := le_trans h8 h25
    have t3 : CL * (2 * Real.log ((M : ℝ) * T)) * 25 ^ k ≤ 2 * (CL * Real.log ((M : ℝ) * T) * 25 ^ (k + 1)) := by
      linarith
    exact dhFinalArith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t1 hA hpair hshift ee0 eeγ t3 t2 le_rfl

  obtain ⟨N, w, hw⟩ := dhFlat
    ((if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then (dhFam Z3 m3 s₁).erase (s₁ - β₁) else dhFam Z3 m3 s₁)
    + (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then (dhFam Z4 m4 s₁).erase (s₁ - β₁) else dhFam Z4 m4 s₁))
  refine ⟨N, w, ?_, ?_, ?_, ?_⟩
  ·
    intro i
    have hx : w i ∈ Finset.univ.val.map w := Multiset.mem_map_of_mem w (Finset.mem_univ i)
    rw [hw] at hx
    rcases Multiset.mem_add.1 hx with h | h
    · exact dhFam_re _ _ _ _ _ hr3 hs₁re (dhMemIte _ _ _ _ h)
    · exact dhFam_re _ _ _ _ _ hr4 hs₁re (dhMemIte _ _ _ _ h)
  ·
    have hx₀ : s₁ - ρ = ((η + (1 - ρ.re) : ℝ) : ℂ) := by
      rw [hs₁]; apply Complex.ext <;> simp; ring
    have hm : s₁ - ρ ∈ dhFam Z3 m3 s₁ := dhFam_mem _ _ _ _ hρZ (hm3 _ hρZ)
    have hm' : s₁ - ρ ∈ (if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then (dhFam Z3 m3 s₁).erase (s₁ - β₁)
        else dhFam Z3 m3 s₁) := by
      split_ifs with hc
      · rw [Multiset.mem_erase_of_ne]
        · exact hm
        · intro h'
          apply hne
          rw [hc.1, sub_right_inj.1 h']
      · exact hm
    have hS : s₁ - ρ ∈ Finset.univ.val.map w := by
      rw [hw]
      exact Multiset.mem_add.2 (Or.inl hm')
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hS
    exact ⟨i, hi.trans hx₀⟩
  ·
    have e1 : ∑ i, 1 / w i = (((if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then (dhFam Z3 m3 s₁).erase (s₁ - β₁)
        else dhFam Z3 m3 s₁) + (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then (dhFam Z4 m4 s₁).erase (s₁ - β₁)
        else dhFam Z4 m4 s₁)).map (fun x : ℂ => 1 / x)).sum := dhFlat_sum w _ hw (fun x : ℂ => 1 / x)
    rw [e1]
    have hb := big 0
    simp only [zero_add, pow_one, Nat.cast_zero] at hb
    rw [Multiset.map_add, Multiset.map_add, Multiset.map_add, Multiset.sum_add, Multiset.sum_add,
      Multiset.sum_add, Complex.add_re, Complex.add_re, Complex.add_re] at hb
    rw [Multiset.map_add, Multiset.sum_add, Complex.add_re]
    have n1 := dhfReNonneg (dhFam Z1 m1 s₀) (fun x hx => by
      have := dhFam_re _ _ _ _ _ hr1 hs₀re hx; linarith)
    have n2 := dhfReNonneg ((dhFam Z2 m2 s₀).erase (s₀ - β₁)) (fun x hx => by
      have := dhFam_re _ _ _ _ _ hr2 hs₀re (Multiset.mem_of_mem_erase hx); linarith)
    have hl := mul_nonneg hCL.le hl0
    have q1 : 2 * (1 * (1 - β₁) / η ^ 2) = 2 * (1 - β₁) / η ^ 2 := by ring
    have q2 : (8 * CL + 1) * Real.log ((M : ℝ) * T) * 25 =
        8 * (CL * Real.log ((M : ℝ) * T) * 25) + 8 * 0 + Real.log ((M : ℝ) * T) * 25 := by ring
    rw [q2, ← q1]
    linarith
  ·
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have e1 : ∑ i, 1 / (w i) ^ (k + 1) = (((if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then (dhFam Z3 m3 s₁).erase (s₁ - β₁)
        else dhFam Z3 m3 s₁) + (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then (dhFam Z4 m4 s₁).erase (s₁ - β₁)
        else dhFam Z4 m4 s₁)).map (fun x : ℂ => 1 / x ^ (k + 1))).sum :=
      dhFlat_sum w _ hw (fun x : ℂ => 1 / x ^ (k + 1))
    rw [e1, Multiset.map_add, Multiset.sum_add, dhfEraseSum Z3 m3 s₁ (s₁ - β₁) _ hb3 k,
      dhfEraseSum Z4 m4 s₁ (s₁ - β₁) _ hb4 k]
    have hdom := hDom M χ₁ χ ρ.im (1 + η) k hχ₁2 (by linarith)
    rw [← hs₁] at hdom
    have hP : ‖(if χ = 1 then 1 / (s₁ - 1) ^ (k + 1) else 0)
        + (if χ * χ₁ = 1 then 1 / (s₁ - 1) ^ (k + 1) else 0)
        - (if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then 1 / (s₁ - β₁) ^ (k + 1) else 0)
        - (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then 1 / (s₁ - β₁) ^ (k + 1) else 0)‖
        ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
      refine dhfPoles χ₁ χ hχ₁2 hχ₁1 η ρ.im β₁ hη hβ1 hβ2 k s₁ hs₁ (χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3) (χ = 1 ∧ (β₁ : ℂ) ∈ Z4) ?_ ?_
        (fun h => h.1) (fun h => h.1)
      · intro h2 hc hd
        apply hc
        refine ⟨h2, (hZ3 β₁).2 ⟨hd, ?_⟩⟩
        rw [h2]
        exact ⟨Or.inl hχ₁1, hβ⟩
      · intro h1 hc hd
        apply hc
        refine ⟨h1, (hZ4 β₁).2 ⟨hd, ?_⟩⟩
        rw [h1, one_mul]
        exact ⟨Or.inl hχ₁1, hβ⟩
    have hm := dhfNormArith _ _ _ _ _ _ _ _ _ _ k _ _ _ _ (hE3 k s₁ h1s₁ hd₁) (hE4 k s₁ h1s₁ hd₁)
      rfl rfl hdom hP
    have eeγ : CL * Real.log ((M : ℝ) * (|ρ.im| + 2)) * 25 ^ k ≤ CL * (2 * Real.log ((M : ℝ) * T)) * 25 ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogγ hCL.le) (by positivity)
    have h25k : (25 : ℝ) ^ k ≤ 25 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have eek := mul_le_mul_of_nonneg_left h25k (mul_nonneg hCL.le hl0)
    have h8 : (8 : ℝ) ^ (k + 1) ≤ 25 ^ (k + 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have h25 : (25 : ℝ) ^ (k + 1) ≤ Real.log ((M : ℝ) * T) * 25 ^ (k + 1) :=
      le_mul_of_one_le_left (by positivity) hlog1
    have hX0 : (0 : ℝ) ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
      apply div_nonneg _ (by positivity); apply mul_nonneg (by positivity); linarith
    have eG : 2 * ((k + 1 : ℕ) : ℝ) * (1 - β₁) / η ^ (k + 1 + 1) =
        2 * (((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2)) := by push_cast; ring
    have t4 : (8 * CL + 1) * Real.log ((M : ℝ) * T) * 25 ^ (k + 1) =
        8 * (CL * Real.log ((M : ℝ) * T) * 25 ^ (k + 1)) + Real.log ((M : ℝ) * T) * 25 ^ (k + 1) := by ring
    rw [eG, t4]
    have hCL0 : 0 ≤ CL * Real.log ((M : ℝ) * T) * 25 ^ (k + 1) := by positivity
    linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
