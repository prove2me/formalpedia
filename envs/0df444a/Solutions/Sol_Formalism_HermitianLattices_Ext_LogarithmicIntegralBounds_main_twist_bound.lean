-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.main_twist_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:31.773987+00:00
-- url     : https://prove2.me/submissions/ac9c338a-8dca-4b64-8806-db040cb93c62

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistB
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_sum_jac_cls_eq_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
private theorem sum_clsB_mul_mod_eq_sum {M : Type*} [AddCommMonoid M] (m₀ s a₀ u : ℕ) (hN : 0 < m₀ * s)
    (hu1 : u % m₀ = 1 % m₀) (hus : u.Coprime s) (f : ℕ → M) :
    ∑ b ∈ clsB m₀ s a₀, f ((b * u) % (m₀ * s)) = ∑ b ∈ clsB m₀ s a₀, f b := by
  have hcm : ∀ x k : ℕ, Nat.Coprime x k ↔ Nat.Coprime (x % k) k := fun x k => by
    rw [Nat.Coprime, Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
  have hum : u.Coprime m₀ := by
    rw [hcm, hu1, ← hcm]
    exact Nat.coprime_one_left _
  have huN : u.Coprime (m₀ * s) := Nat.Coprime.mul_right hum hus
  have hmap : ∀ b ∈ clsB m₀ s a₀, (b * u) % (m₀ * s) ∈ clsB m₀ s a₀ := by
    intro b hb
    simp only [clsB, Finset.mem_filter, Finset.mem_range] at hb ⊢
    refine ⟨Nat.mod_lt _ hN, ?_, ?_⟩
    · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right m₀ s), Nat.mul_mod, hb.2.1, hu1, ← Nat.mul_mod, mul_one]
    · rw [hcm, Nat.mod_mod_of_dvd _ (dvd_mul_left s m₀), ← hcm]
      exact Nat.Coprime.mul hb.2.2 hus
  have hinj : Set.InjOn (fun b => (b * u) % (m₀ * s)) (clsB m₀ s a₀) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, clsB, Finset.mem_filter, Finset.mem_range] at hx hy
    have h := Nat.ModEq.cancel_right_of_coprime huN.symm (show x * u ≡ y * u [MOD m₀ * s] from hxy)
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at h
  have himg : (clsB m₀ s a₀).image (fun b => (b * u) % (m₀ * s)) = clsB m₀ s a₀ :=
    Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hmap)
      (by rw [Finset.card_image_of_injOn hinj])
  calc ∑ b ∈ clsB m₀ s a₀, f ((b * u) % (m₀ * s))
      = ∑ x ∈ (clsB m₀ s a₀).image (fun b => (b * u) % (m₀ * s)), f x := (Finset.sum_image hinj).symm
    _ = ∑ b ∈ clsB m₀ s a₀, f b := by rw [himg]
private theorem jacobiSym_mul_mod_eq_mul (m₀ s b u : ℕ) :
    jacobiSym (((b * u) % (m₀ * s) : ℕ) : ℤ) s = jacobiSym (b : ℤ) s * jacobiSym (u : ℤ) s := by
  rw [← jacobiSym.mul_left]
  apply jacobiSym.mod_left'
  push_cast
  exact Int.emod_emod_of_dvd _ (dvd_mul_left _ _)
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (m₀ s a₀ : ℕ) [NeZero (m₀ * s)] (hm : 0 < m₀) (h1 : 1 < s) (hodd : Odd s)
    (hsq : Squarefree s) (hcop : m₀.Coprime s) (ha : a₀.Coprime m₀) (X r : ℝ)
    (e : Option (DirichletCharacter ℂ (m₀ * s) × ℝ)) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (hli : 0 < liX X)
    (hG : ∀ (χ : DirichletCharacter ℂ (m₀ * s)) (β : ℝ), e = some (χ, β) →
      (∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s → χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)) →
      |liX (X ^ β)| ≤ r * liX X) :
    |∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * mainAP e b X| ≤
      2 * r * ∑ b ∈ clsB m₀ s a₀, |mainAP e b X| := by
  have hN : 0 < m₀ * s := Nat.pos_of_ne_zero (NeZero.ne _)
  have hφ : (0 : ℝ) < ((m₀ * s).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hN
  have hsum0 := sum_jac_cls_eq_zero m₀ s a₀ h1 hodd hsq hcop ha
  have hRHS : 0 ≤ 2 * r * ∑ b ∈ clsB m₀ s a₀, |mainAP e b X| := by positivity
  rcases e with _ | ⟨χ, β⟩
  · simp only [mainAP]
    rw [← Finset.sum_mul, hsum0, zero_mul, abs_zero]
    simpa [mainAP] using hRHS
  · have hexp : ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * mainAP (some (χ, β)) b X =
        -(liX (X ^ β) / ((m₀ * s).totient : ℝ)) *
          ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re := by
      simp only [mainAP]
      rw [Finset.mul_sum]
      have key : ∀ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) *
          ((liX X - (χ (b : ZMod (m₀ * s))).re * liX (X ^ β)) / ((m₀ * s).totient : ℝ)) =
          (jacobiSym (b : ℤ) s : ℝ) * (liX X / ((m₀ * s).totient : ℝ)) +
          -(liX (X ^ β) / ((m₀ * s).totient : ℝ)) *
            ((jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re) := fun b _ => by ring
      rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.sum_mul, hsum0, zero_mul, zero_add]
    have hre1 : ∀ b : ℕ, |(χ (b : ZMod (m₀ * s))).re| ≤ 1 := fun b =>
      (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ _)
    by_cases hc : ∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s →
        χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)
    · have hLb := hG χ β rfl hc
      have hS : |∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re| ≤
          ((clsB m₀ s a₀).card : ℝ) := by
        calc _ ≤ ∑ b ∈ clsB m₀ s a₀, |(jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ b ∈ clsB m₀ s a₀, (1 : ℝ) := Finset.sum_le_sum fun b _ => by
              rw [abs_mul]
              have hj : |(jacobiSym (b : ℤ) s : ℝ)| ≤ 1 := by
                rcases jacobiSym.trichotomy (b : ℤ) s with h | h | h <;> simp [h]
              calc _ ≤ 1 * 1 := mul_le_mul hj (hre1 b) (abs_nonneg _) zero_le_one
                _ = 1 := one_mul 1
          _ = ((clsB m₀ s a₀).card : ℝ) := by simp
      have hlow : ∀ b ∈ clsB m₀ s a₀, liX X / (2 * ((m₀ * s).totient : ℝ)) ≤ |mainAP (some (χ, β)) b X| := by
        intro b _
        have h3 : (χ (b : ZMod (m₀ * s))).re * liX (X ^ β) ≤ r * liX X := by
          calc (χ (b : ZMod (m₀ * s))).re * liX (X ^ β) ≤ |(χ (b : ZMod (m₀ * s))).re * liX (X ^ β)| :=
                le_abs_self _
            _ = |(χ (b : ZMod (m₀ * s))).re| * |liX (X ^ β)| := abs_mul _ _
            _ ≤ 1 * |liX (X ^ β)| := mul_le_mul_of_nonneg_right (hre1 b) (abs_nonneg _)
            _ ≤ r * liX X := by linarith
        refine le_trans ?_ (le_abs_self _)
        simp only [mainAP]
        rw [div_le_div_iff₀ (by positivity) hφ]
        have h4 : liX X / 2 ≤ liX X - (χ (b : ZMod (m₀ * s))).re * liX (X ^ β) := by nlinarith
        nlinarith
      rw [hexp, abs_mul, abs_neg, abs_div, abs_of_pos hφ]
      calc |liX (X ^ β)| / ((m₀ * s).totient : ℝ) *
            |∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re|
          ≤ r * liX X / ((m₀ * s).totient : ℝ) * ((clsB m₀ s a₀).card : ℝ) :=
            mul_le_mul (div_le_div_of_nonneg_right hLb hφ.le) hS (abs_nonneg _) (by positivity)
        _ = 2 * r * ∑ b ∈ clsB m₀ s a₀, liX X / (2 * ((m₀ * s).totient : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            field_simp
        _ ≤ 2 * r * ∑ b ∈ clsB m₀ s a₀, |mainAP (some (χ, β)) b X| :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlow) (by linarith)
    · push_neg at hc
      obtain ⟨u, hu1, hus, hne⟩ := hc
      have hpt : ∀ b : ℕ, (((jacobiSym (((b * u) % (m₀ * s) : ℕ) : ℤ) s : ℝ)) : ℂ) *
          χ ((((b * u) % (m₀ * s) : ℕ)) : ZMod (m₀ * s)) =
          (((jacobiSym (u : ℤ) s : ℝ)) : ℂ) * χ (u : ZMod (m₀ * s)) *
            ((((jacobiSym (b : ℤ) s : ℝ)) : ℂ) * χ (b : ZMod (m₀ * s))) := by
        intro b
        rw [jacobiSym_mul_mod_eq_mul, ZMod.natCast_mod, Nat.cast_mul, map_mul]
        push_cast
        ring
      have hre := sum_clsB_mul_mod_eq_sum m₀ s a₀ u hN hu1 hus
        (fun x => (((jacobiSym (x : ℤ) s : ℝ)) : ℂ) * χ (x : ZMod (m₀ * s)))
      simp only [hpt] at hre
      rw [← Finset.mul_sum] at hre
      have hgcd : Int.gcd (u : ℤ) s = 1 := by rw [Int.gcd_natCast_natCast]; exact hus
      have hc1 : (((jacobiSym (u : ℤ) s : ℝ)) : ℂ) * χ (u : ZMod (m₀ * s)) ≠ 1 := by
        rcases jacobiSym.eq_one_or_neg_one hgcd with h | h
        · rw [h] at hne ⊢
          intro hh
          apply hne
          push_cast at hh ⊢
          simpa using hh
        · rw [h] at hne ⊢
          intro hh
          apply hne
          push_cast at hh ⊢
          linear_combination -hh
      have hT : ∑ b ∈ clsB m₀ s a₀, (((jacobiSym (b : ℤ) s : ℝ)) : ℂ) * χ (b : ZMod (m₀ * s)) = 0 := by
        have h0 : ((((jacobiSym (u : ℤ) s : ℝ)) : ℂ) * χ (u : ZMod (m₀ * s)) - 1) *
            ∑ b ∈ clsB m₀ s a₀, (((jacobiSym (b : ℤ) s : ℝ)) : ℂ) * χ (b : ZMod (m₀ * s)) = 0 := by
          rw [sub_mul, hre, one_mul, sub_self]
        exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc1)
      have hS0 : ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re = 0 := by
        have h0 := congrArg Complex.re hT
        rw [Complex.re_sum] at h0
        simpa [Complex.re_ofReal_mul] using h0
      rw [hexp, hS0, mul_zero, abs_zero]
      exact hRHS
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
