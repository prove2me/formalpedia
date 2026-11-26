-- Prove2me | solution 1 for FixedNumerator.QuarticData.truncSum_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:44:53.408963+00:00
-- url     : https://prove2.me/submissions/6dc3f78c-483b-4682-8f91-035dbd947bc1

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split
public import Theorems.Thm_FixedNumerator_mem_normBall
public import Theorems.Thm_P2M_FixedNumerator_norm_nonneg__64b3937061ea
public import Theorems.Thm_P2M_FixedNumerator_norm_pow__cb22f6c8b435
public import Theorems.Thm_FixedNumerator_ne_zero_of_four_dvd
public import Theorems.Thm_FixedNumerator_two_le_norm_of_prime
public import Theorems.Thm_FixedNumerator_toNat_norm
public import Theorems.Thm_FixedNumerator_le_div_iff_norm
public import Theorems.Thm_FixedNumerator_pow_mul_inj
public import Theorems.Thm_FixedNumerator_weight_pow
public import Theorems.Thm_FixedNumerator_C_sign_congr
public import Theorems.Thm_FixedNumerator_IsPrimary_mul
public import Theorems.Thm_FixedNumerator_IsPrimary_of_dvd_sub
public import Theorems.Thm_FixedNumerator_IsPrimary_pow
public import Theorems.Thm_FixedNumerator_QuarticData_g_split
public import Theorems.Thm_FixedNumerator_pow_two_mul_sub_one


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)
namespace FixedNumerator.QuarticData
theorem _root_.solution (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) {π γ : GaussianInt} (μ β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (X : ℕ) :
    truncSum D W μ β γ X =
      ∑ k ∈ range (X + 1), (-1 : ℂ) ^ C (π ^ k * β) (π ^ k) * D.g μ (π ^ k) * W π ^ k *
        truncSum D W (μ * π ^ (2 * k)) (π ^ k * β) (π * γ) (X / π.norm.toNat ^ k) := by
  classical
  have hN2 := two_le_norm_of_prime hπ
  have hNpos : ∀ k : ℕ, 0 < π.norm.toNat ^ k := fun k => pow_pos (by omega) k
  have hNcast : ∀ k : ℕ, ((π.norm.toNat ^ k : ℕ) : ℤ) = π.norm ^ k := by
    intro k; push_cast; rw [toNat_norm]
  simp only [truncSum, Finset.mul_sum]
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => π ^ x.1 * x.2) ?_ ?_ ?_ ?_
  · -- maps into the left side
    rintro ⟨k, c'⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, mem_normBall] at hx
    obtain ⟨_, hn, hcl, hcop⟩ := hx
    simp only [Finset.mem_filter, mem_normBall]
    refine ⟨?_, ?_, ?_⟩
    · rw [Zsqrtd.norm_mul, norm_pow']
      rw [le_div_iff_norm (hNpos k), hNcast] at hn
      exact hn
    · have h2 := pow_two_mul_sub_one hπp k
      have : π ^ k * c' - β = π ^ k * (c' - π ^ k * β) + (π ^ (2 * k) - 1) * β := by ring
      rw [this]; exact dvd_add (dvd_mul_of_dvd_right hcl _) (dvd_mul_of_dvd_left h2 _)
    · exact IsCoprime.mul_left_iff.mpr ⟨hπγ.pow_left, (IsCoprime.mul_right_iff.mp hcop).2⟩
  · -- injective
    rintro ⟨k, a⟩ ha ⟨j, b⟩ hb h
    simp only [Finset.mem_sigma, Finset.mem_filter] at ha hb
    have hpa : ¬ π ∣ a := fun hd =>
      (hπ.coprime_iff_not_dvd.mp (IsCoprime.mul_right_iff.mp ha.2.2.2).1.symm) hd
    have hpb : ¬ π ∣ b := fun hd =>
      (hπ.coprime_iff_not_dvd.mp (IsCoprime.mul_right_iff.mp hb.2.2.2).1.symm) hd
    obtain ⟨h1, h2⟩ := pow_mul_inj hπ hpa hpb h
    subst h1; subst h2; rfl
  · -- surjective
    intro c hc
    simp only [Finset.mem_filter, mem_normBall] at hc
    obtain ⟨hn, hcl, hcop⟩ := hc
    have hc0 : c ≠ 0 := ne_zero_of_four_dvd hβ hcl
    have hfin := FiniteMultiplicity.of_not_isUnit hπ.not_isUnit hc0
    obtain ⟨c', hcc', hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
    set k := multiplicity π c
    have hc'0 : c' ≠ 0 := by rintro rfl; simp at hcc'; exact hc0 hcc'
    have hnc' : 1 ≤ c'.norm := by
      have := norm_nonneg' c'
      have h0 : c'.norm ≠ 0 := fun h => hc'0 ((Zsqrtd.norm_eq_zero_iff (by norm_num) c').mp h)
      omega
    have hnorm : c.norm = π.norm ^ k * c'.norm := by rw [hcc', Zsqrtd.norm_mul, norm_pow']
    have hkX : k < X + 1 := by
      have h2k : (2 : ℤ) ^ k ≤ π.norm ^ k := pow_le_pow_left₀ (by norm_num) hN2 k
      have hpk : (0 : ℤ) ≤ π.norm ^ k := le_trans (by positivity) h2k
      have : (2 : ℤ) ^ k ≤ X := by nlinarith
      have hk2 : (k : ℤ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
      omega
    have hcop' : IsCoprime c' π := (hπ.coprime_iff_not_dvd.mpr hnd).symm
    have hcopγ : IsCoprime c' γ := by
      rw [hcc'] at hcop; exact (IsCoprime.mul_left_iff.mp hcop).2
    refine ⟨⟨k, c'⟩, ?_, hcc'.symm⟩
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, mem_normBall]
    refine ⟨hkX, ?_, ?_, IsCoprime.mul_right_iff.mpr ⟨hcop', hcopγ⟩⟩
    · rw [le_div_iff_norm (hNpos k), hNcast, ← hnorm]; exact hn
    · have h2 := pow_two_mul_sub_one hπp k
      have : c' - π ^ k * β = π ^ k * (π ^ k * c' - β) - (π ^ (2 * k) - 1) * c' := by ring
      rw [this, ← hcc']
      exact dvd_sub (dvd_mul_of_dvd_right hcl _) (dvd_mul_of_dvd_left h2 _)
  · -- the summands agree
    rintro ⟨k, c'⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter] at hx
    obtain ⟨_, _, hcl, hcop⟩ := hx
    have hkβ : IsPrimary (π ^ k * β) := (hπp.pow k).mul hβ
    have hc'p : IsPrimary c' := hkβ.of_dvd_sub hcl
    have hcop' : IsCoprime π c' := (IsCoprime.mul_right_iff.mp hcop).1.symm
    simp only
    rw [D.g_split μ hπp hc'p hcop' k, C_sign_congr hkβ hcl, hW, weight_pow hW1 hW]
    ring
end FixedNumerator.QuarticData
