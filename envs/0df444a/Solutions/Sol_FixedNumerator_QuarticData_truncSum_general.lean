-- Prove2me | solution 1 for FixedNumerator.QuarticData.truncSum_general
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:46:43.306799+00:00
-- url     : https://prove2.me/submissions/0f263cc3-236a-4d77-a43f-6f451e4cc729

module
public import Definitions.Def_FixedNumerator_Cases
public import Definitions.Def_FixedNumerator_General
public import Theorems.Thm_FixedNumerator_C_sign_even_pow
public import Theorems.Thm_FixedNumerator_IsPrimary_mul
public import Theorems.Thm_FixedNumerator_IsPrimary_pow
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_congr_class
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_num_pow_four
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_split
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_zero
public import Theorems.Thm_FixedNumerator_pow_two_mul_sub_one
public import Theorems.Thm_FixedNumerator_two_le_norm_of_prime


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)
namespace FixedNumerator.QuarticData
theorem _root_.solution (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) {π γ μ' : GaussianInt} (β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    (e X : ℕ) :
    truncSum D W (π ^ e * μ') β γ X =
      ∑ j ∈ range (e / 4 + 1), D.g (π ^ e * μ') (π ^ (4 * j)) * W π ^ (4 * j) *
          truncSum D W (π ^ e * μ') β (π * γ) (X / π.norm.toNat ^ (4 * j)) +
        (-1 : ℂ) ^ C (π ^ (e + 1) * β) (π ^ (e + 1)) * D.g (π ^ e * μ') (π ^ (e + 1)) *
          W π ^ (e + 1) *
          truncSum D W (π ^ e * μ' * π ^ (2 * (e + 1))) (π ^ (e + 1) * β) (π * γ)
            (X / π.norm.toNat ^ (e + 1)) := by
  classical
  set μ := π ^ e * μ' with hμdef
  set F : ℕ → ℂ := fun k => (-1 : ℂ) ^ C (π ^ k * β) (π ^ k) * D.g μ (π ^ k) * W π ^ k *
    truncSum D W (μ * π ^ (2 * k)) (π ^ k * β) (π * γ) (X / π.norm.toNat ^ k) with hF
  have hN2 := two_le_norm_of_prime hπ
  -- terms beyond `X` vanish
  have hbig : ∀ k, X < k → F k = 0 := by
    intro k hk
    have hdiv : X / π.norm.toNat ^ k = 0 := by
      apply Nat.div_eq_of_lt
      calc X < 2 ^ k := lt_trans hk Nat.lt_two_pow_self
        _ ≤ π.norm.toNat ^ k := Nat.pow_le_pow_left (by omega) k
    simp only [hF, hdiv, D.truncSum_zero W _ _ ((hπp.pow k).mul hβ), mul_zero]
  -- terms off the support vanish
  have hsupp : ∀ k, k ≠ e + 1 → ¬ (4 ∣ k ∧ k ≤ e) → F k = 0 := by
    intro k hk1 hk2
    have : D.g μ (π ^ k) = 0 := by
      by_contra hne
      rcases D.g_prime_pow π μ' e k hπ hπp hμ' hne with h | h | h
      · exact hk2 ⟨h ▸ dvd_zero 4, by omega⟩
      · exact hk1 h
      · exact hk2 h
    simp only [hF, this, mul_zero, zero_mul]
  -- the support as a finset
  set K : Finset ℕ := insert (e + 1) ((range (e / 4 + 1)).image (fun j => 4 * j)) with hK
  have hnot : e + 1 ∉ (range (e / 4 + 1)).image (fun j => 4 * j) := by
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro j hj; omega
  have hsplit := D.truncSum_split W hW1 hW μ β hπ hπp hπγ hβ X
  -- both sums equal the sum over `range M`
  set M := max (X + 1) (e + 2) with hM
  have h1 : ∑ k ∈ range (X + 1), F k = ∑ k ∈ range M, F k := by
    apply Finset.sum_subset
    · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
    · intro k _ hk; simp only [Finset.mem_range, not_lt] at hk; exact hbig k (by omega)
  have h2 : ∑ k ∈ K, F k = ∑ k ∈ range M, F k := by
    apply Finset.sum_subset
    · intro k hk
      simp only [hK, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hk ⊢
      rcases hk with rfl | ⟨j, hj, rfl⟩ <;> omega
    · intro k _ hk
      simp only [hK, Finset.mem_insert, Finset.mem_image, Finset.mem_range, not_or,
        not_exists, not_and] at hk
      apply hsupp k hk.1
      rintro ⟨⟨j, rfl⟩, hle⟩
      exact hk.2 j (by omega) rfl
  rw [hsplit]
  change ∑ k ∈ range (X + 1), F k = _
  rw [h1, ← h2, hK, Finset.sum_insert hnot, Finset.sum_image (by intro a _ b _ h; simp only at h; omega),
    add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hev : Even (4 * j) := ⟨2 * j, by ring⟩
  have hcl : (4 : GaussianInt) ∣ π ^ (4 * j) * β - β := by
    have : π ^ (4 * j) * β - β = (π ^ (2 * (2 * j)) - 1) * β := by ring_nf
    rw [this]; exact dvd_mul_of_dvd_left (pow_two_mul_sub_one hπp (2 * j)) _
  simp only [hF]
  rw [C_sign_even_pow hπp _ hev, one_mul, D.truncSum_congr_class W _ _ hcl,
    show 2 * (4 * j) = 4 * (2 * j) by ring, D.truncSum_num_pow_four W _ hβ]
end FixedNumerator.QuarticData
