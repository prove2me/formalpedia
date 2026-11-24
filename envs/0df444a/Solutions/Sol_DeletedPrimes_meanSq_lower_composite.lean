-- Prove2me | solution 1 for DeletedPrimes.meanSq_lower_composite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:14:58.97732+00:00
-- url     : https://prove2.me/submissions/1ba2fffd-c5fa-480b-a621-72af7c74c58a

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
import Theorems.Thm_DeletedPrimes_share_bound
import Theorems.Thm_DeletedPrimes_errExp_le_maxExp
import Theorems.Thm_DeletedPrimes_good_scales
import Theorems.Thm_DeletedPrimes_kappaK_lt_half
import Theorems.Thm_DeletedPrimes_kappaK_lt_one_sub
import Theorems.Thm_DeletedPrimes_maxExp_neg_iff


set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} (hα0 : 0 < dim S) (hα1 : dim S < 1)
    (F : Frame S) {m : ℝ} (hm : 0 < m) (hM : MertensLaw S (dim S) m) {k : ℕ} (hk : 1 ≤ k) {κ : ℝ}
    (hκ0 : 0 < κ) (hκ : κ < kappaK k (dim S)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ c : ℝ, 0 < c ∧ ∃ᶠ X : ℝ in atTop, c * X ^ (κ * (dim S - η)) ≤ meanSq S X := by
  set α := dim S with hαdef
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  set μ := -maxExp k α κ with hμdef
  have hμ : 0 < μ := by have := (maxExp_neg_iff hk hα0 hα1).2 hκ; linarith
  have herr : ∀ τ ∈ Set.Icc 0 κ, errExp k α κ τ ≤ -μ := fun τ hτ => by
    rw [hμdef, neg_neg]; exact errExp_le_maxExp hk hα0 hα1 hκ0.le hτ.1 hτ.2
  have h12 : κ < 1 / 2 := lt_trans hκ (kappaK_lt_half hk hα0 hα1)
  have h1a : κ < 1 - α := lt_trans hκ (kappaK_lt_one_sub hk hα0 hα1)
  obtain ⟨δ, hδ, η₀, hη₀, hF⟩ := F.bound k hk κ μ hκ0 hμ h12 h1a herr
  refine ⟨η₀, hη₀, fun η hη hηlt => ?_⟩
  obtain ⟨c, hc, Y₀, hY⟩ := hF η hη hηlt
  refine ⟨c, hc, ?_⟩
  -- the block exponents `λ_i = (1 + iρ)/k`, separated by the factor `1 + δ'`
  set ρ := min 1 (k * δ / (2 * k + 1)) with hρdef
  have hρ0 : 0 < ρ := lt_min one_pos (div_pos (mul_pos hkpos hδ) (by linarith))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρ2 : ρ ≤ k * δ / (2 * k + 1) := min_le_right _ _
  set δ' := ρ / (2 * (1 + k * ρ)) with hδ'def
  have hD : 0 < 1 + k * ρ := by positivity
  have hδ'0 : 0 < δ' := by positivity
  have hδ'ρ : δ' * (1 + k * ρ) = ρ / 2 := by rw [hδ'def]; field_simp
  have hδ'le : δ' ≤ ρ := by
    have : δ' * 1 ≤ δ' * (1 + k * ρ) := mul_le_mul_of_nonneg_left (by nlinarith) hδ'0.le
    linarith
  set w := (1 + k * ρ) * (1 + δ') - 1 with hwdef
  have hw : w ≤ k * δ := by
    have h1 : w ≤ (2 * k + 1) * ρ := by
      have : (1 + k * ρ) * (1 + δ') ≤ (1 + k * ρ) * (1 + ρ) := mul_le_mul_of_nonneg_left (by linarith) hD.le
      have h2 : k * ρ * ρ ≤ k * ρ := mul_le_of_le_one_right (by positivity) hρ1
      rw [hwdef]; nlinarith
    have h3 : (2 * k + 1) * ρ ≤ k * δ := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * k + 1)] at hρ2; linarith
    linarith
  set lam : Fin k → ℝ := fun i => (1 + (i : ℝ) * ρ) / k with hlamdef
  have hlam0 : ∀ i, 0 < lam i := fun i => by rw [hlamdef]; positivity
  have hlamlo : ∀ i, 1 / k ≤ lam i := fun i => by
    have : (0 : ℝ) ≤ (i : ℝ) * ρ := by positivity
    rw [hlamdef]; apply div_le_div_of_nonneg_right _ hkpos.le; linarith
  have hlamhi : ∀ i, lam i * (1 + δ') ≤ (1 + w) / k := fun i => by
    have hi : (i : ℝ) ≤ k := by exact_mod_cast i.isLt.le
    rw [hlamdef, hwdef, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hkpos.le
    have : 1 + (i : ℝ) * ρ ≤ 1 + k * ρ := by nlinarith
    nlinarith
  have hsep : ∀ i i' : Fin k, i < i' → lam i * (1 + δ') < lam i' := by
    intro i i' hii'
    have hlt : (i : ℝ) + 1 ≤ i' := by exact_mod_cast (show (i : ℕ) + 1 ≤ i' from hii')
    have hi : (i : ℝ) ≤ k := by exact_mod_cast i.isLt.le
    rw [hlamdef, div_mul_eq_mul_div]
    apply div_lt_div_of_pos_right _ hkpos
    have h1 : (1 + (i : ℝ) * ρ) * δ' ≤ (1 + k * ρ) * δ' :=
      mul_le_mul_of_nonneg_right (by nlinarith) hδ'0.le
    nlinarith
  have hgs := good_scales hα0 hm hM hδ'0 hη lam hlam0 hsep
  rw [Filter.frequently_atTop]
  intro B
  have hev : ∀ᶠ X₀ : ℝ in atTop, (∃ j : Fin k → ℕ, StrictMono j ∧ ∀ i,
      X₀ ^ lam i ≤ 2 ^ j i ∧ (2 : ℝ) ^ j i ≤ X₀ ^ (lam i * (1 + δ')) ∧
      ((2 : ℝ) ^ j i) ^ (α - η) ≤ blockCount S (2 ^ j i)) ∧ 1 < X₀ ∧ Y₀ ≤ X₀ ∧ B ≤ X₀ ^ (1 / κ) := by
    filter_upwards [hgs, eventually_gt_atTop 1, eventually_ge_atTop Y₀,
      (tendsto_rpow_atTop (show 0 < 1 / κ by positivity)).eventually_ge_atTop B] with X₀ h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨X₀, ⟨j, hj, hjb⟩, hX₀1, hX₀Y, hX₀B⟩ := hev.exists
  have hX₀0 : 0 < X₀ := by linarith
  set L := Real.log X₀ with hLdef
  have hL : 0 < L := Real.log_pos hX₀1
  set ℓ : Fin k → ℝ := fun i => Real.log ((2 : ℝ) ^ j i) with hℓdef
  have hℓ : ∀ i, L / k ≤ ℓ i ∧ ℓ i ≤ (1 + w) * L / k := by
    intro i
    obtain ⟨hlo, hhi, -⟩ := hjb i
    have hpos : (0 : ℝ) < 2 ^ j i := by positivity
    have e1 : Real.log (X₀ ^ lam i) = lam i * L := Real.log_rpow hX₀0 _
    have e2 : Real.log (X₀ ^ (lam i * (1 + δ'))) = lam i * (1 + δ') * L := Real.log_rpow hX₀0 _
    have l1 : lam i * L ≤ ℓ i := by
      rw [← e1]; exact Real.log_le_log (by positivity) hlo
    have l2 : ℓ i ≤ lam i * (1 + δ') * L := by
      rw [← e2]; exact Real.log_le_log hpos hhi
    constructor
    · calc L / k = 1 / k * L := by ring
        _ ≤ lam i * L := mul_le_mul_of_nonneg_right (hlamlo i) hL.le
        _ ≤ ℓ i := l1
    · calc ℓ i ≤ lam i * (1 + δ') * L := l2
        _ ≤ (1 + w) / k * L := mul_le_mul_of_nonneg_right (hlamhi i) hL.le
        _ = (1 + w) * L / k := by ring
  have hlogY : Real.log (∏ i, (2 : ℝ) ^ j i) = ∑ i, ℓ i :=
    Real.log_prod (fun i _ => by positivity)
  have hYpos : 0 < ∏ i, (2 : ℝ) ^ j i := Finset.prod_pos fun i _ => by positivity
  have hshare : ∀ i, |Real.log ((2 : ℝ) ^ j i) / Real.log (∏ i', (2 : ℝ) ^ j i') - 1 / k| ≤ δ := by
    intro i
    rw [hlogY]
    have := (share_bound hk hL ℓ hℓ i).2
    have h2 : w / k ≤ δ := by rw [div_le_iff₀ hkpos]; linarith
    exact le_trans this h2
  have hYX₀ : X₀ ≤ ∏ i, (2 : ℝ) ^ j i := by
    have h1 : L ≤ Real.log (∏ i, (2 : ℝ) ^ j i) := by
      rw [hlogY]; exact (share_bound hk hL ℓ hℓ ⟨0, by omega⟩).1
    exact (Real.log_le_log_iff hX₀0 hYpos).mp h1
  have hdens : ∀ i, ((2 : ℝ) ^ j i) ^ (α - η) ≤ blockCount S (2 ^ j i) := fun i => (hjb i).2.2
  have key := hY j hj (le_trans hX₀Y hYX₀) hshare hdens
  set Y := ∏ i, (2 : ℝ) ^ j i with hYdef
  refine ⟨Y ^ (1 / κ), le_trans hX₀B (Real.rpow_le_rpow hX₀0.le hYX₀ (by positivity)), ?_⟩
  have hprod : Y ^ (α - η) ≤ ∏ i, (blockCount S (2 ^ j i) : ℝ) := by
    rw [hYdef, ← Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
    gcongr with i _
    exact hdens i
  calc c * (Y ^ (1 / κ)) ^ (κ * (α - η)) = c * Y ^ (α - η) := by
        rw [← Real.rpow_mul hYpos.le]; congr 2; field_simp
    _ ≤ c * ∏ i, (blockCount S (2 ^ j i) : ℝ) := mul_le_mul_of_nonneg_left hprod hc.le
    _ ≤ meanSq S (Y ^ (1 / κ)) := key
end DeletedPrimes
