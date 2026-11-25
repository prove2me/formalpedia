-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.lemma_L_weight_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:06:50.011592+00:00
-- url     : https://prove2.me/submissions/de17213a-1daa-4cc3-bb56-188ce611a4e1

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_torus_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : LemmaLWeight := by
  intro d g k n hd hg hk hkN hlow hup
  have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < g := by linarith
  obtain ⟨hT0, hT1, hT2⟩ := torus_bounds g hg d hd
  set T := (d.map (fun x => (g : ℝ) ^ x - 1)).prod with hTdef
  set N := d.sum with hN
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := pow_pos hg0 k
  have hgN : (0 : ℝ) < (g : ℝ) ^ N := pow_pos hg0 N
  have hk1 : (g : ℝ) ^ k = (g : ℝ) ^ (k - 1) * g := by
    rw [← pow_succ]; congr 1; omega
  constructor
  ·
    have h1 : (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) ≤ n := by
      have : (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) = (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) := by
        rw [hk1]; field_simp
      rw [this]; exact hlow
    have h0 : (0 : ℝ) ≤ 1 - 1 / (g : ℝ) := by
      rw [sub_nonneg, div_le_one hg0]; linarith
    rw [div_le_div_iff₀ hgN (mul_pos hgk hT0)]
    calc (1 - 1 / (g : ℝ)) * ((g : ℝ) ^ k * T) = ((g : ℝ) ^ k * (1 - 1 / (g : ℝ))) * T := by ring
      _ ≤ ((g : ℝ) ^ k * (1 - 1 / (g : ℝ))) * (g : ℝ) ^ N :=
          mul_le_mul_of_nonneg_left hT1 (mul_nonneg hgk.le h0)
      _ ≤ n * (g : ℝ) ^ N := mul_le_mul_of_nonneg_right h1 hgN.le
  · intro h2N
    set t : ℝ := (N : ℝ) / g with ht
    have ht0 : 0 ≤ t := div_nonneg (Nat.cast_nonneg _) hg0.le
    have ht1 : t ≤ 1 / 2 := by
      rw [ht, div_le_iff₀ hg0]
      have : (2 : ℝ) * N ≤ g := by exact_mod_cast h2N
      linarith

    have hsum : ∑ i ∈ Finset.range (k + 1), (N : ℝ) ^ i * (g : ℝ) ^ (k - i)
        = (g : ℝ) ^ k * ∑ i ∈ Finset.range (k + 1), t ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have : (g : ℝ) ^ k = (g : ℝ) ^ (k - i) * (g : ℝ) ^ i := by
        rw [← pow_add]; congr 1; omega
      rw [ht, div_pow, this]
      have hgi : (g : ℝ) ^ i ≠ 0 := (pow_pos hg0 i).ne'
      field_simp
    have hgeom : (∑ i ∈ Finset.range (k + 1), t ^ i) * (1 - t) ≤ 1 := by
      rw [geom_sum_mul_neg]
      have : 0 ≤ t ^ (k + 1) := pow_nonneg ht0 _
      linarith
    have hcard : (d.card : ℝ) ≤ (N : ℝ) := by
      have := Multiset.card_nsmul_le_sum hd
      simp only [smul_eq_mul, mul_one] at this
      exact_mod_cast this
    have hT3 : (g : ℝ) ^ N * (1 - t) ≤ T := by
      refine le_trans ?_ hT2
      apply mul_le_mul_of_nonneg_left _ hgN.le
      have : (d.card : ℝ) / g ≤ t := div_le_div_of_nonneg_right hcard hg0.le
      linarith
    have h1t : (0 : ℝ) < 1 - t := by linarith
    set st := ∑ i ∈ Finset.range (k + 1), t ^ i with hsdef
    have hs0 : 0 ≤ st := Finset.sum_nonneg (fun i _ => pow_nonneg ht0 i)
    have hpoly : 1 ≤ (1 + 6 * t) * (1 - t) ^ 2 := by nlinarith [mul_nonneg ht0 (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - 2 * t) (by linarith : (0:ℝ) ≤ 4 - 3 * t))]
    have e6 : 1 + 6 * (N : ℝ) / g = 1 + 6 * t := by rw [ht]; ring
    rw [e6, div_le_div_iff₀ (mul_pos hgk hT0) hgN]
    have hn : n ≤ (g : ℝ) ^ k * st := by rw [← hsum]; exact hup

    have hA : st ≤ (1 + 6 * t) * (1 - t) := by
      have h7 : st * (1 - t) ≤ ((1 + 6 * t) * (1 - t)) * (1 - t) := by
        calc st * (1 - t) ≤ 1 := hgeom
          _ ≤ (1 + 6 * t) * (1 - t) ^ 2 := hpoly
          _ = ((1 + 6 * t) * (1 - t)) * (1 - t) := by ring
      exact le_of_mul_le_mul_right h7 h1t
    calc n * (g : ℝ) ^ N ≤ ((g : ℝ) ^ k * st) * (g : ℝ) ^ N :=
          mul_le_mul_of_nonneg_right hn hgN.le
      _ ≤ ((g : ℝ) ^ k * ((1 + 6 * t) * (1 - t))) * (g : ℝ) ^ N := by
          apply mul_le_mul_of_nonneg_right _ hgN.le
          exact mul_le_mul_of_nonneg_left hA hgk.le
      _ = (1 + 6 * t) * ((g : ℝ) ^ k * ((g : ℝ) ^ N * (1 - t))) := by ring
      _ ≤ (1 + 6 * t) * ((g : ℝ) ^ k * T) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact mul_le_mul_of_nonneg_left hT3 hgk.le
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
