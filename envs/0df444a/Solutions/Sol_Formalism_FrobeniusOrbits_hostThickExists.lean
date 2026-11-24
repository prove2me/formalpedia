-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostThickExists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:18:39.11485+00:00
-- url     : https://prove2.me/submissions/132ab9b0-6d9a-442d-b1d5-0025fc4164b7

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Lemmata_GeneralBFactSecondLast_Imports
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickExists
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickExists_map_lt
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickExists_noRel_image
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickExists_card_image
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.FrobeniusOrbits.ThickExists
private lemma sphere_mem_lemma {S d k : ℕ} {v : Fin S → ℕ} (hv : v ∈ Behrend.sphere S d k) :
    (∀ i, v i < d) ∧ ∑ i, v i ^ 2 = k := by
  simp only [Behrend.sphere, Finset.mem_filter, Behrend.mem_box] at hv
  exact hv
end Formalism.FrobeniusOrbits.ThickExists
namespace Formalism.FrobeniusOrbits
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000
open ThickExists
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostThickExists := by
  unfold HostThickExists
  refine ⟨32, by norm_num, ?_⟩
  intro n L hL
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.log (L : ℝ) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.log (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (x * y) := ⟨_, rfl⟩
  have hrw : Real.sqrt (Real.log (n : ℝ) * Real.log (L : ℝ)) = s := by rw [hs, hx, hy]
  rw [hrw]
  have hy_half : (1 : ℝ) / 2 < y := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num) hL2
    rw [hy]
    linarith
  have hy0 : 0 < y := by linarith
  by_cases hsmall : (n : ℝ) * Real.exp (-32 * s) / L ≤ 1
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · refine ⟨∅, by simp, ?_, by simp [hn]⟩
      unfold NoRel
      intro s₁ hs₁
      simp at hs₁
    · refine ⟨{0}, ?_, ?_, ?_⟩
      · intro m hm
        rw [Finset.mem_singleton] at hm
        subst hm
        simpa using hn
      · unfold NoRel
        intro s₁ hs₁ s₂ hs₂ s₃ hs₃ h12
        rw [Finset.mem_singleton] at hs₁ hs₂
        exact absurd (hs₁.trans hs₂.symm) h12
      · rw [Finset.card_singleton, Nat.cast_one]
        exact hsmall
  push_neg at hsmall
  have hnpos : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn] at hsmall
      norm_num at hsmall
    · exact_mod_cast hn
  have eL : Real.exp y = L := by rw [hy, Real.exp_log hLpos]
  have en : Real.exp x = n := by rw [hx, Real.exp_log hnpos]
  have hpos : 0 < x + -32 * s - y := by
    rw [← Real.exp_lt_exp, Real.exp_zero, Real.exp_sub, Real.exp_add, eL, en]
    exact hsmall
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hxpos : 0 < x := by linarith
  have hs2 : s ^ 2 = x * y := by rw [hs]; exact Real.sq_sqrt (mul_pos hxpos hy0).le
  have hs32 : 32 * y < s := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hc), mul_pos hpos hy0, sq_nonneg y]
  have hs16 : 16 < s := by linarith
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ, S = ⌊s / y⌋₊ := ⟨_, rfl⟩
  have hS1 : (S : ℝ) ≤ s / y := by rw [hSdef]; exact Nat.floor_le (div_nonneg hs0 hy0.le)
  have hS2 : s / y < S + 1 := by rw [hSdef]; exact Nat.lt_floor_add_one _
  have hSy : (S : ℝ) * y ≤ s := (le_div_iff₀ hy0).mp hS1
  have hSy2 : s < (S + 1) * y := (div_lt_iff₀ hy0).mp hS2
  have hS31 : (31 : ℝ) < S := by
    have h := lt_of_mul_lt_mul_right (show (32 : ℝ) * y < (S + 1) * y by linarith) hy0.le
    linarith
  have hSpos : (0 : ℝ) < S := by linarith
  have hSne : (S : ℝ) ≠ 0 := hSpos.ne'
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (x - y - 3) / S := ⟨_, rfl⟩
  have haS : a * S = x - y - 3 := by rw [ha]; field_simp
  have h2Sy : s ≤ 2 * S * y := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ S - 1) hy0.le]
  have hxle : x ≤ 2 * s * S := by
    have h : x * y ≤ (2 * s * S) * y := by nlinarith [mul_le_mul_of_nonneg_left h2Sy hs0]
    exact le_of_mul_le_mul_right h hy0
  have ha2s : a ≤ 2 * s := by
    have h : a * S ≤ (2 * s) * S := by nlinarith
    exact le_of_mul_le_mul_right h hSpos
  have ha7 : 7 + y ≤ a := by
    have h1 : (7 + y) * S * y ≤ (x - y - 3) * y := by
      nlinarith [mul_nonneg hy0.le (sub_nonneg.mpr hSy), mul_nonneg hs0 (sub_nonneg.mpr hs32.le),
        mul_nonneg hy0.le (sub_nonneg.mpr hs32.le), mul_nonneg hs0 (sub_nonneg.mpr hy_half.le)]
    have h2 : (7 + y) * S ≤ x - y - 3 := le_of_mul_le_mul_right h1 hy0
    exact le_of_mul_le_mul_right (by rw [haS]; exact h2) hSpos
  have hexpb : 3 + S * (7 + y) + S + 2 * a ≤ 32 * s := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy_half.le) hSpos.le]
  have h4L : (0 : ℝ) < 4 * L := by positivity
  obtain ⟨d, hddef⟩ : ∃ d : ℕ, d = ⌊Real.exp a / (4 * L)⌋₊ := ⟨_, rfl⟩
  have hd1 : (d : ℝ) ≤ Real.exp a / (4 * L) := by rw [hddef]; exact Nat.floor_le (by positivity)
  have hd2 : Real.exp a / (4 * L) < d + 1 := by rw [hddef]; exact Nat.lt_floor_add_one _
  have hd1' : (d : ℝ) * (4 * L) ≤ Real.exp a := (le_div_iff₀ h4L).mp hd1
  have hd2' : Real.exp a < (d + 1) * (4 * L) := (div_lt_iff₀ h4L).mp hd2
  have h8Ly : 8 * (L : ℝ) ≤ Real.exp (7 + y) := by
    have h87 : (8 : ℝ) ≤ Real.exp 7 := by linarith [Real.add_one_le_exp (7 : ℝ)]
    rw [Real.exp_add, eL]
    nlinarith
  have h8L : 8 * (L : ℝ) ≤ Real.exp a := le_trans h8Ly (Real.exp_le_exp.mpr ha7)
  have hQd : Real.exp a / (8 * L) ≤ d := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hd1r : (1 : ℝ) ≤ d := le_trans ((one_le_div (by positivity)).mpr h8L) hQd
  have hdpos : (0 : ℝ) < d := by linarith
  have hdQ : (d : ℝ) ≤ Real.exp a := by
    nlinarith [mul_nonneg hdpos.le (by linarith : (0 : ℝ) ≤ 4 * L - 1)]
  have hdS : Real.exp a ^ S ≤ (d : ℝ) ^ S * (8 * L) ^ S := by
    have h : (Real.exp a / (8 * L)) ^ S ≤ (d : ℝ) ^ S := by gcongr
    rwa [div_pow, div_le_iff₀ (by positivity)] at h
  have hQS : Real.exp a ^ S = Real.exp (x - y - 3) := by
    rw [← Real.exp_nat_mul, mul_comm, haS]
  have hn_eq : (n : ℝ) = Real.exp a ^ S * L * Real.exp 3 := by
    rw [hQS, ← eL, ← Real.exp_add, ← Real.exp_add, ← en]
    congr 1
    ring
  have hprod : Real.exp 3 * (8 * L) ^ S * S * Real.exp a ^ 2 ≤ Real.exp (32 * s) := by
    have hP : ((8 : ℝ) * L) ^ S ≤ Real.exp (S * (7 + y)) := by
      rw [Real.exp_nat_mul]
      gcongr
    have hSe : (S : ℝ) ≤ Real.exp S := by linarith [Real.add_one_le_exp (S : ℝ)]
    have hQ2 : Real.exp a ^ 2 = Real.exp (2 * a) := by rw [sq, ← Real.exp_add, two_mul]
    calc Real.exp 3 * (8 * L) ^ S * S * Real.exp a ^ 2
        ≤ Real.exp 3 * Real.exp (S * (7 + y)) * Real.exp S * Real.exp (2 * a) := by
          rw [hQ2]
          gcongr
      _ = Real.exp (3 + S * (7 + y) + S + 2 * a) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (32 * s) := Real.exp_le_exp.mpr hexpb
  obtain ⟨k, hk⟩ := Behrend.exists_large_sphere S d
  refine ⟨(Behrend.sphere S d k).image (Behrend.map (4 * L * d)), ?_,
    noRel_image L S d k (by omega), ?_⟩
  · intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨v, hv, rfl⟩ := hm
    obtain ⟨hbox, -⟩ := sphere_mem_lemma hv
    have hdd : d ≤ 4 * L * d := by nlinarith
    have hmlt := map_lt (4 * L * d) v (fun i => lt_of_lt_of_le (hbox i) hdd)
    have hpowle : ((4 : ℝ) * L * d) ^ S ≤ Real.exp a ^ S := by
      gcongr
      linarith
    have hreal : (4 : ℝ) * L * (4 * L * d) ^ S ≤ n := by
      nlinarith [mul_le_mul_of_nonneg_left hpowle h4L.le,
        mul_nonneg (by linarith [Real.add_one_le_exp (3 : ℝ)] : (0 : ℝ) ≤ Real.exp 3 - 4)
          (by positivity : (0 : ℝ) ≤ L * Real.exp a ^ S)]
    have hnat : 4 * L * (4 * L * d) ^ S ≤ n := by exact_mod_cast hreal
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hmlt (by omega)) hnat
  · rw [card_image L S d k (by omega)]
    refine le_trans ?_ hk
    push_cast
    rw [div_le_iff₀ hLpos, div_mul_eq_mul_div, le_div_iff₀ (mul_pos hSpos (pow_pos hdpos 2))]
    calc (n : ℝ) * Real.exp (-32 * s) * (S * d ^ 2)
        ≤ n * Real.exp (-32 * s) * (S * Real.exp a ^ 2) := by gcongr
      _ = (Real.exp a ^ S * L * Real.exp 3) * Real.exp (-32 * s) * (S * Real.exp a ^ 2) := by
          rw [← hn_eq]
      _ ≤ ((d : ℝ) ^ S * (8 * L) ^ S * L * Real.exp 3) * Real.exp (-32 * s)
            * (S * Real.exp a ^ 2) := by gcongr
      _ = (d : ℝ) ^ S * L * (Real.exp (-32 * s) * (Real.exp 3 * (8 * L) ^ S * S * Real.exp a ^ 2)) := by
          ring
      _ ≤ (d : ℝ) ^ S * L * (Real.exp (-32 * s) * Real.exp (32 * s)) := by gcongr
      _ = (d : ℝ) ^ S * L := by
          rw [← Real.exp_add, show -32 * s + 32 * s = 0 by ring, Real.exp_zero, mul_one]
end Formalism.FrobeniusOrbits
