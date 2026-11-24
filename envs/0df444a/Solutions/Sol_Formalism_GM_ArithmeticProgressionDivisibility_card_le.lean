-- Prove2me | solution 1 for Formalism.GM.ArithmeticProgressionDivisibility.card_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:24.893818+00:00
-- url     : https://prove2.me/submissions/bef3ef93-5855-4ee4-a667-2d7b59597de6

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowAP
import Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_norm_int
import Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_norm_sub_le_max
import Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_dvd_of_norm_lt
import Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_dvd_cancel
import Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_progr_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.GM
open Finset
namespace ArithmeticProgressionDivisibility
variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [NormedField K] [NormedAlgebra ℚ_[p] K]
private lemma card_le_div_add_one_of_subset_range_of_mod_eq (Y₀ q : ℕ) (hq : 0 < q) (S : Finset ℕ) (hS : S ⊆ range Y₀)
    (hmod : ∀ j ∈ S, ∀ j' ∈ S, j % q = j' % q) : S.card ≤ Y₀ / q + 1 := by
  have hinj : Set.InjOn (fun j => j / q) S := by
    intro j hj j' hj' he
    have h1 := hmod j hj j' hj'
    simp only at he
    rw [← Nat.div_add_mod j q, ← Nat.div_add_mod j' q, he, h1]
  have h2 := Finset.card_le_card_of_injOn (fun j => j / q) (t := range (Y₀ / q + 1)) ?_ hinj
  · simpa using h2
  · intro j hj
    have hj2 : j ∈ range Y₀ := hS (Finset.mem_coe.mp hj)
    rw [Finset.mem_range] at hj2
    rw [Finset.mem_coe, Finset.mem_range]
    show j / q < Y₀ / q + 1
    have h3 := Nat.div_le_div_right (c := q) hj2.le
    omega
end ArithmeticProgressionDivisibility
open ArithmeticProgressionDivisibility
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM
open Finset
open Formalism.GM.ArithmeticProgressionDivisibility
variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [NormedField K] [NormedAlgebra ℚ_[p] K]
namespace Formalism.GM.ArithmeticProgressionDivisibility
theorem _root_.solution [IsUltrametricDist K] (ζ : K) (t₀ d : ℤ) (hd : IsCoprime d (p : ℤ)) (Y₀ i : ℕ) :
    (((range Y₀).filter (fun j : ℕ => ‖((progr t₀ d j : ℤ) : K) - ζ‖ < (p : ℝ) ^ (1 - (i : ℤ)))).card : ℝ)
      ≤ (Y₀ : ℝ) / (p : ℝ) ^ i + 1 := by
  have hq0 : 0 < p ^ i := pow_pos hp.out.pos i
  have hcard : ((range Y₀).filter (fun j : ℕ => ‖((progr t₀ d j : ℤ) : K) - ζ‖ < (p : ℝ) ^ (1 - (i : ℤ)))).card
      ≤ Y₀ / p ^ i + 1 := card_le_div_add_one_of_subset_range_of_mod_eq Y₀ (p ^ i) hq0 _ (Finset.filter_subset _ _) (by
    intro j hj j' hj'
    rw [Finset.mem_filter] at hj hj'
    have h1 : ‖((progr t₀ d j : ℤ) : K) - ((progr t₀ d j' : ℤ) : K)‖ < (p : ℝ) ^ (1 - (i : ℤ)) := by
      have h0 := norm_sub_le_max (((progr t₀ d j : ℤ) : K) - ζ) (((progr t₀ d j' : ℤ) : K) - ζ)
      rw [sub_sub_sub_cancel_right] at h0
      exact lt_of_le_of_lt h0 (max_lt hj.2 hj'.2)
    rw [← Int.cast_sub, progr_sub, norm_int (p := p)] at h1
    have h3 := dvd_cancel hd i (dvd_of_norm_lt _ i h1)
    have h4 : ((p ^ i : ℕ) : ℤ) ∣ (j' : ℤ) - j := by
      push_cast
      rw [← dvd_neg, neg_sub]
      exact h3
    exact Nat.modEq_iff_dvd.mpr h4)
  have h5 : ((Y₀ / p ^ i : ℕ) : ℝ) ≤ (Y₀ : ℝ) / (p : ℝ) ^ i := by
    have h6 := Nat.cast_div_le (α := ℝ) (m := Y₀) (n := p ^ i)
    push_cast at h6
    exact h6
  have h7 : ((((range Y₀).filter (fun j : ℕ => ‖((progr t₀ d j : ℤ) : K) - ζ‖ < (p : ℝ) ^ (1 - (i : ℤ)))).card : ℕ) : ℝ)
      ≤ ((Y₀ / p ^ i : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
  linarith
end Formalism.GM.ArithmeticProgressionDivisibility
