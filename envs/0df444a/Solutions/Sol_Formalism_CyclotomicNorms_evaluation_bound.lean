-- Prove2me | solution 1 for Formalism.CyclotomicNorms.evaluation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:32.5896+00:00
-- url     : https://prove2.me/submissions/5b1bf076-ddb9-4c93-882d-914b9f1840f2

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Newton
import Theorems.Thm_Formalism_CyclotomicNorms_NewtonPolygonValuation_val_zeta_sub_one
import Theorems.Thm_Formalism_CyclotomicNorms_NewtonPolygonValuation_val_sum_eq_of_lt
import Theorems.Thm_Formalism_CyclotomicNorms_NewtonPolygonValuation_wt_lt_add
import Theorems.Thm_Formalism_CyclotomicNorms_NewtonPolygonValuation_val_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms
open NewtonPolygonValuation
namespace Formalism.CyclotomicNorms
theorem _root_.solution : Evaluation := by
  intro L _ v ℓ e w j F z hℓ he hv hcoef hunit hz hφw
  classical
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, IsPrimitiveRoot.one_right_iff] at hz
    subst hz
    have hw : w = 0 := by
      rw [pow_zero, Nat.totient_one, Nat.cast_one] at hφw
      have : e * w < 1 := by exact_mod_cast hφw
      rcases Nat.eq_zero_or_pos w with h | h
      · exact h
      · exact absurd this (by have := Nat.mul_le_mul he h; omega)
    subst hw
    obtain ⟨i, hi, hvi⟩ := hunit
    obtain rfl : i = 0 := by omega
    rw [sub_self, ← coeff_zero_eq_eval_zero, hvi]
    simp
  · set φ : ℝ := ((ℓ ^ j).totient : ℝ) with hφdef
    have hφpos : (0 : ℝ) < φ := by
      rw [hφdef]; exact_mod_cast Nat.totient_pos.2 (pow_pos hℓ.pos j)
    have hepos : (0 : ℝ) < e := by exact_mod_cast he
    set t : ℝ := 1 / φ with htdef
    have htpos : 0 < t := by positivity
    have hx : v (z - 1) = wt t := val_zeta_sub_one v hℓ hj hv hz
    have hex : ∃ i, i ≤ w ∧ v (F.coeff i) = wt 0 := by
      obtain ⟨i, hi, h⟩ := hunit; exact ⟨i, hi, h⟩
    set i₀ := Nat.find hex with hi₀def
    have hi₀w : i₀ ≤ w := (Nat.find_spec hex).1
    have hi₀v : v (F.coeff i₀) = wt 0 := (Nat.find_spec hex).2
    have hlow : ∀ i < i₀, wt (1 / e) ≤ v (F.coeff i) := by
      intro i hi
      have hn := Nat.find_min hex hi
      rcases hcoef i with h | h
      · exact absurd ⟨by omega, h⟩ hn
      · exact h
    have hnn : ∀ i, (0 : WithTop ℝ) ≤ v (F.coeff i) := by
      intro i
      rcases hcoef i with h | h
      · rw [h]; rfl
      · refine le_trans ?_ h
        exact WithTop.coe_le_coe.2 (by positivity)
    have hwt : (w : ℝ) * t < 1 / e := by
      have h1 : ((e * w : ℕ) : ℝ) < φ := hφw
      push_cast at h1
      rw [htdef, lt_div_iff₀ hepos]
      rw [mul_one_div, div_mul_eq_mul_div, div_lt_one hφpos]
      linarith
    have hne0 : F.coeff i₀ ≠ 0 := by
      rw [← AddValuation.ne_top_iff v, hi₀v]; exact WithTop.coe_ne_top
    have hmem : i₀ ∈ range (F.natDegree + 1) :=
      mem_range.2 (Nat.lt_succ_of_le (le_natDegree_of_ne_zero hne0))
    rw [eval_eq_sum_range]
    rw [val_sum_eq_of_lt v hmem ?_ ?_]
    · rw [val_term v hx, hi₀v, ← WithTop.coe_add, zero_add]
      apply WithTop.coe_le_coe.2
      rw [htdef, mul_one_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hi₀w) hφpos.le
    · rw [val_term v hx, hi₀v, ← WithTop.coe_add]; exact WithTop.coe_ne_top
    · intro i hi
      have hii : i ≠ i₀ := (mem_erase.1 hi).1
      rw [val_term v hx, val_term v hx, hi₀v, ← WithTop.coe_add, zero_add]
      apply wt_lt_add
      intro r hr
      rcases lt_or_gt_of_ne hii with h | h
      · have h1 := hlow i h
        rw [hr] at h1
        have h1' : 1 / (e : ℝ) ≤ r := WithTop.coe_le_coe.1 h1
        have : (i₀ : ℝ) * t ≤ w * t :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hi₀w) htpos.le
        have : (0 : ℝ) ≤ i * t := by positivity
        linarith
      · have h1 := hnn i
        rw [hr] at h1
        have h1' : (0 : ℝ) ≤ r := WithTop.coe_le_coe.1 h1
        have : (i₀ : ℝ) * t < i * t :=
          mul_lt_mul_of_pos_right (by exact_mod_cast h) htpos
        linarith
end Formalism.CyclotomicNorms
