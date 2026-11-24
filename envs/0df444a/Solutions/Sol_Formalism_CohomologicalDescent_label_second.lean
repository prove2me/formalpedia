-- Prove2me | solution 1 for Formalism.CohomologicalDescent.label_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:07:14.710941+00:00
-- url     : https://prove2.me/submissions/4481f113-722a-45f4-8cdd-ffa8d8091499

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Theorems.Thm_Formalism_CohomologicalDescent_label_sum_le_filter
import Theorems.Thm_Formalism_CohomologicalDescent_leastCongruentPos_mem
import Theorems.Thm_Formalism_CohomologicalDescent_leastCongruentPos_le
import Theorems.Thm_Formalism_CohomologicalDescent_label_harm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
open Classical
namespace Formalism.CohomologicalDescent
theorem _root_.solution {l k t h : ℕ} {i : ℝ} {xm mB : ℤ} (hl : l.Prime) (hi : 0 ≤ i)
    (hmB : 0 ≤ mB) (hmx : mB < xm) (hxh : xm ≤ (h : ℤ)) (hh : h < l ^ 2) (hlh : l ≤ 2 * h) :
    ∑ ct ∈ Finset.Ioo mB xm,
      min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ)) * (vl l (ct - mB) : ℝ)
    ≤ (if ((d0 l (xm - mB) : ℕ) : ℤ) < xm - mB then
        min (min (k : ℝ) (t : ℝ)) (i / (d0 l (xm - mB) : ℝ)) else 0) +
      (i / (l : ℝ)) * (1 + Real.log ((h : ℝ) / (l : ℝ))) := by
  have hlpos : 0 < l := hl.pos
  have hlZ : (0 : ℤ) < l := by exact_mod_cast hlpos
  have hlR : (0 : ℝ) < l := by exact_mod_cast hlpos
  have hhZ : (h : ℤ) < (l : ℤ) ^ 2 := by exact_mod_cast hh
  have hm0 : (0 : ℝ) ≤ min (k : ℝ) (t : ℝ) := le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨hd01, hd0dvd⟩ := leastCongruentPos_mem hlpos (xm - mB) (by omega)
  obtain ⟨d0, hd0⟩ : ∃ d0, d0 = Formalism.CohomologicalDescent.d0 l (xm - mB) := ⟨_, rfl⟩
  rw [← hd0] at hd01 hd0dvd ⊢
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = if ((d0 : ℕ) : ℤ) < xm - mB then
      min (min (k : ℝ) (t : ℝ)) (i / (d0 : ℝ)) else 0 := ⟨_, rfl⟩
  rw [← hA]
  have hA0 : 0 ≤ A := by
    rw [hA]
    split_ifs
    · exact le_min hm0 (div_nonneg hi (Nat.cast_nonneg _))
    · exact le_refl 0
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ, ∀ j, F j = if j = 0 then A else i / ((l : ℝ) * (j : ℝ)) :=
    ⟨_, fun _ => rfl⟩
  have hF0 : ∀ j, 0 ≤ F j := by
    intro j
    rw [hF]
    split_ifs
    · exact hA0
    · exact div_nonneg hi (mul_nonneg hlR.le (Nat.cast_nonneg _))
  have hc : ∀ ct ∈ Finset.Ioo mB xm, 0 ≤ min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ)) := by
    intro ct hct
    rw [Finset.mem_Ioo] at hct
    have hpos : (0 : ℝ) < ((xm - ct : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < xm - ct)
    exact le_min hm0 (div_nonneg hi hpos.le)
  have hr : ∀ ct ∈ Finset.Ioo mB xm, 0 < ct - mB ∧ ct - mB < (l : ℤ) ^ 2 := by
    intro ct hct
    rw [Finset.mem_Ioo] at hct
    exact ⟨by omega, by linarith [hct.2]⟩
  have step1 := label_sum_le_filter hl (Finset.Ioo mB xm) mB
    (fun ct => min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ))) hc hr
  refine le_trans step1 ?_
  obtain ⟨S, hS⟩ : ∃ S, S = (Finset.Ioo mB xm).filter (fun x => (l : ℤ) ∣ x - mB) := ⟨_, rfl⟩
  rw [← hS]
  have key : ∀ ct ∈ S, (l : ℤ) ∣ xm - ct - d0 ∧ (d0 : ℤ) ≤ xm - ct ∧ mB < ct ∧ ct < xm := by
    intro ct hct
    rw [hS, Finset.mem_filter, Finset.mem_Ioo] at hct
    obtain ⟨⟨h1, h2⟩, h3⟩ := hct
    refine ⟨?_, ?_, h1, h2⟩
    · have e : xm - ct - (d0 : ℤ) = (xm - mB - d0) - (ct - mB) := by ring
      rw [e]
      exact dvd_sub hd0dvd h3
    · have hnn : ((xm - ct).toNat : ℤ) = xm - ct := Int.toNat_of_nonneg (by omega)
      have e : xm - mB - (((xm - ct).toNat : ℕ) : ℤ) = ct - mB := by
        rw [hnn]
        ring
      have hle := leastCongruentPos_le (l := l) (xm - mB) (xm - ct).toNat (by omega)
        (by rw [e]; exact h3)
      rw [← hd0] at hle
      have hle' : (d0 : ℤ) ≤ ((xm - ct).toNat : ℤ) := by exact_mod_cast hle
      rw [hnn] at hle'
      exact hle'
  obtain ⟨g, hg⟩ : ∃ g : ℤ → ℕ, ∀ ct, g ct = ((xm - ct - d0) / (l : ℤ)).toNat :=
    ⟨_, fun _ => rfl⟩
  have hgZ : ∀ ct ∈ S, (l : ℤ) * (g ct : ℤ) = xm - ct - d0 := by
    intro ct hct
    obtain ⟨hdv, hle, -, -⟩ := key ct hct
    rw [hg, Int.toNat_of_nonneg (Int.ediv_nonneg (by omega) hlZ.le)]
    exact Int.mul_ediv_cancel' hdv
  have hterm : ∀ ct ∈ S, min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ)) ≤ F (g ct) := by
    intro ct hct
    obtain ⟨-, hle, h1, h2⟩ := key ct hct
    have he := hgZ ct hct
    rw [hF]
    split_ifs with h0
    · rw [h0] at he
      have hd : xm - ct = (d0 : ℤ) := by push_cast at he; linarith
      have hlt : ((d0 : ℕ) : ℤ) < xm - mB := by omega
      rw [hA, if_pos hlt]
      have hdR : ((xm - ct : ℤ) : ℝ) = (d0 : ℝ) := by rw [hd]; norm_cast
      rw [hdR]
    · have hd0nn : (0 : ℤ) ≤ (d0 : ℤ) := by positivity
      have hle' : (l : ℤ) * (g ct : ℤ) ≤ xm - ct := by linarith
      have hprodR : (l : ℝ) * (g ct : ℝ) ≤ ((xm - ct : ℤ) : ℝ) := by exact_mod_cast hle'
      have hgR : (0 : ℝ) < (g ct : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
      have hprodpos : (0 : ℝ) < (l : ℝ) * (g ct : ℝ) := mul_pos hlR hgR
      exact (min_le_right _ _).trans (div_le_div_of_nonneg_left hi hprodpos hprodR)
  have hmaps : ∀ ct ∈ S, g ct ∈ Finset.range (h / l + 1) := by
    intro ct hct
    obtain ⟨-, hle, h1, h2⟩ := key ct hct
    have he := hgZ ct hct
    rw [Finset.mem_range, Nat.lt_add_one_iff, Nat.le_div_iff_mul_le hlpos]
    have hz : ((g ct * l : ℕ) : ℤ) ≤ (h : ℤ) := by
      push_cast
      have hd0nn : (0 : ℤ) ≤ (d0 : ℤ) := by positivity
      linarith
    exact_mod_cast hz
  have hinj : ∀ a ∈ S, ∀ b ∈ S, g a = g b → a = b := by
    intro a ha b hb hab
    have h1 := hgZ a ha
    have h2 := hgZ b hb
    rw [hab] at h1
    linarith
  have hH : ∑ j ∈ Finset.range (h / l), F (j + 1) = (i / l) * ((harmonic (h / l) : ℚ) : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF, if_neg (by omega)]
    push_cast
    field_simp
  have hlog := label_harm_le hlpos hlh
  have hil : 0 ≤ i / (l : ℝ) := div_nonneg hi hlR.le
  have hmul := mul_le_mul_of_nonneg_left hlog hil
  calc ∑ x ∈ S, min (min (k : ℝ) (t : ℝ)) (i / ((xm - x : ℤ) : ℝ))
      ≤ ∑ x ∈ S, F (g x) := Finset.sum_le_sum hterm
    _ = ∑ j ∈ S.image g, F j := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        exact hinj a ha b hb hab
    _ ≤ ∑ j ∈ Finset.range (h / l + 1), F j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps)
          (fun j _ _ => hF0 j)
    _ = ∑ j ∈ Finset.range (h / l), F (j + 1) + F 0 := Finset.sum_range_succ' _ _
    _ = (i / l) * ((harmonic (h / l) : ℚ) : ℝ) + A := by rw [hH, hF 0, if_pos rfl]
    _ ≤ A + (i / (l : ℝ)) * (1 + Real.log ((h : ℝ) / (l : ℝ))) := by linarith
end Formalism.CohomologicalDescent
