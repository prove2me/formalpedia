-- Prove2me | solution 1 for BooleanFun.BV.eq_character_of_eq_sum_degree_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:11:50.451482+00:00
-- url     : https://prove2.me/submissions/4a31189b-228c-43ba-ada8-8bc42fe7f576

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
import Theorems.Thm_BooleanFun_BV_eq_neg_one_of_ne_one
import Theorems.Thm_BooleanFun_BV_neg_boolean_valued
import Theorems.Thm_BooleanFun_flipAt_unflipped
import Theorems.Thm_BooleanFun_walsh_inner_eq


set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV
namespace BooleanFun.BV
theorem _root_.solution (hbv : BooleanValued f) (hn : n>0)
    (hf : ∀ x, f x = ∑ i, 𝓕 f {i} * (-1)^(x i).val):
    ∃ S ∈ {S|S.card = 1}, ∃ c : ℝ, f = c•χ S := by
-- Unfortunately a bit lengthy
  wlog hf1 : f 0 = 1 with h1
  { -- replace f by -f
    -- have h' : IsBooleanValued (-f) := neg_is_boolean_valued (h := h)
    have hf' : ∀ x, (-f) x = ∑ i, 𝓕 (-f) {i} * (-1)^(x i).val := by intro x; simp; exact hf x
    have : (-f) 0 = 1 := by
      rw [Pi.neg_apply, neg_eq_iff_eq_neg]
      exact eq_neg_one_of_ne_one hbv hf1
    specialize h1 (neg_boolean_valued hbv) hn hf' this
    obtain ⟨S, hS0, hS1⟩ := h1
    obtain ⟨c, hc⟩ := hS1
    use S
    constructor
    · assumption
    · use -c
      rw [neg_smul, ← hc, neg_neg]
  }

  cases n with
  | zero => contradiction
  | succ n =>
    induction n with
    | zero => -- only one coordinate
      use {0}
      simp
      use 1
      simp
      ext x
      rw [hf] at hf1
      simp at hf1
      rw [hf]
      simpa
    | succ n hi => -- will reduce one coordinate
      have hf0eq : f 0 = ∑ i, 𝓕 f {i} := by
        rw [hf]
        apply sum_congr (by rfl)
        intro i _
        simp
      have hf0feq : ∀ i₀, f (flipAt i₀ 0) = ∑ i ∈ univ.erase i₀, 𝓕 f {i} + -𝓕 f {i₀} := by
        intro i₀
        rw [hf]
        rw [← sum_erase_add (a := i₀)]
        congr 1
        · apply sum_congr (by rfl)
          intro i hi
          rw [flipAt_unflipped (h := ne_of_mem_erase hi)]
          rw [Pi.zero_apply, Fin.val_zero, pow_zero, mul_one]
        · rw [flipAt_flipped]
          rw [Pi.zero_apply, sub_zero, Fin.val_one, pow_one, mul_neg, mul_one]
        · exact mem_univ i₀
      -- key step:
      have : ∃ i₀, f (flipAt i₀ 0) = 1 := by
        by_contra hc -- suppose not
        have hfm1 : ∀i, f (flipAt i 0) = -1 := by
          intro i
          exact eq_neg_one_of_ne_one hbv ((not_exists.mp hc) i)
        have : ∀ i, 𝓕 f {i} = 1 := by
          intro i; symm
          calc
            1 = (1 - (-1))/2              := by norm_num
            _ = (f 0 - f (flipAt i 0))/2 := by rw [hf1, hfm1]
            _ = (∑ i', 𝓕 f {i'} - ∑ i' ∈ univ.erase i, 𝓕 f {i'} + 𝓕 f {i})/2 := by rw [hf0eq, hf0feq]; ring
            _ = _                         := by rw [← sum_erase_add (a := i)]; ring; exact mem_univ i
        have : f 0 = n + 2 := by
          rw [hf0eq]
          conv => enter [1, 2, i]; rw [this]
          simp; ring
        have : (1 : ℝ) ≥ 2 := by
          calc
            1 = f 0   := by symm; exact hf1
            _ = n + 2 := by exact this
            _ ≥ 0 + 2 := by gcongr; exact Nat.cast_nonneg n
            _ = 2     := by simp
        have : ¬(1 : ℝ)≥2  := by simp
        exact this (by assumption)
      obtain ⟨i₀, hi₀⟩ := this -- this coordinate must have zero coefficient
      have hFi0zero : 𝓕 f {i₀} = 0 := by
        symm
        calc
          0 = (1 - 1)/2                  := by ring
          _ = (f 0 - f (flipAt i₀ 0))/2 := by rw [hf1, hi₀]
          _ = ((∑ i, 𝓕 f {i} - ∑ i ∈ univ.erase i₀, 𝓕 f {i}) + 𝓕 f {i₀})/2 := by rw [hf0eq, hf0feq]; ring
          _ = 𝓕 f {i₀} := by rw [← sum_erase_add (a := i₀) (h := mem_univ i₀)]; ring
      -- apply inductive hypothesis to the fiber with i₀ coordinate fixed
      let g : BooleanFunc (n + 1) := fun x ↦ f (Fin.insertNth i₀ 0 x)
      have hgeq : g = ∑ i, 𝓕 f {i₀.succAbove i}•χ {i} := by
        ext x
        simp [g]
        nth_rewrite 1 [hf]
        rw [← sum_erase_add (a := i₀), hFi0zero, zero_mul, add_zero]
        symm
        apply sum_of_injOn (e := fun i ↦ i₀.succAbove i)
        · intro i _ j _
          dsimp
          exact succAbove_right_inj.mp
        · unfold Set.MapsTo
          intro i _
          simp
        · intro i hi0 hi1
          simp at hi1
          simp at hi0
          contradiction
        · intro i _
          simp
        · exact mem_univ i₀
      have : ∀ i, 𝓕 g {i} = 𝓕 f {i₀.succAbove i} := by
        intro i
        calc
          _ = ⟪χ {i}, g⟫       := by rfl
          _ = ⟪χ {i}, ∑ i, 𝓕 f {i₀.succAbove i}•χ {i}⟫ := by rw [hgeq]
          _ = ∑ i', 𝓕 f {i₀.succAbove i'} * ⟪χ {i}, χ {i'}⟫ := by
            rw [inner_sum]; conv => enter[1, 2, i']; rw [inner_smul_right]
          _ = 𝓕 f {i₀.succAbove i}                     := by
            (conv => enter [1, 2, i']; rw [walsh_inner_eq]); simp
      have hgeq' : ∀ x, g x = ∑ i, 𝓕 g {i} * (-1)^(x i).val := by
        intro x; nth_rewrite 1 [hgeq]; rw [Finset.sum_apply]; apply sum_congr (by rfl); intro i _; simp [this]
      have : g 0 = 1 := by unfold g; simp; exact hf1
      have : BooleanValued g := BooleanValued.mk
        (by intro x; exact hbv.one_or_neg_one (Fin.insertNth i₀ 0 x))
      have := hi (f := g) this (Nat.succ_pos n) (by assumption) (by assumption)
      obtain ⟨S, hS1, hS2⟩ := this
      obtain ⟨c, hc⟩ := hS2
      simp at hS1
      obtain ⟨i₁, hi₁⟩ := card_eq_one.mp hS1
      use {Fin.succAbove i₀ i₁}
      constructor
      · simp
      · use c
        funext x
        simp
        -- f is independent of i₀-coordinate
        have hfxi : f x = f (update x i₀ 0) := by
          calc
            f x = ∑ i, 𝓕 f {i} * (-1)^(x i).val := by rw [hf]
            _  = ∑ i ∈ univ.erase i₀, 𝓕 f {i} * (-1)^(x i).val + 𝓕 f {i₀} * (-1)^(x i₀).val := by
              rw [sum_erase_add (h := mem_univ i₀)]
            _  = ∑ i ∈ univ.erase i₀, 𝓕 f {i} * (-1)^(x i).val +   0 * (-1)^(update x i₀ 0 i₀).val := by
              rw [hFi0zero]; simp
            _  = ∑ i ∈ univ.erase i₀, 𝓕 f {i} * (-1)^(update x i₀ 0 i).val +   0 * (-1)^(update x i₀ 0 i₀).val := by
              congr 1; apply sum_congr (by rfl); intro i hi; apply ne_of_mem_erase at hi; rw [update_of_ne hi]
            _ = _ := by
              rw [← hFi0zero, sum_erase_add (h := mem_univ i₀), ← hf]
        calc
          _ = f (Fin.insertNth i₀ 0 (Fin.removeNth i₀ x))  := by rw [hfxi, Fin.insertNth_removeNth]
          _ = g (Fin.removeNth i₀ x)                      := by rfl
          _ = (c•χ {i₁}) (Fin.removeNth i₀ x)             := by rw [hc, hi₁]
          _ = _                                           := by simp; left; rfl
end BooleanFun.BV
