-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.JmuHC.numHC_addI_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:36:17.519425+00:00
-- url     : https://prove2.me/submissions/887e4503-b1c8-4b2c-9a43-7728b750e7b1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJmuHC
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_JmuHC_prod_ratio_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_JmuHC_sq_prod_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.JmuHC
open Finset
variable {n : ℕ}
namespace Formalism.FourierDecayAlt.P.CutBP.JmuHC
theorem _root_.solution (x : Fin n → ℝ) (hinj : Function.Injective x) (hint : ∀ a b, ∃ m : ℤ, x a - x b = m)
    (I : Finset (Fin n)) :
    numHC (fun i => x i + if i ∈ I then 1 else 0) ≤ (n : ℝ) ^ I.card * numHC x := by
  classical
  set y : Fin n → ℝ := fun i => x i + if i ∈ I then 1 else 0 with hydef
  set f : Fin n → Fin n → ℝ := fun a b => |y a - y b| / |x a - x b| with hf
  have hx0 : ∀ a b, a ≠ b → |x a - x b| ≠ 0 := fun a b h =>
    abs_ne_zero.2 (sub_ne_zero.2 fun e => h (hinj e))
  have hfs : ∀ a b, f a b = f b a := fun a b => by simp only [hf, abs_sub_comm]
  have hy : ∀ a b, a ≠ b → |y a - y b| = f a b * |x a - x b| := fun a b h => by
    simp only [hf]; rw [div_mul_cancel₀ _ (hx0 a b h)]
  have hf1 : ∀ a b, a ≠ b → (a ∈ I ↔ b ∈ I) → f a b = 1 := by
    intro a b h hab
    simp only [hf, hydef]
    have : (x a + if a ∈ I then 1 else 0) - (x b + if b ∈ I then 1 else 0) = x a - x b := by
      by_cases ha : a ∈ I
      · rw [if_pos ha, if_pos (hab.1 ha)]; ring
      · rw [if_neg ha, if_neg (fun hb => ha (hab.2 hb))]; ring
    rw [this, div_self (hx0 a b h)]
  have hsqy : numHC y ^ 2 = ∏ a : Fin n, ∏ b ∈ univ.erase a, |y a - y b| :=
    sq_prod_lt _ fun a b => abs_sub_comm _ _
  have hsqx : numHC x ^ 2 = ∏ a : Fin n, ∏ b ∈ univ.erase a, |x a - x b| :=
    sq_prod_lt _ fun a b => abs_sub_comm _ _
  have hsplit : ∏ a : Fin n, ∏ b ∈ univ.erase a, |y a - y b| =
      (∏ a : Fin n, ∏ b ∈ univ.erase a, f a b) * numHC x ^ 2 := by
    rw [hsqx, ← prod_mul_distrib]
    refine prod_congr rfl fun a _ => ?_
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun b hb => hy a b (ne_of_mem_erase hb).symm
  set Pr := ∏ s ∈ I, ∏ t ∈ univ \ I, f s t with hPr
  have hff : ∏ a : Fin n, ∏ b ∈ univ.erase a, f a b = Pr ^ 2 := by
    have hin : ∀ a ∈ I, ∏ b ∈ univ.erase a, f a b = ∏ b ∈ univ \ I, f a b := by
      intro a ha
      symm
      apply prod_subset
      · intro b hb
        rw [mem_sdiff] at hb
        exact mem_erase.2 ⟨fun e => hb.2 (e ▸ ha), mem_univ b⟩
      · intro b hb hb'
        have hba : b ≠ a := ne_of_mem_erase hb
        have hbI : b ∈ I := by
          by_contra h
          exact hb' (mem_sdiff.2 ⟨mem_univ b, h⟩)
        exact hf1 a b hba.symm ⟨fun _ => hbI, fun _ => ha⟩
    have hout : ∀ a ∉ I, ∏ b ∈ univ.erase a, f a b = ∏ b ∈ I, f a b := by
      intro a ha
      symm
      apply prod_subset
      · intro b hb
        exact mem_erase.2 ⟨fun e => ha (e ▸ hb), mem_univ b⟩
      · intro b hb hb'
        have hba : b ≠ a := ne_of_mem_erase hb
        exact hf1 a b hba.symm ⟨fun h => absurd h ha, fun h => absurd h hb'⟩
    rw [← prod_filter_mul_prod_filter_not univ (fun a => a ∈ I)]
    have e1 : univ.filter (fun a : Fin n => a ∈ I) = I := by ext a; simp
    have e2 : univ.filter (fun a : Fin n => a ∉ I) = univ \ I := by ext a; simp
    rw [e1, e2, prod_congr rfl hin, prod_congr rfl (fun a ha => hout a (mem_sdiff.1 ha).2)]
    have hC : ∏ a ∈ univ \ I, ∏ b ∈ I, f a b = ∏ b ∈ I, ∏ a ∈ univ \ I, f a b := prod_comm
    rw [hC, sq]
    congr 1
    exact prod_congr rfl fun s _ => prod_congr rfl fun t _ => hfs t s
  have hP0 : 0 ≤ Pr := prod_nonneg fun s _ => prod_nonneg fun t _ => by positivity
  have hPn : Pr ≤ (n : ℝ) ^ I.card := by
    rw [← prod_const]
    refine prod_le_prod (fun s _ => prod_nonneg fun t _ => by positivity) fun s hs => ?_
    have e : ∏ t ∈ univ \ I, f s t = ∏ t ∈ univ \ I, |x s + 1 - x t| / |x s - x t| := by
      refine prod_congr rfl fun t ht => ?_
      have htI : t ∉ I := (mem_sdiff.1 ht).2
      simp only [hf, hydef, if_pos hs, if_neg htI]
      congr 1
      ring_nf
    rw [e]
    exact prod_ratio_le x hinj hint s (univ \ I) (fun h => (mem_sdiff.1 h).2 hs)
  have hny : 0 ≤ numHC y := prod_nonneg fun a _ => prod_nonneg fun b _ => abs_nonneg _
  have hnx : 0 ≤ numHC x := prod_nonneg fun a _ => prod_nonneg fun b _ => abs_nonneg _
  have hsq : numHC y ^ 2 ≤ ((n : ℝ) ^ I.card * numHC x) ^ 2 := by
    rw [hsqy, hsplit, hff, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hP0 hPn 2) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ hny (by positivity) two_ne_zero).1 hsq
end Formalism.FourierDecayAlt.P.CutBP.JmuHC
