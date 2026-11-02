-- Prove2me | solution 1 for DiscreteConvex.EconomicEquilibriumB.swgs_iff_mnatural_concave
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:42:56.309648+00:00
-- url     : https://prove2.me/submissions/fcca9256-8f84-4b1f-8aaf-d96ce2c66288

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_UDom
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_MNaturalConcave
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsConcaveExtensible
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_NegSWGS

open Classical
open scoped Pointwise
open DiscreteConvex.EconomicEquilibriumB

private abbrev K0 : Type := ULift.{0} Bool

private def t0 : K0 := ⟨true⟩
private def f0 : K0 := ⟨false⟩

private lemma f0_ne_t0 : f0 ≠ t0 := by decide

private lemma sum_K0 {M : Type*} [AddCommMonoid M] (g : K0 → M) :
    ∑ v : K0, g v = g t0 + g f0 := by
  change ∑ v : ULift.{0} Bool, g v = g ⟨true⟩ + g ⟨false⟩
  rw [Fintype.sum_equiv Equiv.ulift (fun v => g v) (fun b => g ⟨b⟩) (fun _ => rfl)]
  exact Fintype.sum_bool (fun b => g ⟨b⟩)

private def vecA : K0 → ℤ := fun v => if v = t0 then 2 else 0
private def vecZ : K0 → ℤ := fun _ => 0

private def U1 : (K0 → ℤ) → WithBot ℝ :=
  fun x => if x t0 + x f0 ≠ 1 then ((0 : ℝ) : WithBot ℝ) else ⊥

private lemma mem_UDom_U1 (x : K0 → ℤ) : x ∈ UDom U1 ↔ x t0 + x f0 ≠ 1 := by
  simp [UDom, U1]

private lemma toERealOfBot_zero : ToERealOfBot ((0 : ℝ) : WithBot ℝ) = (0 : EReal) := rfl

private lemma U1_concave_extensible : IsConcaveExtensible U1 := by
  intro x hx
  have hUx : U1 x = ((0 : ℝ) : WithBot ℝ) := if_pos ((mem_UDom_U1 x).mp hx)
  rw [hUx, toERealOfBot_zero]
  unfold ConcaveClosureR
  apply le_antisymm
  · apply sInf_le
    refine ⟨fun _ => 0, 0, ?_, by simp⟩
    intro z
    by_cases hzx : z t0 + z f0 ≠ 1
    · have hUz : U1 z = ((0 : ℝ) : WithBot ℝ) := if_pos hzx
      rw [hUz, toERealOfBot_zero]
      simp
    · have hUz : U1 z = ⊥ := if_neg hzx
      rw [hUz]
      exact bot_le
  · apply le_sInf
    rintro _ ⟨p, α, h1, rfl⟩
    have h1x := h1 x
    rw [hUx, toERealOfBot_zero] at h1x
    exact h1x

private lemma vecZ_dom : vecZ t0 + vecZ f0 ≠ 1 := by
  simp [vecZ]

private lemma U1_dom_nonempty : (UDom U1).Nonempty :=
  ⟨vecZ, (mem_UDom_U1 vecZ).mpr vecZ_dom⟩

private lemma not_MNaturalConcave_U1 : ¬ MNaturalConcave U1 := by
  intro hm
  have ha : vecA ∈ UDom U1 := by
    rw [mem_UDom_U1]
    simp [vecA, if_neg f0_ne_t0]
  have hb : vecZ ∈ UDom U1 := (mem_UDom_U1 vecZ).mpr vecZ_dom
  have hi : t0 ∈ SuppPos vecA vecZ := by
    unfold SuppPos
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [vecA, vecZ]
  have h := hm.2 vecA ha vecZ hb t0 hi
  have bot_add_wb : ∀ a : WithBot ℝ, (⊥ : WithBot ℝ) + a = ⊥ := by
    intro a; cases a <;> rfl
  have hA1 : U1 (fun w => vecA w - (if w = t0 then (1 : ℤ) else 0)) = ⊥ := by
    unfold U1
    rw [if_neg]
    intro hne
    apply hne
    simp [vecA, if_neg f0_ne_t0]
  have hsup : (SuppNeg vecA vecZ).sup (fun j =>
      U1 (fun w => vecA w - (if w = t0 then (1 : ℤ) else 0) + (if w = j then (1 : ℤ) else 0)) +
        U1 (fun w => vecZ w + (if w = t0 then (1 : ℤ) else 0) - (if w = j then (1 : ℤ) else 0))) = ⊥ := by
    rw [Finset.sup_eq_bot_iff]
    intro j hj
    unfold SuppNeg at hj
    rw [Finset.mem_filter] at hj
    have hj2 := hj.2
    rcases j with ⟨_ | _⟩ <;> simp [vecA, vecZ, t0] at hj2
  have hUa : U1 vecA = ((0 : ℝ) : WithBot ℝ) := by
    unfold U1
    rw [if_pos]
    simp [vecA, if_neg f0_ne_t0]
  have hUb : U1 vecZ = ((0 : ℝ) : WithBot ℝ) := if_pos vecZ_dom
  rw [hUa, hUb, hA1, bot_add_wb, hsup, max_self, ← WithBot.coe_add, add_zero] at h
  exact WithBot.coe_ne_bot (le_bot_iff.mp h)

private lemma priceShift_of_mem_UDom (q : K0 → ℝ) (z : K0 → ℤ) (hz : z t0 + z f0 ≠ 1) :
    PriceShift U1 q z = ((- (q t0 * (z t0 : ℝ) + q f0 * (z f0 : ℝ)) : ℝ) : WithBot ℝ) := by
  unfold PriceShift
  have hUz : U1 z = ((0 : ℝ) : WithBot ℝ) := if_pos hz
  rw [hUz, sum_K0, ← WithBot.coe_add]
  congr 1
  ring

private lemma dom_and_eq_of_mem_argMax_U1 (q : K0 → ℝ) (x : K0 → ℤ)
    (hx : x ∈ ArgMaxBot (PriceShift U1 q)) : x t0 + x f0 ≠ 1 ∧ q t0 = q f0 := by
  have h0_le : PriceShift U1 q vecZ ≤ PriceShift U1 q x := hx vecZ
  rw [priceShift_of_mem_UDom q vecZ vecZ_dom] at h0_le
  have hx_dom : x t0 + x f0 ≠ 1 := by
    intro h_eq
    have hUx : U1 x = ⊥ := if_neg (not_not.mpr h_eq)
    have hPx : PriceShift U1 q x = ⊥ := by
      unfold PriceShift
      rw [hUx]
      rfl
    rw [hPx] at h0_le
    exact WithBot.coe_ne_bot (le_bot_iff.mp h0_le)
  let y1 : K0 → ℤ := fun k => if k = t0 then x t0 - 1 else x f0 + 1
  let y2 : K0 → ℤ := fun k => if k = t0 then x t0 + 1 else x f0 - 1
  have hy1_dom : y1 t0 + y1 f0 ≠ 1 := by
    simp only [y1, ↓reduceIte, if_neg f0_ne_t0]
    omega
  have hy2_dom : y2 t0 + y2 f0 ≠ 1 := by
    simp only [y2, ↓reduceIte, if_neg f0_ne_t0]
    omega
  have hy1_le : PriceShift U1 q y1 ≤ PriceShift U1 q x := hx y1
  have hy2_le : PriceShift U1 q y2 ≤ PriceShift U1 q x := hx y2
  rw [priceShift_of_mem_UDom q y1 hy1_dom, priceShift_of_mem_UDom q x hx_dom, WithBot.coe_le_coe] at hy1_le
  rw [priceShift_of_mem_UDom q y2 hy2_dom, priceShift_of_mem_UDom q x hx_dom, WithBot.coe_le_coe] at hy2_le
  simp only [y1, y2, ↓reduceIte, if_neg f0_ne_t0, Int.cast_sub, Int.cast_add, Int.cast_one] at hy1_le hy2_le
  exact ⟨hx_dom, by linarith⟩

private lemma NegSWGS_U1 : NegSWGS U1 := by
  intro p x hx i
  obtain ⟨hx_dom, hp⟩ := dom_and_eq_of_mem_argMax_U1 p x hx
  let y : K0 → ℤ := fun k => if k = i then x k - 1 else x k + 1
  have hp0 : (fun k => p k + (if k = i then (0 : ℝ) else 0)) = p := by
    funext k; simp
  refine Or.inr ⟨0, le_refl 0, y, ?_, ?_, ?_⟩
  · rw [hp0]
    have hy_dom : y t0 + y f0 ≠ 1 := by
      rcases i with ⟨_ | _⟩
      · change (if t0 = f0 then x t0 - 1 else x t0 + 1) + (if f0 = f0 then x f0 - 1 else x f0 + 1) ≠ 1
        simp only [if_neg (Ne.symm f0_ne_t0), ↓reduceIte]
        omega
      · change (if t0 = t0 then x t0 - 1 else x t0 + 1) + (if f0 = t0 then x f0 - 1 else x f0 + 1) ≠ 1
        simp only [↓reduceIte, if_neg f0_ne_t0]
        omega
    have hPy : PriceShift U1 p y = PriceShift U1 p x := by
      rw [priceShift_of_mem_UDom p y hy_dom, priceShift_of_mem_UDom p x hx_dom]
      congr 1
      rcases i with ⟨_ | _⟩
      · change - (p t0 * ↑(if t0 = f0 then x t0 - 1 else x t0 + 1) +
            p f0 * ↑(if f0 = f0 then x f0 - 1 else x f0 + 1)) =
          - (p t0 * ↑(x t0) + p f0 * ↑(x f0))
        simp only [if_neg (Ne.symm f0_ne_t0), ↓reduceIte, Int.cast_add, Int.cast_sub, Int.cast_one]
        linarith
      · change - (p t0 * ↑(if t0 = t0 then x t0 - 1 else x t0 + 1) +
            p f0 * ↑(if f0 = t0 then x f0 - 1 else x f0 + 1)) =
          - (p t0 * ↑(x t0) + p f0 * ↑(x f0))
        simp only [↓reduceIte, if_neg f0_ne_t0, Int.cast_add, Int.cast_sub, Int.cast_one]
        linarith
    intro w
    rw [hPy]
    exact hx w
  · simp [y]
  · intro j hj
    simp only [y, if_neg hj]
    omega

theorem solution :
    ¬ (∀ {K : Type} [Fintype K] [DecidableEq K] (U : (K → ℤ) → WithBot ℝ),
      IsConcaveExtensible U →
      (UDom U).Nonempty →
      (MNaturalConcave U ↔ NegSWGS U)) := by
  intro h
  have hiff := @h K0 _ _ U1 U1_concave_extensible U1_dom_nonempty
  exact not_MNaturalConcave_U1 (hiff.mpr NegSWGS_U1)
