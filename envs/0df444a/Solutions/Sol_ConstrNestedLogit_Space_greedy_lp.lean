-- Prove2me | solution 1 for ConstrNestedLogit.Space.greedy_lp
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T19:47:26.784533+00:00
-- url     : https://prove2.me/submissions/bed2909e-8261-4f2d-a5a6-1c08051dbd80

import Mathlib
import Definitions.Def_ConstrNestedLogit_Space_Model

set_option autoImplicit false

namespace FractionalKnapsack

structure Certificate {α : Type*} (S : Finset α) (w a : α → ℝ) (c R : ℝ) where
  x : α → ℝ
  lam : ℝ
  lam_nonneg : 0 ≤ lam
  lam_le : lam ≤ R
  outside : ∀ j, j ∉ S → x j = 0
  box : ∀ j, 0 ≤ x j ∧ x j ≤ 1
  feasible : (∑ j ∈ S, w j * x j) ≤ c
  complement : lam = 0 ∨ (∑ j ∈ S, w j * x j) = c
  positive : ∀ j, 0 < x j → 0 < a j
  lower : ∀ j ∈ S, 0 < x j → lam ≤ a j / w j
  upper : ∀ j ∈ S, x j < 1 → a j / w j ≤ lam
  fractional : ∀ j k, 0 < x j → x j < 1 → 0 < x k → x k < 1 → j = k

theorem update_sum {α : Type*} [DecidableEq α] (S : Finset α) (p : α)
    (hp : p ∈ S) (w y : α → ℝ) (t : ℝ) :
    (∑ j ∈ S, w j * Function.update y p t j) =
      (∑ j ∈ S.erase p, w j * y j) + w p * t := by
  rw [← Finset.sum_erase_add _ _ hp]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    simp [Function.update, (Finset.mem_erase.mp hj).1]
  · simp

theorem build {α : Type*} [DecidableEq α] (S : Finset α) (w a : α → ℝ)
    (hw : ∀ j, 0 < w j) (c R : ℝ) (hc : 0 ≤ c) (hR : 0 ≤ R)
    (hbound : ∀ j ∈ S, a j / w j ≤ R) : Nonempty (Certificate S w a c R) := by
  classical
  induction S using Finset.strongInductionOn generalizing c R with
  | _ S ih =>
    by_cases hpos : ∃ z ∈ S, 0 < a z
    · obtain ⟨z, hz, haz⟩ := hpos
      obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S (fun j => a j / w j) ⟨z, hz⟩
      have hratio : 0 < a p / w p := (div_pos haz (hw z)).trans_le (hmax z hz)
      have hap : 0 < a p := by simpa using (lt_div_iff₀ (hw p)).mp hratio
      by_cases hcap : w p ≤ c
      · obtain ⟨T⟩ := ih (S.erase p) (Finset.erase_ssubset hp) (c - w p) (a p / w p)
          (sub_nonneg.mpr hcap) hratio.le (fun j hj => hmax j (Finset.mem_erase.mp hj).2)
        let x := Function.update T.x p 1
        have hsum : (∑ j ∈ S, w j * x j) = (∑ j ∈ S.erase p, w j * T.x j) + w p := by
          simpa [x] using update_sum S p hp w T.x 1
        refine ⟨{
          x := x, lam := T.lam, lam_nonneg := T.lam_nonneg,
          lam_le := T.lam_le.trans (hbound p hp), outside := ?_, box := ?_,
          feasible := ?_, complement := ?_, positive := ?_, lower := ?_, upper := ?_,
          fractional := ?_ }⟩
        · intro j hj
          have hjp : j ≠ p := fun e => hj (e ▸ hp)
          simp only [x, Function.update_of_ne hjp]
          exact T.outside j (fun h => hj (Finset.mem_erase.mp h).2)
        · intro j
          by_cases hj : j = p
          · subst j; simp [x]
          · simpa [x, hj] using T.box j
        · rw [hsum]; linarith [T.feasible]
        · rcases T.complement with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [hsum]; linarith)
        · intro j hj
          by_cases hjp : j = p
          · subst j; exact hap
          · apply T.positive j
            simpa [x, hjp] using hj
        · intro j hj hjx
          by_cases hjp : j = p
          · subst j; exact T.lam_le
          · exact T.lower j (Finset.mem_erase.mpr ⟨hjp, hj⟩) (by simpa [x, hjp] using hjx)
        · intro j hj hjx
          by_cases hjp : j = p
          · subst j; simp [x] at hjx
          · exact T.upper j (Finset.mem_erase.mpr ⟨hjp, hj⟩) (by simpa [x, hjp] using hjx)
        · intro j k hj0 hj1 hk0 hk1
          have hjp : j ≠ p := by intro e; subst j; simp [x] at hj1
          have hkp : k ≠ p := by intro e; subst k; simp [x] at hk1
          exact T.fractional j k (by simpa [x, hjp] using hj0)
            (by simpa [x, hjp] using hj1) (by simpa [x, hkp] using hk0)
            (by simpa [x, hkp] using hk1)
      · let x : α → ℝ := Function.update (fun _ => 0) p (c / w p)
        have hsum : (∑ j ∈ S, w j * x j) = c := by
          rw [show x = Function.update (fun _ => 0) p (c / w p) from rfl,
            update_sum S p hp]
          simp [mul_div_cancel₀, ne_of_gt (hw p)]
        refine ⟨{
          x := x, lam := a p / w p, lam_nonneg := hratio.le,
          lam_le := hbound p hp, outside := ?_, box := ?_, feasible := hsum.le,
          complement := Or.inr hsum, positive := ?_, lower := ?_, upper := ?_,
          fractional := ?_ }⟩
        · intro j hj
          have hjp : j ≠ p := fun e => hj (e ▸ hp)
          simp [x, hjp]
        · intro j
          by_cases hj : j = p
          · subst j
            simpa [x] using And.intro (div_nonneg hc (hw p).le)
              ((div_le_one (hw p)).2 (le_of_not_ge hcap))
          · simp [x, hj]
        · intro j hj
          by_cases hjp : j = p
          · subst j; exact hap
          · simp [x, hjp] at hj
        · intro j hj hjx
          by_cases hjp : j = p
          · subst j; rfl
          · simp [x, hjp] at hjx
        · intro j hj _
          exact hmax j hj
        · intro j k hj0 _ hk0 _
          have hjp : j = p := by by_contra h; simp [x, h] at hj0
          have hkp : k = p := by by_contra h; simp [x, h] at hk0
          exact hjp.trans hkp.symm
    · refine ⟨{
        x := fun _ => 0, lam := 0, lam_nonneg := le_rfl,
        lam_le := hR, outside := by simp, box := by simp,
        feasible := by simpa using hc, complement := Or.inl rfl,
        positive := by simp, lower := by simp, upper := ?_, fractional := by simp }⟩
      intro j hj _
      exact div_nonpos_of_nonpos_of_nonneg (le_of_not_gt (fun h => hpos ⟨j, hj, h⟩)) (hw j).le

theorem certificate_optimal {α : Type*} [Fintype α] (w a : α → ℝ)
    (hw : ∀ j, 0 < w j) (c R : ℝ) (T : Certificate Finset.univ w a c R)
    (y : α → ℝ) (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1) (hycap : (∑ j, w j * y j) ≤ c) :
    (∑ j, a j * y j) ≤ ∑ j, a j * T.x j := by
  have hpoint (j : α) : (a j - T.lam * w j) * y j ≤ (a j - T.lam * w j) * T.x j := by
    by_cases hz : T.x j = 0
    · have hratio := T.upper j (Finset.mem_univ _) (by rw [hz]; norm_num)
      have hcoeff : a j - T.lam * w j ≤ 0 := by
        have := (div_le_iff₀ (hw j)).mp hratio
        linarith
      rw [hz, mul_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hcoeff (hy j).1
    · have hxpos : 0 < T.x j := lt_of_le_of_ne (T.box j).1 (Ne.symm hz)
      have hl := (le_div_iff₀ (hw j)).mp (T.lower j (Finset.mem_univ _) hxpos)
      have hc0 : 0 ≤ a j - T.lam * w j := by linarith
      by_cases h1 : T.x j = 1
      · rw [h1]
        exact mul_le_mul_of_nonneg_left (hy j).2 hc0
      · have hxlt : T.x j < 1 := lt_of_le_of_ne (T.box j).2 h1
        have hu := (div_le_iff₀ (hw j)).mp (T.upper j (Finset.mem_univ _) hxlt)
        have heq : a j - T.lam * w j = 0 := by linarith
        simp [heq]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset α)) => hpoint j)
  simp_rw [sub_mul, mul_assoc] at hs
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum] at hs
  rcases T.complement with h | h
  · simpa [h] using hs
  · have hcap := mul_le_mul_of_nonneg_left hycap T.lam_nonneg
    rw [h] at hs
    linarith

end FractionalKnapsack

open ConstrNestedLogit.Space

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (hn : 0 < n)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ j, 0 < I.v i j)
    (hw : ∀ j, 0 < w i j) (hwc : ∀ j, w i j ≤ c i)
    (u : ℝ) (hu : 0 ≤ u) :
    ∃ x : Fin n → ℝ, spaceLPOptimal I w c i u x ∧ atMostOneFractional x ∧
      (∀ j, 0 < x j → 0 < utility I i u j) ∧
      (∀ j k, 0 < x j → x k < 1 →
        utilityRatio I w i u k ≤ utilityRatio I w i u j) := by
  classical
  let a := utility I i u
  let R : ℝ := ∑ j, max (a j / w i j) 0
  have hR : 0 ≤ R := Finset.sum_nonneg (fun j _ => le_max_right _ _)
  have hbound : ∀ j ∈ (Finset.univ : Finset (Fin n)), a j / w i j ≤ R := by
    intro j _
    exact (le_max_left _ _).trans (Finset.single_le_sum (fun k _ => le_max_right (a k / w i k) 0)
      (Finset.mem_univ j))
  have hc : 0 ≤ c i := (hw ⟨0, hn⟩).le.trans (hwc ⟨0, hn⟩)
  obtain ⟨T⟩ := FractionalKnapsack.build Finset.univ (w i) a hw (c i) R hc hR hbound
  refine ⟨T.x, ⟨⟨T.box, T.feasible⟩, ?_⟩, T.fractional, T.positive, ?_⟩
  · intro y hy
    exact FractionalKnapsack.certificate_optimal (w i) a hw (c i) R T y hy.1 hy.2
  · intro j k hj hk
    exact (T.upper k (Finset.mem_univ _) hk).trans (T.lower j (Finset.mem_univ _) hj)

#print axioms solution
