-- Prove2me | solution 1 for BudgetCournot.Equilibrium.eq_B11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:12:39.232994+00:00
-- url     : https://prove2.me/submissions/39ee4586-dbbd-47c1-a3fe-504f48609491

import Mathlib
import Definitions.Def_BudgetCournot_Equilibrium_Model

open Finset

namespace Aux_BC_eq_B11

noncomputable def zext {N : ℕ} (g : Fin N → ℝ) (k : ℕ) : ℝ :=
  if h : k < N then g ⟨k, h⟩ else 0

theorem sumLt {N : ℕ} (g : Fin N → ℝ) (i : Fin N) :
    ∑ k ∈ univ.filter (fun k => k < i), g k = ∑ k ∈ range (i : ℕ), zext g k := by
  calc ∑ k ∈ univ.filter (fun k => k < i), g k
      = ∑ k : Fin N, (fun k : ℕ => if k < (i : ℕ) then zext g k else 0) (k : ℕ) := by
        rw [sum_filter]
        apply sum_congr rfl
        intro k _
        have hz : zext g k = g k := by simp only [zext, dif_pos k.isLt, Fin.eta]
        show _ = (if (k : ℕ) < (i : ℕ) then zext g k else 0)
        rw [hz]
        by_cases hk : k < i
        · rw [if_pos hk, if_pos (Fin.lt_iff_val_lt_val.mp hk)]
        · rw [if_neg hk, if_neg (fun h => hk (Fin.lt_iff_val_lt_val.mpr h))]
    _ = ∑ k ∈ range N, (if k < (i : ℕ) then zext g k else 0) :=
        Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < (i : ℕ) then zext g k else 0) N
    _ = ∑ k ∈ range (i : ℕ), zext g k := by
        rw [← sum_filter]
        congr 1
        ext k
        simp only [mem_filter, mem_range]
        have := i.isLt
        omega

end Aux_BC_eq_B11

open Aux_BC_eq_B11 in
theorem solution {N : ℕ} (lam α : Fin N → ℝ)
    (h : ∀ i, α i = ((i : ℕ) + 1 : ℝ) * lam i - ∑ k ∈ univ.filter (fun k => k < i), lam k)
    (i : Fin N) :
    lam i = α i / ((i : ℕ) + 1 : ℝ)
      + ∑ k ∈ univ.filter (fun k => k < i), α k / (((k : ℕ) + 1 : ℝ) * ((k : ℕ) + 2 : ℝ)) := by
  have hA : ∀ k, k < N → zext α k = ((k : ℝ) + 1) * zext lam k - ∑ j ∈ range k, zext lam j := by
    intro k hk
    have := h ⟨k, hk⟩
    rw [sumLt] at this
    simp only [zext, dif_pos hk]
    exact this
  have tele : ∀ m, m ≤ N →
      ∑ k ∈ range m, zext α k / (((k : ℝ) + 1) * ((k : ℝ) + 2)) =
        (∑ j ∈ range m, zext lam j) / ((m : ℝ) + 1) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [sum_range_succ, sum_range_succ, ih (by omega), hA m (by omega)]
      push_cast
      have h1 : (m : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (m : ℝ) + 2 ≠ 0 := by positivity
      have h3 : (m : ℝ) + 1 + 1 ≠ 0 := by positivity
      field_simp
      ring
  rw [sumLt]
  have e : ∑ k ∈ range (i : ℕ), zext (fun k : Fin N => α k / (((k : ℕ) + 1 : ℝ) * ((k : ℕ) + 2 : ℝ))) k
      = ∑ k ∈ range (i : ℕ), zext α k / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    apply sum_congr rfl
    intro k hk
    have hk' : k < N := lt_trans (mem_range.mp hk) i.isLt
    simp only [zext, dif_pos hk']
  rw [e, tele _ i.isLt.le]
  have hi := hA i i.isLt
  have hl : zext lam i = lam i := by simp [zext, dif_pos i.isLt]
  have ha : zext α i = α i := by simp [zext, dif_pos i.isLt]
  rw [hl, ha] at hi
  rw [hi]
  have h1 : ((i : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring
