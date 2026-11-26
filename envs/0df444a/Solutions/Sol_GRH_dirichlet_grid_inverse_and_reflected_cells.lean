-- Prove2me | solution 1 for GRH.dirichlet_grid_inverse_and_reflected_cells
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T18:45:50.950369+00:00
-- url     : https://prove2.me/submissions/940d1113-3b86-4e3d-b718-398c5b6bc52c

import Definitions.Def_GRH_DyadicCharacterGrid
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Complex GRH.DyadicCharacterGrid GRH.DirichletGrid
open scoped ComplexConjugate

private lemma reflect_point (a b H : ℝ) (m i j : ℕ) (hm : 0<m) (hj : j≤m) :
    point a b H m i (m-j) = conj (point a b H m i j) := by
  apply Complex.ext
  · rfl
  · change -H+2*H*(((m-j:ℕ):ℝ)/m) = -(-H+2*H*((j:ℝ)/m))
    rw [Nat.cast_sub hj]
    field_simp [Nat.cast_ne_zero.mpr hm.ne']
    ring

private lemma reflect_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (m : ℕ) (z : ℂ) :
    sample χ⁻¹ m (conj z) = conj (sample χ m z) := by
  unfold sample
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hc : χ⁻¹ (n:ZMod q) = conj (χ (n:ZMod q)) := (MulChar.star_apply' χ _).symm
  have ha : (n:ℂ).arg ≠ Real.pi := by
    have eq : (n:ℂ).arg=0 := Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg (α:=ℝ) n)
    rw [eq]; exact ne_of_lt Real.pi_pos
  rw [map_mul,hc,← map_neg,Complex.cpow_conj _ _ ha]
  simp

private lemma reflected {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b H : ℝ) (m i j : ℕ) (hm : 0<m) (hj : j≤m) :
    Cell χ⁻¹ a b H m i (m-j) ↔ Cell χ a b H m i j := by
  unfold Cell
  rw [reflect_point a b H m i j hm hj,reflect_sum]
  simp

private lemma inverse_pass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b H : ℝ) (m : ℕ) (h : Passes χ a b H m) : Passes χ⁻¹ a b H m := by
  refine ⟨h.1,?_⟩
  intro i hi j hj
  have he := (reflected χ a b H m i (m-j) h.1 (Nat.sub_le _ _)).2
    (h.2 i hi (m-j) (Nat.sub_le _ _))
  change Cell χ⁻¹ a b H m i j
  simpa only [show m-(m-j)=j by omega] using he

/-- Conjugate characters pass at precisely the same mesh denominators.
The reduced row and column test is equivalent to the full finite test. -/
theorem solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b H : ℝ) (m : ℕ) :
    (Passes χ⁻¹ a b H m ↔ Passes χ a b H m) ∧ (Checks χ a b H m ↔ Passes χ a b H m) := by
  refine ⟨⟨fun h => by simpa only [inv_inv] using inverse_pass χ⁻¹ a b H m h,
    inverse_pass χ a b H m⟩,⟨?_,?_⟩⟩
  · intro h
    refine ⟨h.1,?_⟩
    intro i hi j hj
    let i' := if a=b then 0 else i
    have ih : i'≤m := by dsimp [i'];split <;> omega
    have col : a≠b ∨ i'=0 := by by_cases e : a=b <;> simp [i',e]
    have same (k : ℕ) : point a b H m i' k=point a b H m i k := by
      by_cases e : a=b
      · simp [i',e,point]
      · simp [i',e]
    change Cell χ a b H m i j
    suffices hc : Cell χ a b H m i' j by simpa only [Cell,same] using hc
    by_cases row : χ≠χ⁻¹ ∨ m≤2*j
    · exact h.2 i' ih j hj col row
    · push Not at row
      have e:=h.2 i' ih (m-j) (Nat.sub_le _ _) col (Or.inr (by omega))
      have ec : Cell χ⁻¹ a b H m i' (m-j) := by rwa [← row.1]
      exact (reflected χ a b H m i' j h.1 hj).1 ec
  · intro h
    exact ⟨h.1,fun i hi j hj _ _ => h.2 i hi j hj⟩
