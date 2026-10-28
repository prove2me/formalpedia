-- Prove2me | solution 1 for ChinesePostman.Polyhedron.min_attained_at_parity_point
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:08:54.440446+00:00
-- url     : https://prove2.me/submissions/c8a92618-1644-4838-a023-30940b7d5305

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_ChinesePostman_Polyhedron_Setting
import Theorems.Thm_ChinesePostman_Polyhedron_postman_polyhedron

open Classical
open ChinesePostman.Polyhedron

private def zOfBool {E : Type} (b : E → Bool) : E → ℤ :=
  fun e => if b e then 1 else 0

private def xOfBool {E : Type} (b : E → Bool) : E → ℝ :=
  fun e => (zOfBool b e : ℝ)

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ChinesePostman.Polyhedron.Graph V E) (c : E → ℝ)
    (hc : ∀ e, 0 ≤ c e) :
    ∃ x ∈ parityPoints G, ∀ x' ∈ postmanPolyhedron G, objective c x ≤ objective c x' := by
  let B : Finset (E → Bool) :=
    Finset.univ.filter (fun b => ∀ n, incidentSum G (zOfBool b) n ≡ bParity G n [ZMOD 2])
  have hB_ne : B.Nonempty := by
    refine ⟨fun _ => true, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun n => ?_⟩⟩
    have hsum : incidentSum G (zOfBool (fun _ : E => true)) n = (degree G n : ℤ) := by
      simp [incidentSum, zOfBool, degree]
    rw [hsum]
    unfold bParity
    by_cases hodd : Odd (degree G n)
    · rw [if_pos hodd]
      have hmod : degree G n % 2 = 1 := Nat.odd_iff.mp hodd
      change (degree G n : ℤ) % 2 = 1 % 2
      omega
    · rw [if_neg hodd]
      have hmod : degree G n % 2 ≠ 1 := mt Nat.odd_iff.mpr hodd
      change (degree G n : ℤ) % 2 = 0 % 2
      omega
  obtain ⟨b₀, hb₀B, hb₀_min⟩ := Finset.exists_min_image B (fun b => objective c (xOfBool b)) hB_ne
  have hb₀_par : ∀ n, incidentSum G (zOfBool b₀) n ≡ bParity G n [ZMOD 2] :=
    (Finset.mem_filter.mp hb₀B).2
  have hx₀_mem : xOfBool b₀ ∈ parityPoints G := by
    refine ⟨zOfBool b₀, fun e => ?_, hb₀_par, rfl⟩
    dsimp [zOfBool]
    split_ifs <;> omega
  have h_min_parity : ∀ x ∈ parityPoints G, objective c (xOfBool b₀) ≤ objective c x := by
    rintro x ⟨z, hz, hpar, rfl⟩
    let b : E → Bool := fun e => decide (z e % 2 = 1)
    have hzb : ∀ e, zOfBool b e = z e % 2 := by
      intro e
      have := hz e
      simp only [zOfBool, b, decide_eq_true_eq]
      split_ifs with h <;> omega
    have hbB : b ∈ B := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun n => ?_⟩
      have hdecomp : ∀ e, z e = 2 * (z e / 2) + zOfBool b e := by
        intro e
        have := hzb e
        omega
      have hinc : incidentSum G z n =
          2 * (∑ e ∈ Finset.univ.filter (fun e => n ∈ G.ends e), (z e / 2)) +
          incidentSum G (zOfBool b) n := by
        unfold incidentSum
        trans ∑ e ∈ Finset.univ.filter (fun e => n ∈ G.ends e), (2 * (z e / 2) + zOfBool b e)
        · refine Finset.sum_congr rfl (fun e _ => hdecomp e)
        · rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      have hmod : incidentSum G (zOfBool b) n ≡ incidentSum G z n [ZMOD 2] := by
        change incidentSum G (zOfBool b) n % 2 = incidentSum G z n % 2
        omega
      exact hmod.trans (hpar n)
    have hle1 : objective c (xOfBool b₀) ≤ objective c (xOfBool b) := hb₀_min b hbB
    have hle2 : objective c (xOfBool b) ≤ objective c (fun e => (z e : ℝ)) := by
      unfold objective
      refine Finset.sum_le_sum (fun e _ => ?_)
      refine mul_le_mul_of_nonneg_left ?_ (hc e)
      change (zOfBool b e : ℝ) ≤ (z e : ℝ)
      exact Int.cast_le.mpr (by have := hz e; have := hzb e; omega)
    exact hle1.trans hle2
  refine ⟨xOfBool b₀, hx₀_mem, ?_⟩
  rw [← postman_polyhedron G]
  have hconv : Convex ℝ {x' : E → ℝ | objective c (xOfBool b₀) ≤ objective c x'} := by
    intro x hx y hy a b ha hb hab
    change objective c (xOfBool b₀) ≤ objective c x at hx
    change objective c (xOfBool b₀) ≤ objective c y at hy
    change objective c (xOfBool b₀) ≤ objective c (a • x + b • y)
    have hlin : objective c (a • x + b • y) = a * objective c x + b * objective c y := by
      unfold objective
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc
        ∑ e : E, c e * (a * x e + b * y e)
          = ∑ e : E, (a * (c e * x e) + b * (c e * y e)) := by
            refine Finset.sum_congr rfl (fun e _ => by ring)
        _ = a * (∑ e : E, c e * x e) + b * (∑ e : E, c e * y e) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hlin]
    calc
      objective c (xOfBool b₀)
        = (a + b) * objective c (xOfBool b₀) := by rw [hab, one_mul]
      _ = a * objective c (xOfBool b₀) + b * objective c (xOfBool b₀) := by ring
      _ ≤ a * objective c x + b * objective c y :=
          add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
  exact convexHull_min h_min_parity hconv
