-- Prove2me | solution 1 for DistInterpRO.Consistency.box_oscillation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:23:02.770755+00:00
-- url     : https://prove2.me/submissions/46c3477b-a7e1-4545-aae9-ada429d11fb4

import Mathlib
import Definitions.Def_DistInterpRO_Consistency_Model

open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Consistency

theorem aux_boxosc_key {V : Type*} {m : ℕ} (f : V → (Fin m → ℝ) → ℝ) (C : ℝ)
    (hfC : ∀ v x, |f v x| ≤ C) (v : V) {ε : ℝ} (x y : Fin m → ℝ)
    (hxy : ‖x - y‖ ≤ 2 * ε) :
    |f v y - f v (y + (x - y))| ≤ modulus f (2 * ε) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hfC v x)
  have h2C : ∀ v x y, |f v x - f v y| ≤ 2 * C := by
    intro v x y
    calc |f v x - f v y| ≤ |f v x| + |f v y| := abs_sub _ _
      _ ≤ 2 * C := by linarith [hfC v x, hfC v y]
  unfold modulus
  have hin : BddAbove (Set.range fun δ : {δ : Fin m → ℝ // ‖δ‖ ≤ 2 * ε} =>
      |f v y - f v (y + δ.1)|) :=
    ⟨2 * C, by rintro _ ⟨δ, rfl⟩; exact h2C _ _ _⟩
  have hmid : ∀ w, BddAbove (Set.range fun x : Fin m → ℝ =>
      ⨆ δ : {δ : Fin m → ℝ // ‖δ‖ ≤ 2 * ε}, |f w x - f w (x + δ.1)|) := by
    intro w
    refine ⟨2 * C, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact Real.iSup_le (fun δ => h2C _ _ _) (by linarith)
  have hout : BddAbove (Set.range fun w : V => ⨆ x : Fin m → ℝ,
      ⨆ δ : {δ : Fin m → ℝ // ‖δ‖ ≤ 2 * ε}, |f w x - f w (x + δ.1)|) := by
    refine ⟨2 * C, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact Real.iSup_le (fun x => Real.iSup_le (fun δ => h2C _ _ _) (by linarith)) (by linarith)
  calc |f v y - f v (y + (x - y))|
        ≤ ⨆ δ : {δ : Fin m → ℝ // ‖δ‖ ≤ 2 * ε}, |f v y - f v (y + δ.1)| :=
          le_ciSup hin ⟨x - y, hxy⟩
    _ ≤ ⨆ x : Fin m → ℝ, ⨆ δ : {δ : Fin m → ℝ // ‖δ‖ ≤ 2 * ε}, |f v x - f v (x + δ.1)| :=
          le_ciSup (hmid v) y
    _ ≤ _ := le_ciSup hout v

end DistInterpRO.Consistency

open DistInterpRO.Consistency
open MeasureTheory Filter Topology ProbabilityTheory

theorem solution {V : Type*} {m : ℕ} (f : V → (Fin m → ℝ) → ℝ) (C : ℝ)
    (hfC : ∀ v x, |f v x| ≤ C) (v : V) (xi : Fin m → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (⨆ x : box xi ε, f v x) - (⨅ x : box xi ε, f v x) ≤ modulus f (2 * ε) := by
  have hne : Nonempty (box xi ε) := ⟨⟨xi, Metric.mem_closedBall_self hε.le⟩⟩
  have hpair : ∀ x y : box xi ε, f v x - f v y ≤ modulus f (2 * ε) := by
    intro x y
    have hxy : ‖(x : Fin m → ℝ) - y‖ ≤ 2 * ε := by
      have hx := x.2
      have hy := y.2
      simp only [box, Metric.mem_closedBall, dist_eq_norm] at hx hy
      calc ‖(x : Fin m → ℝ) - y‖ = ‖((x : Fin m → ℝ) - xi) - ((y : Fin m → ℝ) - xi)‖ := by
            congr 1; abel
        _ ≤ ‖(x : Fin m → ℝ) - xi‖ + ‖(y : Fin m → ℝ) - xi‖ := norm_sub_le _ _
        _ ≤ 2 * ε := by linarith
    have hk := aux_boxosc_key f C hfC v x y hxy
    have h2 : (y : Fin m → ℝ) + ((x : Fin m → ℝ) - y) = x := by abel
    rw [h2] at hk
    calc f v x - f v y ≤ |f v x - f v y| := le_abs_self _
      _ = |f v y - f v x| := abs_sub_comm _ _
      _ ≤ _ := hk
  have hmain : (⨆ x : box xi ε, f v x) ≤ modulus f (2 * ε) + ⨅ x : box xi ε, f v x := by
    apply ciSup_le
    intro x
    have : f v x - modulus f (2 * ε) ≤ ⨅ y : box xi ε, f v y :=
      le_ciInf (fun y => by linarith [hpair x y])
    linarith
  linarith
