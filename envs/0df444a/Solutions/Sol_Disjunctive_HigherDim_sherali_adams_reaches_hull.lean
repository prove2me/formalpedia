-- Prove2me | solution 1 for Disjunctive.HigherDim.sherali_adams_reaches_hull
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T08:38:53.875582+00:00
-- url     : https://prove2.me/submissions/411767bc-5d66-434b-9c32-9e009e35c572

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_Lifts

set_option autoImplicit false

/-! Counterexample: no constraint rows (`m = 0`), one variable, `N' = {0}`.
`K_1` is all of `ℝ¹` (no inequalities to satisfy), while `conv(K₀) = conv{0,1} ⊆ {x₀ ≤ 1}`. -/

open Disjunctive.HigherDim in
theorem cex_f3c0bd6d :
    ¬ (KtSet (0 : Matrix (Fin 0) (Fin 1) ℝ) 0 ({0} : Finset (Fin 1)) ({0} : Finset (Fin 1)).card
        = convexHull ℝ (K0Set (0 : Matrix (Fin 0) (Fin 1) ℝ) 0 ({0} : Finset (Fin 1)))) := by
  intro h
  have hx : (fun _ => (2 : ℝ)) ∈
      KtSet (0 : Matrix (Fin 0) (Fin 1) ℝ) 0 ({0} : Finset (Fin 1)) ({0} : Finset (Fin 1)).card := by
    refine ⟨fun J => if J = ∅ then 1 else 2, fun _ _ => 0, ?_, ?_, ?_, ?_⟩
    · simp
    · intro j _
      simp
    · intro k hk
      exact absurd (Finset.mem_singleton.mpr (Subsingleton.elim k 0)) hk
    · intro i
      exact i.elim0
  rw [h] at hx
  have hsub : convexHull ℝ (K0Set (0 : Matrix (Fin 0) (Fin 1) ℝ) 0 ({0} : Finset (Fin 1)))
      ⊆ {x : Fin 1 → ℝ | x 0 ≤ 1} := by
    apply convexHull_min
    · rintro x ⟨-, hx⟩
      simp only [Set.mem_iInter] at hx
      rcases hx 0 (by simp) with h0 | h0
      · show x 0 ≤ 1
        rw [h0]; norm_num
      · show x 0 ≤ 1
        rw [h0]
    · intro x hx y hy a b ha hb hab
      simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
      nlinarith
  have h2 := hsub hx
  simp only [Set.mem_setOf_eq] at h2
  norm_num at h2

open Disjunctive.HigherDim in
theorem solution : ¬ (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)),
    KtSet A b Nprime Nprime.card = convexHull ℝ (K0Set A b Nprime)) := by
  intro h
  exact cex_f3c0bd6d (h _ _ _)
