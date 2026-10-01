-- Prove2me | solution 1 for FoundationsML.Regression.lipschitz_loss_rademacher_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T19:43:58.248752+00:00
-- url     : https://prove2.me/submissions/935e34ad-3bdc-44fe-8ab3-cff9a7f38278

import Mathlib
import Definitions.Def_FoundationsML_Regression_EmpiricalRademacherComplexity
import Definitions.Def_FoundationsML_Regression_LossComposedFamily

namespace Cex0a7e59e8
open FoundationsML.Regression

/-- Counterexample: X = Unit, m = 1, L t _ = min |t| 1, M = μ = 1, H = univ, S = ((),0).
The real `⨆` over an unbounded family is 0 (junk value), so the RHS is 0, while the LHS is 1/2. -/
theorem cex :
    ¬ (∀ {X : Type} {m : ℕ}
    (L : ℝ → ℝ → ℝ) (M μ : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y')
    (hLb : ∀ y y', L y y' ≤ M) (hμ : 0 < μ)
    (hLlip : ∀ y' y1 y2, |L y1 y' - L y2 y'| ≤ μ * |y1 - y2|)
    (H : Set (X → ℝ)) (S : Fin m → X × ℝ),
    EmpiricalRademacherComplexity (LossComposedFamily L H) S ≤
      μ * EmpiricalRademacherComplexity H (fun i => (S i).1)) := by
  intro hall
  set L : ℝ → ℝ → ℝ := fun t _ => min |t| 1 with hLdef
  have hLnn : ∀ y y', 0 ≤ L y y' := fun y y' => le_min (abs_nonneg _) zero_le_one
  have hLb : ∀ y y', L y y' ≤ 1 := fun y y' => min_le_right _ _
  have hLlip : ∀ y' y1 y2, |L y1 y' - L y2 y'| ≤ 1 * |y1 - y2| := by
    intro y' y1 y2
    rw [one_mul]
    show |min |y1| 1 - min |y2| 1| ≤ |y1 - y2|
    have e1 := abs_min_sub_min_le_max (|y1|) 1 (|y2|) 1
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at e1
    exact e1.trans (abs_abs_sub_abs_le_abs_sub y1 y2)
  have h := @hall Unit 1 L 1 1 one_pos hLnn hLb one_pos hLlip Set.univ (fun _ => ((), 0))
  -- RHS is zero
  have hR : EmpiricalRademacherComplexity (Set.univ : Set (Unit → ℝ))
      (fun (_ : Fin 1) => ((), (0:ℝ)).1) = 0 := by
    unfold EmpiricalRademacherComplexity
    simp
    apply Finset.sum_eq_zero
    intro σ _
    apply Real.iSup_of_not_bddAbove
    rintro ⟨B, hB⟩
    rcases Bool.eq_false_or_eq_true (σ 0) with h0 | h0
    · have := hB ⟨fun _ => |B| + 1, rfl⟩
      simp [h0] at this
      linarith [le_abs_self B]
    · have := hB ⟨fun _ => -(|B| + 1), rfl⟩
      simp [h0] at this
      linarith [le_abs_self B]
  rw [hR, mul_zero] at h
  -- LHS is positive
  have hL : 0 < EmpiricalRademacherComplexity (LossComposedFamily L Set.univ)
      (fun (_ : Fin 1) => ((), (0:ℝ))) := by
    unfold EmpiricalRademacherComplexity
    set F : (Fin 1 → Bool) → ℝ := fun σ => ⨆ g ∈ LossComposedFamily L (Set.univ : Set (Unit → ℝ)),
      (1 / ((1:ℕ) : ℝ)) * ∑ i : Fin 1, (if σ i then (1 : ℝ) else -1) * g ((), (0:ℝ)) with hF
    have hbdd : ∀ σ : Fin 1 → Bool, BddAbove (Set.range fun g : Unit × ℝ → ℝ =>
        ⨆ (_ : g ∈ LossComposedFamily L (Set.univ : Set (Unit → ℝ))),
        (1 / ((1:ℕ) : ℝ)) * ∑ i : Fin 1, (if σ i then (1 : ℝ) else -1) * g ((), (0:ℝ))) := by
      intro σ
      refine ⟨1, ?_⟩
      rintro _ ⟨g, rfl⟩
      by_cases hg : g ∈ LossComposedFamily L (Set.univ : Set (Unit → ℝ))
      · dsimp only
        rw [ciSup_pos hg]
        obtain ⟨h, -, rfl⟩ := hg
        simp only [Nat.cast_one, div_one, one_mul, Finset.univ_unique, Fin.default_eq_zero,
          Finset.sum_singleton]
        have h1 := hLnn (h ()) 0
        have h2 := hLb (h ()) 0
        rcases Bool.eq_false_or_eq_true (σ 0) with h0 | h0 <;> simp [h0] <;> linarith
      · simp [hg]
    have hnn : ∀ σ, 0 ≤ F σ := by
      intro σ
      have hmem : (fun _ : Unit × ℝ => (-1:ℝ)) ∉ LossComposedFamily L (Set.univ : Set (Unit → ℝ)) := by
        rintro ⟨h, -, hh⟩
        have e := congrFun hh ((), 0)
        have e2 := hLnn (h ()) 0
        dsimp only at e
        linarith
      refine le_trans ?_ (le_ciSup (hbdd σ) (fun _ : Unit × ℝ => (-1:ℝ)))
      dsimp only
      simp [hmem]
    have hpos : 1 ≤ F (fun _ => true) := by
      have hmem : (fun p : Unit × ℝ => L ((fun _ : Unit => (1:ℝ)) p.1) p.2) ∈
          LossComposedFamily L (Set.univ : Set (Unit → ℝ)) :=
        ⟨fun _ => (1:ℝ), Set.mem_univ _, rfl⟩
      refine le_trans ?_ (le_ciSup (hbdd (fun _ => true))
        (fun p : Unit × ℝ => L ((fun _ : Unit => (1:ℝ)) p.1) p.2))
      dsimp only
      rw [ciSup_pos hmem]
      simp [hLdef]
    have hsum : 1 ≤ ∑ σ : Fin 1 → Bool, F σ :=
      hpos.trans (Finset.single_le_sum (fun σ _ => hnn σ) (Finset.mem_univ _))
    have : (0:ℝ) < 1 / 2 ^ 1 := by norm_num
    exact mul_pos this (by linarith)
  linarith

end Cex0a7e59e8

open FoundationsML.Regression in
theorem solution : ¬ (∀ {X : Type} {m : ℕ}
    (L : ℝ → ℝ → ℝ) (M μ : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y')
    (hLb : ∀ y y', L y y' ≤ M) (hμ : 0 < μ)
    (hLlip : ∀ y' y1 y2, |L y1 y' - L y2 y'| ≤ μ * |y1 - y2|)
    (H : Set (X → ℝ)) (S : Fin m → X × ℝ),
    EmpiricalRademacherComplexity (LossComposedFamily L H) S ≤
      μ * EmpiricalRademacherComplexity H (fun i => (S i).1)) := by
  exact Cex0a7e59e8.cex
