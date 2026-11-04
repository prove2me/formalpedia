-- Prove2me | solution 1 for BudgetedAffine.Budget.staticValue_attained
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T21:18:20.139284+00:00
-- url     : https://prove2.me/submissions/f17acfa9-e290-4050-9d91-d6d10a454259

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Budget_Construction
import Definitions.Def_Polyhedron
import Theorems.Thm_LinearOptimization_lp_attains_or_unbounded

set_option autoImplicit false
open Matrix


theorem affdisj_dot_append' {n : ℕ} (u v : Fin n → ℝ) (z : Fin (n + n) → ℝ) :
    Fin.append u v ⬝ᵥ z = u ⬝ᵥ (fun j => z (Fin.castAdd n j)) + v ⬝ᵥ (fun j => z (Fin.natAdd n j)) := by
  simp only [dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem solution {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (r : Fin m → ℝ) (hX : BudgetedAffine.Budget.IsPolyhedral X) (hd : 0 ≤ d)
    (hcX : ∀ x ∈ X, 0 ≤ c ⬝ᵥ x) (hfin : BudgetedAffine.Budget.staticValue A B c d X r ≠ ⊤) :
    ∃ x y : Fin n → ℝ, BudgetedAffine.Budget.IsStaticOpt A B c d X r x y := by
  classical
  obtain ⟨k, G, g, rfl⟩ := hX
  set xOf : (Fin (n + n) → ℝ) → Fin n → ℝ := fun z j => z (Fin.castAdd n j) with hxOf
  set yOf : (Fin (n + n) → ℝ) → Fin n → ℝ := fun z j => z (Fin.natAdd n j) with hyOf
  set A' : Matrix (Fin (k + (n + m))) (Fin (n + n)) ℝ :=
    Matrix.of (fun q => Fin.addCases (motive := fun _ => Fin (n + n) → ℝ)
      (fun κ => Fin.append (-(G κ)) 0)
      (Fin.addCases (motive := fun _ => Fin (n + n) → ℝ) (fun j => Fin.append 0 (Pi.single j 1))
        (fun i => Fin.append (A i) (B i))) q) with hA'
  set b' : Fin (k + (n + m)) → ℝ := Fin.addCases (motive := fun _ => ℝ) (fun κ => -g κ)
    (Fin.addCases (motive := fun _ => ℝ) (fun _ => 0) r) with hb'
  have hmem : ∀ z : Fin (n + n) → ℝ, z ∈ LinearOptimization.polyhedron A' b' ↔
      xOf z ∈ {x | G *ᵥ x ≤ g} ∧ 0 ≤ yOf z ∧ r ≤ A *ᵥ xOf z + B *ᵥ yOf z := by
    intro z
    unfold LinearOptimization.polyhedron
    simp only [Set.mem_setOf_eq]
    rw [Pi.le_def, Fin.forall_fin_add, Fin.forall_fin_add]
    simp only [hA', hb', Matrix.mulVec, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right,
      affdisj_dot_append', zero_dotProduct, add_zero, zero_add, single_dotProduct, one_mul,
      neg_dotProduct, neg_le_neg_iff]
    simp only [Pi.le_def, Pi.add_apply, Matrix.mulVec, Pi.zero_apply]
    rfl
  have hne : (LinearOptimization.polyhedron A' b').Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    apply hfin
    refine top_le_iff.1 (le_iInf (fun x => le_iInf (fun hx => le_iInf (fun y => le_iInf
      (fun hy => ?_)))))
    have : Fin.append x y ∈ LinearOptimization.polyhedron A' b' := by
      rw [hmem]
      have h1 : xOf (Fin.append x y) = x := by funext j; exact Fin.append_left x y j
      have h2 : yOf (Fin.append x y) = y := by funext j; exact Fin.append_right x y j
      rw [h1, h2]
      exact ⟨hx, hy.1, hy.2⟩
    rw [hcon] at this
    exact absurd this (Set.notMem_empty _)
  rcases LinearOptimization.lp_attains_or_unbounded A' b' (Fin.append c d) hne with
    hbot | ⟨z, hzP, hzopt⟩
  · exfalso
    have h0 : (0 : EReal) ≤
        LinearOptimization.lpValue (Fin.append c d) (LinearOptimization.polyhedron A' b') := by
      unfold LinearOptimization.lpValue
      refine le_iInf₂ (fun z hz => ?_)
      obtain ⟨h1, h2, -⟩ := (hmem z).1 hz
      rw [affdisj_dot_append']
      have := hcX _ h1
      have := dotProduct_nonneg_of_nonneg hd h2
      exact_mod_cast (by linarith : (0:ℝ) ≤ c ⬝ᵥ xOf z + d ⬝ᵥ yOf z)
    rw [hbot] at h0
    exact absurd h0 (by simp)
  · obtain ⟨h1, h2, h3⟩ := (hmem z).1 hzP
    refine ⟨xOf z, yOf z, h1, h2, h3, le_antisymm ?_
      (le_trans (iInf₂_le (xOf z) h1) (iInf₂_le (yOf z) ⟨h2, h3⟩))⟩
    refine le_iInf (fun x => le_iInf (fun hx => le_iInf (fun y => le_iInf (fun hy => ?_))))
    have hmemxy : Fin.append x y ∈ LinearOptimization.polyhedron A' b' := by
      rw [hmem]
      have e1 : xOf (Fin.append x y) = x := by funext j; exact Fin.append_left x y j
      have e2 : yOf (Fin.append x y) = y := by funext j; exact Fin.append_right x y j
      rw [e1, e2]
      exact ⟨hx, hy.1, hy.2⟩
    have := hzopt _ hmemxy
    rw [affdisj_dot_append', affdisj_dot_append'] at this
    have e1 : xOf (Fin.append x y) = x := by funext j; exact Fin.append_left x y j
    have e2 : yOf (Fin.append x y) = y := by funext j; exact Fin.append_right x y j
    simp only [hxOf, hyOf] at e1 e2 this
    rw [e1, e2] at this
    exact_mod_cast this
