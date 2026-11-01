-- Prove2me | solution 1 for FlagshipMEA.Monopoly.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T17:59:12.490979+00:00
-- url     : https://prove2.me/submissions/c89b441f-594f-4981-96fa-e3894ddb8430

import Mathlib
import Definitions.Def_FlagshipMEA_Monopoly_Model

open FlagshipMEA.Monopoly

/-- Superadditivity of increments of a concave function on `[b, ∞)`. -/
private lemma two_point {f : ℝ → ℝ} {b : ℝ} (hf : ConcaveOn ℝ (Set.Ici b) f)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    f b + f (b + (x + y)) ≤ f (b + x) + f (b + y) := by
  rcases eq_or_lt_of_le (add_nonneg hx hy) with h | h
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    subst hx0 hy0; simp
  · set s := x + y with hs
    have hb : b ∈ Set.Ici b := le_refl b
    have hbs : b + s ∈ Set.Ici b := by simp; linarith
    have h1 := hf.2 hb hbs (div_nonneg hy h.le) (div_nonneg hx h.le)
      (by field_simp; linarith)
    have h2 := hf.2 hb hbs (div_nonneg hx h.le) (div_nonneg hy h.le)
      (by field_simp; linarith)
    have e1 : (y / s) • b + (x / s) • (b + s) = b + x := by
      simp only [smul_eq_mul]; field_simp; ring
    have e2 : (x / s) • b + (y / s) • (b + s) = b + y := by
      simp only [smul_eq_mul]; field_simp; ring
    rw [e1] at h1; rw [e2] at h2
    simp only [smul_eq_mul] at h1 h2
    have : y / s * f b + x / s * f (b + s) + (x / s * f b + y / s * f (b + s))
        = f b + f (b + s) := by field_simp; ring
    linarith

private lemma sum_increments {ι : Type} (f : ℝ → ℝ) (b : ℝ)
    (hf : ConcaveOn ℝ (Set.Ici b) f) (m : ι → ℝ) (hm : ∀ i, 0 ≤ m i)
    (s : Finset ι) :
    f (b + ∑ i ∈ s, m i) - f b ≤ ∑ i ∈ s, (f (b + m i) - f b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have := two_point hf (hm a) (Finset.sum_nonneg (fun i _ => hm i) : 0 ≤ ∑ i ∈ s, m i)
    linarith

theorem solution {n : ℕ} (D : Data n) (hS : D.Standing)
    (hfc : D.FcConcave) (M : ℝ) (hM : 0 ≤ M) (i : Fin n) :
    ∀ m : Fin n → ℝ, Feasible m → tme m = M →
      D.cost (fun j => if j = i then M else 0) ≤ D.cost m := by
  intro m hm htme
  have hcost : ∀ x : Fin n → ℝ, D.cost x = ∑ j, D.fc (D.base + x j) := by
    intro x; unfold Data.cost Data.fc
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [add_comm (x j)]
  have hkey := sum_increments D.fc D.base hfc m hm Finset.univ
  have hconc : ∑ j, D.fc (D.base + (if j = i then M else 0))
      = D.fc (D.base + M) - D.fc D.base + ∑ j : Fin n, D.fc D.base := by
    have : ∀ j, D.fc (D.base + (if j = i then M else 0))
        = (if j = i then D.fc (D.base + M) - D.fc D.base else 0) + D.fc D.base := by
      intro j; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  rw [hcost, hcost, hconc]
  have htm : ∑ j, m j = M := htme
  rw [htm] at hkey
  have : ∑ j, (D.fc (D.base + m j) - D.fc D.base) = ∑ j, D.fc (D.base + m j) - ∑ j : Fin n, D.fc D.base :=
    Finset.sum_sub_distrib _ _
  linarith
