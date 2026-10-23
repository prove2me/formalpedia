-- Prove2me | solution 1 for Fundraising.PartialCollab.log_concavity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T16:06:30.353267+00:00
-- url     : https://prove2.me/submissions/4e0d9d21-95cf-45e6-86f5-0ec0715b1515

import Mathlib
import Definitions.Def_Fundraising_PartialCollab_Setting

namespace Fundraising.PartialCollab

open Finset

theorem sum_exp_update {n : ℕ} (s : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    ∑ j, Real.exp (Function.update s i t j) =
      Real.exp t + ∑ j ∈ univ.erase i, Real.exp (s j) := by
  rw [← Finset.add_sum_erase _ _ (mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem theta_update {n : ℕ} (s : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    theta (Function.update s i t) i =
      Real.exp t / (1 + Real.exp t + ∑ j ∈ univ.erase i, Real.exp (s j)) := by
  unfold theta
  rw [sum_exp_update, Function.update_self, add_assoc]

theorem log_comp_concave {f : ℝ → ℝ} {D : Set ℝ} (hf : ConcaveOn ℝ D f)
    (hpos : ∀ t ∈ D, 0 < f t) : ConcaveOn ℝ D (fun t => Real.log (f t)) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hfx := hpos x hx
  have hfy := hpos y hy
  have h1 := hf.2 hx hy ha hb hab
  have hmid : 0 < a • f x + b • f y := by
    simp only [smul_eq_mul]
    rcases eq_or_lt_of_le ha with h | h
    · subst h; simp at hab; subst hab; simpa using hfy
    · have := mul_pos h hfx; have := mul_nonneg hb hfy.le; linarith
  have h2 := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 hfx) (Set.mem_Ioi.2 hfy) ha hb hab
  calc a • Real.log (f x) + b • Real.log (f y) ≤ Real.log (a • f x + b • f y) := h2
    _ ≤ Real.log (f (a • x + b • y)) := Real.log_le_log hmid h1

theorem logTheta_concave (R : ℝ) (hR : 0 ≤ R) :
    ConcaveOn ℝ Set.univ (fun t => t - Real.log (1 + Real.exp t + R)) := by
  have hpos : ∀ t, 0 < 1 + Real.exp t + R := fun t => by positivity
  have hd : ∀ t, HasDerivAt (fun t => t - Real.log (1 + Real.exp t + R))
      (1 - Real.exp t / (1 + Real.exp t + R)) t := by
    intro t
    have h1 : HasDerivAt (fun t => 1 + Real.exp t + R) (Real.exp t) t := by
      simpa using ((Real.hasDerivAt_exp t).const_add 1).add_const R
    exact (hasDerivAt_id t).sub (h1.log (hpos t).ne')
  have hderiv : deriv (fun t => t - Real.log (1 + Real.exp t + R)) =
      fun t => 1 - Real.exp t / (1 + Real.exp t + R) := funext fun t => (hd t).deriv
  apply AntitoneOn.concaveOn_of_deriv convex_univ
  · exact (fun t _ => (hd t).continuousAt.continuousWithinAt)
  · exact (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
  · rw [hderiv]
    intro x _ y _ hxy
    simp only
    have hex : Real.exp x ≤ Real.exp y := Real.exp_le_exp.2 hxy
    have h1 := hpos x
    have h2 := hpos y
    rw [sub_le_sub_iff_left, div_le_div_iff₀ h1 h2]
    nlinarith [Real.exp_pos x]

theorem log_concavity {n : ℕ} (G : Setting n) (hG : G.Standing) (i : Fin n)
    (s : Fin n → ℝ) :
    ConcaveOn ℝ (Set.Icc (G.a i) (G.b i))
      (fun t => Real.log (G.δ i t * theta (Function.update s i t) i)) := by
  obtain ⟨l, r, hl, hr, hδpos, _, hconc⟩ := hG.δ_regular i
  set R := ∑ j ∈ univ.erase i, Real.exp (s j) with hRdef
  have hR : 0 ≤ R := Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)
  have hsub : Set.Icc (G.a i) (G.b i) ⊆ Set.Ioo l r := fun t ht =>
    ⟨lt_of_lt_of_le hl ht.1, lt_of_le_of_lt ht.2 hr⟩
  have hA : ConcaveOn ℝ (Set.Ioo l r) (fun t => Real.log (G.δ i t)) :=
    log_comp_concave hconc hδpos
  have hB : ConcaveOn ℝ (Set.Ioo l r) (fun t => t - Real.log (1 + Real.exp t + R)) :=
    (logTheta_concave R hR).subset (Set.subset_univ _) (convex_Ioo l r)
  have hC := (hA.add hB).subset hsub (convex_Icc _ _)
  refine hC.congr ?_
  intro t ht
  have hδ := hδpos t (hsub ht)
  have hp : 0 < 1 + Real.exp t + R := by positivity
  simp only [Pi.add_apply]
  rw [theta_update, ← hRdef, Real.log_mul hδ.ne' (div_pos (Real.exp_pos t) hp).ne',
    Real.log_div (Real.exp_pos t).ne' hp.ne', Real.log_exp]

end Fundraising.PartialCollab

open Fundraising.PartialCollab in
theorem solution {n : ℕ} (G : Setting n) (hG : G.Standing) (i : Fin n)
    (s : Fin n → ℝ) :
    ConcaveOn ℝ (Set.Icc (G.a i) (G.b i))
      (fun t => Real.log (G.δ i t * theta (Function.update s i t) i)) :=
  log_concavity G hG i s
