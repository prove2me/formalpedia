-- Prove2me | solution 1 for DischargeTiming.Ranking.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T23:44:01.327976+00:00
-- url     : https://prove2.me/submissions/b4398cc7-1863-4e17-b9d3-6b2f659d80bf

import Mathlib
import Definitions.Def_DischargeTiming_Ranking_Model

namespace DischargeTiming.Ranking

lemma dt_deriv_nonpos {f : ℝ → ℝ} (hc : ContDiff ℝ 1 f) (ha : AntitoneOn f (Set.Ici 0))
    {x : ℝ} (hx : 0 < x) : deriv f x ≤ 0 := by
  have hd : DifferentiableAt ℝ f x := (hc.differentiable (by norm_num)) x
  refine (hd.hasDerivAt.hasDerivWithinAt (s := Set.Ici 0)).nonpos_of_antitoneOn ?_ ha
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨x + ε / 2, ⟨hball ?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_of_pos (by linarith)]; linarith
  · show (0:ℝ) ≤ x + ε / 2; linarith
  · intro h; linarith

lemma dt_unit_cost {M J : ℕ} (P : Model M J) (Dk : Action M J) (m : Fin M) (j : Fin (J + 1)) :
    dischargeCost P (Dk + unitAction m j) = dischargeCost P Dk + P.R * P.r m ((j : ℕ) : ℝ) := by
  unfold dischargeCost
  have : ∀ m' j', ((Dk + unitAction m j) m' j' : ℝ) * (P.R * P.r m' ((j' : ℕ) : ℝ))
      = (Dk m' j' : ℝ) * (P.R * P.r m' ((j' : ℕ) : ℝ))
        + (if m' = m then (if j' = j then P.R * P.r m ((j : ℕ) : ℝ) else 0) else 0) := by
    intro m' j'
    simp only [Pi.add_apply, unitAction]
    by_cases h1 : m' = m <;> by_cases h2 : j' = j <;> simp [h1, h2] <;> ring
  simp_rw [this, Finset.sum_add_distrib]
  simp

lemma dt_core {M J : ℕ} (P : Model M J) (hP : P.Standing)
    (m1 m2 : Fin M) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdom : StronglyDominates P m1 a m2 b) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    P.r m1 a - P.r m1 (a + Δ) ≤ P.r m2 b - P.r m2 (b + Δ) := by
  obtain ⟨hc, han, _⟩ := hP
  set g : ℝ → ℝ := fun s => P.r m2 (b + s) - P.r m1 (a + s) with hg
  have hdiff : ∀ m (c : ℝ), Differentiable ℝ (fun s => P.r m (c + s)) := by
    intro m c
    exact ((hc m).differentiable (by norm_num)).comp (differentiable_const _ |>.add differentiable_id)
  have hgd : Differentiable ℝ g := (hdiff m2 b).sub (hdiff m1 a)
  have hanti : AntitoneOn g (Set.Icc 0 Δ) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 Δ) hgd.continuous.continuousOn
      hgd.differentiableOn
    intro s hs
    rw [interior_Icc] at hs
    obtain ⟨hs0, _⟩ := hs
    have e1 : ∀ m (c : ℝ), deriv (fun s => P.r m (c + s)) s = deriv (P.r m) (c + s) := by
      intro m c
      have := ((hc m).differentiable (by norm_num) (c + s)).hasDerivAt
      have h2 : HasDerivAt (fun s => P.r m (c + s)) (deriv (P.r m) (c + s)) s := by
        exact HasDerivAt.comp_const_add c s this
      exact h2.deriv
    have hgder : deriv g s = deriv (P.r m2) (b + s) - deriv (P.r m1) (a + s) := by
      rw [hg, deriv_fun_sub (hdiff m2 b s) (hdiff m1 a s), e1, e1]
    rw [hgder]
    have n1 := dt_deriv_nonpos (hc m1) (han m1) (x := a + s) (by linarith)
    have n2 := dt_deriv_nonpos (hc m2) (han m2) (x := b + s) (by linarith)
    have hd := hdom s hs0.le
    rw [abs_of_nonpos n1, abs_of_nonpos n2] at hd
    linarith
  have := hanti (a := 0) (b := Δ) ⟨le_refl _, hΔ⟩ ⟨hΔ, le_refl _⟩ hΔ
  simp only [hg, add_zero] at this
  linarith

end DischargeTiming.Ranking

open DischargeTiming.Ranking

theorem solution {M J : ℕ} (P : Model M J) (hP : P.Standing)
    (m1 m2 : Fin M) (t1 t2 : Fin (J + 1))
    (hdom : StronglyDominates P m1 ((t1 : ℕ) : ℝ) m2 ((t2 : ℕ) : ℝ))
    (Dk Dk' : Action M J) (k k' : ℕ) (hkk' : k < k')
    (h1 : (t1 : ℕ) + (k' - k) ≤ J) (h2 : (t2 : ℕ) + (k' - k) ≤ J) :
    dischargeCost P (Dk + unitAction m1 t1)
        - dischargeCost P (Dk' + unitAction m1 (losShift t1 (k' - k) h1))
      ≤ dischargeCost P (Dk + unitAction m2 t2)
        - dischargeCost P (Dk' + unitAction m2 (losShift t2 (k' - k) h2)) := by
  rw [dt_unit_cost, dt_unit_cost, dt_unit_cost, dt_unit_cost]
  simp only [losShift]
  have hR := hP.2.2
  have hc := dt_core P hP m1 m2 _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) hdom
    ((k' - k : ℕ) : ℝ) (Nat.cast_nonneg _)
  push_cast at hc ⊢
  nlinarith [mul_le_mul_of_nonneg_left hc hR]
