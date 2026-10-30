-- Prove2me | solution 1 for ExactPenGNEP.NonShared.theorem_11_b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:50:01.743546+00:00
-- url     : https://prove2.me/submissions/9d72df75-2a28-4f5e-878d-e7e4ba5c797a

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_ExactPenGNEP_NonShared_Setting
import Theorems.Thm_ExactPenGNEP_NonShared_cq_norm_comparison
import Theorems.Thm_ExactPenGNEP_NonShared_theorem_11_descent_bound
import Theorems.Thm_ExactPenGNEP_NonShared_theorem_11_first_order

open LeiBR.Sync ExactPenGNEP.NonShared

theorem solution {N : ℕ} {n m p : Fin N → ℕ} (C : ∀ ν, Set (Strat n ν))
    (g : ∀ ν, Fin (m ν) → Profile n → ℝ) (h : ∀ ν, Fin (p ν) → Profile n →ᵃ[ℝ] ℝ)
    (θ : Fin N → Profile n → ℝ) (Lip q : ℝ)
    (hCc : ∀ ν, IsCompact (C ν)) (hCv : ∀ ν, Convex ℝ (C ν))
    (hg_cvx : ∀ ν i (x : Profile n), (∀ ν' ≠ ν, x ν' ∈ C ν') →
      ConvexOn ℝ Set.univ (fun y => g ν i (Function.update x ν y)))
    (hg_diff : ∀ ν i (x : Profile n), (∀ ν' ≠ ν, x ν' ∈ C ν') →
      Differentiable ℝ (fun y => g ν i (Function.update x ν y)))
    (hLip : 0 < Lip)
    (hθ_cvx : ∀ ν (x : Profile n), (∀ ν' ≠ ν, x ν' ∈ C ν') →
      ConvexOn ℝ (C ν) (fun y => θ ν (Function.update x ν y)))
    (hθ_lip : ∀ ν (x : Profile n), (∀ ν' ≠ ν, x ν' ∈ C ν') →
      LipschitzOnWith (Real.toNNReal Lip) (fun y => θ ν (Function.update x ν y)) (C ν))
    (hq : 1 < q)
    (hb : SlaterTypeCQ C g h) :
    ∃ ρbar > (0 : ℝ), ∀ ρ > ρbar, ∀ x : Profile n,
      IsNashEq C (fun ν y => θ ν y + ρ * lqRes (g ν) (fun j z => h ν j z) q y) x →
        IsGNE C (frSet g h) θ x := by
  obtain ⟨c, hc, hcq⟩ := cq_norm_comparison q hq
  obtain ⟨α, hα, hS⟩ := hb
  -- uniform diameter bound
  have hbd : ∀ ν, ∃ D : ℝ, ∀ a ∈ C ν, ∀ b ∈ C ν, ‖a - b‖ ≤ D := by
    intro ν
    obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp (hCc ν).isBounded
    exact ⟨D, fun a ha b hb => by rw [← dist_eq_norm]; exact hD ha hb⟩
  choose D hD using hbd
  set Dt : ℝ := ∑ ν, |D ν| with hDt
  have hDt0 : 0 ≤ Dt := Finset.sum_nonneg (fun ν _ => abs_nonneg _)
  have hDle : ∀ ν, D ν ≤ Dt := fun ν =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun ν => |D ν|)
      (fun ν _ => abs_nonneg _) (Finset.mem_univ ν))
  have hcq1 : 0 < c ^ (q - 1) := Real.rpow_pos_of_pos hc _
  have hden : 0 < α * c ^ (q - 1) := mul_pos hα hcq1
  have hfrac : 0 ≤ Lip * Dt / (α * c ^ (q - 1)) := div_nonneg (mul_nonneg hLip.le hDt0) hden.le
  refine ⟨Lip * Dt / (α * c ^ (q - 1)) + 1, by linarith, ?_⟩
  intro ρ hρ x hNE
  have hρbig : Lip * Dt / (α * c ^ (q - 1)) < ρ := by linarith
  have hρ0 : 0 < ρ := lt_of_le_of_lt hfrac hρbig
  obtain ⟨hxC0, hmin⟩ := hNE
  have hxC : ∀ ν, x ν ∈ C ν := fun ν => hxC0 ν (Set.mem_univ _)
  by_cases hG : inGraph (frSet g h) x
  · -- feasible: the penalty vanishes on the feasible set
    intro ν
    refine ⟨⟨hxC ν, hG ν⟩, fun y hy => ?_⟩
    have hzero : ∀ z : Profile n, (∀ i, g ν i z ≤ 0) → (∀ j, h ν j z = 0) →
        lqRes (g ν) (fun j z => h ν j z) q z = 0 := by
      intro z hgz hhz
      have hq0 : (1 / q) ≠ 0 := by
        have : 0 < q := by linarith
        positivity
      simp only [lqRes, max_eq_right (hgz _), hhz, abs_zero,
        Real.zero_rpow (by linarith : q ≠ 0), Finset.sum_const_zero, add_zero,
        Real.zero_rpow hq0]
    have h1 : lqRes (g ν) (fun j z => h ν j z) q x = 0 := by
      have hx' := hG ν
      obtain ⟨hx1, hx2⟩ := hx'
      rw [Function.update_eq_self] at hx1 hx2
      exact hzero x hx1 hx2
    have h2 : lqRes (g ν) (fun j z => h ν j z) q (Function.update x ν y) = 0 :=
      hzero _ hy.2.1 hy.2.2
    have := hmin ν y hy.1
    simp only [h1, h2, mul_zero, add_zero] at this
    exact this
  · exfalso
    obtain ⟨xh, hxhC, νh, hxν, hgb, hhb⟩ := hS x hxC hG
    have hriv : ∀ ν' ≠ νh, x ν' ∈ C ν' := fun ν' _ => hxC ν'
    obtain ⟨θ', -, hfo1, hfo2⟩ := theorem_11_first_order C g h θ Lip q ρ x νh (xh νh) (hCv νh)
      hLip (hθ_cvx νh x hriv) (hθ_lip νh x hriv) (fun i => hg_diff νh i x hriv) hq hxν hρ0
      (hxC νh) (fun y hy => hmin νh y hy) (hxhC νh)
    obtain ⟨hd1, hd2⟩ := theorem_11_descent_bound g h q α c x νh (xh νh) hq hα
      (fun i => hg_diff νh i x hriv) hxν hgb hhb hc hcq
    have hdist : ‖xh νh - x νh‖ ≤ Dt := (hD νh _ (hxhC νh) _ (hxC νh)).trans (hDle νh)
    have hfd : fderiv ℝ (fun y => lqRes (g νh) (fun j z => h νh j z) q
        (Function.update x νh y)) (x νh) (xh νh - x νh) ≤ -α * c ^ (q - 1) := hd1.trans hd2
    have h3 : ρ * (α * c ^ (q - 1)) ≤ Lip * Dt := by
      have := mul_le_mul_of_nonneg_left hfd hρ0.le
      have := mul_le_mul_of_nonneg_left hdist hLip.le
      nlinarith
    rw [div_lt_iff₀ hden] at hρbig
    linarith
