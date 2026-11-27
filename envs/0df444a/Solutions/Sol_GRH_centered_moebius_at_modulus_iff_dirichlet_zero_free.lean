-- Prove2me | solution 1 for GRH.centered_moebius_at_modulus_iff_dirichlet_zero_free
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T00:46:27.895962+00:00
-- url     : https://prove2.me/submissions/c72da535-7bc5-423b-a138-a1ebdb0e7d0b

import Definitions.Def_GRH_FactorialMoebius
import Theorems.Thm_GRH_principal_moebius_upper_excludes_zeta_zeros_at_any_modulus
import Theorems.Thm_GRH_dirichlet_nonvanishing_of_one_sided_moebius_class_bounds
import Theorems.Thm_GRH_centered_moebius_bound_iff_square_mertens_residual
import Theorems.Thm_GRH_centered_moebius_bound_iff_square_residue_bias_of_riemannHypothesis
import Theorems.Thm_GRH_reduced_residue_bias_iff_nonprincipal_character_bounds_at_cutoffs
import Theorems.Thm_GRH_nonprincipal_moebius_uniform_power_bound_of_zero_free_halfplane
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.Linarith

open GRH.OneSidedMoebius GRH.FactorialMoebius

private theorem rh_of_right (nz : ∀ s : ℂ, 1/2 < s.re → s.re < 1 → riemannZeta s ≠ 0) :
    RiemannHypothesis := by
  apply riemannHypothesis_iff_zeros_in_strip_on_line.mpr
  intro s hs h₀ h₁
  rcases lt_trichotomy s.re (1/2) with hlt|he|hgt
  · have hnat (n : ℕ) : s ≠ -n := by
      intro e
      have h := congrArg Complex.re e
      simp at h
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    have hne : s ≠ 1 := by intro e; simp [e] at h₁
    have reflected : riemannZeta (1-s)=0 := by rw [riemannZeta_one_sub hnat hne,hs,mul_zero]
    exact (nz (1-s) (by simp only [Complex.sub_re,Complex.one_re]; linarith)
      (by simp only [Complex.sub_re,Complex.one_re]; linarith) reflected).elim
  · exact he
  · exact (nz s hgt h₁ hs).elim

private theorem rh_of_level (q : ℕ) [NeZero q] (h : rightHalfPlane q) : RiemannHypothesis := by
  apply rh_of_right
  intro s hs hs' hz
  have hs1 : s ≠ 1 := by intro e; simp [e] at hs'
  have hn := h (1:DirichletCharacter ℂ q) s hs (fun e => hs1 e.2)
  apply hn
  change DirichletCharacter.LFunctionTrivChar q s = 0
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1,hz,mul_zero]

private theorem centered_to_upper (q : ℕ) [NeZero q] (h : centered q)
    (θ : ℝ) (hl : 1/2 < θ) (hr : θ < 1) : upper q θ := by
  intro a ha
  obtain ⟨C,hC,hb⟩ := (GRH.centered_moebius_bound_iff_square_mertens_residual q a θ hl.le).1
    (h a ha θ hl hr)
  refine ⟨C,hC,fun u => ?_⟩
  have lo := (le_abs_self _).trans (hb u)
  change residue a (u^2) + _ ≤ _ at lo
  exact (le_add_of_nonneg_right (by positivity)).trans lo

private theorem upper_to_right (q : ℕ) [NeZero q]
    (h : ∀ θ : ℝ, 1/2 < θ → θ < 1 → upper q θ) : rightHalfPlane q := by
  have rh : RiemannHypothesis := by
    apply rh_of_right
    intro s hs low
    let θ := (1/2+s.re)/2
    have hl : 1/2 < θ := by dsimp [θ]; linarith
    have hθ : θ < s.re := by dsimp [θ]; linarith
    have hr := hθ.trans low
    have hp := GRH.principal_moebius_upper_excludes_zeta_zeros_at_any_modulus q θ hl.le hr
    exact hp.2 (hp.1 (h θ hl hr)) s hθ (by intro e; simp [e] at low)
  intro χ s hs pole
  by_cases high : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp pole) high
  let θ := (1/2+s.re)/2
  have hl : 1/2 < θ := by dsimp [θ]; linarith
  have hθ : θ < s.re := by dsimp [θ]; linarith
  have hr := hθ.trans (lt_of_not_ge high)
  exact GRH.dirichlet_nonvanishing_of_one_sided_moebius_class_bounds rh q θ hl hr (h θ hl hr) χ s hθ pole

private theorem right_to_center (q : ℕ) [NeZero q] (h : rightHalfPlane q) : centered q := by
  intro a ha σ hl hr
  apply (GRH.centered_moebius_bound_iff_square_residue_bias_of_riemannHypothesis
    (rh_of_level q h) q a ha σ hl hr).2
  right
  apply (GRH.reduced_residue_bias_iff_nonprincipal_character_bounds_at_cutoffs q
    (fun k => (ArithmeticFunction.moebius k:ℝ)) (fun u => u^2) (fun u => ((u:ℝ)^2+1)^σ)).2 _ a ha
  intro χ hn
  obtain ⟨D,hD,H⟩ := GRH.nonprincipal_moebius_uniform_power_bound_of_zero_free_halfplane
    q χ hn (1/2) σ le_rfl (by norm_num) hl (fun s hs => h χ s hs (fun hh => hn hh.1))
  refine ⟨D,hD,fun u => ?_⟩
  have castSquare : ((u^2 : ℕ) : ℝ) = (u:ℝ)^2 := by norm_cast
  rw [← castSquare]
  simpa only [Complex.ofReal_intCast] using H (u^2)

theorem solution (q : ℕ) [NeZero q] :
    (centered q ↔ ∀ θ : ℝ, 1/2 < θ → θ < 1 → upper q θ) ∧
    ((∀ θ : ℝ, 1/2 < θ → θ < 1 → upper q θ) ↔ rightHalfPlane q) ∧
    (rightHalfPlane q → RiemannHypothesis) := by
  exact ⟨⟨centered_to_upper q,fun h => right_to_center q (upper_to_right q h)⟩,
    ⟨upper_to_right q,fun h => centered_to_upper q (right_to_center q h)⟩,rh_of_level q⟩
