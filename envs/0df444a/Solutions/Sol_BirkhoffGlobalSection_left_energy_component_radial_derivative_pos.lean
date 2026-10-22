-- Prove2me | solution 1 for BirkhoffGlobalSection.left_energy_component_radial_derivative_pos
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T14:42:49.665662+00:00
-- url     : https://prove2.me/submissions/a0a08cfa-6e88-4fa9-a181-1534d1b060e5

import Definitions.Def_BirkhoffGlobalSection
import Theorems.Thm_BirkhoffGlobalSection_left_component_radial_interior_negative
import Theorems.Thm_BirkhoffGlobalSection_left_ray_positive_energy_before_second_collision
import Theorems.Thm_BirkhoffGlobalSection_first_ray_zero_in_left_negative_closure
import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_radial_transversality
import Theorems.Thm_BirkhoffGlobalSection_leviCivita_smoothAt_of_secondCollisionFree
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ leftEnergyComponent μ c,
      0 < fderiv ℝ (leviCivitaHamiltonian μ c) s s := by
  intro s hs
  have hreg : s ∈ regularEnergyLocus μ c := by
    unfold leftEnergyComponent at hs
    have h := connectedComponentIn_subset _ _ hs
    exact h
  obtain ⟨hH, hD⟩ := hreg
  -- the origin has negative energy
  have hD0 : secondCollisionDistanceSq (0 : Phase) = 1 := by
    simp [secondCollisionDistanceSq]
  have hH0 : leviCivitaHamiltonian μ c (0 : Phase) < 0 := by
    simp only [leviCivitaHamiltonian, hD0, zNormSq, wNormSq, Real.sqrt_one]
    simp
    linarith
  -- polar decomposition `s = R • x`
  set N : ℝ := zNormSq s + wNormSq s with hN
  have hNpos : 0 < N := by
    by_contra hle
    push Not at hle
    have h0 : s 0 = 0 ∧ s 1 = 0 ∧ s 2 = 0 ∧ s 3 = 0 := by
      simp only [hN, zNormSq, wNormSq] at hle
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (s 0), sq_nonneg (s 1),
        sq_nonneg (s 2), sq_nonneg (s 3)]
    have hs0 : s = 0 := by
      funext i; fin_cases i <;> simp [h0.1, h0.2.1, h0.2.2.1, h0.2.2.2]
    rw [hs0] at hH
    linarith
  set R : ℝ := Real.sqrt N with hRdef
  have hR : 0 < R := Real.sqrt_pos.2 hNpos
  have hRsq : R ^ 2 = N := Real.sq_sqrt hNpos.le
  set x : Phase := fun i => R⁻¹ * s i with hxdef
  have hx : x ∈ unitThreeSphere := by
    show zNormSq x + wNormSq x = 1
    simp only [zNormSq, wNormSq, hxdef]
    have : (R⁻¹ * s 0) ^ 2 + (R⁻¹ * s 1) ^ 2 + ((R⁻¹ * s 2) ^ 2 + (R⁻¹ * s 3) ^ 2)
        = N / R ^ 2 := by
      simp only [hN, zNormSq, wNormSq]; field_simp
    rw [this, hRsq, div_self hNpos.ne']
  have hsx : (fun i : Fin 4 => R * x i) = s := by
    funext i; simp only [hxdef]; field_simp
  -- negative energy strictly inside the ray
  have hneg : ∀ t : ℝ, 0 ≤ t → t < R →
      leviCivitaHamiltonian μ c (fun i : Fin 4 => t * x i) < 0 := by
    intro t ht0 htR
    rcases ht0.lt_or_eq with ht | ht
    · exact left_component_radial_interior_negative μ c hμ0 hμ1 hc x hx R hR
        (by rw [hsx]; exact hs) t ht htR
    · subst ht
      have : (fun i : Fin 4 => (0 : ℝ) * x i) = 0 := by funext i; simp
      rw [this]; exact hH0
  -- no second collision on the closed segment
  obtain ⟨R0, hR0, hpos, hfree0⟩ :=
    left_ray_positive_energy_before_second_collision μ c hμ0 hμ1 hc x hx
  have hRR0 : R ≤ R0 := by
    by_contra hlt
    push Not at hlt
    have h1 := hneg R0 hR0.le hlt
    linarith
  have hfree : ∀ t : ℝ, 0 ≤ t → t ≤ R →
      0 < secondCollisionDistanceSq (fun i : Fin 4 => t * x i) :=
    fun t ht0 htR => hfree0 t ht0 (htR.trans hRR0)
  have hcl := first_ray_zero_in_left_negative_closure μ c hμ0 hμ1 x R hR hneg hfree
  rw [hsx] at hcl
  have htr := left_negative_closure_radial_transversality μ c hμ0 hμ1 hc s hcl hH
  -- the radial derivative is the differential applied to `s`
  have hdiff : DifferentiableAt ℝ (leviCivitaHamiltonian μ c) s :=
    (leviCivita_smoothAt_of_secondCollisionFree μ c s hD).differentiableAt (by simp)
  have hg : HasDerivAt (fun a : ℝ => (fun i : Fin 4 => a * s i)) s 1 :=
    hasDerivAt_pi.2 fun i => by simpa using HasDerivAt.mul_const (hasDerivAt_id' (1 : ℝ)) (s i)
  have hg1 : (fun a : ℝ => (fun i : Fin 4 => a * s i)) 1 = s := by funext i; simp
  have hf : HasFDerivAt (leviCivitaHamiltonian μ c)
      (fderiv ℝ (leviCivitaHamiltonian μ c) s)
      ((fun a : ℝ => (fun i : Fin 4 => a * s i)) 1) := by
    rw [hg1]; exact hdiff.hasFDerivAt
  have hcomp : HasDerivAt
      (fun a : ℝ => leviCivitaHamiltonian μ c (fun i : Fin 4 => a * s i))
      (fderiv ℝ (leviCivitaHamiltonian μ c) s s) 1 :=
    HasFDerivAt.comp_hasDerivAt (l := leviCivitaHamiltonian μ c) (1 : ℝ) hf hg
  rw [hcomp.deriv] at htr
  exact htr
