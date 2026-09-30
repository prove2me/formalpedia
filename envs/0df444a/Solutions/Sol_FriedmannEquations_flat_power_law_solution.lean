-- Prove2me | solution 1 for FriedmannEquations.flat_power_law_solution
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:38:57.541552+00:00
-- url     : https://prove2.me/submissions/1dcf2aa2-9858-417d-8458-f677d9778aef

import Definitions.Def_FriedmannEquations_Defs
set_option autoImplicit false
open FriedmannEquations Filter Topology

theorem solution (G w a₀ : ℝ) (hG : 0 < G) (hw : w ≠ -1) (ha₀ : 0 < a₀) :
    let R : ℝ → ℝ := fun t => a₀ * t ^ (2 / (3 * (w + 1)))
    let ρ : ℝ → ℝ := fun t => 1 / (6 * Real.pi * G * (1 + w) ^ 2 * t ^ 2)
    ∀ t : ℝ, 0 < t →
      FirstFriedmannEq G 0 0 R ρ t ∧ SecondFriedmannEq G 0 R ρ (fun s => w * ρ s) t := by
  let q : ℝ := 2 / (3 * (w + 1))
  let R : ℝ → ℝ := fun t => a₀ * t ^ q
  change ∀ t : ℝ, 0 < t → FirstFriedmannEq G 0 0 R _ t ∧ SecondFriedmannEq G 0 R _ _ t
  intro t ht
  have hpow : t ^ q ≠ 0 := (Real.rpow_pos_of_pos ht q).ne'
  have hD (s : ℝ) (hs : 0 < s) : deriv R s = a₀ * q * s ^ (q-1) := by
    simpa [R, mul_assoc] using ((Real.hasDerivAt_rpow_const (p := q) (Or.inl hs.ne')).const_mul a₀).deriv
  have hlocal : deriv R =ᶠ[𝓝 t] fun s => a₀ * q * s ^ (q-1) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact hD s hs
  have hDD : deriv (deriv R) t = a₀ * q * ((q-1) * t ^ ((q-1)-1)) :=
    (((Real.hasDerivAt_rpow_const (p := q-1) (Or.inl ht.ne')).const_mul (a₀*q)).congr_of_eventuallyEq hlocal).deriv
  have hH : hubble R t = q / t := by
    unfold hubble
    rw [hD t ht, Real.rpow_sub_one ht.ne']
    dsimp [R]
    field_simp [hpow, ha₀.ne']
  have hacc : deriv (deriv R) t / R t = q * (q-1) / t^2 := by
    rw [hDD, show (q-1)-1 = q-2 by ring, Real.rpow_sub ht, Real.rpow_two]
    dsimp [R]
    field_simp [hpow, ha₀.ne']
    <;> ring
  have hw1 : w+1 ≠ 0 := by intro h; apply hw; linarith
  have hw2 : 1+w ≠ 0 := by simpa [add_comm] using hw1
  constructor
  · unfold FirstFriedmannEq
    rw [hH]
    dsimp [q]
    field_simp [ht.ne', hG.ne', Real.pi_ne_zero, hw1, hw2]
    <;> ring
  · unfold SecondFriedmannEq
    rw [hacc]
    dsimp [q]
    field_simp [ht.ne', hG.ne', Real.pi_ne_zero, hw1, hw2]
    <;> ring
