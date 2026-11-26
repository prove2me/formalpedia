-- Prove2me | solution 1 for FiniteEnergyPlane.injOn_Ico_of_hasLoopWind_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-26T21:45:08.119793+00:00
-- url     : https://prove2.me/submissions/3bf16d4c-77cf-4fca-8109-a7e3b0f6cd14

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib



/-! Child W of P c5a21fab (via G): `injOn_Ico_of_hasLoopWind_one`. -/

namespace FiniteEnergyPlane

open Metric Set Filter Topology

/-- A continuous, locally injective real function on `ℝ` is injective. -/
theorem olpw_injective_of_locally (θ : ℝ → ℝ) (hθ : Continuous θ)
    (hloc : ∀ t, ∃ ε > 0, InjOn θ (ball t ε)) : Function.Injective θ := by
  -- no interior local extremum
  have hnoext : ∀ m : ℝ, ∀ u v : ℝ, u < m → m < v →
      ¬ ((∀ x ∈ Ioo u v, θ x ≤ θ m) ∨ (∀ x ∈ Ioo u v, θ m ≤ θ x)) := by
    intro m u v hu hv hext
    obtain ⟨ε, hε, hinj⟩ := hloc m
    set δ := min ε (min (m - u) (v - m)) / 2 with hδ
    have hδpos : 0 < δ := by
      have : 0 < min ε (min (m - u) (v - m)) := lt_min hε (lt_min (by linarith) (by linarith))
      linarith
    have hδε : δ < ε := by
      have : min ε (min (m - u) (v - m)) ≤ ε := min_le_left _ _
      linarith
    have hδu : δ < m - u := by
      have : min ε (min (m - u) (v - m)) ≤ m - u := (min_le_right _ _).trans (min_le_left _ _)
      linarith
    have hδv : δ < v - m := by
      have : min ε (min (m - u) (v - m)) ≤ v - m := (min_le_right _ _).trans (min_le_right _ _)
      linarith
    have hsub : Ioo (m - δ) (m + δ) ⊆ ball m ε := by
      intro x hx; rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2]
    have hmono := (hθ.continuousOn).strictMonoOn_of_injOn_Ioo (by linarith : m - δ < m + δ)
      (hinj.mono hsub)
    have hm : m ∈ Ioo (m - δ) (m + δ) := ⟨by linarith, by linarith⟩
    have hl : m - δ / 2 ∈ Ioo (m - δ) (m + δ) := ⟨by linarith, by linarith⟩
    have hr : m + δ / 2 ∈ Ioo (m - δ) (m + δ) := ⟨by linarith, by linarith⟩
    have hlI : m - δ / 2 ∈ Ioo u v := ⟨by linarith, by linarith⟩
    have hrI : m + δ / 2 ∈ Ioo u v := ⟨by linarith, by linarith⟩
    rcases hmono with hmono | hmono
    · have h1 := hmono hm hr (by linarith)
      have h2 := hmono hl hm (by linarith)
      rcases hext with hext | hext
      · linarith [hext _ hrI]
      · linarith [hext _ hlI]
    · have h1 := hmono hm hr (by linarith)
      have h2 := hmono hl hm (by linarith)
      rcases hext with hext | hext
      · linarith [hext _ hlI]
      · linarith [hext _ hrI]
  suffices key : ∀ a b, θ a = θ b → a < b → False by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key a b hab h
    · exact key b a hab.symm h
  intro a b hab hlt
  obtain ⟨M, hM, hMmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hlt.le) hθ.continuousOn
  obtain ⟨N, hN, hNmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hlt.le) hθ.continuousOn
  by_cases hc : θ M = θ a ∧ θ N = θ a
  · -- constant on `[a, b]`, contradicting local injectivity at `a`
    obtain ⟨ε, hε, hinj⟩ := hloc ((a + b) / 2)
    set x := (a + b) / 2
    set y := x + min ε ((b - a) / 2) / 2
    have hpos : 0 < min ε ((b - a) / 2) := lt_min hε (by linarith)
    have hyb : y ≤ b := by
      have : min ε ((b - a) / 2) ≤ (b - a) / 2 := min_le_right _ _
      simp only [y, x]; linarith
    have hxI : x ∈ Icc a b := ⟨by simp only [x]; linarith, by simp only [x]; linarith⟩
    have hyI : y ∈ Icc a b := ⟨by simp only [y, x]; linarith, hyb⟩
    have hconst : ∀ z ∈ Icc a b, θ z = θ a := fun z hz =>
      le_antisymm (hc.1 ▸ hMmax hz) (hc.2 ▸ hNmin hz)
    have hxb : x ∈ ball x ε := mem_ball_self hε
    have hyb' : y ∈ ball x ε := by
      rw [mem_ball, Real.dist_eq]
      have : min ε ((b - a) / 2) ≤ ε := min_le_left _ _
      simp only [y]
      rw [abs_of_pos (by linarith)]
      linarith
    have := hinj hyb' hxb (by rw [hconst y hyI, hconst x hxI])
    simp only [y] at this
    linarith
  · push_neg at hc
    by_cases hMa : θ M = θ a
    · have hNa := hc hMa
      have hNI : N ∈ Ioo a b := by
        refine ⟨lt_of_le_of_ne hN.1 ?_, lt_of_le_of_ne hN.2 ?_⟩
        · rintro rfl; exact hNa rfl
        · rintro rfl; exact hNa hab.symm
      exact hnoext N a b hNI.1 hNI.2 (Or.inr fun x hx => hNmin (Ioo_subset_Icc_self hx))
    · have hMI : M ∈ Ioo a b := by
        refine ⟨lt_of_le_of_ne hM.1 ?_, lt_of_le_of_ne hM.2 ?_⟩
        · rintro rfl; exact hMa rfl
        · rintro rfl; exact hMa hab.symm
      exact hnoext M a b hMI.1 hMI.2 (Or.inl fun x hx => hMmax (Ioo_subset_Icc_self hx))

theorem injOn_Ico_of_hasLoopWind_one_aux (γ : ℝ → ℂ) (hγ : HasLoopWind γ 1)
    (h1 : ∀ t, ‖γ t‖ = 1) (hloc : ∀ t, ∃ ε > 0, InjOn γ (ball t ε)) : InjOn γ (Ico 0 1) := by
  obtain ⟨-, -, -, θ, hθc, hθ, hθ1⟩ := hγ
  have hγθ : ∀ t, γ t = Complex.exp ((θ t : ℂ) * Complex.I) := fun t => by
    rw [hθ t, h1 t]; simp
  have hθloc : ∀ t, ∃ ε > 0, InjOn θ (ball t ε) := by
    intro t
    obtain ⟨ε, hε, hinj⟩ := hloc t
    exact ⟨ε, hε, fun x hx y hy hxy => hinj hx hy (by rw [hγθ x, hγθ y, hxy])⟩
  have hθinj := olpw_injective_of_locally θ hθc hθloc
  have hmono : StrictMono θ := by
    rcases hθc.strictMono_of_inj hθinj with h | h
    · exact h
    · have := h (zero_lt_one : (0 : ℝ) < 1)
      have : (0 : ℝ) < 2 * Real.pi * ((1 : ℤ) : ℝ) := by simp [Real.pi_pos]
      linarith
  intro x hx y hy hxy
  rw [hγθ x, hγθ y, Complex.exp_eq_exp_iff_exists_int] at hxy
  obtain ⟨n, hn⟩ := hxy
  have him := congrArg Complex.im hn
  simp at him
  have hx0 := hmono.monotone hx.1
  have hx1 := hmono hx.2
  have hy0 := hmono.monotone hy.1
  have hy1 := hmono hy.2
  have hθ1' : θ 1 = θ 0 + 2 * Real.pi := by simp at hθ1; linarith
  have hn0 : n = 0 := by
    have hlt : (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by nlinarith
    have hgt : -(2 * Real.pi) < (n : ℝ) * (2 * Real.pi) := by nlinarith
    have hpi := Real.pi_pos
    have h1' : (n : ℝ) < 1 := by nlinarith
    have h2' : (-1 : ℝ) < n := by nlinarith
    have : n < 1 := by exact_mod_cast h1'
    have : -1 < n := by exact_mod_cast h2'
    omega
  rw [hn0] at him
  simp at him
  exact hθinj (by linarith)

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Set

theorem solution (γ : ℝ → ℂ) (hγ : HasLoopWind γ 1) (h1 : ∀ t, ‖γ t‖ = 1)
    (hloc : ∀ t, ∃ ε > 0, InjOn γ (ball t ε)) : InjOn γ (Ico 0 1) :=
  injOn_Ico_of_hasLoopWind_one_aux γ hγ h1 hloc
