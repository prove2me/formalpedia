-- Prove2me | solution 1 for FiniteEnergyPlane.exists_bound_iteratedFDeriv_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T10:23:11.131798+00:00
-- url     : https://prove2.me/submissions/2e50b799-5ca4-4658-a40e-63d601c071d0

import Mathlib



namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

theorem exists_bound_iteratedFDeriv_of_periodic_aux {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝ × E → F) (T r : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ ∞ Φ (Set.univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (v : E), ‖v‖ < r → Φ (φ + T, v) = Φ (φ, v)) (n : ℕ) :
    ∃ C : ℝ, ∀ (φ : ℝ) (v : E), ‖v‖ ≤ r / 2 → ‖iteratedFDeriv ℝ n Φ (φ, v)‖ ≤ C := by
  set U : Set (ℝ × E) := Set.univ ×ˢ ball (0 : E) r with hU
  have hUo : IsOpen U := isOpen_univ.prod isOpen_ball
  have hcont : ContinuousOn (iteratedFDeriv ℝ n Φ) U := by
    have h1 := hΦ.continuousOn_iteratedFDerivWithin (m := n) (by exact_mod_cast le_top)
      hUo.uniqueDiffOn
    exact h1.congr fun x hx => (iteratedFDerivWithin_of_isOpen n hUo hx).symm
  set K : Set (ℝ × E) := Set.Icc 0 T ×ˢ closedBall (0 : E) (r / 2) with hK
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKU : K ⊆ U := by
    rintro ⟨φ, v⟩ ⟨_, hv⟩
    refine ⟨Set.mem_univ _, ?_⟩
    rw [mem_closedBall_zero_iff] at hv
    rw [mem_ball_zero_iff]
    linarith
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hcont.mono hKU)
  -- periodicity of the derivatives
  have hperD : ∀ (φ : ℝ) (v : E), ‖v‖ < r →
      iteratedFDeriv ℝ n Φ (φ + T, v) = iteratedFDeriv ℝ n Φ (φ, v) := by
    intro φ v hv
    have hx : ((φ, v) : ℝ × E) ∈ U := ⟨Set.mem_univ _, by rwa [mem_ball_zero_iff]⟩
    have hev : (fun z : ℝ × E => Φ (z + (T, 0))) =ᶠ[nhds (φ, v)] Φ := by
      filter_upwards [hUo.mem_nhds hx] with z hz
      obtain ⟨_, hz2⟩ := hz
      rw [mem_ball_zero_iff] at hz2
      obtain ⟨z1, z2⟩ := z
      simp only [Prod.mk_add_mk, add_zero]
      exact hper z1 z2 hz2
    have h2 := (hev.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
    rw [iteratedFDeriv_comp_add_right] at h2
    simpa using h2
  refine ⟨C, fun φ v hv => ?_⟩
  have hvr : ‖v‖ < r := by linarith
  have hP : Function.Periodic (fun ψ : ℝ => iteratedFDeriv ℝ n Φ (ψ, v)) T :=
    fun ψ => hperD ψ v hvr
  obtain ⟨y, hy, hyeq⟩ := hP.exists_mem_Ico₀ hT φ
  rw [show iteratedFDeriv ℝ n Φ (φ, v) = iteratedFDeriv ℝ n Φ (y, v) from hyeq]
  exact hC (y, v) ⟨Set.Ico_subset_Icc_self hy, by rwa [mem_closedBall_zero_iff]⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped ContDiff

theorem solution {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝ × E → F) (T r : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ ∞ Φ (Set.univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (v : E), ‖v‖ < r → Φ (φ + T, v) = Φ (φ, v)) (n : ℕ) :
    ∃ C : ℝ, ∀ (φ : ℝ) (v : E), ‖v‖ ≤ r / 2 → ‖iteratedFDeriv ℝ n Φ (φ, v)‖ ≤ C :=
  exists_bound_iteratedFDeriv_of_periodic_aux Φ T r hT hr hΦ hper n
