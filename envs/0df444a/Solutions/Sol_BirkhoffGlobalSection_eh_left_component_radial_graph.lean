-- Prove2me | solution 1 for BirkhoffGlobalSection.eh_left_component_radial_graph
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T13:19:19.848981+00:00
-- url     : https://prove2.me/submissions/8e6c94da-230e-4188-a474-cbb47c293c82

import Definitions.Def_BirkhoffGlobalSection_EHConvexPerturbation
import Theorems.Thm_BirkhoffGlobalSection_eh_half_mass_star_shaped
open BirkhoffGlobalSection BirkhoffGlobalSection.EHConvex Filter Topology

theorem eventually_star {c₀ : ℝ} (hc₀ : 2 < c₀) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 ((1 : ℝ) / 2, c₀),
      ∀ s ∈ box c₀, ehLeftHamiltonian p.1 p.2 s = 0 →
        0 < fderiv ℝ (ehLeftHamiltonian p.1 p.2) s s := by
  have h := tube_pos_of_compact (P := ℝ × ℝ) (E := Phase) (isCompact_box c₀)
    (C := {q | Ghat (q.1.1, q.1.2, q.2) = 0})
    (isClosed_eq (continuous_Ghat.comp (by fun_prop)) continuous_const)
    (Φ := fun q => fderiv ℝ Ghat (q.1.1, q.1.2, q.2) (L q.2))
    (by
      have := continuous_fderiv_Ghat.comp
        (by fun_prop : Continuous fun q : (ℝ × ℝ) × Phase => (q.1.1, q.1.2, q.2))
      exact this.clm_apply (L.continuous.comp continuous_snd))
    (p₀ := ((1 : ℝ) / 2, c₀))
    (fun s hs hz => by
      rw [← fderiv_G_apply]
      exact eh_half_mass_star_shaped c₀ hc₀ s hz hs.2.1 hs.1)
  filter_upwards [h] with p hp s hs hz
  rw [fderiv_G_apply]
  exact hp s hs hz

theorem solution (c₀ : ℝ) (hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        (∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧
          (fun i : Fin 4 => r * x i) ∈ ehLeftEnergyComponent μ c) ∧
        (∀ x ∈ unitThreeSphere, ∀ r t : ℝ, 0 < r → 0 < t →
          (fun i : Fin 4 => r * x i) ∈ ehLeftEnergyComponent μ c →
          (fun i : Fin 4 => t * x i) ∈ ehLeftEnergyComponent μ c → r = t) ∧
        (∀ x ∈ unitThreeSphere, ∀ R : ℝ, 0 < R →
          (fun i : Fin 4 => R * x i) ∈ ehLeftEnergyComponent μ c →
          ∀ r : ℝ, 0 ≤ r → r < R → ehLeftHamiltonian μ c (fun i : Fin 4 => r * x i) < 0) := by
  obtain ⟨ε, η, hε, hη, h⟩ := exists_eps_eta_of_eventually
    (((eventually_component_subset hc₀).and (eventually_star hc₀)).and (eventually_faces hc₀))
  refine ⟨ε, η, hε, hη, fun μ c h0 h1 hμ hc _ => ?_⟩
  obtain ⟨⟨hsub, hstar⟩, hfaces⟩ := h μ c hμ hc
  have hG : ContDiff ℝ 1 (ehLeftHamiltonian μ c) := by unfold ehLeftHamiltonian; fun_prop
  have hcomp := (hsub h0 h1).trans (boxCore_subset_box c₀)
  exact radial_graph_generic (G := ehLeftHamiltonian μ c) hG (isCompact_box c₀)
    (isOpen_boxCore c₀) (boxCore_subset_box c₀) box_smul (by rw [G_at_zero]; linarith)
    hfaces hstar (G_collision μ c h1.le) (boxCore_subset_box c₀ (collision_mem_boxCore hc₀ h0))
    hcomp
