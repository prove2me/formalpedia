-- Prove2me | solution 1 for BirkhoffGlobalSection.eh_left_component_regular_compact_starshaped
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T13:19:11.631203+00:00
-- url     : https://prove2.me/submissions/607a1202-6074-440d-a0c8-eb704571c394

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
        IsCompact (ehLeftEnergyComponent μ c) ∧
        (∀ y ∈ ehLeftEnergyComponent μ c,
          fderiv ℝ (ehLeftHamiltonian μ c) y ≠ 0) ∧
        (∀ y ∈ ehLeftEnergyComponent μ c,
          0 < fderiv ℝ (ehLeftHamiltonian μ c) y y) := by
  obtain ⟨ε, η, hε, hη, h⟩ := exists_eps_eta_of_eventually
    ((eventually_component_subset hc₀).and (eventually_star hc₀))
  refine ⟨ε, η, hε, hη, fun μ c h0 h1 hμ hc _ => ?_⟩
  obtain ⟨hsub, hstar⟩ := h μ c hμ hc
  have hsub' := (hsub h0 h1).trans (boxCore_subset_box c₀)
  have hpos : ∀ y ∈ ehLeftEnergyComponent μ c, 0 < fderiv ℝ (ehLeftHamiltonian μ c) y y :=
    fun y hy => hstar y (hsub' hy) (G_zero_of_mem_component hy)
  refine ⟨(isCompact_box c₀).of_isClosed_subset (isClosed_ehLeftEnergyComponent μ c) hsub',
    fun y hy hd => ?_, hpos⟩
  have := hpos y hy
  rw [hd] at this
  simp at this
