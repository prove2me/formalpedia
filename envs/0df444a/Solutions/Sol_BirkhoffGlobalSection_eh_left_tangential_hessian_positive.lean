-- Prove2me | solution 1 for BirkhoffGlobalSection.eh_left_tangential_hessian_positive
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T13:19:18.158737+00:00
-- url     : https://prove2.me/submissions/3acfe3fb-ebda-4d3b-891a-d3e9d6d675d4

import Definitions.Def_BirkhoffGlobalSection_EHConvexPerturbation
import Theorems.Thm_BirkhoffGlobalSection_eh_half_mass_tangential_hessian
open BirkhoffGlobalSection BirkhoffGlobalSection.EHConvex Filter Topology

theorem eventually_hess {c₀ : ℝ} (hc₀ : 2 < c₀) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 ((1 : ℝ) / 2, c₀),
      ∀ y ∈ box c₀ ×ˢ Metric.sphere (0 : Phase) 1,
        (ehLeftHamiltonian p.1 p.2 y.1 = 0 ∧
          fderiv ℝ (ehLeftHamiltonian p.1 p.2) y.1 y.2 = 0) →
        0 < fderiv ℝ (fun x => fderiv ℝ (ehLeftHamiltonian p.1 p.2) x y.2) y.1 y.2 := by
  have hcont : Continuous fun q : (ℝ × ℝ) × (Phase × Phase) =>
      ((q.1.1, q.1.2, q.2.1) : ℝ × ℝ × Phase) := by fun_prop
  have h := tube_pos_of_compact (P := ℝ × ℝ) (E := Phase × Phase)
    ((isCompact_box c₀).prod (isCompact_sphere 0 1))
    (C := {q | Ghat (q.1.1, q.1.2, q.2.1) = 0 ∧
      fderiv ℝ Ghat (q.1.1, q.1.2, q.2.1) (L q.2.2) = 0})
    (IsClosed.inter (isClosed_eq (continuous_Ghat.comp hcont) continuous_const)
      (isClosed_eq ((continuous_fderiv_Ghat.comp hcont).clm_apply
        (L.continuous.comp (by fun_prop))) continuous_const))
    (Φ := fun q => fderiv ℝ (fderiv ℝ Ghat) (q.1.1, q.1.2, q.2.1) (L q.2.2) (L q.2.2))
    (((continuous_fderiv2_Ghat.comp hcont).clm_apply
        (L.continuous.comp (by fun_prop))).clm_apply (L.continuous.comp (by fun_prop)))
    (p₀ := ((1 : ℝ) / 2, c₀))
    (fun y hy hC => by
      obtain ⟨hb, hsph⟩ := hy
      rw [← hess_G_eq]
      have hv : y.2 ≠ 0 := by
        intro h0; rw [mem_sphere_zero_iff_norm, h0, norm_zero] at hsph; norm_num at hsph
      exact eh_half_mass_tangential_hessian c₀ hc₀ y.1 hC.1 hb.2.1 hb.1 y.2 hv
        (by rw [fderiv_G_apply]; exact hC.2))
  filter_upwards [h] with p hp y hy hC
  rw [hess_G_eq]
  exact hp y hy ⟨hC.1, by rw [← fderiv_G_apply]; exact hC.2⟩

theorem solution (c₀ : ℝ) (hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        HasPositiveTangentialHessianOn (ehLeftHamiltonian μ c)
          (ehLeftEnergyComponent μ c) := by
  obtain ⟨ε, η, hε, hη, h⟩ := exists_eps_eta_of_eventually
    ((eventually_component_subset hc₀).and (eventually_hess hc₀))
  refine ⟨ε, η, hε, hη, fun μ c h0 h1 hμ hc _ => ?_⟩
  obtain ⟨hsub, hhess⟩ := h μ c hμ hc
  have hsub' := (hsub h0 h1).trans (boxCore_subset_box c₀)
  refine ⟨fun s _ => ?_, fun s hs v hv htan => ?_⟩
  · have : ContDiff ℝ 2 (ehLeftHamiltonian μ c) := by
      unfold ehLeftHamiltonian; fun_prop
    exact this.contDiffAt
  · set t : ℝ := ‖v‖⁻¹ with ht
    have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have htpos : 0 < t := inv_pos.mpr hnv
    have hw : t • v ∈ Metric.sphere (0 : Phase) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos htpos, ht,
        inv_mul_cancel₀ hnv.ne']
    have htan' : fderiv ℝ (ehLeftHamiltonian μ c) s (t • v) = 0 := by
      rw [map_smul, htan, smul_zero]
    have := hhess (s, t • v) ⟨hsub' hs, hw⟩ ⟨G_zero_of_mem_component hs, htan'⟩
    simp only at this
    rw [hess_G_eq] at this
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul] at this
    rw [hess_G_eq]
    have h2 : 0 < t * t := mul_pos htpos htpos
    nlinarith
