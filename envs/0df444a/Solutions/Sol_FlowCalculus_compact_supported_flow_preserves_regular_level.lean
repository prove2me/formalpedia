-- Prove2me | solution 1 for FlowCalculus.compact_supported_flow_preserves_regular_level
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T08:32:39.781273+00:00
-- url     : https://prove2.me/submissions/226e99bd-d021-4659-9afa-f5a6fcc1d8f5

import Definitions.Def_GrayStability_Basic
import Theorems.Thm_FlowCalculus_exists_continuous_bijective_complete_flow
import Theorems.Thm_FlowCalculus_contDiff_complete_solution_family
import Theorems.Thm_FlowCalculus_regular_level_trajectory_invariant
import Theorems.Thm_FlowCalculus_smooth_flow_spatial_derivative_injective
import Theorems.Thm_ImplicitCalculus_tangent_map_of_mapsTo_regular_level
import Mathlib.Tactic.Linarith

open GrayStability Set Function Filter
open scoped ContDiff Topology
set_option autoImplicit false

theorem solution {n c : ℕ}
    (F : E n → (Fin c → ℝ)) (hF : IsCompactRegularLevel F)
    (X : ℝ → E n → E n)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × E n => X p.1 p.2))
    (hsupp : ∃ K : Set (E n), IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0)
    (htan : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F,
      X t y ∈ tangentSpace F y) :
    ∃ ψ : ℝ → E n → E n,
      ContDiff ℝ ∞ (fun p : ℝ × E n => ψ p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧ (∀ t, Function.Bijective (ψ t)) ∧
      (∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t) ∧
      IsIsotopyOf F ψ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F, ∀ v ∈ tangentSpace F y,
        fderiv ℝ (ψ t) y v ∈ tangentSpace F (ψ t y) := by
  obtain ⟨ψ, hc, _, h0, hb, hd⟩ :=
    FlowCalculus.exists_continuous_bijective_complete_flow X hX hsupp
  have hψ := FlowCalculus.contDiff_complete_solution_family X ψ hX hc h0 hd
  have hlevel : ∀ t ∈ Icc (0 : ℝ) 1, BijOn (ψ t) (levelSet F) (levelSet F) := by
    intro t ht
    have hi : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl ht.2
    have hreg : ∀ y, F y = 0 → Surjective (fderiv ℝ F y) := hF.2.2
    have htan' : ∀ s ∈ Icc (0 : ℝ) t, ∀ y, F y = 0 →
        fderiv ℝ F y (X s y) = 0 := fun s hs y hy => htan s (hi hs) y hy
    have hψc : ∀ y, Continuous (fun s => ψ s y) := fun y =>
      hc.comp (continuous_id.prodMk continuous_const)
    refine ⟨?_, (hb t).injective.injOn, ?_⟩
    · intro y hy
      exact FlowCalculus.regular_level_trajectory_invariant F hF.1 hreg X hX 0 t htan'
        (fun s => ψ s y) (hψc y).continuousOn (fun s _ => hd s y)
        (by simpa [h0, levelSet] using hy) t ⟨ht.1, le_rfl⟩
    · intro y hy
      obtain ⟨z, hz⟩ := (hb t).surjective y
      have hmap : MapsTo (fun s : ℝ => -s) (Icc (-t) 0) (Icc 0 t) := by
        intro s hs
        constructor <;> linarith [hs.1, hs.2]
      have hXr : ContDiff ℝ ∞ (fun p : ℝ × E n => -X (-p.1) p.2) :=
        (hX.comp (contDiff_fst.neg.prodMk contDiff_snd)).neg
      have hgr : ContinuousOn (fun s => ψ (-s) z) (Icc (-t) 0) :=
        (hψc z).continuousOn.comp continuousOn_id.neg hmap
      have hdr : ∀ s ∈ Ico (-t) 0,
          HasDerivAt (fun u => ψ (-u) z) (-X (-s) (ψ (-s) z)) s := by
        intro s hs
        simpa [Function.comp_def] using (hd (-s) z).scomp s (hasDerivAt_neg s)
      have hr := FlowCalculus.regular_level_trajectory_invariant F hF.1 hreg
        (fun s w => -X (-s) w) hXr (-t) 0 (by
          intro s hs w hw
          simp [htan' (-s) (hmap hs) w hw])
        (fun s => ψ (-s) z) hgr hdr (by simpa [hz, levelSet] using hy)
      refine ⟨z, ?_, hz⟩
      simpa [h0, levelSet] using hr 0 ⟨by linarith [ht.1], le_rfl⟩
  have hDinj := FlowCalculus.smooth_flow_spatial_derivative_injective X ψ hX hψ h0 hd
  have hψt : ∀ t, Differentiable ℝ (ψ t) := fun t =>
    (hψ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  refine ⟨ψ, hψ, h0, hb, hd, ?_, ?_⟩
  · exact ⟨hψ, fun y _ => h0 y, fun t ht => ⟨hlevel t ht,
      fun y _ => (hDinj t y).injOn⟩⟩
  · intro t ht y hy v hv
    apply ImplicitCalculus.tangent_map_of_mapsTo_regular_level F (fderiv ℝ F y) y v
      (hF.1.hasStrictFDerivAt (by simp)) (hF.2.2 y hy) hv
      (ψ t) F ((hψt t) y) ((hF.1.differentiable (by simp)) (ψ t y))
    apply Filter.Eventually.of_forall
    intro z hz
    have hzM : z ∈ levelSet F := hz.trans hy
    exact ((hlevel t ht).mapsTo hzM).trans ((hlevel t ht).mapsTo hy).symm
