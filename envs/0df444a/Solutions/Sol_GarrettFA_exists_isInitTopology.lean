-- Prove2me | solution 1 for GarrettFA.exists_isInitTopology
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:08:59.18502+00:00
-- url     : https://prove2.me/submissions/44c980f2-b5e0-48b9-bafc-39f94cc09d72

import Definitions.Def_GarrettFA_IsInitTopology

open Topology Filter

theorem solution {𝕜 : Type*} [RCLike 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] [Module ℝ V] [IsScalarTower ℝ 𝕜 V] :
    ∃ τ : TopologicalSpace V, @IsTopologicalAddGroup V τ _ ∧ @ContinuousSMul 𝕜 V _ _ τ ∧
      @T2Space V τ ∧ @GarrettFA.IsInitTopology 𝕜 V _ _ _ _ _ τ := by
  let p : SeminormFamily 𝕜 V (Seminorm 𝕜 V) := fun q => q
  letI τ : TopologicalSpace V := p.moduleFilterBasis.topology
  have hp : WithSeminorms p := ⟨rfl⟩
  haveI := hp.topologicalAddGroup
  haveI := hp.continuousSMul
  have hsep : ∀ x : V, x ≠ 0 → ∃ q : Seminorm 𝕜 V, p q x ≠ 0 := by
    intro x hx
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual 𝕜 V, f x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx ((Module.forall_dual_apply_eq_zero_iff 𝕜 x).mp h)
    refine ⟨(normSeminorm 𝕜 𝕜).comp f, ?_⟩
    simpa [p] using hf
  haveI : T1Space V := hp.T1_of_separating hsep
  refine ⟨τ, inferInstance, inferInstance, inferInstance, ⟨hp.toLocallyConvexSpace, ?_⟩⟩
  intro U hbal hconv hW
  have habs : Absorbent ℝ U := by
    rw [absorbent_iff_eventually_nhdsNE_zero]
    intro x
    let W : Submodule 𝕜 V := Submodule.span 𝕜 {x}
    have hxW : x ∈ W := Submodule.mem_span_singleton_self x
    have hWU := hW W inferInstance
    let g : 𝕜 → W := fun c => c • (⟨x, hxW⟩ : W)
    have hg : Continuous g := continuous_id.smul continuous_const
    have h0 : g 0 = 0 := by simp [g]
    have h1 : ∀ᶠ c : 𝕜 in 𝓝 0, c • x ∈ U := by
      have := hg.tendsto 0
      rw [h0] at this
      exact this hWU
    have h2 : Tendsto (fun c : ℝ => (c : 𝕜)) (𝓝[≠] 0) (𝓝 0) := by
      have : Tendsto (fun c : ℝ => (c : 𝕜)) (𝓝 0) (𝓝 ((0 : ℝ) : 𝕜)) :=
        (RCLike.continuous_ofReal (K := 𝕜)).tendsto 0
      rw [RCLike.ofReal_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    filter_upwards [h2 h1] with c hc
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    exact hc
  let q := gaugeSeminorm hbal hconv habs
  rw [hp.mem_nhds_iff]
  refine ⟨{q}, 1, one_pos, ?_⟩
  intro y hy
  rw [Finset.sup_singleton, Seminorm.mem_ball_zero] at hy
  exact setOfPred_gauge_lt_one_subset_self hconv habs.zero_mem habs hy
