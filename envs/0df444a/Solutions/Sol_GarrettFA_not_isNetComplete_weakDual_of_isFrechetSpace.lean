-- Prove2me | solution 1 for GarrettFA.not_isNetComplete_weakDual_of_isFrechetSpace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:30:59.160431+00:00
-- url     : https://prove2.me/submissions/f1d29215-d91e-43c6-b6d3-ebdb15d40b51

import Mathlib
import Definitions.Def_GarrettFA_IsNetComplete
import Definitions.Def_GarrettFA_IsFrechetSpace
import Theorems.Thm_GarrettFA_weakDual_isNetComplete_iff

open Topology Set Filter

namespace GADisc

/-- an infinite-dimensional first-countable TVS has a linearly independent null sequence -/
lemma exists_seq {𝕜 : Type*} [RCLike 𝕜] {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y]
    [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul 𝕜 Y]
    [FirstCountableTopology Y] (hinf : ¬ FiniteDimensional 𝕜 Y) :
    ∃ x : ℕ → Y, LinearIndependent 𝕜 x ∧ Tendsto x atTop (𝓝 0) := by
  set b := Module.Basis.ofVectorSpace 𝕜 Y
  have hι : Infinite (Module.Basis.ofVectorSpaceIndex 𝕜 Y) := by
    by_contra h
    rw [not_infinite_iff_finite] at h
    exact hinf (Module.Finite.of_basis b)
  set emb := Infinite.natEmbedding (Module.Basis.ofVectorSpaceIndex 𝕜 Y)
  set y : ℕ → Y := fun k => b (emb k) with hy
  have hli : LinearIndependent 𝕜 y := b.linearIndependent.comp emb emb.injective
  obtain ⟨U, hU⟩ := (𝓝 (0 : Y)).exists_antitone_basis
  have hc : ∀ k, ∃ c : 𝕜, c ≠ 0 ∧ c • y k ∈ U k := by
    intro k
    have ht : Tendsto (fun t : 𝕜 => t • y k) (𝓝[≠] 0) (𝓝 0) := by
      have : Tendsto (fun t : 𝕜 => t • y k) (𝓝 0) (𝓝 ((0 : 𝕜) • y k)) :=
        (continuous_id.smul continuous_const).tendsto 0
      rw [zero_smul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[≠] (0 : 𝕜), t • y k ∈ U k ∧ t ∈ ({0}ᶜ : Set 𝕜) :=
      (ht.eventually_mem (hU.mem k)).and self_mem_nhdsWithin
    obtain ⟨c, hc1, hc2⟩ := hev.exists
    exact ⟨c, hc2, hc1⟩
  choose c hc0 hcU using hc
  refine ⟨fun k => c k • y k, ?_, hU.tendsto hcU⟩
  have := hli.units_smul (fun k => Units.mk0 (c k) (hc0 k))
  convert this using 1
  ext k
  simp [Units.smul_def]

/-- a linearly independent null sequence yields a discontinuous linear functional -/
lemma exists_discont {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [AddCommGroup X] [Module 𝕜 X]
    [TopologicalSpace X] (x : ℕ → X) (hli : LinearIndependent 𝕜 x)
    (ht : Tendsto x atTop (𝓝 0)) : ∃ f : X →ₗ[𝕜] 𝕜, ¬ Continuous f := by
  set bW := Module.Basis.span hli
  set φ : Submodule.span 𝕜 (range x) →ₗ[𝕜] 𝕜 := bW.constr 𝕜 (fun _ => (1 : 𝕜))
  obtain ⟨g, hg⟩ := LinearMap.exists_extend φ
  refine ⟨g, fun hcont => ?_⟩
  have hgx : ∀ k, g (x k) = 1 := by
    intro k
    have h1 : g (x k) = φ (bW k) := by
      rw [← hg]
      simp [bW, Module.Basis.span_apply]
    rw [h1]
    simp [φ, Module.Basis.constr_basis]
  have h2 : Tendsto (fun k => g (x k)) atTop (𝓝 (g 0)) := (hcont.tendsto 0).comp ht
  simp only [hgx, map_zero] at h2
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h2)

end GADisc

open GADisc in
theorem solution {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [AddCommGroup X] [Module 𝕜 X] [Module ℝ X]
    [IsScalarTower ℝ 𝕜 X] [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul 𝕜 X] [T2Space X]
    (hX : GarrettFA.IsFrechetSpace 𝕜 X) (hinf : ¬ FiniteDimensional 𝕜 X) :
    ¬ GarrettFA.IsNetComplete (WeakDual 𝕜 X) := by
  intro hnc
  have : LocallyConvexSpace ℝ X := hX.1
  have : TopologicalSpace.MetrizableSpace X := hX.2.1
  have hall := (GarrettFA.weakDual_isNetComplete_iff (𝕜 := 𝕜) (V := X)).mp hnc
  obtain ⟨x, hli, ht⟩ := exists_seq (𝕜 := 𝕜) hinf
  obtain ⟨f, hf⟩ := exists_discont x hli ht
  exact hf (hall f)
