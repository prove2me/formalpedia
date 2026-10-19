-- Prove2me | solution 1 for GarrettFA.isQuasiComplete_weakDual
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:25:41.369188+00:00
-- url     : https://prove2.me/submissions/44d7fe2f-34ce-4e12-9d44-670db553bbc3

import Mathlib
import Definitions.Def_GarrettFA_IsQuasiComplete
import Definitions.Def_GarrettFA_IsNetComplete
import Definitions.Def_GarrettFA_IsFrechetSpace
import Definitions.Def_GarrettFA_IsLFSpace
import Theorems.Thm_GarrettFA_banach_steinhaus

open Topology Set Filter

namespace GAWD

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]

/-- evaluation as a continuous linear map on the weak dual -/
noncomputable def evalCLM (x : X) : WeakDual 𝕜 X →L[𝕜] 𝕜 where
  toFun φ := φ x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := WeakDual.eval_continuous x

lemma nonempty_of_cauchy {I : Type*} [PartialOrder I] (v : I → WeakDual 𝕜 X)
    (hC : ∀ N ∈ 𝓝 (0 : WeakDual 𝕜 X), ∃ i₀ : I, ∀ i ≥ i₀, ∀ j ≥ i₀, v i - v j ∈ N) :
    Nonempty I := by
  obtain ⟨i₀, -⟩ := hC univ univ_mem
  exact ⟨i₀⟩

/-- pointwise limits of a Cauchy net exist and form a linear functional -/
lemma pointwise_limit {I : Type*} [PartialOrder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (v : I → WeakDual 𝕜 X)
    (hC : ∀ N ∈ 𝓝 (0 : WeakDual 𝕜 X), ∃ i₀ : I, ∀ i ≥ i₀, ∀ j ≥ i₀, v i - v j ∈ N) :
    ∃ g : X →ₗ[𝕜] 𝕜, ∀ x, Tendsto (fun i => v i x) atTop (𝓝 (g x)) := by
  have hcauchy : ∀ x : X, Cauchy (map (fun i => v i x) atTop) := by
    intro x
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    have hN : {φ : WeakDual 𝕜 X | ‖φ x‖ < ε} ∈ 𝓝 (0 : WeakDual 𝕜 X) := by
      apply (isOpen_lt (continuous_norm.comp (WeakDual.eval_continuous x)) continuous_const).mem_nhds
      show ‖(0 : WeakDual 𝕜 X) x‖ < ε
      rw [show (0 : WeakDual 𝕜 X) x = 0 from rfl, norm_zero]; exact hε
    obtain ⟨i₀, hi₀⟩ := hC _ hN
    refine ⟨(fun i => v i x) '' Ici i₀, ?_, ?_⟩
    · rw [mem_map]
      exact mem_of_superset (mem_atTop i₀) (fun i hi => ⟨i, hi, rfl⟩)
    · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      have := hi₀ i hi j hj
      have e : (v i - v j) x = v i x - v j x := rfl
      rw [mem_setOf_eq, e] at this
      rw [dist_eq_norm]
      exact this
  choose g hg using fun x => CompleteSpace.complete (hcauchy x)
  have hg' : ∀ x, Tendsto (fun i => v i x) atTop (𝓝 (g x)) := hg
  refine ⟨{ toFun := g, map_add' := ?_, map_smul' := ?_ }, hg'⟩
  · intro x y
    have h1 := (hg' x).add (hg' y)
    have h2 := hg' (x + y)
    simp only [map_add] at h2
    exact tendsto_nhds_unique h2 h1
  · intro c x
    have h1 := (hg' x).const_smul c
    have h2 := hg' (c • x)
    simp only [map_smul] at h2
    exact tendsto_nhds_unique h2 h1

/-- pointwise convergence gives convergence in the platform's net sense -/
lemma converge {I : Type*} [PartialOrder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (v : I → WeakDual 𝕜 X) (g : WeakDual 𝕜 X)
    (h : ∀ x, Tendsto (fun i => v i x) atTop (𝓝 (g x))) :
    ∀ N ∈ 𝓝 (0 : WeakDual 𝕜 X), ∃ i₀ : I, ∀ i ≥ i₀, v i - g ∈ N := by
  have ht : Tendsto (fun i => v i - g) atTop (𝓝 (0 : WeakDual 𝕜 X)) := by
    refine (WeakBilin.tendsto_iff_forall_eval_tendsto (B := topDualPairing 𝕜 X)
      (f := fun i => v i - g) (x := (0 : WeakDual 𝕜 X))
      (fun a b hab => ContinuousLinearMap.ext fun y => LinearMap.congr_fun hab y)).2 ?_
    intro x
    have := (h x).sub_const (g x)
    rw [sub_self] at this
    exact this
  intro N hN
  exact eventually_atTop.mp (ht hN)

end GAWD

open Topology Set Filter

open GAWD in
theorem solution {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [AddCommGroup X] [Module 𝕜 X] [Module ℝ X]
    [IsScalarTower ℝ 𝕜 X] [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul 𝕜 X] [T2Space X]
    (hX : GarrettFA.IsFrechetSpace 𝕜 X ∨ GarrettFA.IsLFSpace 𝕜 X) :
    GarrettFA.IsQuasiComplete 𝕜 (WeakDual 𝕜 X) := by
  intro I _ _ v hbdd hC
  have := nonempty_of_cauchy v hC
  obtain ⟨g, hg⟩ := pointwise_limit v hC
  set E : Set (X →L[𝕜] 𝕜) := range (fun i => (v i : X →L[𝕜] 𝕜)) with hEdef
  have hE : ∀ x, Bornology.IsVonNBounded 𝕜 ((fun T : X →L[𝕜] 𝕜 => T x) '' E) := by
    intro x
    have hs : (fun T : X →L[𝕜] 𝕜 => T x) '' E = (evalCLM (𝕜 := 𝕜) x) '' (range v) := by
      ext z
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨v i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨v i, ⟨i, rfl⟩, rfl⟩
    rw [hs]
    exact hbdd.image _
  have heq := GarrettFA.banach_steinhaus hX E hE
  have hcont : Continuous g := by
    have : ContinuousAt g.toAddMonoidHom 0 := by
      rw [ContinuousAt, Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨N, hN, hNU⟩ := heq (Metric.ball 0 (ε / 2)) (Metric.ball_mem_nhds 0 (by positivity))
      filter_upwards [hN] with x hx
      have hb : ∀ i, ‖v i x‖ ≤ ε / 2 := by
        intro i
        have := hNU _ ⟨(v i : X →L[𝕜] 𝕜), ⟨i, rfl⟩, rfl⟩ hx
        simp only [Metric.mem_ball, dist_zero_right] at this
        exact this.le
      have hl : ‖g x‖ ≤ ε / 2 :=
        le_of_tendsto (hg x).norm (Filter.Eventually.of_forall hb)
      simp only [LinearMap.toAddMonoidHom_coe, map_zero, dist_zero_right]
      linarith
    exact continuous_of_continuousAt_zero g.toAddMonoidHom this
  let gc : X →L[𝕜] 𝕜 := ⟨g, hcont⟩
  exact ⟨gc, converge v gc hg⟩
