-- Prove2me | solution 1 for GarrettFA.weakDual_isNetComplete_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:28:11.485611+00:00
-- url     : https://prove2.me/submissions/58ba6e15-4c3d-4836-b0a7-2f85a66ba362

import Mathlib
import Definitions.Def_GarrettFA_IsQuasiComplete
import Definitions.Def_GarrettFA_IsNetComplete

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

namespace GANC

lemma sepDual {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V] [LocallyConvexSpace ℝ V] : SeparatingDual 𝕜 V :=
  ⟨fun x hx => by
    obtain ⟨f, hf⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := 𝕜) hx
    exact ⟨f, fun h => by simp [h] at hf⟩⟩

/-- continuous functionals agreeing with a given linear functional on a finite set -/
lemma exists_agree {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V] [LocallyConvexSpace ℝ V] (f : V →ₗ[𝕜] 𝕜) (S : Finset V) :
    ∃ ψ : V →L[𝕜] 𝕜, ∀ s ∈ S, ψ s = f s := by
  have := sepDual (𝕜 := 𝕜) (V := V)
  set W := Submodule.span 𝕜 (S : Set V)
  have hsurj := (SeparatingDual.dualMap_surjective_iff (R := 𝕜) (V := V) (W := W)
    (f := W.subtype)).mpr (Submodule.injective_subtype W)
  obtain ⟨ψ, hψ⟩ := hsurj (f.comp W.subtype)
  refine ⟨ψ, fun s hs => ?_⟩
  have := LinearMap.congr_fun hψ ⟨s, Submodule.subset_span hs⟩
  simpa using this

end GANC

open GAWD GANC in
theorem solution {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V]
    [LocallyConvexSpace ℝ V] :
    GarrettFA.IsNetComplete (WeakDual 𝕜 V) ↔ ∀ f : V →ₗ[𝕜] 𝕜, Continuous f := by
  classical
  constructor
  · intro hc f
    choose ψ hψ using exists_agree f
    let I := ULift.{u_1} (Finset V)
    let v : I → WeakDual 𝕜 V := fun S => (ψ S.down : V →L[𝕜] 𝕜)
    have hv : ∀ (S : I) (x : V), x ∈ S.down → v S x = f x := fun S x hx => hψ S.down x hx
    have : Nonempty I := ⟨⟨∅⟩⟩
    have : IsDirected I (· ≤ ·) := ⟨fun a b => ⟨⟨a.down ∪ b.down⟩,
      (Finset.subset_union_left : a.down ⊆ a.down ∪ b.down),
      (Finset.subset_union_right : b.down ⊆ a.down ∪ b.down)⟩⟩
    -- eventually (S ⊇ {x}) v S x = f x
    have hev : ∀ x : V, ∀ᶠ S in (atTop : Filter I), v S x = f x := by
      intro x
      filter_upwards [eventually_ge_atTop (⟨{x}⟩ : I)] with S hS
      exact hv S x (by
        have : ({x} : Finset V) ⊆ S.down := hS
        exact this (Finset.mem_singleton_self x))
    -- Cauchy
    have hT : Tendsto (fun p : I × I => v p.1 - v p.2) atTop (𝓝 (0 : WeakDual 𝕜 V)) := by
      refine (WeakBilin.tendsto_iff_forall_eval_tendsto (B := topDualPairing 𝕜 V)
        (f := fun p : I × I => v p.1 - v p.2) (x := (0 : WeakDual 𝕜 V))
        (fun a b hab => ContinuousLinearMap.ext fun y => LinearMap.congr_fun hab y)).2 ?_
      intro x
      apply tendsto_const_nhds.congr'
      have h1 := (hev x).prod_mk (hev x)
      rw [← prod_atTop_atTop_eq]
      filter_upwards [h1] with p hp
      show (0 : 𝕜) = v p.1 x - v p.2 x
      rw [hp.1, hp.2, sub_self]
    have hC : ∀ N ∈ 𝓝 (0 : WeakDual 𝕜 V), ∃ i₀ : I, ∀ i ≥ i₀, ∀ j ≥ i₀, v i - v j ∈ N := by
      intro N hN
      obtain ⟨a, ha⟩ := eventually_atTop_prod_self.mp (hT hN)
      exact ⟨a, fun i hi j hj => ha i j hi hj⟩
    obtain ⟨g, hg⟩ := hc I v hC
    have hfg : ∀ x, g x = f x := by
      intro x
      by_contra hne
      have hpos : 0 < ‖g x - f x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have hN : {φ : WeakDual 𝕜 V | ‖φ x‖ < ‖g x - f x‖} ∈ 𝓝 (0 : WeakDual 𝕜 V) := by
        apply (isOpen_lt (continuous_norm.comp (WeakDual.eval_continuous x))
          continuous_const).mem_nhds
        show ‖(0 : WeakDual 𝕜 V) x‖ < ‖g x - f x‖
        rw [show (0 : WeakDual 𝕜 V) x = 0 from rfl, norm_zero]; exact hpos
      obtain ⟨i₀, hi₀⟩ := hg _ hN
      let i₁ : I := ⟨i₀.down ∪ {x}⟩
      have hle : i₀ ≤ i₁ := by
        show i₀.down ≤ i₁.down
        exact Finset.subset_union_left
      have h1 := hi₀ i₁ hle
      have h2 : v i₁ x = f x := hv i₁ x (Finset.mem_union_right _ (Finset.mem_singleton_self x))
      have e : (v i₁ - g) x = v i₁ x - g x := rfl
      rw [mem_setOf_eq, e, h2, norm_sub_rev] at h1
      exact lt_irrefl _ h1
    have : (f : V → 𝕜) = fun x => g x := funext fun x => (hfg x).symm
    rw [this]
    exact (show V →L[𝕜] 𝕜 from g).continuous
  · intro hall I _ _ v hC
    have := nonempty_of_cauchy v hC
    obtain ⟨g, hg⟩ := pointwise_limit v hC
    let gc : V →L[𝕜] 𝕜 := ⟨g, hall g⟩
    exact ⟨gc, converge v gc hg⟩
