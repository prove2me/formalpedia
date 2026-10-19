-- Prove2me | solution 1 for GarrettFA.isQuasiComplete_pointwiseConvergenceCLM
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:33:58.843984+00:00
-- url     : https://prove2.me/submissions/62b1767f-37ad-45e7-bae0-6a60431d2461

import Mathlib
import Definitions.Def_GarrettFA_IsQuasiComplete
import Definitions.Def_GarrettFA_IsFrechetSpace
import Definitions.Def_GarrettFA_IsLFSpace
import Theorems.Thm_GarrettFA_banach_steinhaus

open Topology Set Filter
open scoped PointwiseConvergenceCLM

namespace GAGoal

/-- net convergence in the platform sense implies filter convergence -/
lemma tendsto_of_net {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    {J : Type*} [Preorder J] (a : J → Y) (y : Y)
    (h : ∀ N ∈ 𝓝 (0 : Y), ∃ j₀ : J, ∀ j ≥ j₀, a j - y ∈ N) : Tendsto a atTop (𝓝 y) := by
  intro S hS
  have hN : (fun z => z + y) ⁻¹' S ∈ 𝓝 (0 : Y) :=
    (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (by simpa using hS)
  obtain ⟨j₀, hj₀⟩ := h _ hN
  rw [mem_map]
  exact mem_of_superset (mem_atTop j₀) fun j hj => by
    have := hj₀ j hj
    simpa using this

/-- quasi-completeness, stated for nets indexed in `Y`'s universe, extends to nets indexed in
any universe (re-index by the tails of the net) -/
lemma converge_any {𝕜 : Type*} [RCLike 𝕜] {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y]
    [TopologicalSpace Y] [IsTopologicalAddGroup Y] (hY : GarrettFA.IsQuasiComplete 𝕜 Y)
    {J : Type*} [PartialOrder J] [IsDirected J (· ≤ ·)] [Nonempty J] (w : J → Y)
    (hb : Bornology.IsVonNBounded 𝕜 (range w))
    (hC : ∀ N ∈ 𝓝 (0 : Y), ∃ j₀ : J, ∀ i ≥ j₀, ∀ j ≥ j₀, w i - w j ∈ N) :
    ∃ y : Y, ∀ N ∈ 𝓝 (0 : Y), ∃ j₀ : J, ∀ j ≥ j₀, w j - y ∈ N := by
  -- index set: tails, ordered by reverse inclusion
  let K0 := {T : Set Y // ∃ j, T = w '' Ici j}
  let K := K0ᵒᵈ
  let S : K → Set Y := fun A => (OrderDual.ofDual A).1
  have hS : ∀ A : K, ∃ j, S A = w '' Ici j := fun A => (OrderDual.ofDual A).2
  have hle : ∀ A B : K, A ≤ B ↔ S B ⊆ S A := fun A B => Iff.rfl
  let tail : J → K := fun j => OrderDual.toDual ⟨w '' Ici j, j, rfl⟩
  have hStail : ∀ j, S (tail j) = w '' Ici j := fun j => rfl
  have hdir : IsDirected K (· ≤ ·) := ⟨fun A B => by
    obtain ⟨j₁, h₁⟩ := hS A
    obtain ⟨j₂, h₂⟩ := hS B
    obtain ⟨j₃, h13, h23⟩ := directed_of (· ≤ ·) j₁ j₂
    refine ⟨tail j₃, ?_, ?_⟩
    · rw [hle, hStail, h₁]; exact image_mono (Ici_subset_Ici.mpr h13)
    · rw [hle, hStail, h₂]; exact image_mono (Ici_subset_Ici.mpr h23)⟩
  have hne : ∀ A : K, (S A).Nonempty := fun A => by
    obtain ⟨j, hj⟩ := hS A; rw [hj]; exact ⟨w j, j, le_rfl, rfl⟩
  choose p hp using hne
  have hsub : range p ⊆ range w := by
    rintro _ ⟨A, rfl⟩
    obtain ⟨j, hj⟩ := hS A
    have := hp A; rw [hj] at this
    obtain ⟨i, -, hi⟩ := this
    exact ⟨i, hi⟩
  have hpin : ∀ (A : K) (j : J), tail j ≤ A → ∃ i ≥ j, p A = w i := by
    intro A j hA
    rw [hle, hStail] at hA
    obtain ⟨i, hi, he⟩ := hA (hp A)
    exact ⟨i, hi, he.symm⟩
  have hCp : ∀ N ∈ 𝓝 (0 : Y), ∃ A₀ : K, ∀ A ≥ A₀, ∀ B ≥ A₀, p A - p B ∈ N := by
    intro N hN
    obtain ⟨j₀, hj₀⟩ := hC N hN
    refine ⟨tail j₀, fun A hA B hB => ?_⟩
    obtain ⟨i, hi, hiA⟩ := hpin A j₀ hA
    obtain ⟨k, hk, hkB⟩ := hpin B j₀ hB
    rw [hiA, hkB]; exact hj₀ i hi k hk
  obtain ⟨y, hy⟩ := hY K p (hb.subset hsub) hCp
  refine ⟨y, fun N hN => ?_⟩
  obtain ⟨N', hN', hN'N⟩ := exists_nhds_zero_half hN
  obtain ⟨j₀, hj₀⟩ := hC N' hN'
  obtain ⟨A₁, hA₁⟩ := hy N' hN'
  obtain ⟨j₁, hj₁⟩ := hS A₁
  obtain ⟨j₂, h02, h12⟩ := directed_of (· ≤ ·) j₀ j₁
  have hle2 : A₁ ≤ tail j₂ := by
    rw [hle, hStail, hj₁]; exact image_mono (Ici_subset_Ici.mpr h12)
  obtain ⟨k, hk, hpk⟩ := hpin (tail j₂) j₂ le_rfl
  have h1 := hA₁ (tail j₂) hle2
  rw [hpk] at h1
  refine ⟨j₂, fun j hj => ?_⟩
  have h2 := hj₀ j (h02.trans hj) k (h02.trans hk)
  have := hN'N _ h2 _ h1
  simpa using this

end GAGoal

open GAGoal in
theorem solution {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [AddCommGroup X] [Module 𝕜 X] [Module ℝ X]
    [IsScalarTower ℝ 𝕜 X] [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul 𝕜 X] [T2Space X]
    (hX : GarrettFA.IsFrechetSpace 𝕜 X ∨ GarrettFA.IsLFSpace 𝕜 X)
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [Module ℝ Y] [IsScalarTower ℝ 𝕜 Y]
    [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul 𝕜 Y] [LocallyConvexSpace ℝ Y]
    [T2Space Y]
    (hY : GarrettFA.IsQuasiComplete 𝕜 Y) :
    GarrettFA.IsQuasiComplete 𝕜 (X →Lₚₜ[𝕜] Y) := by
  intro I _ _ v hbdd hC
  have hI : Nonempty I := by
    obtain ⟨i₀, -⟩ := hC univ univ_mem
    exact ⟨i₀⟩
  -- pointwise limits
  have hpt : ∀ x : X, ∃ y : Y, Tendsto (fun i => v i x) atTop (𝓝 y) := by
    intro x
    have hb : Bornology.IsVonNBounded 𝕜 (range fun i => v i x) := by
      have := hbdd.image (PointwiseConvergenceCLM.evalCLM (RingHom.id 𝕜) Y x)
      rw [← range_comp] at this
      exact this
    have hCx : ∀ N ∈ 𝓝 (0 : Y), ∃ j₀ : I, ∀ i ≥ j₀, ∀ j ≥ j₀, v i x - v j x ∈ N := by
      intro N hN
      have hN' : (fun φ : X →Lₚₜ[𝕜] Y => φ x) ⁻¹' N ∈ 𝓝 (0 : X →Lₚₜ[𝕜] Y) :=
        (continuous_eval_const x).continuousAt.preimage_mem_nhds (by simpa using hN)
      obtain ⟨j₀, hj₀⟩ := hC _ hN'
      exact ⟨j₀, fun i hi j hj => by simpa using hj₀ i hi j hj⟩
    obtain ⟨y, hy⟩ := converge_any hY (fun i => v i x) hb hCx
    exact ⟨y, tendsto_of_net _ y hy⟩
  choose g hg using hpt
  have hadd : ∀ x y, g (x + y) = g x + g y := by
    intro x y
    have h2 := hg (x + y)
    simp only [map_add] at h2
    exact tendsto_nhds_unique h2 ((hg x).add (hg y))
  have hsmul : ∀ (c : 𝕜) x, g (c • x) = c • g x := by
    intro c x
    have h2 := hg (c • x)
    simp only [map_smul] at h2
    exact tendsto_nhds_unique h2 ((hg x).const_smul c)
  let gl : X →ₗ[𝕜] Y := { toFun := g, map_add' := hadd, map_smul' := hsmul }
  -- continuity via Banach–Steinhaus
  set E : Set (X →L[𝕜] Y) := range (fun i => (v i : X →L[𝕜] Y)) with hEdef
  have hE : ∀ x, Bornology.IsVonNBounded 𝕜 ((fun T : X →L[𝕜] Y => T x) '' E) := by
    intro x
    have := hbdd.image (PointwiseConvergenceCLM.evalCLM (RingHom.id 𝕜) Y x)
    have hs : (fun T : X →L[𝕜] Y => T x) '' E =
        (PointwiseConvergenceCLM.evalCLM (RingHom.id 𝕜) Y x) '' range v := by
      ext z
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨v i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨v i, ⟨i, rfl⟩, rfl⟩
    rw [hs]; exact this
  have heq := GarrettFA.banach_steinhaus hX E hE
  have hcont : Continuous gl := by
    have : ContinuousAt gl.toAddMonoidHom 0 := by
      intro U hU
      have hg0 : g 0 = 0 := by
        have := hadd 0 0
        simp only [add_zero] at this
        exact left_eq_add.mp this
      have hU' : U ∈ 𝓝 (0 : Y) := by
        have : U ∈ 𝓝 (g 0) := hU
        rwa [hg0] at this
      obtain ⟨W, hW, hWc, hWU⟩ := exists_mem_nhds_isClosed_subset hU'
      obtain ⟨N, hN, hNW⟩ := heq W hW
      rw [mem_map]
      refine mem_of_superset hN fun x hx => hWU ?_
      exact hWc.mem_of_tendsto (hg x) (Filter.Eventually.of_forall fun i =>
        hNW _ ⟨(v i : X →L[𝕜] Y), ⟨i, rfl⟩, rfl⟩ hx)
    exact continuous_of_continuousAt_zero gl.toAddMonoidHom this
  let gc : X →Lₚₜ[𝕜] Y := (⟨gl, hcont⟩ : X →L[𝕜] Y)
  refine ⟨gc, ?_⟩
  have ht : Tendsto (fun i => v i - gc) atTop (𝓝 (0 : X →Lₚₜ[𝕜] Y)) := by
    rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
    intro x
    have := (hg x).sub_const (g x)
    rw [sub_self] at this
    exact this
  intro N hN
  exact eventually_atTop.mp (ht hN)
