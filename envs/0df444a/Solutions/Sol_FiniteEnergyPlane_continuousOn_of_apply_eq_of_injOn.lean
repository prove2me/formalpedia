-- Prove2me | solution 1 for FiniteEnergyPlane.continuousOn_of_apply_eq_of_injOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T11:39:33.394517+00:00
-- url     : https://prove2.me/submissions/07dfc88a-bcab-429f-b6e3-6d63602ac79a

import Mathlib



/-! A solution `ρ` of `F (t, ρ t) = g t` with values in a compact set `K`, on which every
`F (t, ·)` is injective, is continuous. -/

namespace FiniteEnergyPlane

open Filter Topology

theorem continuousOn_of_apply_eq_of_injOn_aux {E : Type*} [TopologicalSpace E] [T2Space E]
    {S : Set ℝ} {K : Set ℂ} (hK : IsCompact K) {F : ℝ × ℂ → E} {g : ℝ → E} {ρ : ℝ → ℂ}
    (hF : ContinuousOn F (S ×ˢ K)) (hg : ContinuousOn g S) (hρK : ∀ t ∈ S, ρ t ∈ K)
    (heq : ∀ t ∈ S, F (t, ρ t) = g t) (hinj : ∀ t ∈ S, Set.InjOn (fun w => F (t, w)) K) :
    ContinuousOn ρ S := by
  intro t₀ ht₀
  refine hK.tendsto_nhds_of_unique_mapClusterPt
    (eventually_nhdsWithin_of_forall hρK) fun x hx hcl => ?_
  obtain ⟨Uf, hUle, hUt⟩ := mapClusterPt_iff_ultrafilter.1 hcl
  have hS : ∀ᶠ t in (Uf : Filter ℝ), t ∈ S := hUle (self_mem_nhdsWithin)
  have hid : Tendsto (fun t : ℝ => t) (Uf : Filter ℝ) (𝓝 t₀) :=
    (hUle.trans nhdsWithin_le_nhds)
  have hpair : Tendsto (fun t => ((t, ρ t) : ℝ × ℂ)) (Uf : Filter ℝ) (𝓝[S ×ˢ K] (t₀, x)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hid.prodMk_nhds hUt, ?_⟩
    filter_upwards [hS] with t ht
    exact ⟨ht, hρK t ht⟩
  have h1 : Tendsto (fun t => F (t, ρ t)) (Uf : Filter ℝ) (𝓝 (F (t₀, x))) :=
    (hF (t₀, x) ⟨ht₀, hx⟩).tendsto.comp hpair
  have h2 : Tendsto (fun t => F (t, ρ t)) (Uf : Filter ℝ) (𝓝 (g t₀)) := by
    have hg' : Tendsto g (Uf : Filter ℝ) (𝓝 (g t₀)) := (hg t₀ ht₀).tendsto.mono_left hUle
    refine hg'.congr' ?_
    filter_upwards [hS] with t ht
    exact (heq t ht).symm
  have hval : F (t₀, x) = F (t₀, ρ t₀) := by
    rw [heq t₀ ht₀]
    exact tendsto_nhds_unique h1 h2
  exact hinj t₀ ht₀ hx (hρK t₀ ht₀) hval

end FiniteEnergyPlane

open FiniteEnergyPlane

open Filter Topology

theorem solution {E : Type*} [TopologicalSpace E] [T2Space E]
    {S : Set ℝ} {K : Set ℂ} (hK : IsCompact K) {F : ℝ × ℂ → E} {g : ℝ → E} {ρ : ℝ → ℂ}
    (hF : ContinuousOn F (S ×ˢ K)) (hg : ContinuousOn g S) (hρK : ∀ t ∈ S, ρ t ∈ K)
    (heq : ∀ t ∈ S, F (t, ρ t) = g t) (hinj : ∀ t ∈ S, Set.InjOn (fun w => F (t, w)) K) :
    ContinuousOn ρ S :=
  continuousOn_of_apply_eq_of_injOn_aux hK hF hg hρK heq hinj
