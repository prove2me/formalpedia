-- Prove2me | solution 1 for CGSpace.continuous_eval
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:01:07.591344+00:00
-- url     : https://prove2.me/submissions/391244d1-97d8-4bd4-8e1b-c08c310db346

import Definitions.Def_CGSpace_FunctionSpace

open Topology TopologicalSpace

set_option autoImplicit false

universe u

open CGSpace

namespace Sol_CGSpace_continuous_eval

/-- The `k`-ification of a topology is finer than the topology. -/
theorem compactlyGenerated_le (X : Type u) [t : TopologicalSpace X] :
    compactlyGenerated.{u} X ≤ t := by
  simp only [compactlyGenerated, ← continuous_iff_coinduced_le, continuous_sigma_iff,
    Sigma.forall]
  exact fun S f ↦ f.2

/-- Evaluation along a pair of continuous maps from a compact Hausdorff space: if
`a₁ : S → C(Y, Z)` is continuous for the compact-open topology defined by test maps and
`a₂ : S → Y` is continuous, then `t ↦ a₁ t (a₂ t)` is continuous. -/
theorem continuous_eval_comp {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    {S : Type u} [TopologicalSpace S] [CompactSpace S] [T2Space S] (a₁ : S → C(Y, Z))
    (ha₁ : Continuous[inferInstance, probeCompactOpen Y Z] a₁)
    (a₂ : S → Y) (ha₂ : Continuous a₂) : Continuous (fun t : S => a₁ t (a₂ t)) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_nhds]
  intro U hU hmem
  -- a neighbourhood of `t₀` on which the single map `a₁ t₀ ∘ a₂` takes values in `U`
  have hV : (fun t : S => a₁ t₀ (a₂ t)) ⁻¹' U ∈ 𝓝 t₀ :=
    ((a₁ t₀).continuous.comp ha₂).continuousAt.preimage_mem_nhds (hU.mem_nhds hmem)
  -- shrink it to a compact neighbourhood `K`
  obtain ⟨K, hK_nhds, hK_sub, hK_compact⟩ := local_compact_nhds hV
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK_compact
  -- the sub-basic open set `N(a₂|K, U)`
  have hN : IsOpen[probeCompactOpen Y Z] {f : C(Y, Z) | ∀ t : K, f (a₂ t) ∈ U} :=
    TopologicalSpace.isOpen_generateFrom_of_mem
      ⟨CompHaus.of K, ⟨fun t : K => a₂ t, ha₂.comp continuous_subtype_val⟩, U, hU, rfl⟩
  have h1 : a₁ ⁻¹' {f : C(Y, Z) | ∀ t : K, f (a₂ t) ∈ U} ∈ 𝓝 t₀ :=
    (continuous_def.mp ha₁ _ hN).mem_nhds (fun t => hK_sub t.2)
  filter_upwards [h1, hK_nhds] with t ht htK
  exact ht ⟨t, htK⟩

end Sol_CGSpace_continuous_eval

open Sol_CGSpace_continuous_eval

theorem solution
    (Y Z : Type u) [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactlyGeneratedSpace Y] [CompactlyGeneratedSpace Z] :
    Continuous (fun p : KSpace (ContK Y Z × Y) =>
      ContK.toContinuousMap (KSpace.mk.symm p).1 (KSpace.mk.symm p).2) := by
  refine continuous_from_compactlyGenerated (X := ContK Y Z × Y)
    (fun p : ContK Y Z × Y => ContK.toContinuousMap p.1 p.2) ?_
  intro S g
  -- the first component is continuous for the `k`-ified topology, hence for the
  -- compact-open topology defined by test maps
  have h₁ : Continuous (fun t : S => (g t).1) := continuous_fst.comp g.continuous
  have h₁' : Continuous[inferInstance, probeCompactOpen Y Z]
      (fun t : S => ContK.toContinuousMap (g t).1) :=
    continuous_le_rng (compactlyGenerated_le (t := probeCompactOpen Y Z) C(Y, Z)) h₁
  have h₂ : Continuous (fun t : S => (g t).2) := continuous_snd.comp g.continuous
  exact continuous_eval_comp _ h₁' _ h₂
