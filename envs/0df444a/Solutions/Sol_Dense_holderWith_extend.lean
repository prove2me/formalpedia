-- Prove2me | solution 1 for Dense.holderWith_extend
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:01:31.31564+00:00
-- url     : https://prove2.me/submissions/8a508af3-6649-47c7-b5fd-017260c0ca2a

import Definitions.Def_BrownianMotion_Auxiliary_Topology_F000
import Mathlib.Topology.UniformSpace.UniformEmbedding

open Bornology Filter
open scoped NNReal ENNReal Topology

theorem solution {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [CompleteSpace Y]
    {C r : ℝ≥0} {s : Set X} {f : s → Y}
    (hs : Dense s) (hf : HolderWith C r f) (hr : 0 < r) :
    HolderWith C r (hs.extend f) := by
  have huc : UniformContinuous f := hf.uniformContinuous hr
  have hext : ∀ x : X, Tendsto f ((𝓝 x).comap ((↑) : s → X)) (𝓝 (hs.extend f x)) :=
    fun x => hs.extend_spec huc x
  intro x₁ x₂
  haveI : ((𝓝 x₁).comap ((↑) : s → X)).NeBot := neBot_comap_nhds hs x₁
  haveI : ((𝓝 x₂).comap ((↑) : s → X)).NeBot := neBot_comap_nhds hs x₂
  have ht1 : Tendsto (fun p : s × s => edist (f p.1) (f p.2))
      (((𝓝 x₁).comap ((↑) : s → X)) ×ˢ ((𝓝 x₂).comap ((↑) : s → X)))
      (𝓝 (edist (hs.extend f x₁) (hs.extend f x₂))) :=
    ((hext x₁).comp tendsto_fst).edist ((hext x₂).comp tendsto_snd)
  have ht2 : Tendsto (fun p : s × s => (C : ℝ≥0∞) * edist (p.1 : X) (p.2 : X) ^ (r : ℝ))
      (((𝓝 x₁).comap ((↑) : s → X)) ×ˢ ((𝓝 x₂).comap ((↑) : s → X)))
      (𝓝 ((C : ℝ≥0∞) * edist x₁ x₂ ^ (r : ℝ))) := by
    have hval1 : Tendsto (fun p : s × s => (p.1 : X))
        (((𝓝 x₁).comap ((↑) : s → X)) ×ˢ ((𝓝 x₂).comap ((↑) : s → X))) (𝓝 x₁) :=
      tendsto_comap.comp tendsto_fst
    have hval2 : Tendsto (fun p : s × s => (p.2 : X))
        (((𝓝 x₁).comap ((↑) : s → X)) ×ˢ ((𝓝 x₂).comap ((↑) : s → X))) (𝓝 x₂) :=
      tendsto_comap.comp tendsto_snd
    exact ENNReal.Tendsto.const_mul ((hval1.edist hval2).ennrpow_const _)
      (Or.inr ENNReal.coe_ne_top)
  exact le_of_tendsto_of_tendsto' ht1 ht2 fun p => hf p.1 p.2
