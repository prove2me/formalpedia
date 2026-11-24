-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_span_RP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:24.426885+00:00
-- url     : https://prove2.me/submissions/6b0801ce-ff26-468e-bdd5-20e7c0182ff8

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_mem_locF
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocalSpans
variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LocalSpans
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (N : Submodule (𝓞 K) V) (x : V) :
    x ∈ Submodule.span (RP K 𝔭) (N : Set V) ↔ x ∈ locF 𝔭 N := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact (mem_locF 𝔭 N x).2 ⟨1, fun h => (Ideal.ne_top_iff_one 𝔭).1 (Ideal.IsPrime.ne_top inferInstance) h, by simpa using hx⟩
    | zero => exact (locF 𝔭 N).zero_mem
    | add x y _ _ hx hy => exact (locF 𝔭 N).add_mem hx hy
    | smul c x _ hx =>
      obtain ⟨a, s, ⟨t, ht, rfl⟩, hc⟩ := c.2
      obtain ⟨u, hu, hx⟩ := (mem_locF 𝔭 N x).1 hx
      refine (mem_locF 𝔭 N _).2 ⟨t * u, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ht hu, ?_⟩
      have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
        intro h0
        have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
        have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
        exact ht (h2 ▸ 𝔭.zero_mem)
      have : algebraMap (𝓞 F) (𝓞 K) (t * u) • c • x = a • (algebraMap (𝓞 F) (𝓞 K) u • x) := by
        rw [Subalgebra.smul_def, hc, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) (t * u)),
          ← algebraMap_smul K a, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) u), smul_smul, smul_smul,
          map_mul, map_mul]
        congr 1
        field_simp
      rw [this]
      exact N.smul_mem _ hx
  · intro hx
    obtain ⟨t, ht, hx⟩ := (mem_locF 𝔭 N x).1 hx
    have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
      intro h0
      have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
      have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
      exact ht (h2 ▸ 𝔭.zero_mem)
    let c : RP K 𝔭 := ⟨(algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹,
      ⟨1, _, ⟨t, ht, rfl⟩, by simp⟩⟩
    have : x = c • (algebraMap (𝓞 F) (𝓞 K) t • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t), smul_smul,
        inv_mul_cancel₀ ht0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)
end Formalism.HermitianLattices.Ext.L3.LocalSpans
