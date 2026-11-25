-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.exists_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:18:28.846265+00:00
-- url     : https://prove2.me/submissions/f36a9270-9de2-4dd9-917e-85a05b3b6c10

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CovolIdxK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.Pf.NcReal.JX.CovB Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
theorem _root_.solution {m : ℕ} (c : Fin m → 𝓞 K) (hc : c ≠ 0) (𝔭 : Ideal (𝓞 K)) (h𝔭 : 𝔭 ≠ ⊤) :
    ∃ t : K, (∀ i, ∃ o : 𝓞 K, (o : K) = t * (c i : K)) ∧ ∃ i, ∀ o : 𝓞 K, (o : K) = t * (c i : K) → o ∉ 𝔭 := by
  classical
  obtain ⟨𝔪, h𝔪, hp𝔪⟩ := Ideal.exists_le_maximal 𝔭 h𝔭
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (funext h)
  have hJ0 : Ideal.span (Set.range c) ≠ ⊥ := by
    intro h
    have hmem : c j ∈ Ideal.span (Set.range c) := Ideal.subset_span ⟨j, rfl⟩
    rw [h, Ideal.mem_bot] at hmem
    exact hj hmem
  have hJF : ((Ideal.span (Set.range c) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hJ0
  by_contra H
  push_neg at H
  have hle : ((Ideal.span (Set.range c) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
      ((Ideal.span (Set.range c) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ ≤
      ((𝔪 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.mul_le]
    intro x hx t ht
    rw [FractionalIdeal.mem_coeIdeal] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [FractionalIdeal.mem_inv_iff hJF] at ht
    have hint_r : ∀ i, ∃ o : 𝓞 K, (o : K) = t * (c i : K) := by
      intro i
      have hci : algebraMap (𝓞 K) K (c i) ∈
          ((Ideal.span (Set.range c) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
        rw [FractionalIdeal.mem_coeIdeal]
        exact ⟨c i, Ideal.subset_span ⟨i, rfl⟩, rfl⟩
      have h1 := ht _ hci
      rw [FractionalIdeal.mem_one_iff] at h1
      obtain ⟨o, ho⟩ := h1
      exact ⟨o, ho⟩
    have hS : Ideal.span (Set.range c) ≤ Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) K t)
        (((𝔪 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨o, ho, hop⟩ := H t hint_r i
      show (LinearMap.toSpanSingleton (𝓞 K) K t) (c i) ∈
        (((𝔪 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
      rw [LinearMap.toSpanSingleton_apply, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal]
      refine ⟨o, hp𝔪 hop, ?_⟩
      rw [Algebra.smul_def, mul_comm]
      exact ho
    have hyS := hS hy
    rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, FractionalIdeal.mem_coe,
      Algebra.smul_def] at hyS
    exact hyS
  first
  | rw [mul_inv_cancel₀ hJF] at hle
  | rw [FractionalIdeal.mul_inv_cancel hJF] at hle
  rw [← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_le_coeIdeal] at hle
  exact h𝔪.ne_top (top_le_iff.mp hle)
end Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
