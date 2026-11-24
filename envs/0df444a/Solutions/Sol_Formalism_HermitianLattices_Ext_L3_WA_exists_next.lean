-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.exists_next
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:36.886418+00:00
-- url     : https://prove2.me/submissions/9b841a8e-8b08-4bc5-9c6f-d912dacf692b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_exists_norm_one_mul_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_exists_norm_one_of_pair


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}
namespace Formalism.HermitianLattices.Ext.L3.WA
theorem _root_.solution (hS : IsHermSemilocal S) (hs : h.IsSymm) (hM : IsSelfDualMod S h M)
    {ι : Type*} [DecidableEq ι] (x : ι → V) (hx : ∀ i j, h (x i) (x j) = if i = j then 1 else 0)
    (s : Finset ι) (hxM : ∀ i ∈ s, x i ∈ M) (j : ι) (hj : j ∉ s) :
    ∃ z ∈ M, h z z = 1 ∧ ∀ i ∈ s, h (x i) z = 0 := by
  have hl : ∀ (c : K) (u w : V), h (c • u) w = star c * h u w := by
    intro c u w
    rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]
  have hr : ∀ (c : K) (u w : V), h u (c • w) = c * h u w := by
    intro c u w
    simp
  have hsym : ∀ u w : V, star (h u w) = h w u := by
    intro u w
    have hsu := hs.eq u w
    rwa [starRingEnd_apply] at hsu
  have hxx : h (x j) (x j) = 1 := by
    rw [hx]
    simp
  have hxj : ∀ i ∈ s, h (x i) (x j) = 0 := by
    intro i hi
    have hij : i ≠ j := fun e => hj (e ▸ hi)
    rw [hx]
    simp [hij]
  have hjx : ∀ i ∈ s, h (x j) (x i) = 0 := by
    intro i hi
    rw [← hsym, hxj i hi, star_zero]
  obtain ⟨t, ht0, htM⟩ := hM.span (x j)
  have hmemA : ∀ a : K, a ∈ M.map (h (x j)).toAddMonoidHom ↔ ∃ m ∈ M, h (x j) m = a := by
    intro a
    rw [AddSubgroup.mem_map]
    rfl
  obtain ⟨α, hαA, hα0, hαS⟩ := hS.principal (M.map (h (x j)).toAddMonoidHom)
    (by
      intro r hr' a ha
      obtain ⟨m, hm, rfl⟩ := (hmemA a).1 ha
      exact (hmemA _).2 ⟨r • m, hM.smul_mem r hr' m hm, hr r _ _⟩)
    ⟨t, (hmemA t).2 ⟨t • x j, htM, by rw [hr, hxx, mul_one]⟩, ht0⟩
    ⟨star t, star_ne_zero.2 ht0, fun a ha => by
      obtain ⟨m, hm, rfl⟩ := (hmemA a).1 ha
      rw [← hl]
      exact hM.int _ htM m hm⟩
  obtain ⟨w1, hw1M, hw1⟩ := (hmemA α).1 hαA
  obtain ⟨a2, ha2⟩ : ∃ a2 : K, a2 = star α⁻¹ := ⟨_, rfl⟩
  have ha20 : a2 ≠ 0 := by
    rw [ha2]
    exact star_ne_zero.2 (inv_ne_zero hα0)
  have hvM : a2 • x j ∈ M := by
    apply hM.dual
    intro m hm
    rw [hr, ← hsym]
    have h1 := hS.star_mem _ (hαS _ ((hmemA _).2 ⟨m, hm, rfl⟩))
    rw [star_mul', ← ha2, mul_comm] at h1
    exact h1
  have hcM : ∀ i ∈ s, (h (x i) w1) • x i ∈ M := fun i hi =>
    hM.smul_mem _ (hM.int _ (hxM i hi) _ hw1M) _ (hxM i hi)
  have hw0M : w1 - ∑ i ∈ s, (h (x i) w1) • x i ∈ M :=
    M.sub_mem hw1M (M.sum_mem hcM)
  have hw0o : ∀ k ∈ s, h (x k) (w1 - ∑ i ∈ s, (h (x i) w1) • x i) = 0 := by
    intro k hk
    rw [map_sub, map_sum]
    simp only [hr, hx]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq', hk]
  have hvw : h (a2 • x j) (w1 - ∑ i ∈ s, (h (x i) w1) • x i) = 1 := by
    rw [map_sub, map_sum, Finset.sum_eq_zero, sub_zero, hl, hw1, ha2, star_star,
      inv_mul_cancel₀ hα0]
    intro i hi
    rw [hr, hl, hjx i hi, mul_zero, mul_zero]
  have hvvS : star a2 * a2 ∈ S := by
    have := hM.int _ hvM _ hvM
    rwa [hl, hr, hxx, mul_one] at this
  obtain ⟨b, hb1, hbS⟩ := exists_norm_one_mul_mem hS hvvS
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb1
  obtain ⟨c, hc, d, hd, hcd⟩ := exists_norm_one_of_pair hS hs (y := b • a2 • x j)
    (w := b • (w1 - ∑ i ∈ s, (h (x i) w1) • x i)) (a := a2 * b) hbS (mul_ne_zero ha20 hb0)
    (by rw [hl, hr, hl, hr, hxx, star_mul']; ring)
    (by rw [hl, hr, hvw, mul_one, hb1])
    (by rw [hl, hr, ← mul_assoc, hb1, one_mul]; exact hM.int _ hw0M _ hw0M)
  refine ⟨c • (w1 - ∑ i ∈ s, (h (x i) w1) • x i) + d • a2 • x j,
    M.add_mem (hM.smul_mem c hc _ hw0M) (hM.smul_mem d hd _ hvM), ?_, ?_⟩
  · rw [smul_comm c b, smul_comm d b, ← smul_add, hl, hr, ← mul_assoc, hb1, one_mul] at hcd
    exact hcd
  · intro i hi
    rw [map_add, hr, hr, hw0o i hi, hr, hxj i hi]
    simp
end Formalism.HermitianLattices.Ext.L3.WA
