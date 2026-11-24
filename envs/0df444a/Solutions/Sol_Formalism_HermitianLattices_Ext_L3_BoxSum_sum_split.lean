-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:28.290467+00:00
-- url     : https://prove2.me/submissions/14bed241-fbe6-4383-89dc-8abd9029a188

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumCoset
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumPeriodic
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_finite_box_inter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) {b 𝔞 : Ideal (𝓞 F)}
    [Fintype (𝓞 F ⧸ 𝔞)] (hco : b ⊔ 𝔞 = ⊤) (x₀ : 𝓞 F) (g : 𝓞 F → ℝ) (φ : 𝓞 F ⧸ 𝔞 → ℝ)
    (x : 𝓞 F ⧸ 𝔞 → 𝓞 F) (hx : ∀ c, x c - x₀ ∈ b ∧ Ideal.Quotient.mk 𝔞 (x c) = c) :
    ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n - x₀ ∈ b}, g n * φ (Ideal.Quotient.mk 𝔞 n) =
      ∑ c, φ c * ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n - x c ∈ b * 𝔞}, g n := by
  set S := {n : 𝓞 F | n ∈ boxSet K F T ∧ n - x₀ ∈ b} with hSdef
  have hS : S.Finite := finite_box_inter hK hF T {n | n - x₀ ∈ b}
  have hT : ∀ c, {n : 𝓞 F | n ∈ boxSet K F T ∧ n - x c ∈ b * 𝔞} = {n | n ∈ S ∧ Ideal.Quotient.mk 𝔞 n = c} := by
    intro c
    ext n
    simp only [Set.mem_setOf_eq, hSdef]
    rw [Ideal.mul_eq_inf_of_coprime hco, Ideal.mem_inf]
    constructor
    · rintro ⟨hn, h1, h2⟩
      refine ⟨⟨hn, ?_⟩, ?_⟩
      · have := b.add_mem h1 (hx c).1
        rwa [sub_add_sub_cancel] at this
      · rw [← (hx c).2]
        exact Ideal.Quotient.eq.mpr h2
    · rintro ⟨⟨hn, h1⟩, h2⟩
      refine ⟨hn, ?_, ?_⟩
      · have := b.sub_mem h1 (hx c).1
        rwa [sub_sub_sub_cancel_right] at this
      · rw [← (hx c).2] at h2
        exact Ideal.Quotient.eq.mp h2
  have hSc : ∀ c, ({n | n ∈ S ∧ Ideal.Quotient.mk 𝔞 n = c} : Set (𝓞 F)).Finite :=
    fun c => hS.subset fun n hn => hn.1
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, ← Finset.sum_fiberwise hS.toFinset (Ideal.Quotient.mk 𝔞)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hT c, finsum_mem_eq_finite_toFinset_sum _ (hSc c), Finset.mul_sum]
  have e : (hSc c).toFinset = hS.toFinset.filter (fun n => Ideal.Quotient.mk 𝔞 n = c) := by
    ext n
    simp
  rw [e]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [(Finset.mem_filter.mp hn).2, mul_comm]
end Formalism.HermitianLattices.Ext.L3.BoxSum
