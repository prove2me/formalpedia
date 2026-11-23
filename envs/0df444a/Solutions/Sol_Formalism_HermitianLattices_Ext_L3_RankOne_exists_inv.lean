-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.RankOne.exists_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:38.559003+00:00
-- url     : https://prove2.me/submissions/d4c67547-19d1-4ce8-ba5b-9952feca5b59

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNeZeroOfIsLattice
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_exists_ne_zero_of_isLattice
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_span_eq_top_of_ne_zero
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
open NumberField Module nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne
open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.RankOne
theorem _root_.solution {A : Submodule (𝓞 K) K} (hA : Submodule.IsLattice K A) :
    ∃ A' : Submodule (𝓞 K) K, Submodule.IsLattice K A' ∧ A' * A = 1 := by
  obtain ⟨a, ha, ha0⟩ := exists_ne_zero_of_isLattice hA
  let I : FractionalIdeal (𝓞 K)⁰ K := ⟨A, FractionalIdeal.isFractional_of_fg hA.fg⟩
  have hI : I ≠ 0 := by
    intro h
    have h' : a ∈ (I : Submodule (𝓞 K) K) := ha
    rw [h, FractionalIdeal.coe_zero, Submodule.mem_bot] at h'
    exact ha0 h'
  have hmul : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) * A = 1 := by
    have e := congrArg (fun J : FractionalIdeal (𝓞 K)⁰ K => (J : Submodule (𝓞 K) K))
      (inv_mul_cancel₀ hI)
    have e2 : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) * (I : Submodule (𝓞 K) K) = 1 := by
      simpa only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one] using e
    exact e2
  refine ⟨_, ⟨FractionalIdeal.fg_of_isNoetherianRing le_rfl _, ?_⟩, hmul⟩
  have hne : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≠ ⊥ := by
    intro hb
    rw [hb, Submodule.bot_mul] at hmul
    have h1 : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.one_le.1 le_rfl
    rw [← hmul, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact span_eq_top_of_ne_zero hc hc0
end Formalism.HermitianLattices.Ext.L3.RankOne
