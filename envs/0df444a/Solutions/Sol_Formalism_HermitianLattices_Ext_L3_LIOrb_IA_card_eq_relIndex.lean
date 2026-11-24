-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.IA.card_eq_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:10:31.619577+00:00
-- url     : https://prove2.me/submissions/0f727bcb-2699-4918-8d58-9d7ec8b9afcb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardEqRelIndex
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_IA_pow_smul_locF
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_IsStep_change
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb Formalism.HermitianLattices.Ext.L3.LIOrb.IA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.LIOrb.IA
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {M N : Submodule (𝓞 K) V} {r : ℕ}
    (hr : ∀ a ∈ 𝔭 ^ r, ∀ y ∈ M, ι a • y ∈ locF 𝔭 N) :
    Nat.card (↥(locF 𝔭 M) ⧸ (locF 𝔭 M ⊓ locF 𝔭 N).submoduleOf (locF 𝔭 M)) =
      (M ⊓ locF 𝔭 N).toAddSubgroup.relIndex M.toAddSubgroup := by
  set B' := (locF 𝔭 M ⊓ locF 𝔭 N).submoduleOf (locF 𝔭 M) with hB'
  let φ : ↥M →ₗ[𝓞 K] ↥(locF 𝔭 M) ⧸ B' := B'.mkQ ∘ₗ Submodule.inclusion (LocF.le_locF 𝔭 M)
  have hsurj : Function.Surjective φ := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H x =>
    obtain ⟨c, hc, hcx⟩ := localizedQuotients.exists_approx h𝔭 M r x.2
    refine ⟨⟨_, hcx⟩, ?_⟩
    simp only [φ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    change (ι c • (x : V) - (x : V)) ∈ locF 𝔭 M ⊓ locF 𝔭 N
    have e : ι c • (x : V) - (x : V) = ι (c - 1) • (x : V) := by
      rw [map_sub, map_one, sub_smul, one_smul]
    rw [e]
    exact Submodule.mem_inf.2 ⟨(locF 𝔭 M).smul_mem _ x.2, pow_smul_locF h𝔭 hr hc x.2⟩
  have hker : (LinearMap.ker φ).toAddSubgroup =
      (M ⊓ locF 𝔭 N).toAddSubgroup.addSubgroupOf M.toAddSubgroup := by
    ext y
    rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, LinearMap.mem_ker]
    simp only [φ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    change ((y : V) ∈ locF 𝔭 M ⊓ locF 𝔭 N) ↔ (y : V) ∈ M ⊓ locF 𝔭 N
    rw [Submodule.mem_inf, Submodule.mem_inf]
    exact ⟨fun h => ⟨y.2, h.2⟩, fun h => ⟨LocF.le_locF 𝔭 M y.2, h.2⟩⟩
  rw [AddSubgroup.relIndex, AddSubgroup.index, ← hker]
  exact (Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv).symm
end Formalism.HermitianLattices.Ext.L3.LIOrb.IA
