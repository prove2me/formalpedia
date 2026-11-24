-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.relIndex_ne_zero_of_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:49:18.158024+00:00
-- url     : https://prove2.me/submissions/bd59bbe1-0c1c-4484-bb8c-71d44cb775c1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution {G X : Type*} [Group G] [Finite X] (H Γ : Subgroup G) (f : H → X)
    (hf : ∀ a b : H, f a = f b → (a : G)⁻¹ * b ∈ Γ) : Γ.relIndex H ≠ 0 := by
  classical
  show (Γ.subgroupOf H).index ≠ 0
  have hfin : Finite (H ⧸ Γ.subgroupOf H) := by
    let g : Set.range f → H ⧸ Γ.subgroupOf H := fun x => QuotientGroup.mk x.2.choose
    apply Finite.of_surjective g
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      refine ⟨⟨f a, a, rfl⟩, ?_⟩
      show QuotientGroup.mk _ = QuotientGroup.mk a
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hf _ _ (⟨f a, a, rfl⟩ : Set.range f).2.choose_spec
  exact Subgroup.index_ne_zero_of_finite
end Formalism.HermitianLattices.Ext.L3.LIOrb
