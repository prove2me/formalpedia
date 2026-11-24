-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.IA.relIndex_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:41:18.992846+00:00
-- url     : https://prove2.me/submissions/3f00c511-ead1-41a1-809e-686c10fe718d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardEqRelIndex
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_exists_zsmul_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb Formalism.HermitianLattices.Ext.L3.LIOrb.IA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.LIOrb.IA
theorem _root_.solution {M N : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M)
    (hN : Submodule.IsLattice K N) (𝔭 : Ideal (𝓞 F)) :
    (M ⊓ locF 𝔭 N).toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := by
  obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hM hN
  have f1 : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.mpr hM.fg
  have f2 : Module.Finite ℤ M := Module.Finite.trans (𝓞 K) M
  have f3 : AddGroup.FG M.toAddSubgroup := Module.Finite.iff_addGroup_fg.mp f2
  have : Finite (↥M.toAddSubgroup ⧸ (M ⊓ locF 𝔭 N).toAddSubgroup.addSubgroupOf M.toAddSubgroup) := by
    apply AddCommGroup.finite_of_fg_isAddTorsion
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H q =>
      rw [isOfFinAddOrder_iff_zsmul_eq_zero]
      refine ⟨n, hn, ?_⟩
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      exact Submodule.mem_inf.2 ⟨zsmul_mem q.2 n, LocF.le_locF 𝔭 N (hnx _ q.2)⟩
  exact AddSubgroup.index_ne_zero_of_finite
end Formalism.HermitianLattices.Ext.L3.LIOrb.IA
