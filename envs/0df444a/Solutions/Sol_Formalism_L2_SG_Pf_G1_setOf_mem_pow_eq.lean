-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G1.setOf_mem_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:59.621861+00:00
-- url     : https://prove2.me/submissions/86b29542-1ed3-4217-bfca-036a4b8b7c41

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AlmostEverywhereSpherical
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G1
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {F : Type} [Field F] [NumberField F] {𝔭 : Ideal (𝓞 F)}
namespace Formalism.L2.SG.Pf.G1
theorem _root_.solution (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) :
    {e : ℕ | n ∈ 𝔭 ^ e} = Set.Iic (multiplicity 𝔭 (Ideal.span {n})) := by
  have hfin : FiniteMultiplicity 𝔭 (Ideal.span {n}) :=
    FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact h𝔭.ne_top)
      (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hn)
  ext e
  simp only [Set.mem_setOf_eq, Set.mem_Iic]
  rw [← hfin.pow_dvd_iff_le_multiplicity, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
end Formalism.L2.SG.Pf.G1
