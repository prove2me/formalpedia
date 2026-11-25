-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.coe_filter_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:31:43.394001+00:00
-- url     : https://prove2.me/submissions/ff9af9ca-4ccb-4c1b-9d36-b30c59d0fca0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumBoxIdeal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlphaNOfVdZeroUnit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LValEtaEqLValEtaF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoWeightedTprod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ALocEqRoL
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSingSSum
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_boxSet_finite
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_mem_bId_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_ne_zero_of_mem_boxSet
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_ne_zero_of_mem_boxSet
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
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.A5
open scoped Classical
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ)
    (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) :
    {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ bId v} =
      ↑((boxSet_finite hK hF T).toFinset.filter fun n => v ≤ valF n) := by
  ext n
  simp only [Set.mem_setOf_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨hb, hI⟩
    exact ⟨hb, (mem_bId_iff (ne_zero_of_mem_boxSet hb) v).mp hI⟩
  · rintro ⟨hb, hv⟩
    exact ⟨hb, (mem_bId_iff (ne_zero_of_mem_boxSet hb) v).mpr hv⟩
end Formalism.HermitianLattices.Ext.L3.A5
