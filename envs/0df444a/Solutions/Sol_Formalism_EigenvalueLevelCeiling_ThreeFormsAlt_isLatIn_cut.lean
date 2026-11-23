-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.isLatIn_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:45.26063+00:00
-- url     : https://prove2.me/submissions/90f1343c-0332-43b7-a6c2-2b53dd2d8547

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_locS_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
open Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
namespace Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
theorem _root_.solution (W : Submodule K Z) (B : Submodule (𝓞 K) Z) (hB : IsLatIn ⊤ B) :
    IsLatIn W (cut W B) := by
  constructor
  · have : IsNoetherian (𝓞 K) B := isNoetherian_of_fg_of_noetherian B hB.1
    exact isNoetherian_submodule.mp this _ inf_le_left
  · apply le_antisymm
    · exact Submodule.span_le.mpr (fun x hx => hx.2)
    · intro x hx
      have htop := indexBasic_locS_top (K := K) B hB.2
      have hx' : x ∈ locS (nonZeroDivisors (𝓞 K)) B := by rw [htop]; exact Submodule.mem_top
      obtain ⟨d, hd, hdx⟩ := hx'
      have hd0 : algebraMap (𝓞 K) K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
      have hmem : d • x ∈ cut W B := by
        refine ⟨hdx, ?_⟩
        change d • x ∈ W
        rw [← algebraMap_smul K d x]
        exact W.smul_mem _ hx
      have := Submodule.smul_mem (Submodule.span K ((cut W B : Submodule (𝓞 K) Z) : Set Z))
        (algebraMap (𝓞 K) K d)⁻¹ (Submodule.subset_span hmem)
      rwa [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd0, one_smul] at this
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
