-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexValuation.isLat_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:35:26.236273+00:00
-- url     : https://prove2.me/submissions/93902f5a-f63a-469c-941a-0bbd3c9d2994

import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndex
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexLength_exists_smul_mem_of_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open scoped Pointwise
open Formalism Formalism.LatticeIndexTer Formalism.LatticeIndexTer.LatticeIndexValuation
variable {O K X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X]
  [IsScalarTower O K X]
namespace Formalism.LatticeIndexTer.LatticeIndexValuation
theorem _root_.solution (A : Submodule O X) (hA : IsLat O K X A) (W : Submodule K X) :
    IsLat O K W (A.comap ((W.subtype).restrictScalars O)) := by
  let ι : W →ₗ[O] X := (W.subtype).restrictScalars O
  have hι : Function.Injective ι := Subtype.val_injective
  constructor
  · have : Module.Finite O A := Module.Finite.iff_fg.mpr hA.1
    have hle : (A.comap ι).map ι ≤ A := Submodule.map_comap_le ι A
    have : IsNoetherian O ((A.comap ι).map ι) := isNoetherian_of_le hle
    have hfg : ((A.comap ι).map ι).FG := Module.Finite.iff_fg.mp inferInstance
    exact Submodule.fg_of_fg_map_injective ι hι hfg
  · rw [eq_top_iff]
    rintro w -
    obtain ⟨d, hd, hdw⟩ := LatticeIndexLength.exists_smul_mem_of_span (K := K) A hA.2 (w : X)
    have hdK : algebraMap O K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hd
    have hmem : d • w ∈ Submodule.span K (A.comap ι : Set W) := by
      apply Submodule.subset_span
      show ((d • w : W) : X) ∈ A
      rw [Submodule.coe_smul_of_tower]
      exact hdw
    have hw : w = (algebraMap O K d)⁻¹ • (d • w) := by
      rw [← algebraMap_smul K d w, smul_smul, inv_mul_cancel₀ hdK, one_smul]
    rw [hw]
    exact Submodule.smul_mem _ _ hmem
end Formalism.LatticeIndexTer.LatticeIndexValuation
