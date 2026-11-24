-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.charpoly_eq_restrict_mul_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:01:32.111803+00:00
-- url     : https://prove2.me/submissions/2546d22f-1cae-4dea-ab50-a76125838faf

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_charpoly_smul_id
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_natAdd
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_natAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_natAdd
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Polynomial Filter Topology
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A B : Submodule K V) (γ₀ : Module.End K V) (c : K) (hAB : IsCompl A B)
    (hA0 : ∀ v ∈ A, γ₀ v ∈ A) (hB0 : ∀ v ∈ B, γ₀ v = c • v) :
    γ₀.charpoly = (γ₀.restrict hA0).charpoly * (X - C c) ^ Module.finrank K B := by
  have hconj : (Submodule.prodEquivOfIsCompl A B hAB).conj
      ((γ₀.restrict hA0).prodMap (c • (LinearMap.id : B →ₗ[K] B))) = γ₀ := by
    apply LinearMap.ext
    intro v
    obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl A B hAB).surjective v
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    simp [Submodule.coe_prodEquivOfIsCompl', hB0 b b.2]
  rw [← charpoly_smul_id, ← LinearMap.charpoly_prodMap, ← LinearEquiv.charpoly_conj
    (Submodule.prodEquivOfIsCompl A B hAB), hconj]
end Formalism.IrreducibleCountingLemmas.Z
