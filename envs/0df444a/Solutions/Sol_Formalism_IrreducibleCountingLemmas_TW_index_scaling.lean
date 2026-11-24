-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.index_scaling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:05:23.33864+00:00
-- url     : https://prove2.me/submissions/08735fb6-4328-458b-834a-b0d10a0ef468

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexDet
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexScale
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_exists_basis
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_isLat_span_basis
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_index_additive
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_index_of_determinant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
namespace Formalism.IrreducibleCountingLemmas.TW
theorem _root_.solution : IndexScale := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ M N ϖ u n hM hN hϖ
  have hinj := IsFractionRing.injective O K
  have hc : algebraMap O K ((u : O) * ϖ ^ n) ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 (mul_ne_zero u.ne_zero (pow_ne_zero _ hϖ.ne_zero))
  obtain ⟨d, β, rfl⟩ := Idx.exists_basis hN
  have hd : Module.finrank K V = d := by
    simpa using Module.finrank_eq_card_basis β
  let wb : Basis (Fin d) K V :=
    β.isUnitSMul (w := fun _ => algebraMap O K ((u : O) * ϖ ^ n)) (fun _ => isUnit_iff_ne_zero.2 hc)
  have hspan : scaleLat ((u : O) * ϖ ^ n) (Submodule.span O (Set.range β))
      = Submodule.span O (Set.range wb) := by
    unfold scaleLat
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    ext i
    simp only [Function.comp_apply, LinearMap.lsmul_apply, wb, Basis.isUnitSMul_apply,
      algebraMap_smul]
  have hdet : β.det wb = algebraMap O K ((u ^ d : Oˣ) : O)
      * (algebraMap O K ϖ) ^ ((d : ℤ) * (n : ℤ)) := by
    rw [Basis.det_isUnitSMul, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_mul,
      mul_pow, Units.val_pow_eq_pow_val, map_pow, map_pow, ← pow_mul, mul_comm n d]
    norm_cast
  have h1 := index_of_determinant O K V d β wb ϖ (u ^ d) ((d : ℤ) * (n : ℤ)) hϖ hdet
  have h2 := (index_additive O K V M _ _ hM hN (Idx.isLat_span_basis (O := O) wb)).2
  rw [hspan, hd, ← h2, h1]
end Formalism.IrreducibleCountingLemmas.TW
