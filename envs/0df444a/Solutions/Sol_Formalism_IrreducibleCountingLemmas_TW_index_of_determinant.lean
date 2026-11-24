-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.index_of_determinant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:44:12.517694+00:00
-- url     : https://prove2.me/submissions/0bb93cfa-8f22-4cb7-8de5-163244391242

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexDet
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_val_unique
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_exists_basis
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_isLat_inf
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_isLat_span_basis
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_ord_unit_mul_pow
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_relLen_span_of_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_sIdx_eq_sub


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
theorem _root_.solution : IndexDet := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ d b w ϖ u n hϖ hdet
  have hinj := IsFractionRing.injective O K
  have hπ : algebraMap O K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have hu : algebraMap O K (u : O) ≠ 0 := (map_ne_zero_iff _ hinj).2 u.ne_zero
  have hne : b.det w ≠ 0 := by
    rw [hdet]; exact mul_ne_zero hu (zpow_ne_zero _ hπ)
  have hb := (b.is_basis_iff_det).2 (isUnit_iff_ne_zero.2 hne)
  obtain ⟨wb, rfl⟩ : ∃ wb : Basis (Fin d) K V, ⇑wb = w :=
    ⟨Basis.mk hb.1 hb.2.ge, Basis.coe_mk _ _⟩
  have hB := Idx.isLat_span_basis (O := O) b
  have hW := Idx.isLat_span_basis (O := O) wb
  have hQ := Idx.isLat_inf hB hW
  obtain ⟨n', γ, hγ⟩ := Idx.exists_basis hQ
  have hn : n' = d := by
    have h1 := Module.finrank_eq_card_basis b
    have h2 := Module.finrank_eq_card_basis γ
    simpa using h2.symm.trans h1
  subst hn
  obtain ⟨D1, hD1, l1⟩ := Idx.relLen_span_of_le (O := O) b γ (hγ ▸ inf_le_left)
    (b.isUnit_det γ).ne_zero
  obtain ⟨D2, hD2, l2⟩ := Idx.relLen_span_of_le (O := O) wb γ (hγ ▸ inf_le_right)
    (wb.isUnit_det γ).ne_zero
  have hD1ne : D1 ≠ 0 := by
    rintro rfl; rw [map_zero] at hD1; exact (b.isUnit_det γ).ne_zero hD1.symm
  have hD2ne : D2 ≠ 0 := by
    rintro rfl; rw [map_zero] at hD2; exact (wb.isUnit_det γ).ne_zero hD2.symm
  rw [Idx.sIdx_eq_sub hB hW hQ inf_le_left inf_le_right, ← hγ, l1, l2]
  obtain ⟨k1, u1, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hD1ne hϖ
  obtain ⟨k2, u2, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hD2ne hϖ
  rw [Idx.ord_unit_mul_pow hϖ, Idx.ord_unit_mul_pow hϖ, ENat.toNat_natCast, ENat.toNat_natCast]
  have hmul := b.det_mul_det wb γ
  rw [← hD1, ← hD2, hdet] at hmul
  have key : (k1 : ℤ) = n + k2 := by
    apply Idx.val_unique (K := K) hϖ u1 (u * u2)
    rw [zpow_add₀ hπ, zpow_natCast, zpow_natCast, Units.val_mul, map_mul]
    rw [map_mul, map_mul, map_pow, map_pow] at hmul
    rw [← hmul]; ring
  omega
end Formalism.IrreducibleCountingLemmas.TW
