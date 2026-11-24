-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.localStepExt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:21:43.776303+00:00
-- url     : https://prove2.me/submissions/51e0ac6c-5781-4725-8399-d1ec4b47310e

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LevelsChain
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepExtOf
import Theorems.Thm_Formalism_IncomingBounds_index_last_reduction_holds
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_levels
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_reduction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.LatticeBaseChangeAlt
open BQuot
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution (hQ : QuotientLengthExt) : LocalStepExt := by
  intro O K K₁ V W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ M Θ N₁ Z Zm N' e be n th c AA AA' N₁'
    ρ a a' X NK hMl hΘl hNΘ hthM hthΘ hker hspan hcM ha ha' hdet hXN hN₁ hZ hZm hρ hkρ himg hN₁'
    hAA hf1 hf2 hf3 V'
  have hp0 : algebraMap O K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero
  have hp1 : algebraMap O K₁ ϖ ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply O K K₁]
    exact (map_ne_zero_iff _ (algebraMap K K₁).injective).2 hp0
  have hsm : ∀ v : V, (algebraMap O K ϖ) ^ e • v = ϖ ^ e • v := by
    intro v
    rw [← map_pow, algebraMap_smul]
  have hIdx := Formalism.IncomingBounds.index_last_reduction_holds O K V ϖ hϖ (e : ℤ) M Θ hMl hΘl V'
  have hbridge : M.map ((((algebraMap O K ϖ) ^ (e : ℤ)) • LinearMap.id : V →ₗ[K] V).restrictScalars O)
      = X := by
    ext x
    simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq, zpow_natCast, X, LinearMap.smul_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, (hsm y).symm⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, hsm y⟩
  rw [hbridge] at hIdx
  let Tj : Submodule O V := Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)
  have hTΘ : Tj ≤ Θ := Submodule.span_le.2 (by
    rintro _ ⟨j, rfl⟩
    show (algebraMap O K ϖ) ^ e • th j ∈ Θ
    rw [hsm]
    exact Θ.smul_mem _ (hthΘ j))
  have hthX : ∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X := by
    intro j
    rw [hsm]
    exact ⟨th j, hthM j, rfl⟩
  have hcX : ∀ x ∈ X, ∀ i, ∃ y ∈ integralClosure O K₁,
      c x i = (algebraMap O K₁ ϖ) ^ ((e : ℤ) - (be : ℤ)) * y := by
    rintro _ ⟨y, hy, rfl⟩ i
    obtain ⟨u, hu, hcu⟩ := hcM y hy i
    refine ⟨u, hu, ?_⟩
    show c (ϖ ^ e • y) i = _
    rw [← hsm, map_smul, Pi.smul_apply, hcu, Algebra.smul_def, map_pow,
      ← IsScalarTower.algebraMap_apply, ← mul_assoc, sub_eq_add_neg, zpow_add₀ hp1, zpow_natCast]
  obtain ⟨m, hm, hmle⟩ := hQ O K K₁ V ϖ hϖ n c _ hker th hspan X e be hcX hthX a a' ha ha' hdet
  have r1 := reduction X Θ (N₁ ⊔ Z) Tj NK hNΘ hTΘ
  have r2 := levels N' ((X ⊓ NK) ⊔ (N₁ ⊔ Z)) N₁ Z Zm AA AA' N₁' ρ
    (sup_le hXN (sup_le hN₁ (hZ.trans hZm))) hρ hkρ himg
  have r3 : ql X ((X ⊓ NK) ⊔ Tj) = m := hm
  set L1 := Module.length O (↥AA' ⧸ AA.comap AA'.subtype)
  set L2 := Module.length O (↥AA ⧸ N₁'.comap AA.subtype)
  set L3 := Module.length O (↥Zm ⧸ Z.comap Zm.subtype)
  set L := Formalism.LatticeIndexTer.qlen O V (X ⊔ Θ) Θ with hL
  have hLA' : L ≤ L1 + L2 + L3 + ((m : ℕ) : ℕ∞) := by
    rw [← r3]; exact r1.trans (add_le_add r2 le_rfl)
  have hsum : L1 + L2 + L3 + ((m : ℕ) : ℕ∞) =
      ((L1.toNat + L2.toNat + L3.toNat + m : ℕ) : ℕ∞) := by
    rw [← ENat.natCast_toNat hf1, ← ENat.natCast_toNat hf2, ← ENat.natCast_toNat hf3]
    simp only [ENat.toNat_natCast]
    push_cast; rfl
  rw [hsum] at hLA'
  have hLt : L.toNat ≤ L1.toNat + L2.toNat + L3.toNat + m := by
    have hLne : L ≠ ⊤ := ne_top_of_le_ne_top (by simp) hLA'
    rw [← ENat.natCast_toNat hLne] at hLA'
    exact_mod_cast hLA'
  have h5 : ((L.toNat : ℕ) : ℤ) ≤ (L1.toNat : ℤ) + (L2.toNat : ℤ) + (L3.toNat : ℤ) + (m : ℤ) := by
    exact_mod_cast hLt
  have hd : (0 : ℤ) ≤ (finrank K K₁ : ℤ) := Int.natCast_nonneg _
  have h6 := mul_le_mul_of_nonneg_left (hIdx.trans (add_le_add le_rfl h5)) hd
  linarith
end Formalism.LatticeBaseChangeAlt
