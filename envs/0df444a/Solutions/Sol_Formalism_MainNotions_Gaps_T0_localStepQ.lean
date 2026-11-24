-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.localStepQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:21:44.652975+00:00
-- url     : https://prove2.me/submissions/5a710643-2a82-44f7-9087-ddd3e595b58d

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepClosed
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepDescent
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LengthLeOfSemilinear
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_ql_scaled_le
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
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
open Module Formalism.LatticeBaseChangeAlt Formalism.LatticeBaseChangeAlt.BQuot
namespace Formalism.MainNotions.Gaps.T0
theorem _root_.solution : LocalStepQ := by
  intro O K V W _ _ _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ M Θ N₁ Z Zm N' Mgg e n q th AA AA' N₁'
    ρ hMl hΘl hNΘ _ hthΘ hgg hggK hq hXN hN₁ hZ hZm hρ hkρ himg _ _ hf1 hf2 hf3 V'
  set X : Submodule O V := M.map ((ϖ ^ e) • (LinearMap.id : V →ₗ[O] V)) with hX
  set NK : Submodule O V :=
    (Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V)).restrictScalars O with hNK
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
  let Tj : Submodule O V := Submodule.span O (Set.range fun j => ϖ ^ e • th j)
  have hTΘ : Tj ≤ Θ := Submodule.span_le.2 (by
    rintro _ ⟨j, rfl⟩
    exact Θ.smul_mem _ (hthΘ j))
  have hggNK : Mgg ≤ NK := fun x hx => hggK (Submodule.subset_span hx)
  have r1 := reduction X Θ (N₁ ⊔ Z) Tj NK hNΘ hTΘ
  have r2 := levels N' ((X ⊓ NK) ⊔ (N₁ ⊔ Z)) N₁ Z Zm AA AA' N₁' ρ
    (sup_le hXN (sup_le hN₁ (hZ.trans hZm))) hρ hkρ himg
  have r3 : ql X ((X ⊓ NK) ⊔ Tj) ≤ (q : ℕ∞) := (ql_scaled_le (ϖ ^ e) M Mgg NK th hgg hggNK).trans hq
  set L1 := Module.length O (↥AA' ⧸ AA.comap AA'.subtype)
  set L2 := Module.length O (↥AA ⧸ N₁'.comap AA.subtype)
  set L3 := Module.length O (↥Zm ⧸ Z.comap Zm.subtype)
  set L := Formalism.LatticeIndexTer.qlen O V (X ⊔ Θ) Θ with hL
  have hLA' : L ≤ L1 + L2 + L3 + ((q : ℕ) : ℕ∞) := r1.trans (add_le_add r2 r3)
  have hsum : L1 + L2 + L3 + ((q : ℕ) : ℕ∞) =
      ((L1.toNat + L2.toNat + L3.toNat + q : ℕ) : ℕ∞) := by
    rw [← ENat.natCast_toNat hf1, ← ENat.natCast_toNat hf2, ← ENat.natCast_toNat hf3]
    simp only [ENat.toNat_natCast]
    push_cast; rfl
  rw [hsum] at hLA'
  have hLt : L.toNat ≤ L1.toNat + L2.toNat + L3.toNat + q := by
    have hLne : L ≠ ⊤ := ne_top_of_le_ne_top (by simp) hLA'
    rw [← ENat.natCast_toNat hLne] at hLA'
    exact_mod_cast hLA'
  have h5 : ((L.toNat : ℕ) : ℤ) ≤ (L1.toNat : ℤ) + (L2.toNat : ℤ) + (L3.toNat : ℤ) + (q : ℤ) := by
    exact_mod_cast hLt
  linarith
end Formalism.MainNotions.Gaps.T0
