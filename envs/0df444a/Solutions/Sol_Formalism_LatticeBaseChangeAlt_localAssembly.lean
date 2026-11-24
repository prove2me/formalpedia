-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.localAssembly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:01.377207+00:00
-- url     : https://prove2.me/submissions/c6964520-513e-4999-876e-a52b2ab3d820

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_reduction
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_levels
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_quotientLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open BQuot
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : LocalAssembly := by
  intro O K V W _ _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ M Θ N₁ Z Zm N' e be n th c AA AA' N₁' ρ a a'
  dsimp only
  intro hN1Z hthM hthΘ hkc hMint ha ha' hdet hXNK hN1N' hZZm hZmN' hρ hkerρ himg hN1'AA hAA
  set X : Submodule O V := M.map ((ϖ ^ e) • (LinearMap.id : V →ₗ[O] V)) with hXdef
  set NK : Submodule O V :=
    (Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V)).restrictScalars O with hNKdef
  set Tj : Submodule O V :=
    Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j) with hTjdef
  have hϖ0 : algebraMap O K ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    exact hϖ.ne_zero
  have hTΘ : Tj ≤ Θ := by
    rw [hTjdef, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show (algebraMap O K ϖ) ^ e • th j ∈ Θ
    rw [← map_pow, algebraMap_smul]
    exact Θ.smul_mem _ (hthΘ j)
  have hX' : ∀ x ∈ X, ∀ i, ∃ u : O,
      c x i = (algebraMap O K ϖ) ^ ((e : ℤ) - (be : ℤ)) * algebraMap O K u := by
    intro x hx i
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨u, hu⟩ := hMint m hm i
    refine ⟨u, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, ← algebraMap_smul K (ϖ ^ e) m, map_smul,
      Pi.smul_apply, smul_eq_mul, hu, map_pow, sub_eq_add_neg, zpow_add₀ hϖ0, zpow_natCast]
    ring
  have hth' : ∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X := by
    intro j
    rw [← map_pow, algebraMap_smul]
    exact Submodule.mem_map.2 ⟨th j, hthM j, by simp⟩
  obtain ⟨m, hm, hmΔ⟩ := quotientLength O K V ϖ hϖ n c
    (Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V)) hkc X e be th hX' hth' a a' ha ha' hdet
  have hql : ql X ((X ⊓ NK) ⊔ Tj) = m := hm
  have hlev := levels N' ((X ⊓ NK) ⊔ (N₁ ⊔ Z)) N₁ Z Zm AA AA' N₁' ρ
    (sup_le hXNK (sup_le hN1N' (hZZm.trans hZmN'))) hρ hkerρ himg
  have hred := reduction X Θ (N₁ ⊔ Z) Tj NK hN1Z hTΘ
  have hmle : (m : ℕ∞) ≤ ((((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
      ((IsDiscreteValuationRing.addVal O a').toNat : ℤ) + (n : ℤ) * (be : ℤ)).toNat : ℕ) := by
    have h1 := hmΔ.trans (Int.self_le_toNat _)
    have h2 : m ≤ (((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
      ((IsDiscreteValuationRing.addVal O a').toNat : ℤ) + (n : ℤ) * (be : ℤ)).toNat := by
      exact_mod_cast h1
    exact_mod_cast h2
  calc ql (X ⊔ Θ) Θ ≤ ql ((X ⊓ NK) ⊔ (N₁ ⊔ Z)) (N₁ ⊔ Z) + ql X ((X ⊓ NK) ⊔ Tj) := hred
    _ ≤ (ql AA' AA + ql AA N₁' + ql Zm Z) + (m : ℕ∞) := by
      rw [hql]
      gcongr
    _ ≤ _ := by gcongr
end Formalism.LatticeBaseChangeAlt
