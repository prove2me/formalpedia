-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvU.map_fixedProj_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:38.580729+00:00
-- url     : https://prove2.me/submissions/dd86e6a9-ef50-42a0-8691-9aa3fc1a2dd5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_ReciprocityTheory_BurnsideSurjectivity_Burnside
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvUnifA
import Theorems.Thm_DiscreteGroups_sglob_LConvU_fixedProj_eq_avg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open DiscreteGroups DiscreteGroups.sglob DiscreteGroups.sglob.LConvU
open GroundTheory.Automorphic Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (hρ : IsSmooth ρ) {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo
namespace DiscreteGroups.sglob.LConvU
theorem _root_.solution {U : Type*} [AddCommGroup U] [Module ℂ U] (f : V →ₗ[ℂ] U)
    (v : V) (hf : ∀ k ∈ K, f (ρ k v) = f v) : f (fixedProj ρ hρ hKc hKo v : V) = f v := by
  have hLo : IsOpen ((K ⊓ stabilizerOf ρ v : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKo.inter (hρ v)
  obtain ⟨N, r, hN, hr, h⟩ := fixedProj_eq_avg hρ hKc hKo (L := K ⊓ stabilizerOf ρ v) inf_le_left hLo
  rw [h v (fun l hl => hl.2), map_smul, map_sum, Finset.sum_congr rfl (fun i _ => hf (r i) (hr i)),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast hN.ne'), one_smul]
end DiscreteGroups.sglob.LConvU
