-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.zero_count_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:06:22.833604+00:00
-- url     : https://prove2.me/submissions/1a8069a4-bd2e-4a56-87e9-1c4cf949d2ac

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : ZCountRange := by
  intro K M N _ _ _ _ _ _ _ I Zg _ _ Ms Nx e θ hI hT hN hb
  classical
  have hmap : ∀ x, (Ms (e x)).map θ = Nx x := by
    intro x
    apply SetLike.coe_injective
    rw [Submodule.map_coe]
    exact (hb x).image_eq
  have hrange : LinearMap.range θ = ⨆ x, Nx x := by
    rw [LinearMap.range_eq_map, ← hT, Submodule.map_iSup,
      ← e.iSup_comp (g := fun s => (Ms s).map θ)]
    simp_rw [hmap]
  have hfr : ∀ x, Module.finrank K (Nx x) = Module.finrank K (Ms (e x)) := by
    intro x
    let φ : Ms (e x) →ₗ[K] Nx x := θ.restrict (fun m hm => (hb x).mapsTo hm)
    have hφ : Function.Bijective φ :=
      ⟨fun a b h => Subtype.ext ((hb x).injOn a.2 b.2 (congrArg Subtype.val h)), fun y => by
        obtain ⟨m, hm, h⟩ := (hb x).surjOn y.2
        exact ⟨⟨m, hm⟩, Subtype.ext h⟩⟩
    exact (LinearEquiv.ofBijective φ hφ).finrank_eq.symm
  have hsumM : ∑ x, Module.finrank K (Nx x) = Module.finrank K M := by
    simp_rw [hfr]
    rw [Equiv.sum_comp e (fun s => Module.finrank K (Ms s))]
    have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hI hT
    rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap Ms) hint).finrank_eq,
      Module.finrank_directSum]
  have hsumR : Module.finrank K (LinearMap.range θ) = ∑ x, Module.finrank K (Nx x) := by
    have hinjΨ : Function.Injective (DirectSum.coeLinearMap Nx) := hN.dfinsupp_lsum_injective
    rw [hrange, ← DirectSum.range_coeLinearMap, LinearMap.finrank_range_of_inj hinjΨ,
      Module.finrank_directSum]
  have hinj : Function.Injective θ := by
    rw [← LinearMap.ker_eq_bot]
    have h := LinearMap.finrank_range_add_finrank_ker θ
    rw [hsumR, hsumM] at h
    exact Submodule.finrank_eq_zero.1 (by omega)
  exact ⟨hinj, hrange, hsumR, hsumR.trans hsumM⟩
end Formalism.IrreducibleCountingLemmas.Z
