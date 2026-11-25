-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.order_unit_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:54:12.759038+00:00
-- url     : https://prove2.me/submissions/4e19d684-4e2b-42af-8a6e-b6e63c4c7b4c

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderChainWeights
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrderChainWeights_mem_ROrd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset MeasureTheory
open Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.OrderChainWeights
open scoped ENNReal
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.ROrderUnits := by
  intro o _ _
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun k => ?_⟩
  · have h1 : IsUnit ((x : o × o).1) := (hx.map (ROrd o).subtype).map (RingHom.fst o o)
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr h1
  · have hm := (mem_ROrd (x : o × o)).mp x.2
    obtain ⟨a, ha⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hx
    obtain ⟨b, hb⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (hm ▸ hx)
    have hinv : ((↑a⁻¹ : o), (↑b⁻¹ : o)) ∈ ROrd o := by
      rw [mem_ROrd]
      simp only [map_units_inv, ha, hb, hm]
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · show (x : o × o).1 * ↑a⁻¹ = 1
      rw [← ha]
      exact a.mul_inv
    · show (x : o × o).2 * ↑b⁻¹ = 1
      rw [← hb]
      exact b.mul_inv
  · obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective k
    exact ⟨⟨(a, a), (mem_ROrd _).mpr rfl⟩, ha⟩
end Formalism.FourierDecayAlt.P
