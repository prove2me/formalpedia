-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.low_pay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:45:53.939229+00:00
-- url     : https://prove2.me/submissions/3f4a6711-af22-4032-a09f-57d7d05cfeb3

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GrowthSums_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryATwoAndB
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_val_add_nat_mod_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
variable {ν r0 r1 E : ℕ}
namespace Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
theorem _root_.solution (hJ : HitsColumnsPos) {K : Type} [Field K] [NeZero ν] {C : ℕ} (p : ℕ)
    (ξ : ZMod (2 * ν) → Fin r0 → K) (β : KapI ν r1 E →₀ ℕ) (l : Fin C → ℕ)
    (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1)
    (h4 : hasseDir (bBof p ξ) β (lowOp l sf T I) ≠ 0) (J : Finset (Fin r1)) :
    ∑ k ∈ univ.filter (fun k : KapI ν r1 E => k.1.val % 2 = 0 ∧ k.2.2 ∈ J), β k ≤
      ∑ c, (if (sf c).val % 2 = 1 then ((univ.image (I c)) ∩ J).card else 0) := by
  classical
  set Od : Finset (ZMod (2 * ν)) := univ.filter (fun s => s.val % 2 = 1) with hOd
  set pos : KapI ν r1 E → ZMod (2 * ν) := fun k => k.1 + ((2 * k.2.1.val + 1 : ℕ) : ZMod (2 * ν))
    with hpos
  have hmaps : ∀ k ∈ univ.filter (fun k : KapI ν r1 E => k.1.val % 2 = 0 ∧ k.2.2 ∈ J), pos k ∈ Od := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [hOd, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [hpos]
    rw [val_add_nat_mod_two]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hR : ∑ c, (if (sf c).val % 2 = 1 then ((univ.image (I c)) ∩ J).card else 0) =
      ∑ y ∈ Od, ∑ c ∈ univ.filter (fun c => sf c = y), ((univ.image (I c)) ∩ J).card := by
    rw [← Finset.sum_filter]
    rw [← Finset.sum_fiberwise_of_maps_to (g := sf) (t := Od) (fun c hc => by
      rw [Finset.mem_filter] at hc
      rw [hOd, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hc.2⟩)]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [hOd, Finset.mem_filter] at hy
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by rw [h]; exact hy.2, h⟩
  rw [hR]
  refine Finset.sum_le_sum (fun y _ => ?_)
  by_contra hlt
  push_neg at hlt
  apply h4
  exact hJ K (ZMod (2 * ν)) (KapI ν r1 E) r0 r1 C l sf T I pos
    (fun k a => ξ k.1 a ^ (p ^ (2 * k.2.1.val + 1))) (fun k => k.2.2)
    ((univ.filter (fun k : KapI ν r1 E => k.1.val % 2 = 0 ∧ k.2.2 ∈ J)).filter (fun k => pos k = y)) y J
    (fun k hk => (Finset.mem_filter.1 hk).2)
    (fun k hk => ((Finset.mem_filter.1 (Finset.mem_filter.1 hk).1).2).2) β hlt
end Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
