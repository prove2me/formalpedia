-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.domination_limit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:05.685827+00:00
-- url     : https://prove2.me/submissions/748d3d47-b87a-4425-ad1d-16ae752fc47f

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointSetConstantMembership
import Theorems.Thm_Formalism_FourierDecayAlt_P_PointSetConstantMembership_isPt_PT
import Theorems.Thm_Formalism_FourierDecayAlt_P_PointSetConstantMembership_mem_PT_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_PointSetConstantMembership_bound_PT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TA.TopDominationLimit := by
  intro E _ _ H _ _ _ n Kn V ρ c B hB hA4 hS R
  classical
  have hsum : ∀ x, Summable (fun p : {p : Pt E // IsPt n p} => c x p.1 • V p.1) := by
    intro x
    refine Summable.of_norm ?_
    simpa [norm_smul] using hS x
  have hlim : Tendsto (fun F : Finset {p : Pt E // IsPt n p} =>
      ∑ x ∈ R, ‖∑ p ∈ F, c x p.1 • V p.1‖ ^ 2) atTop
      (𝓝 (∑ x ∈ R, ‖∑' p : {p : Pt E // IsPt n p}, c x p.1 • V p.1‖ ^ 2)) := by
    refine tendsto_finsetSum _ fun x _ => ?_
    exact ((hsum x).hasSum.norm).pow 2
  refine le_of_tendsto_of_frequently hlim ?_
  rw [Filter.frequently_atTop]
  intro F
  set T : Finset E := F.biUnion fun p => (p.1.map Prod.snd).toFinset with hT
  have hNZ : NZSg (fun _ _ : ℕ => T) := by
    intro i s t ht
    simp only [hT, mem_biUnion, List.mem_toFinset, List.mem_map] at ht
    obtain ⟨p, _, b, hb, rfl⟩ := ht
    exact (p.2.2 b hb).2
  have hPt := PointSetConstantMembership.isPt_PT (fun _ _ => T) hNZ n
  refine ⟨(PT (fun _ _ => T) n).subtype (IsPt n), ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_subtype]
    refine PointSetConstantMembership.mem_PT_const T p.1 n p.2 fun b hb => ?_
    simp only [hT, mem_biUnion, List.mem_toFinset, List.mem_map]
    exact ⟨p, hp, b, hb, rfl⟩
  · have e : ∀ x, ∑ p ∈ (PT (fun _ _ => T) n).subtype (IsPt n), c x p.1 • V p.1
        = ∑ p ∈ PT (fun _ _ => T) n, c x p • V p := by
      intro x
      exact Finset.sum_subtype_of_mem (fun p => c x p • V p) hPt
    simp_rw [e]
    exact (PointSetConstantMembership.bound_PT Kn V c _ R (hA4 _ R hPt)).trans (hB _ hNZ)
end Formalism.FourierDecayAlt.P
