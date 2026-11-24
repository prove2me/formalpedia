-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.HitsColumnsPos_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:01.411206+00:00
-- url     : https://prove2.me/submissions/427e26cf-aeb8-4455-816a-75d6a45026d3

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree

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
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (h1 : HasseDerivProdVanish) (h2 : MinorHits) : HitsColumnsPos := by
  intro K σ κ _ _ _ r0 r1 C l sf T I pos ξ col S s₀ J hpos hJ β hβ
  refine h1 K (σ × Fin r0 × Fin r1) κ (fun k => colDir (pos k) (ξ k) (col k)) C
    (fun c => minorAt (sf c) (T c) (I c))
    (fun c => if sf c = s₀ then ((univ.image (I c)) ∩ J).card else 0) S ?hf β ?hsum
  case hf =>
    intro c β' hc
    try dsimp only at hc
    apply h2 K σ κ r0 r1 (l c) (sf c) (T c) (I c) pos ξ col β'
    by_cases hs : sf c = s₀
    · rw [if_pos hs] at hc
      by_contra hno
      apply absurd hc
      rw [not_lt]
      have hle : ∀ k ∈ S, β' k ≤ 1 := fun k _ => by
        by_contra h'
        exact hno (Or.inl ⟨k, by omega⟩)
      have hinj : ∀ k ∈ S.filter (fun k => β' k ≠ 0), ∀ k' ∈ S.filter (fun k => β' k ≠ 0),
          col k = col k' → k = k' := by
        intro k hk k' hk' hcol
        rw [Finset.mem_filter] at hk hk'
        by_contra hne
        exact hno (Or.inr (Or.inl ⟨k, k', hne, Nat.one_le_iff_ne_zero.mpr hk.2,
          Nat.one_le_iff_ne_zero.mpr hk'.2, (hpos k hk.1).trans (hpos k' hk'.1).symm, Or.inr hcol⟩))
      have hmaps : ∀ k ∈ S.filter (fun k => β' k ≠ 0), col k ∈ (univ.image (I c)) ∩ J := by
        intro k hk
        rw [Finset.mem_filter] at hk
        rw [Finset.mem_inter]
        refine ⟨?_, hJ k hk.1⟩
        by_contra hnot
        exact hno (Or.inr (Or.inr ⟨k, Nat.one_le_iff_ne_zero.mpr hk.2, Or.inr (fun hr => by
          obtain ⟨i, hi⟩ := Set.mem_range.mp hr
          exact hnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩))⟩))
      calc ∑ k ∈ S, β' k = ∑ k ∈ S.filter (fun k => β' k ≠ 0), β' k := by
            rw [Finset.sum_filter_ne_zero]
        _ ≤ ∑ k ∈ S.filter (fun k => β' k ≠ 0), 1 :=
            Finset.sum_le_sum (fun k hk => hle k (Finset.mem_filter.mp hk).1)
        _ = (S.filter (fun k => β' k ≠ 0)).card := by simp
        _ ≤ ((univ.image (I c)) ∩ J).card :=
            Finset.card_le_card_of_injOn col
              (fun k hk => Finset.mem_coe.mpr (hmaps k (Finset.mem_coe.mp hk)))
              (fun k hk k' hk' h => hinj k (Finset.mem_coe.mp hk) k' (Finset.mem_coe.mp hk') h)
    · rw [if_neg hs] at hc
      obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc.ne'
      exact Or.inr (Or.inr ⟨k, Nat.one_le_iff_ne_zero.mpr hk0,
        Or.inl (fun h => hs (h.symm.trans (hpos k hk)))⟩)
  case hsum =>
    rw [Finset.sum_filter] at hβ
    exact hβ
end Formalism.InvariantFactorPaths.G7
