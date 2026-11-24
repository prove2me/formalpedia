-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.HitsCapPos_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:01.580805+00:00
-- url     : https://prove2.me/submissions/06a051da-ad32-4998-9e95-8b50598506e6

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
section
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
private theorem exists_two_le_or_two_pos_of_one_lt_sum {κ : Type} (S : Finset κ) (β : κ →₀ ℕ)
    (h : 1 < ∑ k ∈ S, β k) :
    (∃ k ∈ S, 2 ≤ β k) ∨ ∃ k ∈ S, ∃ k' ∈ S, k ≠ k' ∧ 1 ≤ β k ∧ 1 ≤ β k' := by
  by_cases hA : ∃ k ∈ S, 2 ≤ β k
  · exact Or.inl hA
  right
  by_contra hB
  have hle : ∀ k ∈ S, β k ≤ 1 := fun k hk => by
    by_contra h'
    exact hA ⟨k, hk, by omega⟩
  have hcard : (S.filter (fun k => β k ≠ 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    by_contra hab
    exact hB ⟨a, ha.1, b, hb.1, hab, Nat.one_le_iff_ne_zero.mpr ha.2,
      Nat.one_le_iff_ne_zero.mpr hb.2⟩
  have hsum : ∑ k ∈ S, β k ≤ (S.filter (fun k => β k ≠ 0)).card := by
    calc ∑ k ∈ S, β k = ∑ k ∈ S.filter (fun k => β k ≠ 0), β k := by
          rw [Finset.sum_filter_ne_zero]
      _ ≤ ∑ k ∈ S.filter (fun k => β k ≠ 0), 1 :=
          Finset.sum_le_sum (fun k hk => hle k (Finset.mem_filter.mp hk).1)
      _ = (S.filter (fun k => β k ≠ 0)).card := by simp
  omega
section BiLe
variable {K ι κ : Type} [Field K]
end BiLe
section PosDeg
variable {K σ : Type} [Field K] [DecidableEq σ] {r0 r1 : ℕ}
end PosDeg
end Formalism.InvariantFactorPaths.G7
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (h1 : HasseDerivProdVanish) (h2 : MinorHits) : HitsCapPos := by
  intro K σ κ _ _ _ r0 r1 C l sf T I pos ξ col S s₀ hpos hξ β hβ
  refine h1 K (σ × Fin r0 × Fin r1) κ (fun k => colDir (pos k) (ξ k) (col k)) C
    (fun c => minorAt (sf c) (T c) (I c)) (fun c => if sf c = s₀ then 1 else 0) S ?hf β ?hsum
  case hf =>
    intro c β' hc
    try dsimp only at hc
    apply h2 K σ κ r0 r1 (l c) (sf c) (T c) (I c) pos ξ col β'
    by_cases hs : sf c = s₀
    · rw [if_pos hs] at hc
      rcases exists_two_le_or_two_pos_of_one_lt_sum S β' hc with ⟨k, _, h2k⟩ | ⟨k, hk, k', hk', hne, h1k, h1k'⟩
      · exact Or.inl ⟨k, h2k⟩
      · exact Or.inr (Or.inl ⟨k, k', hne, h1k, h1k', (hpos k hk).trans (hpos k' hk').symm,
          Or.inl (hξ k hk k' hk')⟩)
    · rw [if_neg hs] at hc
      obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc.ne'
      exact Or.inr (Or.inr ⟨k, Nat.one_le_iff_ne_zero.mpr hk0,
        Or.inl (fun h => hs (h.symm.trans (hpos k hk)))⟩)
  case hsum =>
    rw [Finset.card_filter] at hβ
    exact hβ
end Formalism.InvariantFactorPaths.G7
