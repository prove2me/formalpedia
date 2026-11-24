-- Prove2me | solution 1 for Formalism.G0.many_orbits_refined_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:51.025615+00:00
-- url     : https://prove2.me/submissions/46fb7d5e-034b-4eab-8116-bb4a41258a94

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbitsRefined
import Theorems.Thm_Formalism_G0_CyclicSpanLengthLemmas_lengthPart2
import Theorems.Thm_Formalism_G0_ManyOrbitsP_allBut_mono
import Theorems.Thm_Formalism_G0_ManyOrbitsP_esymmR_le


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
open Formalism Formalism.G0
namespace Formalism.G0
theorem _root_.solution (hW : WalkSharp) : ManyOrbitsRefined := by
  intro R X _ _ _ _ _ V π hπ L y m c₀ S d a b c Sv κ G _ _ hd hm hcomm hbb hdb ha hb hc hy hG hκ
    habc hSv hsum
  have hGw : ∀ β : ℕ, ∀ B : Finset (Fin V), B.card = β + 1 →
      (↑(G B) : Set X) ⊆ L (vertexLabel B) ∧ (G B).card ≤ (fun B => (G B).card) B ∧
      ∀ x ∈ L (vertexLabel B), π ^ c₀ • x ∈
        (⨆ v ∈ B, (L (Function.update (vertexLabel B) v Slot.ball)).map (y v)) ⊔
          Submodule.span R (↑(G B) : Set X) := by
    intro β B hB
    have h := hG B (by omega)
    exact ⟨h.1, le_rfl, h.2.2⟩
  have hexp : ∑ v, (a v + b v + (m - 1) * c v + m * c₀) ≤ ∑ v, m * (c v + c₀) := by
    apply Finset.sum_le_sum
    intro v _
    have e : m * (c v + c₀) = c v + (m - 1) * c v + m * c₀ := by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      ring
    rw [e]
    exact Nat.add_le_add_right (Nat.add_le_add_right (habc v) _) _
  have hβ : ∀ β : ℕ, ∃ C : Finset X, (↑C : Set X) ⊆ L (fun _ => Slot.base) ∧
      (C.card : ℝ) ≤ d * (m : ℝ) ^ (β + 1) * esymmR κ (β + 1) ∧
      ∀ x ∈ L (fun _ => Slot.base), π ^ (∑ v, m * (c v + c₀) + β * S) • x ∈
        prodIdealMap π y m Sv (L fun _ => Slot.base) ⊔ Submodule.span R (↑C : Set X) := by
    intro β
    obtain ⟨h1, -⟩ := hW V π L y m β c₀ S a b c Sv (fun B => (G B).card) G hm hcomm hbb hdb ha
      hb hc hy (hGw β) hSv
    obtain ⟨C, hCM, hCcard, hCx⟩ := h1
    refine ⟨C, hCM, ?_, ?_⟩
    · have hC' : C.card ≤ ∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
          m ^ (β + 1) * (G B).card := hCcard
      have hcardG : ∀ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
          ((G B).card : ℝ) ≤ (∏ v ∈ B, κ v) * d := by
        intro B hB
        exact (hG B (by rw [(Finset.mem_powersetCard.mp hB).2]; omega)).2.1
      calc (C.card : ℝ)
          ≤ ((∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
              m ^ (β + 1) * (G B).card : ℕ) : ℝ) := by exact_mod_cast hC'
        _ = ∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
              (m : ℝ) ^ (β + 1) * ((G B).card : ℝ) := by push_cast; rfl
        _ ≤ ∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
              (m : ℝ) ^ (β + 1) * ((∏ v ∈ B, κ v) * d) := by
            apply Finset.sum_le_sum
            intro B hB
            exact mul_le_mul_of_nonneg_left (hcardG B hB) (by positivity)
        _ = d * (m : ℝ) ^ (β + 1) * esymmR κ (β + 1) := by
            unfold esymmR
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro B _
            ring
    · intro x hx
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.add_le_add_right hexp (β * S))
      rw [hk, pow_add, mul_smul]
      exact hCx _ (Submodule.smul_mem _ _ hx)
  have h2 : AllButLE π (L fun _ => Slot.base) (prodIdealMap π y m Sv (L fun _ => Slot.base)) 0
      (∑ v, Sv v) :=
    (hW V π L y m 0 c₀ S a b c Sv (fun B => (G B).card) G hm hcomm hbb hdb ha hb hc hy
      (hGw 0) hSv).2
  refine ⟨hβ, h2, ?_⟩
  have hs0 : (0 : ℝ) ≤ m * ∑ v, κ v :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun v _ => hκ v)
  have hVS : ∑ v, Sv v ≤ V * S := by
    calc ∑ v, Sv v ≤ ∑ _v : Fin V, S := Finset.sum_le_sum fun v _ => hSv v
      _ = V * S := by simp
  apply CyclicSpanLengthLemmas.lengthPart2 π hπ _ _ d hd _ S V _ hs0 hsum
  · intro β _
    obtain ⟨C, hCM, hCcard, hCx⟩ := hβ β
    refine ⟨C, hCM, ?_, hCx⟩
    have hE := ManyOrbitsP.esymmR_le κ hκ (m : ℝ) (Nat.cast_nonneg _) (β + 1)
    have hP : (0 : ℝ) ≤ ((m : ℝ) * ∑ v, κ v) ^ (β + 1) := pow_nonneg hs0 _
    have hF : ((m : ℝ) * ∑ v, κ v) ^ (β + 1) / ((β + 1).factorial : ℝ) ≤
        ((m : ℝ) * ∑ v, κ v) ^ (β + 1) :=
      div_le_self hP (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
    calc (C.card : ℝ) ≤ d * (m : ℝ) ^ (β + 1) * esymmR κ (β + 1) := hCcard
      _ = d * ((m : ℝ) ^ (β + 1) * esymmR κ (β + 1)) := by ring
      _ ≤ d * (((m : ℝ) * ∑ v, κ v) ^ (β + 1)) :=
          mul_le_mul_of_nonneg_left (hE.trans hF) (Nat.cast_nonneg _)
  · exact ManyOrbitsP.allBut_mono h2 le_rfl hVS
end Formalism.G0
