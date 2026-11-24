-- Prove2me | solution 1 for Formalism.G0.manyOrbits_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:06.728146+00:00
-- url     : https://prove2.me/submissions/dbb4ace4-4b79-4707-a83b-35c8ca87fa82

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
import Theorems.Thm_Formalism_G0_ManyOrbitsP_esymmR_le
import Theorems.Thm_Formalism_G0_ManyOrbitsP_allBut_mono
import Theorems.Thm_Formalism_G0_ManyOrbitsP_lengthPart

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
theorem _root_.solution (hW : WalkSharp) : ManyOrbits := by
  intro R X _ _ _ _ _ V π hπ L y m β₀ c₀ S d a b c Sv κ G _ _ hd hm hcomm hb1 hb2 hb3 hb4 hb5
    hb6 hG hκ habc hSv hs
  have hprod : ∀ B : Finset (Fin V), 0 ≤ 2 * (∏ v ∈ B, κ v) * (d : ℝ) := fun B =>
    mul_nonneg (mul_nonneg zero_le_two (Finset.prod_nonneg fun v _ => hκ v)) (Nat.cast_nonneg d)
  have ws : ∀ β ≤ β₀ + 1,
      AllButLE π (L fun _ => Slot.base) (prodIdealMap π y m Sv (L fun _ => Slot.base))
        (∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
          m ^ (β + 1) * ⌊2 * (∏ v ∈ B, κ v) * (d : ℝ)⌋₊)
        (∑ v, (a v + b v + (m - 1) * c v + m * c₀) + β * S) ∧
      AllButLE π (L fun _ => Slot.base) (prodIdealMap π y m Sv (L fun _ => Slot.base)) 0
        (∑ v, Sv v) := by
    intro β hβ
    exact hW V π L y m β c₀ S a b c Sv (fun B => ⌊2 * (∏ v ∈ B, κ v) * (d : ℝ)⌋₊) G hm hcomm
      hb1 hb2 hb3 hb4 hb5 hb6
      (fun B hB => ⟨(hG B (by omega)).1, Nat.le_floor (hG B (by omega)).2.1,
        (hG B (by omega)).2.2⟩) hSv
  have hexp : ∑ v, (a v + b v + (m - 1) * c v + m * c₀) ≤ ∑ v, m * (c v + c₀) := by
    apply Finset.sum_le_sum
    intro v _
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have := habc v
    simp only [Nat.add_sub_cancel]
    nlinarith
  have cl1 : ∀ β ≤ β₀ + 1, ∃ C : Finset X, (↑C : Set X) ⊆ (L fun _ => Slot.base) ∧
      (C.card : ℝ) ≤ 2 * (m : ℝ) ^ (β + 1) * esymmR κ (β + 1) * d ∧
      ∀ x ∈ (L fun _ => Slot.base), π ^ (∑ v, m * (c v + c₀) + β * S) • x ∈
        prodIdealMap π y m Sv (L fun _ => Slot.base) ⊔ Submodule.span R (↑C : Set X) := by
    intro β hβ
    obtain ⟨C, hCM, hcard, hx⟩ :=
      ManyOrbitsP.allBut_mono (ws β hβ).1 le_rfl (Nat.add_le_add_right hexp _)
    refine ⟨C, hCM, ?_, hx⟩
    calc (C.card : ℝ)
        ≤ ((∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
            m ^ (β + 1) * ⌊2 * (∏ v ∈ B, κ v) * (d : ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hcard
      _ ≤ ∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
            (m : ℝ) ^ (β + 1) * (2 * (∏ v ∈ B, κ v) * d) := by
          push_cast
          apply Finset.sum_le_sum
          intro B _
          exact mul_le_mul_of_nonneg_left (Nat.floor_le (hprod B)) (by positivity)
      _ = 2 * (m : ℝ) ^ (β + 1) * esymmR κ (β + 1) * d := by
          unfold esymmR
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro B _
          ring
  have hs0 : 0 ≤ (m : ℝ) * ∑ v, κ v :=
    mul_nonneg (Nat.cast_nonneg m) (Finset.sum_nonneg fun v _ => hκ v)
  have hVS : ∑ v, Sv v ≤ V * S := by
    calc ∑ v, Sv v ≤ ∑ _v : Fin V, S := Finset.sum_le_sum fun v _ => hSv v
      _ = V * S := by simp
  refine ⟨cl1, (ws 0 (by omega)).2, ?_⟩
  refine ManyOrbitsP.lengthPart π hπ (L fun _ => Slot.base)
    (prodIdealMap π y m Sv (L fun _ => Slot.base)) d hd (∑ v, m * (c v + c₀)) S V β₀
    ((m : ℝ) * ∑ v, κ v) hs0 hs ?_ (ManyOrbitsP.allBut_mono (ws 0 (by omega)).2 le_rfl hVS)
  intro β hβ
  obtain ⟨C, hCM, hcard, hx⟩ := cl1 β (by omega)
  refine ⟨C, hCM, ?_, hx⟩
  have hmac := ManyOrbitsP.esymmR_le κ hκ (m : ℝ) (Nat.cast_nonneg m) (β + 1)
  have hd0 : (0 : ℝ) ≤ 2 * d := by positivity
  calc (C.card : ℝ) ≤ 2 * (m : ℝ) ^ (β + 1) * esymmR κ (β + 1) * d := hcard
    _ = 2 * d * ((m : ℝ) ^ (β + 1) * esymmR κ (β + 1)) := by ring
    _ ≤ 2 * d * (((m : ℝ) * ∑ v, κ v) ^ (β + 1) / (β + 1).factorial) :=
        mul_le_mul_of_nonneg_left hmac hd0
end Formalism.G0
