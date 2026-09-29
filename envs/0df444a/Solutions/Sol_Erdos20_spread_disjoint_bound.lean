-- Prove2me | solution 1 for Erdos20.spread_disjoint_bound
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-09-26T16:19:30.652955+00:00
-- url     : https://prove2.me/submissions/b79c2af0-90ec-48d5-bac6-b53cbc88fcb9

import Definitions.Def_SunflowerSpread
import Theorems.Thm_Erdos20_spread_bernoulli_hitting
import Theorems.Thm_Erdos20_disjoint_of_bernoulli_hitting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit false

namespace Erdos20

/-- Restricting a spread family along an embedding preserves spread. -/
theorem isSpread_of_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (R : ℝ) (F : Finset (Finset α))
    (h : IsSpread R (F.map (Finset.mapEmbedding e).toEmbedding)) : IsSpread R F := by
  intro T
  have ht := h (T.map e)
  simpa [Finset.filter_map, Function.comp_def] using ht

/-- Every finite set family can be moved to its finite union, without changing
spread, ranks, or its pairwise-disjoint subfamilies. -/
theorem disjoint_of_finite_ground (n k : ℕ) (R : ℝ)
    (hfinite : ∀ {β : Type} [Fintype β] [DecidableEq β] (G : Finset (Finset β)),
      G.Nonempty → (∀ A ∈ G, A.Nonempty ∧ A.card ≤ n) → IsSpread R G →
      ∃ H ⊆ G, H.card = k ∧ ∀ A ∈ H, ∀ B ∈ H, A ≠ B → Disjoint A B)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hF : F.Nonempty) (hrank : ∀ A ∈ F, A.Nonempty ∧ A.card ≤ n)
    (hspread : IsSpread R F) :
    ∃ H ⊆ F, H.card = k ∧ ∀ A ∈ H, ∀ B ∈ H, A ≠ B → Disjoint A B := by
  classical
  let U := F.biUnion id
  let β := {a // a ∈ U}
  let e : β ↪ α := Function.Embedding.subtype _
  let restrict : Finset α → Finset β := fun A => A.subtype (fun a => a ∈ U)
  have hrecover (A : Finset α) (hA : A ∈ F) : (restrict A).map e = A := by
    apply Finset.subtype_map_of_mem
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨A, hA, ha⟩
  let G := F.image restrict
  have hmap : G.map (Finset.mapEmbedding e).toEmbedding = F := by
    change (F.image restrict).map (Finset.mapEmbedding e).toEmbedding = F
    rw [Finset.map_eq_image, Finset.image_image]
    calc
      _ = F.image id := Finset.image_congr fun A hA => hrecover A hA
      _ = F := Finset.image_id
  have hG : G.Nonempty := hF.image restrict
  have hrankG : ∀ A ∈ G, A.Nonempty ∧ A.card ≤ n := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    have hcard : (restrict B).card = B.card := by
      exact (Finset.card_map _).symm.trans (congrArg Finset.card (hrecover B hB))
    constructor
    · apply Finset.card_pos.mp
      rw [hcard]
      exact Finset.card_pos.mpr (hrank B hB).1
    · simpa only [hcard] using (hrank B hB).2
  have hspreadG : IsSpread R G := isSpread_of_map e R G (hmap.symm ▸ hspread)
  obtain ⟨H, hHG, hHcard, hdisj⟩ := hfinite G hG hrankG hspreadG
  refine ⟨H.map (Finset.mapEmbedding e).toEmbedding, ?_, by simpa, ?_⟩
  · rw [← hmap]
    exact Finset.map_subset_map.mpr hHG
  · intro A hA B hB hne
    obtain ⟨A', hA', rfl⟩ := Finset.mem_map.mp hA
    obtain ⟨B', hB', rfl⟩ := Finset.mem_map.mp hB
    have hne' : A' ≠ B' := fun heq => hne (congrArg _ heq)
    exact (Finset.disjoint_map e).mpr (hdisj A' hA' B' hB' hne')

end Erdos20

namespace Erdos20

private theorem spread_disjoint_proof :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ (n k : ℕ), 2 ≤ n → 2 ≤ k →
      ∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
        F.Nonempty → (∀ A ∈ F, A.Nonempty ∧ A.card ≤ n) →
        IsSpread (C * k * Real.log n) F →
        ∃ H ⊆ F, H.card = k ∧
          ∀ A ∈ H, ∀ B ∈ H, A ≠ B → Disjoint A B := by
  obtain ⟨C, hC, hhit⟩ := spread_bernoulli_hitting
  refine ⟨C, hC, ?_⟩
  intro n k hn hk α _ F hF hrank hspread
  apply disjoint_of_finite_ground n k (C * k * Real.log n) ?_ F hF hrank hspread
  intro β _ _ G hG hrankG hspreadG
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  let p : unitInterval := ⟨(2 * (k : ℝ))⁻¹,
    inv_nonneg.mpr (by positivity), inv_le_one_of_one_le₀ (by linarith)⟩
  have hprob := hhit n k hn hk G hG (fun A hA => (hrankG A hA).2) hspreadG p rfl
  exact disjoint_of_bernoulli_hitting G (fun A hA => (hrankG A hA).1)
    k (by omega) p rfl hprob


end Erdos20

theorem solution :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ (n k : ℕ), 2 ≤ n → 2 ≤ k →
      ∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
        F.Nonempty → (∀ A ∈ F, A.Nonempty ∧ A.card ≤ n) →
        Erdos20.IsSpread (C * k * Real.log n) F →
        ∃ H ⊆ F, H.card = k ∧
          ∀ A ∈ H, ∀ B ∈ H, A ≠ B → Disjoint A B := Erdos20.spread_disjoint_proof
