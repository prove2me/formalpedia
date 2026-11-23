-- Prove2me | solution 1 for GL2QFT.Circuits.totalA_hard_entry
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:39:08.944606+00:00
-- url     : https://prove2.me/submissions/e90ce86c-87ec-4a1c-9028-52a03209429d

import Definitions.Def_GL2QFT_Circuits_Leaves
import Theorems.Thm_GL2QFT_Circuits_A70_eq_AGamma

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

open GL2QFT GL2QFT.Circuits

/-- Entrywise form of the hard block of `totalA`: validity identifies the two character labels,
and the only possible columns are (143). -/
theorem solution (D : FieldData) (hq : 2 < D.q)
    (γ γ' : D.Lab) (κ : D.BIrr) (ω : Bool)
    (hv : ValidIn D (.inr γ) κ ω (.inr γ')) (μ : D.Irr) :
    totalA D (.inr γ, μ, .inr γ') ⟨(.inr γ, κ, ω, .inr γ'), hv⟩ =
      D.AGamma γ μ (if ω then (match κ with | .inl ab => some ab.1 | .inr _ => none) else none) := by
  have h := (A70_eq_AGamma D).1 ⟨(.inr γ, κ, ω, .inr γ'), hv⟩ γ γ' rfl rfl
  rcases h with ⟨hgg, hfalse, htrue⟩
  subst γ'
  simp only [totalA, Matrix.of_apply, and_self, ↓reduceIte]
  cases ω with
  | false =>
      have hk : κ = .inr γ := hfalse rfl
      subst κ
      simpa using (A70_eq_AGamma D).2 hq γ none μ
  | true =>
      cases κ with
      | inl ab =>
          have hab : ab.1 + ab.2 = γ := htrue ab rfl rfl
          have hsub : γ - ab.1 = ab.2 := by rw [← hab, add_sub_cancel_left]
          simpa [hsub] using (A70_eq_AGamma D).2 hq γ (some ab.1) μ
      | inr δ =>
          simp [ValidIn] at hv
