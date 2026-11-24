-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.sum_sLe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:49.613883+00:00
-- url     : https://prove2.me/submissions/724ebb47-8ffd-4902-9ab1-158424a7bc14

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_mem_stripsUp
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_mem_sLe

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
theorem _root_.solution {n : ℕ} (κ : Fin n → ℤ) (b : ℕ) (f : (Fin n → ℤ) → ℕ) :
    ∑ l ∈ sLe κ b, f l = ∑ c ∈ Finset.range (b + 1), ∑ l ∈ stripsUp κ c, f l := by
  have hnn : ∀ l : Fin n → ℤ, (∀ m, κ m ≤ l m) → 0 ≤ ∑ m, l m - ∑ m, κ m := by
    intro l hl
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg (fun m _ => sub_nonneg.mpr (hl m))
  symm
  rw [← Finset.sum_fiberwise_of_maps_to (s := sLe κ b) (t := Finset.range (b + 1))
    (g := fun l => (∑ m, l m - ∑ m, κ m).toNat) (by
      intro l hl
      rw [mem_sLe] at hl
      have := hnn l hl.1
      rw [Finset.mem_range]
      omega)]
  refine Finset.sum_congr rfl (fun c hc => Finset.sum_congr ?_ (fun _ _ => rfl))
  rw [Finset.mem_range] at hc
  ext l
  simp only [Finset.mem_filter, mem_sLe, mem_stripsUp, HStrip]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2, by omega⟩, by omega⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    have := hnn l h1
    exact ⟨h1, h2, by omega⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
