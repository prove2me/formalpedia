-- Prove2me | solution 1 for Formalism.DivisionValues.young_diagram_period
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:01.033864+00:00
-- url     : https://prove2.me/submissions/83077102-e1c1-46bf-ac60-c909b16890ee

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Theorems.Thm_Formalism_DivisionValues_W8_sum_univ_cast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
namespace W8
end W8
open W8
private lemma cast_sum_map_add_offset_eq {n w : ℕ} (c : Fin (n + 1) → ℕ) (blk : Multiset ℕ) :
    ((((Finset.univ.val.map fun i => w + c i) + blk).sum : ℕ) : ℝ) =
      ((n : ℝ) + 1) * w + ∑ i, (c i : ℝ) + (blk.sum : ℝ) := by
  rw [Multiset.sum_add, Nat.cast_add, sum_univ_cast]
  simp only [Nat.cast_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_one]
private lemma cast_sum_cons_cons_map_add_offset_eq {n aT w r0 : ℕ} (c : Fin n → ℕ) (blk : Multiset ℕ) :
    ((((aT + w) ::ₘ r0 ::ₘ ((Finset.univ.val.map fun i => w + c i) + blk)).sum : ℕ) : ℝ) =
      (aT : ℝ) + ((n : ℝ) + 1) * w + r0 + ∑ i, (c i : ℝ) + (blk.sum : ℝ) := by
  rw [Multiset.sum_cons, Multiset.sum_cons, Multiset.sum_add]
  simp only [Nat.cast_add]
  rw [sum_univ_cast]
  simp only [Nat.cast_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring
namespace W8
end W8
end Formalism.DivisionValues
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
open W8
namespace Formalism.DivisionValues
theorem _root_.solution : RowsPeriod := by
  intro n w S Bl sh ν ap
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  refine ⟨fun hoff => ?_, fun aT htop => ?_⟩
  · obtain ⟨c, c', r, blk, sm, hI, -, hblk, hν, -⟩ := hoff
    subst hν
    have hs := cast_sum_map_add_offset_eq (w := w) c blk
    have hcS : ∑ i, (c i : ℝ) ≤ ((n : ℝ) + 1) * S := by
      have h := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
        (hI.1 i).2
      simpa using h
    have hc0 : 0 ≤ ∑ i, (c i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
    have hb0 : (0 : ℝ) ≤ blk.sum := Nat.cast_nonneg _
    constructor <;> linarith
  · obtain ⟨c, c', r, r0, blk, sm, hI, -, hr0, hblk, hν, -⟩ := htop
    subst hν
    have hs := cast_sum_cons_cons_map_add_offset_eq (aT := aT) (w := w) (r0 := r0) c blk
    have hcS : ∑ i, (c i : ℝ) ≤ (n : ℝ) * S := by
      have h := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        le_trans (hI.2 i).1 (hI.1 i.castSucc).2
      simpa using h
    have hc0 : 0 ≤ ∑ i, (c i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
    have hb0 : (0 : ℝ) ≤ blk.sum := Nat.cast_nonneg _
    have hr0' : (r0 : ℝ) ≤ w := by exact_mod_cast hr0
    have hr00 : (0 : ℝ) ≤ r0 := Nat.cast_nonneg _
    constructor <;> linarith
end Formalism.DivisionValues
