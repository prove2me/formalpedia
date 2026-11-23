-- Prove2me | solution 1 for Formalism.DivisionValues.RowsOrigin.off_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:30.529812+00:00
-- url     : https://prove2.me/submissions/ac088aac-4951-475c-944c-b42bb87bf1ef

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRowsShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramTopExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.RowsOrigin
namespace Formalism.DivisionValues.RowsOrigin
theorem _root_.solution {n wr T : ℕ} {Sc Bl sh : ℝ} (νr : Fin (n + 2) → ℕ) (ar : Fin (n + 1) → ℕ)
    (blk sm : Multiset ℕ)
    (H1 : ∀ i, ar i ≤ νr i.castSucc + T) (H2 : ∀ i, νr i.succ + T ≤ ar i)
    (H3 : wr ≤ νr (Fin.last (n + 1))) (H4 : (νr 0 : ℝ) ≤ (wr : ℝ) + Sc) (hT : (T : ℝ) ≤ sh)
    (hB : (blk.sum : ℝ) ≤ Bl) :
    IsRowsOff (n + 1) wr Sc Bl sh (Finset.univ.val.map νr + blk) (Finset.univ.val.map ar + sm) := by
  have anti : Antitone νr := Fin.antitone_iff_succ_le.2 (fun i => by
    have := H1 i; have := H2 i; omega)
  have lo : ∀ i, wr ≤ νr i := fun i => le_trans H3 (anti (Fin.le_last i))
  have hi : ∀ i, νr i ≤ νr 0 := fun i => anti (Fin.zero_le i)
  have loa : ∀ i, wr + T ≤ ar i := fun i => by have := H2 i; have := lo i.succ; omega
  refine ⟨fun i => νr i - wr, fun i => ar i - (wr + T), ar, blk, sm, ⟨?_, ?_⟩, ?_, hB, ?_, rfl⟩
  · intro i
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have h1 : ((νr i - wr : ℕ) : ℝ) = (νr i : ℝ) - (wr : ℝ) := Nat.cast_sub (lo i)
    have h2 : (νr i : ℝ) ≤ (νr 0 : ℝ) := by exact_mod_cast hi i
    simp only
    rw [h1]; linarith
  · intro i
    have := H1 i; have := H2 i; have := lo i.succ; have := lo i.castSucc
    constructor
    · simp only
      exact_mod_cast (by omega : ar i - (wr + T) ≤ νr i.castSucc - wr)
    · simp only
      exact_mod_cast (by omega : νr i.succ - wr ≤ ar i - (wr + T))
  · intro i
    have h1 : ((ar i - (wr + T) : ℕ) : ℝ) = (ar i : ℝ) - ((wr : ℝ) + (T : ℝ)) := by
      rw [Nat.cast_sub (loa i)]; push_cast; ring
    simp only
    rw [h1]
    have : (ar i : ℝ) - ((wr : ℝ) + ((ar i : ℝ) - ((wr : ℝ) + (T : ℝ)))) = (T : ℝ) := by ring
    rw [this, abs_of_nonneg (Nat.cast_nonneg _)]
    exact hT
  · congr 1
    apply Multiset.map_congr rfl
    intro i _
    have := lo i
    simp only
    omega
end Formalism.DivisionValues.RowsOrigin
