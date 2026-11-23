-- Prove2me | solution 1 for Formalism.DivisionValues.RowsOrigin.top_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:39.659039+00:00
-- url     : https://prove2.me/submissions/524aba32-b8b5-4497-b42f-463428d3e9e7

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRowsShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramTopExact
import Theorems.Thm_Formalism_DivisionValues_RowsOrigin_univ_split

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
theorem _root_.solution {n wr T aT : ℕ} {Sc Bl sh : ℝ} (νr : Fin (n + 2) → ℕ) (ar : Fin (n + 1) → ℕ)
    (blk sm : Multiset ℕ)
    (H1 : ∀ i, ar i ≤ νr i.castSucc + T) (H2 : ∀ i, νr i.succ + T ≤ ar i)
    (H0 : νr 0 = aT + wr) (Hl : νr (Fin.last (n + 1)) ≤ wr)
    (H3 : wr + T ≤ ar (Fin.last n)) (H4 : (ar 0 : ℝ) ≤ (wr : ℝ) + (T : ℝ) + Sc) (hT : (T : ℝ) ≤ sh)
    (hB : (blk.sum : ℝ) ≤ Bl) :
    IsRowsTop n aT wr Sc Bl sh (Finset.univ.val.map νr + blk) (Finset.univ.val.map ar + sm) := by
  have anti : Antitone ar := Fin.antitone_iff_succ_le.2 (fun i => by
    have h1 := H1 i.succ; have h2 := H2 i.castSucc
    rw [Fin.succ_castSucc] at h2
    omega)
  have loa : ∀ i, wr + T ≤ ar i := fun i => le_trans H3 (anti (Fin.le_last i))
  have hia : ∀ i, ar i ≤ ar 0 := fun i => anti (Fin.zero_le i)
  have lo : ∀ i : Fin n, wr ≤ νr i.castSucc.succ := fun i => by
    have h1 := H1 i.succ; have := loa i.succ
    rw [← Fin.succ_castSucc] at h1
    omega
  refine ⟨fun i => νr i.castSucc.succ - wr, fun i => ar i - (wr + T), ar, νr (Fin.last (n + 1)), blk, sm,
    ⟨?_, ?_⟩, ?_, Hl, hB, ?_, rfl⟩
  · intro i
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have h1 : ((ar i - (wr + T) : ℕ) : ℝ) = (ar i : ℝ) - ((wr : ℝ) + (T : ℝ)) := by
      rw [Nat.cast_sub (loa i)]; push_cast; ring
    have h2 : (ar i : ℝ) ≤ (ar 0 : ℝ) := by exact_mod_cast hia i
    simp only
    rw [h1]; linarith
  · intro i
    have h1 := H1 i.succ; have h2 := H2 i.castSucc
    rw [← Fin.succ_castSucc] at h1
    have := lo i; have := loa i.succ; have := loa i.castSucc
    constructor
    · simp only
      exact_mod_cast (by omega : νr i.castSucc.succ - wr ≤ ar i.castSucc - (wr + T))
    · simp only
      exact_mod_cast (by omega : ar i.succ - (wr + T) ≤ νr i.castSucc.succ - wr)
  · intro i
    have h1 : ((ar i - (wr + T) : ℕ) : ℝ) = (ar i : ℝ) - ((wr : ℝ) + (T : ℝ)) := by
      rw [Nat.cast_sub (loa i)]; push_cast; ring
    simp only
    rw [h1]
    have : (ar i : ℝ) - ((wr : ℝ) + ((ar i : ℝ) - ((wr : ℝ) + (T : ℝ)))) = (T : ℝ) := by ring
    rw [this, abs_of_nonneg (Nat.cast_nonneg _)]
    exact hT
  · rw [univ_split νr, H0, Multiset.cons_add, Multiset.cons_add]
    congr 3
    apply Multiset.map_congr rfl
    intro i _
    have := lo i
    simp only
    omega
end Formalism.DivisionValues.RowsOrigin
