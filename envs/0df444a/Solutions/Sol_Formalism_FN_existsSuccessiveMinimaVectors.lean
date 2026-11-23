-- Prove2me | solution 1 for Formalism.FN.existsSuccessiveMinimaVectors
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:24.440792+00:00
-- url     : https://prove2.me/submissions/00b5092d-5e00-4db1-b461-4fb5e0df2dfa

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_SuccMin
import Theorems.Thm_Formalism_FN_SuccessiveMinima_mem_smul_iff_gauge
import Theorems.Thm_Formalism_FN_SuccessiveMinima_succMin_mem
import Theorems.Thm_Formalism_FN_SuccessiveMinima_exists_pos_bot
import Theorems.Thm_Formalism_FN_SuccessiveMinima_exists_span_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise
noncomputable section
open Formalism.FN.SuccessiveMinima
namespace Formalism.FN
theorem _root_.solution : Formalism.FN.SuccMinFacts := by
  classical
  intro E _ _ _ L _ _ K hKc hKv _ hK0
  have hmemK : ∀ {t : ℝ}, 0 ≤ t → ∀ u, u ∈ t • K ↔ gauge K u ≤ t :=
    fun ht u => mem_smul_iff_gauge hKc hKv hK0 ht u
  obtain ⟨T, hT0, hTtop⟩ := exists_span_top L hKc hKv hK0
  have hTfin : finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ T • K)) = finrank ℝ E := by
    rw [hTtop, finrank_top]
  have hmem : ∀ j, j ≤ finrank ℝ E → 0 ≤ succMin L K j ∧
      j ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ succMin L K j • K)) :=
    fun j hj => succMin_mem L hKc hKv hK0 ⟨hT0, by rw [hTfin]; exact hj⟩
  have hsub : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → (L : Set E) ∩ s • K ⊆ (L : Set E) ∩ t • K :=
    fun hs hst u hu => ⟨hu.1, (hmemK (hs.trans hst) u).mpr (((hmemK hs u).mp hu.2).trans hst)⟩
  have hle : ∀ {j : ℕ} {t : ℝ}, 0 ≤ t →
      j ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ t • K)) → succMin L K j ≤ t :=
    fun ht h => csInf_le ⟨0, fun x hx => hx.1⟩ ⟨ht, h⟩
  obtain ⟨m, hm0, hmbot⟩ := exists_pos_bot L hKc hKv hK0
  have hpos : ∀ j, 1 ≤ j → j ≤ finrank ℝ E → 0 < succMin L K j := by
    intro j hj1 hjn
    obtain ⟨h0, hj⟩ := hmem j hjn
    by_contra hneg
    push_neg at hneg
    rw [hmbot _ h0 (lt_of_le_of_lt hneg hm0), finrank_bot] at hj
    omega

  have build : ∀ k, k ≤ finrank ℝ E → ∃ w : Fin k → E, LinearIndependent ℝ w ∧
      ∀ j : Fin k, w j ∈ L ∧ w j ∈ succMin L K ((j : ℕ) + 1) • K := by
    intro k
    induction k with
    | zero => intro _; exact ⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨w, hw, hwm⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨_, hdim⟩ := hmem (k + 1) hk
      have hex : ∃ x ∈ (L : Set E) ∩ succMin L K (k + 1) • K,
          x ∉ Submodule.span ℝ (Set.range w) := by
        by_contra hno
        push_neg at hno
        have h1 := Submodule.finrank_mono (Submodule.span_le.mpr hno)
        rw [finrank_span_eq_card hw, Fintype.card_fin] at h1
        omega
      obtain ⟨x, ⟨hxL, hxK⟩, hxw⟩ := hex
      refine ⟨Fin.snoc w x, linearIndependent_fin_snoc.mpr ⟨hw, hxw⟩, fun j => ?_⟩
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.snoc_last, Fin.val_last]
        exact ⟨hxL, hxK⟩
      · simp only [Fin.snoc_castSucc, Fin.coe_castSucc]
        exact hwm i
  obtain ⟨v, hv, hvm⟩ := build (finrank ℝ E) le_rfl
  refine ⟨v, hv, fun i => (hvm i).1, fun i => (hvm i).2,
    fun i => hpos _ (by omega) (Nat.succ_le_of_lt i.isLt), ?_, ?_⟩
  · intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    obtain ⟨h0, hj⟩ := hmem ((j : ℕ) + 1) (Nat.succ_le_of_lt j.isLt)
    exact hle h0 (le_trans (by omega) hj)
  · intro i u huL huint
    have hlam : 0 < succMin L K ((i : ℕ) + 1) := hpos _ (by omega) (Nat.succ_le_of_lt i.isLt)

    have hg : gauge K u < succMin L K ((i : ℕ) + 1) := by
      obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp huint
      rw [gauge_smul_of_nonneg hlam.le, smul_eq_mul]
      exact mul_lt_of_lt_one_right hlam (interior_subset_gauge_lt_one K hy)
    have hg0 : 0 ≤ gauge K u := gauge_nonneg u
    set W := Submodule.span ℝ ((L : Set E) ∩ gauge K u • K) with hW
    have huW : u ∈ W := Submodule.subset_span ⟨huL, (hmemK hg0 u).mpr le_rfl⟩
    have hdn : finrank ℝ W ≤ finrank ℝ E := Submodule.finrank_le W
    have hdi : finrank ℝ W ≤ (i : ℕ) := by
      by_contra hcon
      push_neg at hcon
      have := hle hg0 (show (i : ℕ) + 1 ≤ finrank ℝ W by omega)
      linarith

    have hdW : succMin L K (finrank ℝ W) ≤ gauge K u := hle hg0 le_rfl
    have hvW : ∀ k : Fin (finrank ℝ E), (k : ℕ) < finrank ℝ W → v k ∈ W := by
      intro k hk
      obtain ⟨hd0, hd⟩ := hmem (finrank ℝ W) hdn
      have hk1 : succMin L K ((k : ℕ) + 1) ≤ gauge K u :=
        (hle hd0 (le_trans (by omega) hd)).trans hdW
      exact Submodule.subset_span
        (hsub (hmem _ (Nat.succ_le_of_lt k.isLt)).1 hk1 ⟨(hvm k).1, (hvm k).2⟩)
    have himg : v '' {k | (k : ℕ) < finrank ℝ W} =
        Set.range (fun j : Fin (finrank ℝ W) => v (Fin.castLE hdn j)) := by
      ext x
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨k, hk⟩, congrArg v (Fin.ext rfl)⟩
      · rintro ⟨j, rfl⟩
        exact ⟨Fin.castLE hdn j, by simp, rfl⟩
    have hUW : Submodule.span ℝ (v '' {k | (k : ℕ) < finrank ℝ W}) = W := by
      refine Submodule.eq_of_le_of_finrank_eq
        (Submodule.span_le.mpr ?_) ?_
      · rintro x ⟨k, hk, rfl⟩
        exact hvW k hk
      · rw [himg]
        exact (finrank_span_eq_card (hv.comp _ (Fin.castLE_injective hdn))).trans
          (Fintype.card_fin _)
    rw [← hUW] at huW
    refine Submodule.span_mono (Set.image_mono fun k hk => ?_) huW
    show k < i
    exact Fin.lt_iff_val_lt_val.mpr (lt_of_lt_of_le hk hdi)
end Formalism.FN
