-- Prove2me | solution 1 for FramingFulfillment.RFF.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T15:05:04.086252+00:00
-- url     : https://prove2.me/submissions/0016b511-8a21-4c79-86fb-71585839eec5

import Mathlib
import Definitions.Def_FramingFulfillment_RFF_Model

open FramingFulfillment.RFF Finset

theorem solution (P : Inst) (hP : P.Standing) (x : Fin P.I → Fin P.R → ℝ)
    (h10a : ∀ r, ∑ i, x i r ≤ (P.Q r : ℝ)) (h10b : ∀ i, ∑ r, x i r = 1)
    (h10e : ∀ i r, 0 ≤ x i r ∧ x i r ≤ 1) :
    IsFramingMatrix (Bmat x) (Qtil x) ∧
    ∀ A : Fin (P.I + Itil x) → Fin P.R → ℝ, IsIntegralMatrix A → IsFramingMatrix A (Qtil x) →
      (∃! φ : Fin P.I → Fin P.R, ∀ i r, φ i = r ↔ A (Fin.castAdd (Itil x) i) r = 1) ∧
      ∀ φ : Fin P.I → Fin P.R, (∀ i r, φ i = r ↔ A (Fin.castAdd (Itil x) i) r = 1) →
        φ ∈ P.Omega := by
  classical
  have hq : ∀ r, qSum x r ≤ (Qtil x r : ℝ) := fun r => Nat.le_ceil _
  have hsumq : (∑ r, qSum x r) = (P.I : ℝ) := by
    simp only [qSum]; rw [Finset.sum_comm]; simp [h10b]
  have hge : (P.I : ℝ) ≤ ((∑ r, Qtil x r : ℕ) : ℝ) := by
    rw [← hsumq]; push_cast; exact Finset.sum_le_sum fun r _ => hq r
  have hge' : P.I ≤ ∑ r, Qtil x r := by exact_mod_cast hge
  have hIt : (Itil x : ℝ) = (∑ r, (Qtil x r : ℝ)) - P.I := by
    simp only [Itil]; rw [Nat.cast_sub hge']; push_cast; ring
  refine ⟨⟨fun n => ?_, fun r => ?_⟩, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun k => ?_) n
    · simp [Bmat, h10b]
    · simp only [Bmat, Fin.addCases_right]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, hsumq, ← hIt]
      have : (Itil x : ℝ) ≠ 0 := by
        have := k.pos; exact_mod_cast (by omega : Itil x ≠ 0)
      field_simp
  · rw [Fin.sum_univ_add]
    simp only [Bmat, Fin.addCases_left, Fin.addCases_right]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    by_cases h0 : Itil x = 0
    · -- then every q_r equals its ceiling
      have hall : ∀ r, qSum x r = (Qtil x r : ℝ) := by
        have hz : (∑ r, ((Qtil x r : ℝ) - qSum x r)) = 0 := by
          rw [Finset.sum_sub_distrib, hsumq]
          have := hIt; rw [h0] at this; push_cast at this; linarith
        intro r
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => sub_nonneg.2 (hq r))).1 hz r
          (Finset.mem_univ _)
        linarith
      simp only [h0, Nat.cast_zero, zero_mul, add_zero]
      exact hall r
    · have : (Itil x : ℝ) ≠ 0 := by exact_mod_cast h0
      field_simp
      simp [qSum]
  · intro A hAi hAf
    obtain ⟨hrow, hcol⟩ := hAf
    have hex : ∀ i : Fin P.I, ∃! r, A (Fin.castAdd (Itil x) i) r = 1 := by
      intro i
      have hs := hrow (Fin.castAdd (Itil x) i)
      obtain ⟨r, hr⟩ : ∃ r, A (Fin.castAdd (Itil x) i) r = 1 := by
        by_contra hc
        push_neg at hc
        have : ∀ r, A (Fin.castAdd (Itil x) i) r = 0 := fun r =>
          (hAi _ r).resolve_right (hc r)
        simp [this] at hs
      refine ⟨r, hr, fun r' hr' => ?_⟩
      by_contra hne
      have hnn : ∀ s, 0 ≤ A (Fin.castAdd (Itil x) i) s := fun s => by
        rcases hAi _ s with h | h <;> rw [h] <;> norm_num
      have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {r, r'})
        (fun s _ _ => hnn s)
      rw [Finset.sum_pair (Ne.symm hne), hr, hr', hs] at this
      norm_num at this
    have hmem : ∀ φ : Fin P.I → Fin P.R,
        (∀ i r, φ i = r ↔ A (Fin.castAdd (Itil x) i) r = 1) → φ ∈ P.Omega := by
      intro φ hφ
      simp only [Inst.Omega, Finset.mem_filter, Finset.mem_univ, true_and]
      intro r
      have hnn : ∀ n s, 0 ≤ A n s := fun n s => by
        rcases hAi n s with h | h <;> rw [h] <;> norm_num
      have hcnt : ((univ.filter (fun i => φ i = r)).card : ℝ) =
          ∑ i : Fin P.I, A (Fin.castAdd (Itil x) i) r := by
        rw [Finset.card_filter]; push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : φ i = r
        · rw [if_pos h, (hφ i r).1 h]
        · rw [if_neg h]
          exact ((hAi _ r).resolve_right (fun h' => h ((hφ i r).2 h'))).symm
      have hle : (∑ i : Fin P.I, A (Fin.castAdd (Itil x) i) r) ≤ (Qtil x r : ℝ) := by
        rw [← hcol r, Fin.sum_univ_add]
        have : 0 ≤ ∑ k : Fin (Itil x), A (Fin.natAdd P.I k) r :=
          Finset.sum_nonneg fun k _ => hnn _ _
        linarith
      have hQ : Qtil x r ≤ P.Q r := Nat.ceil_le.2 (h10a r)
      have : ((univ.filter (fun i => φ i = r)).card : ℝ) ≤ (P.Q r : ℝ) := by
        rw [hcnt]; exact hle.trans (by exact_mod_cast hQ)
      exact_mod_cast this
    refine ⟨?_, hmem⟩
    choose φ hφ1 hφ2 using hex
    refine ⟨φ, fun i r => ⟨fun h => h ▸ hφ1 i, fun h => (hφ2 i r h).symm⟩, ?_⟩
    intro ψ hψ
    funext i
    exact (hψ i (φ i)).2 (hφ1 i)
