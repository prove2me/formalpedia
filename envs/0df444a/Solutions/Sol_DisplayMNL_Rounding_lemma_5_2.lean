-- Prove2me | solution 1 for DisplayMNL.Rounding.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:41:08.186873+00:00
-- url     : https://prove2.me/submissions/21f8ca98-09b5-4244-885c-2794a1c54945

import Mathlib
import Definitions.Def_DisplayMNL_Rounding_Model

open Finset

namespace RRBL52
open DisplayMNL.Rounding

theorem rhoSet_nonneg {n : ℕ} (I : Instance n) (hr : ∀ i, 0 < I.r i) (hw : ∀ i, 0 < I.w i)
    (S : Finset (Fin n)) : 0 ≤ rhoSet I S :=
  Finset.sum_nonneg (fun i _ => (mul_pos (hr i) (hw i)).le)

theorem rhoSet_mono {n : ℕ} (I : Instance n) (hr : ∀ i, 0 < I.r i) (hw : ∀ i, 0 < I.w i)
    {S S' : Finset (Fin n)} (h : S ⊆ S') : rhoSet I S ≤ rhoSet I S' :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => (mul_pos (hr i) (hw i)).le)

theorem rhoSet_union_le {n : ℕ} (I : Instance n) (hr : ∀ i, 0 < I.r i) (hw : ∀ i, 0 < I.w i)
    (S S' : Finset (Fin n)) : rhoSet I (S ∪ S') ≤ rhoSet I S + rhoSet I S' := by
  unfold rhoSet
  have := Finset.sum_union_inter (s₁ := S) (s₂ := S') (f := fun i => rho I i)
  have h2 : 0 ≤ ∑ i ∈ S ∩ S', rho I i :=
    Finset.sum_nonneg (fun i _ => (mul_pos (hr i) (hw i)).le)
  linarith

theorem wt_mono {n : ℕ} (I : Instance n) (hw : ∀ i, 0 < I.w i)
    {S S' : Finset (Fin n)} (h : S ⊆ S') : wt I S ≤ wt I S' :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => (hw i).le)

end RRBL52

open DisplayMNL.Rounding in
theorem solution {n : ℕ} (I : Instance n) (ε : ℝ) (kmid : ℕ) (s : DPSeq n) (A : Fin n ≃ Fin n)
    (hst : Standing I ε) (hk1 : 1 ≤ kmid) (hk2 : kmid + 1 ≤ n)
    (hF : IsFeasible I ε kmid s) (hR : IsRounded I s kmid A)
    (j : ℕ) (hj1 : 1 ≤ j) (hjT : j ≤ s.T) :
    (1 - 8 * ε) * rhoSet I (s.sm j) ≤ rhoSet I (pre A (etil s kmid j)) := by
  obtain ⟨hn2, hr, hw, hlam, hε0, hε1⟩ := hst
  obtain ⟨hT1, _, ⟨he1, _⟩, ⟨heT, hSmT, hSpT⟩, htr⟩ := hF
  rw [(hR j hj1 hjT).1]
  -- S⁻_i ⊆ S⁺_i for i ∈ [1, T]
  have hsmsp : ∀ i, 1 ≤ i → i ≤ s.T → s.sm i ⊆ s.sp i := by
    intro i hi1 hiT
    rcases Nat.lt_or_ge i s.T with h | h
    · have := (htr (i + 1) (by omega) (by omega)).1.1
      rw [Nat.add_sub_cancel] at this
      exact this
    · have hi : i = s.T := le_antisymm hiT h
      rw [hi]
      unfold DPSeq.sm DPSeq.sp
      rw [if_neg (by omega), min_self, hSmT, hSpT]
  -- U_i ⊆ S⁺_i (proof of Lemma 5.3)
  have key : ∀ i, 1 ≤ i → i ≤ s.T → U s kmid i ⊆ s.sp i := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ i ih =>
      intro _ hiT
      show U s kmid i ∪ deltaStep s kmid (i + 1) (U s kmid i) ⊆ s.sp (i + 1)
      apply Finset.union_subset
      · rcases Nat.eq_zero_or_pos i with h0 | hpos
        · subst h0; simp [U]
        · have h1 := ih hpos (by omega)
          have h2 := (htr (i + 1) (by omega) hiT).1.2
          rw [Nat.add_sub_cancel] at h2
          exact h1.trans h2
      · unfold deltaStep
        split_ifs
        · exact Finset.sdiff_subset.trans (hsmsp (i + 1) (by omega) hiT)
        · exact Finset.sdiff_subset
  set jm := jmid s kmid with hjm
  have hP1 : (fun j => 1 ≤ j ∧ s.e j ≤ kmid) 1 := ⟨le_rfl, by rw [he1]; exact hk1⟩
  have hspec : 1 ≤ jm ∧ s.e jm ≤ kmid :=
    Nat.findGreatest_spec (P := fun j => 1 ≤ j ∧ s.e j ≤ kmid) hT1 hP1
  have hjmT : jm ≤ s.T := Nat.findGreatest_le _
  -- events are non-decreasing (constraint (11))
  have hev : ∀ t, 1 ≤ t → t ≤ s.T → s.ev t = s.e t := by
    intro t _ ht; unfold DPSeq.ev; rw [min_eq_left ht]
  have hemono : ∀ t d, 1 ≤ t → t + d ≤ s.T → s.e t ≤ s.e (t + d) := by
    intro t d ht1 htd
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
      have h11 := (htr (t + d + 1) (by omega) (by omega)).2.2.2.1.2
      rw [Nat.add_sub_cancel, hev _ (by omega) (by omega), hev _ (by omega) (by omega)] at h11
      have := ih (by omega)
      rw [← add_assoc]; omega
  have hle_kmid : ∀ t, 1 ≤ t → t ≤ jm → s.e t ≤ kmid := by
    intro t ht1 ht
    have := hemono t (jm - t) ht1 (by omega)
    rw [show t + (jm - t) = jm by omega] at this
    omega
  have hρnn := RRBL52.rhoSet_nonneg I hr hw
  by_cases hj : j ≤ jm
  · -- induction along t ∈ [1, j]
    have main : ∀ t, 1 ≤ t → t ≤ jm → (1 - 8 * ε) * rhoSet I (s.sm t) ≤ rhoSet I (U s kmid t) := by
      intro t
      induction t with
      | zero => intro h; omega
      | succ t ih =>
        intro _ htj
        have hU : U s kmid (t + 1) = U s kmid t ∪ deltaStep s kmid (t + 1) (U s kmid t) := rfl
        have hd : deltaStep s kmid (t + 1) (U s kmid t) = s.sm (t + 1) \ (s.sp t ∪ U s kmid t) := by
          unfold deltaStep; rw [if_pos htj, Nat.add_sub_cancel]
        have hdisj : Disjoint (U s kmid t) (s.sm (t + 1) \ (s.sp t ∪ U s kmid t)) := by
          rw [Finset.disjoint_left]; intro x hx hx'
          simp only [mem_sdiff, mem_union] at hx'
          exact hx'.2 (Or.inr hx)
        have hρU : rhoSet I (U s kmid (t + 1)) =
            rhoSet I (U s kmid t) + rhoSet I (s.sm (t + 1) \ (s.sp t ∪ U s kmid t)) := by
          rw [hU, hd]; unfold rhoSet; rw [Finset.sum_union hdisj]
        rcases Nat.eq_zero_or_pos t with h0 | hpos
        · -- t + 1 = 1: Δ_1 = S⁻_1
          subst h0
          have hU0 : U s kmid 0 = ∅ := rfl
          have hsp0 : s.sp 0 = ∅ := by unfold DPSeq.sp; simp
          rw [hρU, hU0, hsp0]
          simp only [union_empty, sdiff_empty]
          have := hρnn (s.sm (0 + 1))
          have h0' : rhoSet I (∅ : Finset (Fin n)) = 0 := by simp [rhoSet]
          rw [h0']; nlinarith
        · have ih' := ih hpos (by omega)
          have hUt := key t hpos (by omega)
          rw [Finset.union_eq_left.mpr hUt] at hρU
          have hFT := htr (t + 1) (by omega) (by omega)
          simp only [FeasibleTransition, Nat.add_sub_cancel] at hFT
          obtain ⟨⟨h8a, h8b⟩, h9, _, _, h12, _, _⟩ := hFT
          -- (38): ρ(S⁻_{t+1} \ S⁺_t) ≥ ρ(S⁻_{t+1}) − ρ(S⁻_t) − ρ(S⁺_t \ S⁻_t)
          have hcov : s.sm (t + 1) ⊆ (s.sm (t + 1) \ s.sp t) ∪ (s.sm t ∪ (s.sp t \ s.sm t)) := by
            intro x hx
            simp only [mem_union, mem_sdiff]
            by_cases h1 : x ∈ s.sp t
            · by_cases h2 : x ∈ s.sm t
              · exact Or.inr (Or.inl h2)
              · exact Or.inr (Or.inr ⟨h1, h2⟩)
            · exact Or.inl ⟨hx, h1⟩
          have h38 := (RRBL52.rhoSet_mono I hr hw hcov).trans
            ((RRBL52.rhoSet_union_le I hr hw _ _).trans
              (add_le_add_right (RRBL52.rhoSet_union_le I hr hw _ _) _))
          -- (12) ⇒ ρ(S⁻_{t+1}) ≥ (1 + ε/2) ρ(S⁻_t)
          have hevt : s.ev (t + 1) ≤ kmid := by
            rw [hev _ (by omega) (by omega)]; exact hle_kmid _ (by omega) htj
          have h12' := h12 hevt
          have hW := RRBL52.wt_mono I hw h8b
          have hWnn : 0 ≤ wt I (s.sp t) := Finset.sum_nonneg (fun i _ => (hw i).le)
          unfold alpha at h12'
          set a := rhoSet I (s.sm t)
          set b := rhoSet I (s.sm (t + 1))
          set W := wt I (s.sp t)
          set W' := wt I (s.sp (t + 1))
          have hpos1 : 0 < 1 + W := by linarith
          have hpos2 : 0 < 1 + W' := by linarith
          have ha := hρnn (s.sm t)
          have hgrow : (1 + ε / 2) * a ≤ b := by
            rw [← mul_div_assoc, div_le_div_iff₀ hpos1 hpos2] at h12'
            have : (1 + ε / 2) * a * (1 + W) ≤ (1 + ε / 2) * a * (1 + W') :=
              mul_le_mul_of_nonneg_left (by linarith) (by nlinarith)
            nlinarith
          rw [hρU]
          nlinarith
    exact main j hj1 hj
  · -- j > j_mid: S⁺_j ⊆ U_j
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hsub : s.sp (i + 1) ⊆ U s kmid (i + 1) := by
      show s.sp (i + 1) ⊆ U s kmid i ∪ deltaStep s kmid (i + 1) (U s kmid i)
      unfold deltaStep
      rw [if_neg hj]
      intro x hx
      by_cases h : x ∈ U s kmid i
      · exact mem_union_left _ h
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hx, h⟩)
    have h1 := RRBL52.rhoSet_mono I hr hw ((hsmsp (i + 1) hj1 hjT).trans hsub)
    have := hρnn (s.sm (i + 1))
    nlinarith
