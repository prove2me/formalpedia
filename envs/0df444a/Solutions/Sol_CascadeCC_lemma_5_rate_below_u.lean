-- Prove2me | solution 1 for CascadeCC.lemma_5_rate_below_u
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:26:13.600329+00:00
-- url     : https://prove2.me/submissions/3bbea8ef-4b06-4107-861c-0584c98d25c1

import Mathlib
import Definitions.Def_CascadeCC_Analysis

namespace Aux_Cascade_l5
open CascadeCC

variable {J : ℕ}

theorem arr_zero (M : Instance J) (a : Fin J → ℝ) (hJ : 0 < J) : arrival M a ⟨0, hJ⟩ = M.lam := by
  unfold arrival
  rw [Finset.filter_false_of_mem (fun i _ => by simp [Fin.lt_iff_val_lt_val])]
  simp

theorem arr_succ (M : Instance J) (a : Fin J → ℝ) (k : ℕ) (hk : k + 1 < J) :
    arrival M a ⟨k + 1, hk⟩ = arrival M a ⟨k, by omega⟩ * ((1 - a ⟨k, by omega⟩) * M.zeta ⟨k, by omega⟩) := by
  unfold arrival
  have : Finset.univ.filter (fun i : Fin J => i < ⟨k + 1, hk⟩) =
      insert ⟨k, by omega⟩ (Finset.univ.filter (fun i : Fin J => i < ⟨k, by omega⟩)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.lt_iff_val_lt_val, Fin.ext_iff]; omega
  rw [this, Finset.prod_insert (by simp)]
  ring

theorem arr_nonneg (M : Instance J) (a : Fin J → ℝ) (ha : ∀ j, a j ∈ Set.Icc 0 M.u) (k : Fin J) :
    0 ≤ arrival M a k := by
  unfold arrival
  apply mul_nonneg M.lam_mem.1
  apply Finset.prod_nonneg
  intro i _
  apply mul_nonneg
  · linarith [(ha i).2, M.u_mem.2]
  · exact (M.zeta_mem i).1.le

theorem price_pos (M : Instance J) (j : Fin J) (x : ℝ) (hx0 : 0 < x) (hxu : x < M.u) :
    0 < M.price j x := by
  have := M.price_anti j ⟨hx0, hxu.le⟩ ⟨lt_trans hx0 hxu, le_refl _⟩ hxu
  rw [M.price_u] at this
  exact this

end Aux_Cascade_l5

open CascadeCC Aux_Cascade_l5 in
theorem solution {J : ℕ} (M : Instance J) (hlam : 0 < M.lam) (T : ℕ) (hT : 0 < T)
    (y : Fin J → ℝ) (hy : ∀ j, 0 < y j) (a : Fin J → ℝ) (ha : IsStationaryOptimal M T y a) :
    ∀ j, a j < M.u := by
  classical
  by_contra hcon
  push_neg at hcon
  -- minimal index with a = u
  have hex : ∃ j : Fin J, a j = M.u := by
    obtain ⟨j, hj⟩ := hcon
    exact ⟨j, le_antisymm (ha.1 j).2 hj⟩
  obtain ⟨j0, hj0, hmin⟩ : ∃ j0 : Fin J, a j0 = M.u ∧ ∀ i : Fin J, i < j0 → a i < M.u := by
    obtain ⟨j0, hj0, hmin⟩ := (Finset.univ.filter (fun j => a j = M.u)).exists_min_image
      (fun j => j.val) (by obtain ⟨j, hj⟩ := hex; exact ⟨j, by simp [hj]⟩)
    refine ⟨j0, (Finset.mem_filter.mp hj0).2, fun i hi => ?_⟩
    rcases (ha.1 i).2.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hmin i (by simp [h])
      exact absurd hi (not_lt.mpr (Fin.le_iff_val_le_val.mpr this))
  have hu := M.u_mem
  set b := M.u / 2 with hb
  have hb0 : 0 < b := by rw [hb]; linarith [hu.1]
  have hbu : b < M.u := by rw [hb]; linarith [hu.1]
  have hA0pos : 0 < arrival M a j0 := by
    unfold arrival
    apply mul_pos hlam
    apply Finset.prod_pos
    intro i hi
    have hi' : i < j0 := (Finset.mem_filter.mp hi).2
    apply mul_pos
    · linarith [hmin i hi', hu.2]
    · exact (M.zeta_mem i).1
  -- target purchases
  set v : Fin J → ℝ := fun k => if k = j0 then arrival M a j0 * b else purchase M a k with hv
  set A' : ℕ → ℝ := hatArrival M v with hA'
  have hA'0 : A' 0 = M.lam := rfl
  have hA'succ : ∀ k (hk : k < J), A' (k + 1) = M.zeta ⟨k, hk⟩ * (A' k - v ⟨k, hk⟩) := by
    intro k hk; show hatArrival M v (k + 1) = _; simp only [hatArrival, dif_pos hk]; rfl
  have hAnn := arr_nonneg M a ha.1
  -- invariant: A' ≥ arrival a
  have hinv : ∀ k (hk : k < J), arrival M a ⟨k, hk⟩ ≤ A' k := by
    intro k
    induction k with
    | zero => intro hk; rw [arr_zero M a hk, hA'0]
    | succ k ih =>
      intro hk
      rw [arr_succ M a k hk, hA'succ k (by omega)]
      have h1 := ih (by omega)
      have hz := (M.zeta_mem ⟨k, by omega⟩).1
      have hdiff : arrival M a ⟨k, by omega⟩ * (1 - a ⟨k, by omega⟩) ≤ A' k - v ⟨k, by omega⟩ := by
        rw [hv]
        simp only
        by_cases hk0 : (⟨k, by omega⟩ : Fin J) = j0
        · rw [if_pos hk0]
          rw [← hk0] at hj0 ⊢
          rw [hj0]
          have := hAnn ⟨k, by omega⟩
          nlinarith
        · rw [if_neg hk0]
          unfold purchase
          linarith
      nlinarith
  -- new rates
  set a' : Fin J → ℝ := fun k => if A' k.val = 0 then 0 else v k / A' k.val with ha'
  have hv0 : ∀ k : Fin J, A' k.val = 0 → v k = 0 := by
    intro k hk
    have h1 := hinv k.val k.2
    have h2 := hAnn k
    have hA : arrival M a k = 0 := le_antisymm (by simpa [hk] using h1) h2
    rw [hv]; simp only
    by_cases hk0 : k = j0
    · subst hk0; rw [if_pos rfl, hA, zero_mul]
    · rw [if_neg hk0]; unfold purchase; rw [hA, zero_mul]
  have harr' : ∀ k (hk : k < J), arrival M a' ⟨k, hk⟩ = A' k := by
    intro k
    induction k with
    | zero => intro hk; rw [arr_zero M a' hk, hA'0]
    | succ k ih =>
      intro hk
      rw [arr_succ M a' k hk, ih (by omega), hA'succ k (by omega)]
      rw [ha']; simp only
      by_cases h0 : A' k = 0
      · rw [if_pos h0, h0, hv0 ⟨k, by omega⟩ h0]; ring
      · rw [if_neg h0]; field_simp
  have hpur' : ∀ k : Fin J, purchase M a' k = v k := by
    intro k
    unfold purchase
    rw [show k = ⟨k.val, k.2⟩ from rfl, harr' k.val k.2]
    rw [ha']; simp only
    by_cases h0 : A' k.val = 0
    · rw [if_pos h0, h0, hv0 k h0, zero_mul]
    · rw [if_neg h0]; field_simp
  -- rates of a' compared with a
  have hrate : ∀ k : Fin J, k ≠ j0 → 0 ≤ a' k ∧ a' k ≤ a k := by
    intro k hk
    rw [ha']; simp only
    by_cases h0 : A' k.val = 0
    · rw [if_pos h0]; exact ⟨le_refl _, (ha.1 k).1⟩
    · rw [if_neg h0]
      have hApos : 0 < A' k.val := lt_of_le_of_ne (le_trans (hAnn k) (hinv k.val k.2)) (Ne.symm h0)
      have hvk : v k = arrival M a k * a k := by rw [hv]; simp only; rw [if_neg hk]; rfl
      rw [hvk]
      constructor
      · exact div_nonneg (mul_nonneg (hAnn k) (ha.1 k).1) hApos.le
      · rw [div_le_iff₀ hApos]
        have := hinv k.val k.2
        have := (ha.1 k).1
        nlinarith
  have heqA : ∀ k (hk : k < J), k ≤ j0.val → A' k = arrival M a ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk _; rw [arr_zero M a hk, hA'0]
    | succ k ih =>
      intro hk hkj
      rw [hA'succ k (by omega), ih (by omega) (by omega), arr_succ M a k hk]
      have hne : (⟨k, by omega⟩ : Fin J) ≠ j0 := by
        intro h; rw [← h] at hkj; simp at hkj
      rw [hv]; simp only; rw [if_neg hne]; unfold purchase; ring
  have hA'j0 : A' j0.val = arrival M a j0 := heqA j0.val j0.2 le_rfl
  have ha'j0 : a' j0 = b := by
    rw [ha']; simp only
    rw [if_neg (by rw [hA'j0]; exact hA0pos.ne'), hA'j0]
    rw [hv]; simp only; rw [if_pos trivial]; field_simp
  have hvj0 : v j0 = arrival M a j0 * b := by rw [hv]; simp only; rw [if_pos trivial]
  have hvk : ∀ k, k ≠ j0 → v k = purchase M a k := by
    intro k hk; rw [hv]; simp only; rw [if_neg hk]
  -- feasibility of the constant plan a'
  have hfeas : Feasible M T y (fun _ => a') := by
    refine ⟨fun _ k => ?_, fun k => ?_⟩
    · show a' k ∈ Set.Icc 0 M.u
      by_cases hk : k = j0
      · rw [hk, ha'j0]; exact ⟨hb0.le, hbu.le⟩
      · obtain ⟨h1, h2⟩ := hrate k hk
        exact ⟨h1, h2.trans (ha.1 k).2⟩
    · simp only [hpur', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      by_cases hk : k = j0
      · rw [hk, hvj0]
        have h1 := ha.2.1 j0
        unfold purchase at h1
        rw [hj0] at h1
        have : (T : ℝ) * (arrival M a j0 * b) ≤ (T : ℝ) * (arrival M a j0 * M.u) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg T)
          exact mul_le_mul_of_nonneg_left hbu.le hA0pos.le
        linarith
      · rw [hvk k hk]; exact ha.2.1 k
  have hobj := ha.2.2 (fun _ => a') hfeas
  have hdet : detObjective M T (fun _ => a') = (T : ℝ) * statObjective M a' := by
    unfold detObjective statObjective
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hdet] at hobj
  have hstat' : statObjective M a' = ∑ k, v k * M.price k (a' k) := by
    unfold statObjective Instance.r
    apply Finset.sum_congr rfl
    intro k _
    rw [← hpur' k]; unfold purchase; ring
  have hstat : statObjective M a = ∑ k, purchase M a k * M.price k (a k) := by
    unfold statObjective Instance.r
    apply Finset.sum_congr rfl
    intro k _
    unfold purchase; ring
  have hlt : statObjective M a < statObjective M a' := by
    rw [hstat, hstat']
    apply Finset.sum_lt_sum
    · intro k _
      by_cases hk : k = j0
      · rw [hk, hvj0, hj0, M.price_u, mul_zero, ha'j0]
        have := price_pos M j0 b hb0 hbu
        positivity
      · rw [hvk k hk]
        have hPnn : 0 ≤ purchase M a k := mul_nonneg (hAnn k) (ha.1 k).1
        rcases hPnn.lt_or_eq with hP | hP
        · apply mul_le_mul_of_nonneg_left _ hPnn
          have hak : 0 < a k := by
            by_contra h; push_neg at h
            have : a k = 0 := le_antisymm h (ha.1 k).1
            unfold purchase at hP; rw [this, mul_zero] at hP; exact lt_irrefl _ hP
          have hAk : 0 < arrival M a k := by
            rcases (hAnn k).lt_or_eq with h | h
            · exact h
            · exfalso; unfold purchase at hP; rw [← h, zero_mul] at hP; exact lt_irrefl _ hP
          have hApos : 0 < A' k.val := lt_of_lt_of_le hAk (hinv k.val k.2)
          have ha'pos : 0 < a' k := by
            rw [ha']; simp only; rw [if_neg hApos.ne', hvk k hk]; exact div_pos hP hApos
          obtain ⟨_, hle⟩ := hrate k hk
          exact (M.price_anti k).antitoneOn ⟨ha'pos, hle.trans (ha.1 k).2⟩ ⟨hak, (ha.1 k).2⟩ hle
        · rw [← hP]; simp
    · refine ⟨j0, Finset.mem_univ _, ?_⟩
      rw [hvj0, hj0, M.price_u, mul_zero, ha'j0]
      have := price_pos M j0 b hb0 hbu
      positivity
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  nlinarith
