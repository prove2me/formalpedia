-- Prove2me | solution 1 for ConstrNestedLogit.Space.ratio_inequality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:40:44.295309+00:00
-- url     : https://prove2.me/submissions/9b4e8246-83eb-4844-ba6d-07691cc30b8d

import Mathlib
import Definitions.Def_ConstrNestedLogit_Space_Model

set_option autoImplicit false
open ConstrNestedLogit.Space

lemma yb_sum_single {n : ℕ} (f : Fin n → ℝ) (j : Fin n) (c : ℝ) :
    ∑ m, f m * (c * (Pi.single j (1 : ℝ) : Fin n → ℝ) m) = c * f j := by
  simp [Pi.single_apply, mul_comm]

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ k, 0 < I.v i k)
    (hw : ∀ k, 0 < w i k) (hwc : ∀ k, w i k ≤ c i)
    (u : ℝ) (hu : 0 ≤ u) (x : Fin n → ℝ)
    (hx : spaceLPOptimal I w c i u x) (j : Fin n)
    (hj : oneFractional x j) :
    utilityRatio I w i u j * (∑ k ∈ rounded x, w i k) ≤
      assortmentUtility I i u (rounded x) := by
  obtain ⟨⟨hbox, hcap⟩, hopt⟩ := hx
  obtain ⟨hj0, hj1, hrest⟩ := hj
  have hkey : ∀ k ∈ rounded x, utilityRatio I w i u j * w i k ≤ utility I i u k := by
    intro k hk
    have hxk : x k = 1 := by unfold rounded at hk; simpa using hk
    have hkj : k ≠ j := by
      rintro rfl; rw [hxk] at hj1; exact lt_irrefl _ hj1
    by_contra hcon
    push Not at hcon
    have hwk := hw k
    have hwj := hw j
    unfold utilityRatio at hcon
    -- hcon : utility k < (utility j / w j) * w k
    set ε := min (w i k) (w i j * (1 - x j)) with hε
    have hεpos : 0 < ε := lt_min hwk (mul_pos hwj (by linarith))
    have hε1 : ε ≤ w i k := min_le_left _ _
    have hε2 : ε ≤ w i j * (1 - x j) := min_le_right _ _
    set y : Fin n → ℝ := fun m => x m + (ε / w i j) * (Pi.single j (1 : ℝ) : Fin n → ℝ) m
        - (ε / w i k) * (Pi.single k (1 : ℝ) : Fin n → ℝ) m with hy
    have hyfeas : knapsackLPFeasible (w i) (c i) y := by
      refine ⟨fun m => ?_, ?_⟩
      · have hym : y m = x m + (if m = j then ε / w i j else 0) - (if m = k then ε / w i k else 0) := by
          simp only [hy, Pi.single_apply]
          split_ifs <;> simp
        by_cases hmj : m = j
        · have hmk : ¬ m = k := fun h => hkj (h.symm.trans hmj)
          rw [if_pos hmj, if_neg hmk] at hym
          have h3 : ε / w i j ≤ 1 - x j := by rw [div_le_iff₀ hwj]; linarith
          have h4 : 0 < ε / w i j := div_pos hεpos hwj
          rw [hmj] at hym ⊢
          constructor <;> linarith [hbox j]
        · by_cases hmk : m = k
          · rw [if_neg hmj, if_pos hmk] at hym
            have h3 : ε / w i k ≤ 1 := by rw [div_le_one hwk]; exact hε1
            have h4 : 0 < ε / w i k := div_pos hεpos hwk
            rw [hmk] at hym ⊢
            rw [hxk] at hym
            constructor <;> linarith
          · rw [if_neg hmj, if_neg hmk] at hym
            rw [hym]; simpa using hbox m
      · have : ∑ m, w i m * y m = ∑ m, w i m * x m := by
          have e : ∀ m, w i m * y m = w i m * x m + w i m * ((ε / w i j) * (Pi.single j (1 : ℝ) : Fin n → ℝ) m)
              - w i m * ((ε / w i k) * (Pi.single k (1 : ℝ) : Fin n → ℝ) m) := by
            intro m; simp only [hy]; ring
          rw [Finset.sum_congr rfl fun m _ => e m, Finset.sum_sub_distrib, Finset.sum_add_distrib,
            yb_sum_single, yb_sum_single]
          field_simp
          ring
        rw [this]; exact hcap
    have hle := hopt y hyfeas
    unfold knapsackLPObjective at hle
    have hobj : ∑ m, utility I i u m * y m = ∑ m, utility I i u m * x m
        + (ε / w i j) * utility I i u j - (ε / w i k) * utility I i u k := by
      have e : ∀ m, utility I i u m * y m = utility I i u m * x m
          + utility I i u m * ((ε / w i j) * (Pi.single j (1 : ℝ) : Fin n → ℝ) m)
          - utility I i u m * ((ε / w i k) * (Pi.single k (1 : ℝ) : Fin n → ℝ) m) := by
        intro m; simp only [hy]; ring
      rw [Finset.sum_congr rfl fun m _ => e m, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        yb_sum_single, yb_sum_single]
    rw [hobj] at hle
    -- contradiction: ε u_j / w_j > ε u_k / w_k
    have h1 : (ε / w i k) * utility I i u k < (ε / w i k) * (utility I i u j / w i j * w i k) :=
      mul_lt_mul_of_pos_left hcon (div_pos hεpos hwk)
    have h2 : (ε / w i k) * (utility I i u j / w i j * w i k) = (ε / w i j) * utility I i u j := by
      field_simp
    linarith
  unfold assortmentUtility
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum hkey
