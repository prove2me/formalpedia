-- Prove2me | solution 1 for CorrClusterExp.IBR.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:32:21.818135+00:00
-- url     : https://prove2.me/submissions/da101a77-71c8-49ea-8f61-7fede45812d4

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting
import Theorems.Thm_CorrClusterExp_IBR_eq_13
import Theorems.Thm_CorrClusterExp_IBR_lemma_4_2

open CorrClusterExp.IBR Matrix Finset

lemma l43_bdd {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    BddAbove ((fun y => y ⬝ᵥ (S *ᵥ y)) '' box w) := by
  have hbox : box w = Set.pi Set.univ (fun i => Set.Icc 0 (w i)) := by
    ext y; simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc]; exact Iff.rfl
  have hc : IsCompact (box w) := by
    rw [hbox]; exact isCompact_univ_pi (fun i => isCompact_Icc)
  apply hc.bddAbove_image
  apply Continuous.continuousOn
  exact Continuous.dotProduct continuous_id (Continuous.matrix_mulVec continuous_const continuous_id)

lemma l43_wc_nonneg {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) : 0 ≤ worstCase S w := by
  unfold worstCase
  apply le_csSup (l43_bdd S w)
  refine ⟨0, fun i => ⟨le_refl _, hw0 i⟩, ?_⟩
  simp

lemma l43_Vk_nonneg (q : ℝ) (k : ℕ) {n : ℕ} (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) :
    0 ≤ Vk q k w := by
  unfold Vk
  exact Real.iInf_nonneg (fun c => l43_wc_nonneg _ w hw0)

/-- Block-counting bound: for an antitone nonnegative `v : ℕ → ℝ` and `k ≥ 1`,
`k · ∑_{h ≤ N} v(hk)² ≤ k·v(0)² + ∑_{j < Nk} v(j+1)²`. -/
lemma l43_block (v : ℕ → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hv : Antitone v) (k : ℕ) :
    ∀ N : ℕ, (k : ℝ) * ∑ h ∈ range (N + 1), v (h * k) ^ 2 ≤
      k * v 0 ^ 2 + ∑ j ∈ range (N * k), v (j + 1) ^ 2 := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    have e1 : ∑ h ∈ range (N + 1 + 1), v (h * k) ^ 2 =
        ∑ h ∈ range (N + 1), v (h * k) ^ 2 + v ((N + 1) * k) ^ 2 := Finset.sum_range_succ _ _
    have e2 : ∑ j ∈ range ((N + 1) * k), v (j + 1) ^ 2 =
        ∑ j ∈ range (N * k), v (j + 1) ^ 2 + ∑ t ∈ range k, v (N * k + t + 1) ^ 2 := by
      rw [show (N + 1) * k = N * k + k by ring, Finset.sum_range_add]
    rw [e1, e2, mul_add]
    have hstep : (k : ℝ) * v ((N + 1) * k) ^ 2 ≤ ∑ t ∈ range k, v (N * k + t + 1) ^ 2 := by
      have : ∀ t ∈ range k, v ((N + 1) * k) ^ 2 ≤ v (N * k + t + 1) ^ 2 := by
        intro t ht
        rw [Finset.mem_range] at ht
        have h1 : v ((N + 1) * k) ≤ v (N * k + t + 1) := hv (by nlinarith)
        have h2 := hv0 ((N + 1) * k)
        nlinarith
      have := Finset.sum_le_sum this
      simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
    have : ∑ t ∈ range k, v (N * k + t + 1) ^ 2 = ∑ x ∈ range k, v (N * k + x + 1) ^ 2 := rfl
    linarith

lemma l43_comb (n : ℕ) (hn : 0 < n) (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w)
    (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * ∑ i ∈ univ.filter (fun i : Fin n => k ∣ i.val), w i ^ 2 ≤
      ((k : ℝ) - 1) * w ⟨0, hn⟩ ^ 2 + ∑ i, w i ^ 2 := by
  set v : ℕ → ℝ := fun i => if h : i < n then w ⟨i, h⟩ else 0 with hvdef
  have hv0 : ∀ i, 0 ≤ v i := by
    intro i; simp only [hvdef]; split_ifs
    · exact hw0 _
    · exact le_refl _
  have hv : Antitone v := by
    intro a b hab
    simp only [hvdef]
    by_cases hb : b < n
    · rw [dif_pos hb, dif_pos (lt_of_le_of_lt hab hb)]
      exact hw (Fin.mk_le_mk.2 hab)
    · rw [dif_neg hb]; split_ifs
      · exact hw0 _
      · exact le_refl _
  have hvw : ∀ i : Fin n, v i.val = w i := by
    intro i; simp [hvdef, i.isLt]
  have hvz : ∀ i, n ≤ i → v i = 0 := by
    intro i hi; simp [hvdef, not_lt.2 hi]
  -- total sum
  have hS : ∀ M, n ≤ M → ∑ i, w i ^ 2 = ∑ j ∈ range M, v j ^ 2 := by
    intro M hM
    rw [show ∑ i, w i ^ 2 = ∑ i : Fin n, v i.val ^ 2 by simp [hvw], Fin.sum_univ_eq_sum_range
      (fun j => v j ^ 2)]
    rw [← Finset.sum_range_add_sum_Ico _ hM]
    have : ∑ j ∈ Ico n M, v j ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_Ico] at hj
      rw [hvz j hj.1]; ring
    rw [this, add_zero]
  -- divisible sum
  have hD : ∑ i ∈ univ.filter (fun i : Fin n => k ∣ i.val), w i ^ 2 =
      ∑ h ∈ range (n + 1), v (h * k) ^ 2 := by
    rw [Finset.sum_filter]
    rw [show (∑ i : Fin n, if k ∣ i.val then w i ^ 2 else 0) =
      ∑ i : Fin n, (fun j : ℕ => if k ∣ j then v j ^ 2 else 0) i.val by
        apply Finset.sum_congr rfl; intro i _; simp [hvw]]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if k ∣ j then v j ^ 2 else 0), ← Finset.sum_filter]
    rw [← Finset.sum_filter_add_sum_filter_not (range (n + 1)) (fun h => h * k < n)]
    have hz : ∑ h ∈ (range (n + 1)).filter (fun h => ¬ h * k < n), v (h * k) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro h hh
      rw [Finset.mem_filter] at hh
      rw [hvz _ (not_lt.1 hh.2)]; ring
    rw [hz, add_zero]
    apply Finset.sum_nbij' (fun i => i / k) (fun h => h * k)
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi ⊢
      obtain ⟨hi1, c, rfl⟩ := hi
      have hkpos : 0 < k := hk
      rw [Nat.mul_div_cancel_left c hkpos]
      refine ⟨?_, ?_⟩
      · have : c ≤ k * c := Nat.le_mul_of_pos_left c hkpos
        omega
      · rw [mul_comm]; exact hi1
    · intro h hh
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hh ⊢
      exact ⟨hh.2, Dvd.intro_left h rfl⟩
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
      exact Nat.div_mul_cancel hi.2
    · intro h _
      exact Nat.mul_div_cancel h hk
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
      rw [Nat.div_mul_cancel hi.2]
  have hblk := l43_block v hv0 hv k n
  have hM : n ≤ n * k + 1 := by nlinarith
  have hS' := hS (n * k + 1) hM
  rw [Finset.sum_range_succ'] at hS'
  have h00 : v 0 = w ⟨0, hn⟩ := hvw ⟨0, hn⟩
  rw [hD, hS']
  rw [h00] at hblk ⊢
  linarith

theorem solution (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (hn : 0 < n) (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w)
    (hw1 : 0 < w ⟨0, hn⟩) :
    Vk q k w / VOPT q w ≤ Vk q k w / VLB w ∧
      Vk q k w / VLB w ≤
        fq q k * (4 / k + ((k : ℝ) - 1) / k * (w ⟨0, hn⟩ ^ 2 / VLB w)) ∧
      fq q k * (4 / k + ((k : ℝ) - 1) / k * (w ⟨0, hn⟩ ^ 2 / VLB w)) ≤
        fq q k * (4 / k + ((k : ℝ) - 1) / k) := by
  have hL := lemma_4_2 q hq0 hq n hn w hw0 hw
  have ha2 : 0 < w ⟨0, hn⟩ ^ 2 := by positivity
  have hL1 : w ⟨0, hn⟩ ^ 2 ≤ VLB w := le_trans (le_max_left _ _) hL.1
  have hL2 : 1 / 4 * ∑ i, w i ^ 2 ≤ VLB w := le_trans (le_max_right _ _) hL.1
  have hLpos : 0 < VLB w := lt_of_lt_of_le ha2 hL1
  have hVk0 := l43_Vk_nonneg q k w hw0
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hfq0 : 0 ≤ fq q k := by
    have h := lemma_4_2 q hq0 hq k hk (fun _ : Fin k => (1 : ℝ)) (fun _ => zero_le_one)
      (fun _ _ _ => le_refl _)
    unfold fq
    have : (0 : ℝ) ≤ max ((1 : ℝ) ^ 2) (1 / 4 * ∑ _i : Fin k, (1 : ℝ) ^ 2) :=
      le_trans zero_le_one (by simp)
    linarith [h.1, h.2.1]
  refine ⟨div_le_div_of_nonneg_left hVk0 hLpos hL.2.1, ?_, ?_⟩
  · have h13 := eq_13 q hq0 hq k hk n w hw0 hw
    have hc := l43_comb n hn w hw0 hw k hk
    set Sk := ∑ i ∈ univ.filter (fun i : Fin n => k ∣ i.val), w i ^ 2
    set S := ∑ i, w i ^ 2
    set L := VLB w
    set a := w ⟨0, hn⟩ ^ 2
    have hSk : Sk ≤ ((k : ℝ) - 1) / k * a + 1 / k * S := by
      rw [show ((k : ℝ) - 1) / k * a + 1 / k * S = (((k : ℝ) - 1) * a + S) / k by ring,
        le_div_iff₀ hkpos]
      linarith
    have hSL : 1 / (k : ℝ) * S / L ≤ 4 / k := by
      rw [div_le_iff₀ hLpos]
      have : S ≤ 4 * L := by linarith
      have : 1 / (k : ℝ) * S ≤ 1 / k * (4 * L) := by
        apply mul_le_mul_of_nonneg_left this; positivity
      calc 1 / (k : ℝ) * S ≤ 1 / k * (4 * L) := this
        _ = 4 / k * L := by ring
    have hbound : Sk / L ≤ 4 / k + ((k : ℝ) - 1) / k * (a / L) := by
      have : Sk / L ≤ (((k : ℝ) - 1) / k * a + 1 / k * S) / L :=
        div_le_div_of_nonneg_right hSk hLpos.le
      have e : (((k : ℝ) - 1) / k * a + 1 / k * S) / L =
          ((k : ℝ) - 1) / k * (a / L) + 1 / k * S / L := by ring
      linarith
    calc Vk q k w / L ≤ fq q k * Sk / L := div_le_div_of_nonneg_right h13 hLpos.le
      _ = fq q k * (Sk / L) := by ring
      _ ≤ fq q k * (4 / k + ((k : ℝ) - 1) / k * (a / L)) :=
          mul_le_mul_of_nonneg_left hbound hfq0
  · apply mul_le_mul_of_nonneg_left _ hfq0
    have h1 : w ⟨0, hn⟩ ^ 2 / VLB w ≤ 1 := (div_le_one hLpos).2 hL1
    have h2 : 0 ≤ ((k : ℝ) - 1) / k := div_nonneg (by linarith) hkpos.le
    have : ((k : ℝ) - 1) / k * (w ⟨0, hn⟩ ^ 2 / VLB w) ≤ ((k : ℝ) - 1) / k * 1 :=
      mul_le_mul_of_nonneg_left h1 h2
    linarith
