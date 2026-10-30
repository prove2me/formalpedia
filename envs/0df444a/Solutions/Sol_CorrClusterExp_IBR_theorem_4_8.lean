-- Prove2me | solution 1 for CorrClusterExp.IBR.theorem_4_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:29:26.840414+00:00
-- url     : https://prove2.me/submissions/e61e8af2-03d7-408c-a63d-c9195b30b5e4

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting
import Theorems.Thm_CorrClusterExp_IBR_lemma_4_3
import Theorems.Thm_CorrClusterExp_IBR_lemma_4_2
import Theorems.Thm_CorrClusterExp_IBR_lemma_4_7
import Theorems.Thm_CorrClusterExp_IBR_ibr_additivity

open CorrClusterExp.IBR Matrix Finset

/-- The worst case over the box is attained-bounded: the image is bounded above. -/
lemma t48_bdd {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    BddAbove ((fun y => y ⬝ᵥ (S *ᵥ y)) '' box w) := by
  have hbox : box w = Set.pi Set.univ (fun i => Set.Icc 0 (w i)) := by
    ext y; simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc]; exact Iff.rfl
  have hc : IsCompact (box w) := by
    rw [hbox]; exact isCompact_univ_pi (fun i => isCompact_Icc)
  apply hc.bddAbove_image
  apply Continuous.continuousOn
  exact Continuous.dotProduct continuous_id (Continuous.matrix_mulVec continuous_const continuous_id)

lemma t48_wc_nonneg {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) : 0 ≤ worstCase S w := by
  unfold worstCase
  apply le_csSup (t48_bdd S w)
  refine ⟨0, fun i => ⟨le_refl _, hw0 i⟩, ?_⟩
  simp

lemma t48_VOPT_le_VDP (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) {n : ℕ} (w : Fin n → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) : VOPT q w ≤ VDP q w := by
  obtain ⟨c, hc⟩ := exists_eq_ciInf_of_finite (f := fun c : Composition n => VIBR q w c)
  unfold VDP
  rw [← hc]
  unfold VOPT VIBR
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro x ⟨P, -, rfl⟩
    exact t48_wc_nonneg _ w hw0
  · exact ⟨ibrLaw q c, (ibr_additivity q hq0 hq n c w hw0).1, rfl⟩

lemma t48_VDP_le_Vk (q : ℝ) (k : ℕ) {n : ℕ} (w : Fin n → ℝ) : VDP q w ≤ Vk q k w := by
  unfold Vk
  have : Nonempty {c : Composition n // KGrouped k c} := by
    refine ⟨⟨Composition.ones n, ?_⟩⟩
    intro h hh
    exact ⟨h * k, by rw [Composition.ones_sizeUpTo]; omega⟩
  apply le_ciInf
  intro c
  unfold VDP
  exact ciInf_le (Finite.bddBelow_range _) c.1

/-- Part 1 of Theorem 4.8 with an explicit constant. -/
lemma t48_rate (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (C' : ℝ) (hC' : 0 ≤ C')
    (hfq : ∀ k : ℕ, 1 ≤ k → fq q k ≤ 1 / 4 * ((k : ℝ) + C'))
    (n : ℕ) (hn : 0 < n) (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w)
    (hw1 : 0 < w ⟨0, hn⟩) :
    (VDP q w - VLB w) / VLB w ≤ (2 * C' + 2) * Real.sqrt (w ⟨0, hn⟩ ^ 2 / ∑ i, w i ^ 2) := by
  set a := w ⟨0, hn⟩ with ha
  set S := ∑ i, w i ^ 2 with hS
  have hL := lemma_4_2 q hq0 hq n hn w hw0 hw
  set L := VLB w with hLdef
  have ha2 : 0 < a ^ 2 := by positivity
  have haS : a ^ 2 ≤ S := by
    rw [hS]
    exact Finset.single_le_sum (f := fun i => w i ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ _)
  have hSpos : 0 < S := lt_of_lt_of_le ha2 haS
  have hL1 : a ^ 2 ≤ L := le_trans (le_max_left _ _) hL.1
  have hL2 : 1 / 4 * S ≤ L := le_trans (le_max_right _ _) hL.1
  have hLpos : 0 < L := lt_of_lt_of_le ha2 hL1
  set r := a ^ 2 / S with hr
  have hr0 : 0 < r := div_pos ha2 hSpos
  have hr1 : r ≤ 1 := (div_le_one hSpos).2 haS
  set s := Real.sqrt r with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hr0
  have hs1 : s ≤ 1 := Real.sqrt_le_one.mpr hr1
  have hss : s * s = r := Real.mul_self_sqrt hr0.le
  -- choose k = ⌈1/s⌉
  set k : ℕ := ⌈1 / s⌉₊ with hk
  have hk1 : 1 ≤ k := by
    rw [hk, Nat.one_le_iff_ne_zero]
    intro h0
    rw [Nat.ceil_eq_zero] at h0
    have : 0 < 1 / s := by positivity
    linarith
  have hkR1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkpos : (0 : ℝ) < k := by linarith
  have hkge : 1 / s ≤ k := Nat.le_ceil _
  have hkle : (k : ℝ) < 1 / s + 1 := Nat.ceil_lt_add_one (by positivity)
  have h1s : 1 ≤ 1 / s := by rw [le_div_iff₀ hs0]; linarith
  have hk2 : (k : ℝ) * s ≤ 2 := by
    have : (k : ℝ) ≤ 2 / s := by
      have : 1 / s + 1 ≤ 2 / s := by
        rw [show (2 : ℝ) / s = 1 / s + 1 / s by ring]; linarith
      linarith
    calc (k : ℝ) * s ≤ 2 / s * s := by gcongr
      _ = 2 := by field_simp
  have hinvk : 1 / (k : ℝ) ≤ s := by
    rw [div_le_iff₀ hkpos]
    have := mul_le_mul_of_nonneg_left hkge hs0.le
    rw [show s * (1 / s) = 1 by field_simp] at this
    linarith
  -- Lemma 4.3
  have h43 := (lemma_4_3 q hq0 hq k hk1 n hn w hw0 hw hw1).2.1
  have hfk := hfq k hk1
  -- w₁²/L ≤ 4 r
  have hb : a ^ 2 / L ≤ 4 * r := by
    rw [hr, div_le_iff₀ hLpos]
    have : 4 * (a ^ 2 / S) * L ≥ 4 * (a ^ 2 / S) * (1 / 4 * S) := by
      gcongr
    have h2 : 4 * (a ^ 2 / S) * (1 / 4 * S) = a ^ 2 := by field_simp
    linarith
  have hb0 : 0 ≤ a ^ 2 / L := by positivity
  have hfac0 : 0 ≤ 4 / (k : ℝ) + ((k : ℝ) - 1) / k * (a ^ 2 / L) := by
    have : 0 ≤ ((k : ℝ) - 1) / k := div_nonneg (by linarith) hkpos.le
    positivity
  have hfac1 : 4 / (k : ℝ) + ((k : ℝ) - 1) / k * (a ^ 2 / L) ≤ 4 / k + 4 * r := by
    have : ((k : ℝ) - 1) / k ≤ 1 := by rw [div_le_one hkpos]; linarith
    have : ((k : ℝ) - 1) / k * (a ^ 2 / L) ≤ 1 * (4 * r) := by
      apply mul_le_mul this hb hb0 (by norm_num)
    linarith
  have hVk : Vk q k w / L ≤ ((k : ℝ) + C') * (1 / k + r) := by
    calc Vk q k w / L ≤ fq q k * (4 / k + ((k : ℝ) - 1) / k * (a ^ 2 / L)) := h43
      _ ≤ 1 / 4 * ((k : ℝ) + C') * (4 / k + ((k : ℝ) - 1) / k * (a ^ 2 / L)) :=
          mul_le_mul_of_nonneg_right hfk hfac0
      _ ≤ 1 / 4 * ((k : ℝ) + C') * (4 / k + 4 * r) := by
          apply mul_le_mul_of_nonneg_left hfac1; positivity
      _ = ((k : ℝ) + C') * (1 / k + r) := by ring
  have hDP : VDP q w / L ≤ Vk q k w / L :=
    div_le_div_of_nonneg_right (t48_VDP_le_Vk q k w) hLpos.le
  have hsub : (VDP q w - L) / L = VDP q w / L - 1 := by field_simp
  rw [hsub]
  have hk' : (k : ℝ) * (1 / k) = 1 := by field_simp
  have hexp : ((k : ℝ) + C') * (1 / k + r) = 1 + C' * (1 / k) + k * r + C' * r := by
    calc ((k : ℝ) + C') * (1 / k + r) = k * (1 / k) + C' * (1 / k) + k * r + C' * r := by ring
      _ = 1 + C' * (1 / k) + k * r + C' * r := by rw [hk']
  have hkr : (k : ℝ) * r ≤ 2 * s := by
    rw [← hss]; nlinarith
  have hCr : C' * r ≤ C' * s := by
    apply mul_le_mul_of_nonneg_left _ hC'
    rw [← hss]; nlinarith
  have hCk : C' * (1 / k) ≤ C' * s := mul_le_mul_of_nonneg_left hinvk hC'
  have hfin : (2 * C' + 2) * s = 2 * (C' * s) + 2 * s := by ring
  rw [hfin]
  linarith

theorem solution (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) :
    (∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n) (w : Fin n → ℝ), (∀ i, 0 ≤ w i) → Antitone w →
        0 < w ⟨0, hn⟩ →
        (VDP q w - VLB w) / VLB w ≤ C * Real.sqrt (w ⟨0, hn⟩ ^ 2 / ∑ i, w i ^ 2)) ∧
    ∀ (N : ℕ → ℕ) (hN : ∀ m, 0 < N m) (W : ∀ m, Fin (N m) → ℝ),
      (∀ m i, 0 ≤ W m i) → (∀ m, Antitone (W m)) → (∀ m, 0 < W m ⟨0, hN m⟩) →
      Filter.Tendsto (fun m => W m ⟨0, hN m⟩ ^ 2 / ∑ i, W m i ^ 2) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun m => (VDP q (W m) - VLB (W m)) / VLB (W m)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun m => VDP q (W m) / VOPT q (W m)) Filter.atTop (nhds 1) := by
  obtain ⟨C0, hC0⟩ := lemma_4_7 q hq0 hq
  set C' := max C0 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hfq : ∀ k : ℕ, 1 ≤ k → fq q k ≤ 1 / 4 * ((k : ℝ) + C') := by
    intro k hk
    have := hC0 k hk
    have : C0 ≤ C' := le_max_left _ _
    linarith
  have hrate := t48_rate q hq0 hq C' hC'0 hfq
  refine ⟨⟨2 * C' + 2, fun n hn w hw0 hw hw1 => hrate n hn w hw0 hw hw1⟩, ?_⟩
  intro N hN W hW0 hW hW1 hT
  -- basic facts per instance
  have hLpos : ∀ m, 0 < VLB (W m) := by
    intro m
    have hL := lemma_4_2 q hq0 hq (N m) (hN m) (W m) (hW0 m) (hW m)
    have : 0 < W m ⟨0, hN m⟩ ^ 2 := by have := hW1 m; positivity
    exact lt_of_lt_of_le this (le_trans (le_max_left _ _) hL.1)
  have hLO : ∀ m, VLB (W m) ≤ VOPT q (W m) := fun m =>
    (lemma_4_2 q hq0 hq (N m) (hN m) (W m) (hW0 m) (hW m)).2.1
  have hOD : ∀ m, VOPT q (W m) ≤ VDP q (W m) := fun m => t48_VOPT_le_VDP q hq0 hq (W m) (hW0 m)
  have hupper : Filter.Tendsto (fun m => (2 * C' + 2) *
      Real.sqrt (W m ⟨0, hN m⟩ ^ 2 / ∑ i, W m i ^ 2)) Filter.atTop (nhds 0) := by
    have := (hT.sqrt).const_mul (2 * C' + 2)
    simpa using this
  have hA : Filter.Tendsto (fun m => (VDP q (W m) - VLB (W m)) / VLB (W m))
      Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro m
      apply div_nonneg _ (hLpos m).le
      linarith [hLO m, hOD m]
    · intro m
      exact hrate (N m) (hN m) (W m) (hW0 m) (hW m) (hW1 m)
  refine ⟨hA, ?_⟩
  have hB : Filter.Tendsto (fun m => 1 + (VDP q (W m) - VLB (W m)) / VLB (W m))
      Filter.atTop (nhds 1) := by
    simpa using hA.const_add 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB
  · intro m
    have hO : 0 < VOPT q (W m) := lt_of_lt_of_le (hLpos m) (hLO m)
    simp only
    rw [le_div_iff₀ hO]; linarith [hOD m]
  · intro m
    have hO : 0 < VOPT q (W m) := lt_of_lt_of_le (hLpos m) (hLO m)
    have hL := hLpos m
    simp only
    have hD : 0 ≤ VDP q (W m) := by linarith [hOD m]
    have : VDP q (W m) / VOPT q (W m) ≤ VDP q (W m) / VLB (W m) :=
      div_le_div_of_nonneg_left hD hL (hLO m)
    have h2 : 1 + (VDP q (W m) - VLB (W m)) / VLB (W m) = VDP q (W m) / VLB (W m) := by
      field_simp; ring
    linarith
