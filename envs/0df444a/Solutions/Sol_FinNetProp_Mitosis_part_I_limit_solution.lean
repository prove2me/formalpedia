-- Prove2me | solution 1 for FinNetProp.Mitosis.part_I_limit_solution
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T16:04:52.264994+00:00
-- url     : https://prove2.me/submissions/9855b55d-90fe-4ede-bbea-0ddc9e537b7f

import Mathlib
import Definitions.Def_FinNetProp_Mitosis_Setting

namespace FinNetProp.Mitosis

open Finset

lemma fnp_relLiab_nonneg (F : FinNet) (i j : ℕ) : 0 ≤ relLiab F i j := by
  unfold relLiab
  split_ifs
  · exact le_rfl
  · exact div_nonneg (F.L_nonneg i j) (Finset.sum_nonneg fun k _ => F.L_nonneg i k)

lemma fnp_rowsum_nonneg (F : FinNet) (i : ℕ) : 0 ≤ ∑ k ∈ F.N, F.L i k :=
  Finset.sum_nonneg fun k _ => F.L_nonneg i k

lemma fnp_L_eq_zero_of_rowsum (F : FinNet) (i j : ℕ) (h : ∑ k ∈ F.N, F.L i k = 0) :
    F.L i j = 0 := by
  by_cases hj : j ∈ F.N
  · exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => F.L_nonneg i k)).1 h j hj
  · exact F.L_out i j (Or.inr hj)

lemma fnp_relLiab_mul (F : FinNet) (i j : ℕ) :
    relLiab F i j * ∑ k ∈ F.N, F.L i k = F.L i j := by
  unfold relLiab
  split_ifs with h
  · simp [h]
  · have hpos : (∑ k ∈ F.N, F.L i k) ≠ 0 := by
      intro h0; exact h (fnp_L_eq_zero_of_rowsum F i j h0)
    field_simp

lemma fnp_relLiab_rowsum (F : FinNet) (i : ℕ) :
    ∑ j ∈ F.N, relLiab F i j = if ∑ k ∈ F.N, F.L i k = 0 then 0 else 1 := by
  split_ifs with h
  · apply Finset.sum_eq_zero
    intro j _
    simp [relLiab, fnp_L_eq_zero_of_rowsum F i j h]
  · have : ∀ j ∈ F.N, relLiab F i j = F.L i j / ∑ k ∈ F.N, F.L i k := by
      intro j _
      unfold relLiab
      split_ifs with hj
      · simp [hj]
      · rfl
    rw [Finset.sum_congr rfl this, ← Finset.sum_div, div_self h]

lemma fnp_relLiab_rowsum_le (F : FinNet) (i : ℕ) : ∑ j ∈ F.N, relLiab F i j ≤ 1 := by
  rw [fnp_relLiab_rowsum]; split_ifs <;> norm_num

lemma fnp_min_eq (F : FinNet) (i j : ℕ) (a : ℝ) :
    min (relLiab F i j * a) (F.L i j) = relLiab F i j * min a (∑ k ∈ F.N, F.L i k) := by
  rw [mul_min_of_nonneg _ _ (fnp_relLiab_nonneg F i j), fnp_relLiab_mul]

lemma fnp_z_nonneg (F : FinNet) (i : ℕ) : 0 ≤ F.z i := by
  by_cases h : i ∈ F.N
  · exact (F.z_pos i h).le
  · exact (F.z_out i h).ge

lemma fnp_rowtotal (F : FinNet) (P : ℕ → ℕ → ℝ) (hP : IsPropSolution F P) :
    ∀ i ∈ F.N, ∑ l ∈ F.N, P i l =
      min (F.z i + ∑ k ∈ F.N, P k i) (∑ k ∈ F.N, F.L i k) := by
  obtain ⟨⟨hnn, _, _⟩, heq⟩ := hP
  intro i hi
  have h1 : ∀ l ∈ F.N, P i l = relLiab F i l *
      min (F.z i + ∑ k ∈ F.N, P k i) (∑ k ∈ F.N, F.L i k) := by
    intro l hl; rw [heq i hi l hl, fnp_min_eq]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, fnp_relLiab_rowsum]
  split_ifs with h
  · rw [h, zero_mul]
    have : 0 ≤ F.z i + ∑ k ∈ F.N, P k i :=
      add_nonneg (fnp_z_nonneg F i) (Finset.sum_nonneg fun k _ => hnn k i)
    exact (min_eq_right this).symm
  · rw [one_mul]

open Filter Topology

theorem fnp_limit (Fs : ℕ → FinNet) (F : FinNet) (hconv : NetConverges Fs F)
    (Ps : ℕ → ℕ → ℕ → ℝ) (hPs : ∀ n, IsPropSolution (Fs n) (Ps n)) (Pbar : ℕ → ℕ → ℝ)
    (hlim : ∀ i j, Tendsto (fun n => Ps n i j) atTop (𝓝 (Pbar i j))) :
    IsPropSolution F Pbar := by
  obtain ⟨hN, hz, hL⟩ := hconv
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro i j
    exact ge_of_tendsto' (hlim i j) (fun n => (hPs n).1.1 i j)
  · intro i
    have : Tendsto (fun n => Ps n i i) atTop (𝓝 0) := by
      simp only [(hPs _).1.2.1 i]; exact tendsto_const_nhds
    exact tendsto_nhds_unique (hlim i i) this
  · intro i j h
    have : Tendsto (fun n => Ps n i j) atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hN] with n hn
      exact ((hPs n).1.2.2 i j (by rw [hn]; exact h)).symm
    exact tendsto_nhds_unique (hlim i j) this
  · intro i hi j hj
    by_cases hLij : F.L i j = 0
    · have h1 : Pbar i j ≤ 0 := by
        have hle : ∀ᶠ n in atTop, Ps n i j ≤ (Fs n).L i j := by
          filter_upwards [hN] with n hn
          rw [(hPs n).2 i (by rw [hn]; exact hi) j (by rw [hn]; exact hj)]
          exact min_le_right _ _
        have := le_of_tendsto_of_tendsto (hlim i j) (hL i j) hle
        rw [hLij] at this; exact this
      have h2 : 0 ≤ Pbar i j := ge_of_tendsto' (hlim i j) (fun n => (hPs n).1.1 i j)
      have : relLiab F i j = 0 := by simp [relLiab, hLij]
      rw [this, hLij, zero_mul, min_self]
      linarith
    · have hLpos : 0 < F.L i j := lt_of_le_of_ne (F.L_nonneg i j) (Ne.symm hLij)
      have hsumpos : 0 < ∑ k ∈ F.N, F.L i k :=
        lt_of_lt_of_le hLpos (Finset.single_le_sum (fun k _ => F.L_nonneg i k) hj)
      have hev : ∀ᶠ n in atTop, (Fs n).L i j ≠ 0 :=
        (hL i j).eventually (isOpen_ne.mem_nhds hLij)
      have hrel : Tendsto (fun n => relLiab (Fs n) i j) atTop (𝓝 (relLiab F i j)) := by
        have hsum : Tendsto (fun n => ∑ k ∈ F.N, (Fs n).L i k) atTop
            (𝓝 (∑ k ∈ F.N, F.L i k)) := tendsto_finsetSum _ fun k _ => hL i k
        have := (hL i j).div hsum hsumpos.ne'
        unfold relLiab
        rw [if_neg hLij]
        apply this.congr'
        filter_upwards [hN, hev] with n hn hne
        rw [if_neg hne, hn]; rfl
      have hA : Tendsto (fun n => (Fs n).z i + ∑ k ∈ (Fs n).N, Ps n k i) atTop
          (𝓝 (F.z i + ∑ k ∈ F.N, Pbar k i)) := by
        have h0 : Tendsto (fun n => (Fs n).z i + ∑ k ∈ F.N, Ps n k i) atTop
            (𝓝 (F.z i + ∑ k ∈ F.N, Pbar k i)) :=
          (hz i).add (tendsto_finsetSum _ fun k _ => hlim k i)
        apply h0.congr'
        filter_upwards [hN] with n hn
        rw [hn]
      have hR := (hrel.mul hA).min (hL i j)
      have hE : (fun n => Ps n i j) =ᶠ[atTop] (fun n => min (relLiab (Fs n) i j *
          ((Fs n).z i + ∑ k ∈ (Fs n).N, Ps n k i)) ((Fs n).L i j)) := by
        filter_upwards [hN] with n hn
        exact (hPs n).2 i (by rw [hn]; exact hi) j (by rw [hn]; exact hj)
      exact tendsto_nhds_unique (hlim i j) (hR.congr' hE.symm)

end FinNetProp.Mitosis

open Filter Topology in
theorem solution (Fs : ℕ → FinNetProp.Mitosis.FinNet) (F : FinNetProp.Mitosis.FinNet)
    (hconv : FinNetProp.Mitosis.NetConverges Fs F)
    (Ps : ℕ → ℕ → ℕ → ℝ) (hPs : ∀ n, FinNetProp.Mitosis.IsPropSolution (Fs n) (Ps n))
    (Pbar : ℕ → ℕ → ℝ)
    (hlim : ∀ i j, Tendsto (fun n => Ps n i j) atTop (𝓝 (Pbar i j))) :
    FinNetProp.Mitosis.IsPropSolution F Pbar :=
  FinNetProp.Mitosis.fnp_limit Fs F hconv Ps hPs Pbar hlim
