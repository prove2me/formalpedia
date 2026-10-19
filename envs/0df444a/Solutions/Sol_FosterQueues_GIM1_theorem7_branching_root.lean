-- Prove2me | solution 1 for FosterQueues.GIM1.theorem7_branching_root
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:26:15.274582+00:00
-- url     : https://prove2.me/submissions/d304cc24-c739-4bd1-a6f9-2850b2344f30

import Mathlib

set_option autoImplicit false

open scoped ENNReal

lemma fr_geom (z : ℝ) (n : ℕ) : 1 - z ^ n = (1 - z) * ∑ k ∈ Finset.range n, z ^ k :=
  (mul_neg_geom_sum z n).symm

lemma fr_le (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ 1) (n : ℕ) : 1 - z ^ n ≤ n * (1 - z) := by
  rw [fr_geom, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  calc ∑ k ∈ Finset.range n, z ^ k ≤ ∑ k ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => pow_le_one₀ h0 h1)
    _ = n := by simp

lemma fr_lt (z : ℝ) (h0 : 0 ≤ z) (h1 : z < 1) (n : ℕ) (hn : 2 ≤ n) :
    1 - z ^ n < n * (1 - z) := by
  rw [fr_geom, mul_comm]
  apply mul_lt_mul_of_pos_right _ (by linarith)
  calc ∑ k ∈ Finset.range n, z ^ k < ∑ k ∈ Finset.range n, (1 : ℝ) := by
        apply Finset.sum_lt_sum (fun k _ => pow_le_one₀ h0 h1.le)
        refine ⟨1, Finset.mem_range.2 (by omega), by simpa using h1⟩
    _ = n := by simp

lemma fr_ge (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ 1) (n N : ℕ) (hn : n ≤ N) :
    (1 - z) * n * z ^ N ≤ 1 - z ^ n := by
  rw [fr_geom]
  have : (n : ℝ) * z ^ N ≤ ∑ k ∈ Finset.range n, z ^ k := by
    calc (n : ℝ) * z ^ N = ∑ k ∈ Finset.range n, z ^ N := by simp
      _ ≤ _ := Finset.sum_le_sum (fun k hk => pow_le_pow_of_le_one h0 h1
            (by have := Finset.mem_range.1 hk; omega))
  have h2 : 0 ≤ 1 - z := by linarith
  calc (1 - z) * n * z ^ N = (1 - z) * (n * z ^ N) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this h2

theorem solution (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n) (hsum : HasSum q 1)
    (hq0 : 0 < q 0) :
    (∃ ξ : ℝ, 0 < ξ ∧ ξ < 1 ∧ HasSum (fun n => ξ ^ n * q n) ξ) ↔
      1 < ∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (q n) := by
  have hqs : Summable q := hsum.summable
  have hfin : ∀ u : Finset ℕ, ENNReal.ofReal (∑ n ∈ u, (n : ℝ) * q n)
      ≤ ∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (q n) := by
    intro u
    rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg n) (hq n))]
    refine le_trans (le_of_eq (Finset.sum_congr rfl ?_)) (ENNReal.sum_le_tsum u)
    intro n _
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  constructor
  · rintro ⟨ξ, h0, h1, hr⟩
    by_contra hle
    push_neg at hle
    have hbd : ∀ u : Finset ℕ, ∑ n ∈ u, (n : ℝ) * q n ≤ 1 := by
      intro u
      have := (hfin u).trans hle
      rwa [ENNReal.ofReal_le_one] at this
    have hnn : ∀ n : ℕ, 0 ≤ (n : ℝ) * q n := fun n => mul_nonneg (Nat.cast_nonneg n) (hq n)
    have hsn : Summable (fun n : ℕ => (n : ℝ) * q n) := summable_of_sum_le hnn hbd
    have hT : ∑' n : ℕ, (n : ℝ) * q n ≤ 1 := hsn.tsum_le_of_sum_le hbd
    have h3 : HasSum (fun n : ℕ => (n : ℝ) * q n * (1 - ξ)) ((∑' n : ℕ, (n : ℝ) * q n) * (1 - ξ)) :=
      hsn.hasSum.mul_right (1 - ξ)
    have h4 := hsum.sub hr
    have h5 := h3.sub h4
    set e : ℕ → ℝ := fun n => q n * (n * (1 - ξ) - (1 - ξ ^ n)) with he
    have hef : (fun n : ℕ => (n : ℝ) * q n * (1 - ξ) - (q n - ξ ^ n * q n)) = e := by
      funext n; simp only [he]; ring
    rw [hef] at h5
    have hen : ∀ n, 0 ≤ e n := fun n =>
      mul_nonneg (hq n) (by have := fr_le ξ h0.le h1.le n; linarith)
    have hval : (∑' n : ℕ, (n : ℝ) * q n) * (1 - ξ) - (1 - ξ) ≤ 0 := by
      nlinarith
    have hz : ∀ n, e n = 0 := fun n =>
      le_antisymm ((le_hasSum h5 n (fun j _ => hen j)).trans hval) (hen n)
    have hq2 : ∀ n, 2 ≤ n → q n = 0 := by
      intro n hn
      have := hz n
      simp only [he] at this
      have hlt := fr_lt ξ h0.le h1 n hn
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · linarith
    have hs1 : ∀ f : ℕ → ℝ, (∀ n ∉ Finset.range 2, f n = 0) →
        HasSum f (∑ n ∈ Finset.range 2, f n) := fun f hf =>
      hasSum_sum_of_ne_finset_zero hf
    have e1 := hsum.unique (hs1 q (fun n hn => hq2 n (by simp at hn; omega)))
    have e2 := hr.unique (hs1 (fun n => ξ ^ n * q n)
      (fun n hn => by rw [hq2 n (by simp at hn; omega)]; simp))
    simp [Finset.sum_range_succ] at e1 e2
    nlinarith [mul_pos hq0 (sub_pos.2 h1)]
  · intro hm
    obtain ⟨u, hu⟩ : ∃ u : Finset ℕ, 1 < ∑ n ∈ u, (n : ℝ≥0∞) * ENNReal.ofReal (q n) := by
      rw [ENNReal.tsum_eq_iSup_sum] at hm
      exact lt_iSup_iff.1 hm
    set S : ℝ := ∑ n ∈ u, (n : ℝ) * q n with hSdef
    have hS : 1 < S := by
      have : ∑ n ∈ u, (n : ℝ≥0∞) * ENNReal.ofReal (q n) = ENNReal.ofReal S := by
        rw [hSdef, ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg n) (hq n))]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
      rw [this] at hu
      exact (ENNReal.one_lt_ofReal).1 hu
    set N : ℕ := u.sup id with hN
    have hnN : ∀ n ∈ u, n ≤ N := fun n hn => Finset.le_sup (f := id) hn
    -- choose z close to 1
    have hlim : Filter.Tendsto (fun z : ℝ => z ^ N * S) (nhdsWithin 1 (Set.Iio 1)) (nhds (1 ^ N * S)) :=
      (((continuous_pow N).mul continuous_const).tendsto 1).mono_left nhdsWithin_le_nhds
    rw [one_pow, one_mul] at hlim
    obtain ⟨z, hz1, hz2⟩ := ((hlim.eventually (lt_mem_nhds hS)).and
      (Ioo_mem_nhdsLT (zero_lt_one' ℝ) : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin 1 (Set.Iio 1))).exists
    have hz0 : 0 < z := hz2.1
    have hz1' : z < 1 := hz2.2
    have hsumz : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Summable (fun n : ℕ => x ^ n * q n) := fun x hx0 hx1 =>
      Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg hx0 n) (hq n))
        (fun n => by
          have := mul_le_mul_of_nonneg_right (pow_le_one₀ hx0 hx1 (n := n)) (hq n)
          simpa using this) hqs
    set g : ℝ → ℝ := fun x => ∑' n : ℕ, x ^ n * q n - x with hg
    have hcont : ContinuousOn g (Set.Icc 0 1) := by
      have : ContinuousOn (fun x : ℝ => ∑' n : ℕ, x ^ n * q n) (Set.Icc 0 1) :=
        continuousOn_tsum (u := q) (fun n => (continuous_pow n |>.mul continuous_const).continuousOn)
          hqs (fun n x hx => by
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx.1 n) (hq n))]
            have := mul_le_mul_of_nonneg_right (pow_le_one₀ hx.1 hx.2 (n := n)) (hq n)
            simpa using this)
      exact this.sub continuousOn_id
    have hg0 : g 0 = q 0 := by
      simp only [hg]
      rw [tsum_eq_single 0]
      · simp
      · intro n hn; simp [hn]
    have hgz : g z < 0 := by
      simp only [hg]
      have hd := hsum.sub (hsumz z hz0.le hz1'.le).hasSum
      have hle : ∑ n ∈ u, (q n - z ^ n * q n) ≤ ∑' n, (q n - z ^ n * q n) :=
        hd.summable.sum_le_tsum u (fun n _ => by
          have := mul_le_mul_of_nonneg_right (pow_le_one₀ hz0.le hz1'.le (n := n)) (hq n)
          simp at this; linarith)
      rw [hd.tsum_eq] at hle
      have hlow : (1 - z) * z ^ N * S ≤ ∑ n ∈ u, (q n - z ^ n * q n) := by
        rw [hSdef, Finset.mul_sum]
        refine Finset.sum_le_sum (fun n hn => ?_)
        have := fr_ge z hz0.le hz1'.le n N (hnN n hn)
        have h2 := mul_le_mul_of_nonneg_right this (hq n)
        calc (1 - z) * z ^ N * ((n : ℝ) * q n) = (1 - z) * n * z ^ N * q n := by ring
          _ ≤ _ := by linarith
      have : (1 - z) < (1 - z) * (z ^ N * S) :=
        lt_mul_of_one_lt_right (by linarith) hz1
      nlinarith
    have hg0' : 0 < g 0 := by rw [hg0]; exact hq0
    have hmem : (0 : ℝ) ∈ Set.Icc (g z) (g 0) := ⟨hgz.le, hg0'.le⟩
    obtain ⟨ξ, hξ, hξ0⟩ := intermediate_value_Icc' hz0.le
      (hcont.mono (Set.Icc_subset_Icc le_rfl hz1'.le)) hmem
    have hξ1 : ξ ≠ 0 := by rintro rfl; linarith
    have hξ2 : ξ ≠ z := by rintro rfl; linarith
    have hξpos : 0 < ξ := lt_of_le_of_ne hξ.1 (Ne.symm hξ1)
    have hξlt : ξ < z := lt_of_le_of_ne hξ.2 hξ2
    refine ⟨ξ, hξpos, hξlt.trans hz1', ?_⟩
    have := (hsumz ξ hξpos.le (hξlt.trans hz1').le).hasSum
    have e : ∑' n : ℕ, ξ ^ n * q n = ξ := by simp only [hg] at hξ0; linarith
    rwa [e] at this
