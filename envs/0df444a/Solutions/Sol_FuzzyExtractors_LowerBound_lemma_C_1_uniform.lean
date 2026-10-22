-- Prove2me | solution 1 for FuzzyExtractors.LowerBound.lemma_C_1_uniform
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T03:46:40.308269+00:00
-- url     : https://prove2.me/submissions/fd273ada-2fb1-4c3a-9a12-b5901dd0e351

import Mathlib
import Definitions.Def_FuzzyExtractors_LowerBound_Basic



namespace FuzzyExtractors.LowerBound

open scoped ENNReal

lemma h34_joint {M V : Type} [Fintype M] [Nonempty M] (SS : M → PMF V) (w : M) (v : V) :
    FuzzyExtractors.Hamming.withSketch SS (PMF.uniformOfFintype M) (w, v)
      = (Fintype.card M : ℝ≥0∞)⁻¹ * SS w v := by
  classical
  unfold FuzzyExtractors.Hamming.withSketch
  rw [PMF.bind_apply]
  rw [tsum_eq_single w]
  · rw [PMF.uniformOfFintype_apply, PMF.map_apply]
    congr 1
    rw [tsum_eq_single v]
    · simp
    · intro s hs
      simp [Ne.symm hs]
  · intro w' hw'
    rw [PMF.map_apply]
    have : ∀ s, (if (w, v) = (w', s) then (SS w') s else 0) = 0 := by
      intro s
      have : (w, v) ≠ (w', s) := fun h => hw' (by simpa using (Prod.mk.inj h).1.symm)
      simp [this]
    have hw'' : w ≠ w' := Ne.symm hw'
    simp [hw'']

lemma h34_core {M V : Type} [Fintype M] [Nonempty M] (dis : M → M → ℕ)
    (hsymm : ∀ x y, dis x y = dis y x)
    (m m' : ℝ) (t : ℕ)
    (SS : M → PMF V) (Rec : M → V → PMF M) (hSS : FuzzyExtractors.Hamming.IsSecureSketch dis m m' t SS Rec)
    (hm : m = Real.logb 2 (Fintype.card M)) :
    (2:ℝ) ^ m' ≤ (K dis t Finset.univ : ℝ) := by
  classical
  obtain ⟨hcorr, hent⟩ := hSS
  set n : ℕ := Fintype.card M with hn
  have hnpos : 0 < n := Fintype.card_pos
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hnt : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  set W : PMF M := PMF.uniformOfFintype M with hW
  have hmin : m ≤ FuzzyExtractors.Hamming.minEntropy W := by
    unfold FuzzyExtractors.Hamming.minEntropy
    have : (⨆ a, W a) = (n : ℝ≥0∞)⁻¹ := by
      simp [hW, PMF.uniformOfFintype_apply, hn]
    rw [this, ENNReal.toReal_inv, ENNReal.toReal_natCast, Real.logb_inv, neg_neg, hm]
  have h1 := hent W hmin
  unfold FuzzyExtractors.Hamming.avgMinEntropy at h1
  set A : ℝ≥0∞ := ∑' v, ⨆ w, SS w v with hA
  have hX : (∑' v, ⨆ w, FuzzyExtractors.Hamming.withSketch SS W (w, v)) = (n : ℝ≥0∞)⁻¹ * A := by
    rw [hA, ← ENNReal.tsum_mul_left]
    congr 1
    ext v
    rw [ENNReal.mul_iSup]
    congr 1
    ext w
    exact h34_joint SS w v
  -- bounds on A
  have hAle : A ≤ n := by
    calc A ≤ ∑' v, ∑ w, SS w v := by
          refine ENNReal.tsum_le_tsum fun v => iSup_le fun w => ?_
          exact Finset.single_le_sum (f := fun w => SS w v) (fun _ _ => zero_le) (Finset.mem_univ w)
      _ = ∑ w, ∑' v, SS w v := Summable.tsum_finsetSum (fun w _ => ENNReal.summable)
      _ = n := by simp [PMF.tsum_coe, hn]
  have hsum : ∑' v, ∑ w, SS w v = n := by
    have : ∑' v, ∑ w, SS w v = ∑ w, ∑' v, SS w v :=
      Summable.tsum_finsetSum (fun w _ => ENNReal.summable)
    rw [this]; simp [PMF.tsum_coe, hn]
  have hApos : 1 ≤ A := by
    obtain ⟨w0⟩ := (inferInstance : Nonempty M)
    calc (1 : ℝ≥0∞) = ∑' v, SS w0 v := (PMF.tsum_coe _).symm
      _ ≤ A := ENNReal.tsum_le_tsum fun v => le_iSup (fun w => SS w v) w0
  have hAtop : A ≠ ⊤ := ne_top_of_le_ne_top hnt hAle
  have hapos : 0 < A.toReal := ENNReal.toReal_pos (by intro h; rw [h] at hApos; simp at hApos) hAtop
  -- counting
  have hcount : (n : ℝ≥0∞) ≤ (K dis t Finset.univ : ℝ≥0∞) * A := by
    rw [← hsum, hA, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun v => ?_
    have hcode : FuzzyExtractors.Hamming.IsCode dis (producers SS Finset.univ v) t := by
      intro x c hc c' hc' h1 h2
      have hc1 : v ∈ (SS c).support := (Finset.mem_filter.1 hc).2
      have hc2 : v ∈ (SS c').support := (Finset.mem_filter.1 hc').2
      have e1 := hcorr c x (by rw [hsymm]; exact h1) v hc1
      have e2 := hcorr c' x (by rw [hsymm]; exact h2) v hc2
      rw [e1] at e2
      have := congrArg (fun p : PMF M => p c) e2
      simpa [PMF.pure_apply, eq_comm] using this
    have hK : (producers SS Finset.univ v).card ≤ K dis t Finset.univ := by
      unfold K
      exact Finset.le_sup (f := Finset.card)
        (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _), hcode⟩)
    calc ∑ w, SS w v = ∑ w ∈ producers SS Finset.univ v, SS w v := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro w _ hw
          by_contra hne
          apply hw
          unfold producers
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by rwa [PMF.mem_support_iff]⟩
      _ ≤ ∑ w ∈ producers SS Finset.univ v, ⨆ w, SS w v :=
          Finset.sum_le_sum fun w _ => le_iSup (fun w => SS w v) w
      _ = (producers SS Finset.univ v).card * ⨆ w, SS w v := by simp
      _ ≤ (K dis t Finset.univ : ℝ≥0∞) * ⨆ w, SS w v :=
          mul_le_mul_left (by exact_mod_cast hK) _
  have hreal : (n : ℝ) ≤ (K dis t Finset.univ : ℝ) * A.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hAtop) hcount
    simpa [ENNReal.toReal_mul] using this
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  rw [hX, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast] at h1
  have h2 : Real.logb 2 ((n : ℝ)⁻¹ * A.toReal) ≤ -m' := by linarith
  have h3 : (n : ℝ)⁻¹ * A.toReal ≤ (2 : ℝ) ^ (-m') :=
    (Real.logb_le_iff_le_rpow (by norm_num) (by positivity)).1 h2
  have h4 : A.toReal ≤ n * (2 : ℝ) ^ (-m') := by
    have := mul_le_mul_of_nonneg_left h3 hnR.le
    rwa [← mul_assoc, mul_inv_cancel₀ hnR.ne', one_mul] at this
  have h5 : (n : ℝ) ≤ K dis t Finset.univ * (n * (2 : ℝ) ^ (-m')) :=
    hreal.trans (mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg _))
  have h6 : (1 : ℝ) ≤ K dis t Finset.univ * (2 : ℝ) ^ (-m') := by
    have : (n : ℝ) * 1 ≤ n * (K dis t Finset.univ * (2 : ℝ) ^ (-m')) := by nlinarith
    exact le_of_mul_le_mul_left this hnR
  have h7 : (2 : ℝ) ^ m' * (2 : ℝ) ^ (-m') = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have h8 : (0 : ℝ) < (2 : ℝ) ^ (-m') := by positivity
  by_contra hlt
  push_neg at hlt
  have := mul_lt_mul_of_pos_right hlt h8
  linarith

theorem uniform_core {M V : Type} [Fintype M] [Nonempty M] (dis : M → M → ℕ)
    (hsymm : ∀ x y, dis x y = dis y x)
    (m m' : ℝ) (t : ℕ)
    (SS : M → PMF V) (Rec : M → V → PMF M) (hSS : FuzzyExtractors.Hamming.IsSecureSketch dis m m' t SS Rec)
    (hm : m = Real.logb 2 (Fintype.card M)) :
    m' ≤ Real.logb 2 (K dis t Finset.univ : ℕ) := by
  have h := h34_core dis hsymm m m' t SS Rec hSS hm
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m' := by positivity
  rw [Real.le_logb_iff_rpow_le (by norm_num) (lt_of_lt_of_le hpos h)]
  exact h

end FuzzyExtractors.LowerBound

open FuzzyExtractors.LowerBound


theorem solution {M V : Type} [Fintype M] [Nonempty M] (dis : M → M → ℕ)
    (hzero : ∀ x y, dis x y = 0 ↔ x = y)
    (hsymm : ∀ x y, dis x y = dis y x)
    (htri : ∀ x y z, dis x z ≤ dis x y + dis y z)
    (m m' : ℝ) (t : ℕ)
    (SS : M → PMF V) (Rec : M → V → PMF M) (hSS : FuzzyExtractors.Hamming.IsSecureSketch dis m m' t SS Rec)
    (hm : m = Real.logb 2 (Fintype.card M)) :
    m' ≤ Real.logb 2 (K dis t Finset.univ) := by
  exact uniform_core dis hsymm m m' t SS Rec hSS hm
