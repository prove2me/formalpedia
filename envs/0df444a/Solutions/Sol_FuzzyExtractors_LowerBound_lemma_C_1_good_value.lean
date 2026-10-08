-- Prove2me | solution 1 for FuzzyExtractors.LowerBound.lemma_C_1_good_value
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:18:58.656201+00:00
-- url     : https://prove2.me/submissions/bfe03ac2-c4b1-4506-a434-51073dd6be68

import Mathlib
import Definitions.Def_FuzzyExtractors_LowerBound_Basic

open FuzzyExtractors.LowerBound FuzzyExtractors.Hamming
open scoped ENNReal

theorem solution {M V : Type} [Fintype M] (SS : M → PMF V) (S : Finset M)
    (hS : S.Nonempty) (m' : ℝ)
    (h : m' ≤ FuzzyExtractors.Hamming.avgMinEntropy (FuzzyExtractors.Hamming.withSketch SS (PMF.uniformOfFinset S hS))) :
    ∃ v : V, 0 < ((PMF.uniformOfFinset S hS).bind SS) v ∧
      ∀ w : M, FuzzyExtractors.Hamming.withSketch SS (PMF.uniformOfFinset S hS) (w, v) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-m')) * ((PMF.uniformOfFinset S hS).bind SS) v := by
  classical
  let W := PMF.uniformOfFinset S hS
  let J := withSketch SS W
  let Q := W.bind SS
  let z : ℝ≥0∞ := ∑' v, ⨆ w, J (w, v)
  let c : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (-m'))
  have hJ (w : M) (v : V) : J (w, v) = W w * SS w v := by
    have hm (a : M) : ((SS a).map fun s => (a,s)) (w,v) =
        if w = a then SS a v else 0 := by
      by_cases ha : w = a
      · subst a; simp [PMF.map_apply]
      · simp [PMF.map_apply, Prod.mk.injEq, ha]
    simp [J, withSketch, PMF.bind_apply, hm, mul_ite]
  have hQ (v : V) : (∑' w, J (w, v)) = Q v := by
    simp only [hJ, Q, PMF.bind_apply]
  have hle (v : V) : (⨆ w, J (w, v)) ≤ Q v := by
    apply iSup_le
    intro w
    rw [← hQ]
    exact ENNReal.le_tsum w
  have hzle : z ≤ 1 := by
    calc
      z ≤ ∑' v, Q v := ENNReal.tsum_le_tsum hle
      _ = 1 := Q.tsum_coe
  have hzfin : z ≠ ∞ := ne_of_lt (lt_of_le_of_lt hzle ENNReal.one_lt_top)
  obtain ⟨⟨w0,v0⟩, hp⟩ := J.support_nonempty
  have hzpos : 0 < z := by
    have hpp : 0 < J (w0,v0) := (J.mem_support_iff _).mp hp |> pos_iff_ne_zero.mpr
    exact hpp.trans_le ((le_iSup (fun w => J (w,v0)) w0).trans (ENNReal.le_tsum v0))
  have hzc : z ≤ c := by
    have hr : 0 < z.toReal := ENNReal.toReal_pos (ne_of_gt hzpos) hzfin
    have hlog : Real.logb 2 z.toReal ≤ -m' := by
      change m' ≤ -Real.logb 2 z.toReal at h
      linarith
    have hb : z.toReal ≤ (2 : ℝ) ^ (-m') :=
      (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hr).mp hlog
    simpa [c, ENNReal.ofReal_toReal hzfin] using ENNReal.ofReal_le_ofReal hb
  by_contra hn
  have hbad : ∀ v, 0 < Q v → c * Q v < ⨆ w, J (w,v) := by
    intro v hv
    have hx : ¬ ∀ w, J (w,v) ≤ c * Q v := by
      intro hx
      apply hn
      exact ⟨v, hv, hx⟩
    push_neg at hx
    obtain ⟨w, hw⟩ := hx
    exact hw.trans_le (le_iSup (fun w => J (w,v)) w)
  have hcQ : (∑' v, c * Q v) = c := by
    rw [ENNReal.tsum_mul_left, Q.tsum_coe, mul_one]
  have hall : ∀ v, c * Q v ≤ ⨆ w, J (w,v) := by
    intro v
    by_cases hv : Q v = 0
    · simp [hv]
    · exact (hbad v (pos_iff_ne_zero.mpr hv)).le
  obtain ⟨v, hv⟩ := Q.support_nonempty
  have hlt := ENNReal.tsum_lt_tsum (by rw [hcQ]; exact ENNReal.ofReal_ne_top)
    hall (hbad v (pos_iff_ne_zero.mpr hv))
  rw [hcQ] at hlt
  exact (not_lt_of_ge hzc) hlt

#print axioms solution
