-- Prove2me | solution 1 for BauerleRiederMDP.Indifference.remark_4_9_3_minimal_entropy
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:15:54.896769+00:00
-- url     : https://prove2.me/submissions/3dfe8b20-16aa-416f-869c-3c77ef1fd12c

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_Market_Q
import Definitions.Def_BauerleRiederMDP_Indifference_Market_IsEMM
import Definitions.Def_BauerleRiederMDP_Indifference_Market_entropy

namespace Aux_BRMDP_minent
open MeasureTheory BauerleRiederMDP.Indifference

lemma sum_dirac_single (c : Fin 4 → ENNReal) (ω : Fin 4) :
    (∑ k, c k • Measure.dirac k) {ω} = c ω := by
  rw [Measure.finsetSum_apply]
  simp [Measure.dirac_apply', Set.indicator_apply]

lemma ac_sum_dirac (c : Fin 4 → ENNReal) (hc : ∀ k, c k ≠ 0) (μ : Measure (Fin 4)) :
    μ ≪ ∑ k, c k • Measure.dirac k := by
  intro s hs
  have : s = ∅ := by
    by_contra hne
    obtain ⟨k, hk⟩ := Set.nonempty_iff_ne_empty.2 hne
    have h1 := measure_mono (μ := ∑ k, c k • Measure.dirac k) (Set.singleton_subset_iff.2 hk)
    rw [sum_dirac_single, hs] at h1
    exact hc k (le_antisymm h1 (by simp))
  rw [this, measure_empty]

lemma P_single (M : Market) (ω : Fin 4) : M.P {ω} = ENNReal.ofReal (M.p ω) := by
  unfold Market.P; exact sum_dirac_single _ ω

lemma entropy_eq (M : Market) (Q' : Measure (Fin 4)) [IsFiniteMeasure Q'] (hac : Q' ≪ M.P) :
    M.entropy Q' = ∑ ω, (Q' {ω}).toReal * Real.log ((Q' {ω}).toReal / M.p ω) := by
  unfold Market.entropy
  rw [integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro ω _
  rw [smul_eq_mul, measureReal_def]
  congr 2
  have h := Measure.withDensity_rnDeriv_eq Q' M.P hac
  have h2 : Q' {ω} = Q'.rnDeriv M.P ω * M.P {ω} := by
    conv_lhs => rw [← h]
    rw [withDensity_apply _ (measurableSet_singleton ω), lintegral_singleton]
  rw [P_single] at h2
  have hp := M.p_pos ω
  have hne : ENNReal.ofReal (M.p ω) ≠ 0 := by simpa using hp
  have hr : Q'.rnDeriv M.P ω = Q' {ω} / ENNReal.ofReal (M.p ω) := by
    rw [h2, ENNReal.mul_div_cancel_right hne ENNReal.ofReal_ne_top]
  rw [hr, ENNReal.toReal_div, ENNReal.toReal_ofReal hp.le]

lemma integral_eq_sum (Q' : Measure (Fin 4)) [IsFiniteMeasure Q'] (f : Fin 4 → ℝ) :
    ∫ ω, f ω ∂Q' = ∑ ω, (Q' {ω}).toReal * f ω := by
  rw [integral_fintype Integrable.of_finite]
  simp [measureReal_def]

lemma q_bounds (M : Market) : 0 < M.q ∧ M.q < 1 := by
  unfold Market.q
  have h1 := M.d_lt_one; have h2 := M.one_lt_u
  constructor
  · apply div_pos <;> linarith
  · rw [div_lt_one (by linarith)]; linarith

lemma gibbs_term (w v p : ℝ) (hw : 0 < w) (hv : 0 < v) (hp : 0 < p) :
    (w - v) + w * Real.log (v / p) ≤ w * Real.log (w / p) := by
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hw hv)
  rw [inv_div] at h1
  have e : Real.log (w / p) = Real.log (w / v) + Real.log (v / p) := by
    rw [Real.log_div hw.ne' hp.ne', Real.log_div hw.ne' hv.ne', Real.log_div hv.ne' hp.ne']
    ring
  rw [e, mul_add]
  have h2 : w * (1 - v / w) ≤ w * Real.log (w / v) := mul_le_mul_of_nonneg_left h1 hw.le
  have h3 : w * (1 - v / w) = w - v := by field_simp
  linarith

end Aux_BRMDP_minent

open MeasureTheory BauerleRiederMDP.Indifference Aux_BRMDP_minent in
theorem solution (M : Market) :
    M.IsEMM M.Q ∧ ∀ Q' : MeasureTheory.Measure (Fin 4), M.IsEMM Q' →
      M.entropy M.Q ≤ M.entropy Q' := by
  obtain ⟨hq0, hq1⟩ := q_bounds M
  have hp := M.p_pos
  have h01 : 0 < M.p 0 + M.p 1 := by linarith [hp 0, hp 1]
  have h23 : 0 < M.p 2 + M.p 3 := by linarith [hp 2, hp 3]
  have hv0 : M.qWeight 0 = M.q * (M.p 0 / (M.p 0 + M.p 1)) := rfl
  have hv1 : M.qWeight 1 = M.q * (M.p 1 / (M.p 0 + M.p 1)) := rfl
  have hv2 : M.qWeight 2 = (1 - M.q) * (M.p 2 / (M.p 2 + M.p 3)) := rfl
  have hv3 : M.qWeight 3 = (1 - M.q) * (M.p 3 / (M.p 2 + M.p 3)) := rfl
  have hvpos : ∀ k, 0 < M.qWeight k := by
    intro k
    fin_cases k
    · show 0 < M.qWeight 0
      rw [hv0]; exact mul_pos hq0 (div_pos (hp 0) h01)
    · show 0 < M.qWeight 1
      rw [hv1]; exact mul_pos hq0 (div_pos (hp 1) h01)
    · show 0 < M.qWeight 2
      rw [hv2]; exact mul_pos (by linarith) (div_pos (hp 2) h23)
    · show 0 < M.qWeight 3
      rw [hv3]; exact mul_pos (by linarith) (div_pos (hp 3) h23)
  have hv01 : M.qWeight 0 + M.qWeight 1 = M.q := by rw [hv0, hv1]; field_simp
  have hv23 : M.qWeight 2 + M.qWeight 3 = 1 - M.q := by rw [hv2, hv3]; field_simp
  have hQs : ∀ k, M.Q {k} = ENNReal.ofReal (M.qWeight k) := by
    intro k; unfold Market.Q; exact sum_dirac_single _ k
  have hQr : ∀ k, (M.Q {k}).toReal = M.qWeight k := by
    intro k; rw [hQs, ENNReal.toReal_ofReal (hvpos k).le]
  have hQprob : IsProbabilityMeasure M.Q := by
    constructor
    unfold Market.Q
    rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => (hvpos k).le), Fin.sum_univ_four]
    rw [show M.qWeight 0 + M.qWeight 1 + M.qWeight 2 + M.qWeight 3 = 1 by linarith]
    simp
  have hQP : M.Q ≪ M.P := by
    unfold Market.P
    exact ac_sum_dirac _ (fun k => by simpa using hp k) M.Q
  have hPQ : M.P ≪ M.Q := by
    unfold Market.Q
    exact ac_sum_dirac _ (fun k => by simpa using hvpos k) M.P
  have hqud : M.q * M.u + (1 - M.q) * M.d = 1 := by
    unfold Market.q
    have h1 := M.d_lt_one; have h2 := M.one_lt_u
    have hne : M.u - M.d ≠ 0 := by linarith
    field_simp
    ring
  refine ⟨⟨hQprob, hQP, hPQ, fun s => ?_⟩, ?_⟩
  · rw [integral_eq_sum, Fin.sum_univ_four]
    simp only [hQr]
    simp [Market.Rt]
    linear_combination (s * M.u) * hv01 + (s * M.d) * hv23 + s * hqud
  · rintro Q' ⟨hprob, hac, hac', hmart⟩
    rw [entropy_eq M M.Q hQP, entropy_eq M Q' hac, Fin.sum_univ_four, Fin.sum_univ_four]
    simp only [hQr]
    have hwpos : ∀ k, 0 < (Q' {k}).toReal := by
      intro k
      apply ENNReal.toReal_pos _ (measure_ne_top _ _)
      intro h0
      have h1 := hac' h0
      rw [P_single, ENNReal.ofReal_eq_zero] at h1
      linarith [hp k]
    have hsum : ∑ k, (Q' {k}).toReal = 1 := by
      have h := integral_eq_sum Q' (fun _ => (1 : ℝ))
      simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at h
      exact h.symm
    have hm := hmart 1
    rw [integral_eq_sum] at hm
    rw [Fin.sum_univ_four] at hsum hm
    simp [Market.Rt] at hm
    obtain ⟨w0, hw0⟩ : ∃ x, x = (Q' {0}).toReal := ⟨_, rfl⟩
    obtain ⟨w1, hw1⟩ : ∃ x, x = (Q' {1}).toReal := ⟨_, rfl⟩
    obtain ⟨w2, hw2⟩ : ∃ x, x = (Q' {2}).toReal := ⟨_, rfl⟩
    obtain ⟨w3, hw3⟩ : ∃ x, x = (Q' {3}).toReal := ⟨_, rfl⟩
    rw [← hw0, ← hw1, ← hw2, ← hw3] at hsum hm ⊢
    have hp0 := hwpos 0; have hp1 := hwpos 1; have hp2 := hwpos 2; have hp3 := hwpos 3
    rw [← hw0] at hp0; rw [← hw1] at hp1; rw [← hw2] at hp2; rw [← hw3] at hp3
    have hud : 0 < M.u - M.d := by linarith [M.d_lt_one, M.one_lt_u]
    have hw01 : w0 + w1 = M.q := by
      unfold Market.q
      rw [eq_div_iff hud.ne']
      linear_combination hm - M.d * hsum
    have hpne : ∀ k, M.p k ≠ 0 := fun k => (hp k).ne'
    have hp0ne := hpne 0; have hp1ne := hpne 1; have hp2ne := hpne 2; have hp3ne := hpne 3
    have h01ne := h01.ne'; have h23ne := h23.ne'
    set L1 := Real.log (M.q / (M.p 0 + M.p 1)) with hL1
    set L2 := Real.log ((1 - M.q) / (M.p 2 + M.p 3)) with hL2
    have l0 : Real.log (M.qWeight 0 / M.p 0) = L1 := by
      rw [hv0, hL1]; congr 1; field_simp <;> ring
    have l1 : Real.log (M.qWeight 1 / M.p 1) = L1 := by
      rw [hv1, hL1]; congr 1; field_simp <;> ring
    have l2 : Real.log (M.qWeight 2 / M.p 2) = L2 := by
      rw [hv2, hL2]; congr 1; field_simp <;> ring
    have l3 : Real.log (M.qWeight 3 / M.p 3) = L2 := by
      rw [hv3, hL2]; congr 1; field_simp <;> ring
    have t0 := gibbs_term w0 (M.qWeight 0) (M.p 0) hp0 (hvpos 0) (hp 0)
    have t1 := gibbs_term w1 (M.qWeight 1) (M.p 1) hp1 (hvpos 1) (hp 1)
    have t2 := gibbs_term w2 (M.qWeight 2) (M.p 2) hp2 (hvpos 2) (hp 2)
    have t3 := gibbs_term w3 (M.qWeight 3) (M.p 3) hp3 (hvpos 3) (hp 3)
    rw [l0] at t0; rw [l1] at t1; rw [l2] at t2; rw [l3] at t3
    rw [l0, l1, l2, l3]
    have m1 : w0 * L1 + w1 * L1 = M.qWeight 0 * L1 + M.qWeight 1 * L1 := by
      rw [← add_mul, ← add_mul, hw01, hv01]
    have m2 : w2 * L2 + w3 * L2 = M.qWeight 2 * L2 + M.qWeight 3 * L2 := by
      rw [← add_mul, ← add_mul, hv23]
      congr 1
      linarith
    linarith
