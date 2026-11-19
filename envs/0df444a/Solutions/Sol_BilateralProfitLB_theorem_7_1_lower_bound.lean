-- Prove2me | solution 1 for BilateralProfitLB.theorem_7_1_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T13:35:41.620194+00:00
-- url     : https://prove2.me/submissions/42b40f30-ac61-4d95-93d8-bf192b798f2a

import Mathlib
import Definitions.Def_BilateralProfitLB_Construction
import Definitions.Def_BilateralProfitLB_Stochastic
import Theorems.Thm_BilateralProfitLB_claim_7_3
import Theorems.Thm_BilateralProfitLB_expCount_transfer_randomized
import Theorems.Thm_BilateralProfitLB_regret_display


section BundlePart000



open Set Filter MeasureTheory
open scoped ENNReal

namespace BilateralProfitLB

open MechanismDesign.BilateralTrade

private abbrev HardLawClaim : Prop :=
  ∀ K : ℕ, 1 ≤ K → ∀ j : ℕ, j ≤ K →
    ∃ E : Environment, UnitSupport E ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, E.fS x = 1) ∧
      (∀ b ∈ Set.Icc (0 : ℝ) 1, E.fB b = fB K j b) ∧
      (∀ b ∈ Set.Icc (0 : ℝ) 1, 1 - E.cdfB b = S K j b) ∧
      E.prior = law K j ∧ E.Regular

private theorem densityEnvironment_integrable {E : Environment} (hE : UnitSupport E) :
    IntegrableOn E.fB (Icc (0 : ℝ) 1) := by
  have hi : IntervalIntegrable E.fB volume 0 1 :=
    hE.2.2.1 ▸ hE.2.2.2 ▸ E.fB_intervalIntegrable
  exact (integrableOn_Icc_iff_integrableOn_Ioc (μ := volume)).2 hi.1

private theorem densityEnvironment_integral {E : Environment} (hE : UnitSupport E) :
    ∫ x in (0 : ℝ)..1, E.fB x = 1 :=
  hE.2.2.1 ▸ hE.2.2.2 ▸ E.fB_integral

private theorem densityEnvironment_linIcc {E : Environment} {K j : ℕ}
    (hE : UnitSupport E) (hB : ∀ b ∈ Icc (0 : ℝ) 1, E.fB b = fB K j b)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ∫⁻ x in Icc q 1, ENNReal.ofReal (fB K j x) =
      ENNReal.ofReal (∫ x in q..1, E.fB x) := by
  have hsub : Icc q 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc_left hq.1
  have hi : IntegrableOn E.fB (Icc q 1) :=
    (densityEnvironment_integrable hE).mono_set hsub
  have hnon : 0 ≤ᵐ[volume.restrict (Icc q 1)] E.fB := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    apply le_of_lt
    apply E.fB_pos
    rw [hE.2.2.1, hE.2.2.2]
    exact hsub hx
  rw [intervalIntegral.integral_of_le hq.2, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hi hnon]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [hB x (hsub hx)]

private theorem densityEnvironment_tail {E : Environment} {K j : ℕ} (hE : UnitSupport E)
    (hS : ∀ b ∈ Icc (0 : ℝ) 1, 1 - E.cdfB b = S K j b) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ∫ x in q..1, E.fB x = S K j q := by
  have hi := densityEnvironment_integrable hE
  have hin₁ : IntervalIntegrable E.fB volume 0 q := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le hq.1]
    exact hi.mono_set (Icc_subset_Icc_right hq.2)
  have hin₂ : IntervalIntegrable E.fB volume q 1 := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le hq.2]
    exact hi.mono_set (Icc_subset_Icc_left hq.1)
  have hsum := intervalIntegral.integral_add_adjacent_intervals hin₁ hin₂
  rw [densityEnvironment_integral hE] at hsum
  have hs := hS q hq
  rw [Environment.cdfB, hE.2.2.1] at hs
  linarith

private theorem S_nonneg_of_claim_7_3 (hClaim : HardLawClaim) {K j : ℕ} (hK : 1 ≤ K)
    (hj : j ≤ K) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : 0 ≤ S K j q := by
  obtain ⟨E, hE, _, _, hS, _, _⟩ := hClaim K hK j hj
  rw [← densityEnvironment_tail hE hS hq]
  apply intervalIntegral.integral_nonneg hq.2
  intro b hb
  have hb' : b ∈ Icc E.loB E.hiB := by
    rw [hE.2.2.1, hE.2.2.2]
    exact ⟨hq.1.trans hb.1, hb.2⟩
  exact (E.fB_pos b hb').le

private theorem S_continuousOn_of_claim_7_3 (hClaim : HardLawClaim) {K j : ℕ} (hK : 1 ≤ K)
    (hj : j ≤ K) : ContinuousOn (S K j) (Icc (0 : ℝ) 1) := by
  obtain ⟨E, hE, _, _, hS, _, _⟩ := hClaim K hK j hj
  have hi := densityEnvironment_integrable hE
  have hcont : ContinuousOn (fun b => ∫ x in (0 : ℝ)..b, E.fB x) (Icc (0 : ℝ) 1) := by
    rw [← uIcc_of_le zero_le_one] at hi ⊢
    exact intervalIntegral.continuousOn_primitive_interval hi
  have hdiff : ContinuousOn (fun b => (1 : ℝ) - ∫ x in (0 : ℝ)..b, E.fB x) (Icc 0 1) :=
    continuousOn_const.sub hcont
  refine hdiff.congr fun b hb => ?_
  simpa only [Environment.cdfB, hE.2.2.1] using (hS b hb).symm

private theorem buyerMeasure_Ici_of_claim_7_3 (hClaim : HardLawClaim) {K j : ℕ}
    (hK : 1 ≤ K) (hj : j ≤ K) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ((volume.restrict (Icc (0 : ℝ) 1)).withDensity fun b => ENNReal.ofReal (fB K j b))
      (Ici q) = ENNReal.ofReal (S K j q) := by
  obtain ⟨E, hE, _, hB, hS, _, _⟩ := hClaim K hK j hj
  have hh : Ici q ∩ Icc (0 : ℝ) 1 = Icc q 1 := by
    ext b
    exact ⟨fun ⟨h, _, h₁⟩ => ⟨h, h₁⟩, fun ⟨h, h₁⟩ => ⟨h, hq.1.trans h, h₁⟩⟩
  rw [withDensity_apply _ measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    hh, densityEnvironment_linIcc hE hB hq, densityEnvironment_tail hE hS hq]

private theorem buyerMeasure_Ici_real_of_claim_7_3 (hClaim : HardLawClaim) {K j : ℕ}
    (hK : 1 ≤ K) (hj : j ≤ K) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ((volume.restrict (Icc (0 : ℝ) 1)).withDensity fun b => ENNReal.ofReal (fB K j b)).real
      (Ici q) = S K j q := by
  rw [Measure.real, buyerMeasure_Ici_of_claim_7_3 hClaim hK hj hq,
    ENNReal.toReal_ofReal (S_nonneg_of_claim_7_3 hClaim hK hj hq)]

private theorem buyerMeasure_inUnit_of_claim_7_3 (hClaim : HardLawClaim) {K j : ℕ}
    (hK : 1 ≤ K) (hj : j ≤ K) :
    ∫⁻ x in Icc (0 : ℝ) 1, ENNReal.ofReal (fB K j x) = 1 := by
  obtain ⟨E, hE, _, hB, _, _, _⟩ := hClaim K hK j hj
  rw [densityEnvironment_linIcc hE hB (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩),
    densityEnvironment_integral hE, ENNReal.ofReal_one]

private theorem buyerMeasure_isProbabilityMeasure_of_claim_7_3 (hClaim : HardLawClaim)
    {K j : ℕ} (hK : 1 ≤ K) (hj : j ≤ K) :
    IsProbabilityMeasure
      ((volume.restrict (Icc (0 : ℝ) 1)).withDensity fun b => ENNReal.ofReal (fB K j b)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    buyerMeasure_inUnit_of_claim_7_3 hClaim hK hj]

private theorem sellerMeasure_isProbabilityMeasure_unit :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := by
  constructor
  simp

private theorem law_isProbabilityMeasure_of_claim_7_3 (hClaim : HardLawClaim)
    {K j : ℕ} (hK : 1 ≤ K) (hj : j ≤ K) : IsProbabilityMeasure (law K j) := by
  letI := sellerMeasure_isProbabilityMeasure_unit
  letI := buyerMeasure_isProbabilityMeasure_of_claim_7_3 hClaim hK hj
  unfold law
  infer_instance

private theorem law_supported_of_claim_7_3 (hClaim : HardLawClaim)
    {K j : ℕ} (hK : 1 ≤ K) (hj : j ≤ K) :
    law K j ((Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) = 1 := by
  letI := sellerMeasure_isProbabilityMeasure_unit
  letI := buyerMeasure_isProbabilityMeasure_of_claim_7_3 hClaim hK hj
  rw [law, Measure.prod_prod]
  have hs : (volume.restrict (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) = 1 := by
    simp [Measure.restrict_apply, measurableSet_Icc]
  have hb : ((volume.restrict (Icc (0 : ℝ) 1)).withDensity
          fun b => ENNReal.ofReal (fB K j b)) (Icc (0 : ℝ) 1) = 1 := by
    rw [withDensity_apply _ measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      inter_self, buyerMeasure_inUnit_of_claim_7_3 hClaim hK hj]
  rw [hs, hb, one_mul]

end BilateralProfitLB
end BundlePart000


section BundlePart001


namespace BilateralProfitLB

private theorem w_pos {K : ℕ} (hK : 0 < K) : 0 < w K := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold w
  positivity

private theorem w_le_quarter {K : ℕ} (hK : 0 < K) : w K ≤ 1 / 4 := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  unfold w
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

private theorem cast_mul_w {K : ℕ} (hK : 0 < K) : (K : ℝ) * w K = 1 / 4 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold w
  field_simp

private theorem a_ge_quarter {K j : ℕ} (hj : 1 ≤ j) : 1 / 4 ≤ a K j := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hw : 0 ≤ w K := by unfold w; positivity
  unfold a
  linarith [mul_nonneg (sub_nonneg.mpr hjr) hw]

private theorem endpoint_le_half {K j : ℕ} (hK : 0 < K) (hj : j ≤ K) :
    a K j + w K ≤ 1 / 2 := by
  have hjr : (j : ℝ) ≤ K := by exact_mod_cast hj
  have hmul := mul_le_mul_of_nonneg_right hjr (w_pos hK).le
  unfold a
  linarith [cast_mul_w hK]

private theorem I_subset {K j : ℕ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ K) :
    I K j ⊆ Set.Ioo (1 / 4 : ℝ) (1 / 2) := by
  have hK : 0 < K := lt_of_lt_of_le (by decide : 0 < 1) (hj₁.trans hj₂)
  intro q hq
  exact ⟨(a_ge_quarter hj₁).trans_lt hq.1, hq.2.trans_le (endpoint_le_half hK hj₂)⟩

private theorem qstar_mem {K j : ℕ} (hK : 0 < K) : qstar K j ∈ I K j := by
  have hw := w_pos hK
  change a K j < a K j + w K / 2 ∧ a K j + w K / 2 < a K j + w K
  exact ⟨by linarith, by linarith⟩

private theorem normalized_qstar {K j : ℕ} (hK : 0 < K) : (qstar K j - a K j) / w K = 1 / 2 := by
  unfold qstar
  apply (div_eq_iff (w_pos hK).ne').mpr
  ring

private theorem I_pairwiseDisjoint (K : ℕ) : Pairwise (fun i j => Disjoint (I K i) (I K j)) := by
  intro i j hij
  have hw : 0 ≤ w K := by unfold w; positivity
  suffices ordered : ∀ {k l : ℕ}, k < l → Disjoint (I K k) (I K l) by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ordered h
    · exact (ordered h).symm
  intro k l hkl
  have hcast : (k : ℝ) + 1 ≤ l := by exact_mod_cast hkl
  have hmul := mul_le_mul_of_nonneg_right (show (k : ℝ) ≤ l - 1 by linarith) hw
  apply Set.disjoint_left.mpr
  intro q hk hl
  have hkq : q < a K k + w K := hk.2
  have hql : a K l < q := hl.1
  unfold a at hkq hql
  nlinarith

open Classical in
private theorem sum_interval_visits_le (K T : ℕ) (s : Finset ℕ) (q : Fin T → ℝ) :
    ∑ j ∈ s, (Finset.univ.filter fun t => q t ∈ I K j).card ≤ T := by
  let visits (j : ℕ) := Finset.univ.filter fun t => q t ∈ I K j
  have hd : (s : Set ℕ).PairwiseDisjoint visits := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun t hi hj => ?_
    exact Set.disjoint_left.mp (I_pairwiseDisjoint K hij)
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  change ∑ j ∈ s, (visits j).card ≤ T
  rw [← Finset.card_biUnion hd]
  simpa using Finset.card_le_univ (s.biUnion visits)

private theorem Delta_eq {K : ℕ} (hK : 0 < K) : Delta K = 1 / (73728 * (K : ℝ) ^ 2) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold Delta w
  field_simp
  ring

private theorem Delta_pos {K : ℕ} (hK : 0 < K) : 0 < Delta K := by
  have hw := w_pos hK
  unfold Delta
  positivity

open Classical in
private theorem sum_outside_interval_gap (K j T : ℕ) (q : Fin T → ℝ) :
    (∑ t : Fin T, Set.indicator (I K j)ᶜ (fun _ => Delta K) (q t)) =
      ((T : ℝ) - ((Finset.univ.filter fun t => q t ∈ I K j).card : ℝ)) * Delta K := by
  have hi (t : Fin T) : Set.indicator (I K j)ᶜ (fun _ => Delta K) (q t) =
      Delta K - if q t ∈ I K j then Delta K else 0 := by
    by_cases ht : q t ∈ I K j
    · simp [Set.indicator, ht]
    · simp [Set.indicator, ht]
  simp_rw [hi]
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter]
  simp [nsmul_eq_mul, sub_mul]

end BilateralProfitLB
end BundlePart001


section BundlePart002


namespace BilateralProfitLB

/-- Ceiling the fifth root gives enough alternatives for information control and a gap of
order `T ^ (-2/5)`. -/
private theorem exists_lower_bound_width (T : ℕ) (hT : 33 ≤ T) :
    ∃ K : ℕ, 3 ≤ K ∧ (T : ℝ) ≤ (K : ℝ) ^ 5 ∧
      (1 / 589824 : ℝ) * (T : ℝ) ^ ((3 : ℝ) / 5) ≤ (T : ℝ) * Delta K / 2 := by
  have ht : (33 : ℝ) ≤ T := by exact_mod_cast hT
  have htpos : (0 : ℝ) < T := by linarith
  let x : ℝ := (T : ℝ) ^ ((1 : ℝ) / 5)
  have hx : 0 ≤ x := (Real.rpow_pos_of_pos htpos _).le
  have hxpow : x ^ 5 = T := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul htpos.le]
    norm_num
  have hx2 : 2 < x := by
    by_contra! hx2
    have hp := pow_le_pow_left₀ hx hx2 5
    rw [hxpow] at hp
    norm_num at hp
    linarith
  let K : ℕ := ⌈x⌉₊
  have hxK : x ≤ (K : ℝ) := Nat.le_ceil x
  have hk2 : 2 < K := by exact_mod_cast (hx2.trans_le hxK)
  have hk : 0 < K := by omega
  have hKx : (K : ℝ) ≤ 2 * x := by
    have hceil : (K : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
    linarith
  refine ⟨K, hk2, ?_, ?_⟩
  · calc
      (T : ℝ) = x ^ 5 := hxpow.symm
      _ ≤ (K : ℝ) ^ 5 := pow_le_pow_left₀ hx hxK 5
  have hscale : (T : ℝ) ^ ((3 : ℝ) / 5) * x ^ 2 = T := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul htpos.le, ← Real.rpow_add htpos]
    norm_num
  have hK0 : 0 ≤ (K : ℝ) := by positivity
  have hweight : (T : ℝ) ^ ((3 : ℝ) / 5) * (K : ℝ) ^ 2 ≤ 4 * T := by
    calc
      _ ≤ (T : ℝ) ^ ((3 : ℝ) / 5) * (2 * x) ^ 2 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hK0 hKx 2) (by positivity)
      _ = 4 * ((T : ℝ) ^ ((3 : ℝ) / 5) * x ^ 2) := by ring
      _ = 4 * T := by rw [hscale]
  rw [Delta_eq hk, show (T : ℝ) * (1 / (73728 * (K : ℝ) ^ 2)) / 2 =
    (T : ℝ) / (147456 * (K : ℝ) ^ 2) by ring]
  apply (le_div_iff₀ (by positivity)).2
  nlinarith only [hweight]

/-- If the total number of baseline visits is at most `T`, the per-alternative information
bound forces at least one alternative to have at most `T/2` expected visits. -/
private theorem exists_count_le_half {ι : Type*} {s : Finset ι} {K : ℕ} {T : ℝ}
    (hs : s.card = K) (hK : 3 ≤ K) (hT : 0 < T) (hTK : T ≤ (K : ℝ) ^ 5)
    (count₀ count₁ : ι → ℝ) (hcount₀ : ∀ j, 0 ≤ count₀ j)
    (hcountsum : ∑ j ∈ s, count₀ j ≤ T)
    (hinfo : ∀ j ∈ s, count₁ j - count₀ j ≤
      T / (22 * (K : ℝ) ^ 2) * Real.sqrt (count₀ j)) :
    ∃ j ∈ s, count₁ j ≤ T / 2 := by
  have hKr : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hsqrt : ∑ j ∈ s, Real.sqrt (count₀ j) ≤ (K : ℝ) ^ 3 := by
    calc
      _ ≤ Real.sqrt (∑ j ∈ s, count₀ j) * Real.sqrt (K : ℝ) := by
        simpa [hs] using Real.sum_sqrt_mul_sqrt_le s hcount₀ (fun _ => (zero_le_one : (0 : ℝ) ≤ 1))
      _ ≤ Real.sqrt T * Real.sqrt (K : ℝ) := by
        exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcountsum) (Real.sqrt_nonneg _)
      _ = Real.sqrt (T * (K : ℝ)) := (Real.sqrt_mul hT.le _).symm
      _ ≤ Real.sqrt (((K : ℝ) ^ 3) ^ 2) := by
        apply Real.sqrt_le_sqrt
        calc
          _ ≤ (K : ℝ) ^ 5 * K := mul_le_mul_of_nonneg_right hTK hKpos.le
          _ = ((K : ℝ) ^ 3) ^ 2 := by ring
      _ = (K : ℝ) ^ 3 := Real.sqrt_sq (by positivity)
  have hsum : ∑ j ∈ s, count₁ j < (K : ℝ) * (T / 2) := by
    calc
      _ ≤ ∑ j ∈ s, (count₀ j + T / (22 * (K : ℝ) ^ 2) * Real.sqrt (count₀ j)) := by
        apply Finset.sum_le_sum
        intro j hj
        linarith [hinfo j hj]
      _ = (∑ j ∈ s, count₀ j) + T / (22 * (K : ℝ) ^ 2) * ∑ j ∈ s, Real.sqrt (count₀ j) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ T + T / (22 * (K : ℝ) ^ 2) * (K : ℝ) ^ 3 := by
        exact add_le_add hcountsum (mul_le_mul_of_nonneg_left hsqrt (by positivity))
      _ = T + T * K / 22 := by field_simp
      _ < (K : ℝ) * (T / 2) := by nlinarith [mul_nonneg (sub_nonneg.mpr hKr) hT.le]
  by_contra! hall
  have hle : (∑ _j ∈ s, T / 2) ≤ ∑ j ∈ s, count₁ j :=
    Finset.sum_le_sum fun j hj => (hall j hj).le
  rw [Finset.sum_const, nsmul_eq_mul, hs] at hle
  exact (not_le_of_gt hsum) hle

end BilateralProfitLB
end BundlePart002


section BundlePart003


noncomputable section

namespace BilateralProfitLB

open MeasureTheory ProbabilityTheory Set BilateralProfit
open scoped ProbabilityTheory ENNReal

private abbrev FeedbackPair := Bool × Bool
private abbrev Valuation := ℝ × ℝ
private abbrev Tape (n : ℕ) := Fin n → Valuation
private abbrev PrefixState (Ω : Type) (n : ℕ) := Ω × (Fin n → FeedbackPair)

variable {Ω : Type} [MeasurableSpace Ω]

private theorem measurable_feedback : Measurable (fun x : Valuation × Valuation => feedback x.1 x.2) := by
  classical
  have h {f g : Valuation × Valuation → ℝ} (hf : Measurable f) (hg : Measurable g) :
      Measurable fun x => decide (f x ≤ g x) := by
    have he : (fun x => decide (f x ≤ g x)) =
        (fun x => if x ∈ {z | f z ≤ g z} then true else false) := by
      funext x
      by_cases hx : f x ≤ g x <;> simp [hx]
    rw [he]
    exact measurable_const.ite (measurableSet_le hf hg) measurable_const
  exact (h (measurable_fst.comp measurable_fst) (measurable_fst.comp measurable_snd)).prodMk
    (h (measurable_snd.comp measurable_snd) (measurable_snd.comp measurable_fst))

private def protocolPrice (π : Policy Ω) {n : ℕ} (z : PrefixState Ω n) : ℝ × ℝ :=
  π.price z.1 (List.ofFn z.2)

private theorem protocolPrice_measurable (π : Policy Ω) (n : ℕ) :
    Measurable (protocolPrice π : PrefixState Ω n → ℝ × ℝ) :=
  measurable_from_prod_countable_left fun h => π.price_measurable (List.ofFn h)

private theorem protocolPrice_mem (π : Policy Ω) {n : ℕ} (z : PrefixState Ω n) :
    protocolPrice π z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
  π.price_mem z.1 (List.ofFn z.2)

private theorem measurable_feedback_at (π : Policy Ω) (n : ℕ) :
    Measurable fun z : PrefixState Ω n × Valuation => feedback z.2 (protocolPrice π z.1) :=
  measurable_feedback.comp (measurable_snd.prodMk ((protocolPrice_measurable π n).comp measurable_fst))

private def protocolUpdate (n : ℕ) (x : PrefixState Ω n × FeedbackPair) : PrefixState Ω (n + 1) :=
  (x.1.1, Fin.snoc x.1.2 x.2)

private theorem protocolUpdate_measurable (n : ℕ) :
    Measurable (protocolUpdate n : PrefixState Ω n × FeedbackPair → _) := by
  apply (measurable_fst.comp measurable_fst).prodMk
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [protocolUpdate] using (measurable_snd :
      Measurable (Prod.snd : PrefixState Ω n × FeedbackPair → FeedbackPair))
  · simpa [protocolUpdate, Function.comp_def] using
      (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)

private def protocolHistory (π : Policy Ω) :
    (n : ℕ) → Ω → Tape n → Fin n → FeedbackPair
  | 0, _, _ => Fin.elim0
  | n+1, ω, v =>
      let h := protocolHistory π n ω (Fin.init v)
      Fin.snoc h (feedback (v (Fin.last n)) (protocolPrice π (ω, h)))

private def prefixState (π : Policy Ω) (n : ℕ) (x : Ω × Tape n) : PrefixState Ω n :=
  (x.1, protocolHistory π n x.1 x.2)

private def valuationPrefix {m n : ℕ} (h : m ≤ n) (v : Tape n) : Tape m :=
  fun i => v (i.castLE h)

private theorem valuationPrefix_measurable {m n : ℕ} (h : m ≤ n) :
    Measurable (valuationPrefix h : Tape n → Tape m) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (i.castLE h)

private theorem prefixState_measurable (π : Policy Ω) (n : ℕ) :
    Measurable (prefixState π n) := by
  induction n with
  | zero => exact measurable_fst.prodMk measurable_const
  | succ n ih =>
    have hprev : Measurable fun x : Ω × Tape (n+1) => prefixState π n (x.1, Fin.init x.2) :=
      ih.comp (measurable_fst.prodMk ((valuationPrefix_measurable (Nat.le_succ n)).comp measurable_snd))
    have hfresh : Measurable fun x : Ω × Tape (n+1) => x.2 (Fin.last n) :=
      (measurable_pi_apply (Fin.last n)).comp measurable_snd
    exact (protocolUpdate_measurable n).comp (hprev.prodMk
      ((measurable_feedback_at π n).comp (hprev.prodMk hfresh)))

private theorem protocolHistory_eq_hist (π : Policy Ω) {T : ℕ} (ω : Ω) (v : Tape T)
    (n : ℕ) (hn : n ≤ T) :
    List.ofFn (protocolHistory π n ω (valuationPrefix hn v)) = hist π ω v n := by
  induction n with
  | zero => simp [protocolHistory, hist]
  | succ n ih =>
    have hn' := Nat.le_of_succ_le hn
    have ht := Nat.lt_of_succ_le hn
    have hinit : Fin.init (valuationPrefix hn v) = valuationPrefix hn' v := rfl
    rw [hist, dif_pos ht, protocolHistory, hinit, List.ofFn_succ_last]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, protocolPrice, ih hn']
    rfl

private theorem protocolPrice_eq_act (π : Policy Ω) {T : ℕ} (x : Ω × Tape T) (t : Fin T) :
    protocolPrice π (prefixState π t (x.1, valuationPrefix t.isLt.le x.2)) = act π x.1 x.2 t := by
  simp only [protocolPrice, prefixState, act, protocolHistory_eq_hist]

private theorem tape_split_preserving (D : Measure Valuation) [IsProbabilityMeasure D] (n : ℕ) :
    MeasurePreserving (fun v : Tape (n+1) => (Fin.init v, v (Fin.last n)))
      (Measure.pi fun _ : Fin (n+1) => D)
      ((Measure.pi fun _ : Fin n => D).prod D) := by
  have h := (Measure.measurePreserving_swap (μ := D) (ν := Measure.pi fun _ : Fin n => D)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => D) (Fin.last n))
  refine h.congr ((valuationPrefix_measurable (Nat.le_succ n)).prodMk
    (measurable_pi_apply (Fin.last n))) ?_
  filter_upwards with v
  simp [Function.comp_def, MeasurableEquiv.piFinSuccAbove_apply, Fin.init]

private theorem valuationPrefix_preserving (D : Measure Valuation) [IsProbabilityMeasure D]
    {m n : ℕ} (h : m ≤ n) :
    MeasurePreserving (valuationPrefix h)
      (Measure.pi fun _ : Fin n => D) (Measure.pi fun _ : Fin m => D) := by
  induction h with
  | refl =>
    refine (MeasurePreserving.id _).congr (valuationPrefix_measurable _) ?_
    filter_upwards with v
    rfl
  | @step n h ih =>
    have hf : MeasurePreserving Prod.fst ((Measure.pi fun _ : Fin n => D).prod D)
        (Measure.pi fun _ : Fin n => D) :=
      ⟨measurable_fst, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩
    refine (ih.comp (hf.comp (tape_split_preserving D n))).congr
      (valuationPrefix_measurable _) ?_
    filter_upwards with v
    rfl

private theorem run_prefix_preserving (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure Valuation)
    [IsProbabilityMeasure D] {m n : ℕ} (h : m ≤ n) :
    MeasurePreserving (fun x : Ω × Tape n => (x.1, valuationPrefix h x.2))
      (runMeasure P D n) (runMeasure P D m) :=
  (MeasurePreserving.id P).prod (valuationPrefix_preserving D h)

private theorem run_split_preserving (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure Valuation)
    [IsProbabilityMeasure D] (n : ℕ) :
    MeasurePreserving (fun x : Ω × Tape (n+1) => ((x.1, Fin.init x.2), x.2 (Fin.last n)))
      (runMeasure P D (n+1)) ((runMeasure P D n).prod D) := by
  have h := (measurePreserving_prodAssoc P (Measure.pi fun _ : Fin n => D) D).symm
  exact h.comp ((MeasurePreserving.id P).prod (tape_split_preserving D n))

private def prefixLaw (π : Policy Ω) (P : Measure Ω) (D : Measure Valuation) (n : ℕ) :
    Measure (PrefixState Ω n) :=
  (runMeasure P D n).map (prefixState π n)

private theorem prefixState_preserving (π : Policy Ω) (P : Measure Ω) (D : Measure Valuation)
    (n : ℕ) : MeasurePreserving (prefixState π n) (runMeasure P D n) (prefixLaw π P D n) :=
  ⟨prefixState_measurable π n, rfl⟩

private instance prefixLaw_probability (π : Policy Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure Valuation) [IsProbabilityMeasure D] (n : ℕ) :
    IsProbabilityMeasure (prefixLaw π P D n) := by
  letI : IsProbabilityMeasure (runMeasure P D n) := by unfold runMeasure; infer_instance
  exact Measure.isProbabilityMeasure_map (prefixState_measurable π n).aemeasurable

private theorem prefixLaw_zero_same (π : Policy Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D D' : Measure Valuation) [IsProbabilityMeasure D] [IsProbabilityMeasure D'] :
    prefixLaw π P D 0 = prefixLaw π P D' 0 := by
  have he (v : Tape 0) : v = Fin.elim0 := Subsingleton.elim _ _
  have hD (μ : Measure Valuation) [IsProbabilityMeasure μ] :
      Measure.pi (fun _ : Fin 0 => μ) = Measure.dirac (Fin.elim0 : Tape 0) := by
    ext s hs
    by_cases h : (Fin.elim0 : Tape 0) ∈ s
    · have hu : s = univ := by ext v; simp [he v, h]
      simp [hu]
    · have hz : s = ∅ := by ext v; simp [he v, h]
      simp [hz]
  simp only [prefixLaw, runMeasure, hD]

private def feedbackKernel (π : Policy Ω) (D : Measure Valuation) (n : ℕ) :
    Kernel (PrefixState Ω n) FeedbackPair :=
  (Kernel.id ×ₖ Kernel.const _ D).map (fun z => feedback z.2 (protocolPrice π z.1))

private instance feedbackKernel_markov (π : Policy Ω) (D : Measure Valuation) [IsProbabilityMeasure D]
    (n : ℕ) : IsMarkovKernel (feedbackKernel π D n) := by
  exact Kernel.IsMarkovKernel.map _ (measurable_feedback_at π n)

private theorem feedbackKernel_apply (π : Policy Ω) (D : Measure Valuation) [IsProbabilityMeasure D]
    (n : ℕ) (z : PrefixState Ω n) :
    feedbackKernel π D n z = D.map (fun v => feedback v (protocolPrice π z)) := by
  rw [feedbackKernel, Kernel.map_apply _ (measurable_feedback_at π n)]
  ext s hs
  have hsec : Measurable fun v => feedback v (protocolPrice π z) :=
    (measurable_feedback_at π n).comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply (measurable_feedback_at π n) hs,
    Kernel.id_prod_apply' _ _ ((measurable_feedback_at π n) hs), Kernel.const_apply,
    Measure.map_apply hsec hs]
  rfl

private theorem prefix_fresh_preserving (π : Policy Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure Valuation) [IsProbabilityMeasure D] {n T : ℕ} (hn : n+1 ≤ T) :
    MeasurePreserving
      (fun x : Ω × Tape T =>
        (prefixState π n (x.1, valuationPrefix (Nat.le_of_succ_le hn) x.2),
         x.2 ⟨n, Nat.lt_of_succ_le hn⟩))
      (runMeasure P D T) ((prefixLaw π P D n).prod D) := by
  letI : IsProbabilityMeasure (runMeasure P D n) := by unfold runMeasure; infer_instance
  exact ((prefixState_preserving π P D n).prod (MeasurePreserving.id D)).comp
    ((run_split_preserving P D n).comp (run_prefix_preserving P D hn))

private theorem prefixLaw_succ (π : Policy Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure Valuation) [IsProbabilityMeasure D] (n : ℕ) :
    prefixLaw π P D (n + 1) =
      ((prefixLaw π P D n) ⊗ₘ (feedbackKernel π D n)).map (protocolUpdate n) := by
  let ν := prefixLaw π P D n
  let F : PrefixState Ω n × Valuation → PrefixState Ω n × FeedbackPair :=
    fun z => (z.1, feedback z.2 (protocolPrice π z.1))
  have hF : Measurable F := measurable_fst.prodMk (measurable_feedback_at π n)
  have hmap : (ν.prod D).map F = ν ⊗ₘ feedbackKernel π D n := by
    ext s hs
    rw [Measure.map_apply hF hs, Measure.prod_apply (hF hs), Measure.compProd_apply hs]
    apply lintegral_congr
    intro z
    have hsec : Measurable fun v => feedback v (protocolPrice π z) :=
      (measurable_feedback_at π n).comp (measurable_const.prodMk measurable_id)
    rw [feedbackKernel_apply, Measure.map_apply hsec (measurable_prodMk_left hs)]
    rfl
  rw [← hmap, Measure.map_map (protocolUpdate_measurable n) hF]
  have hp := prefix_fresh_preserving π P D (le_refl (n+1))
  rw [← hp.map_eq, Measure.map_map ((protocolUpdate_measurable n).comp hF) hp.measurable]
  rfl

end BilateralProfitLB
end
end BundlePart003


section BundlePart004



open MeasureTheory Set

namespace BilateralProfitLB

variable {Ω : Type} [MeasurableSpace Ω]

private def visitEvent (π : Policy Ω) {T : ℕ} (t : Fin T) (J : Set ℝ) : Set (Ω × Tape T) :=
  {x | (act π x.1 x.2 t).2 ∈ J}

private theorem measurePreserving_before_round (π : Policy Ω) (P : Measure Ω)
    [IsProbabilityMeasure P] (D : Measure Valuation) [IsProbabilityMeasure D]
    {T : ℕ} (t : Fin T) :
    MeasurePreserving
      (fun x : Ω × Tape T => prefixState π t (x.1, valuationPrefix t.isLt.le x.2))
      (runMeasure P D T) (prefixLaw π P D t) :=
  (prefixState_preserving π P D t).comp (run_prefix_preserving P D t.isLt.le)

private theorem visitEvent_measurable (π : Policy Ω) {T : ℕ} (t : Fin T)
    {J : Set ℝ} (hJ : MeasurableSet J) : MeasurableSet (visitEvent π t J) := by
  have hm := (protocolPrice_measurable π t).comp
    ((prefixState_measurable π t).comp
      (measurable_fst.prodMk ((valuationPrefix_measurable t.isLt.le).comp measurable_snd)))
  have he : visitEvent π t J =
      (fun x : Ω × Tape T => (protocolPrice π
        (prefixState π t (x.1, valuationPrefix t.isLt.le x.2))).2) ⁻¹' J := by
    ext x
    simp only [visitEvent, mem_ofPred_eq, mem_preimage, protocolPrice_eq_act]
  rw [he]
  exact hm.snd hJ

private theorem visitEvent_real (π : Policy Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure Valuation) [IsProbabilityMeasure D] {T : ℕ} (t : Fin T)
    {J : Set ℝ} (hJ : MeasurableSet J) :
    (runMeasure P D T).real (visitEvent π t J) =
      (prefixLaw π P D t).real {z | (protocolPrice π z).2 ∈ J} := by
  have hp := measurePreserving_before_round π P D t
  have hs : MeasurableSet {z : PrefixState Ω t | (protocolPrice π z).2 ∈ J} :=
    (protocolPrice_measurable π t).snd hJ
  have he : visitEvent π t J =
      (fun x : Ω × Tape T => prefixState π t (x.1, valuationPrefix t.isLt.le x.2)) ⁻¹'
        {z | (protocolPrice π z).2 ∈ J} := by
    ext x
    simp only [visitEvent, mem_ofPred_eq, mem_preimage, protocolPrice_eq_act]
  rw [he, ← hp.map_eq, Measure.real, Measure.real, Measure.map_apply hp.measurable hs]

open Classical in
private noncomputable def visitCount (π : Policy Ω) {T : ℕ} (J : Set ℝ) (x : Ω × Tape T) : ℝ :=
  ((Finset.univ.filter fun t : Fin T => (act π x.1 x.2 t).2 ∈ J).card : ℝ)

private theorem visitCount_eq_sum (π : Policy Ω) {T : ℕ} (J : Set ℝ) (x : Ω × Tape T) :
    visitCount π J x = ∑ t : Fin T, (visitEvent π t J).indicator (fun _ => (1 : ℝ)) x := by
  classical
  unfold visitCount
  rw [← Finset.sum_boole (R := ℝ)]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : (act π x.1 x.2 t).2 ∈ J <;> simp [Set.indicator, visitEvent, ht]

private theorem visitCount_integrable (π : Policy Ω) (P : Measure Ω) (D : Measure Valuation)
    {T : ℕ} [IsFiniteMeasure (runMeasure P D T)] {J : Set ℝ} (hJ : MeasurableSet J) :
    Integrable (visitCount π (T := T) J) (runMeasure P D T) := by
  simp only [funext (visitCount_eq_sum π (T := T) J)]
  exact integrable_finsetSum _ fun t _ =>
    (integrable_const (1 : ℝ)).indicator (visitEvent_measurable π t hJ)

private theorem expCount_nonneg (π : Policy Ω) (P : Measure Ω) (D : Measure Valuation) (T : ℕ)
    (J : Set ℝ) : 0 ≤ expCount π P D T J := by
  unfold expCount
  exact integral_nonneg fun _ => Nat.cast_nonneg _

/-- The expected count is the sum of the event probabilities under the pre-round prefix laws. -/
private theorem expCount_eq_sum_prefix (π : Policy Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure Valuation) [IsProbabilityMeasure D] (T : ℕ) (J : Set ℝ)
    (hJ : MeasurableSet J) :
    expCount π P D T J =
      ∑ t ∈ Finset.range T, (prefixLaw π P D t).real {z | (protocolPrice π z).2 ∈ J} := by
  have hr : IsProbabilityMeasure (runMeasure P D T) := by unfold runMeasure; infer_instance
  change (∫ x, visitCount π J x ∂(runMeasure P D T)) = _
  simp only [visitCount_eq_sum π J, ← Fin.sum_univ_eq_sum_range]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro t _
    exact (integral_indicator_one (μ := runMeasure P D T) (visitEvent_measurable π t hJ)).trans
      (visitEvent_real π P D t hJ)
  · intro t _
    exact (integrable_const (1 : ℝ)).indicator (visitEvent_measurable π t hJ)

/-- The disjoint perturbation intervals together receive at most one visit per round. -/
private theorem sum_expCount_le (π : Policy Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure Valuation) [IsProbabilityMeasure D] (K T : ℕ) (s : Finset ℕ) :
    ∑ j ∈ s, expCount π P D T (I K j) ≤ (T : ℝ) := by
  have hr : IsProbabilityMeasure (runMeasure P D T) := by unfold runMeasure; infer_instance
  have hi (j : ℕ) : Integrable (visitCount π (T := T) (I K j)) (runMeasure P D T) :=
    visitCount_integrable π P D measurableSet_Ioo
  change (∑ j ∈ s, ∫ x, visitCount π (I K j) x ∂(runMeasure P D T)) ≤ _
  rw [← integral_finsetSum _ (fun j _ => hi j)]
  calc
    _ ≤ ∫ (_ : Ω × Tape T), (T : ℝ) ∂(runMeasure P D T) := by
      refine integral_mono (integrable_finsetSum _ (fun j _ => hi j)) (integrable_const _) ?_
      intro x
      classical
      simpa only [visitCount, Nat.cast_sum] using
        (show ((∑ j ∈ s, (Finset.univ.filter fun t => (act π x.1 x.2 t).2 ∈ I K j).card : ℕ) : ℝ)
          ≤ (T : ℝ) by exact_mod_cast sum_interval_visits_le K T s (fun t => (act π x.1 x.2 t).2))
    _ = _ := by simp

end BilateralProfitLB
end BundlePart004


section BundlePart005







noncomputable section

namespace BilateralProfitLB

open MeasureTheory MechanismDesign.BilateralTrade Set

private theorem theorem_7_1_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (π : Policy Ω),
        ∃ E : Environment, UnitSupport E ∧ E.Regular ∧
          ∃ a ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
            c * (T : ℝ) ^ ((3 : ℝ) / 5) ≤ regret π P E.prior T a := by
  refine ⟨1/589824, by norm_num, 33, ?_⟩
  intro T hT Ω _ P _ π
  obtain ⟨K, hK, hTK, hRate⟩ := exists_lower_bound_width T hT
  have hK1 : 1 ≤ K := by omega
  have hD0 : IsProbabilityMeasure (law K 0) :=
    law_isProbabilityMeasure_of_claim_7_3 claim_7_3 hK1 (Nat.zero_le K)
  let s : Finset ℕ := Finset.Icc 1 K
  have hs : s.card = K := by simp [s, Nat.card_Icc]
  let count₀ := fun j => expCount π P (law K 0) T (I K j)
  let count₁ := fun j => expCount π P (law K j) T (I K j)
  have hInfo (j : ℕ) (hj : j ∈ s) :
      count₁ j - count₀ j ≤ (T : ℝ) / (22 * (K : ℝ) ^ 2) * Real.sqrt (count₀ j) := by
    obtain ⟨hj1, hjK⟩ := Finset.mem_Icc.mp hj
    exact expCount_transfer_randomized K hK1 j hj1 hjK T Ω P π
  have hTr : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  obtain ⟨j, hj, hCount⟩ := exists_count_le_half hs hK hTr hTK count₀ count₁
    (fun j => expCount_nonneg π P (law K 0) T (I K j))
    (sum_expCount_le π P (law K 0) K T s) hInfo
  obtain ⟨hj1, hjK⟩ := Finset.mem_Icc.mp hj
  obtain ⟨E, hE, _, _, _, hPrior, hRegular⟩ := claim_7_3 K hK1 j hjK
  obtain ⟨a, ha, hRegret⟩ := regret_display K hK1 j hj1 hjK T Ω P π
  refine ⟨E, hE, hRegular, a, ha, ?_⟩
  rw [hPrior]
  have hGap : (T : ℝ) / 2 ≤ (T : ℝ) - count₁ j := by linarith
  calc
    _ ≤ (T : ℝ) * Delta K / 2 := hRate
    _ = ((T : ℝ) / 2) * Delta K := by ring
    _ ≤ ((T : ℝ) - count₁ j) * Delta K :=
      mul_le_mul_of_nonneg_right hGap (Delta_pos (show 0 < K from hK1)).le
    _ ≤ _ := hRegret


end BilateralProfitLB
end
end BundlePart005

open BilateralProfitLB
open MeasureTheory MechanismDesign.BilateralTrade

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (π : Policy Ω),
        ∃ E : Environment, UnitSupport E ∧ E.Regular ∧
          ∃ a ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
            c * (T : ℝ) ^ ((3 : ℝ) / 5) ≤ regret π P E.prior T a := by
  exact BilateralProfitLB.theorem_7_1_lower_bound
