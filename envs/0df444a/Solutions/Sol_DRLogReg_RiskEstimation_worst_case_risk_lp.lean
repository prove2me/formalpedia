-- Prove2me | solution 1 for DRLogReg.RiskEstimation.worst_case_risk_lp
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T15:43:35.039567+00:00
-- url     : https://prove2.me/submissions/fa0dbac0-edb4-4dd2-85d9-4253fd0a0928

import Mathlib
import Definitions.Def_DRLogReg_RiskEstimation_Core
import Definitions.Def_DRLogReg_RiskEstimation_Risk
import Definitions.Def_DRLogReg_RiskEstimation_Program

set_option autoImplicit false

open Finset in
theorem dr36_knap {N : ℕ} (hN : 0 < N) (c : Fin N → ℝ) (_hc : ∀ i, 0 ≤ c i) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∃ p : Fin N → ℝ, (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧
      ∑ i, p i * c i ≤ N * ε ∧ N * (lam * ε) + ∑ i, max 0 (1 - lam * c i) ≤ ∑ i, p i := by
  have hNe : 0 ≤ (N : ℝ) * ε := mul_nonneg (Nat.cast_nonneg N) hε
  by_cases h1 : ∑ i, c i ≤ N * ε
  · refine ⟨0, le_rfl, fun _ => 1, fun i => ⟨zero_le_one, le_rfl⟩, by simpa using h1, ?_⟩
    simp
  push Not at h1
  set T := univ.filter (fun j => (N : ℝ) * ε < ∑ i ∈ univ.filter (fun i => c i ≤ c j), c i)
    with hTdef
  have hT : T.Nonempty := by
    obtain ⟨j, -, hj⟩ := exists_max_image univ c (univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
    refine ⟨j, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    rwa [filter_true_of_mem (fun i _ => hj i (mem_univ _))]
  obtain ⟨j0, hj0T, hj0min⟩ := exists_min_image T c hT
  set τ := c j0 with hτdef
  have hj0' : (N : ℝ) * ε < ∑ i ∈ univ.filter (fun i => c i ≤ τ), c i := (mem_filter.mp hj0T).2
  have hτpos : 0 < τ := by
    by_contra h
    push Not at h
    have : ∑ i ∈ univ.filter (fun i => c i ≤ τ), c i ≤ 0 :=
      sum_nonpos (fun i hi => le_trans (mem_filter.mp hi).2 h)
    linarith
  have hSlt : ∑ i ∈ univ.filter (fun i => c i < τ), c i ≤ N * ε := by
    by_contra h
    push Not at h
    have hne : (univ.filter (fun i => c i < τ)).Nonempty := by
      by_contra h'
      rw [not_nonempty_iff_eq_empty] at h'
      rw [h', sum_empty] at h
      linarith
    obtain ⟨k, hk, hkmax⟩ := exists_max_image _ c hne
    have hkτ : c k < τ := (mem_filter.mp hk).2
    have heq : univ.filter (fun i => c i ≤ c k) = univ.filter (fun i => c i < τ) := by
      ext i
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro hi; exact lt_of_le_of_lt hi hkτ
      · intro hi; exact hkmax i (mem_filter.mpr ⟨mem_univ _, hi⟩)
    have hkT : k ∈ T := mem_filter.mpr ⟨mem_univ _, by rw [heq]; exact h⟩
    exact absurd (hj0min k hkT) (not_le.mpr hkτ)
  set SL := ∑ i ∈ univ.filter (fun i => c i < τ), c i with hSLdef
  set nE : ℝ := ∑ i, if c i = τ then (1:ℝ) else 0 with hnEdef
  have hsplit : ∑ i ∈ univ.filter (fun i => c i ≤ τ), c i = SL + τ * nE := by
    rw [hSLdef, hnEdef, sum_filter, sum_filter, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rcases lt_trichotomy (c i) τ with h | h | h
    · simp [h, h.le, h.ne]
    · simp [h]
    · simp [not_le.mpr h, not_lt.mpr h.le, h.ne']
  have hnEpos : 0 < nE := by
    have : 0 < τ * nE := by linarith
    exact pos_of_mul_pos_right this hτpos.le
  have htn : 0 < τ * nE := mul_pos hτpos hnEpos
  set θ := ((N : ℝ) * ε - SL) / (τ * nE) with hθdef
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) htn.le
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one htn]; linarith
  have hθτ : θ * (τ * nE) = N * ε - SL := by
    rw [hθdef]; field_simp
  set p : Fin N → ℝ := fun i => if c i < τ then 1 else if c i = τ then θ else 0 with hpdef
  have hcost : ∑ i, p i * c i = N * ε := by
    have : ∀ i, p i * c i = (if c i < τ then c i else 0) + θ * τ * (if c i = τ then 1 else 0) := by
      intro i
      rcases lt_trichotomy (c i) τ with h | h | h
      · simp [hpdef, h, h.ne]
      · simp [hpdef, h]
      · simp [hpdef, not_lt.mpr h.le, h.ne']
    rw [sum_congr rfl (fun i _ => this i), sum_add_distrib, ← sum_filter, ← mul_sum]
    rw [← hSLdef, ← hnEdef]
    linarith [hθτ]
  refine ⟨τ⁻¹, inv_nonneg.mpr hτpos.le, p, ?_, hcost.le, ?_⟩
  · intro i
    simp only [hpdef]
    split_ifs <;> constructor <;> linarith
  · have hNε : (N : ℝ) * (τ⁻¹ * ε) = ∑ i, τ⁻¹ * (p i * c i) := by
      rw [← mul_sum, hcost]; ring
    rw [hNε, ← sum_add_distrib]
    apply sum_le_sum
    intro i _
    rcases lt_trichotomy (c i) τ with h | h | h
    · have hlt : τ⁻¹ * c i < 1 := by
        rw [inv_mul_lt_iff₀ hτpos]; linarith
      simp only [hpdef, if_pos h]
      rw [max_eq_right (by linarith)]
      linarith
    · simp only [hpdef, h, lt_irrefl, if_false, if_true]
      rw [show τ⁻¹ * τ = 1 from inv_mul_cancel₀ hτpos.ne']
      simp
      field_simp
      rfl
    · have hgt : 1 < τ⁻¹ * c i := by
        rw [lt_inv_mul_iff₀ hτpos]; linarith
      simp only [hpdef, if_neg (not_lt.mpr h.le), if_neg h.ne']
      rw [max_eq_left (by linarith)]
      simp

open DRLogReg.RiskEstimation in
theorem dr36_abs_sgn (y : Bool) : |sgn y| = 1 := by cases y <;> simp [sgn]

open DRLogReg.RiskEstimation in
theorem dr36_sgn_sq (y : Bool) : sgn y * sgn y = 1 := by cases y <;> simp [sgn]

open DRLogReg.RiskEstimation in
theorem dr36_dist_self {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (κ : ℝ)
    (ξ : V × Bool) : featureLabelDist κ ξ ξ = 0 := by
  simp [featureLabelDist]

open DRLogReg.RiskEstimation in
theorem dr36_dist_nonneg {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ : ℝ}
    (hκ : 0 ≤ κ) (ξ ξ' : V × Bool) : 0 ≤ featureLabelDist κ ξ ξ' := by
  unfold featureLabelDist
  positivity

open DRLogReg.RiskEstimation in
theorem dr36_norming {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →L[ℝ] ℝ) : ∃ u : V, ‖u‖ ≤ 1 ∧ β u = ‖β‖ := by
  have hK : IsCompact (Metric.closedBall (0 : V) 1) := isCompact_closedBall 0 1
  obtain ⟨u, hu, hmax⟩ := hK.exists_isMaxOn (Metric.nonempty_closedBall.mpr zero_le_one)
    β.continuous.continuousOn
  have hu1 : ‖u‖ ≤ 1 := by simpa using hu
  refine ⟨u, hu1, le_antisymm ?_ ?_⟩
  · have := β.le_opNorm u
    rw [Real.norm_eq_abs] at this
    calc β u ≤ |β u| := le_abs_self _
      _ ≤ ‖β‖ * ‖u‖ := this
      _ ≤ ‖β‖ * 1 := mul_le_mul_of_nonneg_left hu1 (norm_nonneg _)
      _ = ‖β‖ := mul_one _
  · have h0 : 0 ≤ β u := by
      have := isMaxOn_iff.mp hmax 0 (Metric.mem_closedBall_self zero_le_one)
      simpa using this
    apply ContinuousLinearMap.opNorm_le_bound _ h0
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hx' : ‖x‖⁻¹ • x ∈ Metric.closedBall (0 : V) 1 := by
        simp [norm_smul, hxn.ne']
      have hx'' : -(‖x‖⁻¹ • x) ∈ Metric.closedBall (0 : V) 1 := by
        simp [norm_smul, hxn.ne']
      have h1 : β (‖x‖⁻¹ • x) ≤ β u := isMaxOn_iff.mp hmax _ hx'
      have h2 : β (-(‖x‖⁻¹ • x)) ≤ β u := isMaxOn_iff.mp hmax _ hx''
      rw [map_neg, map_smul, smul_eq_mul] at h2
      rw [map_smul, smul_eq_mul] at h1
      have e1 : β x ≤ ‖x‖ * β u := (inv_mul_le_iff₀ hxn).mp h1
      have e2 : -β x ≤ ‖x‖ * β u := by
        have : ‖x‖⁻¹ * (-β x) ≤ β u := by linarith
        exact (inv_mul_le_iff₀ hxn).mp this
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith

open DRLogReg.RiskEstimation in
theorem dr36_idx {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ : ℝ} (hκ : 0 < κ)
    (β : V →L[ℝ] ℝ) {u : V} (hu1 : ‖u‖ ≤ 1) (hu : β u = ‖β‖) (x : V) (y : Bool) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ξ : V × Bool, sgn ξ.2 * β ξ.1 ≤ 0 ∧ featureLabelDist κ ξ (x, y) ≤ c ∧
      ∀ lam : ℝ, 0 ≤ lam → ∃ r t : ℝ,
        1 - r * sgn y * β x ≤ max 0 (1 - lam * c) ∧
        1 + t * sgn y * β x - lam * κ ≤ max 0 (1 - lam * c) ∧
        r * ‖β‖ ≤ lam ∧ t * ‖β‖ ≤ lam ∧ 0 ≤ r ∧ 0 ≤ t := by
  obtain ⟨a, ha_def⟩ : ∃ a, a = sgn y * β x := ⟨_, rfl⟩
  by_cases ha : a ≤ 0
  · refine ⟨0, le_rfl, (x, y), ha_def ▸ ha, by simp [featureLabelDist],
      fun lam hlam => ⟨0, 0, ?_, ?_, ?_, ?_, le_rfl, le_rfl⟩⟩
    · simp
    · simp only [zero_mul, add_zero, mul_zero, sub_zero]
      apply le_max_of_le_right
      nlinarith
    · simpa using hlam
    · simpa using hlam
  push Not at ha
  have hb : 0 < ‖β‖ := by
    have h1 : a ≤ ‖β‖ * ‖x‖ := by
      calc a ≤ |a| := le_abs_self a
        _ = |β x| := by rw [ha_def, abs_mul, dr36_abs_sgn, one_mul]
        _ ≤ ‖β‖ * ‖x‖ := by simpa [Real.norm_eq_abs] using β.le_opNorm x
    by_contra hb
    push Not at hb
    have : ‖β‖ = 0 := le_antisymm hb (norm_nonneg _)
    rw [this, zero_mul] at h1
    linarith
  have hdual : ∀ c, c ≤ a / ‖β‖ → c ≤ κ → ∀ lam : ℝ, 0 ≤ lam → ∃ r t : ℝ,
      1 - r * sgn y * β x ≤ max 0 (1 - lam * c) ∧
      1 + t * sgn y * β x - lam * κ ≤ max 0 (1 - lam * c) ∧
      r * ‖β‖ ≤ lam ∧ t * ‖β‖ ≤ lam ∧ 0 ≤ r ∧ 0 ≤ t := by
    intro c hca hcκ lam hlam
    refine ⟨lam / ‖β‖, 0, ?_, ?_, ?_, ?_, div_nonneg hlam hb.le, le_rfl⟩
    · have : lam / ‖β‖ * sgn y * β x = lam * (a / ‖β‖) := by rw [ha_def]; ring
      rw [this]
      apply le_max_of_le_right
      nlinarith [mul_le_mul_of_nonneg_left hca hlam]
    · apply le_max_of_le_right
      simp only [zero_mul, add_zero]
      nlinarith [mul_le_mul_of_nonneg_left hcκ hlam]
    · rw [div_mul_cancel₀ _ hb.ne']
    · simpa using hlam
  by_cases hk : a / ‖β‖ ≤ κ
  · refine ⟨a / ‖β‖, div_nonneg ha.le hb.le, (x - (a / ‖β‖ * sgn y) • u, y), ?_, ?_,
      hdual _ le_rfl hk⟩
    · have hs := dr36_sgn_sq y
      simp only [map_sub, map_smul, smul_eq_mul, hu]
      have e : a / ‖β‖ * sgn y * ‖β‖ = a * sgn y := by field_simp
      rw [e]
      have : sgn y * (β x - a * sgn y) = a - a * (sgn y * sgn y) := by rw [ha_def]; ring
      rw [this, hs]
      simp
    · simp only [featureLabelDist, sub_sub_cancel_left, norm_neg, norm_smul, sub_self, abs_zero,
        mul_zero, zero_div, add_zero, Real.norm_eq_abs, abs_mul, dr36_abs_sgn, mul_one]
      rw [abs_of_nonneg (div_nonneg ha.le hb.le)]
      calc a / ‖β‖ * ‖u‖ ≤ a / ‖β‖ * 1 := mul_le_mul_of_nonneg_left hu1 (div_nonneg ha.le hb.le)
        _ = a / ‖β‖ := mul_one _
  · push Not at hk
    refine ⟨κ, hκ.le, (x, !y), ?_, ?_, hdual _ hk.le le_rfl⟩
    · cases y <;> simp [sgn] at ha_def ⊢ <;> linarith
    · cases y <;> norm_num [featureLabelDist, sgn]

open DRLogReg.RiskEstimation in
theorem dr36_nonneg {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ ε : ℝ} (hε : 0 ≤ ε)
    {N : ℕ} (hN : 0 < N) {xhat : Fin N → V} {yhat : Fin N → Bool} {β : V →L[ℝ] ℝ}
    {P : ℝ × (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)} (hP : P ∈ feasible10a κ xhat yhat β) :
    0 ≤ P.1 ∧ 0 ≤ objective10 ε P := by
  have h0 := hP ⟨0, hN⟩
  have hl : 0 ≤ P.1 := le_trans (mul_nonneg h0.2.2.2.2.1 (norm_nonneg _)) h0.2.2.1
  refine ⟨hl, ?_⟩
  unfold objective10
  have : 0 ≤ ∑ i, P.2.1 i := Finset.sum_nonneg fun i _ => (hP i).2.2.2.2.2.2
  exact add_nonneg (mul_nonneg hl hε) (mul_nonneg (by positivity) this)

open DRLogReg.RiskEstimation in
theorem dr36_pt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ : ℝ} {N : ℕ}
    {xhat : Fin N → V} {yhat : Fin N → Bool} {β : V →L[ℝ] ℝ}
    {P : ℝ × (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)} (hP : P ∈ feasible10a κ xhat yhat β)
    (i : Fin N) (ξ : V × Bool) (hξ : sgn ξ.2 * β ξ.1 ≤ 0) :
    1 ≤ P.2.1 i + P.1 * featureLabelDist κ ξ (xhat i, yhat i) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP i
  obtain ⟨x, y⟩ := ξ
  have hn : 0 ≤ ‖x - xhat i‖ := norm_nonneg _
  have hβ : |β x - β (xhat i)| ≤ ‖β‖ * ‖x - xhat i‖ := by
    rw [← map_sub]; simpa [Real.norm_eq_abs] using β.le_opNorm (x - xhat i)
  rw [abs_le] at hβ
  obtain ⟨hβ1, hβ2⟩ := hβ
  have k1 := mul_le_mul_of_nonneg_right h3 hn
  have k2 := mul_le_mul_of_nonneg_right h4 hn
  have p1 : 0 ≤ P.2.2.1 i * (‖β‖ * ‖x - xhat i‖ + (β x - β (xhat i))) := mul_nonneg h5 (by linarith)
  have p2 : 0 ≤ P.2.2.1 i * (‖β‖ * ‖x - xhat i‖ - (β x - β (xhat i))) := mul_nonneg h5 (by linarith)
  have p3 : 0 ≤ P.2.2.2 i * (‖β‖ * ‖x - xhat i‖ + (β x - β (xhat i))) := mul_nonneg h6 (by linarith)
  have p4 : 0 ≤ P.2.2.2 i * (‖β‖ * ‖x - xhat i‖ - (β x - β (xhat i))) := mul_nonneg h6 (by linarith)
  simp only [featureLabelDist] at ⊢
  cases y <;> cases hy : yhat i <;> simp only [hy, sgn] at h1 h2 hξ ⊢ <;> norm_num at h1 h2 hξ ⊢ <;>
    nlinarith [mul_nonneg h5 hn, mul_nonneg h6 hn]

open DRLogReg.RiskEstimation in
theorem dr36_measA {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (β : V →L[ℝ] ℝ) : MeasurableSet {ξ : V × Bool | sgn ξ.2 * β ξ.1 ≤ 0} := by
  have h1 : Measurable fun ξ : V × Bool => sgn ξ.2 := (measurable_of_countable sgn).comp measurable_snd
  have h2 : Measurable fun ξ : V × Bool => β ξ.1 := β.continuous.measurable.comp measurable_fst
  exact measurableSet_le (h1.mul h2) measurable_const

open MeasureTheory DRLogReg.RiskEstimation in
theorem dr36_weak {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N) {xhat : Fin N → V}
    {yhat : Fin N → Bool} {β : V →L[ℝ] ℝ}
    {P : ℝ × (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)} (hP : P ∈ feasible10a κ xhat yhat β)
    {Q : Measure (V × Bool)} (hQ : Q ∈ wassersteinBall κ ε (empirical xhat yhat)) :
    Q {ξ | sgn ξ.2 * β ξ.1 ≤ 0} ≤ ENNReal.ofReal (objective10 ε P) := by
  classical
  set A : Set (V × Bool) := {ξ | sgn ξ.2 * β ξ.1 ≤ 0} with hAdef
  have hA : MeasurableSet A := dr36_measA β
  have hlam : 0 ≤ P.1 := (dr36_nonneg hε hN hP).1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set C : ℝ := (N : ℝ)⁻¹ * ∑ i, P.2.1 i with hCdef
  have hC : 0 ≤ C := mul_nonneg (inv_nonneg.mpr hNpos.le)
    (Finset.sum_nonneg fun i _ => (hP i).2.2.2.2.2.2)
  let g : V × Bool → ENNReal := fun ξ' =>
    ⨅ i, if ξ' = (xhat i, yhat i) then ENNReal.ofReal (P.2.1 i) else ⊤
  have hg : Measurable g :=
    Measurable.iInf fun i => Measurable.ite measurableSet_eq measurable_const measurable_const
  have hgle : ∀ i, g (xhat i, yhat i) ≤ ENNReal.ofReal (P.2.1 i) := fun i =>
    (iInf_le _ i).trans (by simp)
  have hpt : ∀ q : (V × Bool) × (V × Bool), (Prod.fst ⁻¹' A).indicator 1 q ≤
      g q.2 + ENNReal.ofReal P.1 * ENNReal.ofReal (featureLabelDist κ q.1 q.2) := by
    intro q
    by_cases hq : q.1 ∈ A
    · rw [Set.indicator_of_mem (show q ∈ Prod.fst ⁻¹' A from hq), Pi.one_apply]
      simp only [g]
      rw [ENNReal.iInf_add]
      refine le_iInf fun i => ?_
      split_ifs with h
      · rw [← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_add (hP i).2.2.2.2.2.2
          (mul_nonneg hlam (dr36_dist_nonneg hκ _ _)), ← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        rw [h]
        exact dr36_pt hP i q.1 hq
      · simp
    · rw [Set.indicator_of_notMem (show q ∉ Prod.fst ⁻¹' A from hq)]
      exact zero_le
  have hcoup : ∀ π : Measure ((V × Bool) × (V × Bool)), π.map Prod.fst = Q →
      π.map Prod.snd = empirical xhat yhat →
      Q A ≤ ENNReal.ofReal C + ENNReal.ofReal P.1 *
        ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π := by
    intro π h1 h2
    calc Q A = π (Prod.fst ⁻¹' A) := by rw [← h1, Measure.map_apply measurable_fst hA]
      _ = ∫⁻ q, (Prod.fst ⁻¹' A).indicator 1 q ∂π :=
          (lintegral_indicator_one (measurable_fst hA)).symm
      _ ≤ ∫⁻ q, (g q.2 + ENNReal.ofReal P.1 * ENNReal.ofReal (featureLabelDist κ q.1 q.2)) ∂π :=
          lintegral_mono hpt
      _ = ∫⁻ q, g q.2 ∂π + ENNReal.ofReal P.1 *
            ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π := by
          rw [lintegral_add_left (f := fun q : (V × Bool) × (V × Bool) => g q.2) (hg.comp measurable_snd),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal C + ENNReal.ofReal P.1 *
            ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π := by
          gcongr
          rw [← lintegral_map hg measurable_snd, h2]
          simp only [empirical, lintegral_smul_measure, lintegral_finsetSum_measure,
            lintegral_dirac, smul_eq_mul]
          calc (N : ENNReal)⁻¹ * ∑ i, g (xhat i, yhat i)
              ≤ (N : ENNReal)⁻¹ * ∑ i, ENNReal.ofReal (P.2.1 i) := by
                gcongr with i
                exact hgle i
            _ = ENNReal.ofReal C := by
                rw [hCdef, ENNReal.ofReal_mul (inv_nonneg.mpr hNpos.le),
                  ENNReal.ofReal_sum_of_nonneg (fun i _ => (hP i).2.2.2.2.2.2),
                  ENNReal.ofReal_inv_of_pos hNpos, ENNReal.ofReal_natCast]
  have hW := hQ.2
  have hobj : objective10 ε P = P.1 * ε + C := rfl
  rw [hobj]
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ _
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  set η : ℝ := (δ : ℝ) / (P.1 + 1) with hηdef
  have hη : 0 < η := div_pos hδr (by linarith)
  have hlt : wasserstein κ Q (empirical xhat yhat) < ENNReal.ofReal (ε + η) := by
    calc _ ≤ ENNReal.ofReal ε := hW
      _ < ENNReal.ofReal (ε + η) := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  simp only [wasserstein, iInf_lt_iff] at hlt
  obtain ⟨π, _, h1, h2, hcost⟩ := hlt
  have hle : P.1 * η ≤ δ := by
    rw [hηdef, mul_div_assoc']
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  calc Q A ≤ ENNReal.ofReal C + ENNReal.ofReal P.1 *
        ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π := hcoup π h1 h2
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal P.1 * ENNReal.ofReal (ε + η) := by gcongr
    _ = ENNReal.ofReal (P.1 * ε + C + P.1 * η) := by
        rw [← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_add hC (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (P.1 * ε + C) + δ := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hlam hε) hC) δ.coe_nonneg]
        apply ENNReal.ofReal_le_ofReal
        linarith

open MeasureTheory DRLogReg.RiskEstimation in
theorem dr36_achieve {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] {κ ε : ℝ} (hκ : 0 ≤ κ) {N : ℕ} (hN : 0 < N) (xhat : Fin N → V)
    (yhat : Fin N → Bool) (A : Set (V × Bool)) (hA : MeasurableSet A)
    (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (ξs : Fin N → V × Bool) (hξA : ∀ i, ξs i ∈ A)
    (hcost : ∑ i, p i / N * featureLabelDist κ (ξs i) (xhat i, yhat i) ≤ ε) :
    ∃ Q ∈ wassersteinBall κ ε (empirical xhat yhat), ENNReal.ofReal (∑ i, p i / N) ≤ Q A := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set π : Measure ((V × Bool) × (V × Bool)) := ∑ i,
    (ENNReal.ofReal ((1 - p i) / N) • Measure.dirac ((xhat i, yhat i), (xhat i, yhat i)) +
      ENNReal.ofReal (p i / N) • Measure.dirac (ξs i, (xhat i, yhat i))) with hπ
  have hcoef : ∀ i, ENNReal.ofReal ((1 - p i) / N) + ENNReal.ofReal (p i / N) =
      (N : ENNReal)⁻¹ := by
    intro i
    rw [← ENNReal.ofReal_add (div_nonneg (by linarith [(hp i).2]) hNpos.le)
      (div_nonneg (hp i).1 hNpos.le)]
    rw [show (1 - p i) / N + p i / N = (N : ℝ)⁻¹ by field_simp; ring]
    rw [ENNReal.ofReal_inv_of_pos hNpos, ENNReal.ofReal_natCast]
  have hπapp : ∀ S, π S = ∑ i, (ENNReal.ofReal ((1 - p i) / N) *
      S.indicator 1 ((xhat i, yhat i), (xhat i, yhat i)) +
      ENNReal.ofReal (p i / N) * S.indicator 1 (ξs i, (xhat i, yhat i))) := by
    intro S
    simp only [hπ, Measure.finsetSum_apply, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply, smul_eq_mul]
  have hsnd : π.map Prod.snd = empirical xhat yhat := by
    ext S hS
    rw [Measure.map_apply measurable_snd hS, hπapp]
    simp only [empirical, Measure.smul_apply, Measure.finsetSum_apply, Measure.dirac_apply,
      smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have e1 : (Prod.snd ⁻¹' S).indicator (1 : (V × Bool) × (V × Bool) → ENNReal)
        ((xhat i, yhat i), (xhat i, yhat i)) = S.indicator 1 (xhat i, yhat i) := rfl
    have e2 : (Prod.snd ⁻¹' S).indicator (1 : (V × Bool) × (V × Bool) → ENNReal)
        (ξs i, (xhat i, yhat i)) = S.indicator 1 (xhat i, yhat i) := rfl
    rw [e1, e2, ← add_mul, hcoef]
  have hprob : IsProbabilityMeasure π := by
    constructor
    rw [hπapp]
    simp only [Set.indicator_univ, Pi.one_apply, mul_one, hcoef]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)
  refine ⟨π.map Prod.fst, ⟨Measure.isProbabilityMeasure_map measurable_fst.aemeasurable, ?_⟩, ?_⟩
  · calc wasserstein κ (π.map Prod.fst) (empirical xhat yhat)
        ≤ ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π :=
          iInf_le_of_le π (iInf_le_of_le hprob (iInf_le_of_le rfl (iInf_le_of_le hsnd le_rfl)))
      _ = ∑ i, ENNReal.ofReal (p i / N) *
            ENNReal.ofReal (featureLabelDist κ (ξs i) (xhat i, yhat i)) := by
          simp [hπ, lintegral_finsetSum_measure, lintegral_add_measure, lintegral_smul_measure,
            lintegral_dirac, dr36_dist_self]
      _ = ENNReal.ofReal (∑ i, p i / N * featureLabelDist κ (ξs i) (xhat i, yhat i)) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ =>
            mul_nonneg (div_nonneg (hp i).1 hNpos.le) (dr36_dist_nonneg hκ _ _))]
          apply Finset.sum_congr rfl
          intro i _
          rw [ENNReal.ofReal_mul (div_nonneg (hp i).1 hNpos.le)]
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hcost
  · rw [Measure.map_apply measurable_fst hA, hπapp,
      ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (hp i).1 hNpos.le)]
    apply Finset.sum_le_sum
    intro i _
    rw [Set.indicator_of_mem (show (ξs i, (xhat i, yhat i)) ∈ Prod.fst ⁻¹' A from hξA i),
      Pi.one_apply, mul_one]
    exact le_add_self

open MeasureTheory DRLogReg.RiskEstimation in
theorem dr36_main {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool) (β : V →L[ℝ] ℝ) :
    ∃ P ∈ feasible10a κ xhat yhat β, ∃ Q ∈ wassersteinBall κ ε (empirical xhat yhat),
      ENNReal.ofReal (objective10 ε P) ≤ Q {ξ | sgn ξ.2 * β ξ.1 ≤ 0} := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨u, hu1, hu⟩ := dr36_norming β
  choose c hc0 ξs hξA hξd hdual using fun i => dr36_idx hκ β hu1 hu (xhat i) (yhat i)
  obtain ⟨lam, hlam, p, hp, hpc, hval⟩ := dr36_knap hN c hc0 hε
  choose r t hrt using fun i => hdual i lam hlam
  refine ⟨(lam, fun i => max 0 (1 - lam * c i), r, t), ?_, ?_⟩
  · intro i
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrt i
    exact ⟨h1, h2, h3, h4, h5, h6, le_max_left _ _⟩
  have hcost : ∑ i, p i / N * featureLabelDist κ (ξs i) (xhat i, yhat i) ≤ ε := by
    calc ∑ i, p i / N * featureLabelDist κ (ξs i) (xhat i, yhat i) ≤ ∑ i, p i / N * c i :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hξd i) (div_nonneg (hp i).1 hNpos.le)
      _ = (∑ i, p i * c i) / N := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ ≤ ε := by
          rw [div_le_iff₀ hNpos]
          linarith
  obtain ⟨Q, hQ, hQA⟩ := dr36_achieve hκ.le hN xhat yhat _ (dr36_measA β) p hp ξs hξA hcost
  refine ⟨Q, hQ, le_trans ?_ hQA⟩
  apply ENNReal.ofReal_le_ofReal
  simp only [objective10]
  have e : lam * ε + (N : ℝ)⁻¹ * ∑ i, max 0 (1 - lam * c i) =
      (N : ℝ)⁻¹ * (N * (lam * ε) + ∑ i, max 0 (1 - lam * c i)) := by
    field_simp
  rw [e, ← Finset.sum_div, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hval (inv_nonneg.mpr hNpos.le)

open MeasureTheory DRLogReg.RiskEstimation in
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (κ ε : ℝ) (hκ : 0 < κ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool) (βhat : V →L[ℝ] ℝ) :
    ∃ v : ℝ, IsLeast (objective10 ε '' feasible10a κ xhat yhat βhat) v ∧
      riskMax κ ε xhat yhat βhat = ENNReal.ofReal v := by
  obtain ⟨P, hP, Q, hQ, hQA⟩ := dr36_main hκ hε hN xhat yhat βhat
  refine ⟨objective10 ε P, ⟨⟨P, hP, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨P', hP', rfl⟩
    exact (ENNReal.ofReal_le_ofReal_iff (dr36_nonneg hε hN hP').2).mp
      (hQA.trans (dr36_weak hκ.le hε hN hP' hQ))
  · unfold riskMax
    apply le_antisymm
    · exact iSup₂_le fun Q' hQ' => dr36_weak hκ.le hε hN hP hQ'
    · exact hQA.trans (le_iSup₂ (f := fun Q (_ : Q ∈ wassersteinBall κ ε (empirical xhat yhat)) =>
        Q {ξ | sgn ξ.2 * βhat ξ.1 ≤ 0}) Q hQ)
