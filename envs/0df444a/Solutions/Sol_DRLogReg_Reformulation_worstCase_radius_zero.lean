-- Prove2me | solution 1 for DRLogReg.Reformulation.worstCase_radius_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T08:04:36.54883+00:00
-- url     : https://prove2.me/submissions/144dd540-3c0a-4c5f-aca9-e712884a8214

import Mathlib
import Definitions.Def_DRLogReg_Reformulation_Core
import Definitions.Def_DRLogReg_Reformulation_Program

set_option autoImplicit false

open DRLogReg.Reformulation in
theorem dre2_sgn_sq (y : Bool) : sgn y * sgn y = 1 := by cases y <;> simp [sgn]

open DRLogReg.Reformulation in
theorem dre2_abs_sgn (y : Bool) : |sgn y| = 1 := by cases y <;> simp [sgn]

theorem dre2_softplus_le (a b : ℝ) :
    Real.log (1 + Real.exp a) ≤ Real.log (1 + Real.exp b) + max 0 (a - b) := by
  have h1 : 0 < 1 + Real.exp a := by positivity
  have h2 : 0 < 1 + Real.exp b := by positivity
  rw [← Real.log_exp (max 0 (a - b)), ← Real.log_mul h2.ne' (Real.exp_pos _).ne']
  apply Real.log_le_log h1
  have hm0 : 1 ≤ Real.exp (max 0 (a - b)) := Real.one_le_exp (le_max_left _ _)
  have hm1 : Real.exp a ≤ Real.exp b * Real.exp (max 0 (a - b)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [le_max_right 0 (a - b)]
  nlinarith

theorem dre2_softplus_ge (a : ℝ) : a ≤ Real.log (1 + Real.exp a) := by
  have := Real.log_le_log (Real.exp_pos a) (show Real.exp a ≤ 1 + Real.exp a by linarith)
  rwa [Real.log_exp] at this

open DRLogReg.Reformulation in
theorem dre2_logloss_pos {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : V →L[ℝ] ℝ) (x : V) (y : Bool) : 0 < logloss β x y := by
  unfold logloss
  apply Real.log_pos
  linarith [Real.exp_pos (-(sgn y * β x))]

open DRLogReg.Reformulation in
theorem dre2_dist_same {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (κ : ℝ)
    (x x' : V) (y : Bool) : featureLabelDist κ (x, y) (x', y) = ‖x - x'‖ := by
  simp [featureLabelDist]

open DRLogReg.Reformulation in
theorem dre2_dist_flip {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (κ : ℝ)
    (x x' : V) (y : Bool) : featureLabelDist κ (x, !y) (x', y) = ‖x - x'‖ + κ := by
  cases y <;> norm_num [featureLabelDist, sgn]

open DRLogReg.Reformulation in
theorem dre2_dist_nonneg {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ : ℝ}
    (hκ : 0 ≤ κ) (ξ ξ' : V × Bool) : 0 ≤ featureLabelDist κ ξ ξ' := by
  unfold featureLabelDist
  positivity

open DRLogReg.Reformulation in
theorem dre2_lip {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : V →L[ℝ] ℝ) (x x' : V) (y : Bool) :
    logloss β x y ≤ logloss β x' y + ‖β‖ * ‖x - x'‖ := by
  unfold logloss
  refine (dre2_softplus_le (-(sgn y * β x)) (-(sgn y * β x'))).trans ?_
  gcongr
  apply max_le (by positivity)
  have h := β.le_opNorm (x - x')
  rw [Real.norm_eq_abs, map_sub] at h
  have e : -(sgn y * β x) - -(sgn y * β x') = -(sgn y * (β x - β x')) := by ring
  rw [e]
  calc -(sgn y * (β x - β x')) ≤ |sgn y * (β x - β x')| := neg_le_abs _
    _ = |β x - β x'| := by rw [abs_mul, dre2_abs_sgn, one_mul]
    _ ≤ ‖β‖ * ‖x - x'‖ := h

open DRLogReg.Reformulation in
theorem dre2_pt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ : ℝ} {N : ℕ}
    {xhat : Fin N → V} {yhat : Fin N → Bool}
    {p : (V →L[ℝ] ℝ) × ℝ × (Fin N → ℝ)} (hp : p ∈ feasible7 κ xhat yhat)
    (i : Fin N) (ξ : V × Bool) :
    logloss p.1 ξ.1 ξ.2 ≤ p.2.2 i + p.2.1 * featureLabelDist κ ξ (xhat i, yhat i) := by
  obtain ⟨h1, h2, h3⟩ := hp
  obtain ⟨x, y⟩ := ξ
  dsimp only
  have hn : 0 ≤ ‖x - xhat i‖ := norm_nonneg _
  have hk : ‖p.1‖ * ‖x - xhat i‖ ≤ p.2.1 * ‖x - xhat i‖ := mul_le_mul_of_nonneg_right h3 hn
  by_cases hy : y = yhat i
  · subst hy
    rw [dre2_dist_same]
    have e1 := dre2_lip p.1 x (xhat i) (yhat i)
    have e2 := h1 i
    linarith
  · have hy' : y = !yhat i := by
      cases y <;> cases h : yhat i <;> simp_all
    subst hy'
    rw [dre2_dist_flip]
    have e1 := dre2_lip p.1 x (xhat i) (!yhat i)
    have e2 := h2 i
    linarith

open DRLogReg.Reformulation in
theorem dre2_meas {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (β : V →L[ℝ] ℝ) : Measurable (fun ξ : V × Bool => logloss β ξ.1 ξ.2) := by
  have h1 : Measurable fun ξ : V × Bool => sgn ξ.2 :=
    (measurable_of_countable sgn).comp measurable_snd
  have h2 : Measurable fun ξ : V × Bool => β ξ.1 := β.continuous.measurable.comp measurable_fst
  unfold logloss
  exact Real.measurable_log.comp (measurable_const.add (Real.measurable_exp.comp (h1.mul h2).neg))

open MeasureTheory DRLogReg.Reformulation in
theorem dre2_weak {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N) {xhat : Fin N → V}
    {yhat : Fin N → Bool} {p : (V →L[ℝ] ℝ) × ℝ × (Fin N → ℝ)}
    (hp : p ∈ feasible7 κ xhat yhat)
    {Q : Measure (V × Bool)} (hQ : Q ∈ wassersteinBall κ ε (empirical xhat yhat)) :
    ∫⁻ ξ, ENNReal.ofReal (logloss p.1 ξ.1 ξ.2) ∂Q ≤ ENNReal.ofReal (objective7 ε p) := by
  classical
  have hs : ∀ i, 0 ≤ p.2.2 i := fun i => (dre2_logloss_pos _ _ _).le.trans (hp.1 i)
  have hlam : 0 ≤ p.2.1 := (norm_nonneg _).trans hp.2.2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set C : ℝ := (N : ℝ)⁻¹ * ∑ i, p.2.2 i with hCdef
  have hC : 0 ≤ C := mul_nonneg (inv_nonneg.mpr hNpos.le) (Finset.sum_nonneg fun i _ => hs i)
  have hfm : Measurable (fun ξ : V × Bool => ENNReal.ofReal (logloss p.1 ξ.1 ξ.2)) :=
    (dre2_meas p.1).ennreal_ofReal
  let g : V × Bool → ENNReal := fun ξ' =>
    ⨅ i, if ξ' = (xhat i, yhat i) then ENNReal.ofReal (p.2.2 i) else ⊤
  have hg : Measurable g :=
    Measurable.iInf fun i => Measurable.ite measurableSet_eq measurable_const measurable_const
  have hgle : ∀ i, g (xhat i, yhat i) ≤ ENNReal.ofReal (p.2.2 i) := fun i =>
    (iInf_le _ i).trans (by simp)
  have hpt : ∀ q : (V × Bool) × (V × Bool), ENNReal.ofReal (logloss p.1 q.1.1 q.1.2) ≤
      g q.2 + ENNReal.ofReal p.2.1 * ENNReal.ofReal (featureLabelDist κ q.1 q.2) := by
    intro q
    simp only [g]
    rw [ENNReal.iInf_add]
    refine le_iInf fun i => ?_
    split_ifs with h
    · rw [← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_add (hs i)
        (mul_nonneg hlam (dre2_dist_nonneg hκ _ _))]
      apply ENNReal.ofReal_le_ofReal
      rw [h]
      exact dre2_pt hp i q.1
    · simp
  have hcoup : ∀ π : Measure ((V × Bool) × (V × Bool)), π.map Prod.fst = Q →
      π.map Prod.snd = empirical xhat yhat →
      ∫⁻ ξ, ENNReal.ofReal (logloss p.1 ξ.1 ξ.2) ∂Q ≤ ENNReal.ofReal C + ENNReal.ofReal p.2.1 *
        ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π := by
    intro π h1 h2
    calc ∫⁻ ξ, ENNReal.ofReal (logloss p.1 ξ.1 ξ.2) ∂Q
        = ∫⁻ q, ENNReal.ofReal (logloss p.1 q.1.1 q.1.2) ∂π := by
          rw [← h1, lintegral_map hfm measurable_fst]
      _ ≤ ∫⁻ q, (g q.2 + ENNReal.ofReal p.2.1 *
            ENNReal.ofReal (featureLabelDist κ q.1 q.2)) ∂π :=
          lintegral_mono hpt
      _ = ∫⁻ q, g q.2 ∂π + ENNReal.ofReal p.2.1 *
            ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π := by
          rw [lintegral_add_left (f := fun q : (V × Bool) × (V × Bool) => g q.2)
            (hg.comp measurable_snd), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal C + ENNReal.ofReal p.2.1 *
            ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π := by
          gcongr
          rw [← lintegral_map hg measurable_snd, h2]
          simp only [empirical, lintegral_smul_measure, lintegral_finsetSum_measure,
            lintegral_dirac, smul_eq_mul]
          calc (N : ENNReal)⁻¹ * ∑ i, g (xhat i, yhat i)
              ≤ (N : ENNReal)⁻¹ * ∑ i, ENNReal.ofReal (p.2.2 i) := by
                gcongr with i
                exact hgle i
            _ = ENNReal.ofReal C := by
                rw [hCdef, ENNReal.ofReal_mul (inv_nonneg.mpr hNpos.le),
                  ENNReal.ofReal_sum_of_nonneg (fun i _ => hs i),
                  ENNReal.ofReal_inv_of_pos hNpos, ENNReal.ofReal_natCast]
  have hW := hQ.2
  have hobj : objective7 ε p = p.2.1 * ε + C := rfl
  rw [hobj]
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ _
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  set η : ℝ := (δ : ℝ) / (p.2.1 + 1) with hηdef
  have hη : 0 < η := div_pos hδr (by linarith)
  have hlt : wasserstein κ Q (empirical xhat yhat) < ENNReal.ofReal (ε + η) := by
    calc _ ≤ ENNReal.ofReal ε := hW
      _ < ENNReal.ofReal (ε + η) := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  simp only [wasserstein, iInf_lt_iff] at hlt
  obtain ⟨π, _, h1, h2, hcost⟩ := hlt
  have hle : p.2.1 * η ≤ δ := by
    rw [hηdef, mul_div_assoc']
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  calc ∫⁻ ξ, ENNReal.ofReal (logloss p.1 ξ.1 ξ.2) ∂Q ≤ ENNReal.ofReal C + ENNReal.ofReal p.2.1 *
        ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π := hcoup π h1 h2
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal p.2.1 * ENNReal.ofReal (ε + η) := by gcongr
    _ = ENNReal.ofReal (p.2.1 * ε + C + p.2.1 * η) := by
        rw [← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_add hC (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (p.2.1 * ε + C) + δ := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add
          (add_nonneg (mul_nonneg hlam hε) hC) δ.coe_nonneg]
        apply ENNReal.ofReal_le_ofReal
        linarith

theorem dre2_norming {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
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

open Finset in
theorem dre2_knap {N : ℕ} (g : Fin N → ℝ) {m : ℝ} (hm : 0 ≤ m) :
    ∃ ν : ℝ, 0 ≤ ν ∧ ∃ p : Fin N → ℝ, (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ ∑ i, p i ≤ m ∧
      ν * m + ∑ i, max 0 (g i - ν) ≤ ∑ i, p i * g i := by
  classical
  by_cases hA : (∑ i, if 0 < g i then (1:ℝ) else 0) ≤ m
  · refine ⟨0, le_rfl, fun i => if 0 < g i then 1 else 0, fun i => ?_, hA, ?_⟩
    · dsimp only
      split_ifs <;> norm_num
    · simp only [zero_mul, zero_add, sub_zero]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with h
      · rw [max_eq_right h.le, one_mul]
      · rw [max_eq_left (not_lt.mp h), zero_mul]
  push Not at hA
  set cnt : Fin N → ℝ := fun j => ∑ i, if g j ≤ g i then (1:ℝ) else 0 with hcnt
  set S := univ.filter (fun j => 0 < g j ∧ m < cnt j) with hS
  have hpos_ne : (univ.filter (fun i => 0 < g i)).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at h
    have : (∑ i, if 0 < g i then (1:ℝ) else 0) = 0 :=
      sum_eq_zero fun i _ => if_neg (h (mem_univ i))
    linarith
  obtain ⟨j1, hj1, hj1min⟩ := exists_min_image _ g hpos_ne
  have hSne : S.Nonempty := by
    refine ⟨j1, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj1).2, ?_⟩⟩
    refine lt_of_lt_of_le hA (sum_le_sum fun i _ => ?_)
    by_cases h1 : 0 < g i
    · rw [if_pos h1, if_pos (hj1min i (mem_filter.mpr ⟨mem_univ _, h1⟩))]
    · rw [if_neg h1]
      split_ifs <;> norm_num
  obtain ⟨j0, hj0S, hj0max⟩ := exists_max_image S g hSne
  have hj0 := (mem_filter.mp hj0S).2
  set τ := g j0 with hτ
  have hτpos : 0 < τ := hj0.1
  have hgt : (∑ i, if τ < g i then (1:ℝ) else 0) ≤ m := by
    by_contra hc
    push Not at hc
    have hne : (univ.filter (fun i => τ < g i)).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at h
      have : (∑ i, if τ < g i then (1:ℝ) else 0) = 0 :=
        sum_eq_zero fun i _ => if_neg (h (mem_univ i))
      linarith
    obtain ⟨k, hk, hkmin⟩ := exists_min_image _ g hne
    have hkτ : τ < g k := (mem_filter.mp hk).2
    have hck : cnt k = ∑ i, if τ < g i then (1:ℝ) else 0 := by
      simp only [hcnt]
      apply sum_congr rfl
      intro i _
      by_cases hi : τ < g i
      · rw [if_pos hi, if_pos (hkmin i (mem_filter.mpr ⟨mem_univ _, hi⟩))]
      · rw [if_neg hi, if_neg]
        intro h
        exact hi (lt_of_lt_of_le hkτ h)
    have hkS : k ∈ S := mem_filter.mpr ⟨mem_univ _, by linarith, by rw [hck]; exact hc⟩
    have := hj0max k hkS
    linarith
  set ngt : ℝ := ∑ i, if τ < g i then (1:ℝ) else 0 with hngt
  set neq : ℝ := ∑ i, if g i = τ then (1:ℝ) else 0 with hneq
  have hsplit : cnt j0 = ngt + neq := by
    simp only [hcnt, hngt, hneq]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rcases lt_trichotomy (g i) τ with h | h | h
    · rw [if_neg (not_le.mpr h), if_neg (not_lt.mpr h.le), if_neg h.ne]
      norm_num
    · rw [if_pos h.ge, if_neg (not_lt.mpr h.le), if_pos h]
      norm_num
    · rw [if_pos h.le, if_pos h, if_neg h.ne']
      norm_num
  have hm_lt : m < ngt + neq := by rw [← hsplit]; exact hj0.2
  have hneq_pos : 0 < neq := by linarith
  set θ := (m - ngt) / neq with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hneq_pos.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hneq_pos]; linarith
  have hθn : θ * neq = m - ngt := by rw [hθ]; field_simp
  set p : Fin N → ℝ := fun i => if τ < g i then 1 else if g i = τ then θ else 0 with hp
  have hpsum : ∑ i, p i = m := by
    have e : ∀ i, p i = (if τ < g i then (1:ℝ) else 0) + θ * (if g i = τ then (1:ℝ) else 0) := by
      intro i
      simp only [hp]
      rcases lt_trichotomy (g i) τ with h | h | h
      · rw [if_neg (not_lt.mpr h.le), if_neg h.ne, if_neg (not_lt.mpr h.le), if_neg h.ne]
        ring
      · rw [if_neg (not_lt.mpr h.le), if_pos h, if_neg (not_lt.mpr h.le), if_pos h]
        ring
      · rw [if_pos h, if_pos h, if_neg h.ne']
        ring
    rw [sum_congr rfl (fun i _ => e i), sum_add_distrib, ← mul_sum]
    linarith
  refine ⟨τ, hτpos.le, p, ?_, hpsum.le, ?_⟩
  · intro i
    simp only [hp]
    split_ifs <;> constructor <;> linarith
  · have hterm : ∀ i, p i * g i - max 0 (g i - τ) = τ * p i := by
      intro i
      simp only [hp]
      rcases lt_trichotomy (g i) τ with h | h | h
      · rw [if_neg (not_lt.mpr h.le), if_neg h.ne, max_eq_left (by linarith)]
        ring
      · rw [if_neg (not_lt.mpr h.le), if_pos h, h, sub_self, max_self]
        ring
      · rw [if_pos h, max_eq_right (by linarith)]
        ring
    have e2 : ∑ i, p i * g i - ∑ i, max 0 (g i - τ) = τ * m := by
      rw [← sum_sub_distrib, sum_congr rfl (fun i _ => hterm i), ← mul_sum, hpsum]
    linarith

open MeasureTheory DRLogReg.Reformulation in
theorem dre2_couple {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] {K : Type*} [Fintype K] {κ ε : ℝ} (hκ : 0 ≤ κ) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool) (w : Fin N → K → ℝ) (hw0 : ∀ i k, 0 ≤ w i k)
    (hw1 : ∀ i, ∑ k, w i k = 1) (ζ : Fin N → K → V × Bool)
    (hcost : ∑ i, ∑ k, w i k / N * featureLabelDist κ (ζ i k) (xhat i, yhat i) ≤ ε)
    (f : V × Bool → ℝ) (hf : Measurable f) (hf0 : ∀ ξ, 0 ≤ f ξ) :
    ∃ Q ∈ wassersteinBall κ ε (empirical xhat yhat),
      ENNReal.ofReal (∑ i, ∑ k, w i k / N * f (ζ i k)) ≤ ∫⁻ ξ, ENNReal.ofReal (f ξ) ∂Q := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hwN : ∀ i k, 0 ≤ w i k / N := fun i k => div_nonneg (hw0 i k) hNpos.le
  set π : Measure ((V × Bool) × (V × Bool)) := ∑ i, ∑ k,
    ENNReal.ofReal (w i k / N) • Measure.dirac (ζ i k, (xhat i, yhat i)) with hπ
  have hcoef : ∀ i, ∑ k, ENNReal.ofReal (w i k / N) = (N : ENNReal)⁻¹ := by
    intro i
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hwN i k), ← Finset.sum_div, hw1 i,
      one_div, ENNReal.ofReal_inv_of_pos hNpos, ENNReal.ofReal_natCast]
  have hπapp : ∀ S, π S = ∑ i, ∑ k, ENNReal.ofReal (w i k / N) *
      S.indicator 1 (ζ i k, (xhat i, yhat i)) := by
    intro S
    simp only [hπ, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  have hsnd : π.map Prod.snd = empirical xhat yhat := by
    ext S hS
    rw [Measure.map_apply measurable_snd hS, hπapp]
    simp only [empirical, Measure.smul_apply, Measure.finsetSum_apply, Measure.dirac_apply,
      smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have e : ∀ k, (Prod.snd ⁻¹' S).indicator (1 : (V × Bool) × (V × Bool) → ENNReal)
        (ζ i k, (xhat i, yhat i)) = S.indicator 1 (xhat i, yhat i) := fun k => rfl
    simp only [e]
    rw [← Finset.sum_mul, hcoef]
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
      _ = ∑ i, ∑ k, ENNReal.ofReal (w i k / N) *
            ENNReal.ofReal (featureLabelDist κ (ζ i k) (xhat i, yhat i)) := by
          simp only [hπ, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
            smul_eq_mul]
      _ = ENNReal.ofReal (∑ i, ∑ k, w i k / N * featureLabelDist κ (ζ i k) (xhat i, yhat i)) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun k _ =>
            mul_nonneg (hwN i k) (dre2_dist_nonneg hκ _ _))]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun k _ =>
            mul_nonneg (hwN i k) (dre2_dist_nonneg hκ _ _))]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ENNReal.ofReal_mul (hwN i k)]
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hcost
  · rw [lintegral_map hf.ennreal_ofReal measurable_fst]
    apply le_of_eq
    simp only [hπ, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
      smul_eq_mul]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (hwN i k) (hf0 _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (hwN i k) (hf0 _))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ENNReal.ofReal_mul (hwN i k)]

open MeasureTheory DRLogReg.Reformulation in
theorem dre2_strong {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool) (β : V →L[ℝ] ℝ) :
    ∃ p ∈ feasible7 κ xhat yhat, p.1 = β ∧ ∀ δ : ℝ, 0 < δ →
      ∃ Q ∈ wassersteinBall κ ε (empirical xhat yhat),
        ENNReal.ofReal (objective7 ε p - δ) ≤ ∫⁻ ξ, ENNReal.ofReal (logloss β ξ.1 ξ.2) ∂Q := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hκne : κ ≠ 0 := hκ.ne'
  have hNi : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hNpos.le
  obtain ⟨u, hu1, hu⟩ := dre2_norming β
  set L := ‖β‖ with hL
  have hL0 : 0 ≤ L := norm_nonneg _
  set a : Fin N → ℝ := fun i => logloss β (xhat i) (yhat i) with ha
  set b : Fin N → ℝ := fun i => logloss β (xhat i) (!yhat i) with hb
  set z : Fin N → ℝ := fun i => -(sgn (yhat i) * β (xhat i)) with hz
  set m : ℝ := N * ε / κ with hm
  have hm0 : 0 ≤ m := div_nonneg (mul_nonneg hNpos.le hε) hκ.le
  obtain ⟨ν, hν, p, hp, hpm, hval⟩ := dre2_knap (fun i => b i - a i - L * κ) hm0
  set lam := L + ν / κ with hlam
  have hlamκ : lam * κ = L * κ + ν := by
    rw [hlam]
    field_simp
  set s : Fin N → ℝ := fun i => max (a i) (b i - lam * κ) with hs
  have hfeas : (β, lam, s) ∈ feasible7 κ xhat yhat := by
    refine ⟨fun i => le_max_left _ _, fun i => le_max_right _ _, ?_⟩
    show L ≤ L + ν / κ
    have := div_nonneg hν hκ.le
    linarith
  refine ⟨(β, lam, s), hfeas, rfl, ?_⟩
  intro δ hδ
  set SP : ℝ := ∑ i, p i with hSP
  set V1 : ℝ := (N : ℝ)⁻¹ * ∑ i, (a i + p i * (b i - a i)) with hV1
  set Z : ℝ := (N : ℝ)⁻¹ * ∑ i, z i with hZ
  set ε' : ℝ := ε - κ * SP / N with hε'
  have hSP0 : 0 ≤ SP := Finset.sum_nonneg fun i _ => (hp i).1
  have hε'0 : 0 ≤ ε' := by
    have h1 : κ * SP ≤ κ * m := mul_le_mul_of_nonneg_left hpm hκ.le
    have h2 : κ * m = N * ε := by
      rw [hm]
      field_simp
    have h3 : κ * SP / N ≤ ε := by
      rw [div_le_iff₀ hNpos]
      linarith
    linarith
  -- the objective is bounded by V1 + L ε'
  have hobj : objective7 ε (β, lam, s) ≤ V1 + L * ε' := by
    have hsi : ∀ i, s i = a i + max 0 ((b i - a i - L * κ) - ν) := by
      intro i
      simp only [hs]
      rw [hlamκ]
      rcases le_total (a i) (b i - (L * κ + ν)) with h | h
      · rw [max_eq_right h, max_eq_right (by linarith)]
        ring
      · rw [max_eq_left h, max_eq_left (by linarith)]
        ring
    have hνm : ν / κ * ε = ν * m / N := by
      rw [hm]
      field_simp
    have e1 : ∑ i, s i = ∑ i, a i + ∑ i, max 0 ((b i - a i - L * κ) - ν) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hsi i
    have e2 : ∑ i, p i * (b i - a i - L * κ) =
        ∑ i, (a i + p i * (b i - a i)) - ∑ i, a i - L * κ * SP := by
      have : ∀ i, p i * (b i - a i - L * κ) = (a i + p i * (b i - a i)) - a i - L * κ * p i :=
        fun i => by ring
      rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
    have hval' : ν * m + ∑ i, max 0 ((b i - a i - L * κ) - ν) ≤
        ∑ i, (a i + p i * (b i - a i)) - ∑ i, a i - L * κ * SP := by
      rw [← e2]
      exact hval
    show lam * ε + (N : ℝ)⁻¹ * ∑ i, s i ≤ V1 + L * ε'
    rw [e1, hlam, add_mul, hνm, hV1, hε']
    have key : (N : ℝ)⁻¹ * (ν * m + ∑ i, max 0 ((b i - a i - L * κ) - ν)) ≤
        (N : ℝ)⁻¹ * (∑ i, (a i + p i * (b i - a i)) - ∑ i, a i - L * κ * SP) :=
      mul_le_mul_of_nonneg_left hval' hNi
    have e3 : ν * m / N = (N : ℝ)⁻¹ * (ν * m) := by ring
    have e4 : L * (ε - κ * SP / N) = L * ε - (N : ℝ)⁻¹ * (L * κ * SP) := by ring
    rw [e3, e4]
    linarith [key]
  -- choice of the push fraction
  set D : ℝ := |V1 - Z| with hD
  have hD0 : 0 ≤ D := abs_nonneg _
  set q : ℝ := min 1 (δ / (D + 1)) with hq
  have hq0 : 0 < q := lt_min one_pos (div_pos hδ (by linarith))
  have hqne : q ≠ 0 := hq0.ne'
  have hq1 : q ≤ 1 := min_le_left _ _
  have hqD : q * D ≤ δ := by
    have h1 : q ≤ δ / (D + 1) := min_le_right _ _
    have h2 : q * (D + 1) ≤ δ := by rwa [le_div_iff₀ (by linarith)] at h1
    linarith
  set t : ℝ := ε' / q with ht
  have ht0 : 0 ≤ t := div_nonneg hε'0 hq0.le
  have hqt : q * t = ε' := by
    rw [ht]
    field_simp
  -- the three destinations of each sample
  set w : Fin N → Fin 3 → ℝ := fun i => ![(1 - q) * (1 - p i), (1 - q) * p i, q] with hw
  set ζ : Fin N → Fin 3 → V × Bool := fun i =>
    ![(xhat i, yhat i), (xhat i, !yhat i), (xhat i - (t * sgn (yhat i)) • u, yhat i)] with hζ
  have hw0 : ∀ i k, 0 ≤ w i k := by
    intro i k
    obtain ⟨h1, h2⟩ := hp i
    fin_cases k <;> simp [hw] <;> nlinarith
  have hw1 : ∀ i, ∑ k, w i k = 1 := by
    intro i
    simp [hw, Fin.sum_univ_three]
    ring
  have hpushd : ∀ i, featureLabelDist κ (xhat i - (t * sgn (yhat i)) • u, yhat i)
      (xhat i, yhat i) ≤ t := by
    intro i
    rw [dre2_dist_same, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_mul,
      dre2_abs_sgn, mul_one, abs_of_nonneg ht0]
    calc t * ‖u‖ ≤ t * 1 := mul_le_mul_of_nonneg_left hu1 ht0
      _ = t := mul_one t
  have hpushl : ∀ i, z i + t * L ≤ logloss β (xhat i - (t * sgn (yhat i)) • u) (yhat i) := by
    intro i
    unfold logloss
    refine le_trans (le_of_eq ?_) (dre2_softplus_ge _)
    rw [map_sub, map_smul, smul_eq_mul, hu]
    have := dre2_sgn_sq (yhat i)
    simp only [hz]
    linear_combination (-(t * L)) * this
  have hcost : ∑ i, ∑ k, w i k / N * featureLabelDist κ (ζ i k) (xhat i, yhat i) ≤ ε := by
    have hterm : ∀ i, ∑ k, w i k / N * featureLabelDist κ (ζ i k) (xhat i, yhat i) ≤
        (N : ℝ)⁻¹ * (κ * p i) + (N : ℝ)⁻¹ * (q * t) := by
      intro i
      obtain ⟨h1, h1'⟩ := hp i
      have h2 := hpushd i
      simp only [hw, hζ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, div_eq_inv_mul]
      rw [dre2_dist_same κ (xhat i) (xhat i) (yhat i), dre2_dist_flip κ (xhat i) (xhat i) (yhat i),
        sub_self, norm_zero]
      have k1 : (N : ℝ)⁻¹ * ((1 - q) * p i * κ) ≤ (N : ℝ)⁻¹ * (κ * p i) := by
        have : (1 - q) * p i * κ ≤ κ * p i := by
          nlinarith [mul_nonneg (mul_nonneg hq0.le h1) hκ.le]
        exact mul_le_mul_of_nonneg_left this hNi
      have k2 : (N : ℝ)⁻¹ * (q * featureLabelDist κ (xhat i - (t * sgn (yhat i)) • u, yhat i)
          (xhat i, yhat i)) ≤ (N : ℝ)⁻¹ * (q * t) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hq0.le) hNi
      linarith [k1, k2]
    calc ∑ i, ∑ k, w i k / N * featureLabelDist κ (ζ i k) (xhat i, yhat i)
        ≤ ∑ i, ((N : ℝ)⁻¹ * (κ * p i) + (N : ℝ)⁻¹ * (q * t)) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (N : ℝ)⁻¹ * (κ * SP) + q * t := by
          rw [hSP]
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          field_simp
      _ = ε := by
          rw [hqt, hε']
          ring
  have hfm := dre2_meas β
  obtain ⟨Q, hQ, hQle⟩ := dre2_couple hκ.le hN xhat yhat w hw0 hw1 ζ hcost
    (fun ξ => logloss β ξ.1 ξ.2) hfm (fun ξ => (dre2_logloss_pos _ _ _).le)
  refine ⟨Q, hQ, le_trans (ENNReal.ofReal_le_ofReal ?_) hQle⟩
  -- value lower bound
  have hvterm : ∀ i, (N : ℝ)⁻¹ * ((1 - q) * (a i + p i * (b i - a i))) + (N : ℝ)⁻¹ * (q * z i) +
      (N : ℝ)⁻¹ * (q * t * L) ≤ ∑ k, w i k / N * logloss β (ζ i k).1 (ζ i k).2 := by
    intro i
    have h1 := hpushl i
    have k2 : (N : ℝ)⁻¹ * (q * (z i + t * L)) ≤
        (N : ℝ)⁻¹ * (q * logloss β (xhat i - (t * sgn (yhat i)) • u) (yhat i)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hq0.le) hNi
    simp only [hw, hζ, ha, hb, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, div_eq_inv_mul]
    linarith [k2]
  have hsum : ∑ i, ((N : ℝ)⁻¹ * ((1 - q) * (a i + p i * (b i - a i))) + (N : ℝ)⁻¹ * (q * z i) +
      (N : ℝ)⁻¹ * (q * t * L)) = (1 - q) * V1 + q * Z + q * t * L := by
    rw [hV1, hZ]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    try ring
  have hge := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hvterm i
  rw [hsum] at hge
  have hVZ : V1 - Z ≤ D := le_abs_self _
  have hqVZ : q * (V1 - Z) ≤ q * D := mul_le_mul_of_nonneg_left hVZ hq0.le
  have hqt' : q * t * L = ε' * L := by rw [hqt]
  show objective7 ε (β, lam, s) - δ ≤ ∑ i, ∑ k, w i k / N * logloss β (ζ i k).1 (ζ i k).2
  linarith

open MeasureTheory DRLogReg.Reformulation in
theorem dr83_obj_nonneg {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {κ ε : ℝ} (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N)
    {xhat : Fin N → V} {yhat : Fin N → Bool} {p : (V →L[ℝ] ℝ) × ℝ × (Fin N → ℝ)}
    (hp : p ∈ feasible7 κ xhat yhat) : 0 ≤ objective7 ε p := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : ∀ i, 0 ≤ p.2.2 i := fun i => (dre2_logloss_pos _ _ _).le.trans (hp.1 i)
  have hlam : 0 ≤ p.2.1 := (norm_nonneg _).trans hp.2.2
  show 0 ≤ p.2.1 * ε + (N : ℝ)⁻¹ * ∑ i, p.2.2 i
  have : 0 ≤ ∑ i, p.2.2 i := Finset.sum_nonneg fun i _ => hs i
  exact add_nonneg (mul_nonneg hlam hε) (mul_nonneg (inv_nonneg.mpr hNpos.le) this)

open MeasureTheory DRLogReg.Reformulation in
theorem dr72_inner
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool) (β : V →L[ℝ] ℝ) :
    ∃ v : ℝ, IsLeast ((fun q : ℝ × (Fin N → ℝ) => objective7 ε (β, q)) ''
        {q | (β, q) ∈ feasible7 κ xhat yhat}) v ∧
      worstCase κ ε xhat yhat β = ENNReal.ofReal v := by
  have hwk : ∀ p ∈ feasible7 κ xhat yhat,
      worstCase κ ε xhat yhat p.1 ≤ ENNReal.ofReal (objective7 ε p) :=
    fun p hp => iSup₂_le fun Q hQ => dre2_weak hκ.le hε hN hp hQ
  obtain ⟨p, hp, hpβ, hδ⟩ := dre2_strong hκ hε hN xhat yhat β
  have hst : ENNReal.ofReal (objective7 ε p) ≤ worstCase κ ε xhat yhat β := by
    apply ENNReal.le_of_forall_pos_le_add
    intro δ hδpos _
    obtain ⟨Q, hQ, hQle⟩ := hδ δ (by exact_mod_cast hδpos)
    have h1 : ∫⁻ ξ, ENNReal.ofReal (logloss β ξ.1 ξ.2) ∂Q ≤ worstCase κ ε xhat yhat β :=
      le_iSup₂ (f := fun Q (_ : Q ∈ wassersteinBall κ ε (empirical xhat yhat)) =>
        ∫⁻ ξ, ENNReal.ofReal (logloss β ξ.1 ξ.2) ∂Q) Q hQ
    calc ENNReal.ofReal (objective7 ε p)
        = ENNReal.ofReal ((objective7 ε p - δ) + δ) := by congr 1; ring
      _ ≤ ENNReal.ofReal (objective7 ε p - δ) + ENNReal.ofReal δ := ENNReal.ofReal_add_le
      _ ≤ worstCase κ ε xhat yhat β + δ := by
          rw [ENNReal.ofReal_coe_nnreal]
          gcongr
          exact hQle.trans h1
  have hpe : p = (β, p.2) := by rw [← hpβ]
  have hp' : p.2 ∈ {q : ℝ × (Fin N → ℝ) | (β, q) ∈ feasible7 κ xhat yhat} := by
    show (β, p.2) ∈ feasible7 κ xhat yhat
    rw [← hpe]; exact hp
  have hwkp : worstCase κ ε xhat yhat β ≤ ENNReal.ofReal (objective7 ε p) := by
    have := hwk p hp
    rwa [hpβ] at this
  refine ⟨objective7 ε p, ⟨⟨p.2, hp', ?_⟩, ?_⟩, le_antisymm hwkp hst⟩
  · show objective7 ε (β, p.2) = objective7 ε p
    rw [← hpe]
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : ((β, q) : (V →L[ℝ] ℝ) × ℝ × (Fin N → ℝ)) ∈ feasible7 κ xhat yhat := hq
    have h1 : ENNReal.ofReal (objective7 ε p) ≤ ENNReal.ofReal (objective7 ε (β, q)) :=
      hst.trans (hwk (β, q) hq')
    exact (ENNReal.ofReal_le_ofReal_iff (dr83_obj_nonneg hε hN hq')).mp h1

open MeasureTheory DRLogReg.Reformulation in
theorem solution
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool) (β : V →L[ℝ] ℝ) :
    worstCase κ 0 xhat yhat β =
      ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i, logloss β (xhat i) (yhat i)) := by
  obtain ⟨v, hv, hw⟩ := dr72_inner hκ (le_refl (0 : ℝ)) hN xhat yhat β
  rw [hw]
  congr 1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  apply le_antisymm
  · -- feasible point achieving the average
    set M : ℝ := ∑ i, logloss β (xhat i) (!yhat i) with hM
    have hMi : ∀ i, logloss β (xhat i) (!yhat i) ≤ M := fun i =>
      Finset.single_le_sum (f := fun i => logloss β (xhat i) (!yhat i))
        (fun j _ => (dre2_logloss_pos _ _ _).le) (Finset.mem_univ i)
    have hM0 : 0 ≤ M := Finset.sum_nonneg fun j _ => (dre2_logloss_pos _ _ _).le
    have hmem : ((‖β‖ + M / κ, fun i => logloss β (xhat i) (yhat i)) : ℝ × (Fin N → ℝ)) ∈
        {q : ℝ × (Fin N → ℝ) | (β, q) ∈ feasible7 κ xhat yhat} := by
      refine ⟨fun i => le_refl _, fun i => ?_, ?_⟩
      · show logloss β (xhat i) (!yhat i) - (‖β‖ + M / κ) * κ ≤ logloss β (xhat i) (yhat i)
        have h1 : (‖β‖ + M / κ) * κ = ‖β‖ * κ + M := by field_simp
        have h2 : 0 ≤ ‖β‖ * κ := mul_nonneg (norm_nonneg _) hκ.le
        have h3 := dre2_logloss_pos β (xhat i) (yhat i)
        have h4 := hMi i
        linarith
      · show ‖β‖ ≤ ‖β‖ + M / κ
        have : 0 ≤ M / κ := div_nonneg hM0 hκ.le
        linarith
    have := hv.2 ⟨_, hmem, rfl⟩
    simpa [objective7] using this
  · obtain ⟨⟨q, hq, hqv⟩, _⟩ := hv
    rw [← hqv]
    have hq' : ((β, q) : (V →L[ℝ] ℝ) × ℝ × (Fin N → ℝ)) ∈ feasible7 κ xhat yhat := hq
    show (N : ℝ)⁻¹ * ∑ i, logloss β (xhat i) (yhat i) ≤ q.1 * 0 + (N : ℝ)⁻¹ * ∑ i, q.2 i
    rw [mul_zero, zero_add]
    gcongr with i
    exact hq'.1 i
