-- Prove2me | solution 1 for CVPricing.CertEquiv.ce_pricing_inconsistent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T00:09:25.72913+00:00
-- url     : https://prove2.me/submissions/4026a3d4-c433-447d-ab14-946d06c88203

import Mathlib
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_CVPricing_CertEquiv_CEPrice

set_option autoImplicit false

theorem c91_split (f : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n) :
    ∑ s ∈ Finset.Icc 1 n, f s = f 1 + f 2 + ∑ s ∈ Finset.Icc 3 n, f s := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [show Finset.Icc 3 2 = (∅ : Finset ℕ) from rfl,
      show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from rfl]
    simp
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
    ring

theorem c91_const (f : ℕ → ℝ) (c : ℝ) {n : ℕ} (hn : 2 ≤ n)
    (hf : ∀ i : ℕ, 3 ≤ i → i ≤ n → f i = c) :
    ∑ s ∈ Finset.Icc 3 n, f s = ((n : ℝ) - 2) * c := by
  rw [Finset.sum_congr rfl (fun i hi => hf i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2),
    Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  congr 1
  rw [show n + 1 - 3 = n - 2 by omega, Nat.cast_sub hn]
  norm_num

theorem c91_const_add (f g : ℕ → ℝ) (c : ℝ) {n : ℕ} (hn : 2 ≤ n)
    (hf : ∀ i : ℕ, 3 ≤ i → i ≤ n → f i = c + g i) :
    ∑ s ∈ Finset.Icc 3 n, f s = ((n : ℝ) - 2) * c + ∑ s ∈ Finset.Icc 3 n, g s := by
  rw [Finset.sum_congr rfl (fun i hi => hf i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2),
    Finset.sum_add_distrib, c91_const (fun _ => c) c hn (fun _ _ _ => rfl)]

open KeskinZeevi.SufficientConditions in
theorem c91_slope (q D : ℕ → ℝ) (n : ℕ) :
    (lsEstimateOf q D n).2 =
      ((n : ℝ) * ∑ s ∈ Finset.Icc 1 n, D s * q s
          - (∑ s ∈ Finset.Icc 1 n, D s) * ∑ s ∈ Finset.Icc 1 n, q s) /
        ((n : ℝ) * ∑ s ∈ Finset.Icc 1 n, q s ^ 2 - (∑ s ∈ Finset.Icc 1 n, q s) ^ 2) := by
  have hF : fisherOf q n = !![(n : ℝ), ∑ s ∈ Finset.Icc 1 n, q s;
      ∑ s ∈ Finset.Icc 1 n, q s, ∑ s ∈ Finset.Icc 1 n, q s ^ 2] := by
    unfold fisherOf
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.sum_apply]
  unfold lsEstimateOf
  simp only [hF, Matrix.inv_def, Matrix.adjugate_fin_two_of, Matrix.det_fin_two_of,
    Ring.inverse_eq_inv']
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

open KeskinZeevi.SufficientConditions CVPricing.CertEquiv in
theorem c91_stuck (M : CVPricing.CertEquiv.Model) {p₁ p₂ : ℝ} (hp₁ : p₁ ∈ Set.Icc M.pl M.ph)
    (hp₂ : p₂ ∈ Set.Icc M.pl M.ph) (e : ℕ → ℝ) (N : ℝ)
    (h1 : -M.a₁ * (p₂ - p₁) ^ 2 ≤ (p₂ - p₁) * (e 2 - e 1))
    (h2 : -M.a₁ * ((p₁ - M.ph) ^ 2 + (p₂ - M.ph) ^ 2) + (2 * M.ph - p₁ - p₂) * N ≤
      (p₁ - M.ph) * e 1 + (p₂ - M.ph) * e 2)
    (htail : ∀ n : ℕ, 2 ≤ n → |∑ s ∈ Finset.Icc 3 n, e s| ≤ N * ((n : ℝ) - 2)) :
    ∀ t : ℕ, 3 ≤ t → cePrice M p₁ p₂ e t = M.ph := by
  have c1 : cePrice M p₁ p₂ e 1 = p₁ := by rw [cePrice]; simp
  have c2 : cePrice M p₁ p₂ e 2 = p₂ := by rw [cePrice]; simp
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro ht
  rw [cePrice, if_neg (by omega), if_neg (by omega)]
  have hn2 : 2 ≤ t - 1 := by omega
  set n := t - 1 with hn
  set q : ℕ → ℝ := fun s => if s < t then cePrice M p₁ p₂ e s else 0 with hq
  set D : ℕ → ℝ := fun s => if s < t then M.a₀ + M.a₁ * cePrice M p₁ p₂ e s + e s else 0
    with hD
  have hq1 : q 1 = p₁ := by simp only [hq, if_pos (show 1 < t by omega), c1]
  have hq2 : q 2 = p₂ := by simp only [hq, if_pos (show 2 < t by omega), c2]
  have hD1 : D 1 = M.a₀ + M.a₁ * p₁ + e 1 := by simp only [hD, if_pos (show 1 < t by omega), c1]
  have hD2 : D 2 = M.a₀ + M.a₁ * p₂ + e 2 := by simp only [hD, if_pos (show 2 < t by omega), c2]
  have hqi : ∀ i, 3 ≤ i → i ≤ n → q i = M.ph := by
    intro i hi hin
    simp only [hq, if_pos (show i < t by omega)]
    exact ih i (by omega) hi
  have hDi : ∀ i, 3 ≤ i → i ≤ n → D i = (M.a₀ + M.a₁ * M.ph) + e i := by
    intro i hi hin
    simp only [hD, if_pos (show i < t by omega)]
    rw [ih i (by omega) hi]
  have hSq : ∑ s ∈ Finset.Icc 1 n, q s = p₁ + p₂ + ((n : ℝ) - 2) * M.ph := by
    rw [c91_split _ hn2, c91_const _ _ hn2 hqi, hq1, hq2]
  have hSq2 : ∑ s ∈ Finset.Icc 1 n, q s ^ 2 = p₁ ^ 2 + p₂ ^ 2 + ((n : ℝ) - 2) * M.ph ^ 2 := by
    rw [c91_split _ hn2, c91_const (fun s => q s ^ 2) (M.ph ^ 2) hn2
      (fun i hi hin => by simp only [hqi i hi hin]), hq1, hq2]
  have hSD : ∑ s ∈ Finset.Icc 1 n, D s = (M.a₀ + M.a₁ * p₁ + e 1) + (M.a₀ + M.a₁ * p₂ + e 2)
      + (((n : ℝ) - 2) * (M.a₀ + M.a₁ * M.ph) + ∑ s ∈ Finset.Icc 3 n, e s) := by
    rw [c91_split _ hn2, c91_const_add _ _ _ hn2 hDi, hD1, hD2]
  have hSDq : ∑ s ∈ Finset.Icc 1 n, D s * q s
      = (M.a₀ + M.a₁ * p₁ + e 1) * p₁ + (M.a₀ + M.a₁ * p₂ + e 2) * p₂
        + (((n : ℝ) - 2) * ((M.a₀ + M.a₁ * M.ph) * M.ph)
          + ∑ s ∈ Finset.Icc 3 n, M.ph * e s) := by
    rw [c91_split _ hn2, c91_const_add (fun s => D s * q s) (fun s => M.ph * e s) ((M.a₀ + M.a₁ * M.ph) * M.ph) hn2
      (fun i hi hin => by rw [hDi i hi hin, hqi i hi hin]; ring), hD1, hD2, hq1, hq2]
  rw [← Finset.mul_sum] at hSDq
  unfold ceRule
  rw [if_pos]
  rw [c91_slope, hSq, hSq2, hSD, hSDq]
  set R := ∑ s ∈ Finset.Icc 3 n, e s
  set k : ℝ := (n : ℝ) - 2 with hk
  have hk0 : 0 ≤ k := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hnk : (n : ℝ) = k + 2 := by rw [hk]; ring
  rw [hnk]
  have hR := htail n hn2
  rw [← hk] at hR
  have hc : 0 ≤ 2 * M.ph - p₁ - p₂ := by linarith [hp₁.2, hp₂.2]
  have hRl : -(N * k) ≤ R := (abs_le.1 hR).1
  have hcR : (2 * M.ph - p₁ - p₂) * (-(N * k)) ≤ (2 * M.ph - p₁ - p₂) * R :=
    mul_le_mul_of_nonneg_left hRl hc
  have hk2 := mul_le_mul_of_nonneg_left h2 hk0
  have ha := M.a₁_neg
  apply div_nonneg
  · have hdet : 0 ≤ (p₁ - p₂) ^ 2 + k * ((p₁ - M.ph) ^ 2 + (p₂ - M.ph) ^ 2) := by positivity
    nlinarith
  · have : (k + 2) * (p₁ ^ 2 + p₂ ^ 2 + k * M.ph ^ 2) - (p₁ + p₂ + k * M.ph) ^ 2
        = (p₁ - p₂) ^ 2 + k * ((p₁ - M.ph) ^ 2 + (p₂ - M.ph) ^ 2) := by ring
    rw [this]
    positivity

theorem c91_tail_meas {Ω : Type*} [MeasurableSpace Ω] (ε : ℕ → Ω → ℝ)
    (hT : ∀ i, 2 ≤ i → Measurable (ε i)) (N : ℕ) :
    MeasurableSet {ω | ∀ m : ℕ, |∑ k ∈ Finset.range m, ε (k + 2) ω| ≤ (N : ℝ) * m} := by
  have : {ω | ∀ m : ℕ, |∑ k ∈ Finset.range m, ε (k + 2) ω| ≤ (N : ℝ) * m}
      = ⋂ m : ℕ, {ω | |∑ k ∈ Finset.range m, ε (k + 2) ω| ≤ (N : ℝ) * m} := by
    ext ω; simp
  rw [this]
  refine MeasurableSet.iInter fun m => measurableSet_le ?_ measurable_const
  exact (Finset.measurable_sum _ fun k _ => hT (k + 2) (by omega)).abs

theorem c91_head_meas {Ω : Type*} [MeasurableSpace Ω] (ε : ℕ → Ω → ℝ)
    (h0 : Measurable (ε 0)) (h1 : Measurable (ε 1)) (a₁ b₁ a₂ b₂ : ℝ) :
    MeasurableSet ({ω | ε 0 ω ∈ Set.Icc a₁ b₁} ∩ {ω | ε 1 ω ∈ Set.Icc a₂ b₂}) :=
  (h0 measurableSet_Icc).inter (h1 measurableSet_Icc)

open MeasureTheory ProbabilityTheory Filter Topology in
theorem c91_tail_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {σ : ℝ} {ε : ℕ → Ω → ℝ} (hε : RobustBooking.Shared.GaussianNoise σ P ε) :
    ∃ N : ℕ, 0 < P {ω | ∀ m : ℕ, |∑ k ∈ Finset.range m, ε (k + 2) ω| ≤ (N : ℝ) * m} := by
  set X : ℕ → Ω → ℝ := fun k => ε (k + 2) with hX
  have hint : Integrable (X 0) P := by
    have : Integrable id (P.map (ε 2)) := by
      rw [hε.law 2]
      exact (memLp_id_gaussianReal 1).integrable (by simp)
    exact this.comp_measurable (hε.measurable 2)
  have hindep : Pairwise (fun i j => IndepFun (X i) (X j) P) := by
    intro i j hij
    exact hε.indep.indepFun (fun h => hij (by omega))
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    ⟨(hε.measurable _).aemeasurable, (hε.measurable _).aemeasurable, by
      simp only [hX]; rw [hε.law, hε.law]⟩
  have hslln := strong_law_ae X hint hindep hident
  have hae : ∀ᵐ ω ∂P, ω ∈ ⋃ N : ℕ,
      {ω | ∀ m : ℕ, |∑ k ∈ Finset.range m, ε (k + 2) ω| ≤ (N : ℝ) * m} := by
    filter_upwards [hslln] with ω hω
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hω)
    refine Set.mem_iUnion.2 ⟨⌈C⌉₊, fun m => ?_⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have h := hC _ (Set.mem_range_self m)
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    rw [Real.norm_eq_abs, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hmR] at h
    have h' : |∑ k ∈ Finset.range m, X k ω| ≤ C * m := by
      rw [inv_mul_le_iff₀ hmR] at h; linarith
    have hCN : C * m ≤ (⌈C⌉₊ : ℝ) * m :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil C) hmR.le
    exact h'.trans hCN
  by_contra hcon
  push Not at hcon
  have hnull : P (⋃ N : ℕ,
      {ω | ∀ m : ℕ, |∑ k ∈ Finset.range m, ε (k + 2) ω| ≤ (N : ℝ) * m}) = 0 :=
    measure_iUnion_null fun N => le_antisymm (hcon N) bot_le
  have h2 := measure_eq_zero_iff_ae_notMem.1 hnull
  obtain ⟨ω, h1, h3⟩ := (hae.and h2).exists
  exact h3 h1

open MeasureTheory ProbabilityTheory in
theorem c91_gauss_pos {σ : ℝ} (hσ : 0 < σ) {a b : ℝ} (hab : a < b) :
    0 < gaussianReal 0 (σ ^ 2).toNNReal (Set.Icc a b) := by
  have hv : (σ ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  have hac := gaussianReal_absolutelyContinuous' 0 hv
  rw [pos_iff_ne_zero]
  intro h
  have := hac h
  rw [Real.volume_Icc, ENNReal.ofReal_eq_zero] at this
  linarith

open MeasureTheory ProbabilityTheory in
theorem c91_prod_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {σ : ℝ} (hσ : 0 < σ) {ε : ℕ → Ω → ℝ} (hε : RobustBooking.Shared.GaussianNoise σ P ε)
    {a₁ b₁ a₂ b₂ : ℝ} (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂) (N : ℕ)
    (hN : 0 < P {ω | ∀ m : ℕ, |∑ k ∈ Finset.range m, ε (k + 2) ω| ≤ (N : ℝ) * m}) :
    0 < P ({ω | ε 0 ω ∈ Set.Icc a₁ b₁} ∩ {ω | ε 1 ω ∈ Set.Icc a₂ b₂} ∩
      {ω | ∀ m : ℕ, |∑ k ∈ Finset.range m, ε (k + 2) ω| ≤ (N : ℝ) * m}) := by
  set m : ℕ → MeasurableSpace Ω := fun i => MeasurableSpace.comap (ε i) inferInstance with hm
  have hle : ∀ i, m i ≤ (inferInstance : MeasurableSpace Ω) := fun i =>
    (hε.measurable i).comap_le
  have hind : iIndep m P := (iIndepFun_iff_iIndep _ ε P).1 hε.indep
  have hdisj : Disjoint ({0, 1} : Set ℕ) {i | 2 ≤ i} := by
    rw [Set.disjoint_left]
    intro i hi hi2
    rcases hi with rfl | rfl <;> simp at hi2
  have hI := indep_iSup_of_disjoint hle hind hdisj
  have hmeasS : ∀ i ∈ ({0, 1} : Set ℕ), Measurable[⨆ j ∈ ({0, 1} : Set ℕ), m j] (ε i) :=
    fun i hi => Measurable.of_comap_le (le_iSup₂_of_le i hi le_rfl)
  have hmeasT : ∀ i, 2 ≤ i → Measurable[⨆ j ∈ {i : ℕ | 2 ≤ i}, m j] (ε i) :=
    fun i hi => Measurable.of_comap_le (le_iSup₂_of_le (f := fun j (_ : j ∈ {i : ℕ | 2 ≤ i}) => m j) i hi le_rfl)
  have hA := @c91_head_meas Ω (⨆ j ∈ ({0, 1} : Set ℕ), m j) ε (hmeasS 0 (by simp))
    (hmeasS 1 (by simp)) a₁ b₁ a₂ b₂
  have hB := @c91_tail_meas Ω (⨆ j ∈ {i : ℕ | 2 ≤ i}, m j) ε hmeasT N
  rw [(Indep_iff _ _ P).1 hI _ _ hA hB]
  have h01 : IndepFun (ε 0) (ε 1) P := hε.indep.indepFun (by norm_num)
  have hhead := h01.measure_inter_preimage_eq_mul (Set.Icc a₁ b₁) (Set.Icc a₂ b₂)
    measurableSet_Icc measurableSet_Icc
  have hp0 : P (ε 0 ⁻¹' Set.Icc a₁ b₁) = gaussianReal 0 (σ ^ 2).toNNReal (Set.Icc a₁ b₁) := by
    rw [← hε.law 0, Measure.map_apply (hε.measurable 0) measurableSet_Icc]
  have hp1 : P (ε 1 ⁻¹' Set.Icc a₂ b₂) = gaussianReal 0 (σ ^ 2).toNNReal (Set.Icc a₂ b₂) := by
    rw [← hε.law 1, Measure.map_apply (hε.measurable 1) measurableSet_Icc]
  change 0 < P (ε 0 ⁻¹' Set.Icc a₁ b₁ ∩ ε 1 ⁻¹' Set.Icc a₂ b₂) * _
  rw [hhead, hp0, hp1]
  exact ENNReal.mul_pos (ENNReal.mul_pos (c91_gauss_pos hσ hab₁).ne' (c91_gauss_pos hσ hab₂).ne').ne'
    hN.ne'

open CVPricing.CertEquiv Filter Topology in
theorem c91_final (M : CVPricing.CertEquiv.Model) {p₁ p₂ : ℝ} (hp₁ : p₁ ∈ Set.Icc M.pl M.ph)
    (hp₂ : p₂ ∈ Set.Icc M.pl M.ph) (e : ℕ → ℝ) (N : ℕ)
    (h1 : -M.a₁ * (p₂ - p₁) ^ 2 ≤ (p₂ - p₁) * (e 2 - e 1))
    (h2 : -M.a₁ * ((p₁ - M.ph) ^ 2 + (p₂ - M.ph) ^ 2) + (2 * M.ph - p₁ - p₂) * N ≤
      (p₁ - M.ph) * e 1 + (p₂ - M.ph) * e 2)
    (hT : ∀ m : ℕ, |∑ k ∈ Finset.range m, e (k + 3)| ≤ (N : ℝ) * m) :
    ¬ Tendsto (fun t => cePrice M p₁ p₂ e t) atTop (𝓝 (optPrice M)) := by
  have htail : ∀ n : ℕ, 2 ≤ n → |∑ s ∈ Finset.Icc 3 n, e s| ≤ (N : ℝ) * ((n : ℝ) - 2) := by
    intro n hn
    have hs : ∑ s ∈ Finset.Icc 3 n, e s = ∑ k ∈ Finset.range (n - 2), e (k + 3) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
        show n + 1 - 3 = n - 2 by omega]
      exact Finset.sum_congr rfl fun k _ => by rw [add_comm]
    rw [hs]
    have := hT (n - 2)
    rwa [Nat.cast_sub hn, Nat.cast_ofNat] at this
  have hstuck := c91_stuck M hp₁ hp₂ e N h1 h2 htail
  intro hT'
  have hph : Tendsto (fun t => cePrice M p₁ p₂ e t) atTop (𝓝 M.ph) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with t ht
    exact (hstuck t ht).symm
  have heq := tendsto_nhds_unique hT' hph
  have := M.opt_mem.2
  unfold optPrice at heq
  linarith

open CVPricing.CertEquiv MeasureTheory ProbabilityTheory Filter Topology in
theorem solution (M : Model) {p₁ p₂ : ℝ} (hp₁ : p₁ ∈ Set.Icc M.pl M.ph)
    (hp₂ : p₂ ∈ Set.Icc M.pl M.ph) (hne : p₁ ≠ p₂)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ε : ℕ → Ω → ℝ} (hε : RobustBooking.Shared.GaussianNoise M.σ P ε) :
    0 < P {ω | ¬ Tendsto (fun t => cePrice M p₁ p₂ (fun i => ε (i - 1) ω) t) atTop
      (𝓝 (optPrice M))} := by
  obtain ⟨N, hN⟩ := c91_tail_pos hε
  have ha := M.a₁_neg
  have hph1 := hp₁.2
  have hph2 := hp₂.2
  have hc : 0 ≤ 2 * M.ph - p₁ - p₂ := by linarith
  have hNc : 0 ≤ (2 * M.ph - p₁ - p₂) * (N : ℝ) := mul_nonneg hc (Nat.cast_nonneg N)
  have t1 : 0 ≤ -M.a₁ * (p₂ - p₁) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have t2 : 0 ≤ -M.a₁ * ((p₁ - M.ph) ^ 2 + (p₂ - M.ph) ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  set K : ℝ := -M.a₁ * (p₂ - p₁) ^ 2 + -M.a₁ * ((p₁ - M.ph) ^ 2 + (p₂ - M.ph) ^ 2)
    + (2 * M.ph - p₁ - p₂) * N + (M.ph - p₁) + (M.ph - p₂) + 1 with hK
  have hK0 : 0 < K := by linarith
  rcases lt_or_gt_of_ne hne with h12 | h12
  · obtain ⟨L, hL⟩ : ∃ L : ℝ, (p₂ - p₁) * L = K :=
      ⟨K / (p₂ - p₁), by field_simp [(sub_pos.2 h12).ne']⟩
    have hpos := c91_prod_pos M.σ_pos hε (a₁ := -L - 1) (b₁ := -L) (a₂ := L) (b₂ := L + 1)
      (by linarith) (by linarith) N hN
    refine lt_of_lt_of_le hpos (measure_mono ?_)
    rintro ω ⟨⟨h0, h1⟩, hT⟩
    have h0 : ε 0 ω ∈ Set.Icc (-L - 1) (-L) := h0
    have h1 : ε 1 ω ∈ Set.Icc L (L + 1) := h1
    obtain ⟨h0a, h0b⟩ := h0
    obtain ⟨h1a, h1b⟩ := h1
    refine c91_final M hp₁ hp₂ (fun i => ε (i - 1) ω) N ?_ ?_ (fun m => hT m)
    · show -M.a₁ * (p₂ - p₁) ^ 2 ≤ (p₂ - p₁) * (ε 1 ω - ε 0 ω)
      nlinarith [mul_le_mul_of_nonneg_left (show 2 * L ≤ ε 1 ω - ε 0 ω by linarith)
        (sub_nonneg.2 h12.le)]
    · show _ ≤ (p₁ - M.ph) * ε 0 ω + (p₂ - M.ph) * ε 1 ω
      nlinarith [mul_nonneg (sub_nonneg.2 hph1) (show 0 ≤ -L - ε 0 ω by linarith),
        mul_nonneg (sub_nonneg.2 hph2) (show 0 ≤ L + 1 - ε 1 ω by linarith)]
  · obtain ⟨L, hL⟩ : ∃ L : ℝ, (p₁ - p₂) * L = K :=
      ⟨K / (p₁ - p₂), by field_simp [(sub_pos.2 h12).ne']⟩
    have hpos := c91_prod_pos M.σ_pos hε (a₁ := L) (b₁ := L + 1) (a₂ := -L - 1) (b₂ := -L)
      (by linarith) (by linarith) N hN
    refine lt_of_lt_of_le hpos (measure_mono ?_)
    rintro ω ⟨⟨h0, h1⟩, hT⟩
    have h0 : ε 0 ω ∈ Set.Icc L (L + 1) := h0
    have h1 : ε 1 ω ∈ Set.Icc (-L - 1) (-L) := h1
    obtain ⟨h0a, h0b⟩ := h0
    obtain ⟨h1a, h1b⟩ := h1
    refine c91_final M hp₁ hp₂ (fun i => ε (i - 1) ω) N ?_ ?_ (fun m => hT m)
    · show -M.a₁ * (p₂ - p₁) ^ 2 ≤ (p₂ - p₁) * (ε 1 ω - ε 0 ω)
      nlinarith [mul_le_mul_of_nonneg_left (show 2 * L ≤ ε 0 ω - ε 1 ω by linarith)
        (sub_nonneg.2 h12.le)]
    · show _ ≤ (p₁ - M.ph) * ε 0 ω + (p₂ - M.ph) * ε 1 ω
      nlinarith [mul_nonneg (sub_nonneg.2 hph1) (show 0 ≤ L + 1 - ε 0 ω by linarith),
        mul_nonneg (sub_nonneg.2 hph2) (show 0 ≤ -L - ε 1 ω by linarith)]
