-- Prove2me | solution 1 for Cohen2019.Tight.radius_tight
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T12:32:24.142071+00:00
-- url     : https://prove2.me/submissions/19b3011e-9b8b-4a23-bc2e-b133e94e7247

import Mathlib
import Definitions.Def_Cohen2019_Tight_Model
import Definitions.Def_Cohen2019_Tight_HalfSpaces

set_option autoImplicit false

open MeasureTheory ProbabilityTheory in
theorem p9c_phi_strictMono : StrictMono Cohen2019.Robust.Phi := by
  intro a b hab
  unfold Cohen2019.Robust.Phi
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  have hpos : (gaussianReal 0 1) (Set.Ioc a b) ≠ 0 := by
    intro h
    have h2 := gaussianReal_absolutelyContinuous' (0 : ℝ) hv h
    rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at h2
    linarith
  have hm := (cdf (gaussianReal 0 1)).measure_Ioc a b
  rw [measure_cdf] at hm
  rw [hm] at hpos
  have : ¬ (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a ≤ 0) := by
    intro hle; exact hpos (ENNReal.ofReal_eq_zero.mpr hle)
  linarith

open MeasureTheory ProbabilityTheory in
theorem p9c_phi_continuous : Continuous Cohen2019.Robust.Phi := by
  have hfun : Cohen2019.Robust.Phi = fun t => cdf (gaussianReal 0 1) t := rfl
  rw [hfun, continuous_iff_continuousAt]
  intro a
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [(monotone_cdf (gaussianReal 0 1)).continuousAt_iff_leftLim_eq_rightLim,
    StieltjesFunction.rightLim_eq]
  have hs := (cdf (gaussianReal 0 1)).measure_singleton a
  rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero] at hs
  have hle := (monotone_cdf (gaussianReal 0 1)).leftLim_le (le_refl a)
  linarith

open MeasureTheory ProbabilityTheory Filter in
theorem p9c_phi_inv {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Cohen2019.Robust.Phi (Cohen2019.Robust.PhiInvReal q) = q := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot (gaussianReal 0 1)).eventually
    (Iio_mem_nhds hq0)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually
    (Ioi_mem_nhds hq1)).exists
  have hmem : q ∈ Set.Icc (Cohen2019.Robust.Phi a) (Cohen2019.Robust.Phi b) :=
    ⟨le_of_lt ha, le_of_lt hb⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ a b p9c_phi_continuous hmem
  have hS : {s : ℝ | q ≤ Cohen2019.Robust.Phi s} = Set.Ici t := by
    ext s
    simp only [Set.mem_Ici]
    rw [← ht]
    exact p9c_phi_strictMono.le_iff_le
  unfold Cohen2019.Robust.PhiInvReal
  rw [hS, csInf_Ici, ht]

open MeasureTheory ProbabilityTheory in
theorem p9c_phi_def (t : ℝ) :
    (gaussianReal 0 1).real (Set.Iic t) = Cohen2019.Robust.Phi t := by
  rw [Cohen2019.Robust.Phi, cdf_eq_real]

open MeasureTheory ProbabilityTheory in
theorem p9c_phi_lt_one (w : ℝ) : Cohen2019.Robust.Phi w < 1 :=
  lt_of_lt_of_le (p9c_phi_strictMono (lt_add_one w)) (cdf_le_one _ _)

open MeasureTheory ProbabilityTheory in
theorem p9c_phi_neg (t : ℝ) : Cohen2019.Robust.Phi (-t) = 1 - Cohen2019.Robust.Phi t := by
  have h := gaussianReal_map_neg (μ := (0:ℝ)) (v := 1)
  rw [neg_zero] at h
  rw [← p9c_phi_def, ← p9c_phi_def]
  have h1 : (gaussianReal 0 1).real (Set.Iic (-t)) = (gaussianReal 0 1).real (Set.Ici t) := by
    conv_lhs => rw [← h]
    rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext y
    simp
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [h1, ← Set.compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio,
    measureReal_congr Iio_ae_eq_Iic]

open MeasureTheory ProbabilityTheory in
theorem p9c_shift_Iic (m t : ℝ) :
    ((gaussianReal 0 1).map (fun w => w + m)).real (Set.Iic t)
      = Cohen2019.Robust.Phi (t - m) := by
  rw [map_measureReal_apply (by fun_prop) measurableSet_Iic, ← p9c_phi_def]
  congr 1
  ext y
  simp [le_sub_iff_add_le]

open MeasureTheory ProbabilityTheory in
theorem p9c_shift_Ioi (m t : ℝ) :
    ((gaussianReal 0 1).map (fun w => w + m)).real (Set.Ioi t)
      = Cohen2019.Robust.Phi (m - t) := by
  have : IsProbabilityMeasure ((gaussianReal 0 1).map (fun w : ℝ => w + m)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, p9c_shift_Iic,
    show m - t = -(t - m) by ring, p9c_phi_neg]

open MeasureTheory ProbabilityTheory in
theorem p9c_lt_mass {q : ℝ} (h0 : 0 < q) (h1 : q < 1) :
    (gaussianReal 0 1).real {w | Cohen2019.Robust.Phi w < q} = q := by
  have hset : {w | Cohen2019.Robust.Phi w < q} = Set.Iio (Cohen2019.Robust.PhiInvReal q) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_Iio]
    have := p9c_phi_strictMono.lt_iff_lt (a := w) (b := Cohen2019.Robust.PhiInvReal q)
    rwa [p9c_phi_inv h0 h1] at this
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [hset, measureReal_congr Iio_ae_eq_Iic, p9c_phi_def, p9c_phi_inv h0 h1]

open MeasureTheory ProbabilityTheory in
theorem p9c_band (α β C : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hC : β - α ≤ C) (hC0 : 0 ≤ C) :
    (gaussianReal 0 1).real {w | α ≤ Cohen2019.Robust.Phi w ∧ Cohen2019.Robust.Phi w < β}
      ≤ C := by
  by_cases hab : α ≤ β
  · have hsub : {w | α ≤ Cohen2019.Robust.Phi w ∧ Cohen2019.Robust.Phi w < β}
        = {w | Cohen2019.Robust.Phi w < β} \ {w | Cohen2019.Robust.Phi w < α} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_diff, not_lt]
      tauto
    have hT : {w | Cohen2019.Robust.Phi w < α} ⊆ {w | Cohen2019.Robust.Phi w < β} :=
      fun w hw => lt_of_lt_of_le hw hab
    have hmT : MeasurableSet {w | Cohen2019.Robust.Phi w < α} :=
      measurableSet_lt p9c_phi_continuous.measurable measurable_const
    rw [hsub, measureReal_sdiff hT hmT, p9c_lt_mass hα0 hα1]
    have : (gaussianReal 0 1).real {w | Cohen2019.Robust.Phi w < β} ≤ β := by
      rcases lt_or_ge β 1 with hb | hb
      · rw [p9c_lt_mass (by linarith) hb]
      · exact measureReal_le_one.trans hb
    linarith
  · have : {w | α ≤ Cohen2019.Robust.Phi w ∧ Cohen2019.Robust.Phi w < β} = ∅ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      linarith [h.1, h.2]
    rw [this, measureReal_empty]
    linarith

open MeasureTheory ProbabilityTheory Cohen2019.Tight in
theorem p9c_transfer {d : ℕ} (x v u : Space d) (σ : ℝ) (hσ : 0 < σ) (hu : ‖u‖ = 1) :
    (gaussNoise (x + v) σ).map (fun z => inner ℝ u (z - x) / σ)
      = (gaussianReal 0 1).map (fun w => w + inner ℝ u v / σ) := by
  set L : StrongDual ℝ (Space d) := innerSL ℝ u with hL
  have hLn : ‖L‖ = 1 := by rw [hL, innerSL_apply_norm, hu]
  have hmapL : (stdGaussian (Space d)).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, hLn]
    simp
  unfold gaussNoise
  rw [Measure.map_map (by fun_prop) (by fun_prop), ← hmapL,
    Measure.map_map (by fun_prop) L.continuous.measurable]
  congr 1
  funext z
  simp only [Function.comp_apply, hL, innerSL_apply_apply]
  rw [show x + v + σ • z - x = v + σ • z by abel, inner_add_right, inner_smul_right]
  field_simp
  ring

/-- Bin index: `0` on `w ≤ a`, otherwise `⌈(1 - Φ w)/pB⌉₊`. -/
noncomputable def p9cK (a pB : ℝ) (w : ℝ) : ℕ :=
  if w ≤ a then 0 else ⌈(1 - Cohen2019.Robust.Phi w) / pB⌉₊

/-- Class map: `0 ↦ cA`, `n ↦ g (n-1)` for `1 ≤ n ≤ N`. -/
def p9cG {Y : Type*} {N : ℕ} (cA : Y) (g : Fin N → Y) (n : ℕ) : Y :=
  if _h : n = 0 then cA else if h' : n - 1 < N then g ⟨n - 1, h'⟩ else cA

theorem p9cK_meas (a pB : ℝ) : Measurable (p9cK a pB) := by
  unfold p9cK
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
    (((measurable_const.sub p9c_phi_continuous.measurable).div_const pB).nat_ceil)

theorem p9cK_zero_iff (a pB w : ℝ) (hpB : 0 < pB) : p9cK a pB w = 0 ↔ w ≤ a := by
  unfold p9cK
  split_ifs with h
  · simp [h]
  · constructor
    · intro h0
      rw [Nat.ceil_eq_zero] at h0
      have := div_pos (sub_pos.mpr (p9c_phi_lt_one w)) hpB
      linarith
    · intro h'
      exact absurd h' h

theorem p9cK_le (a pB pA w : ℝ) (N : ℕ) (hpB : 0 < pB)
    (ha : Cohen2019.Robust.Phi a = pA) (hN : 1 ≤ pA + (N : ℝ) * pB) : p9cK a pB w ≤ N := by
  unfold p9cK
  split_ifs with h
  · exact Nat.zero_le _
  · apply Nat.ceil_le.mpr
    rw [div_le_iff₀ hpB]
    have : Cohen2019.Robust.Phi a < Cohen2019.Robust.Phi w :=
      p9c_phi_strictMono (lt_of_not_ge h)
    linarith

theorem p9cK_band (a pB pA w : ℝ) (j : ℕ) (hj : 1 ≤ j) (hpB : 0 < pB)
    (ha : Cohen2019.Robust.Phi a = pA) (hk : p9cK a pB w = j) :
    max pA (1 - (j : ℝ) * pB) ≤ Cohen2019.Robust.Phi w ∧
      Cohen2019.Robust.Phi w < 1 - ((j : ℝ) - 1) * pB := by
  unfold p9cK at hk
  split_ifs at hk with h
  · omega
  · rw [Nat.ceil_eq_iff (by omega)] at hk
    obtain ⟨h1, h2⟩ := hk
    rw [Nat.cast_sub hj, Nat.cast_one, lt_div_iff₀ hpB] at h1
    rw [div_le_iff₀ hpB] at h2
    have : Cohen2019.Robust.Phi a < Cohen2019.Robust.Phi w :=
      p9c_phi_strictMono (lt_of_not_ge h)
    refine ⟨max_le (by linarith) (by linarith), by linarith⟩

theorem p9cK_one (a c pB w : ℝ) (hpB : 0 < pB) (hac : a ≤ -c)
    (hc : Cohen2019.Robust.Phi (-c) = 1 - pB) (hw : -c < w) : p9cK a pB w = 1 := by
  unfold p9cK
  rw [if_neg (by linarith), Nat.ceil_eq_iff one_ne_zero]
  have h1 : Cohen2019.Robust.Phi (-c) < Cohen2019.Robust.Phi w := p9c_phi_strictMono hw
  have h2 := p9c_phi_lt_one w
  constructor
  · simp only [Nat.sub_self, Nat.cast_zero]
    exact div_pos (by linarith) hpB
  · rw [Nat.cast_one, div_le_iff₀ hpB]
    linarith

theorem p9cG_val {Y : Type*} {N : ℕ} (cA : Y) (g : Fin N → Y) (n : ℕ) (h1 : 1 ≤ n)
    (h2 : n ≤ N) : p9cG cA g n = g ⟨n - 1, by omega⟩ := by
  unfold p9cG
  rw [dif_neg (by omega), dif_pos (by omega)]

theorem p9cG_inj {Y : Type*} {N : ℕ} (cA : Y) (g : Fin N → Y) (s : Finset Y)
    (hcA : cA ∉ s) (hgs : ∀ i, g i ∈ s) (hg : Function.Injective g) (i j : ℕ)
    (hi : i ≤ N) (hj : j ≤ N) (hij : p9cG cA g i = p9cG cA g j) : i = j := by
  rcases Nat.eq_zero_or_pos i with h0 | h0 <;> rcases Nat.eq_zero_or_pos j with h0' | h0'
  · omega
  · exfalso
    rw [h0, p9cG_val cA g j h0' hj] at hij
    unfold p9cG at hij
    simp only [dite_true] at hij
    exact hcA (hij ▸ hgs _)
  · exfalso
    rw [h0', p9cG_val cA g i h0 hi] at hij
    unfold p9cG at hij
    simp only [dite_true] at hij
    exact hcA (hij ▸ hgs _)
  · rw [p9cG_val cA g i h0 hi, p9cG_val cA g j h0' hj] at hij
    have := Fin.mk.inj_iff.mp (hg hij)
    omega

open MeasureTheory ProbabilityTheory in
theorem solution {d : ℕ} {Y : Type*} (σ : ℝ) (hσ : 0 < σ) (x : Cohen2019.Tight.Space d) (cA : Y)
    (pA pB : ℝ) (hpB0 : 0 < pB) (hBA : pB ≤ pA) (hpA1 : pA < 1) (hsum : pA + pB ≤ 1)
    (hcap : ∃ s : Finset Y, cA ∉ s ∧ 1 ≤ pA + (s.card : ℝ) * pB)
    (δ : Cohen2019.Tight.Space d) (hδ : Cohen2019.Tight.radius σ pA pB < ‖δ‖) :
    ∃ f : Cohen2019.Tight.Space d → Y, Cohen2019.Tight.IsMeasurableClassifier f ∧
      Cohen2019.Tight.IsConsistent f σ x cA pA pB ∧
      ∃ c : Y, c ≠ cA ∧ Cohen2019.Tight.classProb f σ (x + δ) cA
        < Cohen2019.Tight.classProb f σ (x + δ) c := by
  classical
  unfold Cohen2019.Tight.radius at hδ
  obtain ⟨s, hAs, hcapN⟩ := hcap
  have hpA0 : 0 < pA := lt_of_lt_of_le hpB0 hBA
  have hpB1 : pB < 1 := lt_of_le_of_lt hBA hpA1
  have hNpos : 0 < s.card := by
    rcases Nat.eq_zero_or_pos s.card with h | h
    · rw [h] at hcapN
      simp at hcapN
      linarith
    · exact h
  set a := Cohen2019.Robust.PhiInvReal pA with ha
  set c := Cohen2019.Robust.PhiInvReal pB with hc
  have hΦa : Cohen2019.Robust.Phi a = pA := p9c_phi_inv hpA0 hpA1
  have hΦc : Cohen2019.Robust.Phi c = pB := p9c_phi_inv hpB0 hpB1
  have hca : c ≤ a := p9c_phi_strictMono.le_iff_le.mp (by rw [hΦa, hΦc]; exact hBA)
  have hΦnc : Cohen2019.Robust.Phi (-c) = 1 - pB := by rw [p9c_phi_neg, hΦc]
  have hac : a ≤ -c := p9c_phi_strictMono.le_iff_le.mp (by rw [hΦa, hΦnc]; linarith)
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hδ
    have : 0 ≤ σ / 2 * (a - c) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hnδ : 0 < ‖δ‖ := norm_pos_iff.mpr hδ0
  set u : Cohen2019.Tight.Space d := ‖δ‖⁻¹ • δ with hu
  have hun : ‖u‖ = 1 := norm_smul_inv_norm hδ0
  have hTm : Measurable (fun z : Cohen2019.Tight.Space d => inner ℝ u (z - x) / σ) := by
    fun_prop
  -- the injection of `Fin N` into `s`
  set N := s.card with hN
  let g : Fin N → Y := fun i => ((s.equivFin.symm i : s) : Y)
  have hg_inj : Function.Injective g := Subtype.val_injective.comp s.equivFin.symm.injective
  have hg_mem : ∀ i, g i ∈ s := fun i => (s.equivFin.symm i).2
  let f : Cohen2019.Tight.Space d → Y :=
    fun z => p9cG cA g (p9cK a pB (inner ℝ u (z - x) / σ))
  have hmS : ∀ c' : Y, MeasurableSet {w | p9cG cA g (p9cK a pB w) = c'} := fun c' =>
    (p9cK_meas a pB) (MeasurableSet.of_discrete (s := {n | p9cG cA g n = c'}))
  -- class probabilities through the transfer lemma
  have hcp : ∀ (v : Cohen2019.Tight.Space d) (c' : Y), Cohen2019.Tight.classProb f σ (x + v) c'
      = ((gaussianReal 0 1).map (fun w => w + inner ℝ u v / σ)).real
          {w | p9cG cA g (p9cK a pB w) = c'} := by
    intro v c'
    rw [← p9c_transfer x v u σ hσ hun, map_measureReal_apply hTm (hmS c')]
    rfl
  have hcp0 : ∀ c' : Y, Cohen2019.Tight.classProb f σ x c'
      = (gaussianReal 0 1).real {w | p9cG cA g (p9cK a pB w) = c'} := by
    intro c'
    have := hcp 0 c'
    rw [add_zero] at this
    rw [this]
    simp only [inner_zero_right, zero_div, add_zero, Measure.map_id']
  have hG0 : p9cG cA g 0 = cA := by unfold p9cG; simp
  have hGne : ∀ n, 1 ≤ n → n ≤ N → p9cG cA g n ≠ cA := by
    intro n h1 h2 heq
    rw [p9cG_val cA g n h1 h2] at heq
    exact hAs (heq ▸ hg_mem _)
  have hkle : ∀ w, p9cK a pB w ≤ N := fun w => p9cK_le a pB pA w N hpB0 hΦa hcapN
  have hsetA : {w | p9cG cA g (p9cK a pB w) = cA} = Set.Iic a := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_Iic]
    rw [← p9cK_zero_iff a pB w hpB0]
    constructor
    · intro h
      by_contra hne
      exact hGne _ (Nat.one_le_iff_ne_zero.mpr hne) (hkle w) h
    · intro h
      rw [h, hG0]
  have hband : ∀ j : ℕ, 1 ≤ j → (gaussianReal 0 1).real {w | p9cK a pB w = j} ≤ pB := by
    intro j hj
    have hsub : {w | p9cK a pB w = j} ⊆ {w | max pA (1 - (j : ℝ) * pB) ≤ Cohen2019.Robust.Phi w
        ∧ Cohen2019.Robust.Phi w < 1 - ((j : ℝ) - 1) * pB} :=
      fun w hw => p9cK_band a pB pA w j hj hpB0 hΦa hw
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hα1 : max pA (1 - (j : ℝ) * pB) < 1 := max_lt hpA1 (by nlinarith)
    have hα0 : 0 < max pA (1 - (j : ℝ) * pB) := lt_of_lt_of_le hpA0 (le_max_left _ _)
    have hm := le_max_right pA (1 - (j : ℝ) * pB)
    have := p9c_band (max pA (1 - (j : ℝ) * pB)) (1 - ((j : ℝ) - 1) * pB) pB hα0 hα1
      (by linarith) hpB0.le
    calc (gaussianReal 0 1).real {w | p9cK a pB w = j}
        ≤ (gaussianReal 0 1).real {w | max pA (1 - (j : ℝ) * pB) ≤ Cohen2019.Robust.Phi w
          ∧ Cohen2019.Robust.Phi w < 1 - ((j : ℝ) - 1) * pB} := measureReal_mono hsub
      _ ≤ pB := by linarith
  refine ⟨f, ?_, ⟨?_, ?_⟩, p9cG cA g 1, hGne 1 le_rfl hNpos, ?_⟩
  · intro c'
    exact hTm (hmS c')
  · rw [hcp0, hsetA, p9c_phi_def, hΦa]
  · intro c' hc'
    rw [hcp0]
    by_cases hex : ∃ w, p9cG cA g (p9cK a pB w) = c'
    · obtain ⟨w₀, hw₀⟩ := hex
      have hj : 1 ≤ p9cK a pB w₀ := by
        by_contra h
        have h0 : p9cK a pB w₀ = 0 := by omega
        rw [h0, hG0] at hw₀
        exact hc' hw₀.symm
      have hsub : {w | p9cG cA g (p9cK a pB w) = c'} ⊆ {w | p9cK a pB w = p9cK a pB w₀} := by
        intro w hw
        exact p9cG_inj cA g s hAs hg_mem hg_inj _ _ (hkle w) (hkle w₀) (hw.trans hw₀.symm)
      exact (measureReal_mono hsub).trans (hband _ hj)
    · push_neg at hex
      have : {w | p9cG cA g (p9cK a pB w) = c'} = ∅ := by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact hex w
      rw [this, measureReal_empty]
      exact hpB0.le
  · rw [hcp, hcp, hsetA, p9c_shift_Iic]
    have hm : inner ℝ u δ / σ = ‖δ‖ / σ := by
      rw [hu, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    rw [hm]
    have hsub : Set.Ioi (-c) ⊆ {w | p9cG cA g (p9cK a pB w) = p9cG cA g 1} := by
      intro w hw
      simp only [Set.mem_setOf_eq]
      rw [p9cK_one a c pB w hpB0 hac hΦnc hw]
    refine lt_of_lt_of_le ?_ (measureReal_mono hsub)
    rw [p9c_shift_Ioi]
    apply p9c_phi_strictMono
    have h2 : a - c < 2 * (‖δ‖ / σ) := by
      rw [mul_div_assoc', lt_div_iff₀ hσ]
      nlinarith
    linarith
