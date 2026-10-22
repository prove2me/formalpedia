-- Prove2me | solution 1 for FrieszDUE.PIE.theorem_2_pie_vip
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T06:26:42.024365+00:00
-- url     : https://prove2.me/submissions/168bf401-53e1-43de-b30f-88286b50655b

import Mathlib
import Definitions.Def_FrieszDUE_PIE_Setting

set_option autoImplicit false

namespace FrieszPIEHelpers

open MeasureTheory FrieszDUE.PIE

lemma nu_univ_ne (T : ℝ) (hT : 0 < T) : ν T Set.univ ≠ 0 := by
  show volume.restrict (Set.Icc (0 : ℝ) T) Set.univ ≠ 0
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
  simpa using hT

lemma essS_bdd (T : ℝ) (hT : 0 < T) (F : ℝ → ℝ) :
    BddAbove {x : ℝ | ν T {t | F t < x} = 0} := by
  by_contra hb
  apply nu_univ_ne T hT
  have hU : (Set.univ : Set ℝ) = ⋃ n : ℕ, {t | F t < n} := by
    ext t
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    exact exists_nat_gt (F t)
  rw [hU]
  apply measure_iUnion_null
  intro n
  rw [not_bddAbove_iff] at hb
  obtain ⟨x, hx, hnx⟩ := hb n
  exact measure_mono_null (fun t (ht : F t < n) => (show F t < x from ht.trans hnx)) hx

lemma zero_mem_S (T : ℝ) (F : ℝ → ℝ) (hF : ∀ t ∈ Set.Icc 0 T, 0 ≤ F t) :
    ν T {t | F t < 0} = 0 := by
  show volume.restrict (Set.Icc (0 : ℝ) T) {t | F t < 0} = 0
  rw [Measure.restrict_apply' measurableSet_Icc]
  have : {t | F t < 0} ∩ Set.Icc 0 T = ∅ := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h ht
    exact absurd (hF t ht) (not_le.2 h)
  rw [this, measure_empty]

lemma essInf_ae (T : ℝ) (hT : 0 < T) (F : ℝ → ℝ) (hF : ∀ t ∈ Set.Icc 0 T, 0 ≤ F t) :
    ν T {t | F t < essInfOn T F} = 0 := by
  have hne : ({x : ℝ | ν T {t | F t < x} = 0}).Nonempty := ⟨0, zero_mem_S T F hF⟩
  have hU : {t | F t < essInfOn T F} = ⋃ n : ℕ, {t | F t < essInfOn T F - 1 / ((n : ℝ) + 1)} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [hU]
  apply measure_iUnion_null
  intro n
  have hlt : essInfOn T F - 1 / ((n : ℝ) + 1) < sSup {x : ℝ | ν T {t | F t < x} = 0} := by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    show essInfOn T F - 1 / ((n : ℝ) + 1) < essInfOn T F
    linarith
  obtain ⟨x, hx, hxl⟩ := exists_lt_of_lt_csSup hne hlt
  exact measure_mono_null
    (fun t (ht : F t < essInfOn T F - 1 / ((n : ℝ) + 1)) => (show F t < x from ht.trans hxl)) hx

lemma le_essInf (T : ℝ) (hT : 0 < T) (F : ℝ → ℝ) (x : ℝ) (hx : ν T {t | F t < x} = 0) :
    x ≤ essInfOn T F :=
  le_csSup (essS_bdd T hT F) hx

lemma int_mul_ind (T : ℝ) {F : ℝ → ℝ} (hF : Integrable F (ν T)) {S : Set ℝ}
    (hS : MeasurableSet S) (c : ℝ) :
    Integrable (fun t => F t * S.indicator (fun _ => c) t) (ν T) ∧
      ∫ t, F t * S.indicator (fun _ => c) t ∂(ν T) = c * ∫ t in S, F t ∂(ν T) := by
  have e : (fun t => F t * S.indicator (fun _ => c) t) = S.indicator (fun t => c * F t) := by
    ext t
    by_cases ht : t ∈ S <;> simp [ht, mul_comm]
  rw [e]
  refine ⟨(hF.const_mul c).indicator hS, ?_⟩
  rw [integral_indicator hS, integral_const_mul]

theorem part1 {P W : Type*} [Fintype P] [DecidableEq W]
    (T : ℝ) (od : P → W) (Q : W → ℝ) (C : P → ℝ → (P → ℝ → ℝ) → ℝ)
    (hs : P → ℝ → ℝ)
    (hC_L2 : ∀ p, MemLp (fun t => C p t hs) 2 (ν T)) (mu : W → ℝ)
    (hE : IsSRDEquilibrium T od Q C hs mu) : IsPIEVISolution T od Q C hs := by
  obtain ⟨hsΛ, -, hEq⟩ := hE
  refine ⟨hsΛ, fun h hΛ => ?_⟩
  have key : ∀ r, mu (od r) * ((∫ t, h r t ∂(ν T)) - ∫ t, hs r t ∂(ν T)) ≤
      ∫ t, C r t hs * (h r t - hs r t) ∂(ν T) := by
    intro r
    have hCi := hC_L2 r
    have hh := hΛ.1 r
    have hhs := hsΛ.1 r
    have i1 : Integrable (fun t => C r t hs * h r t) (ν T) := hCi.integrable_mul hh.1
    have i2 : Integrable (fun t => C r t hs * hs r t) (ν T) := hCi.integrable_mul hhs.1
    have ih : Integrable (h r) (ν T) := hh.1.integrable one_le_two
    have ihs : Integrable (hs r) (ν T) := hhs.1.integrable one_le_two
    have e1 : ∫ t, C r t hs * (h r t - hs r t) ∂(ν T) =
        (∫ t, C r t hs * h r t ∂(ν T)) - ∫ t, C r t hs * hs r t ∂(ν T) := by
      rw [← integral_sub i1 i2]
      congr 1
      ext t
      ring
    have e2 : ∫ t, C r t hs * hs r t ∂(ν T) = ∫ t, mu (od r) * hs r t ∂(ν T) := by
      apply integral_congr_ae
      filter_upwards [(hEq r).1, hhs.2] with t h1 h2
      rcases h2.lt_or_eq with h2 | h2
      · rw [h1 h2]
      · rw [← h2]
        ring
    have e3 : ∫ t, mu (od r) * h r t ∂(ν T) ≤ ∫ t, C r t hs * h r t ∂(ν T) := by
      apply integral_mono_ae (ih.const_mul _) i1
      filter_upwards [(hEq r).2, hh.2] with t h1 h2
      exact mul_le_mul_of_nonneg_right h1 h2
    rw [e1, e2, integral_const_mul]
    rw [integral_const_mul] at e3
    rw [mul_sub]
    linarith
  calc (0 : ℝ) = ∑ r, mu (od r) * ((∫ t, h r t ∂(ν T)) - ∫ t, hs r t ∂(ν T)) := ?_
    _ ≤ _ := Finset.sum_le_sum (fun r _ => key r)
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image od) (g := od)
    (fun i _ => Finset.mem_image_of_mem od (Finset.mem_univ i))]
  symm
  apply Finset.sum_eq_zero
  intro w _
  have hc : ∀ r ∈ Finset.univ.filter (fun r => od r = w),
      mu (od r) * ((∫ t, h r t ∂(ν T)) - ∫ t, hs r t ∂(ν T)) =
        mu w * ((∫ t, h r t ∂(ν T)) - ∫ t, hs r t ∂(ν T)) := by
    intro r hr
    rw [(Finset.mem_filter.1 hr).2]
  rw [Finset.sum_congr rfl hc, ← Finset.mul_sum, Finset.sum_sub_distrib, hΛ.2 w, hsΛ.2 w,
    sub_self, mul_zero]

theorem part2 {P W : Type*} [Fintype P] [DecidableEq W]
    (T : ℝ) (hT : 0 < T) (od : P → W) (Q : W → ℝ) (C : P → ℝ → (P → ℝ → ℝ) → ℝ)
    (hs : P → ℝ → ℝ)
    (hC_nonneg : ∀ p, ∀ t ∈ Set.Icc 0 T, 0 ≤ C p t hs)
    (hC_L2 : ∀ p, MemLp (fun t => C p t hs) 2 (ν T))
    (hVI : IsPIEVISolution T od Q C hs) :
    IsSRDEquilibrium T od Q C hs (muOD T od C hs) := by
  classical
  obtain ⟨hsΛ, hVI⟩ := hVI
  have hle : ∀ p, muOD T od C hs (od p) ≤ muPath T C hs p := fun p =>
    ciInf_le (Set.finite_range _).bddBelow (⟨p, rfl⟩ : {q : P // od q = od p})
  have hlow : ∀ p, ∀ᵐ t ∂(ν T), muOD T od C hs (od p) ≤ C p t hs := by
    intro p
    have h0 := essInf_ae T hT (fun t => C p t hs) (hC_nonneg p)
    rw [ae_iff]
    refine measure_mono_null ?_ h0
    intro t ht
    have ht' : C p t hs < muOD T od C hs (od p) := not_le.1 ht
    show C p t hs < muPath T C hs p
    exact lt_of_lt_of_le ht' (hle p)
  refine ⟨hsΛ, ?_, fun p => ⟨?_, hlow p⟩⟩
  · intro w
    apply Real.iInf_nonneg
    intro q
    exact le_essInf T hT _ 0 (zero_mem_S T _ (hC_nonneg q.1))
  · -- the mass-shift argument
    by_contra hcon
    set m := muOD T od C hs (od p) with hm
    have hgA := (hsΛ.1 p).1.aestronglyMeasurable
    have hfA := (hC_L2 p).aestronglyMeasurable
    have hgm : Measurable (hgA.mk (hs p)) := hgA.stronglyMeasurable_mk.measurable
    have hfm : Measurable (hfA.mk _) := hfA.stronglyMeasurable_mk.measurable
    have hge : hs p =ᵐ[ν T] hgA.mk (hs p) := hgA.ae_eq_mk
    have hfe : (fun t => C p t hs) =ᵐ[ν T] hfA.mk _ := hfA.ae_eq_mk
    set g := hgA.mk (hs p) with hg_def
    set f := hfA.mk (fun t => C p t hs) with hf_def
    let Aset : ℕ → Set ℝ := fun n =>
      {t | 1 / ((n : ℝ) + 1) < g t} ∩ {t | m + 2 / ((n : ℝ) + 1) < f t}
    have hAm : ∀ n, MeasurableSet (Aset n) := fun n =>
      (measurableSet_lt measurable_const hgm).inter (measurableSet_lt measurable_const hfm)
    have hex : ∃ n, ν T (Aset n) ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hcon
      have hnull : ∀ᵐ t ∂(ν T), ∀ n, t ∉ Aset n := by
        rw [ae_all_iff]
        intro n
        rw [ae_iff]
        simpa using hall n
      filter_upwards [hge, hfe, hlow p, hnull] with t h1 h2 h3 h4 hpos
      have h2' : C p t hs = f t := h2
      rw [h2'] at h3 ⊢
      rw [h1] at hpos
      by_contra hne
      have hgt : m < f t := lt_of_le_of_ne h3 (Ne.symm hne)
      have hmin : 0 < min (g t) ((f t - m) / 2) := lt_min hpos (by linarith)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hmin
      apply h4 n
      refine ⟨?_, ?_⟩
      · show 1 / ((n : ℝ) + 1) < g t
        exact lt_of_lt_of_le hn (min_le_left _ _)
      · show m + 2 / ((n : ℝ) + 1) < f t
        have := lt_of_lt_of_le hn (min_le_right _ _)
        have e : 2 / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1)) := by ring
        rw [e]
        linarith
    obtain ⟨n, hAn⟩ := hex
    set δ : ℝ := 1 / ((n : ℝ) + 1) with hδ
    have hδpos : 0 < δ := by positivity
    set A := Aset n with hA_def
    have hA : MeasurableSet A := hAm n
    -- a minimizing path q
    have : Nonempty {q : P // od q = od p} := ⟨⟨p, rfl⟩⟩
    obtain ⟨⟨q, hq⟩, hqm⟩ := exists_eq_ciInf_of_finite
      (f := fun q : {q : P // od q = od p} => muPath T C hs q.1)
    have hqm' : muPath T C hs q = m := hqm
    have hfqA := (hC_L2 q).aestronglyMeasurable
    have hfqm : Measurable (hfqA.mk _) := hfqA.stronglyMeasurable_mk.measurable
    have hfqe : (fun t => C q t hs) =ᵐ[ν T] hfqA.mk _ := hfqA.ae_eq_mk
    set fq := hfqA.mk (fun t => C q t hs) with hfq_def
    set B : Set ℝ := {t | fq t < m + δ} with hB_def
    have hB : MeasurableSet B := measurableSet_lt hfqm measurable_const
    have hBn : ν T B ≠ 0 := by
      intro hB0
      have h1 : ν T {t | C q t hs < m + δ} = 0 := by
        rw [← compl_compl {t | C q t hs < m + δ}]
        have : ∀ᵐ t ∂(ν T), ¬ fq t < m + δ := by
          rw [ae_iff]
          simpa using hB0
        have h2 : ∀ᵐ t ∂(ν T), ¬ C q t hs < m + δ := by
          filter_upwards [this, hfqe] with t ht ht2
          have ht2' : C q t hs = fq t := ht2
          rw [ht2']
          exact ht
        rw [ae_iff] at h2
        simpa using h2
      have h3 : m + δ ≤ muPath T C hs q := le_essInf T hT (fun t => C q t hs) (m + δ) h1
      rw [hqm'] at h3
      linarith
    set a : ℝ := (ν T).real A with ha_def
    set b : ℝ := (ν T).real B with hb_def
    have ha : 0 < a := by
      rw [ha_def, Measure.real]
      exact ENNReal.toReal_pos hAn (measure_ne_top _ _)
    have hb : 0 < b := by
      rw [hb_def, Measure.real]
      exact ENNReal.toReal_pos hBn (measure_ne_top _ _)
    set c : ℝ := δ * a / b with hc_def
    have hc0 : 0 ≤ c := by positivity
    have hcb : c * b = δ * a := by
      rw [hc_def]
      field_simp
    let u : P → ℝ → ℝ := fun r => if r = q then B.indicator (fun _ => c) else 0
    let v : P → ℝ → ℝ := fun r => if r = p then A.indicator (fun _ => δ) else 0
    let h : P → ℝ → ℝ := fun r t => hs r t + u r t - v r t
    have hu_memLp : ∀ r, MemLp (u r) 2 (ν T) := by
      intro r
      by_cases hr : r = q
      · simp only [u, hr, if_true]
        exact memLp_indicator_const 2 hB c (Or.inr (measure_ne_top _ _))
      · simp only [u, hr, if_false]
        exact memLp_const (0 : ℝ)
    have hv_memLp : ∀ r, MemLp (v r) 2 (ν T) := by
      intro r
      by_cases hr : r = p
      · simp only [v, hr, if_true]
        exact memLp_indicator_const 2 hA δ (Or.inr (measure_ne_top _ _))
      · simp only [v, hr, if_false]
        exact memLp_const (0 : ℝ)
    have hu_int : ∀ r, ∫ t, u r t ∂(ν T) = if r = q then b * c else 0 := by
      intro r
      by_cases hr : r = q
      · simp only [u, hr, if_true]
        rw [integral_indicator_const c hB, smul_eq_mul]
      · simp [u, hr]
    have hv_int : ∀ r, ∫ t, v r t ∂(ν T) = if r = p then a * δ else 0 := by
      intro r
      by_cases hr : r = p
      · simp only [v, hr, if_true]
        rw [integral_indicator_const δ hA, smul_eq_mul]
      · simp [v, hr]
    have hΛ : h ∈ Lambda T od Q := by
      refine ⟨fun r => ⟨((hsΛ.1 r).1.add (hu_memLp r)).sub (hv_memLp r), ?_⟩, ?_⟩
      · filter_upwards [(hsΛ.1 r).2, hge] with t h1 h2
        have hu0 : 0 ≤ u r t := by
          by_cases hr : r = q
          · simp only [u, hr, if_true]
            exact Set.indicator_nonneg (fun _ _ => hc0) t
          · simp [u, hr]
        show 0 ≤ hs r t + u r t - v r t
        by_cases hr : r = p
        · subst hr
          by_cases ht : t ∈ A
          · have hvt : v r t = δ := by simp [v, ht]
            have hgt : δ < g t := ht.1
            have h2' : hs r t = g t := h2
            rw [hvt, h2']
            linarith
          · have hvt : v r t = 0 := by simp [v, ht]
            rw [hvt]
            linarith
        · have hvt : v r t = 0 := by simp [v, hr]
          rw [hvt]
          linarith
      · intro w
        have hi : ∀ r, ∫ t, h r t ∂(ν T) =
            (∫ t, hs r t ∂(ν T)) + (if r = q then b * c else 0) - (if r = p then a * δ else 0) := by
          intro r
          have i1 : Integrable (hs r) (ν T) := (hsΛ.1 r).1.integrable one_le_two
          have i2 : Integrable (u r) (ν T) := (hu_memLp r).integrable one_le_two
          have i3 : Integrable (v r) (ν T) := (hv_memLp r).integrable one_le_two
          show ∫ t, hs r t + u r t - v r t ∂(ν T) = _
          have i12 : Integrable (fun t => hs r t + u r t) (ν T) := i1.add i2
          rw [integral_sub i12 i3, integral_add i1 i2, hu_int, hv_int]
        simp only [hi]
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsΛ.2 w, Finset.sum_ite_eq',
          Finset.sum_ite_eq']
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hq]
        by_cases hw : od p = w
        · simp only [hw, if_true]
          rw [mul_comm b c, hcb]
          ring
        · simp [hw]
    have hV := hVI h hΛ
    -- evaluate the VI sum
    have hCint : ∀ r, Integrable (fun t => C r t hs) (ν T) :=
      fun r => (hC_L2 r).integrable one_le_two
    have hterm : ∀ r, ∫ t, C r t hs * (h r t - hs r t) ∂(ν T) =
        (∫ t, C r t hs * u r t ∂(ν T)) - ∫ t, C r t hs * v r t ∂(ν T) := by
      intro r
      have iu : Integrable (fun t => C r t hs * u r t) (ν T) := by
        by_cases hr : r = q
        · simp only [u, hr, if_true]
          exact (int_mul_ind T (hCint q) hB c).1
        · simp [u, hr]
      have iv : Integrable (fun t => C r t hs * v r t) (ν T) := by
        by_cases hr : r = p
        · simp only [v, hr, if_true]
          exact (int_mul_ind T (hCint p) hA δ).1
        · simp [v, hr]
      rw [← integral_sub iu iv]
      congr 1
      ext t
      show C r t hs * (hs r t + u r t - v r t - hs r t) = C r t hs * u r t - C r t hs * v r t
      ring
    have hsu : ∑ r, ∫ t, C r t hs * u r t ∂(ν T) = c * ∫ t in B, C q t hs ∂(ν T) := by
      rw [Finset.sum_eq_single q]
      · simp only [u, if_true]
        exact (int_mul_ind T (hCint q) hB c).2
      · intro r _ hr
        simp [u, hr]
      · intro hq'
        exact absurd (Finset.mem_univ q) hq'
    have hsv : ∑ r, ∫ t, C r t hs * v r t ∂(ν T) = δ * ∫ t in A, C p t hs ∂(ν T) := by
      rw [Finset.sum_eq_single p]
      · simp only [v, if_true]
        exact (int_mul_ind T (hCint p) hA δ).2
      · intro r _ hr
        simp [v, hr]
      · intro hp'
        exact absurd (Finset.mem_univ p) hp'
    simp only [hterm] at hV
    rw [Finset.sum_sub_distrib, hsu, hsv] at hV
    have hIB : ∫ t in B, C q t hs ∂(ν T) ≤ (m + δ) * b := by
      have := setIntegral_mono_on_ae (hCint q).integrableOn
        (integrableOn_const (C := m + δ) (measure_ne_top _ _)) hB
        (by
          filter_upwards [hfqe] with t ht htB
          have ht' : C q t hs = fq t := ht
          rw [ht']
          exact le_of_lt htB)
      rw [setIntegral_const, smul_eq_mul] at this
      rw [mul_comm]
      exact this
    have hIA : (m + 2 * δ) * a ≤ ∫ t in A, C p t hs ∂(ν T) := by
      have := setIntegral_mono_on_ae
        (integrableOn_const (C := m + 2 * δ) (measure_ne_top _ _)) (hCint p).integrableOn hA
        (by
          filter_upwards [hfe] with t ht htA
          have ht' : C p t hs = f t := ht
          rw [ht']
          have h2 : m + 2 / ((n : ℝ) + 1) < f t := htA.2
          have e : 2 / ((n : ℝ) + 1) = 2 * δ := by rw [hδ]; ring
          rw [e] at h2
          exact le_of_lt h2)
      rw [setIntegral_const, smul_eq_mul] at this
      rw [mul_comm]
      exact this
    have k1 : c * ∫ t in B, C q t hs ∂(ν T) ≤ c * ((m + δ) * b) :=
      mul_le_mul_of_nonneg_left hIB hc0
    have k2 : δ * ((m + 2 * δ) * a) ≤ δ * ∫ t in A, C p t hs ∂(ν T) :=
      mul_le_mul_of_nonneg_left hIA hδpos.le
    have k3 : c * ((m + δ) * b) = (m + δ) * (δ * a) := by
      rw [← hcb]
      ring
    have k4 : 0 < δ * a * δ := by positivity
    nlinarith

end FrieszPIEHelpers

open MeasureTheory in
theorem solution {P W : Type*} [Fintype P] [DecidableEq W]
    (T : ℝ) (hT : 0 < T) (od : P → W) (Q : W → ℝ) (C : P → ℝ → (P → ℝ → ℝ) → ℝ)
    (hs : P → ℝ → ℝ)
    (hC_nonneg : ∀ p, ∀ t ∈ Set.Icc 0 T, 0 ≤ C p t hs)
    (hC_L2 : ∀ p, MeasureTheory.MemLp (fun t => C p t hs) 2 (FrieszDUE.PIE.ν T)) :
    (∀ mu : W → ℝ, FrieszDUE.PIE.IsSRDEquilibrium T od Q C hs mu →
        FrieszDUE.PIE.IsPIEVISolution T od Q C hs) ∧
      (FrieszDUE.PIE.IsPIEVISolution T od Q C hs →
        FrieszDUE.PIE.IsSRDEquilibrium T od Q C hs (FrieszDUE.PIE.muOD T od C hs)) := by
  exact ⟨fun mu hE => FrieszPIEHelpers.part1 T od Q C hs hC_L2 mu hE,
    fun hVI => FrieszPIEHelpers.part2 T hT od Q C hs hC_nonneg hC_L2 hVI⟩
