-- Prove2me | solution 1 for Cohen2019.Tight.worst_case_classifier_exists
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T05:06:45.007596+00:00
-- url     : https://prove2.me/submissions/deb46285-ae17-406e-8e35-b0cefed60f97

import Mathlib
import Definitions.Def_Cohen2019_Tight_Model
import Definitions.Def_Cohen2019_Tight_HalfSpaces

set_option autoImplicit false

open MeasureTheory ProbabilityTheory in
theorem wc_phi_strictMono : StrictMono Cohen2019.Robust.Phi := by
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
theorem wc_phi_continuous : Continuous Cohen2019.Robust.Phi := by
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
theorem wc_phi_inv {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Cohen2019.Robust.Phi (Cohen2019.Robust.PhiInvReal q) = q := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot (gaussianReal 0 1)).eventually
    (Iio_mem_nhds hq0)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually
    (Ioi_mem_nhds hq1)).exists
  have hmem : q ∈ Set.Icc (Cohen2019.Robust.Phi a) (Cohen2019.Robust.Phi b) :=
    ⟨le_of_lt ha, le_of_lt hb⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ a b wc_phi_continuous hmem
  have hS : {s : ℝ | q ≤ Cohen2019.Robust.Phi s} = Set.Ici t := by
    ext s
    simp only [Set.mem_Ici]
    rw [← ht]
    exact wc_phi_strictMono.le_iff_le
  unfold Cohen2019.Robust.PhiInvReal
  rw [hS, csInf_Ici, ht]

open MeasureTheory ProbabilityTheory in
theorem wc_mass_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    gaussianReal 0 1 {v | Cohen2019.Robust.Phi v ≤ q} = ENNReal.ofReal q := by
  have hset : {v | Cohen2019.Robust.Phi v ≤ q} = Set.Iic (Cohen2019.Robust.PhiInvReal q) := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_Iic]
    conv_lhs => rw [← wc_phi_inv hq0 hq1]
    exact wc_phi_strictMono.le_iff_le
  rw [hset, ← ofReal_cdf]
  change ENNReal.ofReal (Cohen2019.Robust.Phi _) = _
  rw [wc_phi_inv hq0 hq1]

open MeasureTheory ProbabilityTheory in
theorem wc_mass_lt {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    gaussianReal 0 1 {v | Cohen2019.Robust.Phi v < q} = ENNReal.ofReal q := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hset : {v | Cohen2019.Robust.Phi v < q} = Set.Iio (Cohen2019.Robust.PhiInvReal q) := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_Iio]
    conv_lhs => rw [← wc_phi_inv hq0 hq1]
    exact wc_phi_strictMono.lt_iff_lt
  rw [hset, measure_congr Iio_ae_eq_Iic, ← ofReal_cdf]
  change ENNReal.ofReal (Cohen2019.Robust.Phi _) = _
  rw [wc_phi_inv hq0 hq1]

open MeasureTheory ProbabilityTheory in
theorem wc_mass_Ico {α γ : ℝ} (hα : 0 < α) (hγ : γ < 1) :
    gaussianReal 0 1 {v | α ≤ Cohen2019.Robust.Phi v ∧ Cohen2019.Robust.Phi v < γ}
      ≤ ENNReal.ofReal (γ - α) := by
  by_cases hαγ : α ≤ γ
  · have hset : {v | α ≤ Cohen2019.Robust.Phi v ∧ Cohen2019.Robust.Phi v < γ}
        = {v | Cohen2019.Robust.Phi v < γ} \ {v | Cohen2019.Robust.Phi v < α} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_diff, not_lt]
      tauto
    have hsub : {v | Cohen2019.Robust.Phi v < α} ⊆ {v | Cohen2019.Robust.Phi v < γ} := by
      intro v hv
      simp only [Set.mem_setOf_eq] at hv ⊢
      linarith
    have hmeas : MeasurableSet {v | Cohen2019.Robust.Phi v < α} :=
      measurableSet_lt wc_phi_continuous.measurable measurable_const
    rw [hset, measure_diff hsub hmeas.nullMeasurableSet (measure_ne_top _ _),
      wc_mass_lt (by linarith) hγ, wc_mass_lt hα (by linarith), ENNReal.ofReal_sub _ hα.le]
  · have hset : {v | α ≤ Cohen2019.Robust.Phi v ∧ Cohen2019.Robust.Phi v < γ} = ∅ := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
      intro h
      push_neg at hαγ
      linarith
    rw [hset, measure_empty]
    exact bot_le

open MeasureTheory ProbabilityTheory Cohen2019.Tight in
theorem wc_law {d : ℕ} (x δ : Space d) (σ : ℝ) (hσ : 0 < σ) (hδ : δ ≠ 0) (S : Set ℝ)
    (hS : MeasurableSet S) :
    gaussNoise x σ ((fun z : Space d => inner ℝ δ (z - x) / (σ * ‖δ‖)) ⁻¹' S)
      = gaussianReal 0 1 S := by
  have hnδ : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  set u : Space d := ‖δ‖⁻¹ • δ with hu
  have hun : ‖u‖ = 1 := norm_smul_inv_norm hδ
  set L : StrongDual ℝ (Space d) := innerSL ℝ u with hL
  have hLn : ‖L‖ = 1 := by rw [hL, innerSL_apply_norm, hun]
  have hmapL : (stdGaussian (Space d)).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, hLn]
    simp
  have hmh : Measurable (fun z : Space d => inner ℝ δ (z - x) / (σ * ‖δ‖)) := by fun_prop
  have hkey : ∀ z : Space d, inner ℝ δ (x + σ • z - x) / (σ * ‖δ‖) = L z := by
    intro z
    simp only [hL, innerSL_apply_apply, hu, inner_smul_left, add_sub_cancel_left,
      inner_smul_right, starRingEnd_apply, star_trivial]
    field_simp
  have hpre : (fun z : Space d => x + σ • z) ⁻¹'
      ((fun z : Space d => inner ℝ δ (z - x) / (σ * ‖δ‖)) ⁻¹' S) = L ⁻¹' S := by
    ext z
    simp only [Set.mem_preimage]
    rw [hkey z]
  unfold gaussNoise
  rw [Measure.map_apply (by fun_prop) (hmh hS), hpre,
    ← Measure.map_apply L.continuous.measurable hS, hmapL]

/-- The 1D classifier on the uniformized coordinate `v = Φ(h z)`. -/
noncomputable def wcG {Y : Type*} (cA cB : Y) (g : ℕ → Y) (pA pB v : ℝ) : Y :=
  if v ≤ pA then cA else if 1 - pB ≤ v then cB else g ⌊(v - pA) / pB⌋₊

theorem wcG_measurable {Y : Type*} (cA cB : Y) (g : ℕ → Y) (pA pB : ℝ) :
    @Measurable ℝ Y _ ⊤ (wcG cA cB g pA pB) := by
  letI : MeasurableSpace Y := ⊤
  unfold wcG
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const ?_)
  exact measurable_from_nat.comp
    (((measurable_id.sub_const _).div_const _).nat_floor)

theorem wcG_eq_cA {Y : Type*} {cA cB : Y} {g : ℕ → Y} {pA pB : ℝ}
    (hBA : cB ≠ cA) (hg : ∀ k, g k ≠ cA) (v : ℝ) :
    wcG cA cB g pA pB v = cA ↔ v ≤ pA := by
  unfold wcG
  split_ifs with h1 h2
  · simp [h1]
  · simp [h1, hBA]
  · simp [h1, hg]

theorem wcG_eq_cB {Y : Type*} {cA cB : Y} {g : ℕ → Y} {pA pB : ℝ} {n : ℕ}
    (hBA : cB ≠ cA) (hg : ∀ k, k < n → g k ≠ cB)
    (hfl : ∀ v : ℝ, pA < v → v < 1 - pB → ⌊(v - pA) / pB⌋₊ < n) (v : ℝ) :
    wcG cA cB g pA pB v = cB ↔ (pA < v ∧ 1 - pB ≤ v) := by
  unfold wcG
  split_ifs with h1 h2
  · simp only [hBA.symm, false_iff, not_and, not_le]
    intro h; linarith
  · simp only [true_iff]
    exact ⟨lt_of_not_ge h1, h2⟩
  · simp only [h2, and_false, iff_false]
    exact hg _ (hfl v (lt_of_not_ge h1) (lt_of_not_ge h2))

theorem wcG_eq_other {Y : Type*} {cA cB c : Y} {g : ℕ → Y} {pA pB : ℝ} {i : ℕ}
    (hpB : 0 < pB) (hcA : c ≠ cA) (hcB : c ≠ cB) (hinj : ∀ k, g k = c → k = i) (v : ℝ)
    (hv : wcG cA cB g pA pB v = c) :
    pA + i * pB ≤ v ∧ v < min (pA + (i + 1) * pB) (1 - pB) := by
  unfold wcG at hv
  split_ifs at hv with h1 h2
  · exact absurd hv.symm hcA
  · exact absurd hv.symm hcB
  · have hk := hinj _ hv
    have h1' : pA < v := lt_of_not_ge h1
    have h2' : v < 1 - pB := lt_of_not_ge h2
    have hnn : 0 ≤ (v - pA) / pB := div_nonneg (by linarith) hpB.le
    rw [Nat.floor_eq_iff hnn, le_div_iff₀ hpB, div_lt_iff₀ hpB] at hk
    refine ⟨by linarith [hk.1], lt_min (by linarith [hk.2]) h2'⟩

theorem wcG_mem {Y : Type*} {cA cB : Y} {g : ℕ → Y} {pA pB : ℝ} {s : Finset Y}
    (hcB : cB ∈ s) (hg : ∀ k, g k ∈ s) (v : ℝ) (hv : pA < v) :
    wcG cA cB g pA pB v ∈ s := by
  unfold wcG
  rw [if_neg (not_le.mpr hv)]
  split_ifs
  · exact hcB
  · exact hg _

open MeasureTheory ProbabilityTheory Cohen2019.Tight in
theorem solution {d : ℕ} {Y : Type*} (x δ : Space d) (σ pA pB : ℝ)
    (hσ : 0 < σ) (hδ : δ ≠ 0) (cA cB : Y) (s : Finset Y) (hcA : cA ∉ s) (hcB : cB ∈ s)
    (hpB0 : 0 < pB) (hBA : pB ≤ pA) (hpA1 : pA < 1) (hsum : pA + pB ≤ 1)
    (hcap : 1 ≤ pA + (s.card : ℝ) * pB) :
    ∃ f : Space d → Y, IsMeasurableClassifier f ∧
      (∀ z ∈ setA x δ σ pA, f z = cA) ∧
      (∀ z ∈ setB x δ σ pB, z ∉ setA x δ σ pA → f z = cB) ∧
      (∀ z, z ∉ setA x δ σ pA → f z ∈ s) ∧
      classProb f σ x cA = pA ∧ classProb f σ x cB = pB ∧
      ∀ c : Y, c ≠ cA → classProb f σ x c ≤ pB := by
  classical
  set s' := s.erase cB with hs'
  set n := s'.card with hn
  have hn1 : (n : ℝ) + 1 = (s.card : ℝ) := by
    have := Finset.card_erase_add_one hcB
    exact_mod_cast this
  set e : Fin n ≃ s' := s'.equivFin.symm with he
  set g : ℕ → Y := fun k => if h : k < n then ((e ⟨k, h⟩ : s') : Y) else cB with hgdef
  have hgs' : ∀ k (h : k < n), g k ∈ s' := by
    intro k h
    simp only [hgdef, dif_pos h]
    exact (e ⟨k, h⟩).2
  have hgs : ∀ k, g k ∈ s := by
    intro k
    by_cases h : k < n
    · exact Finset.mem_of_mem_erase (hgs' k h)
    · simp only [hgdef, dif_neg h]; exact hcB
  have hBAne : cB ≠ cA := fun h => hcA (h ▸ hcB)
  have hgA : ∀ k, g k ≠ cA := fun k h => hcA (h ▸ hgs k)
  have hgB : ∀ k, k < n → g k ≠ cB := fun k hk h =>
    Finset.ne_of_mem_erase (hgs' k hk) h
  have hfl : ∀ v : ℝ, pA < v → v < 1 - pB → ⌊(v - pA) / pB⌋₊ < n := by
    intro v h1 h2
    rw [Nat.floor_lt (div_nonneg (by linarith) hpB0.le), div_lt_iff₀ hpB0]
    nlinarith
  have hnδ : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  have hσδ : 0 < σ * ‖δ‖ := mul_pos hσ hnδ
  have hpA0 : 0 < pA := lt_of_lt_of_le hpB0 hBA
  set h : Space d → ℝ := fun z => inner ℝ δ (z - x) / (σ * ‖δ‖) with hh
  have hmh : Measurable h := by fun_prop
  have hle : ∀ z t, h z ≤ t ↔ inner ℝ δ (z - x) ≤ σ * ‖δ‖ * t := by
    intro z t
    simp only [hh]
    rw [div_le_iff₀ hσδ, mul_comm t]
  set G : ℝ → Y := fun v => wcG cA cB g pA pB (Cohen2019.Robust.Phi v) with hG
  have hGmeas : ∀ c : Y, MeasurableSet (G ⁻¹' {c}) := by
    intro c
    letI : MeasurableSpace Y := ⊤
    have hm : Measurable G :=
      (wcG_measurable cA cB g pA pB).comp wc_phi_continuous.measurable
    exact hm (MeasurableSpace.measurableSet_top)
  have hge : ∀ z t, t ≤ h z ↔ σ * ‖δ‖ * t ≤ inner ℝ δ (z - x) := by
    intro z t
    simp only [hh]
    rw [le_div_iff₀ hσδ, mul_comm t]
  have hnotA : ∀ z, z ∉ setA x δ σ pA → pA < Cohen2019.Robust.Phi (h z) := by
    intro z hz
    simp only [setA, Set.mem_setOf_eq, not_le] at hz
    have h1 : Cohen2019.Robust.PhiInvReal pA < h z := by
      rw [← not_le, hle]; exact not_le.mpr hz
    have h2 := wc_phi_strictMono h1
    rwa [wc_phi_inv hpA0 hpA1] at h2
  have hprob : ∀ c, classProb (fun z => G (h z)) σ x c = (gaussianReal 0 1 (G ⁻¹' {c})).toReal := by
    intro c
    have := wc_law x δ σ hσ hδ _ (hGmeas c)
    unfold classProb
    exact congrArg ENNReal.toReal this
  have hcBprob : classProb (fun z => G (h z)) σ x cB = pB := by
    have hset : G ⁻¹' {cB} = {v | pA < Cohen2019.Robust.Phi v ∧ 1 - pB ≤ Cohen2019.Robust.Phi v} := by
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, hG]
      exact wcG_eq_cB hBAne hgB hfl _
    rw [hprob, hset]
    rcases (show pA ≤ 1 - pB by linarith).lt_or_eq with hlt | heq
    · have hset2 : {v | pA < Cohen2019.Robust.Phi v ∧ 1 - pB ≤ Cohen2019.Robust.Phi v}
          = {v | Cohen2019.Robust.Phi v < 1 - pB}ᶜ := by
        ext v
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
        constructor
        · exact fun h => h.2
        · intro h; exact ⟨by linarith, h⟩
      rw [hset2, prob_compl_eq_one_sub (measurableSet_lt wc_phi_continuous.measurable
        measurable_const), wc_mass_lt (by linarith) (by linarith), ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub _ (by linarith : (0:ℝ) ≤ 1 - pB), ENNReal.toReal_ofReal (by linarith)]
      ring
    · have hset2 : {v | pA < Cohen2019.Robust.Phi v ∧ 1 - pB ≤ Cohen2019.Robust.Phi v}
          = {v | Cohen2019.Robust.Phi v ≤ pA}ᶜ := by
        ext v
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
        constructor
        · exact fun h => h.1
        · intro h; exact ⟨h, by linarith⟩
      rw [hset2, prob_compl_eq_one_sub (measurableSet_le wc_phi_continuous.measurable
        measurable_const), wc_mass_le hpA0 hpA1, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub _ hpA0.le, ENNReal.toReal_ofReal (by linarith)]
      linarith
  refine ⟨fun z => G (h z), ?_, ?_, ?_, ?_, ?_, hcBprob, ?_⟩
  · intro c
    exact hmh (hGmeas c)
  · intro z hz
    simp only [setA, Set.mem_setOf_eq] at hz
    have h1 : h z ≤ Cohen2019.Robust.PhiInvReal pA := (hle z _).2 hz
    have h2 := wc_phi_strictMono.monotone h1
    rw [wc_phi_inv hpA0 hpA1] at h2
    exact (wcG_eq_cA hBAne hgA _).2 h2
  · intro z hzB hzA
    simp only [setB, Set.mem_setOf_eq] at hzB
    have h1 : Cohen2019.Robust.PhiInvReal (1 - pB) ≤ h z := (hge z _).2 hzB
    have h2 := wc_phi_strictMono.monotone h1
    rw [wc_phi_inv (by linarith) (by linarith)] at h2
    exact (wcG_eq_cB hBAne hgB hfl _).2 ⟨hnotA z hzA, h2⟩
  · intro z hzA
    exact wcG_mem hcB hgs _ (hnotA z hzA)
  · have hset : G ⁻¹' {cA} = {v | Cohen2019.Robust.Phi v ≤ pA} := by
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, hG]
      exact wcG_eq_cA hBAne hgA _
    rw [hprob, hset, wc_mass_le hpA0 hpA1, ENNReal.toReal_ofReal hpA0.le]
  · intro c hc
    by_cases hcBc : c = cB
    · rw [hcBc, hcBprob]
    by_cases hcs : c ∈ s'
    · have hinj : ∀ k, g k = c → k = ((e.symm ⟨c, hcs⟩ : Fin n) : ℕ) := by
        intro k hk
        by_cases hkn : k < n
        · simp only [hgdef, dif_pos hkn] at hk
          have hek : e ⟨k, hkn⟩ = ⟨c, hcs⟩ := Subtype.ext hk
          rw [← hek, Equiv.symm_apply_apply]
        · simp only [hgdef, dif_neg hkn] at hk
          exact absurd hk.symm hcBc
      set i : ℕ := ((e.symm ⟨c, hcs⟩ : Fin n) : ℕ) with hi
      have hsub : G ⁻¹' {c} ⊆ {v | pA + i * pB ≤ Cohen2019.Robust.Phi v ∧
          Cohen2019.Robust.Phi v < min (pA + (i + 1) * pB) (1 - pB)} := by
        intro v hv
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hG] at hv
        exact wcG_eq_other hpB0 hc hcBc hinj _ hv
      have hi0 : (0 : ℝ) ≤ i * pB := mul_nonneg (Nat.cast_nonneg _) hpB0.le
      have hmin1 := min_le_left (pA + (i + 1) * pB) (1 - pB)
      have hmin2 := min_le_right (pA + (i + 1) * pB) (1 - pB)
      rw [hprob]
      refine ENNReal.toReal_le_of_le_ofReal hpB0.le ?_
      refine (measure_mono hsub).trans ((wc_mass_Ico (by linarith) (by linarith)).trans ?_)
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
    · have hcs2 : c ∉ s := by
        intro hm; exact hcs (Finset.mem_erase.mpr ⟨hcBc, hm⟩)
      have hset : G ⁻¹' {c} = ∅ := by
        ext v
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hG, Set.mem_empty_iff_false,
          iff_false]
        intro hv
        by_cases hvA : Cohen2019.Robust.Phi v ≤ pA
        · exact hc (hv.symm.trans ((wcG_eq_cA hBAne hgA _).2 hvA))
        · exact hcs2 (hv ▸ wcG_mem hcB hgs _ (lt_of_not_ge hvA))
      rw [hprob, hset, measure_empty, ENNReal.toReal_zero]
      exact hpB0.le
