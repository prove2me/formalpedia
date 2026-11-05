-- Prove2me | solution 1 for DiscServLine.SPT.lemma_A7
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-11-04T14:34:16.617857+00:00
-- url     : https://prove2.me/submissions/e9558fed-3a60-4f3c-92f1-b91dd97ec0b3

import Definitions.Def_DiscServLine_SPT_Model

open MeasureTheory Set Filter Topology

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace DslA7

section GenMeas
variable (ν : Measure ℝ) [IsFiniteMeasure ν]

noncomputable def Fn (x : ℝ) : ℝ := ν.real (Iic x)
noncomputable def Fm (x : ℝ) : ℝ := ν.real (Iio x)

lemma Fn_mono : Monotone (Fn ν) := fun _ _ h => measureReal_mono (Iic_subset_Iic.2 h)
lemma Fm_mono : Monotone (Fm ν) := fun _ _ h => measureReal_mono (Iio_subset_Iio h)
lemma Fm_le_Fn (x : ℝ) : Fm ν x ≤ Fn ν x := measureReal_mono Iio_subset_Iic_self
lemma Fn_le_Fm {x y : ℝ} (h : x < y) : Fn ν x ≤ Fm ν y := measureReal_mono (Iic_subset_Iio.2 h)
lemma Fn_nonneg (x : ℝ) : 0 ≤ Fn ν x := measureReal_nonneg
lemma Fm_nonneg (x : ℝ) : 0 ≤ Fm ν x := measureReal_nonneg
lemma Fn_le_univ (x : ℝ) : Fn ν x ≤ ν.real univ := measureReal_mono (subset_univ _)

lemma Fn_sub_Fm (x : ℝ) : Fn ν x - Fm ν x = ν.real {x} := by
  unfold Fn Fm
  rw [← Iio_union_right, measureReal_union (by simp) (measurableSet_singleton x)]
  ring

lemma Fn_rc {x s : ℝ} (h : ∀ y, x < y → s < Fn ν y) : s ≤ Fn ν x := by
  set u : ℕ → Set ℝ := fun n => Iic (x + 1 / ((n:ℝ) + 1))
  have hanti : Antitone u := by
    intro m n hmn
    apply Iic_subset_Iic.2
    have : (1:ℝ) / ((n:ℝ) + 1) ≤ 1 / ((m:ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hmn 1
    linarith
  have hint : (⋂ n, u n) = Iic x := by
    ext y
    simp only [mem_iInter, mem_Iic, u]
    constructor
    · intro hy
      by_contra hc
      push Not at hc
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
      have := hy n
      linarith
    · intro hy n
      have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith
  have ht := tendsto_measure_iInter_atTop (μ := ν) (fun n => measurableSet_Iic.nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [hint] at ht
  have ht2 : Tendsto (fun n : ℕ => Fn ν (x + 1 / ((n:ℝ) + 1))) atTop (𝓝 (Fn ν x)) := by
    have := (ENNReal.tendsto_toReal (measure_ne_top ν (Iic x))).comp ht
    simpa [Fn, Measure.real, Function.comp_def, u] using this
  apply ge_of_tendsto ht2
  filter_upwards with n
  have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
  exact (h _ (by linarith)).le

lemma Fm_lc {x s : ℝ} (h : ∀ y, y < x → Fn ν y ≤ s) : Fm ν x ≤ s := by
  set u : ℕ → Set ℝ := fun n => Iic (x - 1 / ((n:ℝ) + 1))
  have hmono : Monotone u := by
    intro m n hmn
    apply Iic_subset_Iic.2
    have : (1:ℝ) / ((n:ℝ) + 1) ≤ 1 / ((m:ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hmn 1
    linarith
  have hun : (⋃ n, u n) = Iio x := by
    ext y
    simp only [mem_iUnion, mem_Iic, mem_Iio, u]
    constructor
    · rintro ⟨n, hn⟩
      have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
      exact ⟨n, by linarith⟩
  have ht := tendsto_measure_iUnion_atTop (μ := ν) hmono
  rw [hun] at ht
  have ht2 : Tendsto (fun n : ℕ => Fn ν (x - 1 / ((n:ℝ) + 1))) atTop (𝓝 (Fm ν x)) := by
    have := (ENNReal.tendsto_toReal (measure_ne_top ν (Iio x))).comp ht
    simpa [Fn, Fm, Measure.real, Function.comp_def, u] using this
  apply le_of_tendsto ht2
  filter_upwards with n
  have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
  exact h _ (by linarith)

lemma Fn_rc' (x : ℝ) {δ : ℝ} (hδ : 0 < δ) : ∃ y, x < y ∧ Fn ν y < Fn ν x + δ := by
  by_contra hc
  push Not at hc
  have := Fn_rc ν (x := x) (s := Fn ν x + δ / 2) (fun y hy => by linarith [hc y hy])
  linarith

lemma Fm_lc' (x : ℝ) {δ : ℝ} (hδ : 0 < δ) : ∃ y, y < x ∧ Fm ν x - δ < Fn ν y := by
  by_contra hc
  push Not at hc
  have := Fm_lc ν (x := x) (s := Fm ν x - δ / 2) (fun y hy => by linarith [hc y hy])
  linarith

lemma Fn_measurable : Measurable (Fn ν) := (Fn_mono ν).measurable
lemma Fm_measurable : Measurable (Fm ν) := (Fm_mono ν).measurable

end GenMeas

section Quant
variable (ν : Measure ℝ) [IsFiniteMeasure ν] (K : ℝ)

noncomputable def qset (s : ℝ) : Set ℝ := ({t | s < Fn ν t} ∩ Ici 0) ∪ {K}
noncomputable def qf (s : ℝ) : ℝ := sInf (qset ν K s)

variable {ν K}

lemma qset_bdd (hK : 0 ≤ K) (s : ℝ) : BddBelow (qset ν K s) := by
  refine ⟨0, ?_⟩
  rintro t (⟨_, ht⟩ | ht)
  · exact ht
  · rw [mem_singleton_iff.1 ht]; exact hK

lemma qset_ne (s : ℝ) : (qset ν K s).Nonempty := ⟨K, Or.inr rfl⟩

lemma qf_mono (hK : 0 ≤ K) : Monotone (qf ν K) := by
  intro s1 s2 h
  apply csInf_le_csInf (qset_bdd hK s1) (qset_ne s2)
  rintro t (⟨ht1, ht2⟩ | ht)
  · exact Or.inl ⟨lt_of_le_of_lt h ht1, ht2⟩
  · exact Or.inr ht

lemma qf_nonneg (hK : 0 ≤ K) (s : ℝ) : 0 ≤ qf ν K s :=
  le_csInf (qset_ne s) (fun t ht => by
    rcases ht with ⟨_, ht⟩ | ht
    · exact ht
    · rw [mem_singleton_iff.1 ht]; exact hK)

lemma qf_measurable (hK : 0 ≤ K) : Measurable (qf ν K) := (qf_mono hK).measurable

lemma Fn_neg (h0 : ν (Iio 0) = 0) {x : ℝ} (hx : x < 0) : Fn ν x = 0 := by
  unfold Fn
  rw [measureReal_def, measure_mono_null (Iic_subset_Iio.2 hx) h0]; simp

lemma Fn_K (hKs : ν (Ioi K) = 0) : Fn ν K = ν.real univ := by
  unfold Fn
  rw [← Iic_union_Ioi (a := K), measureReal_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi]
  simp [measureReal_def, hKs]

lemma qf_le (hK : 0 ≤ K) (h0 : ν (Iio 0) = 0) {s x : ℝ} (hs : 0 ≤ s) (hx : s < Fn ν x) :
    qf ν K s ≤ x := by
  have hx0 : 0 ≤ x := by
    by_contra hc
    push Not at hc
    rw [Fn_neg h0 hc] at hx
    linarith
  exact csInf_le (qset_bdd hK s) (Or.inl ⟨hx, hx0⟩)

lemma lt_Fn_of_qf_lt (hKs : ν (Ioi K) = 0) {s y : ℝ} (hsT : s < ν.real univ)
    (hy : qf ν K s < y) : s < Fn ν y := by
  obtain ⟨t, ht, hty⟩ := exists_lt_of_csInf_lt (qset_ne s) hy
  have : s < Fn ν t := by
    rcases ht with ⟨ht, _⟩ | ht
    · exact ht
    · rw [mem_singleton_iff.1 ht, Fn_K hKs]; exact hsT
  exact lt_of_lt_of_le this (Fn_mono ν hty.le)

lemma le_Fn_of_qf_le (hKs : ν (Ioi K) = 0) {s x : ℝ} (hsT : s < ν.real univ)
    (hx : qf ν K s ≤ x) : s ≤ Fn ν x :=
  Fn_rc ν (fun y hy => lt_Fn_of_qf_lt hKs hsT (lt_of_le_of_lt hx hy))

lemma Fm_qf_le (hK : 0 ≤ K) (h0 : ν (Iio 0) = 0) {s : ℝ} (hs : 0 ≤ s) :
    Fm ν (qf ν K s) ≤ s := by
  apply Fm_lc ν
  intro y hy
  by_contra hc
  push Not at hc
  have := qf_le hK h0 hs hc
  linarith

lemma map_qf (hK : 0 ≤ K) (h0 : ν (Iio 0) = 0) (hKs : ν (Ioi K) = 0) :
    (volume.restrict (Ico 0 (ν.real univ))).map (qf ν K) = ν := by
  haveI : IsFiniteMeasure (volume.restrict (Ico (0:ℝ) (ν.real univ))) :=
    isFiniteMeasure_restrict.2 (by simp)
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply (qf_measurable hK) measurableSet_Iic, Measure.restrict_apply' measurableSet_Ico]
  have hFT := Fn_le_univ ν x
  have hF0 := Fn_nonneg ν x
  have e : ν (Iic x) = ENNReal.ofReal (Fn ν x) := by
    rw [Fn, ofReal_measureReal]
  rw [e]
  apply le_antisymm
  · calc volume (qf ν K ⁻¹' Iic x ∩ Ico 0 (ν.real univ)) ≤ volume (Icc 0 (Fn ν x)) := by
          apply measure_mono
          rintro s ⟨hs1, hs2, hs3⟩
          exact ⟨hs2, le_Fn_of_qf_le hKs hs3 hs1⟩
      _ = ENNReal.ofReal (Fn ν x) := by simp
  · calc ENNReal.ofReal (Fn ν x) = volume (Ico 0 (Fn ν x)) := by simp
      _ ≤ volume (qf ν K ⁻¹' Iic x ∩ Ico 0 (ν.real univ)) := by
          apply measure_mono
          rintro s ⟨hs1, hs2⟩
          exact ⟨qf_le hK h0 hs1 hs2, hs1, lt_of_lt_of_le hs2 hFT⟩

end Quant

section GLsec
variable {ν : Measure ℝ} [IsFiniteMeasure ν] {K : ℝ}

lemma ae_eq_Ioc_of_sandwich {S : Set ℝ} {a b : ℝ} (hS : MeasurableSet S) (h1 : Ioo a b ⊆ S)
    (h2 : S ⊆ Icc a b) : S =ᵐ[volume] Ioc a b := by
  have e1 : Ioo a b =ᵐ[volume] S := by
    apply ae_eq_of_subset_of_measure_ge h1 _ measurableSet_Ioo.nullMeasurableSet
      (measure_ne_top_of_subset h2 (by simp))
    calc volume S ≤ volume (Icc a b) := measure_mono h2
      _ = volume (Ioo a b) := by simp
  exact e1.symm.trans Ioo_ae_eq_Ioc

theorem glthm (hK : 0 ≤ K) (h0 : ν (Iio 0) = 0) (hKs : ν (Ioi K) = 0)
    (H h : ℝ → ℝ) (hH : ∀ x ∈ Icc 0 (ν.real univ), HasDerivAt H (h x) x)
    (hc : ContinuousOn h (Icc 0 (ν.real univ)))
    (g : ℝ → ℝ) (hgm : Measurable g) (C : ℝ) (hgb : ∀ t, |g t| ≤ C)
    (hatom : ∀ t, 0 < ν.real {t} → g t * ν.real {t} = H (Fn ν t) - H (Fm ν t))
    (hcont : ∀ t, ν.real {t} = 0 → g t = h (Fn ν t)) :
    ∫ t, g t ∂ν = H (ν.real univ) - H 0 := by
  set T := ν.real univ with hTdef
  have hT0 : 0 ≤ T := measureReal_nonneg
  haveI : IsFiniteMeasure (volume.restrict (Ico (0:ℝ) T)) :=
    isFiniteMeasure_restrict.2 (by simp)
  have hqm := qf_measurable (ν := ν) hK
  rw [← map_qf hK h0 hKs, integral_map hqm.aemeasurable hgm.aestronglyMeasurable]
  -- FTC for h on intervals inside [0,T]
  have ftc : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → ∫ s in Ioc a b, h s = H b - H a := by
    intro a b ha hab hb
    rw [← intervalIntegral.integral_of_le hab]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [uIcc_of_le hab] at hx
      exact hH x ⟨ha.trans hx.1, hx.2.trans hb⟩
    · exact (hc.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  have hint : ∫ s in Ico 0 T, h s = H T - H 0 := by
    rw [integral_Ico_eq_integral_Ioc]; exact ftc 0 T le_rfl hT0 le_rfl
  have hhI : IntegrableOn h (Ico 0 T) volume :=
    (hc.integrableOn_Icc).mono_set Ico_subset_Icc_self
  have hgI : IntegrableOn (fun s => g (qf ν K s)) (Ico 0 T) volume := by
    apply Integrable.of_bound (hgm.comp hqm).aestronglyMeasurable C
    filter_upwards with s
    exact (Real.norm_eq_abs _).le.trans (hgb _)
  have hkI : IntegrableOn (fun s => g (qf ν K s) - h s) (Ico 0 T) volume := hgI.sub hhI
  suffices hk : ∫ s in Ico 0 T, (g (qf ν K s) - h s) = 0 by
    rw [integral_sub hgI hhI, sub_eq_zero] at hk
    rw [hk, hint]
  -- atoms
  set A : Set ℝ := {t | 0 < ν {t}} with hA
  have hAc : A.Countable := by
    have := Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top ν
      (As := fun t : ℝ => ({t} : Set ℝ)) (fun t => measurableSet_singleton t)
      (fun x y hxy => Set.disjoint_singleton.2 hxy) (measure_ne_top _ _)
    simpa using this
  have hAm : MeasurableSet (qf ν K ⁻¹' A) := hqm hAc.measurableSet
  rw [← integral_inter_add_sdiff hAm hkI]
  have hfib : ∀ s, 0 ≤ s → s < T → Fm ν (qf ν K s) ≤ s ∧ s ≤ Fn ν (qf ν K s) := fun s hs hsT =>
    ⟨Fm_qf_le hK h0 hs, le_Fn_of_qf_le hKs hsT le_rfl⟩
  have hzero2 : ∫ s in Ico 0 T \ qf ν K ⁻¹' A, (g (qf ν K s) - h s) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    rintro s ⟨⟨hs0, hsT⟩, hsA⟩
    have hz : ν {qf ν K s} = 0 := by
      simp only [mem_preimage, hA, mem_ofPred_eq, not_lt, nonpos_iff_eq_zero] at hsA
      exact hsA
    have hz' : ν.real {qf ν K s} = 0 := by simp [measureReal_def, hz]
    have e := Fn_sub_Fm ν (qf ν K s)
    rw [hz'] at e
    obtain ⟨h1, h2⟩ := hfib s hs0 hsT
    have : Fn ν (qf ν K s) = s := by linarith
    rw [hcont _ hz', this, sub_self]
  rw [hzero2, add_zero]
  -- decompose over atoms
  have hU : Ico 0 T ∩ qf ν K ⁻¹' A = ⋃ t : A, (Ico 0 T ∩ qf ν K ⁻¹' {(t:ℝ)}) := by
    ext s; simp
  haveI : Countable A := hAc.to_subtype
  rw [hU, integral_iUnion]
  · have hterm : ∀ t : A, ∫ s in Ico 0 T ∩ qf ν K ⁻¹' {(t:ℝ)}, (g (qf ν K s) - h s) = 0 := by
      rintro ⟨t, ht⟩
      have htpos : 0 < ν.real {t} := ENNReal.toReal_pos (ne_of_gt ht) (measure_ne_top _ _)
      have hSm : MeasurableSet (Ico 0 T ∩ qf ν K ⁻¹' {t}) :=
        measurableSet_Ico.inter (hqm (measurableSet_singleton _))
      have hS1 : Ioo (Fm ν t) (Fn ν t) ⊆ Ico 0 T ∩ qf ν K ⁻¹' {t} := by
        rintro s ⟨hs1, hs2⟩
        have hs0 : 0 ≤ s := (Fm_nonneg ν t).trans hs1.le
        refine ⟨⟨hs0, lt_of_lt_of_le hs2 (Fn_le_univ ν t)⟩, ?_⟩
        apply le_antisymm (qf_le hK h0 hs0 hs2)
        by_contra hc
        push Not at hc
        have := le_Fn_of_qf_le hKs (lt_of_lt_of_le hs2 (Fn_le_univ ν t)) (le_refl (qf ν K s))
        have := Fn_le_Fm ν hc
        linarith
      have hS2 : Ico 0 T ∩ qf ν K ⁻¹' {t} ⊆ Icc (Fm ν t) (Fn ν t) := by
        rintro s ⟨⟨hs0, hsT⟩, hst⟩
        rw [mem_preimage, mem_singleton_iff] at hst
        obtain ⟨h1, h2⟩ := hfib s hs0 hsT
        rw [hst] at h1 h2
        exact ⟨h1, h2⟩
      rw [setIntegral_congr_fun hSm (g := fun s => g t - h s) (fun s hs => by
        simp only
        rw [show qf ν K s = t from hs.2])]
      rw [setIntegral_congr_set (ae_eq_Ioc_of_sandwich hSm hS1 hS2)]
      have hab := Fm_le_Fn ν t
      have hIoc : IntegrableOn h (Ioc (Fm ν t) (Fn ν t)) volume :=
        (hc.integrableOn_Icc).mono_set (fun x hx => ⟨(Fm_nonneg ν t).trans hx.1.le,
          hx.2.trans (Fn_le_univ ν t)⟩)
      rw [integral_sub (integrableOn_const (C := g t) (by simp)) hIoc, setIntegral_const,
        ftc _ _ (Fm_nonneg ν t) hab (Fn_le_univ ν t), Real.volume_real_Ioc_of_le hab,
        Fn_sub_Fm, smul_eq_mul, mul_comm, hatom t htpos, sub_self]
    simp [hterm]
  · intro t; exact measurableSet_Ico.inter (hqm (measurableSet_singleton _))
  · intro t1 t2 hne
    apply Disjoint.mono inf_le_right inf_le_right
    apply Disjoint.preimage
    simpa using fun h => hne (Subtype.ext h)
  · rw [← hU]; exact hkI.mono_set inter_subset_left

end GLsec

section RealAn
variable (β γ : ℝ)

noncomputable def hf (s : ℝ) : ℝ := Real.sqrt (β + γ / (1 - s) ^ 2)
noncomputable def rf (s : ℝ) : ℝ := Real.sqrt (1 + β / γ * (1 - s) ^ 2)
noncomputable def Hs (s : ℝ) : ℝ :=
  -Real.sqrt γ * (rf β γ s + Real.log (1 - s) - Real.log (1 + rf β γ s))
noncomputable def H2 (s : ℝ) : ℝ := -(rf β γ s) / (β / γ * Real.sqrt γ)
noncomputable def rho (a b : ℝ) : ℝ := β + γ / ((1 - a) * (1 - b))
noncomputable def sig (a b : ℝ) : ℝ :=
  if a < b then (Hs β γ b - Hs β γ a) / (b - a) else hf β γ a

variable {β γ} (hβ : 0 < β) (hγ : 0 < γ)
include hβ hγ

lemma rf_sq (s : ℝ) : rf β γ s ^ 2 = 1 + β / γ * (1 - s) ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma rf_ge_one (s : ℝ) : 1 ≤ rf β γ s := by
  unfold rf
  rw [Real.one_le_sqrt]
  have : 0 ≤ β / γ * (1 - s) ^ 2 := by positivity
  linarith

lemma rf_pos (s : ℝ) : 0 < rf β γ s := lt_of_lt_of_le one_pos (rf_ge_one hβ hγ s)

lemma hf_pos (s : ℝ) : 0 < hf β γ s := by
  unfold hf
  apply Real.sqrt_pos.2
  have : 0 ≤ γ / (1 - s) ^ 2 := by positivity
  linarith

lemma hf_sq (s : ℝ) : hf β γ s ^ 2 = β + γ / (1 - s) ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma hf_eq {s : ℝ} (hs : s < 1) : hf β γ s = Real.sqrt γ * rf β γ s / (1 - s) := by
  have hx : 0 < 1 - s := by linarith
  have hnn : 0 ≤ Real.sqrt γ * rf β γ s / (1 - s) := by
    have := rf_pos hβ hγ s; positivity
  rw [← Real.sqrt_sq hnn, hf]
  congr 1
  rw [div_pow, mul_pow, Real.sq_sqrt hγ.le, rf_sq hβ hγ]
  field_simp
  ring

lemma hf_ge {s : ℝ} (hs : s < 1) : Real.sqrt γ / (1 - s) ≤ hf β γ s := by
  have hx : 0 < 1 - s := by linarith
  rw [hf_eq hβ hγ hs]
  have := rf_ge_one hβ hγ s
  have : 0 ≤ Real.sqrt γ := Real.sqrt_nonneg _
  apply div_le_div_of_nonneg_right _ hx.le
  nlinarith

lemma hf_strictMonoOn : StrictMonoOn (hf β γ) (Iio 1) := by
  intro x hx y hy hxy
  simp only [mem_Iio] at hx hy
  unfold hf
  apply Real.sqrt_lt_sqrt (by positivity)
  have h1 : 0 < 1 - y := by linarith
  have h2 : (1 - y) ^ 2 < (1 - x) ^ 2 := by nlinarith
  have : γ / (1 - x) ^ 2 < γ / (1 - y) ^ 2 := div_lt_div_of_pos_left hγ (by positivity) h2
  linarith

lemma hf_continuousOn : ContinuousOn (hf β γ) (Iio 1) := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  have : (1 - s) ^ 2 ≠ 0 := by
    have : 0 < 1 - s := by simp only [mem_Iio] at hs; linarith
    positivity
  unfold hf
  fun_prop (disch := assumption)

lemma hasDerivAt_rf (s : ℝ) :
    HasDerivAt (rf β γ) (-(β / γ) * (1 - s) / rf β γ s) s := by
  have hu : HasDerivAt (fun s => 1 + β / γ * (1 - s) ^ 2) (β / γ * (2 * (1 - s) * (-1))) s := by
    have := ((hasDerivAt_id s).const_sub 1).pow 2
    simpa using (this.const_mul (β / γ)).const_add 1
  have hne : (1 + β / γ * (1 - s) ^ 2) ≠ 0 := by positivity
  have h := hu.sqrt hne
  rw [show √(1 + β / γ * (1 - s) ^ 2) = rf β γ s from rfl] at h
  have hrp := rf_pos hβ hγ s
  have e : β / γ * (2 * (1 - s) * -1) / (2 * rf β γ s) = -(β / γ) * (1 - s) / rf β γ s := by
    field_simp
  rw [e] at h
  exact h

lemma hasDerivAt_Hs {s : ℝ} (hs : s < 1) : HasDerivAt (Hs β γ) (hf β γ s) s := by
  have hx : 0 < 1 - s := by linarith
  have hr := hasDerivAt_rf hβ hγ s
  have hrp := rf_pos hβ hγ s
  have hlog1 : HasDerivAt (fun s => Real.log (1 - s)) ((-1) / (1 - s)) s := by
    have := ((hasDerivAt_id s).const_sub 1).log (ne_of_gt hx)
    simpa using this
  have hlog2 : HasDerivAt (fun s => Real.log (1 + rf β γ s))
      ((-(β / γ) * (1 - s) / rf β γ s) / (1 + rf β γ s)) s := by
    have := (hr.const_add 1).log (by positivity)
    simpa using this
  have h := ((hr.add hlog1).sub hlog2).const_mul (-Real.sqrt γ)
  have e : -Real.sqrt γ * (-(β / γ) * (1 - s) / rf β γ s + -1 / (1 - s) -
      -(β / γ) * (1 - s) / rf β γ s / (1 + rf β γ s)) = hf β γ s := by
    rw [hf_eq hβ hγ hs]
    have hr2 := rf_sq hβ hγ s
    set κ := β / γ
    set r := rf β γ s
    have e1 : -κ * (1 - s) / r + -1 / (1 - s) - -κ * (1 - s) / r / (1 + r) = -(r / (1 - s)) := by
      field_simp
      linear_combination (exp := 1) r * hr2
    rw [e1]; ring
  rw [e] at h
  exact h

lemma hasDerivAt_H2 {s : ℝ} (hs : s < 1) : HasDerivAt (H2 β γ) (1 / hf β γ s) s := by
  have hx : 0 < 1 - s := by linarith
  have hr := hasDerivAt_rf hβ hγ s
  have hrp := rf_pos hβ hγ s
  have h := (hr.neg).div_const (β / γ * Real.sqrt γ)
  have e : -(-(β / γ) * (1 - s) / rf β γ s) / (β / γ * Real.sqrt γ) = 1 / hf β γ s := by
    rw [hf_eq hβ hγ hs]
    have : 0 < Real.sqrt γ := Real.sqrt_pos.2 hγ
    field_simp
  rw [e] at h
  exact h

lemma hasDerivAt_G2 {s : ℝ} (hs : s < 1) :
    HasDerivAt (fun s => β * s + γ * (1 - s)⁻¹) (hf β γ s ^ 2) s := by
  have hx : 0 < 1 - s := by linarith
  have h1 := ((hasDerivAt_id s).const_sub 1).inv (ne_of_gt hx)
  have h := ((hasDerivAt_id s).const_mul β).add (h1.const_mul γ)
  have e : β * 1 + γ * (- -1 / (1 - id s) ^ 2) = hf β γ s ^ 2 := by
    rw [hf_sq hβ hγ]; simp; field_simp
  exact h.congr_deriv e

lemma sqrt_rho_aa {a : ℝ} (ha : a < 1) : Real.sqrt (rho β γ a a) = hf β γ a := by
  unfold rho hf; congr 2; ring

lemma intervalIntegrable_hf {a b : ℝ} (hab : a ≤ b) (hb : b < 1) :
    IntervalIntegrable (hf β γ) volume a b :=
  ((hf_continuousOn hβ hγ).mono (fun x hx => lt_of_le_of_lt hx.2 hb)).intervalIntegrable_of_Icc hab

lemma integral_hf {a b : ℝ} (hab : a ≤ b) (hb : b < 1) :
    ∫ s in a..b, hf β γ s = Hs β γ b - Hs β γ a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx; rw [uIcc_of_le hab] at hx; exact hasDerivAt_Hs hβ hγ (lt_of_le_of_lt hx.2 hb)
  · exact intervalIntegrable_hf hβ hγ hab hb

lemma jensen_strict {a b : ℝ} (hab : a < b) (hb : b < 1) :
    (Hs β γ b - Hs β γ a) ^ 2 < (b - a) ^ 2 * rho β γ a b := by
  have hba : 0 < b - a := by linarith
  have h1a : 0 < 1 - a := by linarith
  have h1b : 0 < 1 - b := by linarith
  have hI : IntervalIntegrable (hf β γ) volume a b := intervalIntegrable_hf hβ hγ hab.le hb
  have hcont : ContinuousOn (hf β γ) (Icc a b) :=
    (hf_continuousOn hβ hγ).mono (fun x hx => lt_of_le_of_lt hx.2 hb)
  have I1 : ∫ s in a..b, hf β γ s = Hs β γ b - Hs β γ a := integral_hf hβ hγ hab.le hb
  have I2 : ∫ s in a..b, hf β γ s ^ 2 = (b - a) * rho β γ a b := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => β * s + γ * (1 - s)⁻¹)]
    · unfold rho; field_simp; ring
    · intro x hx; rw [uIcc_of_le hab.le] at hx; exact hasDerivAt_G2 hβ hγ (lt_of_le_of_lt hx.2 hb)
    · exact (hcont.pow 2).intervalIntegrable_of_Icc hab.le
  set m := (Hs β γ b - Hs β γ a) / (b - a)
  have hpos : 0 < ∫ s in a..b, (hf β γ s - m) ^ 2 := by
    have hc2 : ContinuousOn (fun s => (hf β γ s - m) ^ 2) (Icc a b) := (hcont.sub continuousOn_const).pow 2
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall (fun s => sq_nonneg _)) (hc2.intervalIntegrable_of_Icc hab.le)]
    refine ⟨hab, ?_⟩
    have hsub : Ioc a b ⊆ (Function.support (fun s => (hf β γ s - m) ^ 2) ∩ Ioc a b) ∪
        ({s | hf β γ s = m} ∩ Ioc a b) := by
      intro s hs
      by_cases h : hf β γ s = m
      · exact Or.inr ⟨h, hs⟩
      · left; refine ⟨?_, hs⟩
        simp only [Function.mem_support]
        exact pow_ne_zero 2 (sub_ne_zero.2 h)
    have hss : ({s | hf β γ s = m} ∩ Ioc a b).Subsingleton := by
      rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩
      exact (hf_strictMonoOn hβ hγ).injOn (lt_of_le_of_lt hx2.2 hb) (lt_of_le_of_lt hy2.2 hb)
        (by simp only [mem_setOf_eq] at hx1 hy1; rw [hx1, hy1])
    have := measure_mono (μ := volume) hsub
    have h3 := measure_union_le (μ := volume) (Function.support (fun s => (hf β γ s - m) ^ 2) ∩ Ioc a b)
      ({s | hf β γ s = m} ∩ Ioc a b)
    rw [hss.measure_zero, add_zero] at h3
    have h4 : 0 < volume (Ioc a b) := by simp [hab]
    exact lt_of_lt_of_le h4 (this.trans h3)
  have hexp : ∫ s in a..b, (hf β γ s - m) ^ 2 =
      (∫ s in a..b, hf β γ s ^ 2) - 2 * m * (∫ s in a..b, hf β γ s) + m ^ 2 * (b - a) := by
    have e : (fun s => (hf β γ s - m) ^ 2) = fun s => (hf β γ s ^ 2 - 2 * m * hf β γ s) + m ^ 2 := by
      funext s; ring
    rw [e, intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    · simp; ring
    · exact (hcont.pow 2).intervalIntegrable_of_Icc hab.le
    · exact hI.const_mul _
    · exact ((hcont.pow 2).intervalIntegrable_of_Icc hab.le).sub (hI.const_mul _)
    · exact intervalIntegrable_const
  rw [hexp, I1, I2] at hpos
  have : m * (b - a) = Hs β γ b - Hs β γ a := by simp only [m]; field_simp
  rw [← this] at hpos ⊢
  nlinarith [mul_pos hba hpos]

lemma Hs_continuousOn : ContinuousOn (Hs β γ) (Iio 1) := fun s hs =>
  (hasDerivAt_Hs hβ hγ hs).continuousAt.continuousWithinAt

lemma Hs_strictMonoOn : StrictMonoOn (Hs β γ) (Iio 1) := by
  intro x hx y hy hxy
  simp only [mem_Iio] at hx hy
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (Hs β γ) (hf β γ) hxy
    ((Hs_continuousOn hβ hγ).mono (fun z hz => lt_of_le_of_lt hz.2 hy))
    (fun z hz => hasDerivAt_Hs hβ hγ (lt_trans hz.2 hy))
  have := hf_pos hβ hγ c
  rw [hc', lt_div_iff₀ (sub_pos.2 hxy)] at this
  linarith

lemma S_ge {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l < 1) : Real.sqrt γ * l ≤ Hs β γ l - Hs β γ 0 := by
  rcases hl0.eq_or_lt with h | h
  · rw [← h]; simp
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (Hs β γ) (hf β γ) h
    ((Hs_continuousOn hβ hγ).mono (fun z hz => lt_of_le_of_lt hz.2 hl1))
    (fun z hz => hasDerivAt_Hs hβ hγ (lt_trans hz.2 hl1))
  have h1 := hf_ge hβ hγ (lt_trans hc.2 hl1)
  have h2 : Real.sqrt γ ≤ Real.sqrt γ / (1 - c) := by
    rw [le_div_iff₀ (by linarith [hc.2])]
    have := Real.sqrt_nonneg γ
    nlinarith [hc.1]
  rw [hc', sub_zero, le_div_iff₀ h] at h1
  nlinarith

noncomputable def phi (β γ l : ℝ) : ℝ := 2 * (Hs β γ l - Hs β γ 0) * hf β γ l

lemma S_nonneg {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l < 1) : 0 ≤ Hs β γ l - Hs β γ 0 := by
  have := S_ge hβ hγ hl0 hl1
  have : 0 ≤ Real.sqrt γ * l := mul_nonneg (Real.sqrt_nonneg _) hl0
  linarith

lemma phi_strictMonoOn : StrictMonoOn (phi β γ) (Ico 0 1) := by
  intro x hx y hy hxy
  unfold phi
  have hS : Hs β γ x - Hs β γ 0 ≤ Hs β γ y - Hs β γ 0 := by
    have := (Hs_strictMonoOn hβ hγ) (show x < 1 from hx.2) (show y < 1 from hy.2) hxy
    linarith
  have hSx := S_nonneg hβ hγ hx.1 hx.2
  have hSy : 0 < Hs β γ y - Hs β γ 0 := by
    have := (Hs_strictMonoOn hβ hγ) (show (0:ℝ) < 1 by norm_num) (show y < 1 from hy.2)
      (lt_of_le_of_lt hx.1 hxy)
    linarith
  have hh : hf β γ x < hf β γ y := hf_strictMonoOn hβ hγ (show x < 1 from hx.2) (show y < 1 from hy.2) hxy
  have := hf_pos hβ hγ x
  nlinarith

lemma phi_continuousOn : ContinuousOn (phi β γ) (Iio 1) := by
  unfold phi
  exact ((continuousOn_const.mul ((Hs_continuousOn hβ hγ).sub continuousOn_const))).mul
    (hf_continuousOn hβ hγ)

lemma phi_zero : phi β γ 0 = 0 := by simp [phi]

lemma exists_lstar {D : ℝ} (hD : 0 < D) : ∃ l ∈ Ioo (0:ℝ) 1, phi β γ l = D := by
  set l1 := D / (D + γ)
  have hl1 : 0 < l1 := by positivity
  have hl1' : l1 < 1 := by rw [div_lt_one (by positivity)]; linarith
  have h1l : 1 - l1 = γ / (D + γ) := by simp only [l1]; field_simp; ring
  have hphi : D ≤ phi β γ l1 := by
    unfold phi
    have hS := S_ge hβ hγ hl1.le hl1'
    have hh := hf_ge hβ hγ hl1'
    have hsg : 0 ≤ Real.sqrt γ := Real.sqrt_nonneg _
    have e : Real.sqrt γ * l1 * (Real.sqrt γ / (1 - l1)) = D := by
      rw [h1l]
      have : Real.sqrt γ * Real.sqrt γ = γ := Real.mul_self_sqrt hγ.le
      simp only [l1]
      field_simp
      exact Real.sq_sqrt hγ.le
    have h2 : Real.sqrt γ * l1 * (Real.sqrt γ / (1 - l1)) ≤ (Hs β γ l1 - Hs β γ 0) * hf β γ l1 := by
      apply mul_le_mul hS hh (by positivity)
      exact S_nonneg hβ hγ hl1.le hl1'
    linarith
  obtain ⟨l, hl, hlD⟩ := intermediate_value_Icc hl1.le
    ((phi_continuousOn hβ hγ).mono (fun z hz => lt_of_le_of_lt hz.2 hl1')) ⟨by rw [phi_zero hβ hγ]; exact hD.le, hphi⟩
  refine ⟨l, ⟨?_, lt_of_le_of_lt hl.2 hl1'⟩, hlD⟩
  rcases hl.1.eq_or_lt with h | h
  · rw [← h, phi_zero hβ hγ] at hlD; linarith
  · exact h

lemma hasDerivAt_g (D : ℝ) {l : ℝ} (hl : l < 1) :
    HasDerivAt (fun l => D * l - (Hs β γ l - Hs β γ 0) ^ 2) (D - phi β γ l) l := by
  have h := ((hasDerivAt_id l).const_mul D).sub (((hasDerivAt_Hs hβ hγ hl).sub_const (Hs β γ 0)).pow 2)
  refine h.congr_deriv ?_
  simp [phi]

lemma g_strict {D ls l : ℝ} (hls : ls ∈ Ioo (0:ℝ) 1) (hphi : phi β γ ls = D) (hl0 : 0 ≤ l)
    (hl1 : l < 1) (hne : l ≠ ls) :
    D * l - (Hs β γ l - Hs β γ 0) ^ 2 < D * ls - (Hs β γ ls - Hs β γ 0) ^ 2 := by
  set g := fun l => D * l - (Hs β γ l - Hs β γ 0) ^ 2
  have gc : ContinuousOn g (Iio 1) := fun x hx => (hasDerivAt_g hβ hγ D hx).continuousAt.continuousWithinAt
  show g l < g ls
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope g (fun x => D - phi β γ x) h
      (gc.mono (fun z hz => lt_of_le_of_lt hz.2 hls.2)) (fun z hz => hasDerivAt_g hβ hγ D (lt_trans hz.2 hls.2))
    have : phi β γ c < phi β γ ls := phi_strictMonoOn hβ hγ ⟨hl0.trans hc.1.le, lt_trans hc.2 hls.2⟩
      ⟨hls.1.le, hls.2⟩ hc.2
    have hpos : 0 < (g ls - g l) / (ls - l) := by rw [← hc']; linarith
    have := (div_pos_iff_of_pos_right (sub_pos.2 h)).1 hpos
    linarith
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope g (fun x => D - phi β γ x) h
      (gc.mono (fun z hz => lt_of_le_of_lt hz.2 hl1)) (fun z hz => hasDerivAt_g hβ hγ D (lt_trans hz.2 hl1))
    have : phi β γ ls < phi β γ c := phi_strictMonoOn hβ hγ ⟨hls.1.le, hls.2⟩
      ⟨hls.1.le.trans hc.1.le, lt_trans hc.2 hl1⟩ hc.1
    have hneg : (g l - g ls) / (l - ls) < 0 := by rw [← hc']; linarith
    have := (div_neg_iff.1 hneg)
    rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · linarith

lemma g_le {D ls l : ℝ} (hls : ls ∈ Ioo (0:ℝ) 1) (hphi : phi β γ ls = D) (hl0 : 0 ≤ l)
    (hl1 : l < 1) :
    D * l - (Hs β γ l - Hs β γ 0) ^ 2 ≤ D * ls - (Hs β γ ls - Hs β γ 0) ^ 2 := by
  by_cases h : l = ls
  · rw [h]
  · exact (g_strict hβ hγ hls hphi hl0 hl1 h).le

end RealAn

section Closed
open DiscServLine.SPT

lemma kappa_eq (P : Params) (hP : P.Standing) : κ P = (P.b / P.Λ) / (P.c / 2) := by
  obtain ⟨hc, hcθ, hb, hΛ⟩ := hP
  unfold κ; field_simp

lemma closed_forms (P : Params) (hP : P.Standing) {ls : ℝ} (hls : ls ∈ Ioo (0:ℝ) 1)
    (hphi : phi (P.b / P.Λ) (P.c / 2) ls = P.θbar - P.c) :
    (1 - ls) ^ 2 ∈ Ioo (0:ℝ) 1 ∧ F35 P ((1 - ls) ^ 2) = 0 ∧ 1 - Real.sqrt ((1 - ls) ^ 2) = ls ∧
    (H2 (P.b / P.Λ) (P.c / 2) ls - H2 (P.b / P.Λ) (P.c / 2) 0) / P.Λ * hf (P.b / P.Λ) (P.c / 2) 0
      = tLoA7 P ((1 - ls) ^ 2) ∧
    (H2 (P.b / P.Λ) (P.c / 2) ls - H2 (P.b / P.Λ) (P.c / 2) 0) / P.Λ * hf (P.b / P.Λ) (P.c / 2) ls
      = tHiA7 P ((1 - ls) ^ 2) ∧
    (H2 (P.b / P.Λ) (P.c / 2) ls - H2 (P.b / P.Λ) (P.c / 2) 0) / P.Λ *
      (Hs (P.b / P.Λ) (P.c / 2) ls - Hs (P.b / P.Λ) (P.c / 2) 0) = Λ2A7 P ((1 - ls) ^ 2) := by
  have hκ := kappa_eq P hP
  obtain ⟨hc, hcθ, hb, hΛ⟩ := hP
  set β := P.b / P.Λ with hβdef
  set γ := P.c / 2 with hγdef
  have hβ : 0 < β := by positivity
  have hγ : 0 < γ := by positivity
  set k := κ P with hkdef
  have hk : 0 < k := by rw [hκ]; positivity
  set x0 := 1 - ls with hx0def
  have hx0 : 0 < x0 := by linarith [hls.2]
  have hx1 : x0 < 1 := by linarith [hls.1]
  have hsq : Real.sqrt (x0 ^ 2) = x0 := Real.sqrt_sq hx0.le
  set r0 := rf β γ ls with hr0def
  set r1 := rf β γ 0 with hr1def
  have hr0p : 0 < r0 := rf_pos hβ hγ ls
  have hr1p : 0 < r1 := rf_pos hβ hγ 0
  have hr0sq : r0 ^ 2 = 1 + k * x0 ^ 2 := by rw [hr0def, rf_sq hβ hγ, hκ]
  have hr1sq : r1 ^ 2 = 1 + k := by rw [hr1def, rf_sq hβ hγ, hκ]; ring
  have e1 : Real.sqrt (1 + k * x0 ^ 2) = r0 := by rw [hr0def, rf, hκ]
  have e1' : Real.sqrt (1 + x0 ^ 2 * k) = r0 := by rw [mul_comm]; exact e1
  have e2 : Real.sqrt (1 + k) = r1 := by rw [hr1def, rf, hκ]; congr 1; ring
  have e3 : Real.sqrt (1 / x0 ^ 2 + k) = r0 / x0 := by
    rw [show 1 / x0 ^ 2 + k = (r0 / x0) ^ 2 by rw [div_pow, hr0sq]; field_simp]
    exact Real.sqrt_sq (by positivity)
  have e4 : Real.sqrt (x0 ^ 2 / (1 + x0 ^ 2 * k)) = x0 / r0 := by
    rw [show x0 ^ 2 / (1 + x0 ^ 2 * k) = (x0 / r0) ^ 2 by rw [div_pow, hr0sq]; ring_nf]
    exact Real.sqrt_sq (by positivity)
  have e5 : Real.sqrt ((1 + k) / (1 + x0 ^ 2 * k)) = r1 / r0 := by
    rw [show (1 + k) / (1 + x0 ^ 2 * k) = (r1 / r0) ^ 2 by rw [div_pow, hr0sq, hr1sq]; ring_nf]
    exact Real.sqrt_sq (by positivity)
  have hsγ : Real.sqrt γ ^ 2 = γ := Real.sq_sqrt hγ.le
  have hsγp : 0 < Real.sqrt γ := Real.sqrt_pos.2 hγ
  have hbc : P.b / (P.Λ * P.c) = k / 2 := by rw [hkdef]; unfold κ; field_simp
  have hkb : k * P.Λ = 2 * P.b / P.c := by rw [hkdef]; unfold κ; field_simp
  -- log term
  have hlog : (1 / 2 : ℝ) * Real.log ((k / 2 + 1 / x0 ^ 2 + (1 / x0) * (r0 / x0)) / (k / 2 + 1 + r1))
      = Real.log (1 + r0) - (Real.log x0 + Real.log (1 + r1)) := by
    have hy : (k / 2 + 1 / x0 ^ 2 + (1 / x0) * (r0 / x0)) / (k / 2 + 1 + r1) =
        ((1 + r0) / (x0 * (1 + r1))) ^ 2 := by
      have h1 : k / 2 + 1 + r1 = (1 + r1) ^ 2 / 2 := by linear_combination (-1/2:ℝ) * hr1sq
      have h2 : k / 2 + 1 / x0 ^ 2 + (1 / x0) * (r0 / x0) = (1 + r0) ^ 2 / (2 * x0 ^ 2) := by
        field_simp
        linear_combination (-1:ℝ) * hr0sq
      rw [h1, h2]; field_simp
    rw [hy, Real.log_pow, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    push_cast; ring
  -- Hs difference
  have hHs : Hs β γ ls - Hs β γ 0 = Real.sqrt γ *
      (r1 - r0 - Real.log x0 + Real.log (1 + r0) - Real.log (1 + r1)) := by
    simp only [Hs, sub_zero, Real.log_one, ← hr0def, ← hr1def, ← hx0def]; ring
  have hhf : hf β γ ls = Real.sqrt γ * r0 / x0 := hf_eq hβ hγ hls.2
  have hhf0 : hf β γ 0 = Real.sqrt γ * r1 := by rw [hf_eq hβ hγ (by norm_num)]; simp [hr1def]
  have hH2 : H2 β γ ls - H2 β γ 0 = (r1 - r0) / (k * Real.sqrt γ) := by
    simp only [H2, ← hr0def, ← hr1def, ← hκ]; ring
  set E := r1 - r0 - Real.log x0 + Real.log (1 + r0) - Real.log (1 + r1) with hE
  have hphi' : P.c * (r0 / x0) * E = P.θbar - P.c := by
    rw [← hphi]; unfold phi; rw [hHs, hhf]
    field_simp
    rw [hsγ, hγdef]; ring
  have hls' : 1 - Real.sqrt (x0 ^ 2) = ls := by rw [hsq, hx0def]; ring
  have hω : x0 ^ 2 ∈ Ioo (0:ℝ) 1 := ⟨by positivity, by nlinarith⟩
  rw [hhf0, hhf, hH2, hHs]
  clear_value E r0 r1 x0 k γ β
  have hEval : E = (P.θbar / P.c - 1) * x0 / r0 := by
    rw [eq_div_iff hr0p.ne']
    field_simp at hphi' ⊢
    linear_combination hphi'
  refine ⟨hω, ?_, hls', ?_, ?_, ?_⟩
  · unfold F35
    rw [hsq, hbc, ← hkdef, e3, e2, e1, hlog]
    have : Real.log (1 + r0) - (Real.log x0 + Real.log (1 + r1)) = E - (r1 - r0) := by rw [hE]; ring
    rw [this, hEval]
    field_simp
    ring
  · have hL : ∀ y, (r1 - r0) / (k * Real.sqrt γ) / P.Λ * (Real.sqrt γ * y) = (r1 - r0) * y / (k * P.Λ) := by
      intro y; field_simp
    rw [hL, hkb]
    unfold tLoA7
    rw [← hkdef, e2, e1']
    field_simp
  · have hL : ∀ y, (r1 - r0) / (k * Real.sqrt γ) / P.Λ * (Real.sqrt γ * y) = (r1 - r0) * y / (k * P.Λ) := by
      intro y; field_simp
    rw [mul_div_assoc, hL, hkb]
    unfold tHiA7
    rw [← hkdef, e2, e1', e4]
    field_simp
  · have hL : ∀ y, (r1 - r0) / (k * Real.sqrt γ) / P.Λ * (Real.sqrt γ * y) = (r1 - r0) * y / (k * P.Λ) := by
      intro y; field_simp
    rw [hL, hkb, hEval]
    unfold Λ2A7
    rw [← hkdef, e5, hsq]
    field_simp
    ring

end Closed

end DslA7


open MeasureTheory Set Filter Topology

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace DslA7
open DiscServLine.SPT

section Feas
variable {d : Design}

lemma ae_supp (hd : Admissible d) : ∀ᵐ t ∂d.μ, t ∈ Icc d.lo d.hi := by
  rw [ae_iff]
  exact hd.2.2.2.1

lemma ae_nonneg (hd : Admissible d) : ∀ᵐ t ∂d.μ, 0 ≤ t := by
  filter_upwards [ae_supp hd] with t ht using hd.2.1.trans ht.1

lemma integrable_of_bdd (hd : Admissible d) {f : ℝ → ℝ} (hf : AEStronglyMeasurable f d.μ) (C : ℝ)
    (hC : ∀ t ∈ Icc d.lo d.hi, |f t| ≤ C) : Integrable f d.μ := by
  haveI := hd.1
  exact Integrable.of_bound hf C (by filter_upwards [ae_supp hd] with t ht; exact hC t ht)

lemma integrable_pow (hd : Admissible d) (k : ℕ) : Integrable (fun t : ℝ => t ^ k) d.μ := by
  apply integrable_of_bdd hd (by fun_prop) (d.hi ^ k)
  intro t ht
  have h0 : 0 ≤ t := hd.2.1.trans ht.1
  rw [abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ h0 ht.2 k

lemma integrable_id' (hd : Admissible d) : Integrable (fun t : ℝ => t) d.μ := by
  simpa using integrable_pow hd 1

/-- the load measure -/
noncomputable def nu (d : Design) : Measure ℝ := d.μ.withDensity (fun t => ENNReal.ofReal t)

lemma nu_finite (hd : Admissible d) : IsFiniteMeasure (nu d) := by
  haveI := hd.1
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  calc ∫⁻ t, ENNReal.ofReal t ∂d.μ ≤ ∫⁻ t, ENNReal.ofReal d.hi ∂d.μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_supp hd] with t ht
        exact ENNReal.ofReal_le_ofReal ht.2
    _ < ⊤ := by rw [lintegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

lemma nu_real (hd : Admissible d) {A : Set ℝ} (hA : MeasurableSet A) :
    (nu d).real A = ∫ t in A, t ∂d.μ := by
  rw [measureReal_def, nu, withDensity_apply _ hA, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [ENNReal.toReal_ofReal]
    exact integral_nonneg_of_ae (ae_restrict_of_ae (ae_nonneg hd))
  · exact (integrable_id' hd).integrableOn
  · exact ae_restrict_of_ae (ae_nonneg hd)

lemma Fn_nu (hd : Admissible d) (x : ℝ) : Fn (nu d) x = d.loadUpTo x := nu_real hd measurableSet_Iic
lemma Fm_nu (hd : Admissible d) (x : ℝ) : Fm (nu d) x = d.loadBelow x := nu_real hd measurableSet_Iio
lemma T_nu (hd : Admissible d) : (nu d).real univ = d.Λk 1 := by
  rw [nu_real hd MeasurableSet.univ, Measure.restrict_univ]
  simp [Design.Λk]

lemma nu_singleton (t : ℝ) : nu d {t} = ENNReal.ofReal t * d.μ {t} := by
  rw [nu, withDensity_apply _ (measurableSet_singleton t), lintegral_singleton]

lemma integral_nu (hd : Admissible d) (g : ℝ → ℝ) : ∫ t, g t ∂(nu d) = ∫ t, t * g t ∂d.μ := by
  have : nu d = d.μ.withDensity (fun t => ((Real.toNNReal t : NNReal) : ENNReal)) := rfl
  rw [this, integral_withDensity_eq_integral_smul measurable_real_toNNReal]
  apply integral_congr_ae
  filter_upwards [ae_nonneg hd] with t ht
  simp [NNReal.smul_def, Real.coe_toNNReal t ht]

lemma nu_Iio0 (hd : Admissible d) : nu d (Iio 0) = 0 := by
  apply withDensity_absolutelyContinuous
  apply measure_mono_null _ hd.2.2.2.1
  intro t ht hmem
  exact absurd (lt_of_lt_of_le ht (hd.2.1.trans hmem.1)) (lt_irrefl _)

lemma nu_Iio_lo (hd : Admissible d) : nu d (Iio d.lo) = 0 := by
  apply withDensity_absolutelyContinuous
  apply measure_mono_null _ hd.2.2.2.1
  intro t ht hmem
  exact absurd (lt_of_lt_of_le ht hmem.1) (lt_irrefl _)

lemma nu_Ioi_hi (hd : Admissible d) : nu d (Ioi d.hi) = 0 := by
  apply withDensity_absolutelyContinuous
  apply measure_mono_null _ hd.2.2.2.1
  intro t ht hmem
  exact absurd (lt_of_le_of_lt hmem.2 ht) (lt_irrefl _)

lemma exists_of_pos {μ : Measure ℝ} {A : Set ℝ} {p : ℝ → Prop} (hA : 0 < μ A) (hp : ∀ᵐ t ∂μ, p t) :
    ∃ t ∈ A, p t := by
  by_contra hc
  push Not at hc
  have : μ A = 0 := measure_mono_null (fun t ht => hc t ht) (ae_iff.1 hp)
  rw [this] at hA; exact lt_irrefl _ hA

section Bound
variable {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
include hβ hγ

lemma rho_pos {a b : ℝ} (ha : a < 1) (hb : b < 1) : 0 < rho β γ a b := by
  unfold rho
  have : 0 < (1 - a) * (1 - b) := mul_pos (by linarith) (by linarith)
  positivity

lemma sig_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) : 0 ≤ sig β γ a b := by
  unfold sig
  split_ifs with h
  · apply div_nonneg _ (by linarith)
    have := (Hs_strictMonoOn hβ hγ) (show a < 1 by linarith) (show b < 1 from hb) h
    linarith
  · exact (hf_pos hβ hγ a).le

lemma sig_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    sig β γ a b ≤ Real.sqrt (rho β γ a b) := by
  rcases hab.lt_or_eq with h | h
  · have hj := jensen_strict hβ hγ h hb
    have hs := sig_nonneg hβ hγ ha hab hb
    apply (Real.le_sqrt hs (rho_pos hβ hγ (by linarith) hb).le).2
    unfold sig; rw [if_pos h, div_pow]
    rw [div_le_iff₀ (by have : 0 < b - a := by linarith
                        positivity)]
    linarith
  · subst h; unfold sig; rw [if_neg (lt_irrefl _), sqrt_rho_aa hβ hγ hb]

lemma sig_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) :
    sig β γ a b < Real.sqrt (rho β γ a b) := by
  have hj := jensen_strict hβ hγ hab hb
  have hs := sig_nonneg hβ hγ ha hab.le hb
  apply (Real.lt_sqrt hs).2
  unfold sig; rw [if_pos hab, div_pow]
  rw [div_lt_iff₀ (by have : 0 < b - a := by linarith
                      positivity)]
  linarith

lemma rho_le {a b T : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T) (hT : T < 1) :
    rho β γ a b ≤ β + γ / ((1 - T) * (1 - T)) := by
  unfold rho
  have h1 : 0 < 1 - T := by linarith
  have : (1 - T) * (1 - T) ≤ (1 - a) * (1 - b) := mul_le_mul (by linarith) (by linarith) h1.le (by linarith)
  have : γ / ((1 - a) * (1 - b)) ≤ γ / ((1 - T) * (1 - T)) :=
    div_le_div_of_nonneg_left hγ.le (by positivity) this
  linarith

lemma sig_measurable {f1 f2 : ℝ → ℝ} (h1 : Measurable f1) (h2 : Measurable f2) :
    Measurable (fun t => sig β γ (f1 t) (f2 t)) := by
  unfold sig Hs rf hf
  apply Measurable.ite (measurableSet_lt h1 h2) <;> fun_prop

end Bound

lemma cs_gen {μ : Measure ℝ} {f1 f2 : ℝ → ℝ} (h11 : Integrable (fun t => f1 t ^ 2) μ)
    (h12 : Integrable (fun t => f1 t * f2 t) μ) (h22 : Integrable (fun t => f2 t ^ 2) μ)
    (hR : 0 < ∫ t, f2 t ^ 2 ∂μ) :
    (∫ t, f1 t * f2 t ∂μ) ^ 2 ≤ (∫ t, f1 t ^ 2 ∂μ) * (∫ t, f2 t ^ 2 ∂μ) ∧
    ((∫ t, f1 t * f2 t ∂μ) ^ 2 = (∫ t, f1 t ^ 2 ∂μ) * (∫ t, f2 t ^ 2 ∂μ) →
      ∀ᵐ t ∂μ, f1 t = (∫ t, f1 t * f2 t ∂μ) / (∫ t, f2 t ^ 2 ∂μ) * f2 t) := by
  set A := ∫ t, f1 t ^ 2 ∂μ
  set M := ∫ t, f1 t * f2 t ∂μ
  set R := ∫ t, f2 t ^ 2 ∂μ
  set l := M / R
  have hint : Integrable (fun t => (f1 t - l * f2 t) ^ 2) μ := by
    have e : (fun t => (f1 t - l * f2 t) ^ 2) = fun t => f1 t ^ 2 - 2 * l * (f1 t * f2 t) + l ^ 2 * f2 t ^ 2 := by
      funext t; ring
    rw [e]; exact (h11.sub (h12.const_mul _)).add (h22.const_mul _)
  have key : ∫ t, (f1 t - l * f2 t) ^ 2 ∂μ = A - M ^ 2 / R := by
    have e : (fun t => (f1 t - l * f2 t) ^ 2) = fun t => f1 t ^ 2 - 2 * l * (f1 t * f2 t) + l ^ 2 * f2 t ^ 2 := by
      funext t; ring
    rw [e]
    calc ∫ t, f1 t ^ 2 - 2 * l * (f1 t * f2 t) + l ^ 2 * f2 t ^ 2 ∂μ
        = ∫ t, (f1 t ^ 2 - 2 * l * (f1 t * f2 t)) ∂μ + ∫ t, l ^ 2 * f2 t ^ 2 ∂μ :=
          integral_add (h11.sub (h12.const_mul _)) (h22.const_mul _)
      _ = (A - 2 * l * M) + l ^ 2 * R := by
          rw [integral_sub h11 (h12.const_mul _), integral_const_mul, integral_const_mul]
      _ = A - M ^ 2 / R := by simp only [l]; field_simp; ring
  have hnn : 0 ≤ ∫ t, (f1 t - l * f2 t) ^ 2 ∂μ := integral_nonneg (fun t => sq_nonneg _)
  rw [key] at hnn
  refine ⟨?_, ?_⟩
  · have := (div_le_iff₀ hR).1 (by linarith : M ^ 2 / R ≤ A)
    linarith
  · intro heq
    have h0 : ∫ t, (f1 t - l * f2 t) ^ 2 ∂μ = 0 := by
      rw [key, heq]; field_simp; ring
    have := (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg _) hint).1 h0
    filter_upwards [this] with t ht
    simp only [Pi.zero_apply, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at ht
    linarith

end Feas
section Main
variable {P : Params} {d : Design}

noncomputable def bt (P : Params) : ℝ := P.b / P.Λ
noncomputable def gm (P : Params) : ℝ := P.c / 2
noncomputable def rhod (P : Params) (d : Design) (t : ℝ) : ℝ :=
  rho (bt P) (gm P) (d.loadBelow t) (d.loadUpTo t)
noncomputable def Jd (d : Design) : ℝ := ∫ t, 1 / ((1 - d.loadBelow t) * (1 - d.loadUpTo t)) ∂d.μ
noncomputable def Rd (P : Params) (d : Design) : ℝ := ∫ t, rhod P d t ∂d.μ
noncomputable def Md (P : Params) (d : Design) : ℝ := ∫ t, t * Real.sqrt (rhod P d t) ∂d.μ
noncomputable def Sf (P : Params) (x : ℝ) : ℝ := Hs (bt P) (gm P) x - Hs (bt P) (gm P) 0

lemma bt_pos (hP : P.Standing) : 0 < bt P := div_pos hP.2.2.1 hP.2.2.2
lemma gm_pos (hP : P.Standing) : 0 < gm P := half_pos hP.1

lemma lb_eq (hd : Admissible d) : d.loadBelow = Fm (nu d) := funext (fun x => (Fm_nu hd x).symm)
lemma lu_eq (hd : Admissible d) : d.loadUpTo = Fn (nu d) := funext (fun x => (Fn_nu hd x).symm)

lemma loads (hd : Admissible d) (t : ℝ) :
    0 ≤ d.loadBelow t ∧ d.loadBelow t ≤ d.loadUpTo t ∧ d.loadUpTo t ≤ d.Λk 1 := by
  haveI := nu_finite hd
  rw [lb_eq hd, lu_eq hd, ← T_nu hd]
  exact ⟨Fm_nonneg _ t, Fm_le_Fn _ t, Fn_le_univ _ t⟩

lemma lb_meas (hd : Admissible d) : Measurable d.loadBelow := by
  haveI := nu_finite hd; rw [lb_eq hd]; exact Fm_measurable _
lemma lu_meas (hd : Admissible d) : Measurable d.loadUpTo := by
  haveI := nu_finite hd; rw [lu_eq hd]; exact Fn_measurable _

lemma T_lt (hd : Admissible d) : d.Λk 1 < 1 := hd.2.2.2.2.2.2

lemma Jint_bdd (hd : Admissible d) (t : ℝ) :
    0 < (1 - d.loadBelow t) * (1 - d.loadUpTo t) ∧
    1 / ((1 - d.loadBelow t) * (1 - d.loadUpTo t)) ≤ 1 / ((1 - d.Λk 1) * (1 - d.Λk 1)) := by
  obtain ⟨h1, h2, h3⟩ := loads hd t
  have hT := T_lt hd
  have hp : 0 < (1 - d.Λk 1) * (1 - d.Λk 1) := mul_pos (by linarith) (by linarith)
  refine ⟨mul_pos (by linarith) (by linarith), ?_⟩
  apply one_div_le_one_div_of_le hp
  exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)

lemma Jint_integrable (hd : Admissible d) :
    Integrable (fun t => 1 / ((1 - d.loadBelow t) * (1 - d.loadUpTo t))) d.μ := by
  apply integrable_of_bdd hd _ (1 / ((1 - d.Λk 1) * (1 - d.Λk 1)))
  · intro t _
    obtain ⟨hp, hle⟩ := Jint_bdd hd t
    rw [abs_of_pos (one_div_pos.2 hp)]; exact hle
  · have := lb_meas hd; have := lu_meas hd
    exact Measurable.aestronglyMeasurable (by fun_prop)

lemma rhod_pos (hP : P.Standing) (hd : Admissible d) (t : ℝ) : 0 < rhod P d t := by
  obtain ⟨h1, h2, h3⟩ := loads hd t
  have hT := T_lt hd
  exact rho_pos (bt_pos hP) (gm_pos hP) (by linarith) (by linarith)

lemma rhod_le (hP : P.Standing) (hd : Admissible d) (t : ℝ) :
    rhod P d t ≤ bt P + gm P / ((1 - d.Λk 1) * (1 - d.Λk 1)) := by
  obtain ⟨h1, h2, h3⟩ := loads hd t
  exact rho_le (bt_pos hP) (gm_pos hP) h1 h2 h3 (T_lt hd)

lemma rhod_meas (hd : Admissible d) : Measurable (rhod P d) := by
  have := lb_meas hd; have := lu_meas hd
  unfold rhod rho; fun_prop

lemma Lk0_eq (d : Design) : d.Λk 0 = d.μ.real univ := by
  simp [Design.Λk]

lemma Lk0_pos (hd : Admissible d) : 0 < d.Λk 0 := by
  haveI := hd.1
  rw [Lk0_eq]
  have := hd.2.2.2.2.1 1 one_pos
  exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le this (measure_mono (subset_univ _))))
    (measure_ne_top _ _)

lemma profit_eq (d : Design) :
    profit P d = (P.θbar - P.c) * d.Λk 1 - d.Λk 2 * (P.b + gm P * Jd d) := by
  have hQ : d.Q = d.Λk 2 / 2 * Jd d := by
    unfold Design.Q Jd
    rw [← integral_const_mul]
    congr 1; funext t; unfold Design.W; rw [div_eq_mul_one_div]
  unfold profit; rw [hQ, gm]; ring

lemma Rd_eq (hP : P.Standing) (hd : Admissible d) : Rd P d = bt P * d.Λk 0 + gm P * Jd d := by
  haveI := hd.1
  unfold Rd Jd
  have e : rhod P d = fun t => bt P + gm P * (1 / ((1 - d.loadBelow t) * (1 - d.loadUpTo t))) := by
    funext t; unfold rhod rho; ring
  rw [e, integral_add (integrable_const _) ((Jint_integrable hd).const_mul _), integral_const,
    integral_const_mul, Lk0_eq, smul_eq_mul, mul_comm (d.μ.real univ)]

lemma Jd_nonneg (hd : Admissible d) : 0 ≤ Jd d :=
  integral_nonneg (fun t => (one_div_pos.2 (Jint_bdd hd t).1).le)

lemma Lk2_nonneg (d : Design) : 0 ≤ d.Λk 2 :=
  integral_nonneg (fun t => sq_nonneg t)

lemma Rd_pos (hP : P.Standing) (hd : Admissible d) : 0 < Rd P d := by
  rw [Rd_eq hP hd]
  have := Lk0_pos hd
  have := Jd_nonneg hd
  have := bt_pos hP
  have := gm_pos hP
  positivity

lemma sqrt_rhod_integrable (hP : P.Standing) (hd : Admissible d) :
    Integrable (fun t => t * Real.sqrt (rhod P d t)) d.μ := by
  apply integrable_of_bdd hd ((measurable_id.mul (rhod_meas hd).sqrt).aestronglyMeasurable)
    (d.hi * Real.sqrt (bt P + gm P / ((1 - d.Λk 1) * (1 - d.Λk 1))))
  intro t ht
  have h0 : 0 ≤ t := hd.2.1.trans ht.1
  show |t * Real.sqrt (rhod P d t)| ≤ _
  rw [abs_of_nonneg (mul_nonneg h0 (Real.sqrt_nonneg _))]
  exact mul_le_mul ht.2 (Real.sqrt_le_sqrt (rhod_le hP hd t)) (Real.sqrt_nonneg _) (h0.trans ht.2)

lemma cs_fact (hP : P.Standing) (hd : Admissible d) :
    Md P d ^ 2 ≤ d.Λk 2 * Rd P d ∧
    (Md P d ^ 2 = d.Λk 2 * Rd P d → ∀ᵐ t ∂d.μ, t = Md P d / Rd P d * Real.sqrt (rhod P d t)) := by
  have e2 : (fun t => Real.sqrt (rhod P d t) ^ 2) = rhod P d := by
    funext t; exact Real.sq_sqrt (rhod_pos hP hd t).le
  have hRint : Integrable (rhod P d) d.μ := by
    apply integrable_of_bdd hd (rhod_meas hd).aestronglyMeasurable
      (bt P + gm P / ((1 - d.Λk 1) * (1 - d.Λk 1)))
    intro t _; rw [abs_of_pos (rhod_pos hP hd t)]; exact rhod_le hP hd t
  have h := cs_gen (μ := d.μ) (f1 := fun t => t) (f2 := fun t => Real.sqrt (rhod P d t))
    (integrable_pow hd 2) (sqrt_rhod_integrable hP hd) (by rw [e2]; exact hRint)
    (by rw [e2]; exact Rd_pos hP hd)
  rw [e2] at h
  exact h

lemma nu_bounds (hd : Admissible d) (t : ℝ) :
    0 ≤ Fm (nu d) t ∧ Fm (nu d) t ≤ Fn (nu d) t ∧ Fn (nu d) t ≤ d.Λk 1 := by
  rw [← lb_eq hd, ← lu_eq hd]; exact loads hd t

lemma gl_fact (hP : P.Standing) (hd : Admissible d) :
    Sf P (d.Λk 1) ≤ Md P d ∧ (Md P d = Sf P (d.Λk 1) → ∀ t, nu d {t} = 0) := by
  haveI := nu_finite hd
  have hβ := bt_pos hP
  have hγ := gm_pos hP
  set β := bt P
  set γ := gm P
  set ν := nu d with hνdef
  have hK : 0 ≤ d.hi := hd.2.1.trans hd.2.2.1
  have hT := T_lt hd
  have hTν := T_nu hd
  set T := d.Λk 1
  set g := fun t => sig β γ (Fm ν t) (Fn ν t) with hg
  set f := fun t => Real.sqrt (rho β γ (Fm ν t) (Fn ν t)) with hf'
  have hgm : Measurable g := sig_measurable hβ hγ (Fm_measurable ν) (Fn_measurable ν)
  have hfm : Measurable f := by
    have := Fm_measurable ν; have := Fn_measurable ν
    simp only [hf', rho]; fun_prop
  set C := Real.sqrt (β + γ / ((1 - T) * (1 - T)))
  have hfle : ∀ t, f t ≤ C := fun t => by
    obtain ⟨h1, h2, h3⟩ := nu_bounds hd t
    exact Real.sqrt_le_sqrt (rho_le hβ hγ h1 h2 h3 hT)
  have hgle : ∀ t, g t ≤ f t := fun t => by
    obtain ⟨h1, h2, h3⟩ := nu_bounds hd t
    exact sig_le hβ hγ h1 h2 (lt_of_le_of_lt h3 hT)
  have hg0 : ∀ t, 0 ≤ g t := fun t => by
    obtain ⟨h1, h2, h3⟩ := nu_bounds hd t
    exact sig_nonneg hβ hγ h1 h2 (lt_of_le_of_lt h3 hT)
  have hgb : ∀ t, |g t| ≤ C := fun t => by
    rw [abs_of_nonneg (hg0 t)]; exact (hgle t).trans (hfle t)
  have hatom : ∀ t, 0 < ν.real {t} → g t * ν.real {t} = Hs β γ (Fn ν t) - Hs β γ (Fm ν t) := by
    intro t ht
    have e := Fn_sub_Fm ν t
    have hlt : Fm ν t < Fn ν t := by linarith
    simp only [hg, sig, if_pos hlt]
    rw [← e]; field_simp [sub_ne_zero.2 hlt.ne']
  have hcont : ∀ t, ν.real {t} = 0 → g t = hf β γ (Fn ν t) := by
    intro t ht
    have e := Fn_sub_Fm ν t
    have heq : Fm ν t = Fn ν t := by linarith
    simp only [hg, sig, heq, lt_irrefl, if_false]
  have hH : ∀ x ∈ Icc 0 (ν.real univ), HasDerivAt (Hs β γ) (hf β γ x) x := by
    intro x hx; rw [hTν] at hx; exact hasDerivAt_Hs hβ hγ (lt_of_le_of_lt hx.2 hT)
  have hc : ContinuousOn (hf β γ) (Icc 0 (ν.real univ)) := by
    apply (hf_continuousOn hβ hγ).mono
    intro x hx; rw [hTν] at hx; exact lt_of_le_of_lt hx.2 hT
  have hGL := glthm hK (nu_Iio0 hd) (nu_Ioi_hi hd) (Hs β γ) (hf β γ) hH hc g hgm C hgb hatom hcont
  rw [hTν] at hGL
  have hM : Md P d = ∫ t, f t ∂ν := by
    rw [hνdef, integral_nu hd]; unfold Md rhod; rw [lb_eq hd, lu_eq hd]
  have hgi : Integrable g ν := Integrable.of_bound hgm.aestronglyMeasurable C
    (Eventually.of_forall (fun t => (Real.norm_eq_abs _).le.trans (hgb t)))
  have hfi : Integrable f ν := Integrable.of_bound hfm.aestronglyMeasurable C
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]; exact hfle t))
  have hSf : Sf P T = ∫ t, g t ∂ν := by rw [hGL]; rfl
  refine ⟨?_, ?_⟩
  · rw [hSf, hM]; exact integral_mono hgi hfi hgle
  · intro heq
    have h0 : ∫ t, (f t - g t) ∂ν = 0 := by
      rw [integral_sub hfi hgi, ← hM, ← hSf, heq, sub_self]
    have hae := (integral_eq_zero_iff_of_nonneg (fun t => sub_nonneg.2 (hgle t)) (hfi.sub hgi)).1 h0
    intro t
    by_contra hne
    have htpos : 0 < ν.real {t} := ENNReal.toReal_pos hne (measure_ne_top _ _)
    have e := Fn_sub_Fm ν t
    have hlt : Fm ν t < Fn ν t := by linarith
    obtain ⟨h1, h2, h3⟩ := nu_bounds hd t
    have hstrict : g t < f t := sig_lt hβ hγ h1 hlt (lt_of_le_of_lt h3 hT)
    have : ν {t} = 0 := by
      apply measure_mono_null _ (ae_iff.1 hae)
      intro x hx
      rw [mem_singleton_iff] at hx; subst hx
      simp only [Pi.zero_apply, mem_setOf_eq]
      linarith
    exact hne this

lemma T_nonneg (hd : Admissible d) : 0 ≤ d.Λk 1 := by
  haveI := nu_finite hd
  rw [← T_nu hd]; exact measureReal_nonneg

theorem bound (hP : P.Standing) (hd : Feasible P d) :
    profit P d ≤ (P.θbar - P.c) * d.Λk 1 - Sf P (d.Λk 1) ^ 2 := by
  obtain ⟨hd, hΛ0⟩ := hd
  have hβ := bt_pos hP
  have hγ := gm_pos hP
  rw [profit_eq]
  have h1 : d.Λk 2 * Rd P d ≤ d.Λk 2 * (P.b + gm P * Jd d) := by
    apply mul_le_mul_of_nonneg_left _ (Lk2_nonneg d)
    rw [Rd_eq hP hd]
    have : bt P * d.Λk 0 ≤ P.b := by
      unfold bt; rw [div_mul_eq_mul_div, div_le_iff₀ hP.2.2.2]
      exact mul_le_mul_of_nonneg_left hΛ0 hP.2.2.1.le
    linarith
  have h2 := (cs_fact hP hd).1
  have h3 := (gl_fact hP hd).1
  have h4 : 0 ≤ Sf P (d.Λk 1) := S_nonneg hβ hγ (T_nonneg hd) (T_lt hd)
  nlinarith

theorem eqcase (hP : P.Standing) (hd : Feasible P d) {ls : ℝ} (hls : ls ∈ Ioo (0:ℝ) 1)
    (hT : d.Λk 1 = ls) (heq : profit P d = (P.θbar - P.c) * ls - Sf P ls ^ 2) :
    d.Λk 0 = P.Λ ∧
    d.Λk 2 = (H2 (bt P) (gm P) ls - H2 (bt P) (gm P) 0) / P.Λ * Sf P ls ∧
    d.lo = (H2 (bt P) (gm P) ls - H2 (bt P) (gm P) 0) / P.Λ * hf (bt P) (gm P) 0 ∧
    d.hi = (H2 (bt P) (gm P) ls - H2 (bt P) (gm P) 0) / P.Λ * hf (bt P) (gm P) ls := by
  obtain ⟨hd, hΛ0⟩ := hd
  haveI := nu_finite hd
  haveI := hd.1
  have hβ := bt_pos hP
  have hγ := gm_pos hP
  have hΛ := hP.2.2.2
  set β := bt P
  set γ := gm P
  set ν := nu d with hνdef
  have hSpos : 0 < Sf P ls := by
    have := (Hs_strictMonoOn hβ hγ) (show (0:ℝ) < 1 by norm_num) (show ls < 1 from hls.2) hls.1
    unfold Sf; linarith
  -- the chain of inequalities
  rw [profit_eq] at heq
  have hb1 : bt P * d.Λk 0 ≤ P.b := by
    unfold bt; rw [div_mul_eq_mul_div, div_le_iff₀ hP.2.2.2]
    exact mul_le_mul_of_nonneg_left hΛ0 hP.2.2.1.le
  have hR := Rd_eq hP hd
  have hRpos := Rd_pos hP hd
  have hL2 := Lk2_nonneg d
  have hJ := Jd_nonneg hd
  have hcs := cs_fact hP hd
  have hgl := gl_fact hP hd
  rw [hT] at heq hgl
  have hA : d.Λk 2 * (P.b + gm P * Jd d) = Sf P ls ^ 2 := by linarith
  have hB1 : d.Λk 2 * Rd P d ≤ d.Λk 2 * (P.b + gm P * Jd d) := by
    apply mul_le_mul_of_nonneg_left _ hL2; rw [hR]; linarith
  have hMS : Sf P ls ≤ Md P d := hgl.1
  have hM2 : Md P d ^ 2 = d.Λk 2 * Rd P d := by nlinarith [hcs.1]
  have hM : Md P d = Sf P ls := by nlinarith
  have hB : d.Λk 2 * Rd P d = d.Λk 2 * (P.b + gm P * Jd d) := by nlinarith
  have hL2pos : 0 < d.Λk 2 := by
    rcases hL2.lt_or_eq with h | h
    · exact h
    · rw [← h] at hA; nlinarith
  have hΛ0eq : d.Λk 0 = P.Λ := by
    have : bt P * d.Λk 0 = P.b := by
      rw [hR] at hB
      have := mul_left_cancel₀ hL2pos.ne' hB
      linarith
    unfold bt at this
    field_simp at this
    nlinarith [hP.2.2.1]
  have hatomless := hgl.2 hM
  set lam := Md P d / Rd P d with hlam
  have hlampos : 0 < lam := div_pos (hM ▸ hSpos) hRpos
  have hae := hcs.2 hM2
  -- Fm = Fn everywhere
  have hFF : ∀ t, Fm ν t = Fn ν t := by
    intro t
    have e := Fn_sub_Fm ν t
    rw [measureReal_def, hatomless t] at e
    simp at e; linarith
  have hT1 : d.Λk 1 < 1 := T_lt hd
  have hrho : ∀ t, Real.sqrt (rhod P d t) = hf β γ (Fn ν t) := by
    intro t
    unfold rhod
    rw [lb_eq hd, lu_eq hd, hFF t]
    obtain ⟨h1, h2, h3⟩ := nu_bounds hd t
    exact sqrt_rho_aa hβ hγ (lt_of_le_of_lt h3 hT1)
  have hae2 : ∀ᵐ t ∂d.μ, t ∈ Icc d.lo d.hi ∧ t = lam * hf β γ (Fn ν t) := by
    filter_upwards [hae, ae_supp hd] with t ht1 ht2
    exact ⟨ht2, by rw [← hrho t]; exact ht1⟩
  have hFnT : ∀ t, 0 ≤ Fn ν t ∧ Fn ν t ≤ ls := fun t => by
    obtain ⟨h1, h2, h3⟩ := nu_bounds hd t
    exact ⟨h1.trans h2, hT ▸ h3⟩
  have hfmono : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y → y ≤ ls → hf β γ x ≤ hf β γ y := by
    intro x y hx hxy hy
    exact (hf_strictMonoOn hβ hγ).monotoneOn (show x < 1 by linarith [hls.2]) (show y < 1 by linarith [hls.2]) hxy
  -- lam value via GL for H2
  have hlamv : lam = (H2 β γ ls - H2 β γ 0) / P.Λ := by
    have hpos_ae : ∀ᵐ t ∂d.μ, 0 < t := by
      filter_upwards [hae2] with t ht
      rw [ht.2]; exact mul_pos hlampos (hf_pos hβ hγ _)
    have hΛ0' : d.Λk 0 = ∫ t, (1 / t) ∂ν := by
      rw [integral_nu hd, Lk0_eq, show d.μ.real univ = ∫ t, (1:ℝ) ∂d.μ by simp]
      apply integral_congr_ae
      filter_upwards [hpos_ae] with t ht
      field_simp
    have hae_nu : ∀ᵐ t ∂ν, 1 / t = 1 / lam * (1 / hf β γ (Fn ν t)) := by
      have := (withDensity_absolutelyContinuous d.μ (fun t => ENNReal.ofReal t)).ae_le hae2
      filter_upwards [this] with t ht
      rw [one_div_mul_one_div, ← ht.2]
    have hg : Measurable (fun t => 1 / hf β γ (Fn ν t)) := by
      have := Fn_measurable ν
      unfold hf; fun_prop
    have hGL := glthm (hd.2.1.trans hd.2.2.1) (nu_Iio0 hd) (nu_Ioi_hi hd) (H2 β γ) (fun x => 1 / hf β γ x)
      (fun x hx => by rw [T_nu hd] at hx; exact hasDerivAt_H2 hβ hγ (lt_of_le_of_lt hx.2 hT1))
      (by
        apply ContinuousOn.div continuousOn_const ((hf_continuousOn hβ hγ).mono _)
        · intro x _; exact (hf_pos hβ hγ x).ne'
        · intro x hx; rw [T_nu hd] at hx; exact lt_of_le_of_lt hx.2 hT1)
      (fun t => 1 / hf β γ (Fn ν t)) hg (1 / Real.sqrt β)
      (fun t => by
        have hp := hf_pos hβ hγ (Fn ν t)
        rw [abs_of_pos (one_div_pos.2 hp)]
        apply one_div_le_one_div_of_le (Real.sqrt_pos.2 hβ)
        unfold hf
        apply Real.sqrt_le_sqrt
        have : 0 ≤ γ / (1 - Fn ν t) ^ 2 := by positivity
        linarith)
      (fun t ht => by
        exfalso
        rw [measureReal_def, hatomless t] at ht
        simp at ht)
      (fun t _ => rfl)
    rw [T_nu hd, hT] at hGL
    have : d.Λk 0 = 1 / lam * (H2 β γ ls - H2 β γ 0) := by
      rw [hΛ0', integral_congr_ae hae_nu, integral_const_mul, hGL]
    rw [hΛ0eq] at this
    field_simp at this ⊢
    linarith
  refine ⟨hΛ0eq, ?_, ?_, ?_⟩
  · -- Λ2
    rw [← hlamv]
    have : d.Λk 2 = ∫ t, lam * (t * Real.sqrt (rhod P d t)) ∂d.μ := by
      unfold Design.Λk
      apply integral_congr_ae
      filter_upwards [hae] with t ht
      rw [show lam * (t * Real.sqrt (rhod P d t)) = t * (lam * Real.sqrt (rhod P d t)) by ring, ← ht, sq]
    rw [this, integral_const_mul]
    unfold Md at hM
    rw [hM]
  · -- lo
    rw [← hlamv]
    have hFlo : Fn ν d.lo = 0 := by
      have e := Fn_sub_Fm ν d.lo
      rw [measureReal_def, hatomless, ENNReal.toReal_zero] at e
      have : Fm ν d.lo = 0 := by
        unfold Fm; rw [measureReal_def, nu_Iio_lo hd, ENNReal.toReal_zero]
      linarith
    apply le_antisymm
    · by_contra hc
      push Not at hc
      have hca : ContinuousAt (hf β γ) 0 :=
        (hf_continuousOn hβ hγ).continuousAt (Iio_mem_nhds (by norm_num))
      obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hca ((d.lo - lam * hf β γ 0) / lam)
        (div_pos (by linarith) hlampos)
      obtain ⟨y, hy, hFy⟩ := Fn_rc' ν d.lo hδ
      rw [hFlo, zero_add] at hFy
      have hpos := hd.2.2.2.2.1 (y - d.lo) (by linarith)
      rw [add_sub_cancel] at hpos
      obtain ⟨t, ht, hPt⟩ := exists_of_pos hpos hae2
      obtain ⟨h1, h2⟩ := hFnT t
      have hFt : Fn ν t < δ := lt_of_le_of_lt (Fn_mono ν ht.2.le) hFy
      have := hδ' (x := Fn ν t) (by rw [Real.dist_eq, sub_zero, abs_of_nonneg h1]; exact hFt)
      rw [Real.dist_eq] at this
      have h3 := (abs_lt.1 this).2
      have h4 : lam * hf β γ (Fn ν t) < d.lo := by
        have := mul_lt_mul_of_pos_left h3 hlampos
        rw [mul_sub, mul_div_cancel₀ _ hlampos.ne'] at this
        linarith
      linarith [hPt.2, ht.1]
    · by_contra hc
      push Not at hc
      have hpos := hd.2.2.2.2.1 (lam * hf β γ 0 - d.lo) (by linarith)
      obtain ⟨t, ht, hPt⟩ := exists_of_pos hpos hae2
      obtain ⟨h1, h2⟩ := hFnT t
      have := hfmono le_rfl h1 h2
      have := mul_le_mul_of_nonneg_left this hlampos.le
      linarith [hPt.2, ht.2]
  · -- hi
    rw [← hlamv]
    have hFhi : Fm ν d.hi = ls := by
      have e := Fn_sub_Fm ν d.hi
      rw [measureReal_def, hatomless, ENNReal.toReal_zero] at e
      have : Fn ν d.hi = ls := by rw [Fn_K (nu_Ioi_hi hd), T_nu hd, hT]
      linarith
    apply le_antisymm
    · by_contra hc
      push Not at hc
      have hpos := hd.2.2.2.2.2.1 (d.hi - lam * hf β γ ls) (by linarith)
      obtain ⟨t, ht, hPt⟩ := exists_of_pos hpos hae2
      obtain ⟨h1, h2⟩ := hFnT t
      have := hfmono h1 h2 le_rfl
      have := mul_le_mul_of_nonneg_left this hlampos.le
      linarith [hPt.2, ht.1]
    · by_contra hc
      push Not at hc
      have hca : ContinuousAt (hf β γ) ls :=
        (hf_continuousOn hβ hγ).continuousAt (Iio_mem_nhds hls.2)
      obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hca ((lam * hf β γ ls - d.hi) / lam)
        (div_pos (by linarith) hlampos)
      obtain ⟨y, hy, hFy⟩ := Fm_lc' ν d.hi hδ
      rw [hFhi] at hFy
      have hpos := hd.2.2.2.2.2.1 (d.hi - y) (by linarith)
      rw [sub_sub_cancel] at hpos
      obtain ⟨t, ht, hPt⟩ := exists_of_pos hpos hae2
      obtain ⟨h1, h2⟩ := hFnT t
      have hFt : ls - δ < Fn ν t := lt_of_lt_of_le hFy (Fn_mono ν ht.1.le)
      have := hδ' (x := Fn ν t) (by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      rw [Real.dist_eq] at this
      have h3 := (abs_lt.1 this).1
      have h4 : d.hi < lam * hf β γ (Fn ν t) := by
        have := mul_lt_mul_of_pos_left h3 hlampos
        rw [mul_neg, mul_div_cancel₀ _ hlampos.ne', mul_sub] at this
        linarith
      linarith [hPt.2, ht.2]

end Main
end DslA7


open MeasureTheory Set Filter Topology

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace DslA7
open DiscServLine.SPT

section Cons
variable {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) {lam ls : ℝ} (hlam : 0 < lam) (hls : ls ∈ Ioo (0:ℝ) 1)

noncomputable def Tf (β γ lam : ℝ) (s : ℝ) : ℝ := lam * hf β γ s
noncomputable def nu0 (β γ lam ls : ℝ) : Measure ℝ :=
  (volume.restrict (Icc 0 ls)).withDensity (fun s => ENNReal.ofReal (1 / Tf β γ lam s))
noncomputable def dstar (β γ lam ls : ℝ) : Design where
  lo := Tf β γ lam 0
  hi := Tf β γ lam ls
  μ := (nu0 β γ lam ls).map (Tf β γ lam)

include hβ hγ hlam

lemma Tf_pos (s : ℝ) : 0 < Tf β γ lam s := mul_pos hlam (hf_pos hβ hγ s)

lemma hf_ge_sqrt (s : ℝ) : Real.sqrt β ≤ hf β γ s := by
  unfold hf; apply Real.sqrt_le_sqrt; have : 0 ≤ γ / (1 - s) ^ 2 := by positivity
  linarith

lemma Tf_meas : Measurable (Tf β γ lam) := by unfold Tf hf; fun_prop

lemma Tf_strictMonoOn : StrictMonoOn (Tf β γ lam) (Iio 1) := fun x hx y hy hxy =>
  mul_lt_mul_of_pos_left (hf_strictMonoOn hβ hγ hx hy hxy) hlam

lemma Tf_continuousOn : ContinuousOn (Tf β γ lam) (Iio 1) :=
  continuousOn_const.mul (hf_continuousOn hβ hγ)

lemma nu0_finite : IsFiniteMeasure (nu0 β γ lam ls) := by
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  calc ∫⁻ s, ENNReal.ofReal (1 / Tf β γ lam s) ∂(volume.restrict (Icc 0 ls))
      ≤ ∫⁻ s, ENNReal.ofReal (1 / (lam * Real.sqrt β)) ∂(volume.restrict (Icc 0 ls)) := by
        apply lintegral_mono
        intro s
        apply ENNReal.ofReal_le_ofReal
        apply one_div_le_one_div_of_le (mul_pos hlam (Real.sqrt_pos.2 hβ))
        exact mul_le_mul_of_nonneg_left (hf_ge_sqrt hβ hγ hlam s) hlam.le
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)

lemma mustar_finite : IsFiniteMeasure (dstar β γ lam ls).μ := by
  haveI := nu0_finite hβ hγ hlam (ls := ls)
  unfold dstar; infer_instance

lemma integral_mustar {φ : ℝ → ℝ} (hφ : Measurable φ) :
    ∫ t, φ t ∂(dstar β γ lam ls).μ = ∫ s in Icc 0 ls, φ (Tf β γ lam s) / Tf β γ lam s := by
  unfold dstar
  simp only
  rw [integral_map (Tf_meas hβ hγ hlam).aemeasurable hφ.aestronglyMeasurable]
  have : nu0 β γ lam ls = (volume.restrict (Icc 0 ls)).withDensity
      (fun s => ((Real.toNNReal (1 / Tf β γ lam s) : NNReal) : ENNReal)) := rfl
  rw [this, integral_withDensity_eq_integral_smul (by
    have := Tf_meas hβ hγ hlam; fun_prop)]
  congr 1; funext s
  rw [NNReal.smul_def, Real.coe_toNNReal _ (one_div_pos.2 (Tf_pos hβ hγ hlam s)).le, smul_eq_mul]
  ring

lemma Tf_le_iff {s s0 : ℝ} (hs : s < 1) (hs0 : s0 < 1) : Tf β γ lam s ≤ Tf β γ lam s0 ↔ s ≤ s0 :=
  (Tf_strictMonoOn hβ hγ hlam).le_iff_le hs hs0

lemma Tf_lt_iff {s s0 : ℝ} (hs : s < 1) (hs0 : s0 < 1) : Tf β γ lam s < Tf β γ lam s0 ↔ s < s0 :=
  (Tf_strictMonoOn hβ hγ hlam).lt_iff_lt hs hs0

lemma loadUpTo_star (hls : ls ∈ Ioo (0:ℝ) 1) {s0 : ℝ} (hs0 : s0 ∈ Icc 0 ls) :
    (dstar β γ lam ls).loadUpTo (Tf β γ lam s0) = s0 := by
  unfold Design.loadUpTo
  rw [← integral_indicator measurableSet_Iic, integral_mustar hβ hγ hlam
    (φ := (Iic (Tf β γ lam s0)).indicator (fun τ => τ)) ((measurable_id.indicator measurableSet_Iic))]
  rw [setIntegral_congr_fun measurableSet_Icc (g := fun s => (Iic s0).indicator 1 s)]
  · rw [integral_indicator_one measurableSet_Iic, measureReal_restrict_apply measurableSet_Iic,
      show Iic s0 ∩ Icc 0 ls = Icc 0 s0 from by
        ext x; exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.trans hs0.2⟩⟩,
      Real.volume_real_Icc_of_le hs0.1, sub_zero]
  · intro s hs
    have hs1 : s < 1 := lt_of_le_of_lt hs.2 hls.2
    have hs01 : s0 < 1 := lt_of_le_of_lt hs0.2 hls.2
    have hp := Tf_pos hβ hγ hlam s
    by_cases h : s ≤ s0
    · simp only [indicator, mem_Iic, (Tf_le_iff hβ hγ hlam hs1 hs01).2 h, if_true, h, id, Pi.one_apply]
      field_simp
    · simp only [indicator, mem_Iic, h, if_false, Pi.one_apply]
      rw [if_neg (by rw [Tf_le_iff hβ hγ hlam hs1 hs01]; exact h)]; simp

lemma loadBelow_star (hls : ls ∈ Ioo (0:ℝ) 1) {s0 : ℝ} (hs0 : s0 ∈ Icc 0 ls) :
    (dstar β γ lam ls).loadBelow (Tf β γ lam s0) = s0 := by
  unfold Design.loadBelow
  rw [← integral_indicator measurableSet_Iio, integral_mustar hβ hγ hlam
    (φ := (Iio (Tf β γ lam s0)).indicator (fun τ => τ)) ((measurable_id.indicator measurableSet_Iio))]
  rw [setIntegral_congr_fun measurableSet_Icc (g := fun s => (Iio s0).indicator 1 s)]
  · rw [integral_indicator_one measurableSet_Iio, measureReal_restrict_apply measurableSet_Iio,
      show Iio s0 ∩ Icc 0 ls = Ico 0 s0 from by
        ext x; exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.le.trans hs0.2⟩⟩,
      Real.volume_real_Ico_of_le hs0.1, sub_zero]
  · intro s hs
    have hs1 : s < 1 := lt_of_le_of_lt hs.2 hls.2
    have hs01 : s0 < 1 := lt_of_le_of_lt hs0.2 hls.2
    have hp := Tf_pos hβ hγ hlam s
    by_cases h : s < s0
    · simp only [indicator, mem_Iio, (Tf_lt_iff hβ hγ hlam hs1 hs01).2 h, if_true, h, id, Pi.one_apply]
      field_simp
    · simp only [indicator, mem_Iio, h, if_false, Pi.one_apply]
      rw [if_neg (by rw [Tf_lt_iff hβ hγ hlam hs1 hs01]; exact h)]; simp

lemma Lk_star (k : ℕ) : (dstar β γ lam ls).Λk k = ∫ s in Icc 0 ls, Tf β γ lam s ^ k / Tf β γ lam s := by
  unfold Design.Λk
  exact integral_mustar hβ hγ hlam (φ := fun t => t ^ k) (measurable_id.pow_const k)

lemma setI_eq (hls : ls ∈ Ioo (0:ℝ) 1) (f : ℝ → ℝ) :
    ∫ s in Icc 0 ls, f s = ∫ s in (0:ℝ)..ls, f s := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hls.1.le]

lemma Lk0_star (hls : ls ∈ Ioo (0:ℝ) 1) :
    (dstar β γ lam ls).Λk 0 = 1 / lam * (H2 β γ ls - H2 β γ 0) := by
  rw [Lk_star hβ hγ hlam, setI_eq hβ hγ hlam hls]
  have e : (fun s => Tf β γ lam s ^ 0 / Tf β γ lam s) = fun s => 1 / lam * (1 / hf β γ s) := by
    funext s; unfold Tf; have := hf_pos hβ hγ s; field_simp
  rw [e, intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx; rw [uIcc_of_le hls.1.le] at hx; exact hasDerivAt_H2 hβ hγ (lt_of_le_of_lt hx.2 hls.2)
  · apply ContinuousOn.intervalIntegrable_of_Icc hls.1.le
    apply ContinuousOn.div continuousOn_const ((hf_continuousOn hβ hγ).mono _)
    · intro x _; exact (hf_pos hβ hγ x).ne'
    · intro x hx; exact lt_of_le_of_lt hx.2 hls.2

lemma Lk1_star (hls : ls ∈ Ioo (0:ℝ) 1) : (dstar β γ lam ls).Λk 1 = ls := by
  rw [Lk_star hβ hγ hlam]
  have e : (fun s => Tf β γ lam s ^ 1 / Tf β γ lam s) = fun s => (1:ℝ) := by
    funext s; have := Tf_pos hβ hγ hlam s; field_simp
  rw [e, setIntegral_const, Real.volume_real_Icc_of_le hls.1.le]; simp

lemma Lk2_star (hls : ls ∈ Ioo (0:ℝ) 1) :
    (dstar β γ lam ls).Λk 2 = lam * (Hs β γ ls - Hs β γ 0) := by
  rw [Lk_star hβ hγ hlam, setI_eq hβ hγ hlam hls]
  have e : (fun s => Tf β γ lam s ^ 2 / Tf β γ lam s) = fun s => lam * hf β γ s := by
    funext s; have := Tf_pos hβ hγ hlam s; unfold Tf at this ⊢; field_simp
  rw [e, intervalIntegral.integral_const_mul, integral_hf hβ hγ hls.1.le hls.2]

lemma admissible_star (hls : ls ∈ Ioo (0:ℝ) 1) : Admissible (dstar β γ lam ls) := by
  have hls0 : (0:ℝ) < 1 := by norm_num
  have hl1 : ls < 1 := hls.2
  have hfm : AEMeasurable (fun s => ENNReal.ofReal (1 / Tf β γ lam s)) (volume.restrict (Icc 0 ls)) := by
    have := Tf_meas hβ hγ hlam; exact (by fun_prop : Measurable _).aemeasurable
  have hne : ∀ A : Set ℝ, (volume.restrict (Icc 0 ls)) A ≠ 0 → nu0 β γ lam ls A ≠ 0 := by
    intro A hA h
    rw [nu0, withDensity_apply_eq_zero' hfm] at h
    apply hA
    refine measure_mono_null ?_ h
    intro x hx
    refine ⟨?_, hx⟩
    simp only [mem_setOf_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact one_div_pos.2 (Tf_pos hβ hγ hlam x)
  refine ⟨mustar_finite hβ hγ hlam, (Tf_pos hβ hγ hlam 0).le,
    (Tf_le_iff hβ hγ hlam hls0 hl1).2 hls.1.le, ?_, ?_, ?_, ?_⟩
  · show ((nu0 β γ lam ls).map (Tf β γ lam)) (Icc (Tf β γ lam 0) (Tf β γ lam ls))ᶜ = 0
    rw [Measure.map_apply (Tf_meas hβ hγ hlam) measurableSet_Icc.compl]
    apply withDensity_absolutelyContinuous
    rw [Measure.restrict_apply ((Tf_meas hβ hγ hlam) measurableSet_Icc.compl)]
    apply measure_mono_null _ measure_empty
    rintro s ⟨hs1, hs2⟩
    exfalso; apply hs1
    have hs1' : s < 1 := lt_of_le_of_lt hs2.2 hl1
    exact ⟨(Tf_le_iff hβ hγ hlam hls0 hs1').2 hs2.1, (Tf_le_iff hβ hγ hlam hs1' hl1).2 hs2.2⟩
  · intro ε hε
    show 0 < ((nu0 β γ lam ls).map (Tf β γ lam)) (Ico (Tf β γ lam 0) (Tf β γ lam 0 + ε))
    rw [Measure.map_apply (Tf_meas hβ hγ hlam) measurableSet_Ico]
    apply pos_iff_ne_zero.2; apply hne
    have hca : ContinuousAt (Tf β γ lam) 0 :=
      (Tf_continuousOn hβ hγ hlam).continuousAt (Iio_mem_nhds hls0)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hca ε hε
    set δ1 := min (δ / 2) ls
    have hδ1 : 0 < δ1 := lt_min (by linarith) hls.1
    rw [Measure.restrict_apply ((Tf_meas hβ hγ hlam) measurableSet_Ico)]
    apply ne_of_gt
    calc (0:ENNReal) < volume (Icc 0 δ1) := by simp [hδ1]
      _ ≤ _ := by
        apply measure_mono
        intro s hs
        have hsl : s ≤ ls := hs.2.trans (min_le_right _ _)
        have hs1' : s < 1 := lt_of_le_of_lt hsl hl1
        refine ⟨⟨(Tf_le_iff hβ hγ hlam hls0 hs1').2 hs.1, ?_⟩, hs.1, hsl⟩
        have := hδ' (x := s) (by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
          exact lt_of_le_of_lt (hs.2.trans (min_le_left _ _)) (by linarith))
        rw [Real.dist_eq] at this
        linarith [(abs_lt.1 this).2]
  · intro ε hε
    show 0 < ((nu0 β γ lam ls).map (Tf β γ lam)) (Ioc (Tf β γ lam ls - ε) (Tf β γ lam ls))
    rw [Measure.map_apply (Tf_meas hβ hγ hlam) measurableSet_Ioc]
    apply pos_iff_ne_zero.2; apply hne
    have hca : ContinuousAt (Tf β γ lam) ls :=
      (Tf_continuousOn hβ hγ hlam).continuousAt (Iio_mem_nhds hl1)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hca ε hε
    set δ1 := min (δ / 2) ls
    have hδ1 : 0 < δ1 := lt_min (by linarith) hls.1
    rw [Measure.restrict_apply ((Tf_meas hβ hγ hlam) measurableSet_Ioc)]
    apply ne_of_gt
    calc (0:ENNReal) < volume (Icc (ls - δ1) ls) := by simp; linarith
      _ ≤ _ := by
        apply measure_mono
        intro s hs
        have hs0 : 0 ≤ s := by linarith [hs.1, min_le_right (δ / 2) ls]
        have hs1' : s < 1 := lt_of_le_of_lt hs.2 hl1
        refine ⟨⟨?_, (Tf_le_iff hβ hγ hlam hs1' hl1).2 hs.2⟩, hs0, hs.2⟩
        have := hδ' (x := s) (by
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith [hs.1, hs.2, min_le_left (δ / 2) ls])
        rw [Real.dist_eq] at this
        linarith [(abs_lt.1 this).1]
  · rw [Lk1_star hβ hγ hlam hls]; exact hl1

end Cons

lemma profit_star (P : Params) (hP : P.Standing) {lam ls : ℝ} (hlam : 0 < lam) (hls : ls ∈ Ioo (0:ℝ) 1)
    (hΛ0 : (dstar (bt P) (gm P) lam ls).Λk 0 = P.Λ) :
    profit P (dstar (bt P) (gm P) lam ls) = (P.θbar - P.c) * ls - Sf P ls ^ 2 := by
  have hβ := bt_pos hP
  have hγ := gm_pos hP
  set β := bt P
  set γ := gm P
  set d := dstar β γ lam ls with hd
  have had := admissible_star hβ hγ hlam hls
  have hl1 : ls < 1 := hls.2
  have hTc : ContinuousOn (Tf β γ lam) (Icc 0 ls) :=
    (Tf_continuousOn hβ hγ hlam).mono (fun x hx => lt_of_le_of_lt hx.2 hl1)
  have hc1 : ContinuousOn (fun s => 1 / Tf β γ lam s) (Icc 0 ls) :=
    continuousOn_const.div hTc (fun s _ => (Tf_pos hβ hγ hlam s).ne')
  have hc2 : ContinuousOn (fun s => 1 / ((1 - s) * (1 - s)) / Tf β γ lam s) (Icc 0 ls) := by
    apply ContinuousOn.div _ hTc (fun s _ => (Tf_pos hβ hγ hlam s).ne')
    apply continuousOn_const.div (by fun_prop)
    intro s hs; have : 0 < 1 - s := by linarith [hs.2]
    positivity
  have hi1 : IntegrableOn (fun s => 1 / Tf β γ lam s) (Icc 0 ls) volume := hc1.integrableOn_Icc
  have hi2 : IntegrableOn (fun s => 1 / ((1 - s) * (1 - s)) / Tf β γ lam s) (Icc 0 ls) volume :=
    hc2.integrableOn_Icc
  set K := ∫ s in Icc 0 ls, 1 / ((1 - s) * (1 - s)) / Tf β γ lam s
  have hW : Measurable d.W := by
    have := lb_meas had; have := lu_meas had
    unfold Design.W; fun_prop
  have hQ : d.Q = d.Λk 2 / 2 * K := by
    unfold Design.Q
    rw [integral_mustar hβ hγ hlam hW, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    simp only
    unfold Design.W
    rw [loadBelow_star hβ hγ hlam hls hs, loadUpTo_star hβ hγ hlam hls hs]
    field_simp
  have hL0 : ∫ s in Icc 0 ls, 1 / Tf β γ lam s = d.Λk 0 := by
    rw [Lk_star hβ hγ hlam]; congr 1
  have hcomb : β * d.Λk 0 + γ * K = (Hs β γ ls - Hs β γ 0) / lam := by
    rw [← hL0, ← integral_const_mul, ← integral_const_mul, ← integral_add (hi1.const_mul _) (hi2.const_mul _)]
    have e : ∀ s ∈ Icc 0 ls, β * (1 / Tf β γ lam s) + γ * (1 / ((1 - s) * (1 - s)) / Tf β γ lam s)
        = 1 / lam * hf β γ s := by
      intro s hs
      have h1s : 0 < 1 - s := by linarith [hs.2]
      have hsq := hf_sq hβ hγ s
      have hp := hf_pos hβ hγ s
      unfold Tf
      field_simp
      rw [hsq]
      field_simp
    rw [setIntegral_congr_fun measurableSet_Icc e, integral_const_mul, setI_eq hβ hγ hlam hls,
      integral_hf hβ hγ hls.1.le hl1]
    ring
  have hb : P.b = β * P.Λ := by
    simp only [β, bt]; field_simp [hP.2.2.2.ne']
  rw [profit, hQ, Lk1_star hβ hγ hlam hls]
  have hL2 := Lk2_star hβ hγ hlam hls
  rw [hΛ0] at hcomb
  have hγc : γ = P.c / 2 := rfl
  have : P.b * d.Λk 2 + P.c * (d.Λk 2 / 2 * K) = d.Λk 2 * (β * P.Λ + γ * K) := by
    rw [hb, hγc]; ring
  have h2 : P.θbar * ls - P.b * d.Λk 2 - P.c * (ls + d.Λk 2 / 2 * K) =
      (P.θbar - P.c) * ls - d.Λk 2 * (β * P.Λ + γ * K) := by linarith
  rw [h2, hcomb, hL2]
  unfold Sf
  field_simp
  rfl

lemma H2_diff_pos {β γ ls : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hls : ls ∈ Ioo (0:ℝ) 1) :
    0 < H2 β γ ls - H2 β γ 0 := by
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (H2 β γ) (fun x => 1 / hf β γ x) hls.1
    (fun x hx => (hasDerivAt_H2 hβ hγ (lt_of_le_of_lt hx.2 hls.2)).continuousAt.continuousWithinAt)
    (fun x hx => hasDerivAt_H2 hβ hγ (lt_trans hx.2 hls.2))
  have := one_div_pos.2 (hf_pos hβ hγ c)
  rw [hc', sub_zero] at this
  exact (div_pos_iff_of_pos_right hls.1).1 this

end DslA7

namespace DiscServLine.SPT
open DslA7

theorem lemma_A7 (P : Params) (hP : P.Standing) :
    (∃ d, IsOptimal P d) ∧
      ∀ d, IsOptimal P d → ∃ ω ∈ Set.Ioo (0 : ℝ) 1, F35 P ω = 0 ∧
        d.Λk 0 = P.Λ ∧ d.Λk 1 = 1 - Real.sqrt ω ∧ d.Λk 2 = Λ2A7 P ω ∧
        d.lo = tLoA7 P ω ∧ d.hi = tHiA7 P ω := by
  have hβ := bt_pos hP
  have hγ := gm_pos hP
  have hD : 0 < P.θbar - P.c := sub_pos.2 hP.2.1
  obtain ⟨ls, hls, hphi⟩ := exists_lstar hβ hγ hD
  set lam := (H2 (bt P) (gm P) ls - H2 (bt P) (gm P) 0) / P.Λ with hlamdef
  have hlam : 0 < lam := div_pos (H2_diff_pos hβ hγ hls) hP.2.2.2
  have hΛ0 : (dstar (bt P) (gm P) lam ls).Λk 0 = P.Λ := by
    rw [Lk0_star hβ hγ hlam hls, hlamdef]
    have := (H2_diff_pos hβ hγ hls).ne'
    field_simp
  have hfeas : Feasible P (dstar (bt P) (gm P) lam ls) := ⟨admissible_star hβ hγ hlam hls, hΛ0.le⟩
  have hprof := profit_star P hP hlam hls hΛ0
  have hgmax : ∀ d, Feasible P d → profit P d ≤ (P.θbar - P.c) * ls - Sf P ls ^ 2 := by
    intro d hd
    exact (bound hP hd).trans (g_le hβ hγ hls hphi (T_nonneg hd.1) (T_lt hd.1))
  refine ⟨⟨_, hfeas, fun d' hd' => (hgmax d' hd').trans_eq hprof.symm⟩, ?_⟩
  rintro d ⟨hdf, hdopt⟩
  have h1 := hdopt _ hfeas
  have h2 := bound hP hdf
  have hT : d.Λk 1 = ls := by
    by_contra hne
    have := g_strict hβ hγ hls hphi (T_nonneg hdf.1) (T_lt hdf.1) hne
    have : (P.θbar - P.c) * d.Λk 1 - Sf P (d.Λk 1) ^ 2 < (P.θbar - P.c) * ls - Sf P ls ^ 2 := this
    linarith
  have heq : profit P d = (P.θbar - P.c) * ls - Sf P ls ^ 2 := by
    rw [hT] at h2; linarith
  obtain ⟨hΛ0d, hΛ2, hlo, hhi⟩ := eqcase hP hdf hls hT heq
  obtain ⟨hω, hF, hsq, hlo', hhi', hΛ2'⟩ := closed_forms P hP hls hphi
  refine ⟨(1 - ls) ^ 2, hω, hF, hΛ0d, by rw [hT, hsq], ?_, ?_, ?_⟩
  · rw [hΛ2, ← hΛ2']; rfl
  · rw [hlo, ← hlo']; rfl
  · rw [hhi, ← hhi']; rfl

end DiscServLine.SPT


-- Platform entry point: restates the target verbatim.
namespace DiscServLine.SPT

theorem _root_.solution (P : Params) (hP : P.Standing) :
    (∃ d, IsOptimal P d) ∧
      ∀ d, IsOptimal P d → ∃ ω ∈ Set.Ioo (0 : ℝ) 1, F35 P ω = 0 ∧
        d.Λk 0 = P.Λ ∧ d.Λk 1 = 1 - Real.sqrt ω ∧ d.Λk 2 = Λ2A7 P ω ∧
        d.lo = tLoA7 P ω ∧ d.hi = tHiA7 P ω := by
  apply @DiscServLine.SPT.lemma_A7 <;> assumption

end DiscServLine.SPT
