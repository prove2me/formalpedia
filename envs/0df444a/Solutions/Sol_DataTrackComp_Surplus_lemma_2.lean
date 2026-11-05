-- Prove2me | solution 1 for DataTrackComp.Surplus.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-11-04T14:10:58.829049+00:00
-- url     : https://prove2.me/submissions/18ae8478-2b5f-498a-a8db-8090d9b7f2c8

import Definitions.Def_DataTrackComp_Surplus_Game
import Definitions.Def_DataTrackComp_Surplus_ReducedGame

/-!
# DataTrackComp.Surplus.lemma_2 (forward-looking setting)

A pair of product-1 prices is a PSNE of the reduced game `G(m)` iff it is supported by a
perfect Bayesian equilibrium of the forward-looking dynamic game.  The key facts are that every
continuation equilibrium after `(pA, pB)` yields exactly the reduced-game profits `piA`, `piB`,
and that such a continuation equilibrium always exists.
-/

open MeasureTheory Set

namespace DataTrackComp.Surplus
namespace DTC

lemma mu0_eq : μ0 = (volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict (Icc (0:ℝ) 1)) := rfl

lemma nu_univ : volume.restrict (Icc (0:ℝ) 1) univ = 1 := by simp

instance mu0_prob : IsProbabilityMeasure μ0 :=
  ⟨by rw [mu0_eq, ← univ_prod_univ, Measure.prod_prod, nu_univ, one_mul]⟩

lemma square_meas : MeasurableSet square := measurableSet_Icc.prod measurableSet_Icc

lemma mu0_restrict : μ0 = (volume : Measure Ty).restrict square := by
  rw [mu0_eq, Measure.prod_restrict, Measure.volume_eq_prod]; rfl

lemma ae_square : ∀ᵐ τ ∂μ0, τ ∈ square := by
  rw [mu0_restrict]; exact ae_restrict_mem square_meas

lemma mu0_compl_square : μ0 squareᶜ = 0 := by
  rw [mu0_restrict, Measure.restrict_apply square_meas.compl]; simp

lemma nu_Iic (c : ℝ) : volume.restrict (Icc (0:ℝ) 1) (Iic c) = ENNReal.ofReal (min c 1) := by
  rw [Measure.restrict_apply measurableSet_Iic]
  have : Iic c ∩ Icc (0:ℝ) 1 = Icc 0 (min c 1) := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]; tauto
  rw [this, Real.volume_Icc, sub_zero]

lemma nu_Ici (t : ℝ) (ht : 0 ≤ t) : volume.restrict (Icc (0:ℝ) 1) (Ici t) = ENNReal.ofReal (1 - t) := by
  rw [Measure.restrict_apply measurableSet_Ici]
  have : Ici t ∩ Icc (0:ℝ) 1 = Icc t 1 := by
    ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]; constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, ht.trans h1, h3⟩
  rw [this, Real.volume_Icc]

lemma nu_Ico_le (t1 t2 : ℝ) : volume.restrict (Icc (0:ℝ) 1) (Ico t1 t2) ≤ ENNReal.ofReal (t2 - t1) := by
  calc volume.restrict (Icc (0:ℝ) 1) (Ico t1 t2) ≤ volume (Ico t1 t2) := Measure.restrict_apply_le _ _
    _ = _ := Real.volume_Ico

lemma nu_Ico (t1 t2 : ℝ) (h1 : 0 ≤ t1) (h2 : t2 ≤ 1) :
    volume.restrict (Icc (0:ℝ) 1) (Ico t1 t2) = ENNReal.ofReal (t2 - t1) := by
  rw [Measure.restrict_apply measurableSet_Ico]
  have : Ico t1 t2 ∩ Icc (0:ℝ) 1 = Ico t1 t2 := by
    apply inter_eq_left.mpr
    intro x hx; exact ⟨h1.trans hx.1, hx.2.le.trans h2⟩
  rw [this, Real.volume_Ico]

lemma mu0_prod (S T : Set ℝ) :
    μ0 (S ×ˢ T) = volume.restrict (Icc (0:ℝ) 1) S * volume.restrict (Icc (0:ℝ) 1) T := by
  rw [mu0_eq, Measure.prod_prod]

lemma mu0_graph_null (g : ℝ → ℝ) (hg : Measurable g) : μ0 {τ : Ty | τ.1 = g τ.2} = 0 := by
  have hm : MeasurableSet {τ : Ty | τ.1 = g τ.2} :=
    measurableSet_eq_fun measurable_fst (hg.comp measurable_snd)
  rw [mu0_eq, Measure.prod_apply_symm hm]
  have : ∀ y : ℝ, volume.restrict (Icc (0:ℝ) 1) ((fun x => (x, y)) ⁻¹' {τ : Ty | τ.1 = g τ.2}) = 0 := by
    intro y
    have : (fun x => (x, y)) ⁻¹' {τ : Ty | τ.1 = g τ.2} = {g y} := by ext x; simp
    rw [this]
    exact le_antisymm ((Measure.restrict_apply_le _ _).trans (by simp)) zero_le
  simp only [this, lintegral_zero]

lemma mu0_null_of_sub (S T : Set Ty) (h : S ∩ square ⊆ T) (hT : μ0 T = 0) : μ0 S = 0 := by
  apply measure_mono_null (t := T ∪ squareᶜ)
  · intro x hx; by_cases hs : x ∈ square
    · exact Or.inl (h ⟨hx, hs⟩)
    · exact Or.inr hs
  · exact measure_union_null hT mu0_compl_square

lemma integrable_of_bdd (f : Ty → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ τ ∈ square, |f τ| ≤ C) :
    Integrable f μ0 := by
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_square] with τ hτ
  simpa [Real.norm_eq_abs] using hC τ hτ

lemma integrable_snd : Integrable (fun τ : Ty => τ.2) μ0 :=
  integrable_of_bdd _ measurable_snd 1 (fun τ hτ => by
    rw [abs_le]; exact ⟨by linarith [hτ.2.1], hτ.2.2⟩)

lemma rev2_meas (m p : ℝ) : Measurable (rev2 m p) := by
  unfold rev2
  exact Measurable.ite (measurableSet_le measurable_const (measurable_const.mul measurable_snd))
    measurable_const measurable_const

lemma integrable_rev2 (m p : ℝ) : Integrable (rev2 m p) μ0 :=
  integrable_of_bdd _ (rev2_meas m p) |p| (fun τ _ => by unfold rev2; split_ifs <;> simp)

lemma rev2_eq_ind (m p : ℝ) : rev2 m p = {τ : Ty | p ≤ m * τ.2}.indicator (fun _ => p) := by
  ext τ; unfold rev2; simp [Set.indicator]

lemma u2_eq (m p : ℝ) (τ : Ty) : u2 m p τ = max (m * τ.2 - p) 0 := by
  unfold u2; split_ifs with h
  · rw [max_eq_left (by linarith)]
  · rw [max_eq_right (by linarith)]


/-! ## The A-set and its θ-tail measures -/

def Aset (m X q : ℝ) : Set Ty := {τ | τ.1 ≤ X + max (m * τ.2 - q) 0}

lemma Aset_meas (m X q : ℝ) : MeasurableSet (Aset m X q) :=
  measurableSet_le measurable_fst (by fun_prop)

noncomputable def Nf (m X q t : ℝ) : ℝ := μ0.real (Aset m X q ∩ {τ | t ≤ τ.2})

def band (m X q t1 t2 : ℝ) : Set Ty := Aset m X q ∩ {τ | t1 ≤ τ.2 ∧ τ.2 < t2}

lemma N_split (m X q t1 t2 : ℝ) (h : t1 ≤ t2) :
    Nf m X q t1 = μ0.real (band m X q t1 t2) + Nf m X q t2 := by
  have hm : MeasurableSet {τ : Ty | τ.2 < t2} := measurableSet_lt measurable_snd measurable_const
  have := measureReal_inter_add_sdiff (μ := μ0) (s := Aset m X q ∩ {τ | t1 ≤ τ.2}) hm
  unfold Nf band; rw [← this]
  congr 2
  · ext τ; simp only [mem_inter_iff, mem_ofPred_eq]; tauto
  · ext τ; simp only [mem_inter_iff, mem_ofPred_eq, mem_sdiff, not_lt]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h.trans h3⟩, h3⟩

lemma band_ge (m X q t1 t2 : ℝ) (hX : 0 < X) (h0 : 0 ≤ t1) (h12 : t1 ≤ t2) (h2 : t2 ≤ 1) :
    min X 1 * (t2 - t1) ≤ μ0.real (band m X q t1 t2) := by
  have hsub : Iic (min X 1) ×ˢ Ico t1 t2 ⊆ band m X q t1 t2 := by
    rintro ⟨s, θ⟩ ⟨hs, hθ⟩
    simp only [mem_Iic, mem_Ico] at hs hθ
    refine ⟨?_, hθ⟩
    show s ≤ X + max (m * θ - q) 0
    have := min_le_left X 1
    have := le_max_right (m * θ - q) 0
    linarith
  have hval : μ0.real (Iic (min X 1) ×ˢ Ico t1 t2) = min X 1 * (t2 - t1) := by
    rw [measureReal_def, mu0_prod, nu_Iic, nu_Ico t1 t2 h0 h2, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by linarith)]
    rw [min_eq_left (min_le_right X 1)]
  rw [← hval]
  exact measureReal_mono hsub

lemma band_le (m X q t1 t2 c : ℝ) (h12 : t1 ≤ t2)
    (hc : ∀ θ, t1 ≤ θ → θ < t2 → X + max (m * θ - q) 0 ≤ c) :
    μ0.real (band m X q t1 t2) ≤ max c 0 * (t2 - t1) := by
  have hsub : band m X q t1 t2 ⊆ Iic c ×ˢ Ico t1 t2 := by
    rintro ⟨s, θ⟩ ⟨hs, hθ1, hθ2⟩
    exact ⟨le_trans hs (hc θ hθ1 hθ2), hθ1, hθ2⟩
  have hle : μ0 (band m X q t1 t2) ≤ ENNReal.ofReal (max c 0 * (t2 - t1)) := by
    calc μ0 (band m X q t1 t2) ≤ μ0 (Iic c ×ˢ Ico t1 t2) := measure_mono hsub
      _ = _ := mu0_prod _ _
      _ ≤ ENNReal.ofReal (max c 0) * ENNReal.ofReal (t2 - t1) := by
          rw [nu_Iic]
          gcongr
          · rcases le_total c 0 with h | h
            · rw [max_eq_right h]; exact (min_le_left _ _).trans h
            · rw [max_eq_left h]; exact min_le_left _ _
          · exact nu_Ico_le t1 t2
      _ = _ := (ENNReal.ofReal_mul (le_max_right _ _)).symm
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (le_max_right _ _) (by linarith)) hle

lemma band_le_len (m X q t1 t2 : ℝ) (h12 : t1 ≤ t2) :
    μ0.real (band m X q t1 t2) ≤ t2 - t1 := by
  have hsub : band m X q t1 t2 ⊆ univ ×ˢ Ico t1 t2 := by
    rintro ⟨s, θ⟩ ⟨_, hθ1, hθ2⟩
    exact ⟨mem_univ _, hθ1, hθ2⟩
  have hle : μ0 (band m X q t1 t2) ≤ ENNReal.ofReal (t2 - t1) := by
    calc μ0 (band m X q t1 t2) ≤ μ0 (univ ×ˢ Ico t1 t2) := measure_mono hsub
      _ = _ := mu0_prod _ _
      _ ≤ 1 * ENNReal.ofReal (t2 - t1) := by rw [nu_univ]; gcongr; exact nu_Ico_le t1 t2
      _ = _ := one_mul _
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (by linarith) hle

lemma Nf_nonneg (m X q t : ℝ) : 0 ≤ Nf m X q t := measureReal_nonneg

lemma Nf_le (m X q t : ℝ) (ht : 0 ≤ t) : Nf m X q t ≤ max (1 - t) 0 := by
  have hsub : Aset m X q ∩ {τ | t ≤ τ.2} ⊆ univ ×ˢ Ici t := by
    rintro ⟨s, θ⟩ ⟨_, hθ⟩; exact ⟨mem_univ _, hθ⟩
  have hle : μ0 (Aset m X q ∩ {τ | t ≤ τ.2}) ≤ ENNReal.ofReal (1 - t) := by
    calc _ ≤ μ0 (univ ×ˢ Ici t) := measure_mono hsub
      _ = _ := by rw [mu0_prod, nu_univ, nu_Ici t ht, one_mul]
  unfold Nf; rw [measureReal_def]
  calc _ ≤ (ENNReal.ofReal (1 - t)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = _ := ENNReal.toReal_ofReal'

lemma Nf_zero (m X q : ℝ) : Nf m X q 0 = μ0.real (Aset m X q) := by
  have hm : MeasurableSet {τ : Ty | 0 ≤ τ.2} := measurableSet_le measurable_const measurable_snd
  have := measureReal_inter_add_sdiff (μ := μ0) (s := Aset m X q) hm
  have h0 : μ0 (Aset m X q \ {τ | 0 ≤ τ.2}) = 0 := by
    apply mu0_null_of_sub _ ∅ _ measure_empty
    rintro τ ⟨⟨_, h⟩, hs⟩; exact absurd hs.2.1 h
  rw [measureReal_def μ0 (Aset m X q \ _), h0, ENNReal.toReal_zero, add_zero] at this
  exact this

noncomputable def Rv (m X q p : ℝ) : ℝ := ∫ τ in Aset m X q, rev2 m p τ ∂μ0

lemma Rv_eq (m X q p : ℝ) (hm : 0 < m) : Rv m X q p = p * Nf m X q (p / m) := by
  unfold Rv Nf
  rw [rev2_eq_ind, setIntegral_indicator (measurableSet_le measurable_const (by fun_prop)),
    setIntegral_const, smul_eq_mul, mul_comm]
  congr 3
  ext τ; simp only [mem_ofPred_eq]; rw [div_le_iff₀ hm, mul_comm]


lemma int_affine (X m t a b : ℝ) :
    ∫ y in a..b, (X + m * (y - t)) = X * (b - a) + m * ((b - t) ^ 2 - (a - t) ^ 2) / 2 := by
  have hd : ∀ y ∈ uIcc a b, HasDerivAt (fun y => X * y + m * ((y - t) * (y - t)) / 2) (X + m * (y - t)) y := by
    intro y _
    have h1 : HasDerivAt (fun y => X * y) X y := by simpa using (hasDerivAt_id y).const_mul X
    have h0 : HasDerivAt (fun y => y - t) 1 y := (hasDerivAt_id y).sub_const t
    have h2 := h0.mul h0
    exact (h1.add ((h2.const_mul m).div_const 2)).congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

lemma int_min (X m t : ℝ) (hm : 0 < m) (hX0 : 0 < X) (hX1 : X < 1) (ht1 : t < 1) :
    ∫ y in t..1, min (X + m * (y - t)) 1 =
      if X + m * (1 - t) ≤ 1 then X * (1 - t) + m * (1 - t) ^ 2 / 2
      else 1 - t - (1 - X) ^ 2 / (2 * m) := by
  split_ifs with hc
  · rw [intervalIntegral.integral_congr (g := fun y => X + m * (y - t))]
    · rw [int_affine]; ring
    · intro y hy
      rw [uIcc_of_le ht1.le] at hy
      simp only
      apply min_eq_left
      nlinarith [hy.2]
  · push Not at hc
    set y0 := t + (1 - X) / m with hy0
    have h1 : t ≤ y0 := by rw [hy0]; have : 0 ≤ (1 - X) / m := div_nonneg (by linarith) hm.le; linarith
    have h2 : y0 ≤ 1 := by
      rw [hy0]; have : (1 - X) / m ≤ 1 - t := by rw [div_le_iff₀ hm]; linarith
      linarith
    have hcont : Continuous (fun y => min (X + m * (y - t)) 1) := by fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := y0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_congr (a := t) (b := y0) (g := fun y => X + m * (y - t)),
      intervalIntegral.integral_congr (a := y0) (b := 1) (g := fun _ => (1:ℝ))]
    · rw [int_affine, intervalIntegral.integral_const, smul_eq_mul, mul_one, hy0]
      field_simp; ring
    · intro y hy
      rw [uIcc_of_le h2] at hy
      simp only
      apply min_eq_right
      have := hy.1; rw [hy0] at this
      have : (1 - X) ≤ m * (y - t) := by
        have h' : (1 - X) / m ≤ y - t := by linarith
        rwa [div_le_iff₀ hm, mul_comm] at h'
      linarith
    · intro y hy
      rw [uIcc_of_le h1] at hy
      simp only
      apply min_eq_left
      have := hy.2; rw [hy0] at this
      have : m * (y - t) ≤ (1 - X) := by
        have h' : y - t ≤ (1 - X) / m := by linarith
        rwa [le_div_iff₀ hm, mul_comm] at h'
      linarith

lemma J_eq (m X t : ℝ) (hm : 0 < m) (hX0 : 0 < X) (hX1 : X < 1) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Nf m X (m * t) t =
      if X + m * (1 - t) ≤ 1 then X * (1 - t) + m * (1 - t) ^ 2 / 2
      else 1 - t - (1 - X) ^ 2 / (2 * m) := by
  rw [← int_min X m t hm hX0 hX1 ht1]
  set g : ℝ → ℝ := fun y => min (X + m * (y - t)) 1 with hg
  have hmeas : MeasurableSet (Aset m X (m * t) ∩ {τ : Ty | t ≤ τ.2}) :=
    (Aset_meas _ _ _).inter (measurableSet_le measurable_const measurable_snd)
  have step1 : μ0 (Aset m X (m * t) ∩ {τ : Ty | t ≤ τ.2}) =
      ∫⁻ y in Icc t 1, ENNReal.ofReal (g y) := by
    rw [mu0_eq, Measure.prod_apply_symm hmeas]
    have hpt : ∀ y : ℝ, volume.restrict (Icc (0:ℝ) 1)
        ((fun x => (x, y)) ⁻¹' (Aset m X (m * t) ∩ {τ : Ty | t ≤ τ.2})) =
        (Ici t).indicator (fun y => ENNReal.ofReal (min (X + max (m * y - m * t) 0) 1)) y := by
      intro y
      by_cases hy : t ≤ y
      · rw [indicator_of_mem (show y ∈ Ici t from hy)]
        have : (fun x => (x, y)) ⁻¹' (Aset m X (m * t) ∩ {τ : Ty | t ≤ τ.2}) =
            Iic (X + max (m * y - m * t) 0) := by
          ext x; simp [Aset, hy]
        rw [this, nu_Iic]
      · rw [indicator_of_notMem (show y ∉ Ici t from hy)]
        have : (fun x => (x, y)) ⁻¹' (Aset m X (m * t) ∩ {τ : Ty | t ≤ τ.2}) = ∅ := by
          ext x; simp [hy]
        rw [this, measure_empty]
    simp_rw [hpt]
    rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have : Ici t ∩ Icc (0:ℝ) 1 = Icc t 1 := by
      ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]; constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, ht0.trans h1, h3⟩
    rw [this]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro y hy
    rw [hg]; simp only
    rw [max_eq_left (by nlinarith [hy.1])]; ring_nf
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hint : IntegrableOn g (Icc t 1) := hgc.integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Icc t 1)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    rw [hg]; simp only; apply le_min _ zero_le_one; nlinarith [hy.1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn] at step1
  unfold Nf; rw [measureReal_def, step1, ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht1.le]


lemma Q_iff (m x : ℝ) (hx : 0 ≤ x) :
    x ≤ xtilde m ↔ 3 * x ^ 2 + 2 * (m - 1) * x - 1 ≤ 0 := by
  unfold xtilde
  set R := Real.sqrt ((m - 1) ^ 2 + 3) with hR
  have hR2 : R ^ 2 = (m - 1) ^ 2 + 3 := Real.sq_sqrt (by positivity)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hpos : 0 < m - 1 + R := by
    by_contra h; push Not at h; nlinarith
  have key : 3 * (3 * x ^ 2 + 2 * (m - 1) * x - 1) = (3 * x + m - 1 - R) * (3 * x + m - 1 + R) := by
    linear_combination hR2
  have hp2 : 0 < 3 * x + m - 1 + R := by linarith
  constructor
  · intro h
    have : 3 * x + m - 1 - R ≤ 0 := by linarith
    nlinarith
  · intro h
    have : 3 * x + m - 1 - R ≤ 0 := by
      by_contra h'; push Not at h'; nlinarith
    linarith

lemma xtilde_pos (m : ℝ) (hm : 0 < m) : 0 < xtilde m := by
  have h := (Q_iff m 0 le_rfl).mpr (by norm_num)
  rcases h.lt_or_eq with h | h
  · exact h
  · exfalso
    unfold xtilde at h
    have hR2 : Real.sqrt ((m - 1) ^ 2 + 3) ^ 2 = (m - 1) ^ 2 + 3 := Real.sq_sqrt (by positivity)
    have : Real.sqrt ((m - 1) ^ 2 + 3) = m - 1 := by linarith
    rw [this] at hR2; nlinarith

lemma xtilde_lt_one (m : ℝ) (hm : 0 < m) : xtilde m < 1 := by
  by_contra h; push Not at h
  have := (Q_iff m 1 zero_le_one).mpr
  have h2 : ¬ (1 ≤ xtilde m) := by
    rw [Q_iff m 1 zero_le_one]; push Not; nlinarith
  exact h2 h

lemma tb0 (m : ℝ) (hm : 0 < m) : thetaBar 0 m = 1 := by
  unfold thetaBar
  rw [if_pos (xtilde_pos m hm).le]
  simp; field_simp

lemma tb1 (m : ℝ) (hm : 0 < m) : thetaBar 1 m = 1 / 2 := by
  unfold thetaBar
  rw [if_neg (not_le.mpr (xtilde_lt_one m hm))]
  norm_num

noncomputable def Jf (X m t : ℝ) : ℝ :=
  if X + m * (1 - t) ≤ 1 then X * (1 - t) + m * (1 - t) ^ 2 / 2
  else 1 - t - (1 - X) ^ 2 / (2 * m)

lemma tb_mem (X m : ℝ) (hm : 0 < m) (hX0 : 0 < X) (hX1 : X < 1) :
    0 < thetaBar X m ∧ thetaBar X m < 1 := by
  unfold thetaBar
  split_ifs with hb
  · set S := Real.sqrt (2 * X * (2 * X + m)) with hS
    have hS2 : S ^ 2 = 2 * X * (2 * X + m) := Real.sq_sqrt (by positivity)
    have hS0 : 0 ≤ S := Real.sqrt_nonneg _
    have h1 : 2 * X < S := by nlinarith
    have h2 : S < 2 * X + m := by nlinarith
    constructor
    · apply mul_pos (by positivity); linarith
    · rw [one_div_mul_eq_div, div_lt_one hm]; linarith
  · push Not at hb
    have hQ : 0 < 3 * X ^ 2 + 2 * (m - 1) * X - 1 := by
      by_contra h; push Not at h; exact absurd ((Q_iff m X hX0.le).mpr h) (not_le.mpr hb)
    have hm2 : (1 - X) ^ 2 < 2 * m := by
      have : X * (1 - X) ^ 2 < X * (2 * m) := by nlinarith [mul_pos (mul_pos hX0 hX0) (by linarith : (0:ℝ) < 1 - X)]
      exact lt_of_mul_lt_mul_left this hX0.le
    have hq : (1 / (2 * m)) * (1 - X) ^ 2 < 1 := by
      rw [one_div_mul_eq_div, div_lt_one (by positivity)]; exact hm2
    constructor
    · apply mul_pos (by positivity); linarith
    · rw [one_div_mul_eq_div, div_lt_one (by positivity)]
      have : 0 ≤ (1 / (2 * m)) * (1 - X) ^ 2 := by positivity
      linarith

lemma J_tb (X m : ℝ) (hm : 0 < m) (hX0 : 0 < X) (hX1 : X < 1) :
    Jf X m (thetaBar X m) = X * thetaBar X m := by
  unfold Jf thetaBar
  split_ifs with hb hc hc
  · set S := Real.sqrt (2 * X * (2 * X + m)) with hS
    have hS2 : S ^ 2 = 2 * X * (2 * X + m) := Real.sq_sqrt (by positivity)
    field_simp
    linear_combination hS2
  · exfalso; apply hc
    set S := Real.sqrt (2 * X * (2 * X + m)) with hS
    have hS2 : S ^ 2 = 2 * X * (2 * X + m) := Real.sq_sqrt (by positivity)
    have hS0 : 0 ≤ S := Real.sqrt_nonneg _
    have hQ := (Q_iff m X hX0.le).mp hb
    have e : X + m * (1 - 1 / m * (2 * X + m - S)) = S - X := by field_simp; ring
    rw [e]; nlinarith
  · exfalso
    have hQ : 0 < 3 * X ^ 2 + 2 * (m - 1) * X - 1 := by
      by_contra h; push Not at h; exact hb ((Q_iff m X hX0.le).mpr h)
    have e : (1 + X) * (X + m * (1 - 1 / (1 + X) * (1 - 1 / (2 * m) * (1 - X) ^ 2)))
        = (2 * m * X + (1 - X) ^ 2) / 2 + X * (1 + X) := by field_simp; ring
    have : 1 + X < (1 + X) * (X + m * (1 - 1 / (1 + X) * (1 - 1 / (2 * m) * (1 - X) ^ 2))) := by
      rw [e]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hc (by linarith : (0:ℝ) ≤ 1 + X)]
  · field_simp; ring

lemma J_uniq (X m t : ℝ) (hm : 0 < m) (hX0 : 0 < X) (hX1 : X < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (h : Jf X m t = X * t) : t = thetaBar X m := by
  unfold Jf at h
  unfold thetaBar
  set S := Real.sqrt (2 * X * (2 * X + m)) with hS
  have hS2 : S ^ 2 = 2 * X * (2 * X + m) := Real.sq_sqrt (by positivity)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  split_ifs at h with hc
  · -- quadratic branch
    have hw : m * (1 - t) + 2 * X = S := by
      have hsq : (m * (1 - t) + 2 * X) ^ 2 = S ^ 2 := by rw [hS2]; linear_combination 2 * m * h
      have h1 : 0 ≤ m * (1 - t) + 2 * X := by nlinarith
      nlinarith [sq_nonneg (m * (1 - t) + 2 * X - S), sq_nonneg (m * (1 - t) + 2 * X + S)]
    have hb : X ≤ xtilde m := by
      rw [Q_iff m X hX0.le]
      have : S ≤ 1 + X := by linarith
      nlinarith
    rw [if_pos hb]
    field_simp; linarith
  · push Not at hc
    have ht : (1 + X) * t = 1 - (1 - X) ^ 2 / (2 * m) := by linarith
    have hb : ¬ X ≤ xtilde m := by
      rw [Q_iff m X hX0.le]; push Not
      have e1 : m * (1 + X) * (1 - t) = m * X + (1 - X) ^ 2 / 2 := by
        have : m * (1 + X) * (1 - t) = m * (1 + X) - m * ((1 + X) * t) := by ring
        rw [this, ht]; field_simp; ring
      have : (1 - X) * (1 + X) < m * (1 + X) * (1 - t) := by
        have : 1 - X < m * (1 - t) := by linarith
        nlinarith
      nlinarith
    rw [if_neg hb]
    rw [show (1:ℝ) - 1 / (2 * m) * (1 - X) ^ 2 = (1 + X) * t by rw [ht]; ring]
    field_simp


lemma Rv_mt (m X q t : ℝ) (hm : 0 < m) : Rv m X q (m * t) = m * t * Nf m X q t := by
  rw [Rv_eq _ _ _ _ hm, mul_div_cancel_left₀ _ hm.ne']

lemma updev (m X t : ℝ) (hm : 0 < m) (ht : 0 ≤ t) (hJ : t * max X 0 < Nf m X (m * t) t) :
    ∃ p, Rv m X (m * t) (m * t) < Rv m X (m * t) p := by
  set c := max X 0 with hc
  set J := Nf m X (m * t) t with hJdef
  have hc0 : 0 ≤ c := le_max_right _ _
  set ε := J - t * c with hε
  have hε0 : 0 < ε := by linarith
  set K := c + m * t + m with hK
  have hK0 : 0 < K := by positivity
  set δ := min 1 (ε / (2 * K)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδK : δ * K ≤ ε / 2 := by
    have : δ ≤ ε / (2 * K) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this; linarith
  refine ⟨m * (t + δ), ?_⟩
  rw [Rv_mt _ _ _ _ hm, Rv_mt _ _ _ _ hm]
  have hsplit := N_split m X (m * t) t (t + δ) (by linarith)
  have hb := band_le m X (m * t) t (t + δ) (X + m * δ) (by linarith) (by
    intro θ h1 h2
    have : max (m * θ - m * t) 0 ≤ m * δ := max_le (by nlinarith) (by positivity)
    linarith)
  have hmx : max (X + m * δ) 0 ≤ c + m * δ := max_le (by rw [hc]; linarith [le_max_left X 0]) (by positivity)
  have hN : J - (c + m * δ) * δ ≤ Nf m X (m * t) (t + δ) := by
    have : max (X + m * δ) 0 * (t + δ - t) ≤ (c + m * δ) * δ := by
      rw [show t + δ - t = δ by ring]; exact mul_le_mul_of_nonneg_right hmx hδ0.le
    linarith
  have key : m * t * J + m * δ * (ε / 2) ≤ m * (t + δ) * Nf m X (m * t) (t + δ) := by
    have h1 : m * (t + δ) * (J - (c + m * δ) * δ) ≤ m * (t + δ) * Nf m X (m * t) (t + δ) :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    have h2 : m * (t + δ) * (J - (c + m * δ) * δ) = m * t * J + m * δ * (ε - δ * (c + m * t + m * δ)) := by
      rw [hε]; ring
    have h3 : δ * (c + m * t + m * δ) ≤ δ * K := by
      apply mul_le_mul_of_nonneg_left _ hδ0.le; rw [hK]; nlinarith
    have h4 : m * δ * (ε / 2) ≤ m * δ * (ε - δ * (c + m * t + m * δ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have : 0 < m * δ * (ε / 2) := by positivity
  linarith

lemma downdev (m X t : ℝ) (hm : 0 < m) (hX0 : 0 < X) (hX1 : X ≤ 1) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hJ : Nf m X (m * t) t < X * t) :
    ∃ p, Rv m X (m * t) (m * t) < Rv m X (m * t) p := by
  set J := Nf m X (m * t) t with hJdef
  set ε := X * t - J with hε
  have hε0 : 0 < ε := by linarith
  set δ := min t (ε / (2 * X)) with hδ
  have hδ0 : 0 < δ := lt_min ht0 (by positivity)
  have hδt : δ ≤ t := min_le_left _ _
  have hδX : X * δ ≤ ε / 2 := by
    have : δ ≤ ε / (2 * X) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this; linarith
  refine ⟨m * (t - δ), ?_⟩
  rw [Rv_mt _ _ _ _ hm, Rv_mt _ _ _ _ hm]
  have hsplit := N_split m X (m * t) (t - δ) t (by linarith)
  have hb := band_ge m X (m * t) (t - δ) t hX0 (by linarith) (by linarith) ht1
  rw [min_eq_left hX1, show t - (t - δ) = δ by ring] at hb
  have hN : J + X * δ ≤ Nf m X (m * t) (t - δ) := by linarith
  have h1 : m * (t - δ) * (J + X * δ) ≤ m * (t - δ) * Nf m X (m * t) (t - δ) :=
    mul_le_mul_of_nonneg_left hN (mul_nonneg hm.le (by linarith))
  have h2 : m * (t - δ) * (J + X * δ) = m * t * J + m * δ * (ε - X * δ) := by rw [hε]; ring
  have h4 : m * δ * (ε / 2) ≤ m * δ * (ε - X * δ) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have : 0 < m * δ * (ε / 2) := by positivity
  linarith

lemma Rv_nonpos (m X q : ℝ) (hm : 0 < m) (hq : q ≤ 0 ∨ m ≤ q) : Rv m X q q ≤ 0 := by
  rw [Rv_eq _ _ _ _ hm]
  rcases hq with hq | hq
  · exact mul_nonpos_of_nonpos_of_nonneg hq (Nf_nonneg _ _ _ _)
  · have h1 : 1 ≤ q / m := by rw [le_div_iff₀ hm]; linarith
    have := Nf_le m X q (q / m) (by linarith)
    rw [max_eq_right (by linarith)] at this
    have h0 : Nf m X q (q / m) = 0 := le_antisymm this (Nf_nonneg _ _ _ _)
    rw [h0, mul_zero]

lemma pos_rev_any (m X q : ℝ) (hm : 0 < m) (hA : 0 < μ0.real (Aset m X q)) :
    ∃ p, 0 < Rv m X q p := by
  set a := μ0.real (Aset m X q)
  refine ⟨m * (a / 2), ?_⟩
  rw [Rv_mt _ _ _ _ hm]
  have h1 := N_split m X q 0 (a / 2) (by positivity)
  have h2 := band_le_len m X q 0 (a / 2) (by positivity)
  rw [Nf_zero] at h1
  have : 0 < Nf m X q (a / 2) := by linarith
  positivity

lemma Areal_pos (m X q : ℝ) (hX : 0 < X) : 0 < μ0.real (Aset m X q) := by
  rw [← Nf_zero]
  have h1 := N_split m X q 0 1 zero_le_one
  have h2 := band_ge m X q 0 1 hX le_rfl zero_le_one le_rfl
  have := Nf_nonneg m X q 1
  have : 0 < min X 1 := lt_min hX one_pos
  linarith

theorem uniq_interior (m X q : ℝ) (hm : 0 < m) (hX0 : 0 < X) (hX1 : X < 1)
    (hopt : ∀ p, Rv m X q p ≤ Rv m X q q) : q = m * thetaBar X m := by
  obtain ⟨p0, hp0⟩ := pos_rev_any m X q hm (Areal_pos m X q hX0)
  have hq : 0 < q ∧ q < m := by
    by_contra h
    have : q ≤ 0 ∨ m ≤ q := by
      by_cases h1 : 0 < q
      · right; by_contra h2; exact h ⟨h1, lt_of_not_ge h2⟩
      · left; linarith
    linarith [Rv_nonpos m X q hm this, hopt p0]
  set t := q / m with htdef
  have hqt : q = m * t := by rw [htdef]; field_simp
  have ht0 : 0 < t := div_pos hq.1 hm
  have ht1 : t < 1 := by rw [htdef, div_lt_one hm]; exact hq.2
  rw [hqt] at hopt ⊢
  have hJ : Nf m X (m * t) t = X * t := by
    rcases lt_trichotomy (Nf m X (m * t) t) (X * t) with h | h | h
    · obtain ⟨p, hp⟩ := downdev m X t hm hX0 hX1.le ht0 ht1.le h
      linarith [hopt p]
    · exact h
    · obtain ⟨p, hp⟩ := updev m X t hm ht0.le (by rw [max_eq_left hX0.le]; linarith)
      linarith [hopt p]
  rw [J_eq m X t hm hX0 hX1 ht0.le ht1] at hJ
  rw [J_uniq X m t hm hX0 hX1 ht0 ht1 hJ]

theorem no_eq_low (m X q : ℝ) (hm : 0 < m) (hX : X ≤ 0) (hA : 0 < μ0.real (Aset m X q))
    (hopt : ∀ p, Rv m X q p ≤ Rv m X q q) : False := by
  obtain ⟨p0, hp0⟩ := pos_rev_any m X q hm hA
  by_cases hq : 0 < q ∧ q < m
  · set t := q / m with htdef
    have hqt : q = m * t := by rw [htdef]; field_simp
    have ht0 : 0 < t := div_pos hq.1 hm
    rw [hqt] at hopt hA
    have h1 := N_split m X (m * t) 0 t ht0.le
    have h2 := band_le m X (m * t) 0 t X ht0.le (by
      intro θ _ h2
      have : max (m * θ - m * t) 0 = 0 := max_eq_right (by nlinarith)
      linarith)
    rw [max_eq_right hX, zero_mul] at h2
    rw [Nf_zero] at h1
    have hb0 := measureReal_nonneg (μ := μ0) (s := band m X (m * t) 0 t)
    obtain ⟨p, hp⟩ := updev m X t hm ht0.le (by rw [max_eq_right hX]; linarith)
    linarith [hopt p]
  · have : q ≤ 0 ∨ m ≤ q := by
      by_cases h1 : 0 < q
      · right; by_contra h2; exact hq ⟨h1, lt_of_not_ge h2⟩
      · left; linarith
    linarith [Rv_nonpos m X q hm this, hopt p0]

lemma top_upper (m X q p : ℝ) (hm : 0 < m) : Rv m X q p ≤ m / 4 := by
  rw [Rv_eq _ _ _ _ hm]
  rcases le_or_gt p 0 with hp | hp
  · nlinarith [Nf_nonneg m X q (p / m)]
  · have h := Nf_le m X q (p / m) (by positivity)
    rcases le_or_gt m p with hpm | hpm
    · have : 1 ≤ p / m := by rw [le_div_iff₀ hm]; linarith
      rw [max_eq_right (by linarith)] at h
      have : Nf m X q (p / m) = 0 := le_antisymm h (Nf_nonneg _ _ _ _)
      rw [this]; linarith
    · have : p / m < 1 := by rw [div_lt_one hm]; exact hpm
      rw [max_eq_left (by linarith)] at h
      calc p * Nf m X q (p / m) ≤ p * (1 - p / m) := mul_le_mul_of_nonneg_left h hp.le
        _ ≤ m / 4 := by
          have e : p * (1 - p / m) = m / 4 - (p - m / 2) ^ 2 / m := by field_simp; ring
          rw [e]; have : 0 ≤ (p - m / 2) ^ 2 / m := by positivity
          linarith

lemma top_lower (m X q : ℝ) (hm : 0 < m) (hX : 1 ≤ X) : m / 4 ≤ Rv m X q (m / 2) := by
  rw [show m / 2 = m * (1 / 2) by ring, Rv_mt _ _ _ _ hm]
  have h1 := N_split m X q (1 / 2) 1 (by norm_num)
  have h2 := band_ge m X q (1 / 2) 1 (by linarith) (by norm_num) (by norm_num) le_rfl
  rw [min_eq_right hX] at h2
  have := Nf_nonneg m X q 1
  nlinarith

theorem top_val (m X q : ℝ) (hm : 0 < m) (hX : 1 ≤ X)
    (hopt : ∀ p, Rv m X q p ≤ Rv m X q q) : Rv m X q q = m / 4 :=
  le_antisymm (top_upper m X q q hm) ((top_lower m X q hm hX).trans (hopt _))

theorem Jtb_val (m X : ℝ) (hm : 0 < m) (hX0 : 0 < X) (hX1 : X < 1) :
    Nf m X (m * thetaBar X m) (thetaBar X m) = X * thetaBar X m := by
  obtain ⟨h0, h1⟩ := tb_mem X m hm hX0 hX1
  rw [J_eq m X _ hm hX0 hX1 h0.le h1]
  exact J_tb X m hm hX0 hX1

theorem exist_interior (m X p : ℝ) (hm : 0 < m) (hX0 : 0 < X) (hX1 : X < 1) :
    Rv m X (m * thetaBar X m) p ≤ Rv m X (m * thetaBar X m) (m * thetaBar X m) := by
  obtain ⟨h0, h1⟩ := tb_mem X m hm hX0 hX1
  set t := thetaBar X m with ht
  have hJ := Jtb_val m X hm hX0 hX1
  rw [← ht] at hJ
  rw [Rv_mt _ _ _ _ hm, hJ, Rv_eq _ _ _ _ hm]
  set θ' := p / m with hθ'
  have hp : p = m * θ' := by rw [hθ']; field_simp
  rw [hp]
  rcases le_or_gt θ' 0 with ha | ha
  · have := Nf_nonneg m X (m * t) θ'
    have : m * θ' * Nf m X (m * t) θ' ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by nlinarith) this
    have : 0 ≤ m * t * (X * t) := by positivity
    linarith
  rcases le_or_gt 1 θ' with hb | hb
  · have h := Nf_le m X (m * t) θ' ha.le
    rw [max_eq_right (by linarith)] at h
    have : Nf m X (m * t) θ' = 0 := le_antisymm h (Nf_nonneg _ _ _ _)
    rw [this, mul_zero]; positivity
  have hN : Nf m X (m * t) θ' ≤ X * (2 * t - θ') := by
    rcases le_total θ' t with hc | hc
    · have h1 := N_split m X (m * t) θ' t hc
      have h2 := band_le m X (m * t) θ' t X hc (by
        intro θ _ h2
        have : max (m * θ - m * t) 0 = 0 := max_eq_right (by nlinarith)
        linarith)
      rw [max_eq_left hX0.le] at h2
      rw [hJ] at h1; nlinarith
    · have h1 := N_split m X (m * t) t θ' hc
      have h2 := band_ge m X (m * t) t θ' hX0 h0.le hc hb.le
      rw [min_eq_left hX1.le] at h2
      rw [hJ] at h1; nlinarith
  calc m * θ' * Nf m X (m * t) θ' ≤ m * θ' * (X * (2 * t - θ')) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
    _ ≤ m * t * (X * t) := by nlinarith [sq_nonneg (t - θ'), mul_pos hm hX0]

theorem Areal_interior (m X : ℝ) (hm : 0 < m) (hX0 : 0 < X) (hX1 : X < 1) :
    μ0.real (Aset m X (m * thetaBar X m)) = 2 * X * thetaBar X m := by
  obtain ⟨h0, h1⟩ := tb_mem X m hm hX0 hX1
  rw [← Nf_zero, N_split m X _ 0 (thetaBar X m) h0.le, Jtb_val m X hm hX0 hX1]
  have h2 := band_le m X (m * thetaBar X m) 0 (thetaBar X m) X h0.le (by
    intro θ _ h2
    have : max (m * θ - m * thetaBar X m) 0 = 0 := max_eq_right (by nlinarith)
    linarith)
  have h3 := band_ge m X (m * thetaBar X m) 0 (thetaBar X m) hX0 le_rfl h0.le h1.le
  rw [max_eq_left hX0.le] at h2
  rw [min_eq_left hX1.le] at h3
  linarith


lemma VA_sub_VB (ubar m a b : ℝ) (c : Cont) (τ : Ty) :
    VA .forward ubar m a c τ - VB .forward ubar m b c τ =
      (b - a + 1 / 2) + max (m * τ.2 - c.pU) 0 - τ.1 - u2 m (c.pT τ) τ := by
  simp only [VA, VB, u1A, u1B, u2_eq m c.pU]; ring

lemma tracked (m : ℝ) (hm : 0 < m) (c : Cont) (hT : TrackedRational .forward m c) :
    ∀ τ ∈ square, rev2 m (c.pT τ) τ = m * τ.2 ∧ u2 m (c.pT τ) τ = 0 := by
  intro τ hτ
  have h := hT τ hτ (m * τ.2)
  have hθ : 0 ≤ m * τ.2 := mul_nonneg hm.le hτ.2.1
  unfold rev2 at h ⊢; unfold u2
  rw [if_pos le_rfl] at h
  split_ifs at h ⊢ with h1
  · constructor <;> linarith
  · constructor <;> linarith

lemma graph_ae (m X q : ℝ) : ∀ᵐ τ ∂μ0, τ.1 ≠ X + max (m * τ.2 - q) 0 := by
  have := mu0_graph_null (fun θ => X + max (m * θ - q) 0) (by fun_prop)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp this] with τ hτ
  exact hτ

lemma gamma_ae (ubar m a b : ℝ) (hm : 0 < m) (c : Cont) (hc : IsContEq .forward ubar m a b c) :
    c.γ1 =ᵐ[μ0] (Aset m (b - a + 1 / 2) c.pU)ᶜ.indicator 1 := by
  obtain ⟨_, _, hγ, hVV, hT, -⟩ := hc
  filter_upwards [ae_square, graph_ae m (b - a + 1 / 2) c.pU] with τ hτ hne
  have hd := VA_sub_VB ubar m a b c τ
  rw [(tracked m hm c hT τ hτ).2, sub_zero] at hd
  rcases lt_or_gt_of_ne hne with h | h
  · have hA : τ ∈ Aset m (b - a + 1 / 2) c.pU := h.le
    rw [indicator_of_notMem (by simpa using hA)]
    by_contra h0
    have hpos : 0 < c.γ1 τ := lt_of_le_of_ne (hγ τ).1 (Ne.symm h0)
    have := (hVV τ hτ).1 hpos
    linarith
  · have hA : τ ∉ Aset m (b - a + 1 / 2) c.pU := not_le.mpr h
    rw [indicator_of_mem (by simpa using hA)]
    by_contra h0
    have hlt : c.γ1 τ < 1 := lt_of_le_of_ne (hγ τ).2 h0
    have := (hVV τ hτ).2 hlt
    simp only [Pi.one_apply] at *
    linarith

lemma one_sub_ind (A : Set Ty) (τ : Ty) : 1 - Aᶜ.indicator 1 τ = A.indicator (1 : Ty → ℝ) τ := by
  by_cases h : τ ∈ A
  · rw [indicator_of_notMem (by simpa using h), indicator_of_mem h]; simp
  · rw [indicator_of_mem (by simpa using h), indicator_of_notMem h]; simp

lemma lint_eq (A : Set Ty) (hA : MeasurableSet A) (γ : Ty → ℝ) (hγ : γ =ᵐ[μ0] Aᶜ.indicator 1) :
    (∫⁻ τ, ENNReal.ofReal (1 - γ τ) ∂μ0) = μ0 A ∧
      μ0.withDensity (fun τ => ENNReal.ofReal (1 - γ τ)) = μ0.restrict A := by
  have hae : (fun τ => ENNReal.ofReal (1 - γ τ)) =ᵐ[μ0] A.indicator 1 := by
    filter_upwards [hγ] with τ hτ
    rw [hτ, one_sub_ind]
    by_cases h : τ ∈ A <;> simp [h]
  constructor
  · rw [lintegral_congr_ae hae, lintegral_indicator_one hA]
  · rw [withDensity_congr_ae hae, withDensity_indicator_one hA]

lemma post_integral (A : Set Ty) (f : Ty → ℝ) :
    ∫ τ, f τ ∂((μ0 A)⁻¹ • μ0.restrict A) = (μ0 A)⁻¹.toReal * ∫ τ in A, f τ ∂μ0 := by
  rw [integral_smul_measure, smul_eq_mul]

lemma inv_pos' (A : Set Ty) (h : μ0 A ≠ 0) : 0 < (μ0 A)⁻¹.toReal :=
  ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (ENNReal.inv_ne_top.mpr h)

lemma opt_of_cont (ubar m a b : ℝ) (hm : 0 < m) (c : Cont) (hc : IsContEq .forward ubar m a b c)
    (hA0 : μ0 (Aset m (b - a + 1 / 2) c.pU) ≠ 0) :
    ∀ p, Rv m (b - a + 1 / 2) c.pU p ≤ Rv m (b - a + 1 / 2) c.pU c.pU := by
  have hg := gamma_ae ubar m a b hm c hc
  obtain ⟨_, _, _, _, _, _, _, hopt, hBC⟩ := hc
  obtain ⟨hZ, hW⟩ := lint_eq _ (Aset_meas _ _ _) _ hg
  have hb : c.belief = (μ0 (Aset m (b - a + 1 / 2) c.pU))⁻¹ • μ0.restrict (Aset m (b - a + 1 / 2) c.pU) := by
    have := hBC (by rw [hZ]; exact hA0)
    rw [this, hZ, hW]
  intro p
  have h := hopt p
  rw [hb, post_integral, post_integral] at h
  exact le_of_mul_le_mul_left h (inv_pos' _ hA0)

lemma profitA_eq (ubar m a b : ℝ) (hm : 0 < m) (c : Cont) (hc : IsContEq .forward ubar m a b c) :
    profitA a c = a * μ0.real (Aset m (b - a + 1 / 2) c.pU) := by
  have hg := gamma_ae ubar m a b hm c hc
  unfold profitA
  congr 1
  rw [← integral_indicator_one (Aset_meas _ _ _)]
  apply integral_congr_ae
  filter_upwards [hg] with τ hτ
  rw [hτ, one_sub_ind]

lemma profitB_eq (ubar m a b : ℝ) (hm : 0 < m) (c : Cont) (hc : IsContEq .forward ubar m a b c) :
    profitB .forward m b c = b * (1 - μ0.real (Aset m (b - a + 1 / 2) c.pU)) +
      m * ∫ τ in (Aset m (b - a + 1 / 2) c.pU)ᶜ, τ.2 ∂μ0 + Rv m (b - a + 1 / 2) c.pU c.pU := by
  have hg := gamma_ae ubar m a b hm c hc
  have hT := hc.2.2.2.2.1
  set A := Aset m (b - a + 1 / 2) c.pU with hAdef
  have hAm : MeasurableSet A := Aset_meas _ _ _
  have hae : (fun τ => c.γ1 τ * (b + rev2 m (c.pT τ) τ) + (1 - c.γ1 τ) * rev2 m c.pU τ) =ᵐ[μ0]
      fun τ => Aᶜ.indicator (fun τ => b + m * τ.2) τ + A.indicator (rev2 m c.pU) τ := by
    filter_upwards [hg, ae_square] with τ hτ hsq
    rw [hτ, one_sub_ind, (tracked m hm c hT τ hsq).1]
    by_cases h : τ ∈ A <;> simp [Set.indicator, h]
  show ∫ τ, (c.γ1 τ * (b + rev2 m (c.pT τ) τ) + (1 - c.γ1 τ) * rev2 m c.pU τ) ∂μ0 = _
  have hi1 : Integrable (fun τ : Ty => b + m * τ.2) μ0 :=
    (integrable_const b).add (integrable_snd.const_mul m)
  rw [integral_congr_ae hae, integral_add (hi1.indicator hAm.compl) ((integrable_rev2 m c.pU).indicator hAm),
    integral_indicator hAm.compl, integral_indicator hAm,
    integral_add (f := fun _ => b) (g := fun τ : Ty => m * τ.2) (integrable_const b).integrableOn
      (integrable_snd.const_mul m).integrableOn,
    setIntegral_const, integral_const_mul, measureReal_compl hAm, probReal_univ, smul_eq_mul]
  unfold Rv; ring


lemma Xbar_low (a b : ℝ) (h : b - a + 1 / 2 ≤ 0) : Xbar a b = 0 := by
  unfold Xbar; exact max_eq_left ((min_le_left _ _).trans h)

lemma Xbar_high (a b : ℝ) (h : 1 ≤ b - a + 1 / 2) : Xbar a b = 1 := by
  unfold Xbar; rw [min_eq_right h]; norm_num

lemma Xbar_mid (a b : ℝ) (h0 : 0 < b - a + 1 / 2) (h1 : b - a + 1 / 2 < 1) :
    Xbar a b = b - a + 1 / 2 := by
  unfold Xbar; rw [min_eq_left h1.le, max_eq_right h0.le]

theorem contProfits (ubar m a b : ℝ) (hm : 0 < m) (c : Cont) (hc : IsContEq .forward ubar m a b c) :
    profitA a c = piA m a b ∧ profitB .forward m b c = piB m a b := by
  rw [profitA_eq ubar m a b hm c hc, profitB_eq ubar m a b hm c hc]
  set X := b - a + 1 / 2 with hX
  set q := c.pU with hq
  set A := Aset m X q with hA
  have hAm : MeasurableSet A := Aset_meas _ _ _
  unfold piA piB phi psi
  rcases le_or_gt X 0 with hX0 | hX0
  · -- nobody buys from A
    have hA0 : μ0 A = 0 := by
      by_contra h
      exact no_eq_low m X q hm hX0 (ENNReal.toReal_pos h (measure_ne_top _ _))
        (opt_of_cont ubar m a b hm c hc h)
    have hAr : μ0.real A = 0 := by rw [measureReal_def, hA0, ENNReal.toReal_zero]
    rw [Xbar_low a b hX0, hAr, tb0 m hm]
    have hR : Rv m X q q = 0 := setIntegral_measure_zero _ hA0
    have hc' : μ0.restrict Aᶜ = μ0 :=
      Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.mp hA0)
    have hxi : xi 0 m = ∫ τ, τ.2 ∂μ0 := by
      unfold xi; rw [tb0 m hm]
      apply integral_congr_ae
      filter_upwards [ae_square] with τ hτ
      rw [if_pos]
      rw [max_eq_right (by linarith [hτ.2.2])]; linarith [hτ.1.1]
    rw [hR, hc', hxi]
    constructor <;> ring
  rcases le_or_gt 1 X with hX1 | hX1
  · -- everybody buys from A
    have hAc : μ0 Aᶜ = 0 := by
      apply mu0_null_of_sub _ ∅ _ measure_empty
      rintro τ ⟨hτ, hsq⟩
      have : ¬ τ.1 ≤ X + max (m * τ.2 - q) 0 := hτ
      have := le_max_right (m * τ.2 - q) 0
      have := hsq.1.2
      exfalso; linarith
    have hAr : μ0.real A = 1 := by
      have := measureReal_compl (μ := μ0) hAm
      rw [probReal_univ, measureReal_def μ0 Aᶜ, hAc, ENNReal.toReal_zero] at this; linarith
    have hA0 : μ0 A ≠ 0 := by
      intro h; rw [measureReal_def, h, ENNReal.toReal_zero] at hAr; norm_num at hAr
    rw [Xbar_high a b hX1, hAr, tb1 m hm, top_val m X q hm hX1 (opt_of_cont ubar m a b hm c hc hA0),
      setIntegral_measure_zero _ hAc]
    have hxi : xi 1 m = 0 := by
      unfold xi
      refine (integral_congr_ae ?_).trans (integral_zero Ty ℝ)
      filter_upwards [ae_square, graph_ae 0 1 0] with τ hτ hne
      rw [if_neg]
      intro h
      simp only [zero_mul, sub_zero, max_self, add_zero] at hne
      have := le_max_right (τ.2 - thetaBar 1 m) 0
      have : 0 ≤ m * max (τ.2 - thetaBar 1 m) 0 := by positivity
      exact hne (le_antisymm hτ.1.2 (by linarith))
    rw [hxi]
    constructor <;> ring
  · -- interior
    have hA0 : μ0 A ≠ 0 := by
      intro h; have := Areal_pos m X q hX0; rw [measureReal_def, h, ENNReal.toReal_zero] at this
      exact lt_irrefl _ this
    have hqv : q = m * thetaBar X m := uniq_interior m X q hm hX0 hX1 (opt_of_cont ubar m a b hm c hc hA0)
    have hAr : μ0.real A = 2 * X * thetaBar X m := by rw [hA, hqv]; exact Areal_interior m X hm hX0 hX1
    have hR : Rv m X q q = m * thetaBar X m * (X * thetaBar X m) := by
      rw [hqv, Rv_mt _ _ _ _ hm, Jtb_val m X hm hX0 hX1]
    have hxi : ∫ τ in Aᶜ, τ.2 ∂μ0 = xi X m := by
      unfold xi
      rw [← integral_indicator hAm.compl]
      apply integral_congr_ae
      filter_upwards [graph_ae m X q] with τ hne
      have e : m * max (τ.2 - thetaBar X m) 0 = max (m * τ.2 - q) 0 := by
        rw [hqv, mul_max_of_nonneg _ _ hm.le, mul_zero, mul_sub]
      rw [e]
      by_cases h : τ ∈ A
      · rw [indicator_of_notMem (by simpa using h), if_neg]
        intro h'; exact hne (le_antisymm h h')
      · rw [indicator_of_mem (by simpa using h), if_pos (le_of_lt (not_le.mp h))]
    rw [Xbar_mid a b hX0 hX1, hAr, hR, hxi]
    constructor <;> ring

noncomputable def mkC (m X q : ℝ) (β : Measure Ty) : Cont :=
  ⟨(Aset m X q)ᶜ.indicator 1, fun τ => m * τ.2, q, β⟩

lemma mk_ok (ubar m a b q : ℝ) (hm : 0 < m) (β : Measure Ty) [IsProbabilityMeasure β]
    (hβs : β squareᶜ = 0)
    (hβo : ∀ p, ∫ τ, rev2 m p τ ∂β ≤ ∫ τ, rev2 m q τ ∂β)
    (hBC : BeliefConsistent .forward (mkC m (b - a + 1 / 2) q β)) :
    IsContEq .forward ubar m a b (mkC m (b - a + 1 / 2) q β) := by
  have hAm := Aset_meas m (b - a + 1 / 2) q
  refine ⟨(measurable_const.indicator hAm.compl).aemeasurable,
    (measurable_const.mul measurable_snd).aemeasurable, ?_, ?_, ?_, (show IsProbabilityMeasure β from inferInstance), hβs, hβo, hBC⟩
  · intro τ
    show (Aset m (b - a + 1 / 2) q)ᶜ.indicator 1 τ ∈ Icc (0:ℝ) 1
    simp only [Set.indicator, mem_Icc]; split_ifs <;> norm_num
  · intro τ hτ
    have hd := VA_sub_VB ubar m a b (mkC m (b - a + 1 / 2) q β) τ
    have hu : u2 m ((mkC m (b - a + 1 / 2) q β).pT τ) τ = 0 := by
      show u2 m (m * τ.2) τ = 0
      rw [u2_eq]; simp
    rw [hu] at hd
    show (0 < (Aset m (b - a + 1 / 2) q)ᶜ.indicator 1 τ → _) ∧
      ((Aset m (b - a + 1 / 2) q)ᶜ.indicator 1 τ < 1 → _)
    have hpU : (mkC m (b - a + 1 / 2) q β).pU = q := rfl
    rw [hpU] at hd
    by_cases h : τ ∈ Aset m (b - a + 1 / 2) q
    · have h' : τ.1 ≤ b - a + 1 / 2 + max (m * τ.2 - q) 0 := h
      rw [indicator_of_notMem (by simpa using h)]
      constructor
      · intro h0; exact absurd h0 (lt_irrefl _)
      · intro _; linarith
    · have h' : ¬ τ.1 ≤ b - a + 1 / 2 + max (m * τ.2 - q) 0 := h
      rw [indicator_of_mem (by simpa using h)]
      constructor
      · intro _; linarith [not_le.mp h']
      · intro h0; simp at h0
  · intro τ hτ p
    show rev2 m p τ ≤ rev2 m (m * τ.2) τ
    have hθ : 0 ≤ m * τ.2 := mul_nonneg hm.le hτ.2.1
    unfold rev2; rw [if_pos le_rfl]
    split_ifs with h
    · exact h
    · exact hθ

lemma post_ok (ubar m a b q : ℝ) (hm : 0 < m)
    (hA0 : μ0 (Aset m (b - a + 1 / 2) q) ≠ 0)
    (hopt : ∀ p, Rv m (b - a + 1 / 2) q p ≤ Rv m (b - a + 1 / 2) q q) :
    ∃ c, IsContEq .forward ubar m a b c := by
  set A := Aset m (b - a + 1 / 2) q with hA
  have hAm : MeasurableSet A := Aset_meas _ _ _
  set γ : Ty → ℝ := Aᶜ.indicator 1 with hγ
  set β := (∫⁻ τ, ENNReal.ofReal (1 - γ τ) ∂μ0)⁻¹ • μ0.withDensity (fun τ => ENNReal.ofReal (1 - γ τ))
    with hβ
  obtain ⟨hZ, hW⟩ := lint_eq A hAm γ (Filter.EventuallyEq.refl _ _)
  have hβ' : β = (μ0 A)⁻¹ • μ0.restrict A := by rw [hβ, hZ, hW]
  have hprob : IsProbabilityMeasure β := by
    rw [hβ']; constructor
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel hA0 (measure_ne_top _ _)]
  refine ⟨mkC m (b - a + 1 / 2) q β, mk_ok ubar m a b q hm β ?_ ?_ ?_⟩
  · rw [hβ', Measure.smul_apply, Measure.restrict_apply square_meas.compl, smul_eq_mul]
    rw [measure_mono_null inter_subset_left mu0_compl_square, mul_zero]
  · intro p
    rw [hβ', post_integral, post_integral]
    exact mul_le_mul_of_nonneg_left (hopt p) (inv_pos' A hA0).le
  · intro _; rfl

theorem contExists (ubar m a b : ℝ) (hm : 0 < m) : ∃ c, IsContEq .forward ubar m a b c := by
  set X := b - a + 1 / 2 with hX
  rcases le_or_gt X 0 with hX0 | hX0
  · refine ⟨mkC m X m (Measure.dirac ((0:ℝ), (1:ℝ))), mk_ok ubar m a b m hm _ ?_ ?_ ?_⟩
    · rw [Measure.dirac_apply' _ square_meas.compl, indicator_of_notMem]
      simp [square]
    · intro p
      rw [integral_dirac, integral_dirac]
      unfold rev2; simp only [mul_one, le_refl, if_true]
      split_ifs with h
      · exact h
      · exact hm.le
    · intro hZ; exfalso; apply hZ
      obtain ⟨hZ', _⟩ := lint_eq (Aset m X m) (Aset_meas _ _ _) ((Aset m X m)ᶜ.indicator 1)
        (Filter.EventuallyEq.refl _ _)
      show (∫⁻ τ, ENNReal.ofReal (1 - (Aset m X m)ᶜ.indicator 1 τ) ∂μ0) = 0
      rw [hZ']
      apply mu0_null_of_sub _ (Iic 0 ×ˢ univ)
      · rintro τ ⟨hτ, hsq⟩
        have h1 : τ.1 ≤ X + max (m * τ.2 - m) 0 := hτ
        have : max (m * τ.2 - m) 0 = 0 := max_eq_right (by nlinarith [hsq.2.2])
        refine ⟨?_, mem_univ _⟩
        show τ.1 ≤ 0; linarith
      · rw [mu0_prod, nu_Iic]; simp
  rcases le_or_gt 1 X with hX1 | hX1
  · apply post_ok ubar m a b (m / 2) hm
    · intro h; have := Areal_pos m X (m / 2) hX0; rw [measureReal_def, h, ENNReal.toReal_zero] at this
      exact lt_irrefl _ this
    · intro p
      exact (top_upper m X _ p hm).trans (top_lower m X _ hm hX1)
  · apply post_ok ubar m a b (m * thetaBar X m) hm
    · intro h; have := Areal_pos m X (m * thetaBar X m) hX0
      rw [measureReal_def, h, ENNReal.toReal_zero] at this
      exact lt_irrefl _ this
    · intro p; exact exist_interior m X p hm hX0 hX1

lemma psne_iff (m pA pB : ℝ) : IsPSNE m pA pB ↔
    pA ∈ SA ∧ pB ∈ SB ∧ (∀ x ∈ SA, piA m x pB ≤ piA m pA pB) ∧
      (∀ y ∈ SB, piB m pA y ≤ piB m pA pB) := by
  unfold IsPSNE CarbonDoubleCount.Planner.IsPureNash
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using h1 0, by simpa using h1 1, fun x hx => ?_, fun y hy => ?_⟩
    · simpa using h2 0 x (by simpa using hx)
    · simpa using h2 1 y (by simpa using hy)
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun n => ?_, fun n x hx => ?_⟩
    · fin_cases n <;> simpa
    · fin_cases n
      · simpa using h3 x (by simpa using hx)
      · simpa using h4 x (by simpa using hx)

end DTC

theorem lemma_2 (ubar m pA pB : ℝ) (hu : 0 < ubar) (hm : 0 < m) :
    IsPSNE m pA pB ↔ ∃ E : Assessment, IsEquilibrium .forward ubar m E ∧ E.pA = pA ∧ E.pB = pB := by
  rw [DTC.psne_iff]
  constructor
  · rintro ⟨hA, hB, h3, h4⟩
    let E : Assessment := ⟨pA, pB, fun a b => Classical.choose (DTC.contExists ubar m a b hm)⟩
    have hE : ∀ a b, IsContEq .forward ubar m a b (E.cont a b) :=
      fun a b => Classical.choose_spec (DTC.contExists ubar m a b hm)
    refine ⟨E, ⟨hA, hB, fun a _ b _ => hE a b, fun a ha => ?_, fun b hb => ?_⟩, rfl, rfl⟩
    · rw [(DTC.contProfits ubar m a pB hm _ (hE a pB)).1,
        (DTC.contProfits ubar m pA pB hm _ (hE pA pB)).1]
      exact h3 a ha
    · rw [(DTC.contProfits ubar m pA b hm _ (hE pA b)).2,
        (DTC.contProfits ubar m pA pB hm _ (hE pA pB)).2]
      exact h4 b hb
  · rintro ⟨E, ⟨hA, hB, hc, hpa, hpb⟩, rfl, rfl⟩
    refine ⟨hA, hB, fun x hx => ?_, fun y hy => ?_⟩
    · have := hpa x hx
      rwa [(DTC.contProfits ubar m x E.pB hm _ (hc x hx E.pB hB)).1,
        (DTC.contProfits ubar m E.pA E.pB hm _ (hc E.pA hA E.pB hB)).1] at this
    · have := hpb y hy
      rwa [(DTC.contProfits ubar m E.pA y hm _ (hc E.pA hA y hy)).2,
        (DTC.contProfits ubar m E.pA E.pB hm _ (hc E.pA hA E.pB hB)).2] at this

end DataTrackComp.Surplus


-- Platform entry point: restates the target verbatim.
namespace DataTrackComp.Surplus

theorem _root_.solution (ubar m pA pB : ℝ) (hu : 0 < ubar) (hm : 0 < m) :
    IsPSNE m pA pB ↔ ∃ E : Assessment, IsEquilibrium .forward ubar m E ∧ E.pA = pA ∧ E.pB = pB := by
  apply @DataTrackComp.Surplus.lemma_2 <;> assumption

end DataTrackComp.Surplus
