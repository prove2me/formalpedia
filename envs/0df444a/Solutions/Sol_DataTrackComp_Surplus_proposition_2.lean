-- Prove2me | solution 1 for DataTrackComp.Surplus.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:10:48.406791+00:00
-- url     : https://prove2.me/submissions/a8ad1315-049b-44fc-b405-5782507ed97b

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_Game

open MeasureTheory

namespace DTCProp2
open DataTrackComp.Surplus

lemma vol_Icc01 : (volume.restrict (Set.Icc (0:ℝ) 1)).real Set.univ = 1 := by
  simp [measureReal_def]

instance : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) :=
  ⟨by simp⟩

instance : IsProbabilityMeasure μ0 := by
  unfold μ0; infer_instance

lemma μ0_squareCompl : μ0 squareᶜ = 0 := by
  have h1 : MeasurableSet square := measurableSet_Icc.prod measurableSet_Icc
  have : μ0 square = 1 := by
    unfold μ0 square
    rw [Measure.prod_prod]; simp
  rw [measure_compl h1 (measure_ne_top _ _), this]; simp

lemma ae_square : ∀ᵐ τ ∂μ0, τ ∈ square := by
  rw [ae_iff]; exact μ0_squareCompl

lemma integral_fst (f : ℝ → ℝ) : ∫ τ, f τ.1 ∂μ0 = ∫ s in Set.Icc (0:ℝ) 1, f s := by
  unfold μ0; rw [integral_fun_fst, vol_Icc01, one_smul]

lemma integral_snd (f : ℝ → ℝ) : ∫ τ, f τ.2 ∂μ0 = ∫ s in Set.Icc (0:ℝ) 1, f s := by
  unfold μ0; rw [integral_fun_snd, vol_Icc01, one_smul]

lemma ae_fst_ne (x : ℝ) : ∀ᵐ τ ∂μ0, τ.1 ≠ x := by
  rw [ae_iff]; simp only [ne_eq, not_not]
  have : {a : Ty | a.1 = x} = Prod.fst ⁻¹' {x} := rfl
  rw [this]; unfold μ0
  rw [← Measure.map_apply measurable_fst (measurableSet_singleton x)]
  rw [Measure.map_fst_prod]; simp

/-- 1-D: ∫_{[0,1]} 1{s ≤ x} = clamp. -/
lemma int_le (x : ℝ) : ∫ s in Set.Icc (0:ℝ) 1, (if s ≤ x then (1:ℝ) else 0) = max 0 (min x 1) := by
  have : (fun s : ℝ => if s ≤ x then (1:ℝ) else 0) = (Set.Iic x).indicator 1 := by
    ext s; simp [Set.indicator, Set.mem_Iic]
  rw [this, integral_indicator_one measurableSet_Iic,
    measureReal_restrict_apply measurableSet_Iic]
  have h2 : Set.Iic x ∩ Set.Icc (0:ℝ) 1 = Set.Icc 0 (min x 1) := by
    ext s; simp [Set.mem_Icc]; constructor <;> intro h <;> refine ⟨?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2]
  rw [h2, measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal']
  rw [max_comm]; simp


/-- clamp -/
noncomputable def X (a b : ℝ) : ℝ := max 0 (min (b - a + 1 / 2) 1)

noncomputable def R (m p : ℝ) : ℝ := p * max (1 - max (p / m) 0) 0

lemma int_rev2 (m p : ℝ) (hm : 0 < m) : ∫ τ, rev2 m p τ ∂μ0 = R m p := by
  have h := integral_snd (fun θ => if p ≤ m * θ then p else 0)
  have e : (fun τ : Ty => rev2 m p τ) = fun τ => (fun θ => if p ≤ m * θ then p else 0) τ.2 := by
    ext τ; rfl
  rw [e, h]
  have : (fun θ : ℝ => if p ≤ m * θ then p else 0) = fun θ => p * (Set.Ici (p / m)).indicator 1 θ := by
    ext θ
    simp only [Set.indicator, Set.mem_Ici, Pi.one_apply]
    have : p ≤ m * θ ↔ p / m ≤ θ := by rw [div_le_iff₀ hm, mul_comm]
    by_cases h1 : p ≤ m * θ
    · simp [h1, this.1 h1]
    · have h2 : ¬ p / m ≤ θ := fun h => h1 (this.2 h)
      simp [h1, h2]
  rw [this, integral_const_mul, integral_indicator_one measurableSet_Ici,
    measureReal_restrict_apply measurableSet_Ici]
  have h2 : Set.Ici (p / m) ∩ Set.Icc (0:ℝ) 1 = Set.Icc (max (p / m) 0) 1 := by
    ext s; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc, max_le_iff]; tauto
  rw [h2, measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal', R]

lemma R_le (m p : ℝ) (hm : 0 < m) : R m p ≤ m / 4 := by
  unfold R
  rcases le_or_gt p 0 with hp | hp
  · have : p / m ≤ 0 := div_nonpos_of_nonpos_of_nonneg hp hm.le
    rw [max_eq_right this]; simp; linarith
  · have hc : 0 < p / m := div_pos hp hm
    rw [max_eq_left hc.le]
    rcases le_or_gt (1 - p / m) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h.le]
      have : p * (1 - p / m) = m / 4 - (p - m / 2) ^ 2 / m := by field_simp; ring
      rw [this]; have := div_nonneg (sq_nonneg (p - m / 2)) hm.le; linarith

lemma R_half (m : ℝ) (hm : 0 < m) : R m (m / 2) = m / 4 := by
  unfold R
  have : m / 2 / m = 1 / 2 := by field_simp
  rw [this]; norm_num; ring

lemma R_eq (m p : ℝ) (hm : 0 < m) (h : m / 4 ≤ R m p) : p = m / 2 := by
  unfold R at h
  rcases le_or_gt p 0 with hp | hp
  · have : p / m ≤ 0 := div_nonpos_of_nonpos_of_nonneg hp hm.le
    rw [max_eq_right this] at h; simp at h; linarith
  · have hc : 0 < p / m := div_pos hp hm
    rw [max_eq_left hc.le] at h
    rcases le_or_gt (1 - p / m) 0 with h' | h'
    · rw [max_eq_right h'] at h; linarith
    · rw [max_eq_left h'.le] at h
      have : p * (1 - p / m) = m / 4 - (p - m / 2) ^ 2 / m := by field_simp; ring
      rw [this] at h
      have h3 : (p - m / 2) ^ 2 / m ≤ 0 := by linarith
      have h4 : (p - m / 2) ^ 2 ≤ 0 := by
        have := (div_le_iff₀ hm).1 h3; simpa using this
      nlinarith [sq_nonneg (p - m / 2)]

lemma rev2_meas (m p : ℝ) : Measurable (fun τ : Ty => rev2 m p τ) := by
  unfold rev2
  exact Measurable.ite (measurableSet_le measurable_const (measurable_const.mul measurable_snd))
    measurable_const measurable_const

lemma rev2_int (m p : ℝ) : Integrable (fun τ : Ty => rev2 m p τ) μ0 := by
  refine Integrable.of_bound (rev2_meas m p).aestronglyMeasurable |p| (Filter.Eventually.of_forall ?_)
  intro τ; unfold rev2; split_ifs <;> simp

lemma γ_int (g : Ty → ℝ) (hg : AEMeasurable g μ0) (h01 : ∀ τ, g τ ∈ Set.Icc (0:ℝ) 1) :
    Integrable g μ0 := by
  refine Integrable.of_bound hg.aestronglyMeasurable 1 (Filter.Eventually.of_forall ?_)
  intro τ; have := h01 τ; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]


lemma int1_rev (m p : ℝ) (hm : 0 < m) :
    ∫ θ in Set.Icc (0:ℝ) 1, (if p ≤ m * θ then p else 0) = R m p := by
  have h := int_rev2 m p hm
  rw [← h]
  have e : (fun τ : Ty => rev2 m p τ) = fun τ => (fun θ => if p ≤ m * θ then p else 0) τ.2 := by
    ext τ; rfl
  rw [e]; exact (integral_snd (fun θ => if p ≤ m * θ then p else 0)).symm

noncomputable def g (x : ℝ) (τ : Ty) : ℝ := if x < τ.1 then 1 else 0

lemma g_meas (x : ℝ) : Measurable (g x) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_fst) measurable_const measurable_const

lemma one_sub_g (x : ℝ) (τ : Ty) : 1 - g x τ = (fun s : ℝ => if s ≤ x then (1:ℝ) else 0) τ.1 := by
  unfold g; by_cases h' : x < τ.1
  · simp [h', not_le.2 h']
  · simp [h', not_lt.1 h']

lemma g_eq (x : ℝ) (τ : Ty) : g x τ = (fun s : ℝ => if x < s then (1:ℝ) else 0) τ.1 := rfl

lemma I1 (x : ℝ) : ∫ τ, (1 - g x τ) ∂μ0 = max 0 (min x 1) := by
  simp_rw [one_sub_g]
  rw [integral_fst (fun s => if s ≤ x then (1:ℝ) else 0), int_le]

lemma Ig (x : ℝ) : ∫ τ, g x τ ∂μ0 = 1 - max 0 (min x 1) := by
  have hi : Integrable (g x) μ0 :=
    γ_int _ (g_meas x).aemeasurable (fun τ => by unfold g; split_ifs <;> norm_num)
  have := integral_sub (integrable_const (1:ℝ)) hi
  rw [I1] at this; simp at this; linarith

lemma I2 (m p x : ℝ) (hm : 0 < m) :
    ∫ τ, (1 - g x τ) * rev2 m p τ ∂μ0 = max 0 (min x 1) * R m p := by
  have e : (fun τ : Ty => (1 - g x τ) * rev2 m p τ) =
      fun τ => (fun s : ℝ => if s ≤ x then (1:ℝ) else 0) τ.1 *
        (fun θ : ℝ => if p ≤ m * θ then p else 0) τ.2 := by
    ext τ; rw [one_sub_g]; rfl
  rw [e]; unfold μ0
  rw [integral_prod_mul (fun s : ℝ => if s ≤ x then (1:ℝ) else 0)
    (fun θ : ℝ => if p ≤ m * θ then p else 0), int_le, int1_rev m p hm]

lemma int_lin (b m : ℝ) : ∫ θ in Set.Icc (0:ℝ) 1, (b + m * θ) = b + m / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((continuous_const_mul m).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    integral_id]
  simp; ring

lemma I3 (b m x : ℝ) :
    ∫ τ, g x τ * (b + m * τ.2) ∂μ0 = (1 - max 0 (min x 1)) * (b + m / 2) := by
  have e : (fun τ : Ty => g x τ * (b + m * τ.2)) =
      fun τ => (fun s : ℝ => if x < s then (1:ℝ) else 0) τ.1 * (fun θ : ℝ => b + m * θ) τ.2 := by
    ext τ; rfl
  rw [e]
  have h1 : ∫ s in Set.Icc (0:ℝ) 1, (if x < s then (1:ℝ) else 0) = 1 - max 0 (min x 1) := by
    rw [← Ig x]; exact (integral_fst (fun s => if x < s then (1:ℝ) else 0)).symm
  unfold μ0
  rw [integral_prod_mul (fun s : ℝ => if x < s then (1:ℝ) else 0) (fun θ : ℝ => b + m * θ),
    h1, int_lin]

/-- the Bayes posterior after buying from A -/
noncomputable def post (γ : Ty → ℝ) : Measure Ty :=
  (∫⁻ τ, ENNReal.ofReal (1 - γ τ) ∂μ0)⁻¹ • μ0.withDensity (fun τ => ENNReal.ofReal (1 - γ τ))

lemma lint_eq (γ : Ty → ℝ) (x : ℝ) (hae : γ =ᵐ[μ0] g x) :
    ∫⁻ τ, ENNReal.ofReal (1 - γ τ) ∂μ0 = ENNReal.ofReal (max 0 (min x 1)) := by
  have hi : Integrable (fun τ => 1 - g x τ) μ0 :=
    (integrable_const (1:ℝ)).sub (γ_int _ (g_meas x).aemeasurable
      (fun τ => by unfold g; split_ifs <;> norm_num))
  have hnn : 0 ≤ᵐ[μ0] (fun τ => 1 - g x τ) :=
    Filter.Eventually.of_forall (fun τ => by
      show (0:ℝ) ≤ 1 - g x τ
      unfold g; split_ifs <;> norm_num)
  rw [← I1, ofReal_integral_eq_lintegral_ofReal hi hnn]
  apply lintegral_congr_ae
  filter_upwards [hae] with τ h; rw [h]

lemma post_prob (γ : Ty → ℝ) (hγm : AEMeasurable γ μ0) (x : ℝ) (hae : γ =ᵐ[μ0] g x)
    (hX : 0 < max 0 (min x 1)) : IsProbabilityMeasure (post γ) := by
  constructor
  unfold post
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lint_eq γ x hae, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simpa using hX) ENNReal.ofReal_ne_top

lemma post_sq (γ : Ty → ℝ) : post γ squareᶜ = 0 := by
  unfold post
  rw [Measure.smul_apply, withDensity_absolutelyContinuous μ0 _ μ0_squareCompl]; simp

lemma post_int (γ : Ty → ℝ) (hγm : AEMeasurable γ μ0) (x : ℝ) (hae : γ =ᵐ[μ0] g x)
    (hX : 0 < max 0 (min x 1)) (m p : ℝ) (hm : 0 < m) :
    ∫ τ, rev2 m p τ ∂(post γ) = R m p := by
  unfold post
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul₀
    ((hγm.const_sub 1).ennreal_ofReal) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    lint_eq γ x hae]
  have : ∫ τ, (ENNReal.ofReal (1 - γ τ)).toReal • rev2 m p τ ∂μ0 = ∫ τ, (1 - g x τ) * rev2 m p τ ∂μ0 := by
    apply integral_congr_ae
    filter_upwards [hae] with τ h
    rw [h, ENNReal.toReal_ofReal (by unfold g; split_ifs <;> norm_num), smul_eq_mul]
  rw [this, I2 m p x hm, ENNReal.toReal_inv, ENNReal.toReal_ofReal hX.le, smul_eq_mul]
  field_simp

lemma clamp_cases (y : ℝ) : (y ≤ 0 ∧ max 0 (min y 1) = 0) ∨ (0 ≤ y ∧ y ≤ 1 ∧ max 0 (min y 1) = y) ∨
    (1 ≤ y ∧ max 0 (min y 1) = 1) := by
  rcases le_total y 0 with h | h
  · left; refine ⟨h, ?_⟩; rw [min_eq_left (by linarith), max_eq_left h]
  · rcases le_total y 1 with h' | h'
    · right; left; refine ⟨h, h', ?_⟩; rw [min_eq_left h', max_eq_right h]
    · right; right; refine ⟨h', ?_⟩; rw [min_eq_right h', max_eq_right (by norm_num)]

lemma rev2_le (m q : ℝ) (τ : Ty) (hm : 0 < m) (hτ : τ ∈ square) : rev2 m q τ ≤ m * τ.2 := by
  have : 0 ≤ τ.2 := hτ.2.1
  unfold rev2; split_ifs with h
  · exact h
  · positivity

lemma cont_M (ubar m a b : ℝ) (hm : 0 < m) (c : Cont) (hc : IsContEq .myopic ubar m a b c) :
    (∀ τ ∈ square, (b - a + 1 / 2 < τ.1 → c.γ1 τ = 1) ∧ (τ.1 < b - a + 1 / 2 → c.γ1 τ = 0)) ∧
    (∀ τ ∈ square, 0 < τ.2 → c.pT τ = m * τ.2) ∧
    (0 < b - a + 1 / 2 → c.pU = m / 2) ∧
    ∫ τ, (1 - c.γ1 τ) ∂μ0 = X a b ∧ ∫ τ, c.γ1 τ ∂μ0 = 1 - X a b ∧
    profitA a c = a * X a b ∧
    profitB .myopic m b c = (1 - X a b) * (b + m / 4) + m / 4 := by
  obtain ⟨hγm, -, hγ01, hinc, hTR, -, -, hopt, hbel⟩ := hc
  have hTR' : ∀ τ ∈ square, ∀ p : ℝ, rev2 m p τ ≤ rev2 m (c.pT τ) τ := hTR
  have hpt : ∀ τ ∈ square, (b - a + 1 / 2 < τ.1 → c.γ1 τ = 1) ∧ (τ.1 < b - a + 1 / 2 → c.γ1 τ = 0) := by
    intro τ hτ
    obtain ⟨h1, h2⟩ := hinc τ hτ
    simp only [VA, VB, u1A, u1B] at h1 h2
    have g := hγ01 τ
    constructor
    · intro hs
      by_contra hne
      have := h2 (lt_of_le_of_ne g.2 hne); linarith
    · intro hs
      by_contra hne
      have := h1 (lt_of_le_of_ne g.1 (Ne.symm hne)); linarith
  have hrevT : ∀ τ ∈ square, rev2 m (c.pT τ) τ = m * τ.2 := by
    intro τ hτ
    refine le_antisymm (rev2_le m _ τ hm hτ) ?_
    have := hTR' τ hτ (m * τ.2)
    unfold rev2 at this; rw [if_pos le_rfl] at this; exact this
  have hpT : ∀ τ ∈ square, 0 < τ.2 → c.pT τ = m * τ.2 := by
    intro τ hτ hθ
    have h := hrevT τ hτ
    unfold rev2 at h
    split_ifs at h with h'
    · exact h
    · exfalso; have : 0 < m * τ.2 := mul_pos hm hθ; linarith
  set x := b - a + 1 / 2 with hx
  have hae : c.γ1 =ᵐ[μ0] g x := by
    filter_upwards [ae_square, ae_fst_ne x] with τ h1 h2
    unfold g
    rcases lt_or_gt_of_ne h2 with h | h
    · rw [(hpt τ h1).2 h, if_neg (by linarith)]
    · rw [(hpt τ h1).1 h, if_pos h]
  have hI1 : ∫ τ, (1 - c.γ1 τ) ∂μ0 = X a b := by
    rw [show X a b = max 0 (min x 1) from rfl, ← I1 x]
    apply integral_congr_ae; filter_upwards [hae] with τ h; rw [h]
  have hγi := γ_int c.γ1 hγm hγ01
  have hI2 : ∫ τ, c.γ1 τ ∂μ0 = 1 - X a b := by
    have := integral_sub (integrable_const (1:ℝ)) hγi
    rw [hI1] at this; simp at this; linarith
  have hpU : 0 < x → c.pU = m / 2 := by
    intro hx0
    have hX : 0 < max 0 (min x 1) := lt_max_of_lt_right (lt_min hx0 one_pos)
    have hne : (∫⁻ τ, ENNReal.ofReal (1 - c.γ1 τ) ∂μ0) ≠ 0 := by
      rw [lint_eq c.γ1 x hae]; simpa using hX
    have hb : c.belief = post c.γ1 := hbel hne
    have := hopt (m / 2)
    rw [hb, post_int c.γ1 hγm x hae hX m _ hm, post_int c.γ1 hγm x hae hX m _ hm, R_half m hm] at this
    exact R_eq m _ hm this
  refine ⟨hpt, hpT, hpU, hI1, hI2, ?_, ?_⟩
  · unfold profitA; rw [hI1]
  · simp only [profitB]
    have e : (fun τ => c.γ1 τ * (b + rev2 m (c.pT τ) τ) + (1 - c.γ1 τ) * rev2 m c.pU τ) =ᵐ[μ0]
        fun τ => g x τ * (b + m * τ.2) + (1 - g x τ) * rev2 m c.pU τ := by
      filter_upwards [hae, ae_square] with τ h hs
      rw [h, hrevT τ hs]
    rw [integral_congr_ae e]
    have i1 : Integrable (fun τ : Ty => g x τ * (b + m * τ.2)) μ0 := by
      refine Integrable.of_bound ((g_meas x).mul (measurable_const.add
        (measurable_const.mul measurable_snd))).aestronglyMeasurable (|b| + |m|) ?_
      filter_upwards [ae_square] with τ hs
      have h0 : 0 ≤ τ.2 := hs.2.1
      have h1 : τ.2 ≤ 1 := hs.2.2
      unfold g; split_ifs
      · simp only [one_mul, Real.norm_eq_abs]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg h0]
        nlinarith [abs_nonneg m]
      · simp; positivity
    have i2 : Integrable (fun τ : Ty => (1 - g x τ) * rev2 m c.pU τ) μ0 := by
      refine Integrable.of_bound (((measurable_const.sub (g_meas x)).mul
        (rev2_meas m c.pU))).aestronglyMeasurable |c.pU| (Filter.Eventually.of_forall ?_)
      intro τ; unfold g rev2; split_ifs <;> simp
    rw [integral_add i1 i2, I3, I2 m _ x hm]
    rcases le_or_gt x 0 with h | h
    · have : X a b = 0 := by
        show max 0 (min x 1) = 0
        rw [min_eq_left (by linarith), max_eq_left h]
      show (1 - max 0 (min x 1)) * (b + m / 2) + max 0 (min x 1) * R m c.pU = _
      rw [show max 0 (min x 1) = X a b from rfl, this]; ring
    · rw [hpU h, R_half m hm]; show _ = (1 - max 0 (min x 1)) * _ + _; ring

noncomputable def contM (m a b : ℝ) : Cont :=
  ⟨g (b - a + 1 / 2), fun τ => m * τ.2, m / 2,
    if (∫⁻ τ, ENNReal.ofReal (1 - g (b - a + 1 / 2) τ) ∂μ0) = 0 then μ0
    else post (g (b - a + 1 / 2))⟩

lemma contM_eq (ubar m a b : ℝ) (hm : 0 < m) : IsContEq .myopic ubar m a b (contM m a b) := by
  set x := b - a + 1 / 2 with hx
  have hae : g x =ᵐ[μ0] g x := Filter.EventuallyEq.rfl
  have hlint := lint_eq (g x) x hae
  refine ⟨(g_meas x).aemeasurable, (measurable_const.mul measurable_snd).aemeasurable, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro τ; simp only [contM]; unfold g; split_ifs <;> norm_num
  · intro τ _
    simp only [VA, VB, u1A, u1B, contM]
    unfold g
    constructor
    · intro h; split_ifs at h with h' <;> [linarith; norm_num at h]
    · intro h; split_ifs at h with h' <;> [norm_num at h; linarith [not_lt.1 h']]
  · intro τ hτ p
    show rev2 m p τ ≤ rev2 m (m * τ.2) τ
    have : rev2 m (m * τ.2) τ = m * τ.2 := by unfold rev2; rw [if_pos le_rfl]
    rw [this]; exact rev2_le m p τ hm hτ
  · simp only [contM]
    split_ifs with h
    · infer_instance
    · have hX : 0 < max 0 (min x 1) := by
        rw [hlint] at h
        rcases lt_or_eq_of_le (le_max_left 0 (min x 1)) with h' | h'
        · exact h'
        · exfalso; apply h; rw [← h']; simp
      exact post_prob (g x) (g_meas x).aemeasurable x hae hX
  · simp only [contM]
    split_ifs
    · exact μ0_squareCompl
    · exact post_sq _
  · intro p
    simp only [contM]
    split_ifs with h
    · rw [int_rev2 m _ hm, int_rev2 m _ hm, R_half m hm]; exact R_le m p hm
    · have hX : 0 < max 0 (min x 1) := by
        rw [hlint] at h
        rcases lt_or_eq_of_le (le_max_left 0 (min x 1)) with h' | h'
        · exact h'
        · exfalso; apply h; rw [← h']; simp
      rw [post_int (g x) (g_meas x).aemeasurable x hae hX m _ hm,
        post_int (g x) (g_meas x).aemeasurable x hae hX m _ hm, R_half m hm]
      exact R_le m p hm
  · intro h
    simp only [contM] at h ⊢
    rw [if_neg h]; rfl

lemma nash_M (m a0 b0 : ℝ) (hm : 0 < m) (hA' : a0 ∈ Set.Icc (0:ℝ) 1) (hB' : b0 ∈ Set.Icc (-1/2:ℝ) 1)
    (hpa : ∀ a ∈ Set.Icc (0:ℝ) 1, a * X a b0 ≤ a0 * X a0 b0)
    (hpb : ∀ b ∈ Set.Icc (-1/2:ℝ) 1, (1 - X a0 b) * (b + m / 4) + m / 4 ≤
      (1 - X a0 b0) * (b0 + m / 4) + m / 4) :
    a0 = max (1 / 2 - m / 12) 0 ∧ b0 = max (1 / 2 - m / 6) (-1 / 2) ∧
        X a0 b0 = a0 ∧ a0 < 1/2 := by
  set k := m / 4 with hk
  set a' := (b0 + 1/2) / 2 with ha'
  have ha'S : a' ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith [hB'.1, hB'.2]
  have dA := hpa a' ha'S
  have XA : X a' b0 = a' := by
    unfold X; rw [show b0 - a' + 1/2 = a' by rw [ha']; ring]
    rw [min_eq_left (by linarith [hB'.2]), max_eq_right (by linarith [hB'.1])]
  rw [XA] at dA
  have hb1S : a0 - 1/2 ∈ Set.Icc (-1/2:ℝ) 1 := by constructor <;> linarith [hA'.1, hA'.2]
  have dB1 := hpb (a0 - 1/2) hb1S
  have XB1 : X a0 (a0 - 1/2) = 0 := by unfold X; norm_num
  rw [XB1] at dB1
  set X0 := X a0 b0 with hX0
  rcases eq_or_lt_of_le hB'.1 with hbm | hbm
  · -- b0 = -1/2
    have hX0z : X0 = 0 := by
      rw [hX0]; unfold X; rw [← hbm]
      rw [min_eq_left (by linarith [hA'.1]), max_eq_left (by linarith [hA'.1])]
    rw [hX0z] at dB1
    have ha0 : a0 = 0 := by linarith [hA'.1]
    have hm6 : 6 ≤ m := by
      by_contra hm6; push Not at hm6
      set b2 := (1/2 - k) / 2 with hb2
      have hb2S : b2 ∈ Set.Icc (-1/2:ℝ) 1 := by constructor <;> linarith
      have dB2 := hpb b2 hb2S
      rw [hX0z] at dB2
      have XB2 : X a0 b2 = b2 + 1/2 := by
        unfold X; rw [ha0, min_eq_left (by linarith), max_eq_right (by linarith)]; ring
      rw [XB2, ← hbm] at dB2
      nlinarith [sq_nonneg (k - 3/2)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ha0, max_eq_right (by linarith)]
    · rw [← hbm, max_eq_right (by linarith)]
    · rw [hX0z, ha0]
    · rw [ha0]; norm_num
  · -- b0 > -1/2
    have hX01 : 0 ≤ X0 ∧ X0 ≤ 1 := ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
    have ha'pos : 0 < a' := by rw [ha']; linarith
    have hApos : 0 < a0 * X0 := lt_of_lt_of_le (mul_pos ha'pos ha'pos) dA
    have hX0pos : 0 < X0 := by
      by_contra h; push Not at h
      have := mul_nonpos_of_nonneg_of_nonpos hA'.1 h; linarith
    have ha0pos : 0 < a0 := by
      by_contra h; push Not at h
      have := mul_nonpos_of_nonpos_of_nonneg h hX01.1; linarith
    have hx0 : X0 = b0 - a0 + 1/2 := by
      rcases clamp_cases (b0 - a0 + 1/2) with ⟨hh, h⟩ | ⟨h0, h1, h⟩ | ⟨hh, h⟩
      · exfalso; have : X0 = 0 := h; linarith
      · exact h
      · exfalso
        have : X0 = 1 := h
        rw [this] at dA
        have q : (a0+1)/2 ≤ a' := by rw [ha']; linarith
        have q0 : 0 ≤ (a0+1)/2 := by linarith [hA'.1]
        have q2 : ((a0+1)/2) * ((a0+1)/2) ≤ a' * a' := mul_le_mul q q q0 (q0.trans q)
        have h3 : (a0 - 1)^2 ≤ 0 := by
          have e : (a0 - 1)^2 = 4 * (((a0+1)/2) * ((a0+1)/2) - a0) := by ring
          rw [e]; linarith
        have := le_antisymm h3 (sq_nonneg _)
        have ha1 : a0 = 1 := by linarith [sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)]
        linarith [hB'.2]
    rw [hx0] at dA dB1
    have e1 : a0 = a' := by
      have h2 : b0 - a0 + 1/2 = 2*a' - a0 := by rw [ha']; ring
      rw [h2] at dA
      have h3 : (a0 - a')^2 ≤ 0 := by ring_nf; ring_nf at dA; linarith
      have := le_antisymm h3 (sq_nonneg _)
      exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
    have hx1 : b0 - a0 + 1/2 < 1 := by
      rcases lt_or_eq_of_le (show b0 - a0 + 1/2 ≤ 1 by rw [← hx0]; exact hX01.2) with h | h
      · exact h
      · exfalso; rw [ha'] at e1; nlinarith [hB'.2]
    -- B's interior deviation
    have hcase : a0 + k ≤ 3/2 := by
      by_contra h; push Not at h
      -- f(b0) < f(a0 - 1/2)
      have p1 : 0 < b0 - (a0 - 1/2) := by linarith
      have p2 : 0 < k + b0 - 1 := by linarith
      have := mul_pos p1 p2
      have e : (1 - (b0 - a0 + 1/2)) * (b0 + k) + k - ((1 - 0) * (a0 - 1/2 + k) + k)
          = -((b0 - (a0 - 1/2)) * (k + b0 - 1)) := by ring
      linarith
    set bs := (a0 + 1/2 - k) / 2 with hbs
    have hbsS : bs ∈ Set.Icc (-1/2:ℝ) 1 := by
      constructor <;> linarith [hA'.2]
    have dBs := hpb bs hbsS
    have XBs : X a0 bs = bs - a0 + 1/2 := by
      unfold X; rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    rw [XBs, hx0] at dBs
    have e2 : b0 = bs := by
      have h3 : (b0 - bs)^2 ≤ 0 := by
        have e : (b0 - bs)^2 = ((1 - (bs - a0 + 1/2)) * (bs + k) + k) -
            ((1 - (b0 - a0 + 1/2)) * (b0 + k) + k) := by rw [hbs]; ring
        rw [e]; linarith
      have := le_antisymm h3 (sq_nonneg _)
      exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
    have pa : a0 = 1/2 - m/12 := by rw [ha'] at e1; rw [hbs] at e2; linarith
    have pb : b0 = 1/2 - m/6 := by rw [ha'] at e1; rw [hbs] at e2; linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [pa, max_eq_left (by linarith)]
    · rw [pb, max_eq_left (by linarith)]
    · rw [hx0, pa, pb]; ring
    · rw [pa]; linarith

end DTCProp2

open DTCProp2 in
theorem solution (ubar m : ℝ) (hu : 0 < ubar) (hm : 0 < m) :
    (∃ E : DataTrackComp.Surplus.Assessment, DataTrackComp.Surplus.IsEquilibrium .myopic ubar m E) ∧
    ∀ E : DataTrackComp.Surplus.Assessment, DataTrackComp.Surplus.IsEquilibrium .myopic ubar m E →
      E.pA = max (1 / 2 - m / 12) 0 ∧ E.pB = max (1 / 2 - m / 6) (-1 / 2) ∧
      (∀ τ ∈ DataTrackComp.Surplus.square, (E.pB - E.pA + 1 / 2 < τ.1 → (E.cont E.pA E.pB).γ1 τ = 1) ∧
        (τ.1 < E.pB - E.pA + 1 / 2 → (E.cont E.pA E.pB).γ1 τ = 0)) ∧
      (∀ τ ∈ DataTrackComp.Surplus.square, 0 < τ.2 → (E.cont E.pA E.pB).pT τ = m * τ.2) ∧
      (0 < E.pB - E.pA + 1 / 2 → (E.cont E.pA E.pB).pU = m / 2) ∧
      (∫ τ, (1 - (E.cont E.pA E.pB).γ1 τ) ∂DataTrackComp.Surplus.μ0 <
          ∫ τ, (E.cont E.pA E.pB).γ1 τ ∂DataTrackComp.Surplus.μ0 ∧
        ∫ τ, (1 - (E.cont E.pA E.pB).γ1 τ) ∂DataTrackComp.Surplus.μ0 = E.pA ∧ E.pA < 1 / 2) := by
  open DataTrackComp.Surplus in
  constructor
  · -- existence
    set a0 := max (1 / 2 - m / 12) 0 with ha0
    set b0 := max (1 / 2 - m / 6) (-1 / 2) with hb0
    have K0 := cont_M ubar m a0 b0 hm _ (contM_eq ubar m a0 b0 hm)
    refine ⟨⟨a0, b0, fun a b => contM m a b⟩, ?_, ?_, ?_, ?_, ?_⟩
    · show a0 ∈ Set.Icc (0:ℝ) 1
      constructor
      · exact le_max_right _ _
      · exact max_le (by linarith) (by norm_num)
    · show b0 ∈ Set.Icc (-1/2:ℝ) 1
      constructor
      · exact le_max_right _ _
      · exact max_le (by linarith) (by norm_num)
    · intro a _ b _; exact contM_eq ubar m a b hm
    · intro a ha
      have ha' : a ∈ Set.Icc (0:ℝ) 1 := ha
      have h1 := (cont_M ubar m a b0 hm _ (contM_eq ubar m a b0 hm)).2.2.2.2.2.1
      simp only at h1 ⊢
      rw [h1, K0.2.2.2.2.2.1]
      unfold X
      rcases le_or_gt m 6 with hm6 | hm6
      · have e1 : a0 = 1/2 - m/12 := max_eq_left (by linarith)
        have e2 : b0 = 1/2 - m/6 := max_eq_left (by linarith)
        rw [e1, e2]
        have hX0 : max 0 (min (1/2 - m/6 - (1/2 - m/12) + 1/2) 1) = 1/2 - m/12 := by
          rw [min_eq_left (by linarith), max_eq_right (by linarith)]; ring
        rw [hX0]
        rcases clamp_cases (1/2 - m/6 - a + 1/2) with ⟨_, h⟩ | ⟨h0, h1, h⟩ | ⟨hh, h⟩ <;> rw [h]
        · nlinarith [ha'.1]
        · nlinarith [sq_nonneg (a - (1/2 - m/12))]
        · nlinarith [ha'.1]
      · have e1 : a0 = 0 := max_eq_right (by linarith)
        have e2 : b0 = -1/2 := max_eq_right (by linarith)
        rw [e1, e2]
        rcases clamp_cases (-1/2 - a + 1/2) with ⟨_, h⟩ | ⟨h0, h1, h⟩ | ⟨hh, h⟩ <;> rw [h]
        · simp
        · nlinarith [ha'.1]
        · nlinarith [ha'.1]
    · intro b hb
      have hb' : b ∈ Set.Icc (-1/2:ℝ) 1 := hb
      have h1 := (cont_M ubar m a0 b hm _ (contM_eq ubar m a0 b hm)).2.2.2.2.2.2
      simp only at h1 ⊢
      rw [h1, K0.2.2.2.2.2.2]
      unfold X
      rcases le_or_gt m 6 with hm6 | hm6
      · have e1 : a0 = 1/2 - m/12 := max_eq_left (by linarith)
        have e2 : b0 = 1/2 - m/6 := max_eq_left (by linarith)
        rw [e1, e2]
        have hX0 : max 0 (min (1/2 - m/6 - (1/2 - m/12) + 1/2) 1) = 1/2 - m/12 := by
          rw [min_eq_left (by linarith), max_eq_right (by linarith)]; ring
        rw [hX0]
        rcases clamp_cases (b - (1/2 - m/12) + 1/2) with ⟨hh, h⟩ | ⟨h0, h1, h⟩ | ⟨hh, h⟩ <;> rw [h]
        · nlinarith [sq_nonneg (1/2 - m/12)]
        · nlinarith [sq_nonneg (b - (1/2 - m/6))]
        · nlinarith [sq_nonneg (1/2 + m/12)]
      · have e1 : a0 = 0 := max_eq_right (by linarith)
        have e2 : b0 = -1/2 := max_eq_right (by linarith)
        rw [e1, e2]
        have hX0 : max 0 (min (-1/2 - 0 + 1/2 : ℝ) 1) = 0 := by norm_num
        rw [hX0]
        rcases clamp_cases (b - 0 + 1/2) with ⟨hh, h⟩ | ⟨h0, h1, h⟩ | ⟨hh, h⟩ <;> rw [h]
        · nlinarith [hb'.1]
        · nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 - (b - 0 + 1/2) by linarith)
            (show (0:ℝ) ≤ m / 4 - 1/2 - (1/2 - b) by nlinarith [hb'.1])]
        · nlinarith
  · intro E hE
    obtain ⟨hA, hB, hcont, hpa, hpb⟩ := hE
    have hA' : E.pA ∈ Set.Icc (0:ℝ) 1 := hA
    have hB' : E.pB ∈ Set.Icc (-1/2:ℝ) 1 := hB
    have K0 := cont_M ubar m E.pA E.pB hm _ (hcont E.pA hA E.pB hB)
    have main := nash_M m E.pA E.pB hm hA' hB'
      (fun a ha => by
        have := hpa a ha
        rwa [(cont_M ubar m a E.pB hm _ (hcont a ha E.pB hB)).2.2.2.2.2.1,
          K0.2.2.2.2.2.1] at this)
      (fun b hb => by
        have := hpb b hb
        rwa [(cont_M ubar m E.pA b hm _ (hcont E.pA hA b hb)).2.2.2.2.2.2,
          K0.2.2.2.2.2.2] at this)
    obtain ⟨m1, m2, m3, m4⟩ := main
    refine ⟨m1, m2, K0.1, K0.2.1, K0.2.2.1, ?_⟩
    rw [K0.2.2.2.1, K0.2.2.2.2.1, m3]
    refine ⟨by linarith, rfl, m4⟩
