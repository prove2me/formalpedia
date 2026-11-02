-- Prove2me | solution 1 for DataTrackComp.Surplus.claim_20
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:14:19.690235+00:00
-- url     : https://prove2.me/submissions/e1d08350-d7a3-4b6c-b857-26f0313bd37f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_Game
import Definitions.Def_DataTrackComp_Surplus_ReducedGame
import Theorems.Thm_DataTrackComp_Surplus_remark_1

open MeasureTheory

namespace DTCC20
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

lemma cont_R (ubar m a b : ℝ) (hm : 0 < m) (c : Cont) (hc : IsContEq .restricted ubar m a b c) :
    c.pU = m / 2 ∧
    (∀ τ ∈ square, (τ.1 < b - a + 1 / 2 → c.γ1 τ = 0) ∧ (b - a + 1 / 2 < τ.1 → c.γ1 τ = 1)) ∧
    ∫ τ, (1 - c.γ1 τ) ∂μ0 = X a b ∧ ∫ τ, c.γ1 τ ∂μ0 = 1 - X a b ∧
    ∫ τ, rev2 m c.pU τ ∂μ0 = m / 4 ∧
    profitA a c = a * X a b ∧ profitB .restricted m b c = b * (1 - X a b) + m / 4 := by
  obtain ⟨hγm, -, hγ01, hinc, -, -, -, hopt, hbel⟩ := hc
  have hbel' : c.belief = μ0 := hbel
  have hpU : c.pU = m / 2 := by
    have := hopt (m / 2)
    rw [hbel', int_rev2 m _ hm, int_rev2 m _ hm, R_half m hm] at this
    exact R_eq m _ hm this
  have hpt : ∀ τ ∈ square, (τ.1 < b - a + 1 / 2 → c.γ1 τ = 0) ∧ (b - a + 1 / 2 < τ.1 → c.γ1 τ = 1) := by
    intro τ hτ
    obtain ⟨h1, h2⟩ := hinc τ hτ
    simp only [VA, VB, u1A, u1B] at h1 h2
    have g := hγ01 τ
    constructor
    · intro hs
      by_contra hne
      have := h1 (lt_of_le_of_ne g.1 (Ne.symm hne)); linarith
    · intro hs
      by_contra hne
      have := h2 (lt_of_le_of_ne g.2 hne); linarith
  set x := b - a + 1 / 2 with hx
  have hae : c.γ1 =ᵐ[μ0] fun τ => if x < τ.1 then 1 else 0 := by
    filter_upwards [ae_square, ae_fst_ne x] with τ h1 h2
    rcases lt_or_gt_of_ne h2 with h | h
    · rw [(hpt τ h1).1 h, if_neg (by linarith)]
    · rw [(hpt τ h1).2 h, if_pos h]
  have hI1 : ∫ τ, (1 - c.γ1 τ) ∂μ0 = X a b := by
    have : (fun τ => 1 - c.γ1 τ) =ᵐ[μ0] fun τ => (fun s : ℝ => if s ≤ x then (1:ℝ) else 0) τ.1 := by
      filter_upwards [hae] with τ h
      rw [h]; by_cases h' : x < τ.1
      · simp [h', not_le.2 h']
      · simp [h', not_lt.1 h']
    rw [integral_congr_ae this, integral_fst (fun s => if s ≤ x then (1:ℝ) else 0), int_le]; rfl
  have hγi := γ_int c.γ1 hγm hγ01
  have hI2 : ∫ τ, c.γ1 τ ∂μ0 = 1 - X a b := by
    have := integral_sub (integrable_const (1:ℝ)) hγi
    rw [hI1] at this; simp at this; linarith
  have hR : ∫ τ, rev2 m c.pU τ ∂μ0 = m / 4 := by rw [int_rev2 m _ hm, hpU, R_half m hm]
  refine ⟨hpU, hpt, hI1, hI2, hR, ?_, ?_⟩
  · unfold profitA; rw [hI1]
  · simp only [profitB]
    rw [integral_add (hγi.mul_const b) (rev2_int m _), integral_mul_const, hI2, hR]; ring



lemma uniqR (ubar m : ℝ) (hm : 0 < m) (E : Assessment) (hE : IsEquilibrium .restricted ubar m E) :
    E.pA = 1/2 ∧ E.pB = 1/2 := by
  obtain ⟨hA, hB, hcont, hpa, hpb⟩ := hE
  have hA' : E.pA ∈ Set.Icc (0:ℝ) 1 := hA
  have hB' : E.pB ∈ Set.Icc (-1/2:ℝ) 1 := hB
  set a0 := E.pA
  set b0 := E.pB
  -- deviations
  set a' := (b0 + 1/2) / 2 with ha'
  set b' := (a0 + 1/2) / 2 with hb'
  have ha'S : a' ∈ SA := show a' ∈ Set.Icc (0:ℝ) 1 by
    constructor <;> linarith [hB'.1, hB'.2]
  have hb'S : b' ∈ SB := show b' ∈ Set.Icc (-1/2:ℝ) 1 by
    constructor <;> linarith [hA'.1, hA'.2]
  have K0 := cont_R ubar m a0 b0 hm _ (hcont a0 hA b0 hB)
  have KA := (cont_R ubar m a' b0 hm _ (hcont a' ha'S b0 hB)).2.2.2.2.2.1
  have KB := (cont_R ubar m a0 b' hm _ (hcont a0 hA b' hb'S)).2.2.2.2.2.2
  have dA := hpa a' ha'S
  have dB := hpb b' hb'S
  rw [KA, K0.2.2.2.2.2.1] at dA
  rw [KB, K0.2.2.2.2.2.2] at dB
  have XA : X a' b0 = a' := by
    unfold X; rw [show b0 - a' + 1/2 = a' by rw [ha']; ring]
    rw [min_eq_left (by linarith [hB'.2]), max_eq_right (by linarith [hB'.1])]
  have XB : X a0 b' = 3/4 - a0/2 := by
    unfold X; rw [show b' - a0 + 1/2 = 3/4 - a0/2 by rw [hb']; ring]
    rw [min_eq_left (by linarith [hA'.1]), max_eq_right (by linarith [hA'.2])]
  rw [XA] at dA; rw [XB] at dB
  set X0 := X a0 b0 with hX0
  have hX01 : 0 ≤ X0 ∧ X0 ≤ 1 := by
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_right _ _)
  -- B's profit positive
  have hBpos : 0 < b0 * (1 - X0) := by nlinarith [hA'.1]
  have hb0 : 0 < b0 := by
    by_contra h; push Not at h; nlinarith [hX01.2]
  have hX0lt : X0 < 1 := by
    by_contra h; push Not at h; nlinarith
  have hApos : 0 < a0 * X0 := by nlinarith
  have hX0pos : 0 < X0 := by
    by_contra h; push Not at h; nlinarith [hA'.1]
  have hX0eq : X0 = b0 - a0 + 1/2 := by
    rw [hX0]; unfold X
    rcases le_or_gt (b0 - a0 + 1/2) 1 with h | h
    · rw [min_eq_left h]
      rcases le_or_gt (b0 - a0 + 1/2) 0 with h' | h'
      · exfalso; have : X0 = 0 := by rw [hX0]; unfold X; rw [min_eq_left h, max_eq_left h']
        linarith
      · rw [max_eq_right h'.le]
    · exfalso; have : X0 = 1 := by
        rw [hX0]; unfold X; rw [min_eq_right h.le, max_eq_right (by norm_num)]
      linarith
  rw [hX0eq] at dA dB
  have e1 : a0 = a' := by
    have h2 : b0 - a0 + 1/2 = 2*a' - a0 := by rw [ha']; ring
    rw [h2] at dA
    have h3 : (a0 - a')^2 ≤ 0 := by ring_nf; ring_nf at dA; linarith
    have := le_antisymm h3 (sq_nonneg _)
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
  have e2 : b0 = b' := by
    have h2 : 1 - (b0 - a0 + 1/2) = 2*b' - b0 := by rw [hb']; ring
    have h2' : 1 - (3/4 - a0/2) = b' := by rw [hb']; ring
    rw [h2, h2'] at dB
    have h3 : (b0 - b')^2 ≤ 0 := by ring_nf; ring_nf at dB; linarith
    have := le_antisymm h3 (sq_nonneg _)
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
  have pa : a0 = 1/2 := by rw [ha'] at e1; rw [hb'] at e2; linarith
  have pb : b0 = 1/2 := by rw [hb'] at e2; linarith
  exact ⟨pa, pb⟩

lemma split_int (x A0 A1 : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ s in Set.Icc (0:ℝ) 1, (if x < s then A1 + s / 2 else A0 - s / 2) =
      A0 * x - x ^ 2 / 4 + A1 * (1 - x) + (1 - x ^ 2) / 4 := by
  have e : (fun s : ℝ => if x < s then A1 + s / 2 else A0 - s / 2) =
      fun s => (A0 - s / 2) + (Set.Ioi x).indicator (fun s => (A1 - A0) + s) s := by
    ext s; by_cases h : x < s
    · simp [Set.indicator, h]; ring
    · simp [Set.indicator, h]
  rw [e]
  have c1 : Continuous (fun s : ℝ => A0 - s / 2) := by fun_prop
  have c2 : Continuous (fun s : ℝ => (A1 - A0) + s) := by fun_prop
  rw [integral_add (c1.integrableOn_Icc) ((c2.integrableOn_Icc).indicator measurableSet_Ioi),
    setIntegral_indicator measurableSet_Ioi]
  have h1 : Set.Icc (0:ℝ) 1 ∩ Set.Ioi x = Set.Ioc x 1 := by
    ext s; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioi, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩; exact ⟨⟨by linarith, h2⟩, h3⟩
  rw [h1, ← intervalIntegral.integral_of_le hx1, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((by fun_prop : Continuous (fun s : ℝ => s / 2)).intervalIntegrable _ _),
    intervalIntegral.integral_add intervalIntegrable_const
      ((by fun_prop : Continuous (fun s : ℝ => s)).intervalIntegrable _ _)]
  simp [intervalIntegral.integral_div, integral_id]
  ring

lemma u2_half (m : ℝ) (hm : 0 < m) :
    ∫ θ in Set.Icc (0:ℝ) 1, (if m / 2 ≤ m * θ then m * θ - m / 2 else 0) = m / 8 := by
  have e : (fun θ : ℝ => if m / 2 ≤ m * θ then m * θ - m / 2 else 0) =
      (Set.Ici (1/2 : ℝ)).indicator (fun θ => m * θ - m / 2) := by
    ext θ; simp only [Set.indicator, Set.mem_Ici]
    have : m / 2 ≤ m * θ ↔ 1 / 2 ≤ θ := by
      constructor <;> intro h <;> nlinarith
    by_cases h : 1 / 2 ≤ θ
    · rw [if_pos (this.2 h), if_pos h]
    · rw [if_neg (fun h' => h (this.1 h')), if_neg h]
  rw [e, setIntegral_indicator measurableSet_Ici]
  have h1 : Set.Icc (0:ℝ) 1 ∩ Set.Ici (1/2) = Set.Icc (1/2) 1 := by
    ext s; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩; exact ⟨⟨by linarith, h2⟩, h3⟩
  rw [h1, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  rw [intervalIntegral.integral_sub ((continuous_const_mul m).intervalIntegrable _ _)
    intervalIntegrable_const, intervalIntegral.integral_const_mul, integral_id]
  simp; ring

lemma H_int (x A0 A1 : ℝ) :
    Integrable (fun τ : Ty => (fun s : ℝ => if x < s then A1 + s / 2 else A0 - s / 2) τ.1) μ0 := by
  have hm : Measurable (fun s : ℝ => if x < s then A1 + s / 2 else A0 - s / 2) :=
    Measurable.ite measurableSet_Ioi (by fun_prop) (by fun_prop)
  refine Integrable.of_bound (hm.comp measurable_fst).aestronglyMeasurable
    (|A0| + |A1| + 1) ?_
  filter_upwards [ae_square] with τ hs
  have h0 : 0 ≤ τ.1 := hs.1.1
  have h1 : τ.1 ≤ 1 := hs.1.2
  simp only [Real.norm_eq_abs]
  split_ifs
  · refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (by linarith : 0 ≤ τ.1 / 2)]; linarith [abs_nonneg A0]
  · refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by linarith : 0 ≤ τ.1 / 2)]; linarith [abs_nonneg A1]

lemma u2_meas (m p : ℝ) : Measurable (fun θ : ℝ => if p ≤ m * θ then m * θ - p else 0) :=
  Measurable.ite (measurableSet_le measurable_const (measurable_const.mul measurable_id))
    (by fun_prop) measurable_const

lemma CS_R (ubar m : ℝ) (hm : 0 < m) (E : Assessment) (hE : IsEquilibrium .restricted ubar m E)
    (hpa : E.pA = 1/2) (hpb : E.pB = 1/2) :
    consumerSurplus .restricted ubar m E = ubar - 5 / 8 + m / 8 := by
  obtain ⟨hA, hB, hcont, -, -⟩ := hE
  have K := cont_R ubar m E.pA E.pB hm _ (hcont _ hA _ hB)
  unfold consumerSurplus
  simp only [surplus]
  set c := E.cont E.pA E.pB
  set x := E.pB - E.pA + 1 / 2 with hx
  have hx' : x = 1/2 := by rw [hx, hpa, hpb]; norm_num
  have hae : c.γ1 =ᵐ[μ0] g x := by
    filter_upwards [ae_square, ae_fst_ne x] with τ h1 h2
    unfold g
    rcases lt_or_gt_of_ne h2 with h | h
    · rw [(K.2.1 τ h1).1 h, if_neg (by linarith)]
    · rw [(K.2.1 τ h1).2 h, if_pos h]
  have e : (fun τ => c.γ1 τ * u1B ubar E.pB τ + (1 - c.γ1 τ) * u1A ubar E.pA τ + u2 m c.pU τ) =ᵐ[μ0]
      fun τ => (fun s : ℝ => if x < s then (ubar - 1/2 - E.pB) + s / 2 else (ubar - E.pA) - s / 2) τ.1
        + (fun θ : ℝ => if m / 2 ≤ m * θ then m * θ - m / 2 else 0) τ.2 := by
    filter_upwards [hae] with τ h
    rw [h, K.1]; unfold g u1A u1B u2
    split_ifs <;> ring
  rw [integral_congr_ae e, integral_add (H_int _ _ _)]
  · rw [integral_fst (fun s : ℝ => if x < s then (ubar - 1/2 - E.pB) + s / 2 else (ubar - E.pA) - s / 2),
      integral_snd (fun θ : ℝ => if m / 2 ≤ m * θ then m * θ - m / 2 else 0),
      hx', split_int _ _ _ (by norm_num) (by norm_num), u2_half m hm, hpa, hpb]
    ring
  · refine Integrable.of_bound ((u2_meas m (m/2)).comp measurable_snd).aestronglyMeasurable m ?_
    filter_upwards [ae_square] with τ hs
    have h0 : 0 ≤ τ.2 := hs.2.1
    have h1 : τ.2 ≤ 1 := hs.2.2
    simp only [Real.norm_eq_abs]
    split_ifs with h
    · rw [abs_le]; constructor <;> nlinarith
    · simp; linarith

lemma CS_M (ubar m : ℝ) (hm : 0 < m) (E : Assessment) (hE : IsEquilibrium .myopic ubar m E) :
    consumerSurplus .myopic ubar m E =
      if m ≤ 6 then ubar - 5 / 8 + m / 144 * (27 - m) else ubar + 1 / 4 := by
  obtain ⟨hA, hB, hcont, hpa, hpb⟩ := hE
  have hA' : E.pA ∈ Set.Icc (0:ℝ) 1 := hA
  have hB' : E.pB ∈ Set.Icc (-1/2:ℝ) 1 := hB
  have K := cont_M ubar m E.pA E.pB hm _ (hcont _ hA _ hB)
  have main := nash_M m E.pA E.pB hm hA' hB'
    (fun a ha => by
      have := hpa a ha
      rwa [(cont_M ubar m a E.pB hm _ (hcont a ha E.pB hB)).2.2.2.2.2.1,
        K.2.2.2.2.2.1] at this)
    (fun b hb => by
      have := hpb b hb
      rwa [(cont_M ubar m E.pA b hm _ (hcont E.pA hA b hb)).2.2.2.2.2.2,
        K.2.2.2.2.2.2] at this)
  obtain ⟨m1, m2, m3, m4⟩ := main
  obtain ⟨hγm, -, hγ01, -, hTR, -, -, -, -⟩ := hcont _ hA _ hB
  unfold consumerSurplus
  simp only [surplus]
  set c := E.cont E.pA E.pB
  set x := E.pB - E.pA + 1 / 2 with hx
  have hTR' : ∀ τ ∈ square, ∀ p : ℝ, rev2 m p τ ≤ rev2 m (c.pT τ) τ := hTR
  have hu2T : ∀ τ ∈ square, u2 m (c.pT τ) τ = 0 := by
    intro τ hτ
    have h := hTR' τ hτ (m * τ.2)
    unfold rev2 at h; rw [if_pos le_rfl] at h
    unfold u2; split_ifs with h'
    · rw [if_pos h'] at h; linarith
    · rfl
  have hae : c.γ1 =ᵐ[μ0] g x := by
    filter_upwards [ae_square, ae_fst_ne x] with τ h1 h2
    unfold g
    rcases lt_or_gt_of_ne h2 with h | h
    · rw [(K.1 τ h1).2 h, if_neg (by linarith)]
    · rw [(K.1 τ h1).1 h, if_pos h]
  have hX : X E.pA E.pB = max 0 (min x 1) := rfl
  have hx01 : 0 ≤ x ∧ x ≤ 1 := by
    rcases clamp_cases x with ⟨h0, h⟩ | ⟨h0, h1, h⟩ | ⟨h1, h⟩
    · rw [← hX, m3] at h
      constructor <;> linarith [hA'.1, hB'.1]
    · exact ⟨h0, h1⟩
    · rw [← hX, m3] at h; linarith
  have hxX : X E.pA E.pB = x := by
    rw [hX, min_eq_left hx01.2, max_eq_right hx01.1]
  -- the product-2 term for untracked consumers
  have hU : ∀ τ, (1 - g x τ) * u2 m c.pU τ =
      (fun s : ℝ => if s ≤ x then (1:ℝ) else 0) τ.1 *
        (fun θ : ℝ => if m / 2 ≤ m * θ then m * θ - m / 2 else 0) τ.2 ∨ x = 0 := by
    intro τ
    rcases eq_or_lt_of_le hx01.1 with h | h
    · right; exact h.symm
    · left; rw [one_sub_g, K.2.2.1 h]; rfl
  have e : (fun τ => c.γ1 τ * (u1B ubar E.pB τ + u2 m (c.pT τ) τ) +
        (1 - c.γ1 τ) * (u1A ubar E.pA τ + u2 m c.pU τ)) =ᵐ[μ0]
      fun τ => (fun s : ℝ => if x < s then (ubar - 1/2 - E.pB) + s / 2 else (ubar - E.pA) - s / 2) τ.1
        + (1 - g x τ) * u2 m c.pU τ := by
    filter_upwards [hae, ae_square] with τ h hs
    rw [h, hu2T τ hs]; unfold g u1A u1B
    split_ifs <;> ring
  have i2 : Integrable (fun τ : Ty => (1 - g x τ) * u2 m c.pU τ) μ0 := by
    have hmeas : Measurable (fun τ : Ty => (1 - g x τ) * u2 m c.pU τ) := by
      refine (measurable_const.sub (g_meas x)).mul ?_
      exact (u2_meas m c.pU).comp measurable_snd
    refine Integrable.of_bound hmeas.aestronglyMeasurable (m + |c.pU|) ?_
    filter_upwards [ae_square] with τ hs
    have h0 : 0 ≤ τ.2 := hs.2.1
    have h1 : τ.2 ≤ 1 := hs.2.2
    simp only [Real.norm_eq_abs]
    have hg : |1 - g x τ| ≤ 1 := by unfold g; split_ifs <;> norm_num
    have hu : |u2 m c.pU τ| ≤ m + |c.pU| := by
      unfold u2; split_ifs with h
      · rw [abs_le]; constructor <;> nlinarith [abs_nonneg c.pU, le_abs_self c.pU, neg_abs_le c.pU]
      · simp; positivity
    rw [abs_mul]
    calc |1 - g x τ| * |u2 m c.pU τ| ≤ 1 * (m + |c.pU|) :=
          mul_le_mul hg hu (abs_nonneg _) zero_le_one
      _ = m + |c.pU| := one_mul _
  rw [integral_congr_ae e, integral_add (H_int _ _ _) i2,
    integral_fst (fun s : ℝ => if x < s then (ubar - 1/2 - E.pB) + s / 2 else (ubar - E.pA) - s / 2),
    split_int _ _ _ hx01.1 hx01.2]
  have hI : ∫ τ, (1 - g x τ) * u2 m c.pU τ ∂μ0 = x * (m / 8) := by
    rcases eq_or_lt_of_le hx01.1 with h | h
    · have : (fun τ => (1 - g x τ) * u2 m c.pU τ) =ᵐ[μ0] fun _ => 0 := by
        filter_upwards [ae_fst_ne x, ae_square] with τ h2 hs
        have : x < τ.1 := lt_of_le_of_ne (h ▸ hs.1.1) (Ne.symm h2)
        unfold g; rw [if_pos this]; ring
      rw [integral_congr_ae this, ← h]; simp
    · have e2 : (fun τ => (1 - g x τ) * u2 m c.pU τ) =
          fun τ => (fun s : ℝ => if s ≤ x then (1:ℝ) else 0) τ.1 *
            (fun θ : ℝ => if m / 2 ≤ m * θ then m * θ - m / 2 else 0) τ.2 := by
        ext τ; rw [one_sub_g, K.2.2.1 h]; rfl
      rw [e2]; unfold μ0
      rw [integral_prod_mul (fun s : ℝ => if s ≤ x then (1:ℝ) else 0)
        (fun θ : ℝ => if m / 2 ≤ m * θ then m * θ - m / 2 else 0), int_le, u2_half m hm,
        min_eq_left hx01.2, max_eq_right hx01.1]
  rw [hI]
  have hxa : x = E.pA := by rw [← hxX, m3]
  rw [hxa]
  split_ifs with h6
  · rw [m1, m2, max_eq_left (by linarith), max_eq_left (by linarith)]; ring
  · rw [m1, m2, max_eq_right (by linarith), max_eq_right (by linarith)]; ring

end DTCC20

open DTCC20 in
theorem solution (ubar m : ℝ) (hu : 0 < ubar) (hm : 0 < m) :
    (∀ E : DataTrackComp.Surplus.Assessment, DataTrackComp.Surplus.IsEquilibrium .restricted ubar m E →
      DataTrackComp.Surplus.consumerSurplus .restricted ubar m E = ubar - 5 / 8 + m / 8) ∧
    (∀ E : DataTrackComp.Surplus.Assessment, DataTrackComp.Surplus.IsEquilibrium .myopic ubar m E →
      DataTrackComp.Surplus.consumerSurplus .myopic ubar m E =
        if m ≤ 6 then ubar - 5 / 8 + m / 144 * (27 - m) else ubar + 1 / 4) ∧
    (DataTrackComp.Surplus.InInteriorRegime m → ∀ ER EM : DataTrackComp.Surplus.Assessment,
      DataTrackComp.Surplus.IsEquilibrium .restricted ubar m ER →
      DataTrackComp.Surplus.IsEquilibrium .myopic ubar m EM →
      DataTrackComp.Surplus.consumerSurplus .restricted ubar m ER <
        DataTrackComp.Surplus.consumerSurplus .myopic ubar m EM) := by
  have hR : ∀ E : DataTrackComp.Surplus.Assessment,
      DataTrackComp.Surplus.IsEquilibrium .restricted ubar m E →
      DataTrackComp.Surplus.consumerSurplus .restricted ubar m E = ubar - 5 / 8 + m / 8 := by
    intro E hE
    have := uniqR ubar m hm E hE
    exact CS_R ubar m hm E hE this.1 this.2
  refine ⟨hR, fun E hE => CS_M ubar m hm E hE, ?_⟩
  intro hmL ER EM hER hEM
  obtain ⟨-, b, hb4, hb⟩ := DataTrackComp.Surplus.remark_1
  obtain ⟨m', hmm', hm'⟩ := hmL
  have h4 : m < 4 := by have := hb m' hm'; linarith
  rw [hR ER hER, CS_M ubar m hm EM hEM, if_pos (by linarith)]
  nlinarith
