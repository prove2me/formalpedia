-- Prove2me | solution 1 for DataTrackComp.Surplus.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:02:04.259023+00:00
-- url     : https://prove2.me/submissions/e532bfa0-31c4-465b-8166-8e655f6b1317

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_Game

open MeasureTheory

namespace DTCProp1
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


noncomputable def contR (m a b : ℝ) : Cont :=
  ⟨fun τ => if b - a + 1 / 2 < τ.1 then 1 else 0, fun _ => 0, m / 2, μ0⟩

lemma contR_eq (ubar m a b : ℝ) (hm : 0 < m) : IsContEq .restricted ubar m a b (contR m a b) := by
  refine ⟨?_, measurable_const.aemeasurable, ?_, ?_, trivial, (show IsProbabilityMeasure μ0 from inferInstance),
    μ0_squareCompl, ?_, rfl⟩
  · exact (Measurable.ite (measurableSet_lt measurable_const measurable_fst)
      measurable_const measurable_const).aemeasurable
  · intro τ; simp only [contR]; split_ifs <;> norm_num
  · intro τ _
    simp only [VA, VB, u1A, u1B, contR]
    constructor
    · intro h; split_ifs at h with h' <;> [linarith; norm_num at h]
    · intro h; split_ifs at h with h' <;> [norm_num at h; linarith [not_lt.1 h']]
  · intro p
    show ∫ τ, rev2 m p τ ∂μ0 ≤ ∫ τ, rev2 m (m / 2) τ ∂μ0
    rw [int_rev2 m _ hm, int_rev2 m _ hm, R_half m hm]; exact R_le m p hm

end DTCProp1

open DTCProp1 in
theorem solution (ubar m : ℝ) (hu : 0 < ubar) (hm : 0 < m) :
    (∃ E : DataTrackComp.Surplus.Assessment, DataTrackComp.Surplus.IsEquilibrium .restricted ubar m E) ∧
    ∀ E : DataTrackComp.Surplus.Assessment, DataTrackComp.Surplus.IsEquilibrium .restricted ubar m E →
      E.pA = 1 / 2 ∧ E.pB = 1 / 2 ∧
      (∀ τ ∈ DataTrackComp.Surplus.square, (τ.1 < 1 / 2 → (E.cont E.pA E.pB).γ1 τ = 0) ∧
        (1 / 2 < τ.1 → (E.cont E.pA E.pB).γ1 τ = 1)) ∧
      (∫ τ, (1 - (E.cont E.pA E.pB).γ1 τ) ∂DataTrackComp.Surplus.μ0 = 1 / 2 ∧
        ∫ τ, (E.cont E.pA E.pB).γ1 τ ∂DataTrackComp.Surplus.μ0 = 1 / 2) ∧
      (E.cont E.pA E.pB).pU = m / 2 := by
  open DataTrackComp.Surplus in
  constructor
  · refine ⟨⟨1 / 2, 1 / 2, fun a b => contR m a b⟩, ?_, ?_, ?_, ?_, ?_⟩
    · show (1/2 : ℝ) ∈ Set.Icc 0 1; constructor <;> norm_num
    · show (1/2 : ℝ) ∈ Set.Icc (-1/2) 1; constructor <;> norm_num
    · intro a _ b _; exact contR_eq ubar m a b hm
    · intro a ha
      have h1 := (cont_R ubar m a (1/2) hm _ (contR_eq ubar m a (1/2) hm)).2.2.2.2.2.1
      have h2 := (cont_R ubar m (1/2) (1/2) hm _ (contR_eq ubar m (1/2) (1/2) hm)).2.2.2.2.2.1
      simp only at h1 h2 ⊢
      rw [h1, h2]
      have ha' : a ∈ Set.Icc (0:ℝ) 1 := ha
      unfold X
      rw [show (1/2:ℝ) - a + 1/2 = 1 - a by ring, min_eq_left (by linarith [ha'.1]),
        max_eq_right (by linarith [ha'.2])]
      norm_num; nlinarith [sq_nonneg (a - 1/2)]
    · intro b hb
      have h1 := (cont_R ubar m (1/2) b hm _ (contR_eq ubar m (1/2) b hm)).2.2.2.2.2.2
      have h2 := (cont_R ubar m (1/2) (1/2) hm _ (contR_eq ubar m (1/2) (1/2) hm)).2.2.2.2.2.2
      simp only at h1 h2 ⊢
      rw [h1, h2]
      have hb' : b ∈ Set.Icc (-1/2:ℝ) 1 := hb
      unfold X
      rw [show b - 1/2 + 1/2 = b by ring, min_eq_left hb'.2]
      norm_num
      rcases le_or_gt b 0 with h | h
      · rw [max_eq_left h]; linarith
      · rw [max_eq_right h.le]; nlinarith [sq_nonneg (b - 1/2)]
  · intro E hE
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
    refine ⟨pa, pb, ?_, ?_, K0.1⟩
    · intro τ hτ
      have := K0.2.1 τ hτ
      have hx : b0 - a0 + 1 / 2 = 1 / 2 := by rw [pa, pb]; norm_num
      rw [hx] at this; exact this
    · rw [K0.2.2.1, K0.2.2.2.1]
      have : X0 = 1/2 := by rw [hX0eq, pa, pb]; norm_num
      rw [this]; norm_num
