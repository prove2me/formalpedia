-- Prove2me | solution 1 for BousquetElisseeff.KLReg.theorem_24_uniform_stability
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T22:50:53.301149+00:00
-- url     : https://prove2.me/submissions/bd4d5dfd-3866-45ac-883b-57b0cb22c90c

import Mathlib
import Definitions.Def_BousquetElisseeff_KLReg_IsDensity
import Definitions.Def_BousquetElisseeff_KLReg_relEnt
import Definitions.Def_BousquetElisseeff_KLReg_avgLoss
import Definitions.Def_BousquetElisseeff_KLReg_IsKLRegMinimizer

set_option autoImplicit false

open MeasureTheory

namespace BE24Aux

open Real InformationTheory BousquetElisseeff.KLReg

/-- Pointwise: `|e^(b-u) - 1| ≤ (D - b) + b e^(b-u)` for `b, u ∈ [0, D]`. -/
lemma abs_exp_sub_one_le (b u D : ℝ) (hb0 : 0 ≤ b) (hbD : b ≤ D) (hu0 : 0 ≤ u) (huD : u ≤ D) :
    |exp (b - u) - 1| ≤ (D - b) + b * exp (b - u) := by
  have hE := exp_pos (b - u)
  rcases le_total (b - u) 0 with h | h
  · have h1 : exp (b - u) ≤ 1 := exp_le_one_iff.mpr h
    have h2 : (b - u) + 1 ≤ exp (b - u) := add_one_le_exp _
    have h3 : 0 ≤ b * exp (b - u) := mul_nonneg hb0 hE.le
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h1 : 1 ≤ exp (b - u) := one_le_exp h
    have h2 : -(b - u) + 1 ≤ exp (-(b - u)) := add_one_le_exp _
    have h4 : exp (b - u) * exp (-(b - u)) = 1 := by rw [← exp_add]; simp
    have h5 : exp (b - u) * (1 - (b - u)) ≤ exp (b - u) * exp (-(b - u)) :=
      mul_le_mul_of_nonneg_left (by linarith) hE.le
    have h5' : exp (b - u) * (1 - (b - u)) = exp (b - u) - (b - u) * exp (b - u) := by ring
    have h6 : (b - u) * exp (b - u) ≤ b * exp (b - u) :=
      mul_le_mul_of_nonneg_right (by linarith) hE.le
    rw [abs_of_nonneg (by linarith)]
    linarith

lemma intg_of_bdd {α : Type*} [MeasurableSpace α] (P : Measure α) [IsFiniteMeasure P]
    {g : α → ℝ} (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) : Integrable g P :=
  Integrable.of_bound hg.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)

/-- Total-variation bound for an exponential tilt whose exponent has oscillation at most `D`. -/
lemma tilt_bound {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    (ψ h : α → ℝ) (hψ : Measurable ψ) (hh : Measurable h) (a D M : ℝ) (hM : 0 ≤ M)
    (hψb : ∀ x, a ≤ ψ x ∧ ψ x ≤ a + D) (hhb : ∀ x, 0 ≤ h x ∧ h x ≤ M) :
    |∫ x, h x ∂(P.tilted (fun x => -ψ x)) - ∫ x, h x ∂P| ≤ M * D / 2 := by
  have hexpm : Measurable (fun x => exp (-ψ x)) := hψ.neg.exp
  have hexpb : ∀ x, exp (-a - D) ≤ exp (-ψ x) ∧ exp (-ψ x) ≤ exp (-a) := fun x =>
    ⟨exp_le_exp.mpr (by linarith [(hψb x).2]), exp_le_exp.mpr (by linarith [(hψb x).1])⟩
  have hexpi : Integrable (fun x => exp (-ψ x)) P := by
    refine intg_of_bdd P hexpm (exp (-a)) (fun x => ?_)
    rw [abs_of_pos (exp_pos _)]; exact (hexpb x).2
  set Z := ∫ x, exp (-ψ x) ∂P with hZ
  have hZlo : exp (-a - D) ≤ Z := by
    have := integral_mono (integrable_const (exp (-a - D))) hexpi (fun x => (hexpb x).1)
    simpa using this
  have hZhi : Z ≤ exp (-a) := by
    have := integral_mono hexpi (integrable_const (exp (-a))) (fun x => (hexpb x).2)
    simpa using this
  have hZpos : 0 < Z := lt_of_lt_of_le (exp_pos _) hZlo
  set b := -a - log Z with hb
  have hb0 : 0 ≤ b := by
    have : log Z ≤ -a := by rw [← log_exp (-a)]; exact log_le_log hZpos hZhi
    linarith
  have hbD : b ≤ D := by
    have : -a - D ≤ log Z := by rw [← log_exp (-a - D)]; exact log_le_log (exp_pos _) hZlo
    linarith
  have hD : 0 ≤ D := le_trans hb0 hbD
  set ρ : α → ℝ := fun x => exp (-ψ x) / Z with hρdef
  have hρ : ∀ x, ρ x = exp (b - (ψ x - a)) := by
    intro x
    simp only [hρdef]
    rw [hb, show -a - log Z - (ψ x - a) = -ψ x - log Z by ring, exp_sub, exp_log hZpos]
  have hρm : Measurable ρ := hexpm.div_const Z
  have hρb : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ exp D := by
    intro x
    rw [hρ x]
    refine ⟨(exp_pos _).le, exp_le_exp.mpr ?_⟩
    linarith [(hψb x).1]
  have hρi : Integrable ρ P := hexpi.div_const Z
  have hρ1 : ∫ x, ρ x ∂P = 1 := by
    simp only [hρdef]
    rw [integral_div, ← hZ, div_self hZpos.ne']
  have hhi : Integrable h P := by
    refine intg_of_bdd P hh M (fun x => ?_)
    rw [abs_of_nonneg (hhb x).1]; exact (hhb x).2
  have hρhi : Integrable (fun x => ρ x * h x) P := by
    refine intg_of_bdd P (hρm.mul hh) (exp D * M) (fun x => ?_)
    rw [abs_mul, abs_of_nonneg (hρb x).1, abs_of_nonneg (hhb x).1]
    exact mul_le_mul (hρb x).2 (hhb x).2 (hhb x).1 (exp_pos _).le
  have htilt : ∫ x, h x ∂(P.tilted (fun x => -ψ x)) = ∫ x, ρ x * h x ∂P := by
    rw [integral_tilted]
    rfl
  have hprodi : Integrable (fun x => (ρ x - 1) * (h x - M / 2)) P := by
    refine intg_of_bdd P ((hρm.sub measurable_const).mul (hh.sub measurable_const))
      ((exp D + 1) * M) (fun x => ?_)
    rw [abs_mul]
    have e1 : |ρ x - 1| ≤ exp D + 1 := by
      rw [abs_le]; constructor <;> linarith [(hρb x).1, (hρb x).2, exp_pos D]
    have e2 : |h x - M / 2| ≤ M := by
      rw [abs_le]; constructor <;> linarith [(hhb x).1, (hhb x).2]
    exact mul_le_mul e1 e2 (abs_nonneg _) (by linarith [exp_pos D])
  have key : ∫ x, ρ x * h x ∂P - ∫ x, h x ∂P = ∫ x, (ρ x - 1) * (h x - M / 2) ∂P := by
    have e : ∀ x, (ρ x - 1) * (h x - M / 2) = (ρ x * h x - h x) - (M / 2 * ρ x - M / 2) := by
      intro x; ring
    simp_rw [e]
    have i1 : Integrable (fun x => ρ x * h x - h x) P := hρhi.sub hhi
    have i2 : Integrable (fun x => M / 2 * ρ x - M / 2) P :=
      (hρi.const_mul (M / 2)).sub (integrable_const _)
    rw [integral_sub i1 i2, integral_sub hρhi hhi, integral_sub (hρi.const_mul (M / 2)) (integrable_const _),
      integral_const_mul, hρ1]
    simp
  have hbound : ∀ x, |(ρ x - 1) * (h x - M / 2)| ≤ M / 2 * ((D - b) + b * ρ x) := by
    intro x
    rw [abs_mul]
    have e1 : |ρ x - 1| ≤ (D - b) + b * ρ x := by
      rw [hρ x]
      exact abs_exp_sub_one_le b (ψ x - a) D hb0 hbD (by linarith [(hψb x).1])
        (by linarith [(hψb x).2])
    have e2 : |h x - M / 2| ≤ M / 2 := by
      rw [abs_le]; constructor <;> linarith [(hhb x).1, (hhb x).2]
    calc |ρ x - 1| * |h x - M / 2| ≤ ((D - b) + b * ρ x) * (M / 2) :=
          mul_le_mul e1 e2 (abs_nonneg _) (by nlinarith [(hρb x).1])
      _ = M / 2 * ((D - b) + b * ρ x) := by ring
  have hRi : Integrable (fun x => M / 2 * ((D - b) + b * ρ x)) P :=
    ((integrable_const (D - b)).add (hρi.const_mul b)).const_mul (M / 2)
  have hR : ∫ x, M / 2 * ((D - b) + b * ρ x) ∂P = M * D / 2 := by
    rw [integral_const_mul, integral_add (integrable_const _) (hρi.const_mul b),
      integral_const_mul, hρ1]
    simp
    ring
  rw [htilt, key]
  calc |∫ x, (ρ x - 1) * (h x - M / 2) ∂P|
      ≤ ∫ x, |(ρ x - 1) * (h x - M / 2)| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ x, M / 2 * ((D - b) + b * ρ x) ∂P := integral_mono hprodi.abs hRi hbound
    _ = M * D / 2 := hR

/-- EReal bookkeeping for the regularized objective. -/
lemma ereal_aux (a b lam : ℝ) (x y : ENNReal) (hlam : 0 < lam) (hy : y ≠ ⊤)
    (h : ((a : ℝ) : EReal) + (lam : EReal) * ((x : ENNReal) : EReal)
      ≤ ((b : ℝ) : EReal) + (lam : EReal) * ((y : ENNReal) : EReal)) :
    x ≠ ⊤ ∧ a + lam * x.toReal ≤ b + lam * y.toReal := by
  rw [← EReal.coe_ennreal_toReal hy, ← EReal.coe_mul, ← EReal.coe_add] at h
  by_cases hx : x = ⊤
  · exfalso
    subst hx
    rw [EReal.coe_ennreal_top, EReal.coe_mul_top_of_pos hlam, EReal.coe_add_top] at h
    exact (not_le.mpr (EReal.coe_lt_top _)) h
  · rw [← EReal.coe_ennreal_toReal hx, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    exact ⟨hx, h⟩

/-- Gibbs variational principle: a minimizer of `∫ φ dP + KL(P, Q)` is the tilt of `Q` by `-φ`. -/
lemma eq_tilted_of_min {α : Type*} [MeasurableSpace α] (Q P G : Measure α)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    (φ : α → ℝ) (hφ : Measurable φ) (C : ℝ) (hφb : ∀ x, |φ x| ≤ C) (lam : ℝ) (hlam : 0 < lam)
    (hG : G = Q.tilted (fun x => -φ x))
    (hmin : ((lam * ∫ x, φ x ∂P : ℝ) : EReal) + (lam : EReal) * ((klDiv P Q : ENNReal) : EReal)
       ≤ ((lam * ∫ x, φ x ∂G : ℝ) : EReal) + (lam : EReal) * ((klDiv G Q : ENNReal) : EReal)) :
    P = G := by
  have hexpi : Integrable (fun x => exp (-φ x)) Q := by
    refine intg_of_bdd Q hφ.neg.exp (exp C) (fun x => ?_)
    rw [abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr (by linarith [neg_abs_le (φ x), hφb x])
  have : IsProbabilityMeasure G := hG ▸ isProbabilityMeasure_tilted hexpi
  set Z := ∫ x, exp (-φ x) ∂Q with hZ
  have hGQ : G ≪ Q := hG ▸ tilted_absolutelyContinuous Q _
  have hQG : Q ≪ G := hG ▸ absolutelyContinuous_tilted hexpi
  have hφG : Integrable φ G := intg_of_bdd G hφ C hφb
  have hφP : Integrable φ P := intg_of_bdd P hφ C hφb
  -- llr of G w.r.t. Q
  have hllrG : llr G Q =ᵐ[G] fun x => -φ x - log Z := by
    have h1 := llr_tilted_right hGQ hexpi
    rw [← hG] at h1
    filter_upwards [h1, llr_self G] with x hx1 hx2
    have : (0 : ℝ) = -(-φ x) + log Z + llr G Q x := by rw [← hx1]; exact hx2.symm
    linarith
  have hllrGi : Integrable (llr G Q) G :=
    (integrable_congr hllrG).mpr (hφG.neg.sub (integrable_const _))
  have hKG : (klDiv G Q).toReal = -∫ x, φ x ∂G - log Z := by
    have hn : Integrable (fun x => -φ x) G := hφG.neg
    rw [toReal_klDiv_of_measure_eq hGQ (by simp), integral_congr_ae hllrG,
      integral_sub hn (integrable_const _), integral_neg]
    simp
  have hKGne : klDiv G Q ≠ ⊤ := klDiv_ne_top hGQ hllrGi
  obtain ⟨hKPne, hineq⟩ := ereal_aux _ _ lam _ _ hlam hKGne hmin
  obtain ⟨hPQ, hllrPi⟩ := klDiv_ne_top_iff.mp hKPne
  have hKP : (klDiv P Q).toReal = ∫ x, llr P Q x ∂P :=
    toReal_klDiv_of_measure_eq hPQ (by simp)
  have hPG : P ≪ G := hPQ.trans hQG
  have hφPn : Integrable (fun x => -φ x) P := hφP.neg
  have hint := integral_llr_tilted_right hPQ hφPn hexpi hllrPi
  have hintI := integrable_llr_tilted_right hPQ hφPn hllrPi hexpi
  rw [← hG] at hint hintI
  rw [integral_neg] at hint
  have hle : ∫ x, llr P G x ∂P ≤ 0 := by
    rw [hint]
    rw [hKP, hKG] at hineq
    have h2 : lam * (∫ x, φ x ∂P + ∫ x, llr P Q x ∂P + log Z) ≤ 0 := by nlinarith
    have h3 : ∫ x, φ x ∂P + ∫ x, llr P Q x ∂P + log Z ≤ 0 := by
      by_contra hc
      linarith [mul_pos hlam (not_le.mp hc)]
    linarith
  have hK0 : klDiv P G = 0 := by
    rw [klDiv_of_ac_of_integrable hPG hintI]
    simp only [probReal_univ, add_sub_cancel_right]
    exact ENNReal.ofReal_eq_zero.mpr hle
  exact klDiv_eq_zero_iff.mp hK0

lemma integral_wd {Θ : Type*} [MeasurableSpace Θ] (μ : Measure Θ) (g : Θ → ℝ) (hg : Measurable g)
    (h : Θ → ℝ) :
    ∫ θ, h θ ∂(μ.withDensity fun θ => ENNReal.ofReal (g θ)) = ∫ θ, max (g θ) 0 * h θ ∂μ := by
  rw [show (fun θ => ENNReal.ofReal (g θ)) = fun θ => (((g θ).toNNReal : NNReal) : ENNReal) from rfl,
    integral_withDensity_eq_integral_smul hg.real_toNNReal]
  congr 1

lemma isProb_of_density {Θ : Type*} [MeasurableSpace Θ] (μ : Measure Θ) (g : Θ → ℝ)
    (hg : IsDensity μ g) : IsProbabilityMeasure (μ.withDensity fun θ => ENNReal.ofReal (g θ)) := by
  have hint : Integrable g μ := by
    by_contra hc
    have := hg.2.2
    rw [integral_undef hc] at this
    exact zero_ne_one this
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hg.2.1), hg.2.2,
    ENNReal.ofReal_one]

lemma avgLoss_eq {Θ Z : Type*} [MeasurableSpace Θ] (μ : Measure Θ) (r : Θ → Z → ℝ) (g : Θ → ℝ)
    (hg : IsDensity μ g) (z : Z) :
    avgLoss μ r g z = ∫ θ, r θ z ∂(μ.withDensity fun θ => ENNReal.ofReal (g θ)) := by
  rw [integral_wd μ g hg.1, avgLoss]
  congr 1
  ext θ
  rw [max_eq_left (hg.2.1 θ), mul_comm]

/-- Every minimizer of the regularized objective has the Gibbs distribution. -/
lemma min_eq_tilted {Θ Z : Type*} [MeasurableSpace Θ] (μ : Measure Θ) (r : Θ → Z → ℝ)
    (M lam w : ℝ) (f0 : Θ → ℝ)
    (hr_meas : ∀ z, Measurable (fun θ => r θ z)) (hr : ∀ θ z, 0 ≤ r θ z ∧ r θ z ≤ M)
    (hlam : 0 < lam) (hf0 : IsDensity μ f0) {m : ℕ} (T : Finset (Fin m)) (S : Fin m → Z)
    (g : Θ → ℝ) (hg : IsKLRegMinimizer μ r f0 lam w T S g) :
    μ.withDensity (fun θ => ENNReal.ofReal (g θ)) =
      (μ.withDensity (fun θ => ENNReal.ofReal (f0 θ))).tilted
        (fun θ => -((w / lam) * ∑ j ∈ T, r θ (S j))) := by
  set Q := μ.withDensity (fun θ => ENNReal.ofReal (f0 θ)) with hQ
  have : IsProbabilityMeasure Q := isProb_of_density μ f0 hf0
  set φ : Θ → ℝ := fun θ => (w / lam) * ∑ j ∈ T, r θ (S j) with hφdef
  have hφm : Measurable φ :=
    measurable_const.mul (Finset.measurable_sum T (fun j _ => hr_meas (S j)))
  have hsum : ∀ θ, 0 ≤ ∑ j ∈ T, r θ (S j) ∧ ∑ j ∈ T, r θ (S j) ≤ T.card * M := by
    intro θ
    refine ⟨Finset.sum_nonneg (fun j _ => (hr θ (S j)).1), ?_⟩
    have := Finset.sum_le_card_nsmul T (fun j => r θ (S j)) M (fun j _ => (hr θ (S j)).2)
    simpa [nsmul_eq_mul] using this
  have hφb : ∀ θ, |φ θ| ≤ |w / lam| * (T.card * M) := by
    intro θ
    simp only [hφdef]
    rw [abs_mul, abs_of_nonneg (hsum θ).1]
    exact mul_le_mul_of_nonneg_left (hsum θ).2 (abs_nonneg _)
  set C := |w / lam| * (T.card * M)
  have hexpi : Integrable (fun x => exp (-φ x)) Q := by
    refine intg_of_bdd Q hφm.neg.exp (exp C) (fun x => ?_)
    rw [abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr (by linarith [neg_abs_le (φ x), hφb x])
  set G := Q.tilted (fun θ => -φ θ) with hG
  have : IsProbabilityMeasure G := isProbabilityMeasure_tilted hexpi
  set Zc := ∫ x, exp (-φ x) ∂Q with hZc
  have hZpos : 0 < Zc := integral_exp_pos hexpi
  -- a density for G
  set gs : Θ → ℝ := fun θ => f0 θ * (exp (-φ θ) / Zc) with hgs
  have hgsm : Measurable gs := hf0.1.mul (hφm.neg.exp.div_const Zc)
  have hGeq : μ.withDensity (fun θ => ENNReal.ofReal (gs θ)) = G := by
    have hk : Measurable (fun x => ENNReal.ofReal (exp (-φ x) / Zc)) :=
      (hφm.neg.exp.div_const Zc).ennreal_ofReal
    have hk0 : Measurable (fun x => ENNReal.ofReal (f0 x)) := hf0.1.ennreal_ofReal
    rw [hG, Measure.tilted, ← hZc, hQ, ← withDensity_mul μ hk0 hk]
    congr 1
    ext θ
    simp only [Pi.mul_apply, hgs]
    rw [ENNReal.ofReal_mul (hf0.2.1 θ)]
  have hgsd : IsDensity μ gs := by
    refine ⟨hgsm, fun θ => mul_nonneg (hf0.2.1 θ) (div_nonneg (exp_pos _).le hZpos.le), ?_⟩
    have h1 := integral_wd μ gs hgsm (fun _ => (1 : ℝ))
    rw [hGeq] at h1
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    rw [h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    show gs θ = max (gs θ) 0
    exact (max_eq_left (mul_nonneg (hf0.2.1 θ) (div_nonneg (exp_pos _).le hZpos.le))).symm
  -- the objective in terms of the measure
  have hobj : ∀ g' : Θ → ℝ, IsDensity μ g' →
      w * ∑ j ∈ T, avgLoss μ r g' (S j) =
        lam * ∫ θ, φ θ ∂(μ.withDensity fun θ => ENNReal.ofReal (g' θ)) := by
    intro g' hg'
    have : IsProbabilityMeasure (μ.withDensity fun θ => ENNReal.ofReal (g' θ)) :=
      isProb_of_density μ g' hg'
    simp only [hφdef]
    rw [integral_const_mul, integral_finsetSum]
    · simp_rw [avgLoss_eq μ r g' hg']
      field_simp
    · intro j _
      refine intg_of_bdd _ (hr_meas (S j)) M (fun θ => ?_)
      rw [abs_of_nonneg (hr θ (S j)).1]; exact (hr θ (S j)).2
  have hmin := hg.2 gs hgsd
  rw [hobj g hg.1, hobj gs hgsd, hGeq] at hmin
  have : IsProbabilityMeasure (μ.withDensity fun θ => ENNReal.ofReal (g θ)) :=
    isProb_of_density μ g hg.1
  have hrel : ∀ g' : Θ → ℝ, relEnt μ g' f0 =
      klDiv (μ.withDensity fun θ => ENNReal.ofReal (g' θ)) Q := fun g' => rfl
  rw [hrel g, hrel gs, hGeq] at hmin
  exact eq_tilted_of_min Q _ G φ hφm C hφb lam hlam rfl hmin

lemma sum_bdd {Θ Z : Type*} (r : Θ → Z → ℝ) (M : ℝ) (hr : ∀ θ z, 0 ≤ r θ z ∧ r θ z ≤ M)
    {m : ℕ} (T : Finset (Fin m)) (S : Fin m → Z) (θ : Θ) :
    0 ≤ ∑ j ∈ T, r θ (S j) ∧ ∑ j ∈ T, r θ (S j) ≤ T.card * M := by
  refine ⟨Finset.sum_nonneg (fun j _ => (hr θ (S j)).1), ?_⟩
  have := Finset.sum_le_card_nsmul T (fun j => r θ (S j)) M (fun j _ => (hr θ (S j)).2)
  simpa [nsmul_eq_mul] using this

lemma phi_meas {Θ Z : Type*} [MeasurableSpace Θ] (r : Θ → Z → ℝ)
    (hr_meas : ∀ z, Measurable (fun θ => r θ z)) (c : ℝ) {m : ℕ} (T : Finset (Fin m))
    (S : Fin m → Z) : Measurable (fun θ => c * ∑ j ∈ T, r θ (S j)) :=
  measurable_const.mul (Finset.measurable_sum T (fun j _ => hr_meas (S j)))

lemma phi_bdd {Θ Z : Type*} (r : Θ → Z → ℝ) (M : ℝ) (hr : ∀ θ z, 0 ≤ r θ z ∧ r θ z ≤ M)
    (c : ℝ) {m : ℕ} (T : Finset (Fin m)) (S : Fin m → Z) (θ : Θ) :
    |c * ∑ j ∈ T, r θ (S j)| ≤ |c| * (T.card * M) := by
  rw [abs_mul, abs_of_nonneg (sum_bdd r M hr T S θ).1]
  exact mul_le_mul_of_nonneg_left (sum_bdd r M hr T S θ).2 (abs_nonneg _)

lemma diff_bound {α : Type*} [MeasurableSpace α] (Q : Measure α) [IsProbabilityMeasure Q]
    (φ1 φ2 : α → ℝ) (h1 : Measurable φ1) (h2 : Measurable φ2) (C : ℝ) (hb2 : ∀ x, |φ2 x| ≤ C)
    (h : α → ℝ) (hh : Measurable h) (M K : ℝ) (hM : 0 ≤ M) (hhb : ∀ x, 0 ≤ h x ∧ h x ≤ M)
    (hψ : ∀ x, |φ1 x - φ2 x| ≤ K) :
    |∫ x, h x ∂(Q.tilted fun x => -φ1 x) - ∫ x, h x ∂(Q.tilted fun x => -φ2 x)| ≤ M * K := by
  have hexpi2 : Integrable (fun x => exp (-φ2 x)) Q := by
    refine intg_of_bdd Q h2.neg.exp (exp C) (fun x => ?_)
    rw [abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr (by linarith [neg_abs_le (φ2 x), hb2 x])
  have htt : Q.tilted (fun x => -φ1 x) =
      (Q.tilted fun x => -φ2 x).tilted (fun x => -(φ1 x - φ2 x)) := by
    rw [tilted_tilted hexpi2]
    congr 1
    funext x
    simp only [Pi.add_apply]
    ring
  rw [htt]
  have : IsProbabilityMeasure (Q.tilted fun x => -φ2 x) := isProbabilityMeasure_tilted hexpi2
  have hb := tilt_bound (Q.tilted fun x => -φ2 x) (fun x => φ1 x - φ2 x) h (h1.sub h2) hh
    (-K) (2 * K) M hM
    (fun x => ⟨by linarith [(abs_le.mp (hψ x)).1], by linarith [(abs_le.mp (hψ x)).2]⟩) hhb
  calc _ ≤ M * (2 * K) / 2 := hb
    _ = M * K := by ring

lemma part1_alg (k lam ri s M : ℝ) (hk : 1 ≤ k) (hlam : 0 < lam) (hri : 0 ≤ ri ∧ ri ≤ M)
    (hs : 0 ≤ s ∧ s ≤ (k - 1) * M) :
    |(1 / k / lam) * (ri + s) - (1 / (k - 1) / lam) * s| ≤ M / (lam * k) := by
  rcases eq_or_lt_of_le hk with h | h
  · have hs0 : s = 0 := by
      have : (k - 1) * M = 0 := by rw [← h]; ring
      linarith [hs.1, hs.2]
    rw [hs0, ← h]
    have e : (1 / 1 / lam) * (ri + 0) - (1 / (1 - 1) / lam) * 0 = ri / (lam * 1) := by
      simp only [sub_self, div_zero, zero_div, mul_zero, sub_zero, add_zero, mul_one, div_one]
      ring
    rw [e, abs_of_nonneg (div_nonneg hri.1 (by positivity))]
    exact div_le_div_of_nonneg_right hri.2 (by positivity)
  · have hk1 : 0 < k - 1 := by linarith
    have hk0 : 0 < k := by linarith
    have ht0 : 0 ≤ s / (k - 1) := div_nonneg hs.1 hk1.le
    have htM : s / (k - 1) ≤ M := by rw [div_le_iff₀ hk1]; linarith [hs.2]
    have e : (1 / k / lam) * (ri + s) - (1 / (k - 1) / lam) * s = (ri - s / (k - 1)) / (lam * k) := by
      field_simp
      ring
    rw [e, abs_div, abs_of_pos (by positivity : 0 < lam * k)]
    exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) (by positivity)

end BE24Aux

open MeasureTheory BousquetElisseeff.KLReg in
theorem solution {Θ Z : Type*} [MeasurableSpace Θ] (μ : Measure Θ) (r : Θ → Z → ℝ)
    (M lam : ℝ) (f0 : Θ → ℝ) (hr_meas : ∀ z, Measurable (fun θ => r θ z))
    (hr : ∀ θ z, 0 ≤ r θ z ∧ r θ z ≤ M) (hlam : 0 < lam) (hf0 : IsDensity μ f0)
    {m : ℕ} (S : Fin m → Z) (i : Fin m) (f : Θ → ℝ)
    (hf : IsKLRegMinimizer μ r f0 lam (1 / (m : ℝ)) Finset.univ S f) :
    (∀ f' : Θ → ℝ,
        IsKLRegMinimizer μ r f0 lam (1 / ((m : ℝ) - 1)) (Finset.univ.erase i) S f' →
        ∀ z : Z, |avgLoss μ r f z - avgLoss μ r f' z| ≤ M ^ 2 / (lam * (m : ℝ))) ∧
    (∀ f' : Θ → ℝ,
        IsKLRegMinimizer μ r f0 lam (1 / (m : ℝ)) (Finset.univ.erase i) S f' →
        ∀ z : Z, |avgLoss μ r f z - avgLoss μ r f' z| ≤ M ^ 2 / (lam * (m : ℝ))) := by
  have hQ := BE24Aux.isProb_of_density μ f0 hf0
  have hm1 : 1 ≤ m := Fin.pos i
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hcard : ((Finset.univ.erase i).card : ℝ) = (m : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hm1, Nat.cast_one]
  have hsplit : ∀ θ, ∑ j ∈ (Finset.univ : Finset (Fin m)), r θ (S j)
      = r θ (S i) + ∑ j ∈ Finset.univ.erase i, r θ (S j) := fun θ =>
    (Finset.add_sum_erase Finset.univ (fun j => r θ (S j)) (Finset.mem_univ i)).symm
  have hMnn : ∀ z : Z, 0 ≤ M := by
    intro z
    rcases isEmpty_or_nonempty Θ with hΘ | ⟨⟨θ⟩⟩
    · exfalso
      have := hf0.2.2
      rw [Measure.eq_zero_of_isEmpty μ, integral_zero_measure] at this
      exact zero_ne_one this
    · exact le_trans (hr θ z).1 (hr θ z).2
  have hfin : ∀ (w' : ℝ) (f' : Θ → ℝ),
      IsKLRegMinimizer μ r f0 lam w' (Finset.univ.erase i) S f' →
      (∀ θ, |(1 / (m : ℝ) / lam) * ∑ j ∈ (Finset.univ : Finset (Fin m)), r θ (S j)
          - (w' / lam) * ∑ j ∈ Finset.univ.erase i, r θ (S j)| ≤ M / (lam * m)) →
      ∀ z : Z, |avgLoss μ r f z - avgLoss μ r f' z| ≤ M ^ 2 / (lam * (m : ℝ)) := by
    intro w' f' hf' hψ z
    rw [BE24Aux.avgLoss_eq μ r f hf.1, BE24Aux.avgLoss_eq μ r f' hf'.1,
      BE24Aux.min_eq_tilted μ r M lam _ f0 hr_meas hr hlam hf0 _ S f hf,
      BE24Aux.min_eq_tilted μ r M lam _ f0 hr_meas hr hlam hf0 _ S f' hf']
    refine le_trans (BE24Aux.diff_bound _ _ _ (BE24Aux.phi_meas r hr_meas _ _ S)
      (BE24Aux.phi_meas r hr_meas _ _ S) _ (BE24Aux.phi_bdd r M hr _ _ S) _ (hr_meas z) M
      (M / (lam * m)) (hMnn z) (fun θ => hr θ z) hψ) (le_of_eq (by ring))
  refine ⟨fun f' hf' => hfin _ f' hf' (fun θ => ?_), fun f' hf' => hfin _ f' hf' (fun θ => ?_)⟩
  · rw [hsplit θ]
    have hs := BE24Aux.sum_bdd r M hr (Finset.univ.erase i) S θ
    rw [hcard] at hs
    exact BE24Aux.part1_alg (m : ℝ) lam (r θ (S i)) _ M hmR hlam (hr θ (S i)) hs
  · rw [hsplit θ, show ∀ a b : ℝ, 1 / (m : ℝ) / lam * (a + b) - 1 / (m : ℝ) / lam * b
        = a / (lam * m) from fun a b => by field_simp; ring]
    rw [abs_of_nonneg (div_nonneg (hr θ (S i)).1 (by positivity))]
    exact div_le_div_of_nonneg_right (hr θ (S i)).2 (by positivity)
