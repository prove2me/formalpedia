-- Prove2me | solution 1 for DataDrivenNV.LRS.lrsSet_subset_epsOptimal
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:23:44.869987+00:00
-- url     : https://prove2.me/submissions/1fad56a1-c99e-486d-835d-71ba6d450c36

import Definitions.Def_DataDrivenNV_LRS_Setting
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.CDF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open MeasureTheory ProbabilityTheory
namespace DataDrivenNV.LRS.Regret

noncomputable def indLt (q d : ℝ) : ℝ := if d<q then 1 else 0
noncomputable def indLe (q d : ℝ) : ℝ := if d≤q then 1 else 0

lemma indLt_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (q : ℝ) :
    Integrable (indLt q) μ := by
  exact (integrable_const (1:ℝ)).indicator measurableSet_Iio

lemma indLe_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (q : ℝ) :
    Integrable (indLe q) μ := by
  exact (integrable_const (1:ℝ)).indicator measurableSet_Iic

lemma integral_indLt (μ : Measure ℝ) [IsProbabilityMeasure μ] (q : ℝ) :
    (∫ d, indLt q d ∂μ) = (μ (Set.Iio q)).toReal := by
  exact integral_indicator_one measurableSet_Iio

lemma integral_indLe (μ : Measure ℝ) [IsProbabilityMeasure μ] (q : ℝ) :
    (∫ d, indLe q d ∂μ) = cdf μ q := by
  rw [cdf_eq_real]
  exact integral_indicator_one measurableSet_Iic

lemma loss_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (b h q : ℝ) : Integrable (nvLoss b h q) μ := by
  exact (((integrable_const q).sub hμ).pos_part.const_mul h).add
    ((hμ.sub (integrable_const q)).pos_part.const_mul b)

lemma loss_nonneg (b h q d : ℝ) (hb : 0≤b) (hh : 0≤h) : 0≤nvLoss b h q d := by
  exact add_nonneg (mul_nonneg hh (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))

lemma loss_alt_left (b h q d : ℝ) :
    nvLoss b h q d = b*(d-q)+(b+h)*max (q-d) 0 := by
  unfold nvLoss InventoryControl.newsboyLoss
  by_cases hd : q≤d
  · rw [max_eq_right (sub_nonpos.mpr hd),max_eq_left (sub_nonneg.mpr hd)]
    ring
  · have hd' : d≤q := (lt_of_not_ge hd).le
    rw [max_eq_left (sub_nonneg.mpr hd'),max_eq_right (sub_nonpos.mpr hd')]
    ring

lemma loss_alt_right (b h q d : ℝ) :
    nvLoss b h q d = h*(q-d)+(b+h)*max (d-q) 0 := by
  unfold nvLoss InventoryControl.newsboyLoss
  by_cases hd : q≤d
  · rw [max_eq_right (sub_nonpos.mpr hd),max_eq_left (sub_nonneg.mpr hd)]
    ring
  · have hd' : d≤q := (lt_of_not_ge hd).le
    rw [max_eq_left (sub_nonneg.mpr hd'),max_eq_right (sub_nonpos.mpr hd')]
    ring

lemma point_left (b h q z d : ℝ) (hb : 0≤b) (hh : 0≤h) (hzq : z≤q) :
    nvLoss b h q d-nvLoss b h z d ≤ ((b+h)*indLt q d-b)*(q-z) := by
  rw [loss_alt_left,loss_alt_left]
  by_cases hd : d<q
  · have hx : max (q-d) 0-max (z-d) 0 ≤ q-z := by
      rw [max_eq_left (sub_nonneg.mpr hd.le)]
      linarith [le_max_left (z-d) 0]
    have hx' := mul_le_mul_of_nonneg_left hx (add_nonneg hb hh)
    simp only [indLt,if_pos hd]
    nlinarith only [hx']
  · have hqd : q≤d := le_of_not_gt hd
    rw [max_eq_right (sub_nonpos.mpr hqd),max_eq_right (sub_nonpos.mpr (hzq.trans hqd))]
    simp only [indLt,if_neg hd]
    ring_nf <;> exact le_rfl

lemma point_right (b h q z d : ℝ) (hb : 0≤b) (hh : 0≤h) (hqz : q≤z) :
    nvLoss b h q d-nvLoss b h z d ≤ (b-(b+h)*indLe q d)*(z-q) := by
  rw [loss_alt_right,loss_alt_right]
  by_cases hd : d≤q
  · rw [max_eq_right (sub_nonpos.mpr hd),max_eq_right (sub_nonpos.mpr (hd.trans hqz))]
    simp only [indLe,if_pos hd]
    ring_nf <;> exact le_rfl
  · have hqd : q≤d := (lt_of_not_ge hd).le
    have hx : max (d-q) 0-max (d-z) 0 ≤ z-q := by
      rw [max_eq_left (sub_nonneg.mpr hqd)]
      linarith [le_max_left (d-z) 0]
    have hx' := mul_le_mul_of_nonneg_left hx (add_nonneg hb hh)
    simp only [indLe,if_neg hd]
    nlinarith only [hx']

lemma point_lower_left (b h q z d : ℝ) (hb : 0≤b) (hh : 0≤h) (hzq : z≤q) :
    b*(q-z)*(1-indLt q d) ≤ nvLoss b h z d := by
  by_cases hd : d<q
  · simpa only [indLt,if_pos hd,sub_self,mul_zero] using loss_nonneg b h z d hb hh
  · have hqd : q≤d := le_of_not_gt hd
    have hx : q-z ≤ max (d-z) 0 := (sub_le_sub_right hqd z).trans (le_max_left _ _)
    have hx' := mul_le_mul_of_nonneg_left hx hb
    have hh' := mul_nonneg hh (le_max_right (z-d) 0)
    simp only [indLt,if_neg hd,sub_zero,mul_one,nvLoss,InventoryControl.newsboyLoss]
    linarith only [hx',hh']

lemma point_lower_right (b h q z d : ℝ) (hb : 0≤b) (hh : 0≤h) (hqz : q≤z) :
    h*(z-q)*indLe q d ≤ nvLoss b h z d := by
  by_cases hd : d≤q
  · have hx : z-q ≤ max (z-d) 0 := (sub_le_sub_left hd z).trans (le_max_left _ _)
    have hx' := mul_le_mul_of_nonneg_left hx hh
    have hb' := mul_nonneg hb (le_max_right (d-z) 0)
    simp only [indLe,if_pos hd,mul_one,nvLoss,InventoryControl.newsboyLoss]
    linarith only [hx',hb']
  · simpa only [indLe,if_neg hd,mul_zero] using loss_nonneg b h z d hb hh

lemma cost_left (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (b h q z : ℝ) (hb : 0≤b) (hh : 0≤h) (hzq : z≤q) :
    expCost μ b h q-expCost μ b h z ≤ dMinus μ b h q*(q-z) := by
  have hi := indLt_integrable μ q
  calc
    _ = ∫ d, nvLoss b h q d-nvLoss b h z d ∂μ :=
      (integral_sub (loss_integrable μ hμ b h q) (loss_integrable μ hμ b h z)).symm
    _ ≤ ∫ d, ((b+h)*indLt q d-b)*(q-z) ∂μ :=
      integral_mono ((loss_integrable μ hμ b h q).sub (loss_integrable μ hμ b h z))
        (((hi.const_mul (b+h)).sub (integrable_const b)).mul_const (q-z))
        (fun d => point_left b h q z d hb hh hzq)
    _ = _ := by
      rw [integral_mul_const,integral_sub (hi.const_mul (b+h)) (integrable_const b),
        integral_const_mul,integral_indLt]
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,dMinus]
      ring

lemma cost_right (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (b h q z : ℝ) (hb : 0≤b) (hh : 0≤h) (hqz : q≤z) :
    expCost μ b h q-expCost μ b h z ≤ -dPlus μ b h q*(z-q) := by
  have hi := indLe_integrable μ q
  calc
    _ = ∫ d, nvLoss b h q d-nvLoss b h z d ∂μ :=
      (integral_sub (loss_integrable μ hμ b h q) (loss_integrable μ hμ b h z)).symm
    _ ≤ ∫ d, (b-(b+h)*indLe q d)*(z-q) ∂μ :=
      integral_mono ((loss_integrable μ hμ b h q).sub (loss_integrable μ hμ b h z))
        (((integrable_const b).sub (hi.const_mul (b+h))).mul_const (z-q))
        (fun d => point_right b h q z d hb hh hqz)
    _ = _ := by
      rw [integral_mul_const,integral_sub (integrable_const b) (hi.const_mul (b+h)),
        integral_const_mul,integral_indLe]
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,dPlus]
      ring

lemma cost_lower_left (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (b h q z : ℝ) (hb : 0≤b) (hh : 0≤h) (hzq : z≤q) :
    b*(q-z)*(1-(μ (Set.Iio q)).toReal) ≤ expCost μ b h z := by
  have hi := indLt_integrable μ q
  calc
    _ = ∫ d, b*(q-z)*(1-indLt q d) ∂μ := by
      rw [integral_const_mul,integral_sub (integrable_const 1) hi,integral_indLt]
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    _ ≤ _ := integral_mono (((integrable_const 1).sub hi).const_mul (b*(q-z)))
      (loss_integrable μ hμ b h z) (fun d => point_lower_left b h q z d hb hh hzq)

lemma cost_lower_right (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (b h q z : ℝ) (hb : 0≤b) (hh : 0≤h) (hqz : q≤z) :
    h*(z-q)*cdf μ q ≤ expCost μ b h z := by
  calc
    _ = ∫ d, h*(z-q)*indLe q d ∂μ := by rw [integral_const_mul,integral_indLe]
    _ ≤ _ := integral_mono ((indLe_integrable μ q).const_mul (h*(z-q)))
      (loss_integrable μ hμ b h z) (fun d => point_lower_right b h q z d hb hh hqz)

lemma coefficient (b h ε : ℝ) (hb : 0<b) (hh : 0<h) (hε : 0<ε) (hε1 : ε≤1) :
    let δ:=ε/3*min b h
    δ*(b+h) ≤ ε*b*(h-δ) ∧ δ*(b+h) ≤ ε*h*(b-δ) := by
  dsimp only
  have hm : 0 ≤ min b h := le_min hb.le hh.le
  have hmin : min b h*(b+h) ≤ 2*b*h := by
    rcases le_total b h with he|he
    · rw [min_eq_left he]
      nlinarith [mul_le_mul_of_nonneg_left he hb.le]
    · rw [min_eq_right he]
      nlinarith [mul_le_mul_of_nonneg_left he hh.le]
  have hδh : ε/3*min b h ≤ h/3 := by
    have he := mul_le_mul_of_nonneg_right hε1 hm
    nlinarith [min_le_right b h]
  have hδb : ε/3*min b h ≤ b/3 := by
    have he := mul_le_mul_of_nonneg_right hε1 hm
    nlinarith [min_le_left b h]
  have hbase : (ε/3*min b h)*(b+h) ≤ ε/3*(2*b*h) := by
    nlinarith [mul_le_mul_of_nonneg_left hmin (show 0≤ε/3 by positivity)]
  constructor
  · have he := mul_le_mul_of_nonneg_left hδh (show 0≤ε*b by positivity)
    nlinarith only [hbase,he]
  · have he := mul_le_mul_of_nonneg_left hδb (show 0≤ε*h by positivity)
    nlinarith only [hbase,he]

lemma control (S C δ ε a t u : ℝ) (hS : 0<S) (hε : 0≤ε) (ha : 0≤a)
    (hupper : δ*S ≤ ε*t*u) (hlower : t*a*u ≤ C*S) : δ*a ≤ ε*C := by
  apply (mul_le_mul_iff_left₀ hS).mp
  have h1 := mul_le_mul_of_nonneg_right hupper ha
  have h2 := mul_le_mul_of_nonneg_left hlower hε
  nlinarith only [h1,h2]

lemma all_comparators (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (b h ε q z : ℝ) (hb : 0<b) (hh : 0<h) (hε : 0<ε) (hε1 : ε≤1)
    (hq : q ∈ lrsSet μ b h ε) : expCost μ b h q ≤ (1+ε)*expCost μ b h z := by
  let δ:=ε/3*min b h
  have hS : 0<b+h := add_pos hb hh
  obtain ⟨hminus,hplus⟩ := hq
  have hcoef := coefficient b h ε hb hh hε hε1
  rcases le_total z q with hzq|hqz
  · have hup := cost_left μ hμ b h q z hb.le hh.le hzq
    have hdiff : expCost μ b h q-expCost μ b h z ≤ δ*(q-z) :=
      hup.trans (mul_le_mul_of_nonneg_right hminus (sub_nonneg.mpr hzq))
    have hlo := cost_lower_left μ hμ b h q z hb.le hh.le hzq
    have hprob : h-δ ≤ (b+h)*(1-(μ (Set.Iio q)).toReal) := by
      dsimp [dMinus] at hminus
      dsimp [δ]
      linarith only [hminus]
    have hlow : b*(q-z)*(h-δ) ≤ expCost μ b h z*(b+h) := by
      have h1 := mul_le_mul_of_nonneg_left hprob (mul_nonneg hb.le (sub_nonneg.mpr hzq))
      have h2 := mul_le_mul_of_nonneg_right hlo hS.le
      nlinarith only [h1,h2]
    have hc := control (b+h) (expCost μ b h z) δ ε (q-z) b (h-δ)
      hS hε.le (sub_nonneg.mpr hzq) hcoef.1 hlow
    nlinarith only [hdiff,hc]
  · have hup := cost_right μ hμ b h q z hb.le hh.le hqz
    have hdiff : expCost μ b h q-expCost μ b h z ≤ δ*(z-q) :=
      hup.trans (mul_le_mul_of_nonneg_right (by dsimp [δ]; linarith only [hplus]) (sub_nonneg.mpr hqz))
    have hlo := cost_lower_right μ hμ b h q z hb.le hh.le hqz
    have hprob : b-δ ≤ (b+h)*cdf μ q := by
      dsimp [dPlus] at hplus
      dsimp [δ]
      linarith only [hplus]
    have hlow : h*(z-q)*(b-δ) ≤ expCost μ b h z*(b+h) := by
      have h1 := mul_le_mul_of_nonneg_left hprob (mul_nonneg hh.le (sub_nonneg.mpr hqz))
      have h2 := mul_le_mul_of_nonneg_right hlo hS.le
      nlinarith only [h1,h2]
    have hc := control (b+h) (expCost μ b h z) δ ε (z-q) h (b-δ)
      hS hε.le (sub_nonneg.mpr hqz) hcoef.2 hlow
    nlinarith only [hdiff,hc]

end DataDrivenNV.LRS.Regret

open DataDrivenNV.LRS

theorem solution (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    lrsSet μ b h ε ⊆ {q | IsEpsOptimal μ b h ε q} := by
  intro q hq
  exact Regret.all_comparators μ hμ b h ε q (critQuantile μ b h) hb hh hε hε1 hq
