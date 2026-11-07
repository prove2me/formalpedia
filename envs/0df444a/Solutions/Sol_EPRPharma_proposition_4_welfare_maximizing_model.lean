-- Prove2me | solution 1 for EPRPharma.proposition_4_welfare_maximizing_model
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T16:18:28.667748+00:00
-- url     : https://prove2.me/submissions/df29f717-fc94-4ec7-b6ce-c951979aaa6e

import Mathlib
import Definitions.Def_EPRPharma_Params_Standing
import Definitions.Def_EPRPharma_PolicyFeasible
import Definitions.Def_EPRPharma_NonnegOptimalProfit
import Definitions.Def_EPRPharma_OPStrictlyMoreProfitable
import Definitions.Def_EPRPharma_CanEliminate
import Definitions.Def_EPRPharma_EliminationOptimal
import Definitions.Def_EPRPharma_WelfareEqual
import Definitions.Def_EPRPharma_WelfareAtLeast

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace P4Y
open EPRPharma

/-! ## Integrals -/

lemma inner_min (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ y in (0:ℝ)..1, min y x = x - x ^ 2 / 2 := by
  have hc : Continuous (fun y : ℝ => min y x) := continuous_id.min continuous_const
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ y in (0:ℝ)..x, min y x = ∫ y in (0:ℝ)..x, y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hx0] at hy
    exact min_eq_left hy.2
  have h2 : ∫ y in x..1, min y x = ∫ y in x..1, x := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hx1] at hy
    exact min_eq_right hy.1
  rw [h1, h2, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

lemma inner_min1 : ∫ y in (0:ℝ)..1, min y (1:ℝ) = 1 / 2 := by
  have : ∫ y in (0:ℝ)..1, min y (1:ℝ) = ∫ y in (0:ℝ)..1, y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le zero_le_one] at hy
    exact min_eq_left hy.2
  rw [this, integral_id]; norm_num

lemma outer_poly (A B C : ℝ) :
    ∫ x in (0:ℝ)..1, (A + B * x + C * x ^ 2) = A + B / 2 + C / 3 := by
  have i1 : IntervalIntegrable (fun x : ℝ => A + B * x) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ => A + B * x).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ => C * x ^ 2) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ => C * x ^ 2).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun _ : ℝ => A) MeasureTheory.volume 0 1 :=
    (continuous_const).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun x : ℝ => B * x) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ => B * x).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_add i3 i4,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, integral_pow]
  norm_num
  ring

lemma E1L {f : ℝ → ℝ} (A B : ℝ) (hf : ∀ x ∈ Set.Icc (0:ℝ) 1, f x = A + B * x) :
    E1 f = A + B / 2 := by
  unfold E1
  have hin : ∀ x ∈ Set.uIcc (0:ℝ) 1, f x = A + B * x + 0 * x ^ 2 := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    rw [hf x hx]; ring
  rw [intervalIntegral.integral_congr hin, outer_poly]
  ring

lemma E2N {f : ℝ → ℝ → ℝ} (A B C : ℝ)
    (hf : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y, f x y = A + B * x + C * min y x) :
    E2 f = A + B / 2 + C / 3 := by
  unfold E2
  have hin : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      (∫ y in (0:ℝ)..1, f x y) = A + (B + C) * x + (-C / 2) * x ^ 2 := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    simp only [hf x hx]
    have hI1 : IntervalIntegrable (fun _ : ℝ => A + B * x) MeasureTheory.volume 0 1 :=
      continuous_const.intervalIntegrable _ _
    have hI2 : IntervalIntegrable (fun y : ℝ => C * min y x) MeasureTheory.volume 0 1 :=
      (continuous_const.mul (continuous_id.min continuous_const)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul,
      inner_min x hx.1 hx.2, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [intervalIntegral.integral_congr hin, outer_poly]
  ring

lemma E2O {f : ℝ → ℝ → ℝ} (A B C : ℝ)
    (hf : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y, f x y = A + B * x + C * min y 1) :
    E2 f = A + B / 2 + C / 2 := by
  unfold E2
  have hin : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      (∫ y in (0:ℝ)..1, f x y) = (A + C / 2) + B * x + 0 * x ^ 2 := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    simp only [hf x hx]
    have hI1 : IntervalIntegrable (fun _ : ℝ => A + B * x) MeasureTheory.volume 0 1 :=
      continuous_const.intervalIntegrable _ _
    have hI2 : IntervalIntegrable (fun y : ℝ => C * min y (1:ℝ)) MeasureTheory.volume 0 1 :=
      (continuous_const.mul (continuous_id.min continuous_const)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul,
      inner_min1, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [intervalIntegral.integral_congr hin, outer_poly]
  ring

/-! ## The doctor's response -/

variable {P : Params}

noncomputable def slp (P : Params) (d : Decision) : ℝ := d.etaD - d.p - P.od * (1 - d.etaP)

lemma Ud_eq {d : Decision} (θ q : ℝ) :
    Ud P d θ q = (P.up + P.od * (1 - d.etaP)) * θ + slp P d * q := by
  simp only [Ud, slp]; ring

lemma dQ_O {d : Decision} (hs : 0 ≤ slp P d) {θ : ℝ} (h1 : θ ≤ 1) : doctorQ P d θ = 1 := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨⟨h1, le_rfl⟩, fun q hq => ?_⟩, fun q hq => hq.1.2⟩
  rw [Ud_eq, Ud_eq]
  have := mul_nonneg hs (sub_nonneg.2 hq.2)
  linarith

lemma dQ_N {d : Decision} (hs : slp P d < 0) {θ : ℝ} (h1 : θ ≤ 1) : doctorQ P d θ = θ := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨⟨le_rfl, h1⟩, fun q hq => ?_⟩, fun q hq => ?_⟩
  · rw [Ud_eq, Ud_eq]
    have := mul_le_mul_of_nonpos_left hq.1 hs.le
    linarith
  · have h := hq.2 θ ⟨le_rfl, h1⟩
    rw [Ud_eq, Ud_eq] at h
    by_contra hc
    have := mul_lt_mul_of_neg_left (not_le.1 hc) hs
    linarith

lemma OP_iff {d : Decision} : OverPrescribes P d ↔ 0 ≤ slp P d := by
  constructor
  · rintro ⟨θ, hθ, hlt⟩
    by_contra hc
    rw [dQ_N (not_le.1 hc) hθ.2] at hlt
    exact lt_irrefl _ hlt
  · intro hs
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [dQ_O hs zero_le_one]; exact zero_lt_one⟩

/-! ## Expectations for an over-prescribing decision -/

section OPc
variable {d : Decision} (hs : 0 ≤ slp P d)
include hs

lemma sale_O : E1 (fun x => d.p * doctorQ P d x) = d.p := by
  refine (E1L d.p 0 (fun x hx => ?_)).trans (by ring)
  simp only [dQ_O hs hx.2]; ring

lemma doc_O : E1 (fun x => Ud P d x (doctorQ P d x)) =
    slp P d + (P.up + P.od * (1 - d.etaP)) / 2 := by
  refine (E1L (slp P d) (P.up + P.od * (1 - d.etaP)) (fun x hx => ?_)).trans (by ring)
  simp only [dQ_O hs hx.2, Ud_eq]; ring

lemma ccEC_O (y : ℝ × ℝ) : complianceCost P .EC y d = P.k * y.1 / 2 := by
  simp only [complianceCost]
  refine (E2O (P.k * y.1) 0 (-(P.k * y.1)) (fun x hx z => ?_)).trans (by ring)
  simp only [dQ_O hs hx.2]; ring

lemma ccSR_O (y : ℝ × ℝ) : complianceCost P .SR y d = y.2 := by
  simp only [complianceCost]
  refine (E1L y.2 0 (fun x hx => ?_)).trans (by ring)
  simp only [dQ_O hs hx.2]; ring

lemma plSR_O (y : ℝ × ℝ) : plannerSurplus P .SR y d = y.2 - P.k * y.1 / 2 := by
  simp only [plannerSurplus]
  refine (E2O (y.2 - P.k * y.1) 0 (P.k * y.1) (fun x hx z => ?_)).trans (by ring)
  simp only [dQ_O hs hx.2]; ring

lemma env_O (y : ℝ × ℝ) :
    envDisutility P y d = P.epsE * (1 - y.1) + P.epsE * y.1 / 2 := by
  simp only [envDisutility]
  refine (E2O (P.epsE * (1 - y.1)) 0 (P.epsE * y.1) (fun x hx z => ?_)).trans (by ring)
  simp only [dQ_O hs hx.2]; ring

lemma soc_O (y : ℝ × ℝ) : socDisutility P y d = P.epsS * (1 - y.1) / 2 := by
  simp only [socDisutility]
  refine (E2O (P.epsS * (1 - y.1)) 0 (-(P.epsS * (1 - y.1))) (fun x hx z => ?_)).trans
    (by ring)
  simp only [dQ_O hs hx.2]; ring

end OPc

section Nc
variable {d : Decision} (hs : slp P d < 0)
include hs

lemma sale_N : E1 (fun x => d.p * doctorQ P d x) = d.p / 2 := by
  refine (E1L 0 d.p (fun x hx => ?_)).trans (by ring)
  simp only [dQ_N hs hx.2]; ring

lemma doc_N : E1 (fun x => Ud P d x (doctorQ P d x)) = (P.up - d.p + d.etaD) / 2 := by
  refine (E1L 0 (P.up - d.p + d.etaD) (fun x hx => ?_)).trans (by ring)
  simp only [dQ_N hs hx.2, Ud_eq, slp]; ring

lemma ccEC_N (y : ℝ × ℝ) : complianceCost P .EC y d = P.k * y.1 / 6 := by
  simp only [complianceCost]
  refine (E2N 0 (P.k * y.1) (-(P.k * y.1)) (fun x hx z => ?_)).trans (by ring)
  simp only [dQ_N hs hx.2]; ring

lemma ccSR_N (y : ℝ × ℝ) : complianceCost P .SR y d = y.2 / 2 := by
  simp only [complianceCost]
  refine (E1L 0 y.2 (fun x hx => ?_)).trans (by ring)
  simp only [dQ_N hs hx.2]; ring

lemma plSR_N (y : ℝ × ℝ) : plannerSurplus P .SR y d = y.2 / 2 - P.k * y.1 / 6 := by
  simp only [plannerSurplus]
  refine (E2N 0 (y.2 - P.k * y.1) (P.k * y.1) (fun x hx z => ?_)).trans (by ring)
  simp only [dQ_N hs hx.2]; ring

lemma env_N (y : ℝ × ℝ) : envDisutility P y d = P.epsE / 2 - P.epsE * y.1 / 6 := by
  simp only [envDisutility]
  refine (E2N 0 (P.epsE * (1 - y.1)) (P.epsE * y.1) (fun x hx z => ?_)).trans (by ring)
  simp only [dQ_N hs hx.2]; ring

lemma soc_N (y : ℝ × ℝ) : socDisutility P y d = P.epsS * (1 - y.1) / 6 := by
  simp only [socDisutility]
  refine (E2N 0 (P.epsS * (1 - y.1)) (-(P.epsS * (1 - y.1))) (fun x hx z => ?_)).trans
    (by ring)
  simp only [dQ_N hs hx.2]; ring

end Nc

noncomputable def ccN (P : Params) : Model → ℝ × ℝ → ℝ
  | .EC, y => P.k * y.1 / 6
  | .SR, y => y.2 / 2

noncomputable def ccO (P : Params) : Model → ℝ × ℝ → ℝ
  | .EC, y => P.k * y.1 / 2
  | .SR, y => y.2

lemma prof_N {d : Decision} (hs : slp P d < 0) (m : Model) (y : ℝ × ℝ) :
    producerProfit P m y d = d.p / 2 - P.alpha * d.etaD ^ 2 - P.beta * d.etaP ^ 2 - ccN P m y := by
  cases m
  · simp only [producerProfit, sale_N hs, ccEC_N hs, ccN]
  · simp only [producerProfit, sale_N hs, ccSR_N hs, ccN]

lemma prof_O {d : Decision} (hs : 0 ≤ slp P d) (m : Model) (y : ℝ × ℝ) :
    producerProfit P m y d = d.p - P.alpha * d.etaD ^ 2 - P.beta * d.etaP ^ 2 - ccO P m y := by
  cases m
  · simp only [producerProfit, sale_O hs, ccEC_O hs, ccO]
  · simp only [producerProfit, sale_O hs, ccSR_O hs, ccO]

lemma wel_N {d : Decision} (hs : slp P d < 0) (m : Model) (y : ℝ × ℝ) :
    welfare P m y d = (P.up - d.p + d.etaD) / 2 + producerProfit P m y d
      + plannerSurplus P m y d - (P.epsE / 2 - P.epsE * y.1 / 6) - P.epsS * (1 - y.1) / 6 := by
  simp only [welfare, doc_N hs, env_N hs, soc_N hs]

lemma wel_O {d : Decision} (hs : 0 ≤ slp P d) (m : Model) (y : ℝ × ℝ) :
    welfare P m y d = (slp P d + (P.up + P.od * (1 - d.etaP)) / 2) + producerProfit P m y d
      + plannerSurplus P m y d - (P.epsE * (1 - y.1) + P.epsE * y.1 / 2)
      - P.epsS * (1 - y.1) / 2 := by
  simp only [welfare, doc_O hs, env_O hs, soc_O hs]

/-! ## Producer optimum -/

noncomputable def eD (a : ℝ) : ℝ := min 1 (1 / (2 * a))
noncomputable def eP (b o : ℝ) : ℝ := min 1 (o / (2 * b))
noncomputable def eN (a : ℝ) : ℝ := min 1 ((1 / 2) / (2 * a))
noncomputable def VO (a b o : ℝ) : ℝ :=
  eD a - a * eD a ^ 2 - o * (1 - eP b o) - b * eP b o ^ 2
noncomputable def VN0 (a : ℝ) : ℝ := eN a / 2 - a * eN a ^ 2

noncomputable def XX (P : Params) : ℝ := 2 * VO P.alpha P.beta P.od - 2 * VN0 P.alpha - P.up
noncomputable def YY (P : Params) : ℝ := P.up + 2 * VN0 P.alpha
noncomputable def ZZ (P : Params) : ℝ := VO P.alpha P.beta P.od
noncomputable def W0 (P : Params) : ℝ := (P.up + P.od * (1 - eP P.beta P.od)) / 2 + ZZ P

lemma XX_eq (P : Params) : XX P = 2 * ZZ P - YY P := by unfold XX ZZ YY; ring

noncomputable def dO (P : Params) : Decision :=
  ⟨eD P.alpha - P.od * (1 - eP P.beta P.od), eD P.alpha, eP P.beta P.od⟩
noncomputable def dN (P : Params) : Decision := ⟨P.up + eN P.alpha, eN P.alpha, 0⟩

lemma dec_ext {d e : Decision} (h1 : d.p = e.p) (h2 : d.etaD = e.etaD) (h3 : d.etaP = e.etaP) :
    d = e := by
  obtain ⟨_, _, _⟩ := d
  obtain ⟨_, _, _⟩ := e
  simp only [Decision.mk.injEq]
  exact ⟨h1, h2, h3⟩

lemma conc {a c m x : ℝ} (ha : 0 < a) (hk : 0 ≤ (m - x) * (c - 2 * a * m)) :
    c * x - a * x ^ 2 ≤ c * m - a * m ^ 2 ∧ (c * m - a * m ^ 2 ≤ c * x - a * x ^ 2 → x = m) := by
  have e : c * m - a * m ^ 2 - (c * x - a * x ^ 2) = (m - x) * (c - 2 * a * m) + a * (m - x) ^ 2 := by
    ring
  have h2 : 0 ≤ a * (m - x) ^ 2 := by positivity
  refine ⟨by linarith, fun h => ?_⟩
  have h3 : a * (m - x) ^ 2 = 0 := by linarith
  have h4 : (m - x) ^ 2 = 0 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h ha.ne'
    · exact h
  have h5 : m - x = 0 := (pow_eq_zero_iff two_ne_zero).1 h4
  linarith

lemma kkt {a c x : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hx1 : x ≤ 1) :
    0 ≤ (min 1 (c / (2 * a)) - x) * (c - 2 * a * min 1 (c / (2 * a))) := by
  rcases min_cases (1:ℝ) (c / (2 * a)) with ⟨h, hle⟩ | ⟨h, -⟩
  · rw [h]
    have h2 := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * a)).1 hle
    exact mul_nonneg (by linarith) (by linarith)
  · rw [h]
    have ha' : a ≠ 0 := ha.ne'
    have : 2 * a * (c / (2 * a)) = c := by field_simp
    rw [this, sub_self, mul_zero]

lemma minbd {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    0 ≤ min 1 (c / (2 * a)) ∧ min 1 (c / (2 * a)) ≤ 1 :=
  ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩

lemma VN0_pos {a : ℝ} (ha : 0 < a) : 0 < VN0 a := by
  unfold VN0 eN
  have hm : 0 < min 1 ((1 / 2) / (2 * a)) := lt_min one_pos (by positivity)
  have hle : min 1 ((1 / 2) / (2 * a)) ≤ (1 / 2) / (2 * a) := min_le_right _ _
  have h2 := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * a)).1 hle
  have h3 : 0 ≤ min 1 ((1 / 2) / (2 * a)) * (1 / 4 - a * min 1 ((1 / 2) / (2 * a))) :=
    mul_nonneg hm.le (by linarith)
  nlinarith

lemma YY_pos (hP : P.Standing) : 0 < YY P := by
  unfold YY; have := VN0_pos hP.1; linarith [hP.2.2.2.1]

lemma slp_dN (hP : P.Standing) : slp P (dN P) < 0 := by
  obtain ⟨-, -, ho, hu, -⟩ := hP
  simp only [slp, dN]; linarith

lemma slp_dO (P : Params) : 0 ≤ slp P (dO P) := by
  simp only [slp, dO]; linarith

lemma profN (hP : P.Standing) (m : Model) (y : ℝ × ℝ) :
    producerProfit P m y (dN P) = YY P / 2 - ccN P m y := by
  rw [prof_N (slp_dN hP) m y]; simp only [dN, YY, VN0]; ring

lemma profO (P : Params) (m : Model) (y : ℝ × ℝ) :
    producerProfit P m y (dO P) = ZZ P - ccO P m y := by
  rw [prof_O (slp_dO P) m y]; simp only [dO, ZZ, VO]; ring

lemma feas_dN (hP : P.Standing) : DecisionFeasible P (dN P) := by
  have hb := minbd (a := P.alpha) (c := 1 / 2) hP.1 (by norm_num)
  refine ⟨show (0:ℝ) ≤ eN P.alpha from hb.1, show eN P.alpha ≤ 1 from hb.2,
    show (0:ℝ) ≤ 0 from le_rfl, show (0:ℝ) ≤ 1 from zero_le_one, fun x hx => ?_⟩
  rw [dQ_N (slp_dN hP) hx.2, Ud_eq]
  simp only [slp, dN]
  linarith

lemma feas_dO (hP : P.Standing) : DecisionFeasible P (dO P) := by
  obtain ⟨ha, hb, ho, hu, -⟩ := hP
  have bD := minbd (a := P.alpha) (c := 1) ha zero_le_one
  have bP := minbd (a := P.beta) (c := P.od) hb ho.le
  refine ⟨show (0:ℝ) ≤ eD P.alpha from bD.1, show eD P.alpha ≤ 1 from bD.2,
    show (0:ℝ) ≤ eP P.beta P.od from bP.1, show eP P.beta P.od ≤ 1 from bP.2, fun x hx => ?_⟩
  rw [dQ_O (slp_dO P) hx.2, Ud_eq]
  have h1 : 0 ≤ (P.up + P.od * (1 - (dO P).etaP)) * x := by
    refine mul_nonneg ?_ hx.1
    show 0 ≤ P.up + P.od * (1 - eP P.beta P.od)
    have : 0 ≤ P.od * (1 - eP P.beta P.od) := mul_nonneg ho.le (sub_nonneg.2 bP.2)
    linarith
  have h2 := slp_dO P
  linarith

lemma bound_N (hP : P.Standing) {d : Decision} (hf : DecisionFeasible P d)
    (hN : ¬ OverPrescribes P d) (m : Model) (y : ℝ × ℝ) :
    producerProfit P m y d ≤ producerProfit P m y (dN P) ∧
    (producerProfit P m y (dN P) ≤ producerProfit P m y d → d = dN P) := by
  have hP' := hP
  obtain ⟨ha, hb, ho, hu, hk, -, -⟩ := hP'
  obtain ⟨hd0, hd1, hq0, hq1, hx⟩ := hf
  have hs : slp P d < 0 := not_le.1 (fun h => hN (OP_iff.2 h))
  have hp : d.p ≤ P.up + d.etaD := by
    have := hx 1 ⟨zero_le_one, le_rfl⟩
    rw [dQ_N hs le_rfl, Ud_eq] at this
    simp only [slp] at this
    linarith
  have hc := conc (c := 1 / 2) (m := eN P.alpha) (x := d.etaD) ha (kkt ha (by norm_num) hd1)
  have h2 : 0 ≤ P.beta * d.etaP ^ 2 := by positivity
  have hy : YY P = P.up + 2 * (eN P.alpha / 2 - P.alpha * eN P.alpha ^ 2) := rfl
  rw [prof_N hs m y, profN hP]
  refine ⟨by linarith [hc.1], fun hle => ?_⟩
  have e1 : 1 / 2 * eN P.alpha - P.alpha * eN P.alpha ^ 2 ≤
      1 / 2 * d.etaD - P.alpha * d.etaD ^ 2 := by linarith [hc.1]
  have hd := hc.2 e1
  have e2 : P.beta * d.etaP ^ 2 = 0 := by linarith [hc.1]
  have hq : d.etaP = 0 := by
    have h4 : d.etaP ^ 2 = 0 := by
      rcases mul_eq_zero.1 e2 with h | h
      · exact absurd h hb.ne'
      · exact h
    exact (pow_eq_zero_iff two_ne_zero).1 h4
  have hpp : d.p = P.up + eN P.alpha := by linarith [hc.1]
  exact dec_ext hpp hd hq

lemma bound_O (hP : P.Standing) {d : Decision} (hf : DecisionFeasible P d)
    (hO : OverPrescribes P d) (m : Model) (y : ℝ × ℝ) :
    producerProfit P m y d ≤ producerProfit P m y (dO P) ∧
    (producerProfit P m y (dO P) ≤ producerProfit P m y d → d = dO P) := by
  obtain ⟨ha, hb, ho, hu, hk, -, -⟩ := hP
  obtain ⟨hd0, hd1, hq0, hq1, -⟩ := hf
  have hs : 0 ≤ slp P d := OP_iff.1 hO
  have hp : d.p ≤ d.etaD - P.od * (1 - d.etaP) := by simp only [slp] at hs; linarith
  have hcD := conc (c := 1) (m := eD P.alpha) (x := d.etaD) ha (kkt ha zero_le_one hd1)
  have hcP := conc (c := P.od) (m := eP P.beta P.od) (x := d.etaP) hb (kkt hb ho.le hq1)
  have hz : ZZ P = eD P.alpha - P.alpha * eD P.alpha ^ 2 - P.od * (1 - eP P.beta P.od)
      - P.beta * eP P.beta P.od ^ 2 := rfl
  rw [prof_O hs m y, profO]
  refine ⟨by linarith [hcD.1, hcP.1], fun hle => ?_⟩
  have e1 : 1 * eD P.alpha - P.alpha * eD P.alpha ^ 2 ≤ 1 * d.etaD - P.alpha * d.etaD ^ 2 := by
    linarith [hcD.1, hcP.1]
  have e2 : P.od * eP P.beta P.od - P.beta * eP P.beta P.od ^ 2 ≤
      P.od * d.etaP - P.beta * d.etaP ^ 2 := by
    linarith [hcD.1, hcP.1]
  have hd := hcD.2 e1
  have hq := hcP.2 e2
  have hpp : d.p = eD P.alpha - P.od * (1 - eP P.beta P.od) := by
    rw [hd, hq] at hle hp
    linarith [hcD.1, hcP.1]
  exact dec_ext hpp hd hq

lemma opt_iff (hP : P.Standing) (m : Model) (y : ℝ × ℝ) (d : Decision) :
    IsProducerOptimal P m y d ↔
      (d = dN P ∧ producerProfit P m y (dO P) ≤ producerProfit P m y (dN P)) ∨
      (d = dO P ∧ producerProfit P m y (dN P) ≤ producerProfit P m y (dO P)) := by
  constructor
  · rintro ⟨hf, hmax⟩
    by_cases h : OverPrescribes P d
    · have hb := bound_O hP hf h m y
      have := hb.2 (hmax (dO P) (feas_dO hP))
      subst this
      exact Or.inr ⟨rfl, hmax _ (feas_dN hP)⟩
    · have hb := bound_N hP hf h m y
      have := hb.2 (hmax (dN P) (feas_dN hP))
      subst this
      exact Or.inl ⟨rfl, hmax _ (feas_dO hP)⟩
  · rintro (⟨rfl, hle⟩ | ⟨rfl, hle⟩)
    · refine ⟨feas_dN hP, fun a' ha' => ?_⟩
      by_cases h : OverPrescribes P a'
      · exact (bound_O hP ha' h m y).1.trans hle
      · exact (bound_N hP ha' h m y).1
    · refine ⟨feas_dO hP, fun a' ha' => ?_⟩
      by_cases h : OverPrescribes P a'
      · exact (bound_O hP ha' h m y).1
      · exact (bound_N hP ha' h m y).1.trans hle

lemma nOP_dN (hP : P.Standing) : ¬ OverPrescribes P (dN P) :=
  fun h => absurd (OP_iff.1 h) (not_le.2 (slp_dN hP))

lemma OP_dO (P : Params) : OverPrescribes P (dO P) := OP_iff.2 (slp_dO P)

lemma ops_iff (hP : P.Standing) (m : Model) (y : ℝ × ℝ) :
    OPStrictlyMoreProfitable P m y ↔
      producerProfit P m y (dN P) < producerProfit P m y (dO P) := by
  constructor
  · rintro ⟨d, hf, hop, h⟩
    exact (h (dN P) (feas_dN hP) (nOP_dN hP)).trans_le (bound_O hP hf hop m y).1
  · intro h
    exact ⟨dO P, feas_dO hP, OP_dO P, fun d' hf' hn' => (bound_N hP hf' hn' m y).1.trans_lt h⟩

/-! ## Welfare of the two candidate decisions -/

noncomputable def WN (P : Params) (r : ℝ) : ℝ :=
  YY P / 2 - P.k * r / 6 - (P.epsE / 2 - P.epsE * r / 6) - P.epsS * (1 - r) / 6

noncomputable def WO (P : Params) (r : ℝ) : ℝ :=
  W0 P - P.k * r / 2 - (P.epsE * (1 - r) + P.epsE * r / 2) - P.epsS * (1 - r) / 2

lemma welN (hP : P.Standing) (m : Model) (y : ℝ × ℝ) :
    welfare P m y (dN P) = WN P y.1 := by
  rw [wel_N (slp_dN hP) m y, profN hP]
  cases m
  · simp only [plannerSurplus, ccN, dN, WN]; ring
  · rw [plSR_N (slp_dN hP)]; simp only [ccN, dN, WN]; ring

lemma welO (m : Model) (y : ℝ × ℝ) : welfare P m y (dO P) = WO P y.1 := by
  rw [wel_O (slp_dO P) m y, profO]
  cases m
  · simp only [plannerSurplus, ccO, dO, WO, W0, slp]; ring
  · rw [plSR_O (slp_dO P)]; simp only [ccO, dO, WO, W0, slp]; ring

/-! ## Equilibrium sets -/

def ach (P : Params) (m : Model) : Set ℝ :=
  {w | ∃ y d, IsEquilibrium P m y d ∧ welfare P m y d = w}

lemma imw_iff (P : Params) (m : Model) (v : ℝ) : IsMaxWelfare P m v ↔ IsGreatest (ach P m) v := by
  constructor
  · rintro ⟨⟨y, d, h, hw⟩, hle⟩
    exact ⟨⟨y, d, h, hw⟩, by rintro _ ⟨y', d', h', rfl⟩; exact hle y' d' h'⟩
  · rintro ⟨⟨y, d, h, hw⟩, hle⟩
    exact ⟨⟨y, d, h, hw⟩, fun y' d' h' => hle ⟨y', d', h', rfl⟩⟩

noncomputable def NE (P : Params) : Set ℝ :=
  Set.Icc 0 1 ∩ {r | 3 * XX P ≤ 2 * P.k * r} ∩ {r | P.k * r ≤ 3 * YY P}
noncomputable def OE (P : Params) : Set ℝ :=
  Set.Icc 0 1 ∩ {r | 2 * P.k * r ≤ 3 * XX P} ∩ {r | P.k * r ≤ 2 * ZZ P}
noncomputable def NS (P : Params) : Set ℝ :=
  Set.Icc 0 1 ∩ {_r | XX P ≤ YY P} ∩ {r | P.k * r ≤ 3 * YY P}
noncomputable def OS (P : Params) : Set ℝ :=
  Set.Icc 0 1 ∩ {r | P.k * r ≤ 2 * XX P} ∩ {r | P.k * r ≤ 2 * ZZ P}

lemma mNE {r : ℝ} : r ∈ NE P ↔ ((0 ≤ r ∧ r ≤ 1) ∧ 3 * XX P ≤ 2 * P.k * r) ∧
    P.k * r ≤ 3 * YY P := Iff.rfl
lemma mOE {r : ℝ} : r ∈ OE P ↔ ((0 ≤ r ∧ r ≤ 1) ∧ 2 * P.k * r ≤ 3 * XX P) ∧
    P.k * r ≤ 2 * ZZ P := Iff.rfl
lemma mNS {r : ℝ} : r ∈ NS P ↔ ((0 ≤ r ∧ r ≤ 1) ∧ XX P ≤ YY P) ∧
    P.k * r ≤ 3 * YY P := Iff.rfl
lemma mOS {r : ℝ} : r ∈ OS P ↔ ((0 ≤ r ∧ r ≤ 1) ∧ P.k * r ≤ 2 * XX P) ∧
    P.k * r ≤ 2 * ZZ P := Iff.rfl

lemma pfEC {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : PolicyFeasible .EC (r, 0) := ⟨h0, h1, rfl⟩
lemma pfSR {r t : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (ht : 0 ≤ t) : PolicyFeasible .SR (r, t) :=
  ⟨h0, h1, ht⟩

lemma eqN_EC (hP : P.Standing) {y : ℝ × ℝ} (h : IsEquilibrium P .EC y (dN P)) : y.1 ∈ NE P := by
  obtain ⟨⟨hr0, hr1, -⟩, ⟨-, hmax⟩, hpr, -⟩ := h
  have hle := hmax (dO P) (feas_dO hP)
  rw [profN hP, profO] at hle; rw [profN hP] at hpr
  simp only [ccN, ccO] at hle hpr
  have hx := XX_eq P
  exact mNE.2 ⟨⟨⟨hr0, hr1⟩, by linarith⟩, by linarith⟩

lemma eqO_EC (hP : P.Standing) {y : ℝ × ℝ} (h : IsEquilibrium P .EC y (dO P)) : y.1 ∈ OE P := by
  obtain ⟨⟨hr0, hr1, -⟩, ⟨-, hmax⟩, hpr, -⟩ := h
  have hle := hmax (dN P) (feas_dN hP)
  rw [profN hP, profO] at hle; rw [profO] at hpr
  simp only [ccN, ccO] at hle hpr
  have hx := XX_eq P
  exact mOE.2 ⟨⟨⟨hr0, hr1⟩, by linarith⟩, by linarith⟩

lemma eqN_SR (hP : P.Standing) {y : ℝ × ℝ} (h : IsEquilibrium P .SR y (dN P)) : y.1 ∈ NS P := by
  obtain ⟨⟨hr0, hr1, ht⟩, ⟨-, hmax⟩, hpr, hpl⟩ := h
  have hle := hmax (dO P) (feas_dO hP)
  rw [profN hP, profO] at hle; rw [profN hP] at hpr; rw [plSR_N (slp_dN hP)] at hpl
  simp only [ccN, ccO] at hle hpr
  have hx := XX_eq P
  exact mNS.2 ⟨⟨⟨hr0, hr1⟩, by linarith⟩, by linarith⟩

lemma eqO_SR (hP : P.Standing) {y : ℝ × ℝ} (h : IsEquilibrium P .SR y (dO P)) : y.1 ∈ OS P := by
  obtain ⟨⟨hr0, hr1, ht⟩, ⟨-, hmax⟩, hpr, hpl⟩ := h
  have hle := hmax (dN P) (feas_dN hP)
  rw [profN hP, profO] at hle; rw [profO] at hpr; rw [plSR_O (slp_dO P)] at hpl
  simp only [ccN, ccO] at hle hpr
  have hx := XX_eq P
  exact mOS.2 ⟨⟨⟨hr0, hr1⟩, by linarith⟩, by linarith⟩

lemma outN_EC (hP : P.Standing) {r : ℝ} (hr : r ∈ NE P) : IsEquilibrium P .EC (r, 0) (dN P) := by
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := mNE.1 hr
  have hx := XX_eq P
  refine ⟨pfEC h0 h1, (opt_iff hP _ _ _).2 (Or.inl ⟨rfl, ?_⟩), ?_, ?_⟩
  · rw [profN hP, profO]; simp only [ccN, ccO]; linarith
  · rw [profN hP]; simp only [ccN]; linarith
  · simp only [plannerSurplus]; exact le_rfl

lemma outO_EC (hP : P.Standing) {r : ℝ} (hr : r ∈ OE P) : IsEquilibrium P .EC (r, 0) (dO P) := by
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := mOE.1 hr
  have hx := XX_eq P
  refine ⟨pfEC h0 h1, (opt_iff hP _ _ _).2 (Or.inr ⟨rfl, ?_⟩), ?_, ?_⟩
  · rw [profN hP, profO]; simp only [ccN, ccO]; linarith
  · rw [profO]; simp only [ccO]; linarith
  · simp only [plannerSurplus]; exact le_rfl

lemma outN_SR (hP : P.Standing) {r : ℝ} (hr : r ∈ NS P) :
    IsEquilibrium P .SR (r, YY P) (dN P) := by
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := mNS.1 hr
  have hx := XX_eq P
  have hY := YY_pos hP
  refine ⟨pfSR h0 h1 hY.le, (opt_iff hP _ _ _).2 (Or.inl ⟨rfl, ?_⟩), ?_, ?_⟩
  · rw [profN hP, profO]; simp only [ccN, ccO]; linarith
  · rw [profN hP]; simp only [ccN]; linarith
  · rw [plSR_N (slp_dN hP)]; linarith

lemma outO_SR (hP : P.Standing) {r : ℝ} (hr : r ∈ OS P) :
    IsEquilibrium P .SR (r, P.k * r / 2) (dO P) := by
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := mOS.1 hr
  have hx := XX_eq P
  have hkr : 0 ≤ P.k * r := mul_nonneg hP.2.2.2.2.1.le h0
  refine ⟨pfSR h0 h1 (by linarith), (opt_iff hP _ _ _).2 (Or.inr ⟨rfl, ?_⟩), ?_, ?_⟩
  · rw [profN hP, profO]; simp only [ccN, ccO]; linarith
  · rw [profO]; simp only [ccO]; linarith
  · rw [plSR_O (slp_dO P)]; linarith

lemma achEC (hP : P.Standing) : ach P .EC = WN P '' NE P ∪ WO P '' OE P := by
  ext w
  constructor
  · rintro ⟨y, d, h, rfl⟩
    rcases (opt_iff hP _ _ _).1 h.2.1 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl ⟨y.1, eqN_EC hP h, (welN hP _ _).symm⟩
    · exact Or.inr ⟨y.1, eqO_EC hP h, (welO _ _).symm⟩
  · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · exact ⟨(r, 0), dN P, outN_EC hP hr, welN hP _ _⟩
    · exact ⟨(r, 0), dO P, outO_EC hP hr, welO _ _⟩

lemma achSR (hP : P.Standing) : ach P .SR = WN P '' NS P ∪ WO P '' OS P := by
  ext w
  constructor
  · rintro ⟨y, d, h, rfl⟩
    rcases (opt_iff hP _ _ _).1 h.2.1 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl ⟨y.1, eqN_SR hP h, (welN hP _ _).symm⟩
    · exact Or.inr ⟨y.1, eqO_SR hP h, (welO _ _).symm⟩
  · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · exact ⟨_, dN P, outN_SR hP hr, welN hP _ _⟩
    · exact ⟨_, dO P, outO_SR hP hr, welO _ _⟩

/-! ## Compactness and maxima -/

lemma cNE : IsCompact (NE P) :=
  (isCompact_Icc.inter_right (isClosed_le continuous_const (by fun_prop))).inter_right
    (isClosed_le (by fun_prop) continuous_const)
lemma cOE : IsCompact (OE P) :=
  (isCompact_Icc.inter_right (isClosed_le (by fun_prop) continuous_const)).inter_right
    (isClosed_le (by fun_prop) continuous_const)
lemma cNS : IsCompact (NS P) :=
  (isCompact_Icc.inter_right (isClosed_le continuous_const continuous_const)).inter_right
    (isClosed_le (by fun_prop) continuous_const)
lemma cOS : IsCompact (OS P) :=
  (isCompact_Icc.inter_right (isClosed_le (by fun_prop) continuous_const)).inter_right
    (isClosed_le (by fun_prop) continuous_const)

lemma contWN : Continuous (WN P) := by
  show Continuous (fun r => WN P r); simp only [WN]; fun_prop
lemma contWO : Continuous (WO P) := by
  show Continuous (fun r => WO P r); simp only [WO]; fun_prop

lemma greatest_of {S : Set ℝ} (hc : IsCompact S) (hne : S.Nonempty) : IsGreatest S (sSup S) :=
  ⟨hc.sSup_mem hne, fun _ hx => le_csSup hc.bddAbove hx⟩

lemma cpt_EC (hP : P.Standing) : IsCompact (ach P .EC) := by
  rw [achEC hP]; exact (cNE.image contWN).union (cOE.image contWO)

lemma cpt_SR (hP : P.Standing) : IsCompact (ach P .SR) := by
  rw [achSR hP]; exact (cNS.image contWN).union (cOS.image contWO)

lemma ne_EC (hP : P.Standing) : (ach P .EC).Nonempty := by
  rw [achEC hP]
  have hx := XX_eq P
  have hY := YY_pos hP
  by_cases h : XX P ≤ 0
  · exact ⟨WN P 0, Or.inl ⟨0, mNE.2 ⟨⟨⟨le_rfl, zero_le_one⟩, by linarith⟩, by linarith⟩, rfl⟩⟩
  · exact ⟨WO P 0, Or.inr ⟨0, mOE.2 ⟨⟨⟨le_rfl, zero_le_one⟩, by linarith⟩, by linarith⟩, rfl⟩⟩

lemma ne_SR (hP : P.Standing) : (ach P .SR).Nonempty := by
  rw [achSR hP]
  have hx := XX_eq P
  have hY := YY_pos hP
  by_cases h : XX P ≤ YY P
  · exact ⟨WN P 0, Or.inl ⟨0, mNS.2 ⟨⟨⟨le_rfl, zero_le_one⟩, h⟩, by linarith⟩, rfl⟩⟩
  · exact ⟨WO P 0, Or.inr ⟨0, mOS.2 ⟨⟨⟨le_rfl, zero_le_one⟩, by linarith⟩, by linarith⟩, rfl⟩⟩

lemma greatest (hP : P.Standing) (m : Model) : IsGreatest (ach P m) (sSup (ach P m)) := by
  cases m
  · exact greatest_of (cpt_EC hP) (ne_EC hP)
  · exact greatest_of (cpt_SR hP) (ne_SR hP)

lemma wal_of (hP : P.Standing) {m1 m2 : Model} (h : sSup (ach P m2) ≤ sSup (ach P m1)) :
    WelfareAtLeast P m1 m2 :=
  ⟨_, _, (imw_iff _ _ _).2 (greatest hP m1), (imw_iff _ _ _).2 (greatest hP m2), h⟩

lemma OE_OS (hP : P.Standing) {r : ℝ} (hr : r ∈ OE P) : r ∈ OS P := by
  have hk : 0 < P.k := hP.2.2.2.2.1
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := mOE.1 hr
  have hkr : 0 ≤ P.k * r := mul_nonneg hk.le h0
  exact mOS.2 ⟨⟨⟨h0, h1⟩, by linarith⟩, h3⟩

lemma sub_ECSR (hP : P.Standing) (hus : XX P ≤ YY P) : ach P .EC ⊆ ach P .SR := by
  rw [achEC hP, achSR hP]
  rintro x (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
  · obtain ⟨⟨h01, -⟩, h3⟩ := mNE.1 hr
    exact Or.inl ⟨r, mNS.2 ⟨⟨h01, hus⟩, h3⟩, rfl⟩
  · exact Or.inr ⟨r, OE_OS hP hr, rfl⟩

lemma NE_empty1 (hP : P.Standing) (h : 2 * YY P < XX P) : NE P = ∅ := by
  ext r; simp only [Set.mem_empty_iff_false, iff_false]
  intro hr
  obtain ⟨⟨-, h2⟩, h3⟩ := mNE.1 hr
  linarith

lemma NE_empty2 (hP : P.Standing) (hkb : 2 * P.k < 3 * XX P) : NE P = ∅ := by
  have hk : 0 < P.k := hP.2.2.2.2.1
  ext r; simp only [Set.mem_empty_iff_false, iff_false]
  intro hr
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, -⟩ := mNE.1 hr
  have : P.k * r ≤ P.k := mul_le_of_le_one_right hk.le h1
  linarith

lemma NS_empty (hus : YY P < XX P) : NS P = ∅ := by
  ext r; simp only [Set.mem_empty_iff_false, iff_false]
  intro hr
  obtain ⟨⟨-, h2⟩, -⟩ := mNS.1 hr
  linarith

lemma OE_eq_OS1 (hP : P.Standing) (h : 2 * YY P < XX P) : OE P = OS P := by
  have hx := XX_eq P
  have hY := YY_pos hP
  ext r; rw [mOE, mOS]
  constructor
  · rintro ⟨⟨h01, -⟩, h3⟩
    exact ⟨⟨h01, by linarith⟩, h3⟩
  · rintro ⟨⟨h01, -⟩, h3⟩
    exact ⟨⟨h01, by linarith⟩, h3⟩

lemma OE_eq_OS2 (hP : P.Standing) (hkb : 2 * P.k < 3 * XX P) : OE P = OS P := by
  have hk : 0 < P.k := hP.2.2.2.2.1
  ext r; rw [mOE, mOS]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, -⟩, h3⟩
    have : P.k * r ≤ P.k := mul_le_of_le_one_right hk.le h1
    exact ⟨⟨⟨h0, h1⟩, by linarith⟩, h3⟩
  · rintro ⟨⟨⟨h0, h1⟩, -⟩, h3⟩
    have : P.k * r ≤ P.k := mul_le_of_le_one_right hk.le h1
    exact ⟨⟨⟨h0, h1⟩, by linarith⟩, h3⟩

/-! ## Varying the disutilities -/

def Q (P : Params) (e s : ℝ) : Params := ⟨P.alpha, P.beta, P.od, P.up, P.k, e, s⟩

lemma stQ (hP : P.Standing) {e s : ℝ} (he : 0 ≤ e) (hs : 0 ≤ s) : (Q P e s).Standing :=
  ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2.1, he, hs⟩

lemma WN_Q (P : Params) (e s r : ℝ) :
    WN (Q P e s) r = YY P / 2 - P.k * r / 6 - (e / 2 - e * r / 6) - s * (1 - r) / 6 := rfl
lemma WO_Q (P : Params) (e s r : ℝ) :
    WO (Q P e s) r = W0 P - P.k * r / 2 - (e * (1 - r) + e * r / 2) - s * (1 - r) / 2 := rfl

noncomputable def rN (P : Params) : ℝ := min 1 (3 * YY P / P.k)

lemma rN_pos (hP : P.Standing) : 0 < rN P :=
  lt_min one_pos (div_pos (by linarith [YY_pos hP]) hP.2.2.2.2.1)

lemma rN_le1 : rN P ≤ 1 := min_le_left _ _

lemma rN_ge (hP : P.Standing) {r : ℝ} (h1 : r ≤ 1) (h2 : P.k * r ≤ 3 * YY P) : r ≤ rN P := by
  have hk : 0 < P.k := hP.2.2.2.2.1
  exact le_min h1 (by rw [le_div_iff₀ hk]; linarith)

lemma rN_mem (hP : P.Standing) (h2 : XX P ≤ 2 * YY P) (hkb : 3 * XX P ≤ 2 * P.k) : rN P ∈ NE P := by
  have hk : 0 < P.k := hP.2.2.2.2.1
  have hrN := rN_pos hP
  rcases min_cases (1:ℝ) (3 * YY P / P.k) with ⟨h, hle⟩ | ⟨h, -⟩
  · have e : rN P = 1 := h
    have := (le_div_iff₀ hk).1 hle
    refine mNE.2 ⟨⟨⟨hrN.le, rN_le1⟩, ?_⟩, ?_⟩ <;> rw [e] <;> linarith
  · have e : rN P = 3 * YY P / P.k := h
    have hk0 : P.k ≠ 0 := hk.ne'
    have hkr : P.k * rN P = 3 * YY P := by rw [e]; field_simp
    exact mNE.2 ⟨⟨⟨hrN.le, rN_le1⟩, by linarith⟩, by linarith⟩

noncomputable def Tb (P : Params) (s : ℝ) : ℝ :=
  P.k + (6 * |W0 P - YY P / 2| + P.k + s) / rN P

lemma Tb_nonneg (hP : P.Standing) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ Tb P s := by
  have hk : 0 < P.k := hP.2.2.2.2.1
  have hrN := rN_pos hP
  have : 0 ≤ (6 * |W0 P - YY P / 2| + P.k + s) / rN P := by positivity
  unfold Tb; linarith

lemma key (hP : P.Standing) {e s r : ℝ} (hs : 0 ≤ s) (he : Tb P s ≤ e)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : WO (Q P e s) r ≤ WN (Q P e s) (rN P) := by
  have hk : 0 < P.k := hP.2.2.2.2.1
  have hrN := rN_pos hP
  have hrN1 : rN P ≤ 1 := rN_le1
  have hC : 6 * |W0 P - YY P / 2| + P.k + s ≤ (e - P.k) * rN P := by
    have : (6 * |W0 P - YY P / 2| + P.k + s) / rN P ≤ e - P.k := by unfold Tb at he; linarith
    rwa [div_le_iff₀ hrN] at this
  have he0 : 0 ≤ e := (Tb_nonneg hP hs).trans he
  have a1 := le_abs_self (W0 P - YY P / 2)
  have a3 : 0 ≤ P.k * r := mul_nonneg hk.le hr0
  have a4 : 0 ≤ e * (1 - r) := mul_nonneg he0 (by linarith)
  have a5 : 0 ≤ s * (1 - r) := mul_nonneg hs (by linarith)
  have a6 : 0 ≤ s * rN P := mul_nonneg hs hrN.le
  rw [WN_Q, WO_Q]
  nlinarith

lemma envelope {K : Set ℝ} (V : ℝ → ℝ → ℝ) (M : ℝ → ℝ) {lo hi e1 e2 : ℝ}
    (hV : ∀ r ∈ K, lo * (e2 - e1) ≤ V e2 r - V e1 r ∧ V e2 r - V e1 r ≤ hi * (e2 - e1))
    (h1 : IsGreatest ((V e1) '' K) (M e1)) (h2 : IsGreatest ((V e2) '' K) (M e2)) :
    lo * (e2 - e1) ≤ M e2 - M e1 ∧ M e2 - M e1 ≤ hi * (e2 - e1) := by
  obtain ⟨r1, hr1, hm1⟩ := h1.1
  obtain ⟨r2, hr2, hm2⟩ := h2.1
  have a1 : V e2 r1 ≤ M e2 := h2.2 ⟨r1, hr1, rfl⟩
  have a2 : V e1 r2 ≤ M e1 := h1.2 ⟨r2, hr2, rfl⟩
  have b1 := hV r1 hr1
  have b2 := hV r2 hr2
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]

lemma threshold (A B : ℝ → ℝ)
    (hmono : ∀ e1 e2, 0 ≤ e1 → e1 ≤ e2 → B e2 - B e1 ≤ A e2 - A e1)
    (hlip : ∀ e1 e2, 0 ≤ e1 → e1 ≤ e2 → (A e2 - B e2) - (A e1 - B e1) ≤ 2 * (e2 - e1))
    (e0 : ℝ) (he0 : 0 ≤ e0) (h0 : B e0 ≤ A e0) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ e, 0 ≤ e → (T ≤ e → B e ≤ A e) ∧ (e < T → A e < B e) := by
  let S : Set ℝ := {e | 0 ≤ e ∧ B e ≤ A e}
  have hne : S.Nonempty := ⟨e0, he0, h0⟩
  have hbdd : BddBelow S := ⟨0, fun x hx => hx.1⟩
  have hT0 : 0 ≤ sInf S := le_csInf hne (fun x hx => hx.1)
  have hTS : B (sInf S) ≤ A (sInf S) := by
    by_contra hcon
    have hcon' := not_le.1 hcon
    obtain ⟨s, hs, hlt⟩ := exists_lt_of_csInf_lt hne
      (show sInf S < sInf S + (B (sInf S) - A (sInf S)) / 4 by linarith)
    have hle : sInf S ≤ s := csInf_le hbdd hs
    have h3 := hlip (sInf S) s hT0 hle
    have h4 : B s ≤ A s := hs.2
    linarith
  refine ⟨sInf S, hT0, fun e he => ⟨fun hTe => ?_, fun heT => ?_⟩⟩
  · have := hmono (sInf S) e hT0 hTe; linarith
  · by_contra hcon
    exact absurd (csInf_le hbdd ⟨he, not_lt.1 hcon⟩) (not_le.2 heT)

lemma thr {s : ℝ} {K1 K2 : Set ℝ}
    (c1 : IsCompact K1) (c2 : IsCompact K2) (n1 : K1.Nonempty) (n2 : K2.Nonempty)
    (s1 : K1 ⊆ Set.Icc 0 1) (s2 : K2 ⊆ Set.Icc 0 1)
    {e0 r0 : ℝ} (he0 : 0 ≤ e0) (hr0 : r0 ∈ K1)
    (hbig : ∀ r ∈ K2, WO (Q P e0 s) r ≤ WN (Q P e0 s) r0) :
    ∃ T, 0 ≤ T ∧ ∀ e, 0 ≤ e →
      (T ≤ e → sSup (WO (Q P e s) '' K2) ≤ sSup (WN (Q P e s) '' K1)) ∧
      (e < T → sSup (WN (Q P e s) '' K1) < sSup (WO (Q P e s) '' K2)) := by
  have hAg : ∀ e, IsGreatest (WN (Q P e s) '' K1) (sSup (WN (Q P e s) '' K1)) := fun e =>
    greatest_of (c1.image contWN) (n1.image _)
  have hBg : ∀ e, IsGreatest (WO (Q P e s) '' K2) (sSup (WO (Q P e s) '' K2)) := fun e =>
    greatest_of (c2.image contWO) (n2.image _)
  have slN : ∀ e1 e2 : ℝ, e1 ≤ e2 → ∀ r ∈ K1,
      (-1/2) * (e2 - e1) ≤ WN (Q P e2 s) r - WN (Q P e1 s) r ∧
      WN (Q P e2 s) r - WN (Q P e1 s) r ≤ (-1/3) * (e2 - e1) := by
    intro e1 e2 h12 r hr
    obtain ⟨h0, h1⟩ := s1 hr
    have i1 := mul_nonneg (sub_nonneg.2 h12) h0
    have i2 := mul_nonneg (sub_nonneg.2 h12) (sub_nonneg.2 h1)
    rw [WN_Q, WN_Q]
    constructor <;> nlinarith
  have slO : ∀ e1 e2 : ℝ, e1 ≤ e2 → ∀ r ∈ K2,
      (-1) * (e2 - e1) ≤ WO (Q P e2 s) r - WO (Q P e1 s) r ∧
      WO (Q P e2 s) r - WO (Q P e1 s) r ≤ (-1/2) * (e2 - e1) := by
    intro e1 e2 h12 r hr
    obtain ⟨h0, h1⟩ := s2 hr
    have i1 := mul_nonneg (sub_nonneg.2 h12) h0
    have i2 := mul_nonneg (sub_nonneg.2 h12) (sub_nonneg.2 h1)
    rw [WO_Q, WO_Q]
    constructor <;> nlinarith
  have h0 : sSup (WO (Q P e0 s) '' K2) ≤ sSup (WN (Q P e0 s) '' K1) := by
    obtain ⟨r, hr, hrw⟩ := (hBg e0).1
    rw [← hrw]
    exact (hbig r hr).trans ((hAg e0).2 ⟨r0, hr0, rfl⟩)
  exact threshold (fun e => sSup (WN (Q P e s) '' K1)) (fun e => sSup (WO (Q P e s) '' K2))
    (fun e1 e2 _ h12 => by
      have a := envelope (K := K1) (fun e r => WN (Q P e s) r)
        (fun e => sSup (WN (Q P e s) '' K1)) (slN e1 e2 h12) (hAg e1) (hAg e2)
      have b := envelope (K := K2) (fun e r => WO (Q P e s) r)
        (fun e => sSup (WO (Q P e s) '' K2)) (slO e1 e2 h12) (hBg e1) (hBg e2)
      try simp only at a b ⊢
      linarith [a.1, b.2])
    (fun e1 e2 _ h12 => by
      have a := envelope (K := K1) (fun e r => WN (Q P e s) r)
        (fun e => sSup (WN (Q P e s) '' K1)) (slN e1 e2 h12) (hAg e1) (hAg e2)
      have b := envelope (K := K2) (fun e r => WO (Q P e s) r)
        (fun e => sSup (WO (Q P e s) '' K2)) (slO e1 e2 h12) (hBg e1) (hBg e2)
      try simp only at a b ⊢
      linarith [a.2, b.1])
    e0 he0 h0

/-! ## Eliminating over-prescription under EC -/

lemma elim_iff (hP : P.Standing) (hNE : (NE P).Nonempty) :
    EliminationOptimal P .EC ↔ ∀ r ∈ OE P, WO P r ≤ sSup (WN P '' NE P) := by
  have gA := greatest_of ((cNE (P := P)).image (contWN (P := P))) (hNE.image _)
  constructor
  · rintro ⟨y, d, h, hnop, hmax⟩ r hr
    rcases (opt_iff hP _ _ _).1 h.2.1 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · have h1 := hmax (r, 0) (dO P) (outO_EC hP hr)
      rw [welO, welN hP] at h1
      exact h1.trans (gA.2 ⟨y.1, eqN_EC hP h, rfl⟩)
    · exact absurd (OP_dO P) hnop
  · intro hall
    obtain ⟨r1, hr1, hv⟩ := gA.1
    refine ⟨(r1, 0), dN P, outN_EC hP hr1, nOP_dN hP, fun y' d' h' => ?_⟩
    have hw : welfare P .EC y' d' ∈ ach P .EC := ⟨y', d', h', rfl⟩
    rw [achEC hP] at hw
    have hbound : welfare P .EC y' d' ≤ sSup (WN P '' NE P) := by
      rcases hw with ⟨r, hr, hrw⟩ | ⟨r, hr, hrw⟩
      · rw [← hrw]; exact gA.2 ⟨r, hr, rfl⟩
      · rw [← hrw]; exact hall r hr
    calc welfare P .EC y' d' ≤ sSup (WN P '' NE P) := hbound
      _ = WN P r1 := hv.symm
      _ = welfare P .EC (r1, 0) (dN P) := (welN hP .EC (r1, 0)).symm

lemma elim_big (hP : P.Standing) (h2 : XX P ≤ 2 * YY P) (hk : 3 * XX P ≤ 2 * P.k)
    {e s : ℝ} (hs : 0 ≤ s) (he : Tb P s ≤ e) : EliminationOptimal (Q P e s) .EC := by
  have he0 : 0 ≤ e := (Tb_nonneg hP hs).trans he
  have hQ := stQ hP he0 hs
  have hNE : (NE P).Nonempty := ⟨rN P, rN_mem hP h2 hk⟩
  rw [elim_iff hQ hNE]
  change ∀ r ∈ OE P, WO (Q P e s) r ≤ sSup (WN (Q P e s) '' NE P)
  intro r hr
  obtain ⟨⟨⟨h0, h1⟩, -⟩, -⟩ := mOE.1 hr
  exact (key hP hs he h0 h1).trans
    (le_csSup ((cNE (P := P)).image (contWN (P := Q P e s))).bddAbove ⟨rN P, rN_mem hP h2 hk, rfl⟩)

lemma exists_ET (hP : P.Standing) (h2 : XX P ≤ 2 * YY P) (hk : 3 * XX P ≤ 2 * P.k)
    {s : ℝ} (hs : 0 ≤ s) :
    ∃ T, 0 ≤ T ∧ ∀ e, 0 ≤ e → (EliminationOptimal (Q P e s) .EC ↔ T ≤ e) := by
  have hNE : (NE P).Nonempty := ⟨rN P, rN_mem hP h2 hk⟩
  have sNE : NE P ⊆ Set.Icc 0 1 := fun r hr => (mNE.1 hr).1.1
  have sOE : OE P ⊆ Set.Icc 0 1 := fun r hr => (mOE.1 hr).1.1
  by_cases hOE : (OE P).Nonempty
  · obtain ⟨T, hT0, hT⟩ := thr (s := s) cNE cOE hNE hOE sNE sOE (Tb_nonneg hP hs)
      (rN_mem hP h2 hk) (fun r hr => key hP hs le_rfl (sOE hr).1 (sOE hr).2)
    refine ⟨T, hT0, fun e he => ?_⟩
    have hQ := stQ hP he hs
    rw [elim_iff hQ hNE]
    change (∀ r ∈ OE P, WO (Q P e s) r ≤ sSup (WN (Q P e s) '' NE P)) ↔ T ≤ e
    have gB := greatest_of ((cOE (P := P)).image (contWO (P := Q P e s))) (hOE.image _)
    constructor
    · intro hall
      by_contra hlt
      have h3 := (hT e he).2 (not_le.1 hlt)
      obtain ⟨r, hr, hrv⟩ := gB.1
      have h4 := hall r hr
      rw [hrv] at h4
      linarith
    · intro hTe r hr
      exact (gB.2 ⟨r, hr, rfl⟩).trans ((hT e he).1 hTe)
  · refine ⟨0, le_rfl, fun e he => ?_⟩
    rw [elim_iff (stQ hP he hs) hNE]
    exact ⟨fun _ => he, fun _ r hr => absurd ⟨r, hr⟩ hOE⟩

/-! ## The thresholds -/

noncomputable def uECt (a b o : ℝ) : ℝ := (2 * VO a b o - 6 * VN0 a) / 3
noncomputable def uSRt (a b o : ℝ) : ℝ := VO a b o - 2 * VN0 a
noncomputable def uECf (a b o : ℝ) : ℝ := if 0 < uECt a b o then uECt a b o else -1
noncomputable def uSRf (a b o : ℝ) : ℝ := if 0 < uSRt a b o then uSRt a b o else 0
noncomputable def kbarf (a b o u : ℝ) : ℝ := 3 * (2 * VO a b o - 2 * VN0 a - u) / 2

noncomputable def epsBar (a b o u k s : ℝ) : ℝ :=
  sInf {e | 0 ≤ e ∧ EliminationOptimal ⟨a, b, o, u, k, e, s⟩ .EC}

def Good (a b o u k s T : ℝ) : Prop :=
  epsBar a b o u k s ≤ T ∧ ∀ e : ℝ, 0 ≤ e →
    (T ≤ e → WelfareAtLeast ⟨a, b, o, u, k, e, s⟩ .EC .SR) ∧
    (e < T → WelfareAtLeast ⟨a, b, o, u, k, e, s⟩ .SR .EC)

open Classical in
noncomputable def epsTil (a b o u k s : ℝ) : ℝ :=
  if h : ∃ T, Good a b o u k s T then Classical.choose h else 0

lemma uEC_le (hP : P.Standing) : uECf P.alpha P.beta P.od ≤ P.up ↔ XX P ≤ 2 * YY P := by
  have hu := hP.2.2.2.1
  have hv := VN0_pos hP.1
  unfold uECf uECt XX YY
  split_ifs with h
  · constructor <;> intro <;> linarith
  · constructor <;> intro <;> linarith [not_lt.1 h]

lemma uSR_le (hP : P.Standing) : uSRf P.alpha P.beta P.od ≤ P.up ↔ XX P ≤ YY P := by
  have hu := hP.2.2.2.1
  have hv := VN0_pos hP.1
  unfold uSRf uSRt XX YY
  split_ifs with h
  · constructor <;> intro <;> linarith
  · constructor <;> intro <;> linarith [not_lt.1 h]

lemma kbar_le : kbarf P.alpha P.beta P.od P.up ≤ P.k ↔ 3 * XX P ≤ 2 * P.k := by
  unfold kbarf XX
  constructor <;> intro <;> linarith

lemma uEC_lt_uSR {a b o : ℝ} (ha : 0 < a) : uECf a b o < uSRf a b o := by
  have hv := VN0_pos ha
  unfold uECf uSRf uECt uSRt
  split_ifs with h1 h2 h2 <;> linarith

lemma mono_s (hP : P.Standing) (h2 : XX P ≤ 2 * YY P) (hk : 3 * XX P ≤ 2 * P.k)
    {e s s' : ℝ} (he : 0 ≤ e) (hs : 0 ≤ s) (hss : s ≤ s')
    (h : EliminationOptimal (Q P e s) .EC) : EliminationOptimal (Q P e s') .EC := by
  have hNE : (NE P).Nonempty := ⟨rN P, rN_mem hP h2 hk⟩
  have hkP : 0 < P.k := hP.2.2.2.2.1
  rw [elim_iff (stQ hP he hs) hNE] at h
  rw [elim_iff (stQ hP he (hs.trans hss)) hNE]
  change ∀ r ∈ OE P, WO (Q P e s) r ≤ sSup (WN (Q P e s) '' NE P) at h
  change ∀ r ∈ OE P, WO (Q P e s') r ≤ sSup (WN (Q P e s') '' NE P)
  obtain ⟨r1, hr1, hv⟩ :=
    (greatest_of ((cNE (P := P)).image (contWN (P := Q P e s))) (hNE.image _)).1
  intro r hr
  have h0 := h r hr
  rw [← hv] at h0
  obtain ⟨⟨⟨a0, a1⟩, a2⟩, -⟩ := mOE.1 hr
  obtain ⟨⟨⟨b0, b1⟩, b2⟩, -⟩ := mNE.1 hr1
  have hle : r ≤ r1 := by
    have : P.k * r ≤ P.k * r1 := by linarith
    exact le_of_mul_le_mul_left this hkP
  refine le_trans ?_ (le_csSup ((cNE (P := P)).image (contWN (P := Q P e s'))).bddAbove
    ⟨r1, hr1, rfl⟩)
  rw [WO_Q, WN_Q] at h0
  rw [WO_Q, WN_Q]
  have m1 := mul_nonneg (sub_nonneg.2 hss) (sub_nonneg.2 hle)
  have m2 := mul_nonneg (sub_nonneg.2 hss) (sub_nonneg.2 b1)
  nlinarith

lemma epsBar_eq (hP : P.Standing) (h2 : XX P ≤ 2 * YY P) (hk : 3 * XX P ≤ 2 * P.k)
    {s : ℝ} (hs : 0 ≤ s) :
    ∃ T, 0 ≤ T ∧ (∀ e, 0 ≤ e → (EliminationOptimal (Q P e s) .EC ↔ T ≤ e)) ∧
      epsBar P.alpha P.beta P.od P.up P.k s = T := by
  obtain ⟨T, hT0, hT⟩ := exists_ET hP h2 hk hs
  refine ⟨T, hT0, hT, ?_⟩
  have hS : {e | 0 ≤ e ∧ EliminationOptimal (⟨P.alpha, P.beta, P.od, P.up, P.k, e, s⟩ : Params) .EC}
      = Set.Ici T := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    constructor
    · rintro ⟨he, h⟩; exact (hT e he).1 h
    · intro h; exact ⟨hT0.trans h, (hT e (hT0.trans h)).2 h⟩
  unfold epsBar
  rw [hS, csInf_Ici]

lemma caseA_big (hP : P.Standing) (h2 : XX P ≤ 2 * YY P) (hk : 3 * XX P ≤ 2 * P.k)
    (hA : XX P ≤ YY P) {e : ℝ} (he : Tb P P.epsS ≤ e) :
    WelfareAtLeast (Q P e P.epsS) .EC .SR := by
  have hs : 0 ≤ P.epsS := hP.2.2.2.2.2.2
  have hkP : 0 < P.k := hP.2.2.2.2.1
  have he0 : 0 ≤ e := (Tb_nonneg hP hs).trans he
  have hQ := stQ hP he0 hs
  have hrNm := rN_mem hP h2 hk
  have hrN := rN_pos hP
  have hX0 : 0 ≤ e + P.epsS - P.k := by
    have : 0 ≤ (6 * |W0 P - YY P / 2| + P.k + P.epsS) / rN P := by positivity
    unfold Tb at he; linarith
  have hSR : ∀ x ∈ ach (Q P e P.epsS) .SR, x ≤ WN (Q P e P.epsS) (rN P) := by
    rw [achSR hQ]
    rintro x (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · have hr' : r ∈ NS P := hr
      obtain ⟨⟨⟨h0, h1⟩, -⟩, h3⟩ := mNS.1 hr'
      have hle : r ≤ rN P := rN_ge hP h1 h3
      have := mul_nonneg (sub_nonneg.2 hle) hX0
      rw [WN_Q, WN_Q]
      nlinarith
    · have hr' : r ∈ OS P := hr
      obtain ⟨⟨⟨h0, h1⟩, -⟩, -⟩ := mOS.1 hr'
      exact key hP hs he h0 h1
  have hwEC : WN (Q P e P.epsS) (rN P) ∈ ach (Q P e P.epsS) .EC := by
    rw [achEC hQ]; exact Or.inl ⟨rN P, hrNm, rfl⟩
  exact wal_of hQ (csSup_le (ne_SR hQ)
    (fun x hx => (hSR x hx).trans (le_csSup (cpt_EC hQ).bddAbove hwEC)))

lemma exists_good (hP : P.Standing) (h2 : XX P ≤ 2 * YY P) (hk : 3 * XX P ≤ 2 * P.k) :
    ∃ T, Good P.alpha P.beta P.od P.up P.k P.epsS T := by
  have hs : 0 ≤ P.epsS := hP.2.2.2.2.2.2
  have hNE : (NE P).Nonempty := ⟨rN P, rN_mem hP h2 hk⟩
  by_cases hA : XX P ≤ YY P
  · refine ⟨max (Tb P P.epsS) (epsBar P.alpha P.beta P.od P.up P.k P.epsS), le_max_right _ _,
      fun e he => ⟨fun hTe => ?_, fun _ => ?_⟩⟩
    · exact caseA_big hP h2 hk hA ((le_max_left _ _).trans hTe)
    · have hQ := stQ hP he hs
      exact wal_of hQ (csSup_le_csSup (cpt_SR hQ).bddAbove (ne_EC hQ) (sub_ECSR hQ hA))
  · have hB : YY P < XX P := not_le.1 hA
    have hx := XX_eq P
    have hY := YY_pos hP
    have hOS : (OS P).Nonempty :=
      ⟨0, mOS.2 ⟨⟨⟨le_rfl, zero_le_one⟩, by linarith⟩, by linarith⟩⟩
    have sNE : NE P ⊆ Set.Icc 0 1 := fun r hr => (mNE.1 hr).1.1
    have sOS : OS P ⊆ Set.Icc 0 1 := fun r hr => (mOS.1 hr).1.1
    obtain ⟨T, hT0, hT⟩ := thr (s := P.epsS) cNE cOS hNE hOS sNE sOS (Tb_nonneg hP hs)
      (rN_mem hP h2 hk) (fun r hr => key hP hs le_rfl (sOS hr).1 (sOS hr).2)
    refine ⟨T, ?_, fun e he => ⟨fun hTe => ?_, fun heT => ?_⟩⟩
    · unfold epsBar
      apply csInf_le ⟨0, fun x hx => hx.1⟩
      refine ⟨hT0, ?_⟩
      show EliminationOptimal (Q P T P.epsS) .EC
      rw [elim_iff (stQ hP hT0 hs) hNE]
      change ∀ r ∈ OE P, WO (Q P T P.epsS) r ≤ sSup (WN (Q P T P.epsS) '' NE P)
      intro r hr
      have gB := greatest_of ((cOS (P := P)).image (contWO (P := Q P T P.epsS))) (hOS.image _)
      exact (gB.2 ⟨r, OE_OS hP hr, rfl⟩).trans ((hT T hT0).1 le_rfl)
    · have hQ := stQ hP he hs
      show WelfareAtLeast (Q P e P.epsS) .EC .SR
      apply wal_of hQ
      have gA := greatest_of ((cNE (P := P)).image (contWN (P := Q P e P.epsS))) (hNE.image _)
      have gB := greatest_of ((cOS (P := P)).image (contWO (P := Q P e P.epsS))) (hOS.image _)
      obtain ⟨r1, hr1, hv⟩ := gA.1
      have hmem : WN (Q P e P.epsS) r1 ∈ ach (Q P e P.epsS) .EC := by
        rw [achEC hQ]; exact Or.inl ⟨r1, hr1, rfl⟩
      apply csSup_le (ne_SR hQ)
      intro x hx
      rw [achSR hQ] at hx
      rcases hx with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
      · have hr' : r ∈ NS P := hr
        rw [NS_empty hB] at hr'
        simp at hr'
      · calc WO (Q P e P.epsS) r ≤ sSup (WO (Q P e P.epsS) '' OS P) := gB.2 ⟨r, hr, rfl⟩
          _ ≤ sSup (WN (Q P e P.epsS) '' NE P) := (hT e he).1 hTe
          _ = WN (Q P e P.epsS) r1 := hv.symm
          _ ≤ sSup (ach (Q P e P.epsS) .EC) := le_csSup (cpt_EC hQ).bddAbove hmem
    · have hQ := stQ hP he hs
      show WelfareAtLeast (Q P e P.epsS) .SR .EC
      apply wal_of hQ
      have gA := greatest_of ((cNE (P := P)).image (contWN (P := Q P e P.epsS))) (hNE.image _)
      have gB := greatest_of ((cOS (P := P)).image (contWO (P := Q P e P.epsS))) (hOS.image _)
      obtain ⟨r2, hr2, hv2⟩ := gB.1
      have hmem : WO (Q P e P.epsS) r2 ∈ ach (Q P e P.epsS) .SR := by
        rw [achSR hQ]; exact Or.inr ⟨r2, hr2, rfl⟩
      apply csSup_le (ne_EC hQ)
      intro x hx
      rw [achEC hQ] at hx
      rcases hx with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
      · calc WN (Q P e P.epsS) r ≤ sSup (WN (Q P e P.epsS) '' NE P) := gA.2 ⟨r, hr, rfl⟩
          _ ≤ sSup (WO (Q P e P.epsS) '' OS P) := ((hT e he).2 heT).le
          _ = WO (Q P e P.epsS) r2 := hv2.symm
          _ ≤ sSup (ach (Q P e P.epsS) .SR) := le_csSup (cpt_SR hQ).bddAbove hmem
      · exact le_csSup (cpt_SR hQ).bddAbove
          (by rw [achSR hQ]; exact Or.inr ⟨r, OE_OS hP hr, rfl⟩)

lemma epsTil_spec (hP : P.Standing) (h2 : XX P ≤ 2 * YY P) (hk : 3 * XX P ≤ 2 * P.k) :
    Good P.alpha P.beta P.od P.up P.k P.epsS (epsTil P.alpha P.beta P.od P.up P.k P.epsS) := by
  have hex := exists_good hP h2 hk
  unfold epsTil
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-! ## The clauses -/

lemma c1 (hP : P.Standing) (h : P.up < uECf P.alpha P.beta P.od) {y : ℝ × ℝ}
    (hy : PolicyFeasible .EC y) (hn : NonnegOptimalProfit P .EC y) :
    OPStrictlyMoreProfitable P .EC y := by
  have hX : 2 * YY P < XX P := by
    have h' : ¬ (uECf P.alpha P.beta P.od ≤ P.up) := not_le.2 h
    rw [uEC_le hP] at h'; exact not_le.1 h'
  rw [ops_iff hP]
  by_contra hc
  have hc' := not_lt.1 hc
  obtain ⟨d, ⟨hf, -⟩, hpr⟩ := hn
  have hle : producerProfit P .EC y d ≤ producerProfit P .EC y (dN P) := by
    by_cases hop : OverPrescribes P d
    · exact (bound_O hP hf hop _ y).1.trans hc'
    · exact (bound_N hP hf hop _ y).1
  rw [profN hP, profO] at hc'
  rw [profN hP] at hle
  simp only [ccN, ccO] at hc' hle
  have hx := XX_eq P
  linarith

lemma c2 (hP : P.Standing) (h : P.up < uSRf P.alpha P.beta P.od) {y : ℝ × ℝ}
    (hy : PolicyFeasible .SR y) (hn : NonnegOptimalProfit P .SR y) :
    OPStrictlyMoreProfitable P .SR y := by
  have hX : YY P < XX P := by
    have h' : ¬ (uSRf P.alpha P.beta P.od ≤ P.up) := not_le.2 h
    rw [uSR_le hP] at h'; exact not_le.1 h'
  rw [ops_iff hP]
  by_contra hc
  have hc' := not_lt.1 hc
  obtain ⟨d, ⟨hf, -⟩, hpr⟩ := hn
  have hle : producerProfit P .SR y d ≤ producerProfit P .SR y (dN P) := by
    by_cases hop : OverPrescribes P d
    · exact (bound_O hP hf hop _ y).1.trans hc'
    · exact (bound_N hP hf hop _ y).1
  rw [profN hP, profO] at hc'
  rw [profN hP] at hle
  simp only [ccN, ccO] at hc' hle
  have hx := XX_eq P
  linarith

lemma c4 (hP : P.Standing) (hkb : P.k < kbarf P.alpha P.beta P.od P.up) {y : ℝ × ℝ}
    (hy : PolicyFeasible .EC y) : OPStrictlyMoreProfitable P .EC y := by
  have hk' : 2 * P.k < 3 * XX P := by
    have h' : ¬ (kbarf P.alpha P.beta P.od P.up ≤ P.k) := not_le.2 hkb
    rw [kbar_le] at h'; linarith [not_le.1 h']
  obtain ⟨hr0, hr1, -⟩ := hy
  have hkP : 0 < P.k := hP.2.2.2.2.1
  have : P.k * y.1 ≤ P.k := mul_le_of_le_one_right hkP.le hr1
  rw [ops_iff hP, profN hP, profO]
  simp only [ccN, ccO]
  have hx := XX_eq P
  linarith

lemma c5 (hP : P.Standing) :
    CanEliminate P .EC ↔
      uECf P.alpha P.beta P.od ≤ P.up ∧ kbarf P.alpha P.beta P.od P.up ≤ P.k := by
  rw [uEC_le hP, kbar_le]
  constructor
  · rintro ⟨y, d, h, hnop⟩
    rcases (opt_iff hP _ _ _).1 h.2.1 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := mNE.1 (eqN_EC hP h)
      have hk := hP.2.2.2.2.1
      have : P.k * y.1 ≤ P.k := mul_le_of_le_one_right hk.le h1
      constructor <;> linarith
    · exact absurd (OP_dO P) hnop
  · rintro ⟨h2, hk⟩
    exact ⟨(rN P, 0), dN P, outN_EC hP (rN_mem hP h2 hk), nOP_dN hP⟩

lemma c6 (hP : P.Standing) : CanEliminate P .SR ↔ uSRf P.alpha P.beta P.od ≤ P.up := by
  rw [uSR_le hP]
  constructor
  · rintro ⟨y, d, h, hnop⟩
    rcases (opt_iff hP _ _ _).1 h.2.1 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact (mNS.1 (eqN_SR hP h)).1.2
    · exact absurd (OP_dO P) hnop
  · intro h
    have hY := YY_pos hP
    exact ⟨(0, YY P), dN P,
      outN_SR hP (mNS.2 ⟨⟨⟨le_rfl, zero_le_one⟩, h⟩, by linarith⟩), nOP_dN hP⟩

lemma c7 (hP : P.Standing) (h1 : uECf P.alpha P.beta P.od ≤ P.up)
    (h2 : kbarf P.alpha P.beta P.od P.up ≤ P.k) :
    EliminationOptimal P .EC ↔ epsBar P.alpha P.beta P.od P.up P.k P.epsS ≤ P.epsE := by
  rw [uEC_le hP] at h1
  rw [kbar_le] at h2
  obtain ⟨T, -, hT, hEq⟩ := epsBar_eq hP h1 h2 hP.2.2.2.2.2.2
  rw [hEq]
  exact hT P.epsE hP.2.2.2.2.2.1

lemma c8 (hP : P.Standing) (h1 : uECf P.alpha P.beta P.od ≤ P.up)
    (h2 : kbarf P.alpha P.beta P.od P.up ≤ P.k) (s' : ℝ) (hss : P.epsS ≤ s') :
    epsBar P.alpha P.beta P.od P.up P.k s' ≤ epsBar P.alpha P.beta P.od P.up P.k P.epsS := by
  rw [uEC_le hP] at h1
  rw [kbar_le] at h2
  have hs : 0 ≤ P.epsS := hP.2.2.2.2.2.2
  have hne : ({e | 0 ≤ e ∧ EliminationOptimal
      (⟨P.alpha, P.beta, P.od, P.up, P.k, e, P.epsS⟩ : Params) .EC} : Set ℝ).Nonempty :=
    ⟨Tb P P.epsS, Tb_nonneg hP hs, elim_big hP h1 h2 hs le_rfl⟩
  unfold epsBar
  refine csInf_le_csInf ?_ hne ?_
  · exact ⟨0, fun x hx => hx.1⟩
  rintro e ⟨he, hE⟩
  exact ⟨he, mono_s hP h1 h2 he hs hss hE⟩

lemma c10 (hP : P.Standing) (h : P.up < uECf P.alpha P.beta P.od) : WelfareEqual P := by
  have hX : 2 * YY P < XX P := by
    have h' : ¬ (uECf P.alpha P.beta P.od ≤ P.up) := not_le.2 h
    rw [uEC_le hP] at h'; exact not_le.1 h'
  have hY := YY_pos hP
  have hEq : ach P .EC = ach P .SR := by
    rw [achEC hP, achSR hP, NE_empty1 hP hX, NS_empty (by linarith), OE_eq_OS1 hP hX]
  refine ⟨sSup (ach P .SR), ?_, (imw_iff _ _ _).2 (greatest hP .SR)⟩
  rw [imw_iff, hEq]
  exact greatest hP .SR

lemma c11 (hP : P.Standing) (h1 : uECf P.alpha P.beta P.od ≤ P.up)
    (h2 : P.up < uSRf P.alpha P.beta P.od) (h3 : P.k < kbarf P.alpha P.beta P.od P.up) :
    WelfareEqual P := by
  have hX : YY P < XX P := by
    have h' : ¬ (uSRf P.alpha P.beta P.od ≤ P.up) := not_le.2 h2
    rw [uSR_le hP] at h'; exact not_le.1 h'
  have hk' : 2 * P.k < 3 * XX P := by
    have h' : ¬ (kbarf P.alpha P.beta P.od P.up ≤ P.k) := not_le.2 h3
    rw [kbar_le] at h'; linarith [not_le.1 h']
  have hEq : ach P .EC = ach P .SR := by
    rw [achEC hP, achSR hP, NE_empty2 hP hk', NS_empty hX, OE_eq_OS2 hP hk']
  refine ⟨sSup (ach P .SR), ?_, (imw_iff _ _ _).2 (greatest hP .SR)⟩
  rw [imw_iff, hEq]
  exact greatest hP .SR

lemma c12 (hP : P.Standing) (h1 : uSRf P.alpha P.beta P.od ≤ P.up) :
    WelfareAtLeast P .SR .EC := by
  rw [uSR_le hP] at h1
  exact wal_of hP (csSup_le_csSup (cpt_SR hP).bddAbove (ne_EC hP) (sub_ECSR hP h1))

end P4Y

open EPRPharma in
theorem solution :
    ∃ (uEC uSR : ℝ → ℝ → ℝ → ℝ) (kbar : ℝ → ℝ → ℝ → ℝ → ℝ)
      (epsBarEC epsTilde : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ),
      -- Proposition 1
      (∀ P : Params, P.Standing → P.up < uEC P.alpha P.beta P.od →
        ∀ y : ℝ × ℝ, PolicyFeasible .EC y → NonnegOptimalProfit P .EC y →
          OPStrictlyMoreProfitable P .EC y) ∧
      (∀ P : Params, P.Standing → P.up < uSR P.alpha P.beta P.od →
        ∀ y : ℝ × ℝ, PolicyFeasible .SR y → NonnegOptimalProfit P .SR y →
          OPStrictlyMoreProfitable P .SR y) ∧
      (∀ a b o : ℝ, 0 < a → 0 < b → 0 < o → uEC a b o < uSR a b o) ∧
      -- Proposition 2
      (∀ P : Params, P.Standing → uEC P.alpha P.beta P.od ≤ P.up →
        P.k < kbar P.alpha P.beta P.od P.up →
        ∀ y : ℝ × ℝ, PolicyFeasible .EC y → OPStrictlyMoreProfitable P .EC y) ∧
      -- p. 17: when over-prescription can be eliminated
      (∀ P : Params, P.Standing →
        (CanEliminate P .EC ↔
          uEC P.alpha P.beta P.od ≤ P.up ∧ kbar P.alpha P.beta P.od P.up ≤ P.k)) ∧
      (∀ P : Params, P.Standing → (CanEliminate P .SR ↔ uSR P.alpha P.beta P.od ≤ P.up)) ∧
      -- Proposition 3 (EC), and ε̃_e ≥ ε̄_e^EC
      (∀ P : Params, P.Standing → uEC P.alpha P.beta P.od ≤ P.up →
        kbar P.alpha P.beta P.od P.up ≤ P.k →
        (EliminationOptimal P .EC ↔
          epsBarEC P.alpha P.beta P.od P.up P.k P.epsS ≤ P.epsE)) ∧
      (∀ P : Params, P.Standing → uEC P.alpha P.beta P.od ≤ P.up →
        kbar P.alpha P.beta P.od P.up ≤ P.k →
        ∀ s' : ℝ, P.epsS ≤ s' →
          epsBarEC P.alpha P.beta P.od P.up P.k s'
            ≤ epsBarEC P.alpha P.beta P.od P.up P.k P.epsS) ∧
      (∀ P : Params, P.Standing → uEC P.alpha P.beta P.od ≤ P.up →
        kbar P.alpha P.beta P.od P.up ≤ P.k →
        epsBarEC P.alpha P.beta P.od P.up P.k P.epsS
          ≤ epsTilde P.alpha P.beta P.od P.up P.k P.epsS) ∧
      -- Table 2
      (∀ P : Params, P.Standing → P.up < uEC P.alpha P.beta P.od → WelfareEqual P) ∧
      (∀ P : Params, P.Standing → uEC P.alpha P.beta P.od ≤ P.up →
        P.up < uSR P.alpha P.beta P.od → P.k < kbar P.alpha P.beta P.od P.up →
        WelfareEqual P) ∧
      (∀ P : Params, P.Standing → uSR P.alpha P.beta P.od ≤ P.up →
        P.k < kbar P.alpha P.beta P.od P.up → WelfareAtLeast P .SR .EC) ∧
      (∀ P : Params, P.Standing → uEC P.alpha P.beta P.od ≤ P.up →
        kbar P.alpha P.beta P.od P.up ≤ P.k →
        (epsTilde P.alpha P.beta P.od P.up P.k P.epsS ≤ P.epsE → WelfareAtLeast P .EC .SR) ∧
        (P.epsE < epsTilde P.alpha P.beta P.od P.up P.k P.epsS → WelfareAtLeast P .SR .EC)) := by
  refine ⟨P4Y.uECf, P4Y.uSRf, P4Y.kbarf, P4Y.epsBar, P4Y.epsTil,
    fun P hP h y hy hn => P4Y.c1 hP h hy hn,
    fun P hP h y hy hn => P4Y.c2 hP h hy hn,
    fun a b o ha _ _ => P4Y.uEC_lt_uSR ha,
    fun P hP _ hkb y hy => P4Y.c4 hP hkb hy,
    fun P hP => P4Y.c5 hP,
    fun P hP => P4Y.c6 hP,
    fun P hP h1 h2 => P4Y.c7 hP h1 h2,
    fun P hP h1 h2 s' hss => P4Y.c8 hP h1 h2 s' hss,
    fun P hP h1 h2 => ?_,
    fun P hP h => P4Y.c10 hP h,
    fun P hP h1 h2 h3 => P4Y.c11 hP h1 h2 h3,
    fun P hP h1 _ => P4Y.c12 hP h1,
    fun P hP h1 h2 => ?_⟩
  · rw [P4Y.uEC_le hP] at h1
    rw [P4Y.kbar_le] at h2
    exact (P4Y.epsTil_spec hP h1 h2).1
  · rw [P4Y.uEC_le hP] at h1
    rw [P4Y.kbar_le] at h2
    have hG := P4Y.epsTil_spec hP h1 h2
    exact ⟨fun h => (hG.2 P.epsE hP.2.2.2.2.2.1).1 h, fun h => (hG.2 P.epsE hP.2.2.2.2.2.1).2 h⟩
