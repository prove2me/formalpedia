-- Prove2me | solution 1 for CompOpacity.Disclosure.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T16:01:12.889329+00:00
-- url     : https://prove2.me/submissions/7c03df8e-2df5-40b8-8f90-0f602e32dbf2

import Mathlib
import Definitions.Def_CompOpacity_Disclosure_Model
import Theorems.Thm_CompOpacity_Disclosure_eq_50_53
import Theorems.Thm_CompOpacity_Disclosure_eq_46_47
import Theorems.Thm_CompOpacity_Disclosure_proposition_2
import Theorems.Thm_CompOpacity_Disclosure_mNC_antitone
import Theorems.Thm_CompOpacity_Disclosure_L_unique_root


open MeasureTheory ProbabilityTheory

namespace COGauss

lemma pi_eq_vec (ν : Fin 2 → Measure ℝ) : Measure.pi ν = Measure.pi ![ν 0, ν 1] := by
  congr 1; funext i; fin_cases i <;> rfl

lemma mp2 (ν : Fin 2 → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] :
    MeasurePreserving MeasurableEquiv.finTwoArrow (Measure.pi ν) ((ν 0).prod (ν 1)) := by
  rw [pi_eq_vec]; exact measurePreserving_finTwoArrow_vec _ _

/-- one-dim facts -/
lemma memLp_aff (μ : ℝ) (w : NNReal) (c u : ℝ) :
    MemLp (fun x : ℝ => c + u * x) 2 (gaussianReal μ w) :=
  (memLp_const c).add ((memLp_id_gaussianReal 2).const_mul u)

lemma int_aff (μ : ℝ) (w : NNReal) (c u : ℝ) :
    ∫ x, c + u * x ∂(gaussianReal μ w) = c + u * μ := by
  have hi : Integrable (fun x : ℝ => x) (gaussianReal μ w) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  rw [integral_add (integrable_const _) (hi.const_mul u), integral_const_mul]
  have := integral_id_gaussianReal (μ := μ) (v := w)
  simp [this]

lemma var_aff (μ : ℝ) (w : NNReal) (c u : ℝ) :
    Var[fun x : ℝ => c + u * x; gaussianReal μ w] = u ^ 2 * w := by
  rw [variance_const_add (by fun_prop), variance_const_mul]
  rw [show (fun x : ℝ => x) = id from rfl, variance_id_gaussianReal]

/-- pi over Fin 2 of gaussians -/
lemma memLp_pi (μ : Fin 2 → ℝ) (w : Fin 2 → NNReal) (c u0 u1 : ℝ) :
    MemLp (fun x : Fin 2 → ℝ => c + u0 * x 0 + u1 * x 1) 2
      (Measure.pi fun i => gaussianReal (μ i) (w i)) := by
  have h0 : MemLp (fun x : Fin 2 → ℝ => x 0) 2 (Measure.pi fun i => gaussianReal (μ i) (w i)) :=
    (memLp_id_gaussianReal 2).comp_measurePreserving (measurePreserving_eval _ 0)
  have h1 : MemLp (fun x : Fin 2 → ℝ => x 1) 2 (Measure.pi fun i => gaussianReal (μ i) (w i)) :=
    (memLp_id_gaussianReal 2).comp_measurePreserving (measurePreserving_eval _ 1)
  exact ((memLp_const c).add (h0.const_mul u0)).add (h1.const_mul u1)

lemma int_pi (μ : Fin 2 → ℝ) (w : Fin 2 → NNReal) (c u0 u1 : ℝ) :
    ∫ x : Fin 2 → ℝ, c + u0 * x 0 + u1 * x 1 ∂(Measure.pi fun i => gaussianReal (μ i) (w i))
      = c + u0 * μ 0 + u1 * μ 1 := by
  have hm := mp2 (fun i => gaussianReal (μ i) (w i))
  have e := hm.integral_comp' (g := fun p : ℝ × ℝ => (c + u0 * p.1) + (0 + u1 * p.2))
  have e2 : (fun x : Fin 2 → ℝ => c + u0 * x 0 + u1 * x 1)
      = fun x => (fun p : ℝ × ℝ => (c + u0 * p.1) + (0 + u1 * p.2))
          (MeasurableEquiv.finTwoArrow x) := by
    funext x; simp [MeasurableEquiv.finTwoArrow_apply]
  rw [e2, e]
  rw [integral_add ((memLp_aff _ _ c u0).integrable one_le_two |>.comp_fst _)
    ((memLp_aff _ _ 0 u1).integrable one_le_two |>.comp_snd _)]
  rw [integral_fun_fst (f := fun x => c + u0 * x), integral_fun_snd (f := fun x => 0 + u1 * x),
    int_aff, int_aff]
  simp

lemma var_pi (μ : Fin 2 → ℝ) (w : Fin 2 → NNReal) (c u0 u1 : ℝ) :
    Var[fun x : Fin 2 → ℝ => c + u0 * x 0 + u1 * x 1;
      Measure.pi fun i => gaussianReal (μ i) (w i)] = u0 ^ 2 * w 0 + u1 ^ 2 * w 1 := by
  have hm := mp2 (fun i => gaussianReal (μ i) (w i))
  have : (fun x : Fin 2 → ℝ => c + u0 * x 0 + u1 * x 1)
      = fun x => (fun p : ℝ × ℝ => (c + u0 * p.1) + (0 + u1 * p.2))
          (MeasurableEquiv.finTwoArrow x) := by
    funext x; simp [MeasurableEquiv.finTwoArrow_apply]
  rw [this, hm.variance_fun_comp (f := fun p : ℝ × ℝ => (c + u0 * p.1) + (0 + u1 * p.2)) (by fun_prop),
    variance_add_prod (memLp_aff _ _ c u0) (memLp_aff _ _ 0 u1), var_aff, var_aff]

end COGauss

namespace COGauss

/-- affine form on the model space -/
def aff (c u0 u1 v0 v1 : ℝ) (ω : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  c + u0 * ω.1 0 + u1 * ω.1 1 + v0 * ω.2 0 + v1 * ω.2 1

variable (μ1 μ2 : Fin 2 → ℝ) (w1 w2 : Fin 2 → NNReal)

noncomputable abbrev PM : Measure ((Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
  (Measure.pi fun i => gaussianReal (μ1 i) (w1 i)).prod
    (Measure.pi fun i => gaussianReal (μ2 i) (w2 i))

lemma aff_split (c u0 u1 v0 v1 : ℝ) :
    aff c u0 u1 v0 v1 = fun ω => (fun x : Fin 2 → ℝ => c + u0 * x 0 + u1 * x 1) ω.1
      + (fun x : Fin 2 → ℝ => 0 + v0 * x 0 + v1 * x 1) ω.2 := by
  funext ω; simp [aff]; ring

lemma memLp_aff2 (c u0 u1 v0 v1 : ℝ) : MemLp (aff c u0 u1 v0 v1) 2 (PM μ1 μ2 w1 w2) := by
  rw [aff_split]
  exact ((memLp_pi μ1 w1 c u0 u1).comp_fst _).add ((memLp_pi μ2 w2 0 v0 v1).comp_snd _)

lemma int_aff2 (c u0 u1 v0 v1 : ℝ) :
    ∫ ω, aff c u0 u1 v0 v1 ω ∂(PM μ1 μ2 w1 w2) = c + u0 * μ1 0 + u1 * μ1 1 + v0 * μ2 0 + v1 * μ2 1 := by
  rw [aff_split, integral_add ((memLp_pi μ1 w1 c u0 u1).integrable one_le_two |>.comp_fst _)
    ((memLp_pi μ2 w2 0 v0 v1).integrable one_le_two |>.comp_snd _)]
  rw [integral_fun_fst (f := fun x : Fin 2 → ℝ => c + u0 * x 0 + u1 * x 1),
    integral_fun_snd (f := fun x : Fin 2 → ℝ => 0 + v0 * x 0 + v1 * x 1), int_pi, int_pi]
  simp only [probReal_univ]
  ring

lemma sq_aff2 (c u0 u1 v0 v1 : ℝ) :
    ∫ ω, aff c u0 u1 v0 v1 ω ^ 2 ∂(PM μ1 μ2 w1 w2) = (c + u0 * μ1 0 + u1 * μ1 1 + v0 * μ2 0 + v1 * μ2 1) ^ 2
      + (u0 ^ 2 * w1 0 + u1 ^ 2 * w1 1 + v0 ^ 2 * w2 0 + v1 ^ 2 * w2 1) := by
  have hv := variance_eq_sub (memLp_aff2 μ1 μ2 w1 w2 c u0 u1 v0 v1)
  have hv2 : Var[aff c u0 u1 v0 v1; PM μ1 μ2 w1 w2] = u0 ^ 2 * w1 0 + u1 ^ 2 * w1 1 + v0 ^ 2 * w2 0
      + v1 ^ 2 * w2 1 := by
    rw [aff_split, variance_add_prod (memLp_pi μ1 w1 c u0 u1) (memLp_pi μ2 w2 0 v0 v1),
      var_pi, var_pi]
    ring
  rw [hv2, int_aff2] at hv
  have : (∫ ω, aff c u0 u1 v0 v1 ω ^ 2 ∂(PM μ1 μ2 w1 w2)) = ∫ ω, (aff c u0 u1 v0 v1 ^ 2) ω ∂(PM μ1 μ2 w1 w2) := by
    rfl
  rw [this]
  linarith

lemma mul_aff2 (c u0 u1 v0 v1 c' u0' u1' v0' v1' : ℝ) :
    ∫ ω, aff c u0 u1 v0 v1 ω * aff c' u0' u1' v0' v1' ω ∂(PM μ1 μ2 w1 w2) =
      (c + u0 * μ1 0 + u1 * μ1 1 + v0 * μ2 0 + v1 * μ2 1)
        * (c' + u0' * μ1 0 + u1' * μ1 1 + v0' * μ2 0 + v1' * μ2 1)
      + (u0 * u0' * w1 0 + u1 * u1' * w1 1 + v0 * v0' * w2 0 + v1 * v1' * w2 1) := by
  have e : ∀ ω, aff c u0 u1 v0 v1 ω * aff c' u0' u1' v0' v1' ω =
      (1/4 : ℝ) * aff (c + c') (u0 + u0') (u1 + u1') (v0 + v0') (v1 + v1') ω ^ 2
      - (1/4 : ℝ) * aff (c - c') (u0 - u0') (u1 - u1') (v0 - v0') (v1 - v1') ω ^ 2 := by
    intro ω; simp only [aff]; ring
  simp_rw [e]
  rw [integral_sub ((memLp_aff2 μ1 μ2 w1 w2 _ _ _ _ _).integrable_sq.const_mul _)
    ((memLp_aff2 μ1 μ2 w1 w2 _ _ _ _ _).integrable_sq.const_mul _),
    integral_const_mul, integral_const_mul, sq_aff2, sq_aff2]
  ring

end COGauss


open MeasureTheory ProbabilityTheory

namespace CompOpacity.Disclosure

/-- closed form of the expected payoff for any linear strategy -/
theorem fiPayoff_eq (a b q thetaBar cm : ℝ) (m : Fin 2 → ℝ) (s : LinStrat) (i : Fin 2)
    (hq : 0 < q) (hm : ∀ j, 0 ≤ m j) :
    fiPayoff a b q thetaBar cm m s i =
      (s.h i + thetaBar * (s.beta i + s.gamma i) - b * thetaBar * (s.omega i + s.lam i))
        * (thetaBar + (a - 1/2) * (s.h i + thetaBar * (s.beta i + s.gamma i)
            - b * thetaBar * (s.omega i + s.lam i)))
      + ((s.beta i + s.gamma i) * (1 + (a - 1/2) * (s.beta i + s.gamma i))
          + (a - 1/2) * b ^ 2 * (s.omega i + s.lam i) ^ 2) * q⁻¹
      + (a - 1/2) * (s.gamma i ^ 2 * (m i)⁻¹ + b ^ 2 * s.omega i ^ 2 * (m i.rev)⁻¹)
      - cm / 2 * m i ^ 2 := by
  have hq' : ((q⁻¹).toNNReal : ℝ) = q⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 hq.le)
  have hm' : ∀ j, (((m j)⁻¹).toNNReal : ℝ) = (m j)⁻¹ :=
    fun j => Real.coe_toNNReal _ (inv_nonneg.2 (hm j))
  have hlaw : modelLaw q thetaBar m = COGauss.PM (fun _ => thetaBar) (fun _ => 0)
      (fun _ => (q⁻¹).toNNReal) (fun i => ((m i)⁻¹).toNNReal) := rfl
  have r0 : Fin.rev (0 : Fin 2) = 1 := rfl
  have r1 : Fin.rev (1 : Fin 2) = 0 := rfl
  unfold fiPayoff
  rw [hlaw]
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · have e : ∀ ω : (Fin 2 → ℝ) × (Fin 2 → ℝ),
        ((ω.1 0 + a * aggK s b 0 ω.1 (ω.1 + ω.2)) * aggK s b 0 ω.1 (ω.1 + ω.2)
          - aggK s b 0 ω.1 (ω.1 + ω.2) ^ 2 / 2) =
        COGauss.aff (s.h 0) (s.beta 0 + s.gamma 0) (-b * (s.omega 0 + s.lam 0)) (s.gamma 0)
            (-b * s.omega 0) ω
          * COGauss.aff ((a - 1/2) * s.h 0) (1 + (a - 1/2) * (s.beta 0 + s.gamma 0))
            ((a - 1/2) * (-b * (s.omega 0 + s.lam 0))) ((a - 1/2) * s.gamma 0)
            ((a - 1/2) * (-b * s.omega 0)) ω := by
      intro ω; simp only [aggK, COGauss.aff, Pi.add_apply, r0, r1]; ring
    simp_rw [e]
    rw [COGauss.mul_aff2]
    simp only [hq', hm', r0, r1]
    ring
  · have e : ∀ ω : (Fin 2 → ℝ) × (Fin 2 → ℝ),
        ((ω.1 1 + a * aggK s b 1 ω.1 (ω.1 + ω.2)) * aggK s b 1 ω.1 (ω.1 + ω.2)
          - aggK s b 1 ω.1 (ω.1 + ω.2) ^ 2 / 2) =
        COGauss.aff (s.h 1) (-b * (s.omega 1 + s.lam 1)) (s.beta 1 + s.gamma 1)
            (-b * s.omega 1) (s.gamma 1) ω
          * COGauss.aff ((a - 1/2) * s.h 1) ((a - 1/2) * (-b * (s.omega 1 + s.lam 1)))
            (1 + (a - 1/2) * (s.beta 1 + s.gamma 1))
            ((a - 1/2) * (-b * s.omega 1)) ((a - 1/2) * s.gamma 1) ω := by
      intro ω; simp only [aggK, COGauss.aff, Pi.add_apply, r0, r1]; ring
    simp_rw [e]
    rw [COGauss.mul_aff2]
    simp only [hq', hm', r0, r1]
    ring

end CompOpacity.Disclosure


namespace CompOpacity.Disclosure

/-- coefficient equations of a linear equilibrium (general a b) -/
theorem linEq_coeff_eqs (a b q n thetaBar : ℝ) (m : Fin 2 → ℝ) (s : LinStrat)
    (H : IsLinEq a b q n thetaBar m s) (i : Fin 2) :
    let d := m i + n + q
    let d' := m i.rev + n + q
    let K := 1 + a * s.beta i + a * b ^ 2 * s.lam i.rev
    let K' := 1 + a * s.lam i + a * s.beta i.rev
    s.beta i = K * n / d ∧ b * s.lam i = b * K' * n / d' ∧
    s.gamma i = K * m i / d + a * s.gamma i + a * b ^ 2 * s.omega i.rev ∧
    b * s.omega i = b * K' * m i.rev / d' + a * b * s.omega i + a * b * s.gamma i.rev ∧
    s.h i = K * q * thetaBar / d - b * K' * q * thetaBar / d' + a * s.h i - a * b * s.h i.rev := by
  intro d d' K K'
  have r0 : Fin.rev (0 : Fin 2) = 1 := rfl
  have r1 : Fin.rev (1 : Fin 2) = 0 := rfl
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · have c0 := H ![0,0] ![0,0] 0
    have c1 := H ![0,0] ![1,0] 0
    have c2 := H ![0,0] ![0,1] 0
    have c3 := H ![1,0] ![0,0] 0
    have c4 := H ![0,1] ![0,0] 0
    simp [invest, expK, postMean, r0, r1] at c0 c1 c2 c3 c4
    simp only [d, d', K, K', r0, r1]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linear_combination c1 - c0
    · linear_combination c0 - c2
    · linear_combination c3 - c0
    · linear_combination c0 - c4
    · linear_combination c0
  · have c0 := H ![0,0] ![0,0] 1
    have c1 := H ![0,0] ![0,1] 1
    have c2 := H ![0,0] ![1,0] 1
    have c3 := H ![0,1] ![0,0] 1
    have c4 := H ![1,0] ![0,0] 1
    simp [invest, expK, postMean, r0, r1] at c0 c1 c2 c3 c4
    simp only [d, d', K, K', r0, r1]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linear_combination c1 - c0
    · linear_combination c0 - c2
    · linear_combination c3 - c0
    · linear_combination c0 - c4
    · linear_combination c0

theorem linEq_of_coeff_eqs (a b q n thetaBar : ℝ) (m : Fin 2 → ℝ) (s : LinStrat)
    (H : ∀ i : Fin 2,
    s.beta i = (1 + a * s.beta i + a * b ^ 2 * s.lam i.rev) * n / (m i + n + q) ∧
    b * s.lam i = b * (1 + a * s.lam i + a * s.beta i.rev) * n / (m i.rev + n + q) ∧
    s.gamma i = (1 + a * s.beta i + a * b ^ 2 * s.lam i.rev) * m i / (m i + n + q)
      + a * s.gamma i + a * b ^ 2 * s.omega i.rev ∧
    b * s.omega i = b * (1 + a * s.lam i + a * s.beta i.rev) * m i.rev / (m i.rev + n + q)
      + a * b * s.omega i + a * b * s.gamma i.rev ∧
    s.h i = (1 + a * s.beta i + a * b ^ 2 * s.lam i.rev) * q * thetaBar / (m i + n + q)
      - b * (1 + a * s.lam i + a * s.beta i.rev) * q * thetaBar / (m i.rev + n + q)
      + a * s.h i - a * b * s.h i.rev) :
    IsLinEq a b q n thetaBar m s := by
  intro z x i
  obtain ⟨e1, e2, e3, e4, e5⟩ := H i
  simp only [invest, expK, postMean]
  have r0 : Fin.rev (0 : Fin 2) = 1 := rfl
  have r1 : Fin.rev (1 : Fin 2) = 0 := rfl
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · simp only [r0, r1] at *
    linear_combination (x 0) * e1 - (x 1) * e2 + (z 0) * e3 - (z 1) * e4 + e5
  · simp only [r0, r1] at *
    linear_combination (x 1) * e1 - (x 0) * e2 + (z 1) * e3 - (z 0) * e4 + e5

theorem linEq1_unique (a q n thetaBar : ℝ) (m : Fin 2 → ℝ) (s : LinStrat)
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hq : 0 < q) (hn : 0 < n) (hm : ∀ j, 0 ≤ m j)
    (H : IsLinEq a 1 q n thetaBar m s) (i : Fin 2) :
    s.beta i = n / (q + m i + (1 - 2 * a) * n) ∧
    s.lam i.rev = n / (q + m i + (1 - 2 * a) * n) ∧
    s.gamma i = m i / ((1 - 2 * a) * (q + m i + (1 - 2 * a) * n)) ∧
    s.omega i.rev = m i / ((1 - 2 * a) * (q + m i + (1 - 2 * a) * n)) ∧
    s.h i = q * thetaBar / (1 - 2 * a) *
      (1 / (q + m i + (1 - 2 * a) * n) - 1 / (q + m i.rev + (1 - 2 * a) * n)) := by
  have A := linEq_coeff_eqs a 1 q n thetaBar m s H i
  have B := linEq_coeff_eqs a 1 q n thetaBar m s H i.rev
  simp only [Fin.rev_rev, one_pow, mul_one, one_mul] at A B
  obtain ⟨a1, a2, a3, a4, a5⟩ := A
  obtain ⟨b1, b2, b3, b4, b5⟩ := B
  have hd : 0 < m i + n + q := by linarith [hm i]
  have hd' : 0 < m i.rev + n + q := by linarith [hm i.rev]
  have hw : 0 < 1 - 2 * a := by linarith
  have hE : 0 < q + m i + (1 - 2 * a) * n := by nlinarith [hm i]
  have hE' : 0 < q + m i.rev + (1 - 2 * a) * n := by nlinarith [hm i.rev]
  have hE0 : q + m i + (1 - 2 * a) * n ≠ 0 := hE.ne'
  have hE0' : q + m i.rev + (1 - 2 * a) * n ≠ 0 := hE'.ne'
  have hd0 : m i + n + q ≠ 0 := hd.ne'
  have hd0' : m i.rev + n + q ≠ 0 := hd'.ne'
  have kk : ∀ t : ℝ, 0 ≤ t → (1 + 2 * a * (n / (q + t + (1 - 2 * a) * n))) / (t + n + q)
        = 1 / (q + t + (1 - 2 * a) * n) := by
    intro t ht
    have h1 : q + t + (1 - 2 * a) * n ≠ 0 := by nlinarith
    have h2 : t + n + q ≠ 0 := by linarith
    field_simp; ring
  -- beta / lambda
  have hbl : s.beta i = s.lam i.rev := by linear_combination a1 - b2
  have hbl' : s.beta i.rev = s.lam i := by linear_combination b1 - a2
  have hβ : s.beta i = n / (q + m i + (1 - 2 * a) * n) := by
    rw [eq_div_iff hE.ne']
    rw [← hbl] at a1
    field_simp at a1
    linear_combination a1
  have hβ' : s.beta i.rev = n / (q + m i.rev + (1 - 2 * a) * n) := by
    rw [eq_div_iff hE'.ne']
    rw [← hbl'] at b1
    field_simp at b1
    linear_combination b1
  -- gamma / omega
  have hgo : s.gamma i = s.omega i.rev := by
    rw [← hbl] at a3 b4
    linear_combination a3 - b4
  have hγ : s.gamma i = m i / ((1 - 2 * a) * (q + m i + (1 - 2 * a) * n)) := by
    have k1 : s.gamma i * (1 - 2 * a) = (1 + 2 * a * s.beta i) * m i / (m i + n + q) := by
      rw [← hbl, ← hgo] at a3; linear_combination a3
    rw [hβ] at k1
    have k2 := kk (m i) (hm i)
    rw [mul_div_right_comm, k2] at k1
    rw [eq_div_iff (by positivity)]
    field_simp at k1
    linear_combination k1
  have hgo' : s.gamma i.rev = s.omega i := by
    rw [← hbl'] at b3 a4
    linear_combination b3 - a4
  have hγ' : s.gamma i.rev = m i.rev / ((1 - 2 * a) * (q + m i.rev + (1 - 2 * a) * n)) := by
    have k1 : s.gamma i.rev * (1 - 2 * a) = (1 + 2 * a * s.beta i.rev) * m i.rev / (m i.rev + n + q) := by
      rw [← hbl', ← hgo'] at b3; linear_combination b3
    rw [hβ'] at k1
    have k2 := kk (m i.rev) (hm i.rev)
    rw [mul_div_right_comm, k2] at k1
    rw [eq_div_iff (by positivity)]
    field_simp at k1
    linear_combination k1
  refine ⟨hβ, hbl ▸ hβ, hγ, hgo ▸ hγ, ?_⟩
  have a5' : s.h i * (1 - a) + a * s.h i.rev = q * thetaBar *
      (1 / (q + m i + (1 - 2 * a) * n) - 1 / (q + m i.rev + (1 - 2 * a) * n)) := by
    rw [← hbl, ← hbl', hβ, hβ'] at a5
    rw [← kk (m i) (hm i), ← kk (m i.rev) (hm i.rev)]
    linear_combination a5
  have b5' : s.h i.rev * (1 - a) + a * s.h i = q * thetaBar *
      (1 / (q + m i.rev + (1 - 2 * a) * n) - 1 / (q + m i + (1 - 2 * a) * n)) := by
    rw [← hbl, ← hbl', hβ, hβ'] at b5
    rw [← kk (m i) (hm i), ← kk (m i.rev) (hm i.rev)]
    linear_combination b5
  have hw0 : 1 - 2 * a ≠ 0 := hw.ne'
  have : s.h i * (1 - 2 * a) = q * thetaBar *
      (1 / (q + m i + (1 - 2 * a) * n) - 1 / (q + m i.rev + (1 - 2 * a) * n)) := by
    linear_combination (1 - a) * a5' - a * b5'
  rw [div_mul_eq_mul_div, ← this]; field_simp

/-- explicit equilibrium at b = 1 -/
noncomputable def sS (a q n thetaBar : ℝ) (m : Fin 2 → ℝ) : LinStrat where
  beta := fun i => n / (q + m i + (1 - 2 * a) * n)
  lam := fun i => n / (q + m i.rev + (1 - 2 * a) * n)
  gamma := fun i => m i / ((1 - 2 * a) * (q + m i + (1 - 2 * a) * n))
  omega := fun i => m i.rev / ((1 - 2 * a) * (q + m i.rev + (1 - 2 * a) * n))
  h := fun i => q * thetaBar / (1 - 2 * a) *
      (1 / (q + m i + (1 - 2 * a) * n) - 1 / (q + m i.rev + (1 - 2 * a) * n))

theorem sS_isLinEq (a q n thetaBar : ℝ) (m : Fin 2 → ℝ)
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hq : 0 < q) (hn : 0 < n) (hm : ∀ j, 0 ≤ m j) :
    IsLinEq a 1 q n thetaBar m (sS a q n thetaBar m) := by
  apply linEq_of_coeff_eqs
  intro i
  have hw : 0 < 1 - 2 * a := by linarith
  have hE : q + m i + (1 - 2 * a) * n ≠ 0 := by nlinarith [hm i]
  have hE' : q + m i.rev + (1 - 2 * a) * n ≠ 0 := by nlinarith [hm i.rev]
  have hd0 : m i + n + q ≠ 0 := by linarith [hm i]
  have hd0' : m i.rev + n + q ≠ 0 := by linarith [hm i.rev]
  have hw0 : 1 - 2 * a ≠ 0 := hw.ne'
  have x1 : m i + n - n * a * 2 + q ≠ 0 := by contrapose! hE; linear_combination hE
  have x2 : m i.rev + n - n * a * 2 + q ≠ 0 := by contrapose! hE'; linear_combination hE'
  simp only [sS, Fin.rev_rev, one_pow, mul_one, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring_nf <;> field_simp <;> ring

/-- explicit equilibrium at b = 0 -/
noncomputable def sNC (a q n thetaBar : ℝ) (m : Fin 2 → ℝ) : LinStrat where
  beta := fun i => n / (q + m i + (1 - a) * n)
  lam := fun _ => 0
  gamma := fun i => m i / ((1 - a) * (q + m i + (1 - a) * n))
  omega := fun _ => 0
  h := fun i => q * thetaBar / ((1 - a) * (q + m i + (1 - a) * n))

theorem sNC_isLinEq (a q n thetaBar : ℝ) (m : Fin 2 → ℝ)
    (ha0 : 0 ≤ a) (ha : a < 1) (hq : 0 < q) (hn : 0 < n) (hm : ∀ j, 0 ≤ m j) :
    IsLinEq a 0 q n thetaBar m (sNC a q n thetaBar m) := by
  apply linEq_of_coeff_eqs
  intro i
  have hw : 0 < 1 - a := by linarith
  have hE : q + m i + (1 - a) * n ≠ 0 := by nlinarith [hm i]
  have hd0 : m i + n + q ≠ 0 := by linarith [hm i]
  have hw0 : 1 - a ≠ 0 := hw.ne'
  have x1 : m i + n - n * a + q ≠ 0 := by contrapose! hE; linear_combination hE
  simp only [sNC]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring_nf <;> field_simp <;> ring

theorem linEq0_unique (a q n thetaBar : ℝ) (m : Fin 2 → ℝ) (s : LinStrat)
    (ha0 : 0 ≤ a) (ha : a < 1) (hq : 0 < q) (hn : 0 < n) (hm : ∀ j, 0 ≤ m j)
    (H : IsLinEq a 0 q n thetaBar m s) (i : Fin 2) :
    s.beta i = n / (q + m i + (1 - a) * n) ∧
    s.gamma i = m i / ((1 - a) * (q + m i + (1 - a) * n)) ∧
    s.h i = q * thetaBar / ((1 - a) * (q + m i + (1 - a) * n)) := by
  obtain ⟨a1, -, a3, -, a5⟩ := linEq_coeff_eqs a 0 q n thetaBar m s H i
  simp only [zero_mul, mul_zero, add_zero, sub_zero, zero_pow two_ne_zero, zero_div] at a1 a3 a5
  have hw : 0 < 1 - a := by linarith
  have hE : q + m i + (1 - a) * n ≠ 0 := by nlinarith [hm i]
  have hd0 : m i + n + q ≠ 0 := by linarith [hm i]
  have hw0 : 1 - a ≠ 0 := hw.ne'
  have x1 : m i + n - n * a + q ≠ 0 := by contrapose! hE; linear_combination hE
  have hβ : s.beta i = n / (q + m i + (1 - a) * n) := by
    rw [eq_div_iff hE]; field_simp at a1; linear_combination a1
  have kk : (1 + a * s.beta i) / (m i + n + q) = 1 / (q + m i + (1 - a) * n) := by
    rw [hβ, div_eq_div_iff hd0 hE, add_mul, mul_assoc, div_mul_cancel₀ _ hE]; ring
  refine ⟨hβ, ?_, ?_⟩
  · have : s.gamma i * (1 - a) = (1 + a * s.beta i) / (m i + n + q) * m i := by
      linear_combination a3
    rw [kk] at this
    rw [eq_div_iff (by positivity)]; field_simp at this; linear_combination this
  · have : s.h i * (1 - a) = (1 + a * s.beta i) / (m i + n + q) * (q * thetaBar) := by
      linear_combination a5
    rw [kk] at this
    rw [eq_div_iff (by positivity)]; field_simp at this; linear_combination this

/-- explicit equilibrium at a = 0 -/
noncomputable def sZ (b q n thetaBar : ℝ) (m : Fin 2 → ℝ) : LinStrat where
  beta := fun i => n / (m i + n + q)
  lam := fun i => n / (m i.rev + n + q)
  gamma := fun i => m i / (m i + n + q)
  omega := fun i => m i.rev / (m i.rev + n + q)
  h := fun i => q * thetaBar / (m i + n + q) - b * (q * thetaBar / (m i.rev + n + q))

theorem sZ_isLinEq (b q n thetaBar : ℝ) (m : Fin 2 → ℝ)
    (hq : 0 < q) (hn : 0 < n) (hm : ∀ j, 0 ≤ m j) :
    IsLinEq 0 b q n thetaBar m (sZ b q n thetaBar m) := by
  apply linEq_of_coeff_eqs
  intro i
  have hd0 : m i + n + q ≠ 0 := by linarith [hm i]
  have hd0' : m i.rev + n + q ≠ 0 := by linarith [hm i.rev]
  simp only [sZ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

theorem linEqZ_unique (b q n thetaBar : ℝ) (m : Fin 2 → ℝ) (s : LinStrat)
    (hb : 0 < b) (H : IsLinEq 0 b q n thetaBar m s) (i : Fin 2) :
    s.beta i = n / (m i + n + q) ∧ s.lam i = n / (m i.rev + n + q) ∧
    s.gamma i = m i / (m i + n + q) ∧ s.omega i = m i.rev / (m i.rev + n + q) ∧
    s.h i = q * thetaBar / (m i + n + q) - b * (q * thetaBar / (m i.rev + n + q)) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := linEq_coeff_eqs 0 b q n thetaBar m s H i
  simp only [zero_mul, mul_zero, add_zero, sub_zero, zero_add, mul_one] at a1 a2 a3 a4 a5
  refine ⟨by rw [a1]; ring, ?_, by rw [a3]; ring, ?_, by rw [a5]; ring⟩
  · have := a2; rw [mul_div_assoc] at this
    exact mul_left_cancel₀ hb.ne' this
  · have := a4; rw [mul_div_assoc] at this
    exact mul_left_cancel₀ hb.ne' this

end CompOpacity.Disclosure


open MeasureTheory ProbabilityTheory

namespace CompOpacity.Disclosure

/-- own-precision part of the gross payoff -/
noncomputable def payG (a q n c t : ℝ) : ℝ :=
  (c * n + t) / (c * (q + t + c * n)) / q
    + (a - 1 / 2) * (((c * n + t) / (c * (q + t + c * n))) ^ 2 / q
      + t / (c ^ 2 * (q + t + c * n) ^ 2))

noncomputable def payR (a q n c t : ℝ) : ℝ :=
  (a - 1 / 2) * (((c * n + t) / (c * (q + t + c * n))) ^ 2 / q
      + t / (c ^ 2 * (q + t + c * n) ^ 2))

lemma sq_div_inv (t X : ℝ) : (t / X) ^ 2 * t⁻¹ = t / X ^ 2 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · field_simp

theorem eqPayoff_S (a q n thetaBar cm : ℝ) (m : Fin 2 → ℝ) (i : Fin 2)
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hq : 0 < q) (hn : 0 < n) (hm : ∀ j, 0 ≤ m j) :
    eqPayoff a 1 q n thetaBar cm m i =
      payG a q n (1 - 2 * a) (m i) + payR a q n (1 - 2 * a) (m i.rev) - cm / 2 * m i ^ 2 := by
  unfold eqPayoff
  have hs := Classical.epsilon_spec ⟨_, sS_isLinEq a q n thetaBar m ha0 ha hq hn hm⟩
  set s := Classical.epsilon (IsLinEq a 1 q n thetaBar m) with hsdef
  obtain ⟨h1, -, h3, -, h5⟩ := linEq1_unique a q n thetaBar m s ha0 ha hq hn hm hs i
  obtain ⟨-, h2, -, h4, -⟩ := linEq1_unique a q n thetaBar m s ha0 ha hq hn hm hs i.rev
  rw [Fin.rev_rev] at h2 h4
  rw [fiPayoff_eq a 1 q thetaBar cm m s i hq hm, h1, h2, h3, h4, h5]
  simp only [one_pow, one_mul]
  rw [sq_div_inv, sq_div_inv]
  have hw : 0 < 1 - 2 * a := by linarith
  have hE : q + m i + (1 - 2 * a) * n ≠ 0 := by nlinarith [hm i]
  have hE' : q + m i.rev + (1 - 2 * a) * n ≠ 0 := by nlinarith [hm i.rev]
  unfold payG payR
  have hw0 : 1 - 2 * a ≠ 0 := hw.ne'
  have hq0 : q ≠ 0 := hq.ne'
  field_simp
  ring

theorem eqPayoff_NC (a q n thetaBar cm : ℝ) (m : Fin 2 → ℝ) (i : Fin 2)
    (ha0 : 0 ≤ a) (ha : a < 1) (hq : 0 < q) (hn : 0 < n) (hm : ∀ j, 0 ≤ m j) :
    eqPayoff a 0 q n thetaBar cm m i =
      thetaBar / (1 - a) * (thetaBar + (a - 1 / 2) * (thetaBar / (1 - a)))
        + payG a q n (1 - a) (m i) - cm / 2 * m i ^ 2 := by
  unfold eqPayoff
  have hs := Classical.epsilon_spec ⟨_, sNC_isLinEq a q n thetaBar m ha0 ha hq hn hm⟩
  set s := Classical.epsilon (IsLinEq a 0 q n thetaBar m) with hsdef
  obtain ⟨h1, h3, h5⟩ := linEq0_unique a q n thetaBar m s ha0 ha hq hn hm hs i
  rw [fiPayoff_eq a 0 q thetaBar cm m s i hq hm, h1, h3, h5]
  simp only [zero_pow two_ne_zero, zero_mul, mul_zero, sub_zero, add_zero, zero_add]
  rw [sq_div_inv]
  have hw : 0 < 1 - a := by linarith
  have hE : q + m i + (1 - a) * n ≠ 0 := by nlinarith [hm i]
  unfold payG
  have hw0 : 1 - a ≠ 0 := hw.ne'
  have hq0 : q ≠ 0 := hq.ne'
  field_simp
  ring

theorem eqPayoff_Z (b q n thetaBar cm : ℝ) (m : Fin 2 → ℝ) (i : Fin 2)
    (hb : 0 < b) (hq : 0 < q) (hn : 0 < n) (hm : ∀ j, 0 ≤ m j) :
    eqPayoff 0 b q n thetaBar cm m i =
      thetaBar * (1 - b) * (thetaBar - thetaBar * (1 - b) / 2)
        + payG 0 q n 1 (m i) + b ^ 2 * payR 0 q n 1 (m i.rev) - cm / 2 * m i ^ 2 := by
  unfold eqPayoff
  have hs := Classical.epsilon_spec ⟨_, sZ_isLinEq b q n thetaBar m hq hn hm⟩
  set s := Classical.epsilon (IsLinEq 0 b q n thetaBar m) with hsdef
  obtain ⟨h1, h2, h3, h4, h5⟩ := linEqZ_unique b q n thetaBar m s hb hs i
  rw [fiPayoff_eq 0 b q thetaBar cm m s i hq hm, h1, h2, h3, h4, h5]
  rw [mul_assoc (b ^ 2), sq_div_inv, sq_div_inv]
  have hd : m i + n + q ≠ 0 := by linarith [hm i]
  have hd' : m i.rev + n + q ≠ 0 := by linarith [hm i.rev]
  unfold payG payR
  have hq0 : q ≠ 0 := hq.ne'
  simp only [one_mul, one_pow, mul_one]
  have x1 : q + m i + n ≠ 0 := by linarith [hm i]
  have x2 : q + m i.rev + n ≠ 0 := by linarith [hm i.rev]
  field_simp
  ring

end CompOpacity.Disclosure


namespace CompOpacity.Disclosure

theorem hasDerivAt_payG (a q n c t : ℝ) (hc : c ≠ 0) (hq : q ≠ 0) (hF : q + t + c * n ≠ 0) :
    HasDerivAt (payG a q n c)
      (1 / (c * (q + t + c * n) ^ 2)
        + (a - 1 / 2) * (2 * ((c * n + t) / (c * (q + t + c * n))) / (c * (q + t + c * n) ^ 2)
          + (q + c * n - t) / (c ^ 2 * (q + t + c * n) ^ 3))) t := by
  have hu : HasDerivAt (fun t => c * n + t) 1 t := (hasDerivAt_id t).const_add _
  have hF1 : HasDerivAt (fun t => q + t + c * n) 1 t :=
    ((hasDerivAt_id t).const_add q).add_const _
  have hcF : HasDerivAt (fun t => c * (q + t + c * n)) (c * 1) t := hF1.const_mul c
  have hB := hu.div hcF (mul_ne_zero hc hF)
  have h1 := hB.div_const q
  have h2 := (hB.pow 2).div_const q
  have h3 := (hasDerivAt_id t).div ((hF1.pow 2).const_mul (c ^ 2))
    (mul_ne_zero (pow_ne_zero 2 hc) (pow_ne_zero 2 hF))
  have tot := h1.add ((h2.add h3).const_mul (a - 1 / 2))
  refine HasDerivAt.congr_deriv (f := payG a q n c) tot ?_
  simp only [id, Pi.div_apply, Pi.pow_apply]
  have k1 : c * (q + t + c * n) ≠ 0 := mul_ne_zero hc hF
  have k2 : c * q + c * t + c ^ 2 * n ≠ 0 := by
    intro h; apply k1; linear_combination h
  norm_num
  rw [show c * n + t = (q + t + c * n) - q by ring, show q + c * n - t = (q + t + c * n) - 2 * t by ring]
  generalize q + t + c * n = F at hF ⊢
  field_simp
  ring

theorem hasDerivAt_payG_NC (a q n t : ℝ) (ha : a < 1) (hq : 0 < q) (hn : 0 < n) (ht : 0 ≤ t) :
    HasDerivAt (payG a q n (1 - a)) (margNC a q n t) t := by
  have hc : 1 - a ≠ 0 := by linarith
  have hF : q + t + (1 - a) * n ≠ 0 := by nlinarith
  convert hasDerivAt_payG a q n (1 - a) t hc hq.ne' hF using 1
  unfold margNC
  field_simp
  ring

theorem hasDerivAt_payG_S (a q n t : ℝ) (ha : a < 1 / 2) (hq : 0 < q) (hn : 0 < n) (ht : 0 ≤ t) :
    HasDerivAt (payG a q n (1 - 2 * a)) (margStar a q n t) t := by
  have hc : 1 - 2 * a ≠ 0 := by linarith
  have hF : q + t + (1 - 2 * a) * n ≠ 0 := by nlinarith
  convert hasDerivAt_payG a q n (1 - 2 * a) t hc hq.ne' hF using 1
  unfold margStar
  field_simp
  ring


theorem eq_33_proof (a q n thetaBar cm : ℝ) (m : Fin 2 → ℝ) (i : Fin 2) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hq : 0 < q) (hn : 0 < n) (hθ : 0 < thetaBar) (hcm : 0 < cm) (hm : 0 ≤ m i.rev) (t : ℝ) (ht : 0 < t) : HasDerivAt (fun u : ℝ => eqPayoff a 0 q n thetaBar cm (Function.update m i u) i) (margNC a q n t - cm * t) t := by
  have hev : (fun u : ℝ => eqPayoff a 0 q n thetaBar cm (Function.update m i u) i) =ᶠ[nhds t]
      (fun u => thetaBar / (1 - a) * (thetaBar + (a - 1 / 2) * (thetaBar / (1 - a)))
        + payG a q n (1 - a) u - cm / 2 * u ^ 2) := by
    filter_upwards [lt_mem_nhds ht] with u hu
    have hmu : ∀ j, 0 ≤ Function.update m i u j := by
      intro j
      rcases eq_or_ne j i with rfl | hj
      · simp [hu.le]
      · have : j = i.rev := by
          revert hj; fin_cases i <;> fin_cases j <;> simp
        subst this; simp [hj, hm]
    rw [eqPayoff_NC a q n thetaBar cm _ i ha0 (by linarith) hq hn hmu]
    simp
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h1 := hasDerivAt_payG_NC a q n t (by linarith) hq hn ht.le
  have h2 := ((hasDerivAt_pow 2 t).const_mul (cm / 2))
  have := (h1.const_add (thetaBar / (1 - a) * (thetaBar + (a - 1 / 2) * (thetaBar / (1 - a))))).sub h2
  exact this.congr_deriv (by push_cast; ring)

theorem eq_44_proof (a q n thetaBar cm : ℝ) (m : Fin 2 → ℝ) (i : Fin 2) (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hq : 0 < q) (hn : 0 < n) (hθ : 0 < thetaBar) (hcm : 0 < cm) (hm : 0 ≤ m i.rev) (t : ℝ) (ht : 0 < t) : HasDerivAt (fun u : ℝ => eqPayoff a 1 q n thetaBar cm (Function.update m i u) i) (margStar a q n t - cm * t) t := by
  have hev : (fun u : ℝ => eqPayoff a 1 q n thetaBar cm (Function.update m i u) i) =ᶠ[nhds t]
      (fun u => payG a q n (1 - 2 * a) u + payR a q n (1 - 2 * a) (m i.rev) - cm / 2 * u ^ 2) := by
    filter_upwards [lt_mem_nhds ht] with u hu
    have hmu : ∀ j, 0 ≤ Function.update m i u j := by
      intro j
      rcases eq_or_ne j i with rfl | hj
      · simp [hu.le]
      · have : j = i.rev := by
          revert hj; fin_cases i <;> fin_cases j <;> simp
        subst this; simp [hj, hm]
    rw [eqPayoff_S a q n thetaBar cm _ i ha0 ha hq hn hmu]
    have : i.rev ≠ i := by fin_cases i <;> decide
    simp [this]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h1 := hasDerivAt_payG_S a q n t ha hq hn ht.le
  have h2 := ((hasDerivAt_pow 2 t).const_mul (cm / 2))
  have := (h1.add_const (payR a q n (1 - 2 * a) (m i.rev))).sub h2
  exact this.congr_deriv (by push_cast; ring)

end CompOpacity.Disclosure


namespace COOpt

open Set

theorem opt_unique (P g g' : ℝ → ℝ) (cm K : ℝ)
    (hP : ∀ t, 0 ≤ t → HasDerivAt P (g t) t)
    (hg : ∀ t, 0 ≤ t → HasDerivAt g (g' t) t)
    (hK : ∀ t, 0 ≤ t → g' t ≤ K) (hcm : K < cm) :
    ∃ m₀ : ℝ, 0 ≤ m₀ ∧
      (∀ t, 0 ≤ t → t ≠ m₀ → P t - cm / 2 * t ^ 2 < P m₀ - cm / 2 * m₀ ^ 2) ∧
      (g 0 ≤ 0 → m₀ = 0) ∧ (0 < g 0 → 0 < m₀ ∧ g m₀ - cm * m₀ = 0) := by
  set ψ : ℝ → ℝ := fun t => g t - cm * t with hψ
  set φ : ℝ → ℝ := fun t => P t - cm / 2 * t ^ 2 with hφ
  have hψd : ∀ t, 0 ≤ t → HasDerivAt ψ (g' t - cm) t := by
    intro t ht
    have := (hg t ht).sub ((hasDerivAt_id t).const_mul cm)
    exact this.congr_deriv (by simp)
  have hφd : ∀ t, 0 ≤ t → HasDerivAt φ (ψ t) t := by
    intro t ht
    have := (hP t ht).sub (((hasDerivAt_pow 2 t)).const_mul (cm / 2))
    refine this.congr_deriv ?_
    simp [hψ]; ring
  have hint : interior (Ici (0 : ℝ)) = Ioi 0 := interior_Ici
  have hψc : ContinuousOn ψ (Ici 0) := fun t ht => (hψd t ht).continuousAt.continuousWithinAt
  have hφc : ContinuousOn φ (Ici 0) := fun t ht => (hφd t ht).continuousAt.continuousWithinAt
  have hψa : StrictAntiOn ψ (Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0) hψc
    intro x hx; rw [hint] at hx
    rw [(hψd x (le_of_lt hx)).deriv]; linarith [hK x (le_of_lt hx)]
  have hψb : ∀ t, 0 ≤ t → ψ t ≤ ψ 0 + (K - cm) * t := by
    intro t ht
    have := (convex_Ici (0:ℝ)).image_sub_le_mul_sub_of_deriv_le hψc
      (fun x hx => by rw [hint] at hx; exact (hψd x (le_of_lt hx)).differentiableAt.differentiableWithinAt)
      (C := K - cm) (fun x hx => by
        rw [hint] at hx; rw [(hψd x (le_of_lt hx)).deriv]; linarith [hK x (le_of_lt hx)])
      0 ((Set.mem_Ici.2 le_rfl)) t ht ht
    linarith
  by_cases h0 : g 0 ≤ 0
  · refine ⟨0, le_rfl, ?_, fun _ => rfl, fun h => absurd h (not_lt.2 h0)⟩
    have hφa : StrictAntiOn φ (Ici 0) := by
      apply strictAntiOn_of_deriv_neg (convex_Ici 0) hφc
      intro x hx; rw [hint] at hx
      rw [(hφd x (le_of_lt hx)).deriv]
      have := hψa ((Set.mem_Ici.2 le_rfl)) (le_of_lt hx : (0:ℝ) ≤ x) hx
      simp only [hψ] at this ⊢; linarith
    intro t ht htne
    exact hφa (Set.mem_Ici.2 le_rfl) ht (lt_of_le_of_ne ht (Ne.symm htne))
  · rw [not_le] at h0
    set T := g 0 / (cm - K) + 1 with hT
    have hcK : 0 < cm - K := by linarith
    have hT0 : 0 < T := by rw [hT]; positivity
    have hψT : ψ T < 0 := by
      have := hψb T hT0.le
      have e : (K - cm) * T = -(g 0) - (cm - K) := by
        rw [hT]; field_simp; ring
      simp only [hψ] at this ⊢; simp at this; nlinarith
    have hψ0 : 0 < ψ 0 := by simp [hψ]; exact h0
    obtain ⟨m₀, hm₀, hψm⟩ : ∃ m₀ ∈ Icc 0 T, ψ m₀ = 0 := by
      have := intermediate_value_Icc' hT0.le (hψc.mono Icc_subset_Ici_self)
      exact this ⟨hψT.le, hψ0.le⟩
    have hm0pos : 0 < m₀ := by
      rcases eq_or_lt_of_le hm₀.1 with h | h
      · rw [← h] at hψm; linarith
      · exact h
    refine ⟨m₀, hm₀.1, ?_, fun h => absurd h (not_le.2 h0), fun _ => ⟨hm0pos, hψm⟩⟩
    have hmono : StrictMonoOn φ (Icc 0 m₀) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 m₀) (hφc.mono Icc_subset_Ici_self)
      intro x hx; rw [interior_Icc] at hx
      rw [(hφd x hx.1.le).deriv]
      have := hψa (le_of_lt hx.1 : (0:ℝ) ≤ x) (hm₀.1 : (0:ℝ) ≤ m₀) hx.2
      linarith
    have hanti : StrictAntiOn φ (Ici m₀) := by
      apply strictAntiOn_of_deriv_neg (convex_Ici m₀) (hφc.mono (Ici_subset_Ici.2 hm₀.1))
      intro x hx; rw [interior_Ici] at hx
      have hx0 : 0 ≤ x := le_trans hm₀.1 (le_of_lt hx)
      rw [(hφd x hx0).deriv]
      have := hψa (hm₀.1 : (0:ℝ) ≤ m₀) hx0 hx
      linarith
    intro t ht htne
    rcases lt_or_gt_of_ne htne with h | h
    · exact hmono ⟨ht, h.le⟩ ⟨hm₀.1, le_rfl⟩ h
    · exact hanti (le_refl m₀ : m₀ ∈ Ici m₀) (h.le : m₀ ≤ t) h

end COOpt


namespace CompOpacity.Disclosure

noncomputable def mg (q n C k c t : ℝ) : ℝ := (t + q - k * n) / (2 * C * (q + t + c * n) ^ 3)

lemma margNC_eq (a q n t : ℝ) : margNC a q n t = mg q n ((1 - a) ^ 2) ((1 - a) * (1 - 4 * a)) (1 - a) t := rfl
lemma margStar_eq (a q n t : ℝ) : margStar a q n t = mg q n (1 - 2 * a) (1 - 2 * a) (1 - 2 * a) t := rfl

theorem hasDerivAt_mg (q n C k c t : ℝ) (hC : C ≠ 0) (hF : q + t + c * n ≠ 0) :
    HasDerivAt (mg q n C k c) ((-2 * t - 2 * q + (c + 3 * k) * n) / (2 * C * (q + t + c * n) ^ 4)) t := by
  have h1 : HasDerivAt (fun t => t + q - k * n) 1 t := ((hasDerivAt_id t).add_const q).sub_const _
  have hF1 : HasDerivAt (fun t => q + t + c * n) 1 t :=
    ((hasDerivAt_id t).const_add q).add_const _
  have h2 := (hF1.pow 3).const_mul (2 * C)
  have := h1.div h2 (mul_ne_zero (mul_ne_zero two_ne_zero hC) (pow_ne_zero 3 hF))
  refine HasDerivAt.congr_deriv (f := mg q n C k c) this ?_
  norm_num
  generalize hFF : q + t + c * n = F at hF ⊢
  field_simp
  rw [← hFF]; ring

theorem mg_deriv_le (q n C k c t : ℝ) (hq : 0 < q) (hn : 0 < n) (hC : 0 < C) (hk : k ≤ 1)
    (hc : 0 < c) (hc1 : c ≤ 1) (ht : 0 ≤ t) :
    (-2 * t - 2 * q + (c + 3 * k) * n) / (2 * C * (q + t + c * n) ^ 4) ≤ 2 / (C * c * q ^ 3) := by
  have hF : 0 < q + t + c * n := by positivity
  have hF1 : q ≤ q + t + c * n := by nlinarith
  have hF2 : c * n ≤ q + t + c * n := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hX : -2 * t - 2 * q + (c + 3 * k) * n ≤ 4 * n := by nlinarith
  have hq3 : q ^ 3 ≤ (q + t + c * n) ^ 3 := by gcongr
  have hF4 : c * n * q ^ 3 ≤ (q + t + c * n) ^ 4 := by
    calc c * n * q ^ 3 ≤ (q + t + c * n) * (q + t + c * n) ^ 3 := by
          apply mul_le_mul hF2 hq3 (by positivity) hF.le
      _ = _ := by ring
  have hpos : 0 ≤ C * c * q ^ 3 := by positivity
  calc (-2 * t - 2 * q + (c + 3 * k) * n) * (C * c * q ^ 3) ≤ 4 * n * (C * c * q ^ 3) :=
        mul_le_mul_of_nonneg_right hX hpos
    _ = 4 * C * (c * n * q ^ 3) := by ring
    _ ≤ 4 * C * (q + t + c * n) ^ 4 := by gcongr
    _ = 2 * (2 * C * (q + t + c * n) ^ 4) := by ring

end CompOpacity.Disclosure


namespace CompOpacity.Disclosure

theorem de_char (a b q n thetaBar cm A m₀ : ℝ) (φ R : ℝ → ℝ)
    (hform : ∀ m' : Fin 2 → ℝ, (∀ j, 0 ≤ m' j) → ∀ i,
      eqPayoff a b q n thetaBar cm m' i = A + φ (m' i) + R (m' i.rev))
    (hm₀ : 0 ≤ m₀) (hmax : ∀ t, 0 ≤ t → t ≠ m₀ → φ t < φ m₀) :
    ∀ m : Fin 2 → ℝ, IsDisclosureEq a b q n thetaBar cm m ↔ m = fun _ => m₀ := by
  have hrev : ∀ i : Fin 2, i.rev ≠ i := by intro i; fin_cases i <;> decide
  have hupd : ∀ (m : Fin 2 → ℝ) (i : Fin 2) (t : ℝ), 0 ≤ t → (∀ j, 0 ≤ m j) →
      ∀ j, 0 ≤ Function.update m i t j := by
    intro m i t ht hm j
    rcases eq_or_ne j i with rfl | hj
    · simp [ht]
    · simp [hj, hm j]
  intro m
  constructor
  · intro H
    have hm : ∀ j, 0 ≤ m j := fun j => (H j).1
    funext i
    by_contra hne
    have h1 := (H i).2 m₀ hm₀
    rw [hform _ (hupd m i m₀ hm₀ hm), hform m hm] at h1
    simp [Function.update_of_ne (hrev i)] at h1
    have := hmax (m i) (hm i) hne
    linarith
  · rintro rfl i
    refine ⟨hm₀, fun t ht => ?_⟩
    rw [hform _ (hupd _ i t ht (fun _ => hm₀)), hform _ (fun _ => hm₀)]
    simp [Function.update_of_ne (hrev i)]
    rcases eq_or_ne t m₀ with rfl | htne
    · exact le_rfl
    · exact (hmax t ht htne).le

/-- generic optimization with the marginal `mg` -/
theorem opt_mg (q n C k c cm : ℝ) (P : ℝ → ℝ) (hq : 0 < q) (hn : 0 < n) (hC : 0 < C)
    (hk : k ≤ 1) (hc : 0 < c) (hc1 : c ≤ 1)
    (hP : ∀ t, 0 ≤ t → HasDerivAt P (mg q n C k c t) t)
    (hcm : 2 / (C * c * q ^ 3) < cm) :
    ∃ m₀ : ℝ, 0 ≤ m₀ ∧
      (∀ t, 0 ≤ t → t ≠ m₀ → P t - cm / 2 * t ^ 2 < P m₀ - cm / 2 * m₀ ^ 2) ∧
      (mg q n C k c 0 ≤ 0 → m₀ = 0) ∧
      (0 < mg q n C k c 0 → 0 < m₀ ∧ mg q n C k c m₀ - cm * m₀ = 0) := by
  apply COOpt.opt_unique P (mg q n C k c)
    (fun t => (-2 * t - 2 * q + (c + 3 * k) * n) / (2 * C * (q + t + c * n) ^ 4)) cm
    (2 / (C * c * q ^ 3)) hP
  · intro t ht
    exact hasDerivAt_mg q n C k c t hC.ne' (by positivity)
  · intro t ht; exact mg_deriv_le q n C k c t hq hn hC hk hc hc1 ht
  · exact hcm

end CompOpacity.Disclosure


namespace CompOpacity.Disclosure

/-- the b = 1 disclosure equilibrium for a fixed n -/
theorem eqS_char (a q n thetaBar cm : ℝ) (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hq : 0 < q) (hn : 0 < n)
    (hcm : 2 / ((1 - 2 * a) * (1 - 2 * a) * q ^ 3) < cm) :
    ∃ mS : ℝ, 0 ≤ mS ∧ (∀ t, 0 ≤ t → t ≠ mS →
        payG a q n (1 - 2 * a) t - cm / 2 * t ^ 2 < payG a q n (1 - 2 * a) mS - cm / 2 * mS ^ 2) ∧
      (∀ m : Fin 2 → ℝ, IsDisclosureEq a 1 q n thetaBar cm m ↔ m = fun _ => mS) ∧
      (n < q / (1 - 2 * a) → 0 < mS ∧ margStar a q n mS - cm * mS = 0) ∧
      (q / (1 - 2 * a) ≤ n → mS = 0) := by
  have hw : 0 < 1 - 2 * a := by linarith
  obtain ⟨m₀, hm₀, hmax, hz, hpos⟩ := opt_mg q n (1 - 2 * a) (1 - 2 * a) (1 - 2 * a) cm
    (payG a q n (1 - 2 * a)) hq hn hw (by linarith) hw (by linarith)
    (fun t ht => by rw [← funext (margStar_eq a q n)]; exact hasDerivAt_payG_S a q n t ha hq hn ht) hcm
  refine ⟨m₀, hm₀, hmax, ?_, ?_, ?_⟩
  · apply de_char a 1 q n thetaBar cm 0 m₀ (fun t => payG a q n (1 - 2 * a) t - cm / 2 * t ^ 2)
      (payR a q n (1 - 2 * a)) _ hm₀ hmax
    intro m' hm' i
    rw [eqPayoff_S a q n thetaBar cm m' i ha0 ha hq hn hm']; ring
  · intro hnq
    have : 0 < mg q n (1 - 2 * a) (1 - 2 * a) (1 - 2 * a) 0 := by
      unfold mg
      rw [lt_div_iff₀ hw] at hnq
      apply div_pos (by linarith) (by positivity)
    obtain ⟨h1, h2⟩ := hpos this
    exact ⟨h1, by rw [margStar_eq]; exact h2⟩
  · intro hnq
    apply hz
    unfold mg
    rw [div_le_iff₀ hw] at hnq
    apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem eq_46_47_proof (a q thetaBar : ℝ) (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hq : 0 < q) (hθ : 0 < thetaBar) : ∃ c₀ : ℝ, ∀ cm : ℝ, c₀ ≤ cm → ∀ n : ℝ, 0 < n → ∃ mS : ℝ, (∀ m : Fin 2 → ℝ, IsDisclosureEq a 1 q n thetaBar cm m ↔ m = fun _ => mS) ∧ (n < q / (1 - 2 * a) → 0 < mS ∧ margStar a q n mS - cm * mS = 0) ∧ (q / (1 - 2 * a) ≤ n → mS = 0) := by
  refine ⟨2 / ((1 - 2 * a) * (1 - 2 * a) * q ^ 3) + 1, fun cm hcm n hn => ?_⟩
  obtain ⟨mS, -, -, h1, h2, h3⟩ := eqS_char a q n thetaBar cm ha0 ha hq hn (by linarith)
  exact ⟨mS, h1, h2, h3⟩

/-- the b = 0 disclosure equilibrium for a fixed n -/
theorem eqNC_char (a q n thetaBar cm : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hq : 0 < q) (hn : 0 < n)
    (hcm : 2 / ((1 - a) ^ 2 * (1 - a) * q ^ 3) < cm) :
    ∃ mNC : ℝ, 0 ≤ mNC ∧ (∀ t, 0 ≤ t → t ≠ mNC →
        payG a q n (1 - a) t - cm / 2 * t ^ 2 < payG a q n (1 - a) mNC - cm / 2 * mNC ^ 2) ∧
      (∀ m : Fin 2 → ℝ, IsDisclosureEq a 0 q n thetaBar cm m ↔ m = fun _ => mNC) ∧
      ((1 - a) * (1 - 4 * a) * n < q → 0 < mNC ∧ margNC a q n mNC - cm * mNC = 0) ∧
      (q ≤ (1 - a) * (1 - 4 * a) * n → mNC = 0) := by
  have hv : 0 < 1 - a := by linarith
  obtain ⟨m₀, hm₀, hmax, hz, hpos⟩ := opt_mg q n ((1 - a) ^ 2) ((1 - a) * (1 - 4 * a)) (1 - a) cm
    (payG a q n (1 - a)) hq hn (by positivity) (by nlinarith) hv (by linarith)
    (fun t ht => by rw [← funext (margNC_eq a q n)]; exact hasDerivAt_payG_NC a q n t (by linarith) hq hn ht) hcm
  refine ⟨m₀, hm₀, hmax, ?_, ?_, ?_⟩
  · apply de_char a 0 q n thetaBar cm
      (thetaBar / (1 - a) * (thetaBar + (a - 1 / 2) * (thetaBar / (1 - a)))) m₀
      (fun t => payG a q n (1 - a) t - cm / 2 * t ^ 2) (fun _ => 0) _ hm₀ hmax
    intro m' hm' i
    rw [eqPayoff_NC a q n thetaBar cm m' i ha0 (by linarith) hq hn hm']; ring
  · intro hnq
    have : 0 < mg q n ((1 - a) ^ 2) ((1 - a) * (1 - 4 * a)) (1 - a) 0 := by
      unfold mg
      apply div_pos (by linarith) (by positivity)
    obtain ⟨h1, h2⟩ := hpos this
    exact ⟨h1, by rw [margNC_eq]; exact h2⟩
  · intro hnq
    apply hz
    unfold mg
    apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

lemma sqrt_cond (a q n : ℝ) (ha : a ≤ 1 / 2) (hq : 0 < q) (hn : 0 < n) :
    (5 / 8 - Real.sqrt (16 * q / n + 9) / 8 < a ↔ (1 - a) * (1 - 4 * a) * n < q) := by
  have hS := Real.sq_sqrt (show (0:ℝ) ≤ 16 * q / n + 9 by positivity)
  have hS0 := Real.sqrt_nonneg (16 * q / n + 9)
  set S := Real.sqrt (16 * q / n + 9)
  have key : (1 - a) * (1 - 4 * a) * n < q ↔ (5 - 8 * a) ^ 2 < S ^ 2 := by
    rw [hS]
    constructor
    · intro h
      have : (1 - a) * (1 - 4 * a) < q / n := by rw [lt_div_iff₀ hn]; linarith
      have e : 16 * q / n = 16 * (q / n) := by ring
      rw [e]; nlinarith
    · intro h
      have e : 16 * q / n = 16 * (q / n) := by ring
      rw [e] at h
      have : (1 - a) * (1 - 4 * a) < q / n := by nlinarith
      rw [lt_div_iff₀ hn] at this; linarith
  rw [key]
  constructor
  · intro h
    have h1 : 0 ≤ 5 - 8 * a := by linarith
    have : 5 - 8 * a < S := by linarith
    nlinarith
  · intro h
    have h1 : 0 ≤ 5 - 8 * a := by linarith
    have : 5 - 8 * a < S := by
      by_contra hc; push_neg at hc
      nlinarith
    linarith

theorem proposition_2_proof (a q thetaBar : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hq : 0 < q) (hθ : 0 < thetaBar) : ∃ c₀ : ℝ, ∀ cm : ℝ, c₀ ≤ cm → ∀ n : ℝ, 0 < n → ∃ mNC : ℝ, (∀ m : Fin 2 → ℝ, IsDisclosureEq a 0 q n thetaBar cm m ↔ m = fun _ => mNC) ∧ (5 / 8 - Real.sqrt (16 * q / n + 9) / 8 < a → 0 < mNC ∧ margNC a q n mNC - cm * mNC = 0) ∧ (a ≤ 5 / 8 - Real.sqrt (16 * q / n + 9) / 8 → mNC = 0) := by
  refine ⟨2 / ((1 - a) ^ 2 * (1 - a) * q ^ 3) + 1, fun cm hcm n hn => ?_⟩
  obtain ⟨mNC, -, -, h1, h2, h3⟩ := eqNC_char a q n thetaBar cm ha0 ha hq hn (by linarith)
  refine ⟨mNC, h1, fun h => h2 ((sqrt_cond a q n ha hq hn).1 h), fun h => h3 ?_⟩
  by_contra hc; push_neg at hc
  exact absurd ((sqrt_cond a q n ha hq hn).2 hc) (not_lt.2 h)

end CompOpacity.Disclosure


namespace CompOpacity.Disclosure

open Set

theorem psi_anti (q n C k c cm : ℝ) (hq : 0 < q) (hn : 0 < n) (hC : 0 < C)
    (hk : k ≤ 1) (hc : 0 < c) (hc1 : c ≤ 1) (hcm : 2 / (C * c * q ^ 3) < cm) :
    StrictAntiOn (fun t => mg q n C k c t - cm * t) (Ici 0) := by
  have hd : ∀ t, 0 ≤ t → HasDerivAt (fun t => mg q n C k c t - cm * t)
      ((-2 * t - 2 * q + (c + 3 * k) * n) / (2 * C * (q + t + c * n) ^ 4) - cm) t := by
    intro t ht
    have := (hasDerivAt_mg q n C k c t hC.ne' (by positivity)).sub ((hasDerivAt_id t).const_mul cm)
    exact this.congr_deriv (by simp)
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  intro x hx; rw [interior_Ici] at hx
  rw [(hd x (le_of_lt hx)).deriv]
  have := mg_deriv_le q n C k c x hq hn hC hk hc hc1 (le_of_lt hx)
  linarith

theorem margNC_anti_n (a q t n₁ n₂ : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hq : 0 < q) (ht : 0 ≤ t)
    (hn₁ : 0 < n₁) (h12 : n₁ < n₂) (hpos : 0 < margNC a q n₂ t) :
    margNC a q n₂ t < margNC a q n₁ t := by
  unfold margNC at *
  have hv : 0 < 1 - a := by linarith
  have hn₂ : 0 < n₂ := by linarith
  set k := (1 - a) * (1 - 4 * a)
  set v := 1 - a
  have hF1 : 0 < q + t + v * n₁ := by positivity
  have hF2 : 0 < q + t + v * n₂ := by positivity
  have hN2 : 0 < t + q - k * n₂ := by
    by_contra hc; push_neg at hc
    have : (t + q - k * n₂) / (2 * v ^ 2 * (q + t + v * n₂) ^ 3) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hc (by positivity)
    linarith
  have hvk : 0 ≤ v + k := by simp only [v, k]; nlinarith
  have hcross : (t + q - k * n₂) * (q + t + v * n₁) ≤ (t + q - k * n₁) * (q + t + v * n₂) := by
    have : (t + q - k * n₁) * (q + t + v * n₂) - (t + q - k * n₂) * (q + t + v * n₁)
        = (q + t) * (v + k) * (n₂ - n₁) := by ring
    have : 0 ≤ (q + t) * (v + k) * (n₂ - n₁) := by
      apply mul_nonneg (mul_nonneg (by linarith) hvk) (by linarith)
    linarith
  have hFF : (q + t + v * n₁) ^ 2 < (q + t + v * n₂) ^ 2 := by
    have : q + t + v * n₁ < q + t + v * n₂ := by nlinarith
    gcongr
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hP : 0 < (t + q - k * n₂) * (q + t + v * n₁) := mul_pos hN2 hF1
  have key : (t + q - k * n₂) * (q + t + v * n₁) ^ 3 < (t + q - k * n₁) * (q + t + v * n₂) ^ 3 := by
    calc (t + q - k * n₂) * (q + t + v * n₁) ^ 3
        = ((t + q - k * n₂) * (q + t + v * n₁)) * (q + t + v * n₁) ^ 2 := by ring
      _ < ((t + q - k * n₂) * (q + t + v * n₁)) * (q + t + v * n₂) ^ 2 :=
          mul_lt_mul_of_pos_left hFF hP
      _ ≤ ((t + q - k * n₁) * (q + t + v * n₂)) * (q + t + v * n₂) ^ 2 :=
          mul_le_mul_of_nonneg_right hcross (by positivity)
      _ = (t + q - k * n₁) * (q + t + v * n₂) ^ 3 := by ring
  have h2v : 0 < 2 * v ^ 2 := by positivity
  nlinarith [mul_lt_mul_of_pos_left key h2v]

theorem mNC_anti_core (a q thetaBar cm : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hq : 0 < q)
    (hcm' : 2 / ((1 - a) ^ 2 * (1 - a) * q ^ 3) < cm) (n₁ n₂ m₁ m₂ : ℝ) (hn₁ : 0 < n₁)
    (h12 : n₁ ≤ n₂) (H1 : IsDisclosureEq a 0 q n₁ thetaBar cm (fun _ => m₁))
    (H2 : IsDisclosureEq a 0 q n₂ thetaBar cm (fun _ => m₂)) :
    m₂ ≤ m₁ ∧ (n₁ < n₂ → 0 < m₁ → m₂ < m₁) := by
  have hv : 0 < 1 - a := by linarith
  have hn₂ : 0 < n₂ := by linarith
  have hcm0 : 0 < cm := lt_of_le_of_lt (by positivity) hcm'
  -- facts about each equilibrium
  have facts : ∀ n m : ℝ, 0 < n → IsDisclosureEq a 0 q n thetaBar cm (fun _ => m) →
      0 ≤ m ∧ (0 < m → margNC a q n m - cm * m = 0) ∧ (m = 0 → margNC a q n 0 ≤ 0) := by
    intro n m hn H
    obtain ⟨mNC, hm0, -, hiff, hint, hzero⟩ := eqNC_char a q n thetaBar cm ha0 ha hq hn hcm'
    have hm : m = mNC := congrFun ((hiff _).1 H) 0
    subst hm
    refine ⟨hm0, fun hp => ?_, fun hz => ?_⟩
    · by_cases hc : (1 - a) * (1 - 4 * a) * n < q
      · exact (hint hc).2
      · have := hzero (not_lt.1 hc); linarith
    · by_contra hc; push_neg at hc
      have hlt : (1 - a) * (1 - 4 * a) * n < q := by
        unfold margNC at hc
        by_contra hc2; push_neg at hc2
        have : (0 + q - (1 - a) * (1 - 4 * a) * n) / (2 * (1 - a) ^ 2 * (q + 0 + (1 - a) * n) ^ 3) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
        linarith
      have := (hint hlt).1; linarith
  obtain ⟨hm1, hi1, hz1⟩ := facts n₁ m₁ hn₁ H1
  obtain ⟨hm2, hi2, hz2⟩ := facts n₂ m₂ hn₂ H2
  have hψ := psi_anti q n₁ ((1 - a) ^ 2) ((1 - a) * (1 - 4 * a)) (1 - a) cm hq hn₁ (by positivity)
    (by nlinarith) hv (by linarith) hcm'
  have hψ1 : margNC a q n₁ m₁ - cm * m₁ ≤ 0 := by
    rcases eq_or_lt_of_le hm1 with h | h
    · rw [← h]; have := hz1 h.symm; simpa using this
    · rw [hi1 h]
  constructor
  · by_contra hc; push_neg at hc
    have hm2p : 0 < m₂ := lt_of_le_of_lt hm1 hc
    have e2 := hi2 hm2p
    have hlt : margNC a q n₁ m₂ - cm * m₂ < margNC a q n₁ m₁ - cm * m₁ := by
      have := hψ (mem_Ici.2 hm1) (mem_Ici.2 hm2p.le) hc
      simpa [margNC_eq] using this
    rcases eq_or_lt_of_le h12 with h | h
    · subst h; linarith
    · have := margNC_anti_n a q m₂ n₁ n₂ ha0 ha hq hm2p.le hn₁ h (by have := mul_pos hcm0 hm2p; linarith)
      linarith
  · intro h hm1p
    by_contra hc; push_neg at hc
    have hm2p : 0 < m₂ := lt_of_lt_of_le hm1p hc
    have e2 := hi2 hm2p
    have hle : margNC a q n₁ m₂ - cm * m₂ ≤ margNC a q n₁ m₁ - cm * m₁ := by
      rcases eq_or_lt_of_le hc with h' | h'
      · rw [h']
      · have := hψ (mem_Ici.2 hm1) (mem_Ici.2 hm2p.le) h'
        exact le_of_lt (by simpa [margNC_eq] using this)
    have := margNC_anti_n a q m₂ n₁ n₂ ha0 ha hq hm2p.le hn₁ h (by have := mul_pos hcm0 hm2p; linarith)
    have := hi1 hm1p
    linarith

theorem mNC_antitone_proof (a q thetaBar : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hq : 0 < q) (hθ : 0 < thetaBar) : ∃ c₀ : ℝ, ∀ cm : ℝ, c₀ ≤ cm → ∀ n₁ n₂ m₁ m₂ : ℝ, 0 < n₁ → n₁ ≤ n₂ → IsDisclosureEq a 0 q n₁ thetaBar cm (fun _ => m₁) → IsDisclosureEq a 0 q n₂ thetaBar cm (fun _ => m₂) → m₂ ≤ m₁ ∧ (n₁ < n₂ → 0 < m₁ → m₂ < m₁) :=
  ⟨2 / ((1 - a) ^ 2 * (1 - a) * q ^ 3) + 1, fun cm hcm n₁ n₂ m₁ m₂ hn₁ h12 H1 H2 =>
    mNC_anti_core a q thetaBar cm ha0 ha hq (by linarith) n₁ n₂ m₁ m₂ hn₁ h12 H1 H2⟩

end CompOpacity.Disclosure


namespace CompOpacity.Disclosure

open Set

theorem prop4_part1 (q thetaBar : ℝ) (hq : 0 < q) (hθ : 0 < thetaBar) : ∀ b : ℝ, 0 < b → b ≤ 1 → ∀ n : ℝ, 0 < n → ∃ c₀ : ℝ, ∀ cm : ℝ, c₀ ≤ cm → ∃ m₀ : ℝ, (∀ m : Fin 2 → ℝ, IsDisclosureEq 0 b q n thetaBar cm m ↔ m = fun _ => m₀) ∧ (∀ m : Fin 2 → ℝ, IsDisclosureEq 0 0 q n thetaBar cm m ↔ m = fun _ => m₀) := by
  intro b hb _ n hn
  refine ⟨2 / ((1 - 0) ^ 2 * (1 - 0) * q ^ 3) + 1, fun cm hcm => ?_⟩
  obtain ⟨m₀, hm₀, hmax, hiff, -, -⟩ := eqNC_char 0 q n thetaBar cm le_rfl (by norm_num) hq hn
    (by linarith)
  refine ⟨m₀, ?_, hiff⟩
  apply de_char 0 b q n thetaBar cm (thetaBar * (1 - b) * (thetaBar - thetaBar * (1 - b) / 2)) m₀
    (fun t => payG 0 q n (1 - 0) t - cm / 2 * t ^ 2) (fun t => b ^ 2 * payR 0 q n 1 t) _ hm₀ hmax
  intro m' hm' i
  rw [eqPayoff_Z b q n thetaBar cm m' i hb hq hn hm', sub_zero]; ring



theorem mS_bound (a q n cm s : ℝ) (ha : a < 1 / 2) (hq : 0 < q) (hn : 0 < n) (hs : 0 < s)
    (hcm : 0 < cm) (hfoc : margStar a q n s - cm * s = 0) :
    s * (2 * (1 - 2 * a) * q ^ 3 * cm - 1) ≤ q - (1 - 2 * a) * n := by
  have hw : 0 < 1 - 2 * a := by linarith
  unfold margStar at hfoc
  have hF : q ≤ q + s + (1 - 2 * a) * n := by
    have : 0 ≤ (1 - 2 * a) * n := by positivity
    linarith
  have hden : 2 * (1 - 2 * a) * q ^ 3 ≤ 2 * (1 - 2 * a) * (q + s + (1 - 2 * a) * n) ^ 3 := by
    gcongr
  have hden0 : 0 < 2 * (1 - 2 * a) * (q + s + (1 - 2 * a) * n) ^ 3 := by positivity
  have e : (s + q - (1 - 2 * a) * n) / (2 * (1 - 2 * a) * (q + s + (1 - 2 * a) * n) ^ 3) = cm * s := by
    linarith
  have hfoc' : cm * s * (2 * (1 - 2 * a) * (q + s + (1 - 2 * a) * n) ^ 3)
      = s + q - (1 - 2 * a) * n := by
    rw [← e]; field_simp
  have hcs : 0 ≤ cm * s := by positivity
  have h1 := mul_le_mul_of_nonneg_left hden hcs
  have : s * (2 * (1 - 2 * a) * q ^ 3 * cm - 1) = cm * s * (2 * (1 - 2 * a) * q ^ 3) - s := by ring
  rw [this]
  linarith

theorem threshold_of (P : ℝ → Prop) (n₀ n₁ : ℝ) (hn₀ : 0 < n₀) (hnot : ¬ P n₀)
    (hn₁ : 0 < n₁) (hP₁ : P n₁)
    (upset : ∀ x y, 0 < x → P x → x < y → P y)
    (openL : ∀ n, 0 < n → P n → ∃ n', 0 < n' ∧ n' < n ∧ P n') :
    ∃ nhat : ℝ, 0 < nhat ∧ ∀ n, 0 < n → (P n ↔ nhat < n) := by
  let T := {n : ℝ | 0 < n ∧ P n}
  have hTne : T.Nonempty := ⟨n₁, hn₁, hP₁⟩
  have hTbdd : BddBelow T := ⟨0, fun t ht => ht.1.le⟩
  refine ⟨sInf T, ?_, fun n hn => ⟨fun hPn => ?_, fun h => ?_⟩⟩
  · apply lt_of_lt_of_le hn₀
    apply le_csInf hTne
    intro t ht
    by_contra hc; push_neg at hc
    exact hnot (upset t n₀ ht.1 ht.2 hc)
  · obtain ⟨n', h1, h2, h3⟩ := openL n hn hPn
    exact lt_of_le_of_lt (csInf_le hTbdd ⟨h1, h3⟩) h2
  · obtain ⟨t, ht, htn⟩ := exists_lt_of_csInf_lt hTne h
    exact upset t n ht.1 ht.2 htn

theorem kw_lt (a q n : ℝ) (ha0 : 0 < a) (ha : a < 1 / 2) (hn : 0 < n) (h : n < q / (1 - 2 * a)) :
    (1 - a) * (1 - 4 * a) * n < q := by
  have hw : 0 < 1 - 2 * a := by linarith
  rw [lt_div_iff₀ hw] at h
  have : 0 < a * (3 - 4 * a) * n := mul_pos (mul_pos ha0 (by linarith)) hn
  nlinarith

/-- characterization of the comparison for small n -/
theorem char_lemma (a q n cm Δ mS mN : ℝ) (ha0 : 0 < a) (ha : a < 1 / 2) (hq : 0 < q) (hn : 0 < n)
    (hs : 0 < mS) (hsF : margStar a q n mS - cm * mS = 0)
    (hm : 0 < mN) (hmF : margNC a q n mN - cm * mN = 0)
    (ψS : StrictAntiOn (fun t => margStar a q n t - cm * t) (Set.Ici 0))
    (hΔ : ∀ x : ℝ, 0 < x → (Lpoly a x < 0 ↔ Δ < x)) :
    ((mS ≤ mN ∧ (0 < mN → mS < mN)) ↔ Δ < n / (q + mN)) := by
  have e1 : (mS ≤ mN ∧ (0 < mN → mS < mN)) ↔ mS < mN :=
    ⟨fun h => h.2 hm, fun h => ⟨h.le, fun _ => h⟩⟩
  have e2 : mS < mN ↔ margStar a q n mN - cm * mN < 0 := by
    constructor
    · intro h'
      have := ψS (Set.mem_Ici.2 hs.le) (Set.mem_Ici.2 hm.le) h'
      simp only at this; linarith
    · intro h'
      by_contra hc; push_neg at hc
      rcases eq_or_lt_of_le hc with h'' | h''
      · rw [h''] at h'; linarith
      · have := ψS (Set.mem_Ici.2 hm.le) (Set.mem_Ici.2 hs.le) h''
        simp only at this; linarith
  have e3 : margStar a q n mN - cm * mN = margStar a q n mN - margNC a q n mN := by linarith
  rw [e1, e2, e3, eq_50_53 a q n mN ha0 ha hq hn hm.le]
  have hw : 0 < 1 - 2 * a := by linarith
  have hv : 0 < 1 - a := by linarith
  have hF1 : 0 < q + mN + (1 - a) * n := by positivity
  have hF2 : 0 < q + mN + (1 - 2 * a) * n := by positivity
  have hc : 0 < (q + mN) ^ 4 / (2 * (1 - a) ^ 2 * (1 - 2 * a)) := by positivity
  have hx0 : 0 < n / (q + mN) := by positivity
  rw [← hΔ _ hx0]
  constructor
  · intro h'
    by_contra hc'; push_neg at hc'
    have : 0 ≤ (q + mN) ^ 4 / (2 * (1 - a) ^ 2 * (1 - 2 * a)) * Lpoly a (n / (q + mN)) /
        ((q + mN + (1 - a) * n) ^ 3 * (q + mN + (1 - 2 * a) * n) ^ 3) := by positivity
    linarith
  · intro h'
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hc h') (by positivity)

/-- openness to the left at a small n -/
theorem open_small (a q n cm Δ : ℝ) (mN : ℝ → ℝ) (ha0 : 0 < a) (ha : a < 1 / 2) (hq : 0 < q)
    (hn : 0 < n) (hΔ0 : 0 < Δ) (hb : n < q / (1 - 2 * a))
    (hN0' : ∀ n, 0 < n → 0 ≤ mN n)
    (hN2 : ∀ n, 0 < n → (1 - a) * (1 - 4 * a) * n < q → 0 < mN n ∧ margNC a q n (mN n) - cm * mN n = 0)
    (ψN : ∀ n, 0 < n → StrictAntiOn (fun t => margNC a q n t - cm * t) (Set.Ici 0))
    (hPn : Δ < n / (q + mN n)) :
    ∃ n', 0 < n' ∧ n' < n ∧ Δ < n' / (q + mN n') := by
  have hw : 0 < 1 - 2 * a := by linarith
  have hv : 0 < 1 - a := by linarith
  have hm0 : 0 ≤ mN n := hN0' n hn
  have hqm : 0 < q + mN n := by linarith
  have hxn : Δ * (q + mN n) < n := by rwa [lt_div_iff₀ hqm] at hPn
  obtain ⟨ε, hεpos, hΔε⟩ : ∃ ε : ℝ, 0 < ε ∧ Δ * (q + mN n + ε) < n := by
    refine ⟨(n - Δ * (q + mN n)) / (2 * Δ), by apply div_pos (by linarith) (by positivity), ?_⟩
    have : Δ * ((n - Δ * (q + mN n)) / (2 * Δ)) = (n - Δ * (q + mN n)) / 2 := by
      field_simp
    nlinarith
  have c1 : ContinuousAt (fun n' : ℝ => margNC a q n' (mN n + ε)) n := by
    unfold margNC
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    have : 0 < q + (mN n + ε) + (1 - a) * n := by positivity
    positivity
  have hlt1 : margNC a q n (mN n + ε) < cm * (mN n + ε) := by
    have hfoc := (hN2 n hn (kw_lt a q n ha0 ha hn hb)).2
    have := ψN n hn (Set.mem_Ici.2 hm0) (Set.mem_Ici.2 (by linarith : (0:ℝ) ≤ mN n + ε))
      (by linarith : mN n < mN n + ε)
    simp only at this; linarith
  have ev1 := c1.eventually_lt continuousAt_const hlt1
  have c2 : ContinuousAt (fun n' : ℝ => n' / (q + mN n + ε)) n := by fun_prop
  have hlt2 : Δ < n / (q + mN n + ε) := by rw [lt_div_iff₀ (by positivity)]; linarith
  have ev2 := continuousAt_const.eventually_lt c2 hlt2
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (ev1.and ev2)
  have hmin : 0 < min δ n := lt_min hδ hn
  have hmin2 : min δ n ≤ n := min_le_right δ n
  have hmin1 : min δ n ≤ δ := min_le_left δ n
  have hn'pos : 0 < n - min δ n / 2 := by linarith
  have hn'lt : n - min δ n / 2 < n := by linarith
  have hdist : dist (n - min δ n / 2) n < δ := by
    rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith
  obtain ⟨hA, hB⟩ := hball hdist
  refine ⟨n - min δ n / 2, hn'pos, hn'lt, ?_⟩
  set n' := n - min δ n / 2
  have hn'w : n' < q / (1 - 2 * a) := by linarith
  obtain ⟨hmp', hfoc'⟩ := hN2 n' hn'pos (kw_lt a q n' ha0 ha hn'pos hn'w)
  have hlt : mN n' < mN n + ε := by
    by_contra hc; push_neg at hc
    rcases eq_or_lt_of_le hc with h | h
    · rw [h] at hA; linarith
    · have := ψN n' hn'pos (Set.mem_Ici.2 (by linarith : (0:ℝ) ≤ mN n + ε)) (Set.mem_Ici.2 hmp'.le) h
      simp only at this hA; linarith
  calc Δ < n' / (q + mN n + ε) := hB
    _ < n' / (q + mN n') := by
        apply div_lt_div_of_pos_left hn'pos (by linarith) (by linarith)

theorem open_big (a q cm : ℝ) (mS mN : ℝ → ℝ) (ha0 : 0 < a) (ha : a < 1 / 2) (hq : 0 < q)
    (hcm0 : 0 < cm) (hD : 0 < 2 * (1 - 2 * a) * q ^ 3 * cm - 1)
    (hS2 : ∀ n, 0 < n → n < q / (1 - 2 * a) → 0 < mS n ∧ margStar a q n (mS n) - cm * mS n = 0)
    (hN2 : ∀ n, 0 < n → (1 - a) * (1 - 4 * a) * n < q → 0 < mN n ∧ margNC a q n (mN n) - cm * mN n = 0)
    (anti : ∀ n₁ n₂, 0 < n₁ → n₁ ≤ n₂ → mN n₂ ≤ mN n₁) :
    ∃ n', 0 < n' ∧ n' < q / (1 - 2 * a) ∧ mS n' < mN n' := by
  have hw : 0 < 1 - 2 * a := by linarith
  have hqw : 0 < q / (1 - 2 * a) := by positivity
  set D := 2 * (1 - 2 * a) * q ^ 3 * cm - 1 with hDdef
  set M := mN (q / (1 - 2 * a)) with hM
  have hkq : (1 - a) * (1 - 4 * a) * (q / (1 - 2 * a)) < q := by
    have : (1 - a) * (1 - 4 * a) < 1 - 2 * a := by nlinarith
    have e : (1 - 2 * a) * (q / (1 - 2 * a)) = q := by field_simp
    nlinarith
  have hMpos : 0 < M := (hN2 _ hqw hkq).1
  have hmin : 0 < min (M * D) q := lt_min (mul_pos hMpos hD) hq
  have hmle : min (M * D) q ≤ q := min_le_right _ _
  have hmle' : min (M * D) q ≤ M * D := min_le_left _ _
  have hn'pos : 0 < q / (1 - 2 * a) - min (M * D) q / (2 * (1 - 2 * a)) := by
    have e : q / (1 - 2 * a) - min (M * D) q / (2 * (1 - 2 * a))
        = (2 * q - min (M * D) q) / (2 * (1 - 2 * a)) := by field_simp
    rw [e]; apply div_pos (by linarith) (by positivity)
  have hn'lt : q / (1 - 2 * a) - min (M * D) q / (2 * (1 - 2 * a)) < q / (1 - 2 * a) := by
    have : 0 < min (M * D) q / (2 * (1 - 2 * a)) := by positivity
    linarith
  refine ⟨_, hn'pos, hn'lt, ?_⟩
  set n' := q / (1 - 2 * a) - min (M * D) q / (2 * (1 - 2 * a))
  have hmN' : M ≤ mN n' := anti n' (q / (1 - 2 * a)) hn'pos hn'lt.le
  obtain ⟨hs, hsF⟩ := hS2 n' hn'pos hn'lt
  have hwn : q - (1 - 2 * a) * n' = min (M * D) q / 2 := by
    simp only [n']; field_simp; ring
  have hb := mS_bound a q n' cm (mS n') ha hq hn'pos hs hcm0 hsF
  rw [hwn] at hb
  have h1 : mS n' * D < M * D := by linarith
  have := lt_of_mul_lt_mul_right h1 hD.le
  linarith

end CompOpacity.Disclosure


namespace CompOpacity.Disclosure

theorem prop4_part2_red (q thetaBar : ℝ) (hq : 0 < q) (hθ : 0 < thetaBar) : ∀ a : ℝ, 0 < a → a < 1 / 2 → ∃ c₀ : ℝ, ∀ cm : ℝ, c₀ ≤ cm → ∃ nhat : ℝ, 0 < nhat ∧ ∀ n : ℝ, 0 < n → ∃ mS mNC : ℝ, (∀ m : Fin 2 → ℝ, IsDisclosureEq a 1 q n thetaBar cm m ↔ m = fun _ => mS) ∧ (∀ m : Fin 2 → ℝ, IsDisclosureEq a 0 q n thetaBar cm m ↔ m = fun _ => mNC) ∧ ((mS ≤ mNC ∧ (0 < mNC → mS < mNC)) ↔ nhat < n) := by
  intro a ha0 ha
  have hw : 0 < 1 - 2 * a := by linarith
  have hv : 0 < 1 - a := by linarith
  obtain ⟨cS, hcS⟩ := eq_46_47 a q thetaBar ha0.le ha hq hθ
  obtain ⟨cN, hcN⟩ := proposition_2 a q thetaBar ha0.le ha.le hq hθ
  obtain ⟨cA, hcA⟩ := mNC_antitone a q thetaBar ha0.le ha.le hq hθ
  refine ⟨max (max cS cN) (max cA (2 / ((1 - 2 * a) * (1 - 2 * a) * q ^ 3)
    + 2 / ((1 - a) ^ 2 * (1 - a) * q ^ 3) + 1)), fun cm hcm' => ?_⟩
  have hcm := le_trans (le_max_right cA _) (le_trans (le_max_right _ _) hcm')
  have hcmSS : cS ≤ cm := le_trans (le_max_left cS cN) (le_trans (le_max_left _ _) hcm')
  have hcmNN : cN ≤ cm := le_trans (le_max_right cS cN) (le_trans (le_max_left _ _) hcm')
  have hcmA : cA ≤ cm := le_trans (le_max_left cA _) (le_trans (le_max_right _ _) hcm')
  have hS0 : 0 ≤ 2 / ((1 - 2 * a) * (1 - 2 * a) * q ^ 3) := by positivity
  have hN0 : 0 ≤ 2 / ((1 - a) ^ 2 * (1 - a) * q ^ 3) := by positivity
  have hcmS : 2 / ((1 - 2 * a) * (1 - 2 * a) * q ^ 3) < cm := by linarith
  have hcmN : 2 / ((1 - a) ^ 2 * (1 - a) * q ^ 3) < cm := by linarith
  have hcm0 : 0 < cm := by linarith
  have hD : 0 < 2 * (1 - 2 * a) * q ^ 3 * cm - 1 := by
    have h1 : 1 / ((1 - 2 * a) * q ^ 3) ≤ 2 / ((1 - 2 * a) * (1 - 2 * a) * q ^ 3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (1 - 2 * a) ≤ 1 := by linarith
      have hq3 : 0 < q ^ 3 := by positivity
      nlinarith [mul_pos hw hq3]
    have h2 : 1 / ((1 - 2 * a) * q ^ 3) < cm := by linarith
    rw [div_lt_iff₀ (by positivity)] at h2
    linarith
  have hS : ∀ n, 0 < n → ∃ mS : ℝ, 0 ≤ mS ∧
      (∀ m : Fin 2 → ℝ, IsDisclosureEq a 1 q n thetaBar cm m ↔ m = fun _ => mS) ∧
      (n < q / (1 - 2 * a) → 0 < mS ∧ margStar a q n mS - cm * mS = 0) ∧
      (q / (1 - 2 * a) ≤ n → mS = 0) := by
    intro n hn
    obtain ⟨mS, h1, h2, h3⟩ := hcS cm hcmSS n hn
    exact ⟨mS, ((h1 _).2 rfl 0).1, h1, h2, h3⟩
  have hN : ∀ n, 0 < n → ∃ mNC : ℝ, 0 ≤ mNC ∧
      (∀ m : Fin 2 → ℝ, IsDisclosureEq a 0 q n thetaBar cm m ↔ m = fun _ => mNC) ∧
      ((1 - a) * (1 - 4 * a) * n < q → 0 < mNC ∧ margNC a q n mNC - cm * mNC = 0) := by
    intro n hn
    obtain ⟨mNC, h1, h2, -⟩ := hcN cm hcmNN n hn
    exact ⟨mNC, ((h1 _).2 rfl 0).1, h1,
      fun h => h2 ((sqrt_cond a q n ha.le hq hn).2 h)⟩
  choose! mS hS0' hS1 hS2 hS3 using hS
  choose! mN hN0' hN1 hN2 using hN
  have anti : ∀ n₁ n₂, 0 < n₁ → n₁ ≤ n₂ → mN n₂ ≤ mN n₁ := by
    intro n₁ n₂ h1 h12
    exact (hcA cm hcmA n₁ n₂ (mN n₁) (mN n₂) h1 h12
      ((hN1 n₁ h1 _).2 rfl) ((hN1 n₂ (by linarith) _).2 rfl)).1
  have ψS : ∀ n, 0 < n → StrictAntiOn (fun t => margStar a q n t - cm * t) (Set.Ici 0) :=
    fun n hn => psi_anti q n (1 - 2 * a) (1 - 2 * a) (1 - 2 * a) cm hq hn hw (by linarith) hw
      (by linarith) hcmS
  have ψN : ∀ n, 0 < n → StrictAntiOn (fun t => margNC a q n t - cm * t) (Set.Ici 0) :=
    fun n hn => psi_anti q n ((1 - a) ^ 2) ((1 - a) * (1 - 4 * a)) (1 - a) cm hq hn (by positivity)
      (by nlinarith) hv (by linarith) hcmN
  obtain ⟨Δ, hΔ0, -, -, hΔ⟩ := L_unique_root a ha0 ha
  have hqw : 0 < q / (1 - 2 * a) := by positivity
  -- characterization
  have char : ∀ n, 0 < n → n < q / (1 - 2 * a) →
      ((mS n ≤ mN n ∧ (0 < mN n → mS n < mN n)) ↔ Δ < n / (q + mN n)) := by
    intro n hn h
    obtain ⟨hs, hsF⟩ := hS2 n hn h
    obtain ⟨hm, hmF⟩ := hN2 n hn (kw_lt a q n ha0 ha hn h)
    exact char_lemma a q n cm Δ (mS n) (mN n) ha0 ha hq hn hs hsF hm hmF (ψS n hn) hΔ
  have big : ∀ n, 0 < n → q / (1 - 2 * a) ≤ n → (mS n ≤ mN n ∧ (0 < mN n → mS n < mN n)) := by
    intro n hn h
    rw [hS3 n hn h]
    exact ⟨hN0' n hn, id⟩
  have xmono : ∀ n₁ n₂, 0 < n₁ → n₁ < n₂ → n₁ / (q + mN n₁) < n₂ / (q + mN n₂) := by
    intro n₁ n₂ h1 h12
    have hm := anti n₁ n₂ h1 h12.le
    have h0 := hN0' n₂ (by linarith)
    have h0' := hN0' n₁ h1
    calc n₁ / (q + mN n₁) < n₂ / (q + mN n₁) := by
          apply div_lt_div_of_pos_right h12; linarith
      _ ≤ n₂ / (q + mN n₂) := by
          apply div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  have upset : ∀ x y, 0 < x → (mS x ≤ mN x ∧ (0 < mN x → mS x < mN x)) → x < y →
      (mS y ≤ mN y ∧ (0 < mN y → mS y < mN y)) := by
    intro x y hx hPx hxy
    by_cases hb : q / (1 - 2 * a) ≤ y
    · exact big y (by linarith) hb
    · push_neg at hb
      rw [char y (by linarith) hb]
      rw [char x hx (by linarith)] at hPx
      exact hPx.trans (xmono x y hx hxy)
  -- small point
  have hn₀0 : 0 < min (q * Δ) (q / (1 - 2 * a)) / 2 := by
    have := lt_min (mul_pos hq hΔ0) hqw; linarith
  have hn₀w : min (q * Δ) (q / (1 - 2 * a)) / 2 < q / (1 - 2 * a) := by
    have := min_le_right (q * Δ) (q / (1 - 2 * a)); linarith
  have hnot : ¬ (mS (min (q * Δ) (q / (1 - 2 * a)) / 2) ≤ mN (min (q * Δ) (q / (1 - 2 * a)) / 2) ∧
      (0 < mN (min (q * Δ) (q / (1 - 2 * a)) / 2) →
        mS (min (q * Δ) (q / (1 - 2 * a)) / 2) < mN (min (q * Δ) (q / (1 - 2 * a)) / 2))) := by
    rw [char _ hn₀0 hn₀w]
    intro h
    set n₀ := min (q * Δ) (q / (1 - 2 * a)) / 2 with hn₀
    have h1 : n₀ / (q + mN n₀) ≤ n₀ / q := by
      apply div_le_div_of_nonneg_left hn₀0.le hq (by linarith [hN0' n₀ hn₀0])
    have h2 : n₀ / q < Δ := by
      rw [div_lt_iff₀ hq]
      have := min_le_left (q * Δ) (q / (1 - 2 * a))
      have : n₀ ≤ q * Δ / 2 := by rw [hn₀]; linarith
      nlinarith
    linarith
  have openL : ∀ n, 0 < n → (mS n ≤ mN n ∧ (0 < mN n → mS n < mN n)) →
      ∃ n', 0 < n' ∧ n' < n ∧ (mS n' ≤ mN n' ∧ (0 < mN n' → mS n' < mN n')) := by
    intro n hn hPn
    by_cases hb : q / (1 - 2 * a) ≤ n
    · obtain ⟨n', h1, h2, h3⟩ := open_big a q cm mS mN ha0 ha hq hcm0 hD hS2 hN2 anti
      exact ⟨n', h1, lt_of_lt_of_le h2 hb, h3.le, fun _ => h3⟩
    · push_neg at hb
      rw [char n hn hb] at hPn
      obtain ⟨n', h1, h2, h3⟩ := open_small a q n cm Δ mN ha0 ha hq hn hΔ0 hb hN0' hN2 ψN hPn
      exact ⟨n', h1, h2, (char n' h1 (by linarith)).2 h3⟩
  obtain ⟨nhat, hpos, hiff⟩ := threshold_of (fun n => mS n ≤ mN n ∧ (0 < mN n → mS n < mN n))
    _ (q / (1 - 2 * a)) hn₀0 hnot hqw (big _ hqw le_rfl) upset openL
  exact ⟨nhat, hpos, fun n hn => ⟨mS n, mN n, hS1 n hn, hN1 n hn, hiff n hn⟩⟩


theorem proposition_4_red (q thetaBar : ℝ) (hq : 0 < q) (hθ : 0 < thetaBar) : (∀ b : ℝ, 0 < b → b ≤ 1 → ∀ n : ℝ, 0 < n → ∃ c₀ : ℝ, ∀ cm : ℝ, c₀ ≤ cm → ∃ m₀ : ℝ, (∀ m : Fin 2 → ℝ, IsDisclosureEq 0 b q n thetaBar cm m ↔ m = fun _ => m₀) ∧ (∀ m : Fin 2 → ℝ, IsDisclosureEq 0 0 q n thetaBar cm m ↔ m = fun _ => m₀)) ∧ ∀ a : ℝ, 0 < a → a < 1 / 2 → ∃ c₀ : ℝ, ∀ cm : ℝ, c₀ ≤ cm → ∃ nhat : ℝ, 0 < nhat ∧ ∀ n : ℝ, 0 < n → ∃ mS mNC : ℝ, (∀ m : Fin 2 → ℝ, IsDisclosureEq a 1 q n thetaBar cm m ↔ m = fun _ => mS) ∧ (∀ m : Fin 2 → ℝ, IsDisclosureEq a 0 q n thetaBar cm m ↔ m = fun _ => mNC) ∧ ((mS ≤ mNC ∧ (0 < mNC → mS < mNC)) ↔ nhat < n) :=
  ⟨prop4_part1 q thetaBar hq hθ, prop4_part2_red q thetaBar hq hθ⟩

end CompOpacity.Disclosure

open CompOpacity.Disclosure in
theorem solution (q thetaBar : ℝ) (hq : 0 < q) (hθ : 0 < thetaBar) : (∀ b : ℝ, 0 < b → b ≤ 1 → ∀ n : ℝ, 0 < n → ∃ c₀ : ℝ, ∀ cm : ℝ, c₀ ≤ cm → ∃ m₀ : ℝ, (∀ m : Fin 2 → ℝ, IsDisclosureEq 0 b q n thetaBar cm m ↔ m = fun _ => m₀) ∧ (∀ m : Fin 2 → ℝ, IsDisclosureEq 0 0 q n thetaBar cm m ↔ m = fun _ => m₀)) ∧ ∀ a : ℝ, 0 < a → a < 1 / 2 → ∃ c₀ : ℝ, ∀ cm : ℝ, c₀ ≤ cm → ∃ nhat : ℝ, 0 < nhat ∧ ∀ n : ℝ, 0 < n → ∃ mS mNC : ℝ, (∀ m : Fin 2 → ℝ, IsDisclosureEq a 1 q n thetaBar cm m ↔ m = fun _ => mS) ∧ (∀ m : Fin 2 → ℝ, IsDisclosureEq a 0 q n thetaBar cm m ↔ m = fun _ => mNC) ∧ ((mS ≤ mNC ∧ (0 < mNC → mS < mNC)) ↔ nhat < n) :=
  proposition_4_red q thetaBar hq hθ
