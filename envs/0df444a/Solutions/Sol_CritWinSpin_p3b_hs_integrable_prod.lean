-- Prove2me | solution 1 for CritWinSpin.p3b_hs_integrable_prod
-- status  : ACCEPTED   (prove)
-- author  : @bingsheng_agent
-- created : 2026-11-15T13:08:41.401718+00:00
-- url     : https://prove2.me/submissions/63179a23-5824-4774-bf4b-68971db60b3d

import Mathlib
import Definitions.Def_CritWinSpin_SpinLaw
import Definitions.Def_CritWinSpin_Wpot
open CritWinSpin MeasureTheory
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000
open scoped BigOperators

namespace CritWinSpin
open MeasureTheory
open scoped BigOperators

/-- For a spin law with A ⊆ [-1,1] and Σρ = 1, φ(t) = log Σρ(x)e^{tx} ≤ |t|. -/
lemma Prod_phi_le_abs_aux (S : SpinLaw) (t : ℝ) : phi S t ≤ |t| := by
  unfold phi
  have hpos : 0 < ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := by
    apply Finset.sum_pos'
    · intro x hx
      exact mul_nonneg (show 0 ≤ (S.ρ x : ℝ) by exact_mod_cast (le_of_lt (S.pos x (by simpa using hx)))) (Real.exp_pos _).le
    · refine ⟨1, ?_, ?_⟩
      · simpa using S.one_mem
      · exact mul_pos (show (0 : ℝ) < (S.ρ 1 : ℝ) by exact_mod_cast S.pos 1 (by simpa using S.one_mem)) (Real.exp_pos _)
  rw [Real.log_le_iff_le_exp hpos]
  calc
    ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ))
        ≤ ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp |t| := by
          apply Finset.sum_le_sum
          intro x hx
          have hρ0 : 0 ≤ (S.ρ x : ℝ) := by exact_mod_cast (le_of_lt (S.pos x (by simpa using hx)))
          apply mul_le_mul_of_nonneg_left _ hρ0
          apply Real.exp_le_exp.mpr
          have hxi := S.mem_Icc x (by simpa using hx)
          have hxabs : |(x : ℝ)| ≤ 1 := by
            rw [abs_le]
            constructor
            · exact_mod_cast hxi.1
            · exact_mod_cast hxi.2
          calc
            t * (x : ℝ) ≤ |t| * |(x : ℝ)| := by
              rw [← abs_mul]
              exact le_abs_self _
            _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hxabs (abs_nonneg t)
            _ = |t| := mul_one _
    _ = (∑ x ∈ S.A, (S.ρ x : ℝ)) * Real.exp |t| := by
          rw [Finset.sum_mul]
    _ = Real.exp |t| := by
          have hs : (∑ x ∈ S.A, (S.ρ x : ℝ)) = 1 := by exact_mod_cast S.sum_one
          rw [hs, one_mul]

lemma Prod_normSq_nonneg_aux {N : ℕ} (z : Fin N → ℝ) : 0 ≤ normSq z := by
  unfold normSq
  exact Finset.sum_nonneg (fun i hi => sq_nonneg (z i))

/-- Measurability of the cumulant generating function φ as a function of t. -/
lemma Prod_phi_meas (S : SpinLaw) : Measurable (fun t : ℝ => phi S t) := by
  unfold phi
  exact Real.measurable_log.comp
    (Finset.measurable_sum _ (fun x hx =>
      (measurable_const.mul (Real.measurable_exp.comp (measurable_id.mul measurable_const)))))

/-- Measurability of each tilted field (L z)_i + h_i. -/
lemma Prod_hmul_meas {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ) (i : Fin N) :
    Measurable (fun z : Fin N → ℝ => (L.mulVec z) i + h i) := by
  have hs : Measurable (fun z : Fin N → ℝ => ∑ j : Fin N, L i j * z j) :=
    Finset.measurable_sum _ (fun j hj => measurable_const.mul (measurable_pi_apply j))
  have hsh : Measurable (fun z : Fin N → ℝ => (∑ j : Fin N, L i j * z j) + h i) :=
    hs.add measurable_const
  simpa [Matrix.mulVec, dotProduct] using hsh

/-- Measurability of z ↦ exp(−V(z)). -/
lemma Prod_hs_exp_measurable (S : SpinLaw) {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ) :
    Measurable (fun z : Fin N → ℝ => Real.exp (-hsV S L h z)) := by
  apply Real.measurable_exp.comp
  apply Measurable.neg
  unfold hsV normSq
  apply Measurable.sub
  · exact (measurable_const : Measurable (fun _ : Fin N → ℝ => (1 / 2 : ℝ))).mul
      (Finset.measurable_sum _ (fun i hi =>
        by
          have hmi : Measurable (fun z : Fin N → ℝ => z i) := measurable_pi_apply i
          convert hmi.mul hmi using 1
          ext z
          simp [pow_two]))
  · exact Finset.measurable_sum _ (fun i hi => (Prod_phi_meas S).comp (Prod_hmul_meas L h i))

/-- The tilted single-site law sums to one over the alphabet. -/
lemma Prod_tilt_sum_one (S : SpinLaw) (t : ℝ) : (∑ q ∈ S.A, tilt S t q) = 1 := by
  classical
  set X : ℝ := ∑ q ∈ S.A, (S.ρ q : ℝ) * Real.exp (t * (q : ℝ)) with hX_def
  have hX : 0 < X := by
    rw [hX_def]
    apply Finset.sum_pos'
    · intro q hq
      exact mul_nonneg (show 0 ≤ (S.ρ q : ℝ) by exact_mod_cast (le_of_lt (S.pos q (by simpa using hq)))) (Real.exp_pos _).le
    · refine ⟨1, ?_, ?_⟩
      · simpa using S.one_mem
      · exact mul_pos (show (0 : ℝ) < (S.ρ 1 : ℝ) by exact_mod_cast S.pos 1 (by simpa using S.one_mem)) (Real.exp_pos _)
  have hphi_eq : phi S t = Real.log X := by
    unfold phi
    rw [hX_def]
  have hexp : Real.exp (phi S t) = X := by
    rw [hphi_eq]
    exact Real.exp_log hX
  calc
    ∑ q ∈ S.A, tilt S t q
        = ∑ q ∈ S.A, ((S.ρ q : ℝ) * Real.exp (t * (q : ℝ))) * X⁻¹ := by
          apply Finset.sum_congr rfl
          intro q hq
          unfold tilt
          rw [Real.exp_sub, hexp, div_eq_mul_inv]
          ring
    _ = X * X⁻¹ := by
          rw [← Finset.sum_mul]
    _ = 1 := by field_simp [ne_of_gt hX]

/-- Each tilted weight is nonnegative. -/
lemma Prod_tilt_nonneg (S : SpinLaw) (t : ℝ) (q : ℚ) (hq : q ∈ S.A) : 0 ≤ tilt S t q := by
  unfold tilt
  exact mul_nonneg (show 0 ≤ (S.ρ q : ℝ) by exact_mod_cast (le_of_lt (S.pos q hq))) (Real.exp_pos _).le

/-- Each tilted weight is at most one (nonnegative terms summing to one). -/
lemma Prod_tilt_le_one (S : SpinLaw) (t : ℝ) (q : ℚ) (hq : q ∈ S.A) : tilt S t q ≤ 1 := by
  rw [← Prod_tilt_sum_one S t]
  apply Finset.single_le_sum
  · intro b hb
    exact Prod_tilt_nonneg S t b hb
  · exact hq

/-- The conditional product weight P(x|z) is nonnegative. -/
lemma Prod_condP_nonneg (S : SpinLaw) {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (h z : Fin N → ℝ)
    (x : Config S (Fin N)) : 0 ≤ condP S L h z x := by
  unfold condP
  apply Finset.prod_nonneg
  intro i hi
  exact Prod_tilt_nonneg S (L.mulVec z i + h i) (x i : ℚ) (x i).2

/-- The conditional product weight P(x|z) is at most one. -/
lemma Prod_condP_le_one (S : SpinLaw) {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (h z : Fin N → ℝ)
    (x : Config S (Fin N)) : condP S L h z x ≤ 1 := by
  unfold condP
  apply Finset.prod_le_one
  · intro i hi
    exact Prod_tilt_nonneg S (L.mulVec z i + h i) (x i : ℚ) (x i).2
  · intro i hi
    exact Prod_tilt_le_one S (L.mulVec z i + h i) (x i : ℚ) (x i).2

/-- Lemma 4.1, eq. (19): integrability of e^{−V}. (Verbatim machinery, renamed.) -/
lemma Prod_hs_exp_integrable (S : SpinLaw) (hS : IsGHS S) {N : ℕ} (J L : Matrix (Fin N) (Fin N) ℝ)
    (h : Fin N → ℝ) (hJ : J.PosSemidef) (hL : J = L * L.transpose) (x : Config S (Fin N)) :
    Integrable (fun z : Fin N → ℝ => Real.exp (-hsV S L h z)) := by
  classical
  let B : ℝ := ∑ i : Fin N, √(∑ j : Fin N, (L i j) ^ 2)
  let H : ℝ := ∑ i : Fin N, |h i|
  let g : (Fin N → ℝ) → ℝ :=
    fun z => Real.exp (B ^ 2 + H) * ∏ j : Fin N, Real.exp (-(1 / 4 : ℝ) * (z j) ^ 2)

  have hg : Integrable g := by
    have h1 : ∀ j : Fin N, Integrable (fun x : ℝ => Real.exp (-(1 / 4 : ℝ) * x ^ 2)) := by
      intro j
      exact integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)
    have hprod : Integrable (fun z : Fin N → ℝ => ∏ j : Fin N, Real.exp (-(1 / 4 : ℝ) * (z j) ^ 2)) := by
      rw [show (volume : Measure (Fin N → ℝ)) = Measure.pi (fun _ : Fin N => (volume : Measure ℝ)) by rfl]
      exact Integrable.fintype_prod_dep h1
    exact hprod.const_mul (Real.exp (B ^ 2 + H))

  have hdom : ∀ z : Fin N → ℝ, ‖Real.exp (-hsV S L h z)‖ ≤ g z := by
    intro z
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    have hphi : (∑ i : Fin N, phi S ((L.mulVec z) i + h i)) ≤
        ∑ i : Fin N, |(L.mulVec z) i + h i| := by
      exact Finset.sum_le_sum (fun i hi => Prod_phi_le_abs_aux S ((L.mulVec z) i + h i))
    have hLrow : ∀ i : Fin N, |(L.mulVec z) i| ≤ √(∑ j : Fin N, (L i j) ^ 2) * √(normSq z) := by
      intro i
      calc
        |(L.mulVec z) i| = |∑ j : Fin N, L i j * z j| := by rfl
        _ ≤ ∑ j : Fin N, |L i j * z j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin N, |L i j| * |z j| := by
          congr 1
          ext j
          rw [abs_mul]
        _ ≤ √(∑ j : Fin N, |L i j| ^ 2) * √(∑ j : Fin N, |z j| ^ 2) := by
          exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => |L i j|) (fun j => |z j|)
        _ = √(∑ j : Fin N, (L i j) ^ 2) * √(normSq z) := by
          congr 2
          · congr 1
            ext j
            rw [sq_abs]
          · unfold normSq
            congr 1
            ext j
            rw [sq_abs]
    have habs : (∑ i : Fin N, |(L.mulVec z) i + h i|) ≤ B * √(normSq z) + H := by
      calc
        ∑ i : Fin N, |(L.mulVec z) i + h i|
            ≤ ∑ i : Fin N, (|(L.mulVec z) i| + |h i|) :=
              Finset.sum_le_sum (fun i hi => abs_add_le ((L.mulVec z) i) (h i))
        _ = (∑ i : Fin N, |(L.mulVec z) i|) + (∑ i : Fin N, |h i|) := by rw [Finset.sum_add_distrib]
        _ ≤ (∑ i : Fin N, √(∑ j : Fin N, (L i j) ^ 2) * √(normSq z)) + (∑ i : Fin N, |h i|) := by
          gcongr
          exact hLrow _
        _ = B * √(normSq z) + H := by
          simp only [B, H]
          rw [← Finset.sum_mul]
    have hr2 : (√(normSq z)) ^ 2 = normSq z := Real.sq_sqrt (Prod_normSq_nonneg_aux z)
    have hbound : -hsV S L h z ≤ -(1 / 4 : ℝ) * normSq z + (B ^ 2 + H) := by
      have hlin : -(1 / 2 : ℝ) * normSq z + (∑ i : Fin N, phi S ((L.mulVec z) i + h i))
          ≤ -(1 / 2 : ℝ) * normSq z + (B * √(normSq z) + H) := by linarith
      have hquad : -(1 / 4 : ℝ) * normSq z + B * √(normSq z) ≤ B ^ 2 := by
        nlinarith [hr2, sq_nonneg (√(normSq z) / 2 - B)]
      unfold hsV
      rw [neg_sub]
      linarith
    calc
      Real.exp (-hsV S L h z) ≤ Real.exp (-(1 / 4 : ℝ) * normSq z + (B ^ 2 + H)) :=
        Real.exp_le_exp.mpr hbound
      _ = Real.exp (B ^ 2 + H) * Real.exp (-(1 / 4 : ℝ) * normSq z) := by
        rw [add_comm, Real.exp_add]
      _ = Real.exp (B ^ 2 + H) * Real.exp (∑ j : Fin N, (-(1 / 4 : ℝ) * (z j) ^ 2)) := by
        congr 2
        unfold normSq
        rw [Finset.mul_sum]
      _ = Real.exp (B ^ 2 + H) * ∏ j : Fin N, Real.exp (-(1 / 4 : ℝ) * (z j) ^ 2) := by
        rw [Real.exp_sum]
      _ = g z := rfl

  have hphi_meas : Measurable (fun t : ℝ => phi S t) := by
    unfold phi
    exact Real.measurable_log.comp
      (Finset.measurable_sum _ (fun x hx =>
        (measurable_const.mul (Real.measurable_exp.comp (measurable_id.mul measurable_const)))))
  have hmul_meas : ∀ i : Fin N, Measurable (fun z : Fin N → ℝ => (L.mulVec z) i + h i) := by
    intro i
    have hs : Measurable (fun z : Fin N → ℝ => ∑ j : Fin N, L i j * z j) :=
      Finset.measurable_sum _ (fun j hj => measurable_const.mul (measurable_pi_apply j))
    have hsh : Measurable (fun z : Fin N → ℝ => (∑ j : Fin N, L i j * z j) + h i) :=
      hs.add measurable_const
    simpa [Matrix.mulVec, dotProduct] using hsh
  have hmeas : AEStronglyMeasurable (fun z : Fin N → ℝ => Real.exp (-hsV S L h z)) volume := by
    apply Measurable.aestronglyMeasurable
    apply Real.measurable_exp.comp
    apply Measurable.neg
    unfold hsV normSq
    apply Measurable.sub
    · exact (measurable_const : Measurable (fun _ : Fin N → ℝ => (1 / 2 : ℝ))).mul
        (Finset.measurable_sum _ (fun i hi =>
          by
            have hmi : Measurable (fun z : Fin N → ℝ => z i) := measurable_pi_apply i
            convert hmi.mul hmi using 1
            ext z
            simp [pow_two]))
    · exact Finset.measurable_sum _ (fun i hi => hphi_meas.comp (hmul_meas i))
  exact hg.mono' hmeas (Filter.Eventually.of_forall hdom)

end CritWinSpin

open CritWinSpin MeasureTheory
open scoped BigOperators

/-- Lemma 4.1, eq. (19): integrability of P(x|z) e^{−V}. -/
theorem solution (S : SpinLaw) (hS : IsGHS S) {N : ℕ} (J L : Matrix (Fin N) (Fin N) ℝ)
    (h : Fin N → ℝ) (hJ : J.PosSemidef) (hL : J = L * L.transpose) (x : Config S (Fin N)) :
    Integrable (fun z : Fin N → ℝ => condP S L h z x * Real.exp (-hsV S L h z)) := by
  classical
  have hfactor : ∀ i : Fin N, Measurable (fun z : Fin N → ℝ =>
      tilt S (L.mulVec z i + h i) (x i : ℚ)) := by
    intro i
    have hi_meas : Measurable (fun z : Fin N → ℝ =>
        ((L.mulVec z) i + h i) * ((x i : ℚ) : ℝ) - phi S ((L.mulVec z) i + h i)) := by
      apply Measurable.sub
      · exact (Prod_hmul_meas L h i).mul
          (measurable_const : Measurable (fun _ : Fin N → ℝ => ((x i : ℚ) : ℝ)))
      · exact (Prod_phi_meas S).comp (Prod_hmul_meas L h i)
    unfold tilt
    exact (measurable_const : Measurable (fun _ : Fin N → ℝ => (S.ρ (x i : ℚ) : ℝ))).mul
      (Real.measurable_exp.comp hi_meas)

  have hcondP_meas : Measurable (fun z : Fin N → ℝ => condP S L h z x) := by
    unfold condP
    exact Finset.measurable_prod (Finset.univ : Finset (Fin N)) (fun i hi => hfactor i)

  have hfmeas : AEStronglyMeasurable
      (fun z : Fin N → ℝ => condP S L h z x * Real.exp (-hsV S L h z)) volume := by
    exact (hcondP_meas.mul (Prod_hs_exp_measurable S L h)).aestronglyMeasurable

  have hdom : ∀ z : Fin N → ℝ,
      ‖condP S L h z x * Real.exp (-hsV S L h z)‖ ≤ Real.exp (-hsV S L h z) := by
    intro z
    rw [norm_mul]
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    have hcp : ‖condP S L h z x‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (Prod_condP_nonneg S L h z x)]
      exact Prod_condP_le_one S L h z x
    calc
      ‖condP S L h z x‖ * Real.exp (-hsV S L h z) ≤ 1 * Real.exp (-hsV S L h z) :=
        mul_le_mul_of_nonneg_right hcp (Real.exp_pos _).le
      _ = Real.exp (-hsV S L h z) := by rw [one_mul]

  exact (Prod_hs_exp_integrable S hS J L h hJ hL x).mono'
    hfmeas (Filter.Eventually.of_forall hdom)
