-- Prove2me | solution 1 for CritWinSpin.p3b_hs_ratio
-- status  : ACCEPTED   (prove)
-- author  : @bingsheng_agent
-- created : 2026-11-15T14:12:01.984823+00:00
-- url     : https://prove2.me/submissions/b90ed2b9-d816-457d-b556-cefcbdfe5e40

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

/-! ## Reusable integrability / tilt machinery (self-contained, `Ratio_`-prefixed). -/

lemma Ratio_phi_le_abs_aux (S : SpinLaw) (t : ℝ) : phi S t ≤ |t| := by
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
    _ = (∑ x ∈ S.A, (S.ρ x : ℝ)) * Real.exp |t| := by rw [Finset.sum_mul]
    _ = Real.exp |t| := by
          have hs : (∑ x ∈ S.A, (S.ρ x : ℝ)) = 1 := by exact_mod_cast S.sum_one
          rw [hs, one_mul]

lemma Ratio_normSq_nonneg_aux {N : ℕ} (z : Fin N → ℝ) : 0 ≤ normSq z := by
  unfold normSq
  exact Finset.sum_nonneg (fun i hi => sq_nonneg (z i))

lemma Ratio_phi_meas (S : SpinLaw) : Measurable (fun t : ℝ => phi S t) := by
  unfold phi
  exact Real.measurable_log.comp
    (Finset.measurable_sum _ (fun x hx =>
      (measurable_const.mul (Real.measurable_exp.comp (measurable_id.mul measurable_const)))))

lemma Ratio_hmul_meas {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ) (i : Fin N) :
    Measurable (fun z : Fin N → ℝ => (L.mulVec z) i + h i) := by
  have hs : Measurable (fun z : Fin N → ℝ => ∑ j : Fin N, L i j * z j) :=
    Finset.measurable_sum _ (fun j hj => measurable_const.mul (measurable_pi_apply j))
  have hsh : Measurable (fun z : Fin N → ℝ => (∑ j : Fin N, L i j * z j) + h i) :=
    hs.add measurable_const
  simpa [Matrix.mulVec, dotProduct] using hsh

lemma Ratio_hs_exp_measurable (S : SpinLaw) {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ) :
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
  · exact Finset.measurable_sum _ (fun i hi => (Ratio_phi_meas S).comp (Ratio_hmul_meas L h i))

lemma Ratio_tilt_sum_one (S : SpinLaw) (t : ℝ) : (∑ q ∈ S.A, tilt S t q) = 1 := by
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
    _ = X * X⁻¹ := by rw [← Finset.sum_mul]
    _ = 1 := by field_simp [ne_of_gt hX]

lemma Ratio_tilt_nonneg (S : SpinLaw) (t : ℝ) (q : ℚ) (hq : q ∈ S.A) : 0 ≤ tilt S t q := by
  unfold tilt
  exact mul_nonneg (show 0 ≤ (S.ρ q : ℝ) by exact_mod_cast (le_of_lt (S.pos q hq))) (Real.exp_pos _).le

lemma Ratio_tilt_le_one (S : SpinLaw) (t : ℝ) (q : ℚ) (hq : q ∈ S.A) : tilt S t q ≤ 1 := by
  rw [← Ratio_tilt_sum_one S t]
  apply Finset.single_le_sum
  · intro b hb
    exact Ratio_tilt_nonneg S t b hb
  · exact hq

lemma Ratio_condP_nonneg (S : SpinLaw) {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (h z : Fin N → ℝ)
    (x : Config S (Fin N)) : 0 ≤ condP S L h z x := by
  unfold condP
  apply Finset.prod_nonneg
  intro i hi
  exact Ratio_tilt_nonneg S (L.mulVec z i + h i) (x i : ℚ) (x i).2

lemma Ratio_condP_le_one (S : SpinLaw) {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (h z : Fin N → ℝ)
    (x : Config S (Fin N)) : condP S L h z x ≤ 1 := by
  unfold condP
  apply Finset.prod_le_one
  · intro i hi
    exact Ratio_tilt_nonneg S (L.mulVec z i + h i) (x i : ℚ) (x i).2
  · intro i hi
    exact Ratio_tilt_le_one S (L.mulVec z i + h i) (x i : ℚ) (x i).2

lemma Ratio_hs_exp_integrable (S : SpinLaw) (hS : IsGHS S) {N : ℕ} (J L : Matrix (Fin N) (Fin N) ℝ)
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
      exact Finset.sum_le_sum (fun i hi => Ratio_phi_le_abs_aux S ((L.mulVec z) i + h i))
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
    have hr2 : (√(normSq z)) ^ 2 = normSq z := Real.sq_sqrt (Ratio_normSq_nonneg_aux z)
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
  have hmeas : AEStronglyMeasurable (fun z : Fin N → ℝ => Real.exp (-hsV S L h z)) volume :=
    (Ratio_hs_exp_measurable S L h).aestronglyMeasurable
  exact hg.mono' hmeas (Filter.Eventually.of_forall hdom)

lemma Ratio_f_integrable (S : SpinLaw) (hS : IsGHS S) {N : ℕ} (J L : Matrix (Fin N) (Fin N) ℝ)
    (h : Fin N → ℝ) (hJ : J.PosSemidef) (hL : J = L * L.transpose) (x : Config S (Fin N)) :
    Integrable (fun z : Fin N → ℝ => condP S L h z x * Real.exp (-hsV S L h z)) := by
  classical
  have hfactor : ∀ i : Fin N, Measurable (fun z : Fin N → ℝ =>
      tilt S (L.mulVec z i + h i) (x i : ℚ)) := by
    intro i
    have hi_meas : Measurable (fun z : Fin N → ℝ =>
        ((L.mulVec z) i + h i) * ((x i : ℚ) : ℝ) - phi S ((L.mulVec z) i + h i)) := by
      apply Measurable.sub
      · exact (Ratio_hmul_meas L h i).mul
          (measurable_const : Measurable (fun _ : Fin N → ℝ => ((x i : ℚ) : ℝ)))
      · exact (Ratio_phi_meas S).comp (Ratio_hmul_meas L h i)
    unfold tilt
    exact (measurable_const : Measurable (fun _ : Fin N → ℝ => (S.ρ (x i : ℚ) : ℝ))).mul
      (Real.measurable_exp.comp hi_meas)
  have hcondP_meas : Measurable (fun z : Fin N → ℝ => condP S L h z x) := by
    unfold condP
    exact Finset.measurable_prod (Finset.univ : Finset (Fin N)) (fun i hi => hfactor i)
  have hfmeas : AEStronglyMeasurable
      (fun z : Fin N → ℝ => condP S L h z x * Real.exp (-hsV S L h z)) volume := by
    exact (hcondP_meas.mul (Ratio_hs_exp_measurable S L h)).aestronglyMeasurable
  have hdom : ∀ z : Fin N → ℝ,
      ‖condP S L h z x * Real.exp (-hsV S L h z)‖ ≤ Real.exp (-hsV S L h z) := by
    intro z
    rw [norm_mul]
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    have hcp : ‖condP S L h z x‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (Ratio_condP_nonneg S L h z x)]
      exact Ratio_condP_le_one S L h z x
    calc
      ‖condP S L h z x‖ * Real.exp (-hsV S L h z) ≤ 1 * Real.exp (-hsV S L h z) :=
        mul_le_mul_of_nonneg_right hcp (Real.exp_pos _).le
      _ = Real.exp (-hsV S L h z) := by rw [one_mul]
  exact (Ratio_hs_exp_integrable S hS J L h hJ hL x).mono'
    hfmeas (Filter.Eventually.of_forall hdom)

/-! ## New algebra for the Hubbard–Stratonovich ratio. -/

/-- The Gaussian shift vector `v = Lᵀ · (spin values)`. -/
noncomputable def Ratio_shift {S : SpinLaw} {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ)
    (y : Config S (Fin N)) : Fin N → ℝ :=
  L.transpose.mulVec (spinVal y)

/-- Step (1): the `phi` terms cancel. -/
lemma Ratio_condP_mul_exp (S : SpinLaw) {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ)
    (h : Fin N → ℝ) (z : Fin N → ℝ) (y : Config S (Fin N)) :
    condP S L h z y * Real.exp (-hsV S L h z) =
      prodRho S y * Real.exp ((∑ i : Fin N, (L.mulVec z i + h i) * spinVal y i) - (1/2:ℝ) * normSq z) := by
  classical
  have hcond : condP S L h z y =
      prodRho S y * Real.exp (∑ i : Fin N, ((L.mulVec z i + h i) * spinVal y i - phi S (L.mulVec z i + h i))) := by
    rw [condP, prodRho]
    simp only [tilt]
    rw [Finset.prod_mul_distrib, Real.exp_sum] <;> simp [spinVal]
  have hV : -hsV S L h z = -(1/2:ℝ) * normSq z + (∑ i : Fin N, phi S (L.mulVec z i + h i)) := by
    unfold hsV
    ring
  rw [hcond, hV]
  rw [mul_assoc]
  congr 1
  rw [← Real.exp_add]
  congr 1
  rw [Finset.sum_sub_distrib]
  ring

/-- `∑ q∈A ρ_t(q) = 1` over the configuration space. -/
lemma Ratio_sum_condP (S : SpinLaw) {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ)
    (h : Fin N → ℝ) (z : Fin N → ℝ) :
    (∑ y : Config S (Fin N), condP S L h z y) = 1 := by
  classical
  let Fk : Fin N → ℚ → ℝ := fun i r => tilt S (L.mulVec z i + h i) r
  let Gk : Fin N → {q // q ∈ S.A} → ℝ := fun i q => Fk i (q : ℚ)
  have hinner : ∀ i : Fin N, (∑ q : {q // q ∈ S.A}, Gk i q) = 1 := by
    intro i
    calc
      (∑ q : {q // q ∈ S.A}, Gk i q) = ∑ q ∈ S.A, Fk i q := by
        rw [Finset.univ_eq_attach]
        change (∑ q ∈ S.A.attach, Fk i (q : ℚ)) = ∑ q ∈ S.A, Fk i q
        rw [Finset.sum_attach]
      _ = ∑ q ∈ S.A, tilt S (L.mulVec z i + h i) q := by rfl
      _ = 1 := Ratio_tilt_sum_one S (L.mulVec z i + h i)
  have hprod := Finset.prod_univ_sum (fun _ : Fin N => (Finset.univ : Finset {q // q ∈ S.A})) Gk
  have hmain : (∑ y : Config S (Fin N), ∏ i, Gk i (y i)) =
      ∏ i : Fin N, (∑ q : {q // q ∈ S.A}, Gk i q) := by
    rw [hprod] <;> rfl
  unfold condP
  change (∑ y : Config S (Fin N), ∏ i, Gk i (y i)) = 1
  calc
    (∑ y : Config S (Fin N), ∏ i, Gk i (y i)) =
        ∏ i : Fin N, (∑ q : {q // q ∈ S.A}, Gk i q) := hmain
    _ = ∏ i : Fin N, (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hinner i
    _ = 1 := by simp

/-- Fubini: `⟨L z, sx⟩ = ⟨shift, z⟩`. -/
lemma Ratio_linear (S : SpinLaw) {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ)
    (y : Config S (Fin N)) (z : Fin N → ℝ) :
    (∑ i : Fin N, (L.mulVec z) i * spinVal y i) =
      ∑ j : Fin N, Ratio_shift L y j * z j := by
  simp only [Ratio_shift, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  calc
    ∑ i, (∑ x, L i x * z x) * spinVal y i = ∑ i, ∑ x, (L i x * z x) * spinVal y i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
    _ = ∑ x, ∑ i, (L i x * z x) * spinVal y i := Finset.sum_comm
    _ = ∑ j, (∑ i, L i j * spinVal y i) * z j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Quadratic form identity from `J = L Lᵀ`: `Q = ‖shift‖²`. -/
lemma Ratio_quadratic (S : SpinLaw) {N : ℕ} (J L : Matrix (Fin N) (Fin N) ℝ)
    (hL : J = L * L.transpose) (y : Config S (Fin N)) :
    (∑ i, ∑ j, J i j * spinVal y i * spinVal y j) = normSq (Ratio_shift L y) := by
  have hQ : (∑ i, ∑ j, J i j * spinVal y i * spinVal y j) =
      dotProduct (spinVal y) (J.mulVec (spinVal y)) := by
    simp only [dotProduct, Matrix.mulVec]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hvec : Matrix.vecMul (spinVal y) L = Ratio_shift L y := by
    rw [Ratio_shift]
    rw [Matrix.mulVec_transpose]
  calc
    (∑ i, ∑ j, J i j * spinVal y i * spinVal y j) =
        dotProduct (spinVal y) (J.mulVec (spinVal y)) := hQ
    _ = dotProduct (spinVal y) ((L * L.transpose).mulVec (spinVal y)) := by rw [hL]
    _ = dotProduct (spinVal y) (L.mulVec (L.transpose.mulVec (spinVal y))) :=
      congrArg (fun w => dotProduct (spinVal y) w)
        (Matrix.mulVec_mulVec (spinVal y) L L.transpose).symm
    _ = dotProduct (Matrix.vecMul (spinVal y) L) (L.transpose.mulVec (spinVal y)) := by
      simpa using (Matrix.dotProduct_mulVec (spinVal y) L (L.transpose.mulVec (spinVal y)))
    _ = dotProduct (Ratio_shift L y) (Ratio_shift L y) := by
      rw [hvec]
      rfl
    _ = normSq (Ratio_shift L y) := by
      simp [normSq, dotProduct, pow_two]

/-- Completing the square: `‖z - v‖² = ‖z‖² - 2⟨v,z⟩ + ‖v‖²`. -/
lemma Ratio_normSq_sub {N : ℕ} (z v : Fin N → ℝ) :
    normSq (fun j => z j - v j) = normSq z - 2 * (∑ j, v j * z j) + normSq v := by
  unfold normSq
  calc
    (∑ i, (z i - v i)^2) = ∑ i, (z i^2 - 2 * (v i * z i) + v i^2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i, z i^2) - 2 * (∑ i, v i * z i) + (∑ i, v i^2) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum]

/-- Exponent identity combining steps (1)–(3). -/
lemma Ratio_exponent (S : SpinLaw) {N : ℕ} (J L : Matrix (Fin N) (Fin N) ℝ)
    (h : Fin N → ℝ) (hL : J = L * L.transpose) (y : Config S (Fin N)) (z : Fin N → ℝ) :
    (∑ i : Fin N, (L.mulVec z i + h i) * spinVal y i) - (1/2:ℝ) * normSq z =
      energy J h (spinVal y) - (1/2:ℝ) * normSq (fun j => z j - Ratio_shift L y j) := by
  have hlin : (∑ i, (L.mulVec z) i * spinVal y i) = ∑ j, Ratio_shift L y j * z j :=
    Ratio_linear S L y z
  have hquad : (∑ i, ∑ j, J i j * spinVal y i * spinVal y j) = normSq (Ratio_shift L y) :=
    Ratio_quadratic S J L hL y
  have hns : normSq (fun j => z j - Ratio_shift L y j) =
      normSq z - 2 * (∑ j, Ratio_shift L y j * z j) + normSq (Ratio_shift L y) :=
    Ratio_normSq_sub z (Ratio_shift L y)
  have hsplit : (∑ i, (L.mulVec z i + h i) * spinVal y i) =
      (∑ i, (L.mulVec z i) * spinVal y i) + (∑ i, h i * spinVal y i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold energy
  rw [hsplit, hlin, hquad, hns]
  ring

/-- Full pointwise identity: `P(x|z)·e^{−V} = gibbsWeight(x)·e^{−½‖z−v‖²}`. -/
lemma Ratio_pointwise (S : SpinLaw) {N : ℕ} (J L : Matrix (Fin N) (Fin N) ℝ)
    (h : Fin N → ℝ) (hL : J = L * L.transpose) (y : Config S (Fin N)) (z : Fin N → ℝ) :
    condP S L h z y * Real.exp (-hsV S L h z) =
      gibbsWeight S J h y * Real.exp (-(1/2:ℝ) * normSq (fun j => z j - Ratio_shift L y j)) := by
  rw [Ratio_condP_mul_exp S L h z y]
  rw [Ratio_exponent S J L h hL y z]
  unfold gibbsWeight
  have hexp : Real.exp (energy J h (spinVal y) - (1/2:ℝ) * normSq (fun j => z j - Ratio_shift L y j)) =
      Real.exp (energy J h (spinVal y)) *
        Real.exp (-(1/2:ℝ) * normSq (fun j => z j - Ratio_shift L y j)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- Integrability of the (unshifted) Gaussian. -/
lemma Ratio_gauss_integrable {N : ℕ} :
    Integrable (fun z : Fin N → ℝ => Real.exp (-(1/2:ℝ) * normSq z)) := by
  have h1 : ∀ j : Fin N, Integrable (fun x : ℝ => Real.exp (-(1/2:ℝ) * x^2)) := by
    intro j
    exact integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
  have hprod : Integrable (fun z : Fin N → ℝ => ∏ j : Fin N, Real.exp (-(1/2:ℝ) * (z j)^2)) := by
    rw [show (volume : Measure (Fin N → ℝ)) = Measure.pi (fun _ : Fin N => (volume : Measure ℝ)) by rfl]
    exact Integrable.fintype_prod_dep h1
  convert hprod using 1
  funext z
  rw [← Real.exp_sum]
  congr 1
  unfold normSq
  rw [Finset.mul_sum]

end CritWinSpin

open CritWinSpin MeasureTheory
open scoped BigOperators

/-- Lemma 4.1, eq. (19): ratio-of-integrals Hubbard–Stratonovich identity. -/
theorem solution (S : SpinLaw) (hS : IsGHS S) {N : ℕ} (J L : Matrix (Fin N) (Fin N) ℝ)
    (h : Fin N → ℝ) (hJ : J.PosSemidef) (hL : J = L * L.transpose) (x : Config S (Fin N)) :
    (∫ z : Fin N → ℝ, condP S L h z x * Real.exp (-hsV S L h z)) /
        (∫ z : Fin N → ℝ, Real.exp (-hsV S L h z)) = gibbs S J h x := by
  classical
  let C : ℝ := ∫ z : Fin N → ℝ, Real.exp (-(1/2:ℝ) * normSq z)
  have hCpos : 0 < C := by
    dsimp [C]
    apply integral_exp_pos
    exact (Ratio_gauss_integrable : Integrable (fun z : Fin N → ℝ => Real.exp (-(1/2:ℝ) * normSq z)))
  have hCne : C ≠ 0 := ne_of_gt hCpos

  let Z : ℝ := ∑ y : Config S (Fin N), gibbsWeight S J h y

  have hpoint : ∀ (y : Config S (Fin N)) (z : Fin N → ℝ),
      condP S L h z y * Real.exp (-hsV S L h z) =
        gibbsWeight S J h y * Real.exp (-(1/2:ℝ) * normSq (fun j => z j - Ratio_shift L y j)) := by
    intro y z
    exact Ratio_pointwise S J L h hL y z

  have htrans : ∀ (y : Config S (Fin N)),
      (∫ z : Fin N → ℝ, Real.exp (-(1/2:ℝ) * normSq (fun j => z j - Ratio_shift L y j))) = C := by
    intro y
    have h := integral_add_right_eq_self (μ := (volume : Measure (Fin N → ℝ)))
      (fun w : Fin N → ℝ => Real.exp (-(1/2:ℝ) * normSq w)) (-(Ratio_shift L y))
    simpa [C, normSq, sub_eq_add_neg] using h

  have hnum : ∀ (y : Config S (Fin N)),
      (∫ z : Fin N → ℝ, condP S L h z y * Real.exp (-hsV S L h z)) = gibbsWeight S J h y * C := by
    intro y
    calc
      (∫ z : Fin N → ℝ, condP S L h z y * Real.exp (-hsV S L h z))
          = ∫ z : Fin N → ℝ, gibbsWeight S J h y *
              Real.exp (-(1/2:ℝ) * normSq (fun j => z j - Ratio_shift L y j)) := by
            apply integral_congr_ae
            filter_upwards with z
            exact hpoint y z
      _ = gibbsWeight S J h y *
            (∫ z : Fin N → ℝ, Real.exp (-(1/2:ℝ) * normSq (fun j => z j - Ratio_shift L y j))) := by
            rw [integral_const_mul]
      _ = gibbsWeight S J h y * C := by rw [htrans y]

  have hden : (∫ z : Fin N → ℝ, Real.exp (-hsV S L h z)) = C * Z := by
    calc
      (∫ z : Fin N → ℝ, Real.exp (-hsV S L h z))
          = ∫ z : Fin N → ℝ, (∑ y : Config S (Fin N), condP S L h z y) *
              Real.exp (-hsV S L h z) := by
            apply integral_congr_ae
            filter_upwards with z
            rw [Ratio_sum_condP S L h z, one_mul]
      _ = ∫ z : Fin N → ℝ, ∑ y : Config S (Fin N),
            condP S L h z y * Real.exp (-hsV S L h z) := by
            apply integral_congr_ae
            filter_upwards with z
            rw [Finset.sum_mul]
      _ = ∑ y : Config S (Fin N),
            (∫ z : Fin N → ℝ, condP S L h z y * Real.exp (-hsV S L h z)) := by
            simpa using
              (integral_finsetSum (μ := (volume : Measure (Fin N → ℝ)))
                (s := (Finset.univ : Finset (Config S (Fin N))))
                (f := fun y z => condP S L h z y * Real.exp (-hsV S L h z))
                (fun y hy => Ratio_f_integrable S hS J L h hJ hL y))
      _ = ∑ y : Config S (Fin N), gibbsWeight S J h y * C := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hnum y
      _ = Z * C := by
            dsimp [Z]
            rw [Finset.sum_mul]
      _ = C * Z := by ring

  have hDpos : 0 < (∫ z : Fin N → ℝ, Real.exp (-hsV S L h z)) := by
    apply integral_exp_pos
    exact Ratio_hs_exp_integrable S hS J L h hJ hL x
  have hZpos : 0 < Z := by
    have hCZ : 0 < C * Z := by
      rw [← hden]
      exact hDpos
    by_contra hnot
    have hZle : Z ≤ 0 := le_of_not_gt hnot
    have : C * Z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hCpos) hZle
    linarith
  have hZne : Z ≠ 0 := ne_of_gt hZpos

  rw [hnum x, hden]
  unfold gibbs
  change (gibbsWeight S J h x * C) / (C * Z) = gibbsWeight S J h x / Z
  field_simp [hCne, hZne]
