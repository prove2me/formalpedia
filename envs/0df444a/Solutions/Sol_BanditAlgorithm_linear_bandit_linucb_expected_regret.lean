-- Prove2me | solution 1 for BanditAlgorithm.linear_bandit_linucb_expected_regret
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:36:24.030662+00:00
-- url     : https://prove2.me/submissions/42b6f318-6a91-49f9-a2ea-c173cbc35818

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_StochasticLinearBandit
import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_banditRegret
set_option autoImplicit false



set_option autoImplicit false

section Exp3ConcentrationC5

-- The pinned older Mathlib predates the corresponding logarithm bound.
lemma Exp3ConcentrationC5.log_lower {x : ℝ} (hx : 0 ≤ x) :
    2 * x / (x + 2) ≤ Real.log (1 + x) := by
  let f : ℝ → ℝ := fun y => Real.log (1 + y) - 2 * y / (y + 2)
  have hd : ∀ y : ℝ, 0 ≤ y →
      HasDerivAt f (y ^ 2 / ((1 + y) * (y + 2) ^ 2)) y := by
    intro y hy
    have h1 : 1 + y ≠ 0 := ne_of_gt (by positivity)
    have h2 : y + 2 ≠ 0 := ne_of_gt (by positivity)
    have hlog := ((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).log h1
    have hfrac := ((hasDerivAt_id y).const_mul 2).div
      ((hasDerivAt_id y).add_const 2) h2
    convert hlog.sub hfrac using 1
    · rfl
    · rfl
    · funext z
      simp only [f, Pi.sub_apply, Pi.div_apply, Pi.add_apply, id_eq]
    · simp only [Pi.add_apply, id_eq]
      field_simp
      ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (f' := fun y => y ^ 2 / ((1 + y) * (y + 2) ^ 2))
    · intro y hy
      exact (hd y (Set.mem_Ici.mp (interior_subset hy))).hasDerivWithinAt
    · intro y hy
      have hy0 : 0 ≤ y := Set.mem_Ici.mp (interior_subset hy)
      positivity
  have h := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hx hx
  dsimp [f] at h
  norm_num at h
  linarith

end Exp3ConcentrationC5






















set_option autoImplicit false











set_option autoImplicit false

-- Accepted Harry_Xu source, submission 166b3e3d-2ca5-4b2a-ade4-cdfad74ab4e7.








open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder ENNReal

section BanditAlgorithm
open BanditAlgorithm

private lemma BanditAlgorithm.dot_mulVec_comm_of_isHermitian
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.IsHermitian) (x y : Fin d → ℝ) :
    x ⬝ᵥ K *ᵥ y = y ⬝ᵥ K *ᵥ x := by
  simp only [dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hsym : K j i = K i j := by
    have heq := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i j) hK.eq
    simpa using heq
  rw [hsym]
  ring

private lemma BanditAlgorithm.quadratic_completion
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (S x : Fin d → ℝ) :
    x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x) =
      1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S) -
        1 / 2 * ((x - K⁻¹ *ᵥ S) ⬝ᵥ K *ᵥ (x - K⁻¹ *ᵥ S)) := by
  have hunit : IsUnit K := hK.isUnit
  have hdetunit : IsUnit K.det :=
    (Matrix.isUnit_iff_isUnit_det K).mp hunit
  have hKS : K *ᵥ (K⁻¹ *ᵥ S) = S := by
    rw [mulVec_mulVec, mul_nonsing_inv K hdetunit]
    exact one_mulVec S
  have hcomm (u v : Fin d → ℝ) :
      u ⬝ᵥ K *ᵥ v = v ⬝ᵥ K *ᵥ u :=
    dot_mulVec_comm_of_isHermitian hK.isHermitian u v
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [hKS, hcomm (K⁻¹ *ᵥ S) x, hKS,
    dotProduct_comm (K⁻¹ *ᵥ S) S]
  ring

private lemma BanditAlgorithm.sqrt_mulVec_sq
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (x : Fin d → ℝ) :
    x ⬝ᵥ K *ᵥ x =
      (CFC.sqrt K *ᵥ x) ⬝ᵥ (CFC.sqrt K *ᵥ x) := by
  let B := CFC.sqrt K
  have hBps : B.PosSemidef :=
    nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg K)
  have hBB : B * B = K :=
    CFC.sqrt_mul_sqrt_self K hK.posSemidef.nonneg
  have hxvec : x ᵥ* B = B *ᵥ x := by
    have heq := vecMul_conjTranspose B x
    rw [hBps.isHermitian.eq] at heq
    simpa [B] using heq
  calc
    x ⬝ᵥ K *ᵥ x = x ⬝ᵥ (B * B) *ᵥ x := by rw [hBB]
    _ = x ⬝ᵥ B *ᵥ (B *ᵥ x) := by rw [mulVec_mulVec]
    _ = (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by rw [dotProduct_mulVec, hxvec]

private lemma BanditAlgorithm.isotropic_b_integrable {d : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Fin d → ℝ => Real.exp (-b * (x ⬝ᵥ x))) := by
  have hcoord : ∀ i : Fin d,
      Integrable (fun r : ℝ => Real.exp (-b * r ^ 2)) :=
    fun _ => integrable_exp_neg_mul_sq hb
  have hprod := Integrable.fintype_prod hcoord
  have heq : (fun x : Fin d → ℝ => Real.exp (-b * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-b * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, volume_pi]
  exact hprod

private lemma BanditAlgorithm.isotropic_b_integral (d : ℕ) (b : ℝ) :
    (∫ x : Fin d → ℝ, Real.exp (-b * (x ⬝ᵥ x))) =
      (Real.sqrt (Real.pi / b)) ^ d := by
  have heq : (fun x : Fin d → ℝ => Real.exp (-b * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-b * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, integral_fintype_prod_volume_eq_prod
    (f := fun (_ : Fin d) (r : ℝ) => Real.exp (-b * r ^ 2))]
  rw [show (∫ r : ℝ, Real.exp (-b * r ^ 2)) =
      Real.sqrt (Real.pi / b) by exact integral_gaussian b,
    Finset.prod_const]
  simp

private lemma BanditAlgorithm.isotropic_integrable (d : ℕ) :
    Integrable (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ x))) := by
  have hcoord : ∀ i : Fin d,
      Integrable (fun r : ℝ => Real.exp (-1 / 2 * r ^ 2)) :=
    fun _ => by
      simpa only [neg_div] using
        integrable_exp_neg_mul_sq (show 0 < (1 / 2 : ℝ) by norm_num)
  have hprod := Integrable.fintype_prod hcoord
  have heq : (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-1 / 2 * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, volume_pi]
  exact hprod

private lemma BanditAlgorithm.isotropic_integral (d : ℕ) :
    (∫ x : Fin d → ℝ, Real.exp (-1 / 2 * (x ⬝ᵥ x))) =
      (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d := by
  have heq : (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-1 / 2 * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, integral_fintype_prod_volume_eq_prod
    (f := fun (_ : Fin d) (r : ℝ) => Real.exp (-1 / 2 * r ^ 2))]
  have hscalar :
      (∫ r : ℝ, Real.exp (-1 / 2 * r ^ 2)) =
        Real.sqrt (Real.pi / (1 / 2 : ℝ)) := by
    simpa only [neg_div] using integral_gaussian (1 / 2 : ℝ)
  rw [hscalar, Finset.prod_const]
  simp

private lemma BanditAlgorithm.centered_quadratic_integrable
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ} (hK : K.PosDef) :
    Integrable (fun x : Fin d → ℝ =>
      Real.exp (-1 / 2 * (x ⬝ᵥ K *ᵥ x))) := by
  let B := CFC.sqrt K
  have hBdet : B.det ≠ 0 := by
    rw [hK.posSemidef.det_sqrt]
    simpa using (Real.sqrt_pos.2 hK.det_pos).ne'
  have hBmeas : Measurable (toLin' B) :=
    (LinearMap.continuous_on_pi (toLin' B)).measurable
  have hmap :
      Measure.map (toLin' B) volume =
        ENNReal.ofReal (abs B.det⁻¹) • volume :=
    Real.map_matrix_volume_pi_eq_smul_volume_pi hBdet
  have hgsmul :
      Integrable (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y)))
        (Measure.map (toLin' B) volume) := by
    rw [hmap]
    exact (isotropic_integrable d).smul_measure (by finiteness)
  have hcomp := hgsmul.comp_measurable hBmeas
  have hfun : (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y))) ∘ (toLin' B) := by
    funext x
    simp only [B, Function.comp_apply, toLin'_apply, sqrt_mulVec_sq hK]
  rw [hfun]
  exact hcomp

private lemma BanditAlgorithm.centered_quadratic_integral
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ} (hK : K.PosDef) :
    (∫ x : Fin d → ℝ, Real.exp (-1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      (ENNReal.ofReal (abs (CFC.sqrt K).det⁻¹)).toReal *
      (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d := by
  let B := CFC.sqrt K
  have hBdet : B.det ≠ 0 := by
    rw [hK.posSemidef.det_sqrt]
    simpa using (Real.sqrt_pos.2 hK.det_pos).ne'
  have hBmeas : Measurable (toLin' B) :=
    (LinearMap.continuous_on_pi (toLin' B)).measurable
  have hgsm :
      AEStronglyMeasurable
        (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y)))
        (Measure.map (toLin' B) volume) := by
    have hm : Measurable
        (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y))) := by
      simp only [dotProduct]
      fun_prop
    exact hm.aestronglyMeasurable
  have hi := integral_map hBmeas.aemeasurable hgsm
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hBdet,
    integral_smul_measure] at hi
  rw [isotropic_integral d] at hi
  simpa only [B, toLin'_apply, sqrt_mulVec_sq hK, smul_eq_mul] using hi.symm

private lemma BanditAlgorithm.shifted_quadratic_integrable
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (S : Fin d → ℝ) :
    Integrable (fun x : Fin d → ℝ =>
      Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) := by
  let c := K⁻¹ *ᵥ S
  have heq :
      (fun x : Fin d → ℝ =>
        Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      fun x =>
        Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
          Real.exp (-1 / 2 * ((x - c) ⬝ᵥ K *ᵥ (x - c))) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    convert quadratic_completion hK S x using 1 <;> simp only [c] <;> ring
  rw [heq]
  exact ((centered_quadratic_integrable hK).comp_sub_right c).const_mul _

private lemma BanditAlgorithm.shifted_quadratic_integral
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (S : Fin d → ℝ) :
    (∫ x : Fin d → ℝ,
      Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
        (ENNReal.ofReal (abs (CFC.sqrt K).det⁻¹)).toReal *
          (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d := by
  let c := K⁻¹ *ᵥ S
  have heq :
      (fun x : Fin d → ℝ =>
        Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      fun x =>
        Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
          Real.exp (-1 / 2 * ((x - c) ⬝ᵥ K *ᵥ (x - c))) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    convert quadratic_completion hK S x using 1 <;> simp only [c] <;> ring
  have htrans :
      (∫ a : Fin d → ℝ,
        Real.exp (-1 / 2 * ((a - c) ⬝ᵥ K *ᵥ (a - c)))) =
      ∫ a : Fin d → ℝ, Real.exp (-1 / 2 * (a ⬝ᵥ K *ᵥ a)) :=
    integral_sub_right_eq_self
      (fun a : Fin d → ℝ => Real.exp (-1 / 2 * (a ⬝ᵥ K *ᵥ a))) c
  rw [heq, integral_const_mul, htrans, centered_quadratic_integral hK]
  ring

private lemma BanditAlgorithm.gaussian_normalization
    {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    {K : Matrix (Fin d) (Fin d) ℝ} (hK : K.PosDef) :
    ((Real.sqrt (Real.pi / (lam / 2))) ^ d)⁻¹ *
          |(CFC.sqrt K).det|⁻¹ *
        (Real.sqrt Real.pi * Real.sqrt 2) ^ d =
      Real.exp (-1 / 2 * Real.log (K.det / lam ^ d)) := by
  let L : ℝ :=
    ((Real.sqrt (Real.pi / (lam / 2))) ^ d)⁻¹ *
          |(CFC.sqrt K).det|⁻¹ *
        (Real.sqrt Real.pi * Real.sqrt 2) ^ d
  let R : ℝ := Real.exp (-1 / 2 * Real.log (K.det / lam ^ d))
  have hdet : 0 < K.det := hK.det_pos
  have hdetB :
      (CFC.sqrt K).det = Real.sqrt K.det := by
    simpa using hK.posSemidef.det_sqrt
  have hBpos : 0 < (CFC.sqrt K).det := by
    rw [hdetB]
    exact Real.sqrt_pos.2 hdet
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  apply (sq_eq_sq₀ hL hR).mp
  have hJ2 :
      ((Real.sqrt (Real.pi / (lam / 2))) ^ d) ^ 2 =
        (Real.pi / (lam / 2)) ^ d := by
    calc
      _ = (Real.sqrt (Real.pi / (lam / 2)) ^ 2) ^ d := by
        simp only [← pow_mul]
        congr 1
        omega
      _ = _ := by
        rw [Real.sq_sqrt]
        positivity
  have hB2 : |(CFC.sqrt K).det| ^ 2 = K.det := by
    rw [abs_of_pos hBpos, hdetB, Real.sq_sqrt hdet.le]
  have hC2 :
      ((Real.sqrt Real.pi * Real.sqrt 2) ^ d) ^ 2 =
        (Real.pi * 2) ^ d := by
    calc
      _ = ((Real.sqrt Real.pi * Real.sqrt 2) ^ 2) ^ d := by
        simp only [← pow_mul]
        congr 1
        omega
      _ = _ := by
        congr 1
        rw [mul_pow, Real.sq_sqrt Real.pi_pos.le,
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hratio : 0 < K.det / lam ^ d := div_pos hdet (pow_pos hlam d)
  change L ^ 2 = R ^ 2
  have hR2 : R ^ 2 = (K.det / lam ^ d)⁻¹ := by
    dsimp [R]
    rw [← Real.exp_nat_mul]
    have hexpArg :
        (↑(2 : ℕ) : ℝ) * (-1 / 2 * Real.log (K.det / lam ^ d)) =
          -Real.log (K.det / lam ^ d) := by
      ring
    rw [hexpArg]
    rw [Real.exp_neg, Real.exp_log hratio]
  rw [hR2]
  dsimp [L]
  rw [mul_pow, mul_pow, inv_pow, inv_pow, hJ2, hB2, hC2]
  field_simp [hlam.ne', hdet.ne', Real.pi_ne_zero]
  rw [← mul_pow]
  congr 1
  field_simp [hlam.ne']

end BanditAlgorithm

theorem BanditAlgorithm.isotropic_gaussian_unregularized_quadratic_mixture
    {d : ℕ} {lam : ℝ} (hlam : 0 < lam) :
    ∃ h : Measure (Fin d → ℝ),
      IsProbabilityMeasure h ∧
      ∀ (S : Fin d → ℝ) (V : Matrix (Fin d) (Fin d) ℝ),
        V.PosSemidef →
        Integrable
            (fun x => Real.exp
              (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x))) h ∧
          (∫ x, Real.exp
              (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x)) ∂h) =
            Real.exp
              (1 / 2 *
                (S ⬝ᵥ (lam • (1 : Matrix (Fin d) (Fin d) ℝ) + V)⁻¹ *ᵥ S -
                  Real.log
                    ((lam • (1 : Matrix (Fin d) (Fin d) ℝ) + V).det / lam ^ d))) := by
  let b : ℝ := lam / 2
  let J : ℝ := (Real.sqrt (Real.pi / b)) ^ d
  let q : (Fin d → ℝ) → ℝ :=
    fun x => J⁻¹ * Real.exp (-b * (x ⬝ᵥ x))
  let ρ : (Fin d → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (q x)
  let h : Measure (Fin d → ℝ) := volume.withDensity ρ
  have hb : 0 < b := by dsimp [b]; positivity
  have hJ : 0 < J := by
    dsimp [J]
    positivity
  have hqnonneg : ∀ x, 0 ≤ q x := by
    intro x
    exact mul_nonneg (inv_nonneg.mpr hJ.le) (Real.exp_pos _).le
  have hqmeas : Measurable q := by
    dsimp [q]
    simp only [dotProduct]
    fun_prop
  have hρmeas : Measurable ρ :=
    hqmeas.ennreal_ofReal
  have hρtop : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), ρ x < ∞ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hqint : Integrable q := by
    dsimp [q]
    exact (BanditAlgorithm.isotropic_b_integrable hb).const_mul _
  have hqone : (∫ x, q x) = 1 := by
    dsimp [q]
    rw [integral_const_mul, BanditAlgorithm.isotropic_b_integral d b]
    dsimp [J]
    exact inv_mul_cancel₀ hJ.ne'
  have hhprob : IsProbabilityMeasure h := by
    change IsProbabilityMeasure (volume.withDensity ρ)
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hqint
      (Filter.Eventually.of_forall hqnonneg)]
    rw [hqone]
    simp
  refine ⟨h, hhprob, ?_⟩
  intro S V hV
  let K : Matrix (Fin d) (Fin d) ℝ :=
    lam • (1 : Matrix (Fin d) (Fin d) ℝ) + V
  have hlamI : (lam • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef :=
    Matrix.PosDef.one.smul hlam
  have hK : K.PosDef := hlamI.add_posSemidef hV
  have hquad (x : Fin d → ℝ) :
      x ⬝ᵥ K *ᵥ x = lam * (x ⬝ᵥ x) + x ⬝ᵥ V *ᵥ x := by
    simp only [K, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_add, dotProduct_smul]
    ring
  have hcombine (x : Fin d → ℝ) :
      (ρ x).toReal *
          Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x)) =
        J⁻¹ * Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x)) := by
    rw [show ρ x = ENNReal.ofReal (q x) by rfl,
      ENNReal.toReal_ofReal (hqnonneg x)]
    dsimp [q]
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    rw [hquad]
    dsimp [b]
    ring
  constructor
  · change Integrable
      (fun x => Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x)))
      (volume.withDensity ρ)
    rw [integrable_withDensity_iff_integrable_smul' hρmeas hρtop]
    have hi :=
      (BanditAlgorithm.shifted_quadratic_integrable hK S).const_mul J⁻¹
    apply hi.congr
    exact Filter.Eventually.of_forall fun x => by
      simpa only [smul_eq_mul] using (hcombine x).symm
  · change (∫ x, Real.exp
        (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x)) ∂volume.withDensity ρ) = _
    rw [integral_withDensity_eq_integral_toReal_smul hρmeas hρtop]
    have hint :
        (∫ x, (ρ x).toReal •
            Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x))) =
          J⁻¹ * ∫ x,
            Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simpa only [smul_eq_mul] using hcombine x
    rw [hint, BanditAlgorithm.shifted_quadratic_integral hK S]
    have hnorm := BanditAlgorithm.gaussian_normalization hlam hK
    have hJdef :
        J = (Real.sqrt (Real.pi / (lam / 2))) ^ d := by
      rfl
    calc
      J⁻¹ *
          (Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
              (ENNReal.ofReal |(CFC.sqrt K).det⁻¹|).toReal *
            (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d) =
          Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
            (((Real.sqrt (Real.pi / (lam / 2))) ^ d)⁻¹ *
              |(CFC.sqrt K).det|⁻¹ *
                (Real.sqrt Real.pi * Real.sqrt 2) ^ d) := by
            rw [hJdef]
            have hBpos : 0 < (CFC.sqrt K).det := by
              rw [hK.posSemidef.det_sqrt]
              simpa using Real.sqrt_pos.2 hK.det_pos
            rw [ENNReal.toReal_ofReal (abs_nonneg _),
              abs_inv, abs_of_pos hBpos]
            have hsqrt :
                Real.sqrt (Real.pi / (1 / 2 : ℝ)) =
                  Real.sqrt Real.pi * Real.sqrt 2 := by
              rw [show Real.pi / (1 / 2 : ℝ) = Real.pi * 2 by ring,
                Real.sqrt_mul Real.pi_pos.le]
            rw [hsqrt]
            ring
      _ = Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
            Real.exp (-1 / 2 * Real.log (K.det / lam ^ d)) := by
          rw [hnorm]
      _ = Real.exp
            (1 / 2 *
              (S ⬝ᵥ K⁻¹ *ᵥ S - Real.log (K.det / lam ^ d))) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ = Real.exp
            (1 / 2 *
              (S ⬝ᵥ
                  (lam • (1 : Matrix (Fin d) (Fin d) ℝ) + V)⁻¹ *ᵥ S -
                Real.log
                  ((lam • (1 : Matrix (Fin d) (Fin d) ℝ) + V).det /
                    lam ^ d))) := by
          rfl





set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open BanditAlgorithm

section LinUCBProof

def LinUCBProof.historyPrefix {k t n : Nat} (ht : t ≤ n) (h : BanditHistory k n) : BanditHistory k t :=
  fun i => h (Fin.castLE ht i)

lemma LinUCBProof.measurable_prefix {k t n : Nat} (ht : t ≤ n) :
    Measurable (historyPrefix (k := k) ht) := by
  exact measurable_pi_lambda _ fun i => measurable_pi_apply (Fin.castLE ht i)

lemma LinUCBProof.prefix_self {k n : Nat} (ht : n ≤ n) :
    historyPrefix (k := k) ht = id := by
  funext h i
  rfl

lemma LinUCBProof.prefix_snoc {k t n : Nat} (ht : t ≤ n + 1) (htn : t ≤ n)
    (h : BanditHistory k n) (z : Fin k × Real) :
    historyPrefix ht (Fin.snoc h z) = historyPrefix htn h := by
  funext i
  have hi : (i : Nat) < n := lt_of_lt_of_le i.isLt htn
  simp [historyPrefix, Fin.snoc, hi]
  congr 1

lemma LinUCBProof.banditMeasure_map_prefix {k : Nat} (ν : StochasticBandit k) (π : BanditPolicy k)
    {t n : Nat} (ht : t ≤ n) :
    Measure.map (historyPrefix ht) (banditMeasure ν π n) = banditMeasure ν π t := by
  induction n generalizing t with
  | zero =>
    have ht0 : t = 0 := by omega
    subst t
    rw [prefix_self, Measure.map_id]
  | succ n ih =>
    by_cases htn : t ≤ n
    · rw [banditMeasure, Measure.map_map (measurable_prefix ht) measurable_banditHistorySnoc]
      have hcomp :
          historyPrefix ht ∘ (fun p : BanditHistory k n × (Fin k × Real) => Fin.snoc p.1 p.2) =
            historyPrefix htn ∘ Prod.fst := by
        funext p
        exact prefix_snoc ht htn p.1 p.2
      rw [hcomp, ← Measure.map_map (measurable_prefix htn) measurable_fst,
        ← Measure.fst, Measure.fst_compProd]
      exact ih htn
    · have hteq : t = n + 1 := by omega
      subst t
      rw [prefix_self, Measure.map_id]

end LinUCBProof






set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix
open BanditAlgorithm
open scoped ENNReal

section LinUCBProof
open LinUCBProof

noncomputable def LinUCBProof.increment {k d : Nat} (arms : Fin k → Fin d → Real)
    (θ x : Fin d → Real) (z : Fin k × Real) : Real :=
  (x ⬝ᵥ arms z.1) * (z.2 - arms z.1 ⬝ᵥ θ) - (x ⬝ᵥ arms z.1) ^ 2 / 2

noncomputable def LinUCBProof.potential {k d n : Nat} (arms : Fin k → Fin d → Real)
    (θ x : Fin d → Real) (h : BanditHistory k n) : Real :=
  Real.exp (∑ t : Fin n, increment arms θ x (h t))

lemma LinUCBProof.measurable_increment {k d : Nat} (arms : Fin k → Fin d → Real)
    (θ x : Fin d → Real) : Measurable (increment arms θ x) := by
  have ha (i : Fin d) : Measurable (fun j : Fin k => arms j i) := measurable_of_countable _
  unfold increment
  simp only [dotProduct]
  fun_prop

lemma LinUCBProof.measurable_potential_joint {k d n : Nat} (arms : Fin k → Fin d → Real)
    (θ : Fin d → Real) :
    Measurable (fun p : (Fin d → Real) × BanditHistory k n => potential arms θ p.1 p.2) := by
  have ha (i : Fin d) : Measurable (fun j : Fin k => arms j i) := measurable_of_countable _
  simp only [potential, increment, dotProduct]
  fun_prop

lemma LinUCBProof.measurable_potential {k d n : Nat} (arms : Fin k → Fin d → Real)
    (θ x : Fin d → Real) : Measurable (potential (n := n) arms θ x) := by
  unfold potential
  apply Real.measurable_exp.comp
  exact Finset.measurable_sum _ fun t _ =>
    (measurable_increment arms θ x).comp (measurable_pi_apply t)

lemma LinUCBProof.potential_snoc {k d n : Nat} (arms : Fin k → Fin d → Real)
    (θ x : Fin d → Real) (h : BanditHistory k n) (z : Fin k × Real) :
    potential arms θ x (Fin.snoc h z) = potential arms θ x h * Real.exp (increment arms θ x z) := by
  simp [potential, Fin.sum_univ_castSucc, Real.exp_add]

lemma LinUCBProof.subgaussian_factor_lintegral {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    (Y : Ω → Real) (hY : HasSubgaussianMGF Y 1 μ) (u : Real) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (u * Y ω - u ^ 2 / 2)) ∂μ) ≤ 1 := by
  have hfactor : (fun ω => Real.exp (u * Y ω - u ^ 2 / 2)) =
      fun ω => Real.exp (-u ^ 2 / 2) * Real.exp (u * Y ω) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  have hint : Integrable (fun ω => Real.exp (u * Y ω - u ^ 2 / 2)) μ := by
    rw [hfactor]
    exact (hY.integrable_exp_mul u).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
  have hmean : (∫ ω, Real.exp (u * Y ω - u ^ 2 / 2) ∂μ) ≤ 1 := by
    rw [hfactor, integral_const_mul]
    calc
      _ ≤ Real.exp (-u ^ 2 / 2) * Real.exp (u ^ 2 / 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        simpa [mgf] using hY.mgf_le u
      _ = 1 := by
        rw [← Real.exp_add, show -u ^ 2 / 2 + u ^ 2 / 2 = 0 by ring, Real.exp_zero]
  exact (ENNReal.ofReal_le_ofReal hmean).trans_eq (by simp)

lemma LinUCBProof.increment_lintegral_le_one {k d : Nat} (arms : Fin k → Fin d → Real)
    (θ x : Fin d → Real) (ν : StochasticBandit k) (hν : IsLinearBandit arms θ ν)
    (π : BanditPolicy k) (n : Nat) (h : BanditHistory k n) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (increment arms θ x z)) ∂banditStepKernel ν π n h) ≤ 1 := by
  have hm := (measurable_increment arms θ x).exp.ennreal_ofReal
  rw [banditStepKernel, Kernel.lintegral_compProd _ _ _ hm]
  have hstep (j : Fin k) :
      (∫⁻ y, ENNReal.ofReal (Real.exp (increment arms θ x (j, y))) ∂ν.P j) ≤ 1 := by
    have hsg : HasSubgaussianMGF (fun y => y - arms j ⬝ᵥ θ) 1 (ν.P j) := by
      simpa only [one_pow, hν.1 j] using hν.2.2 j
    exact subgaussian_factor_lintegral _ hsg (x ⬝ᵥ arms j)
  calc
    _ ≤ ∫⁻ _j, (1 : ENNReal) ∂π.select n h := by
      apply lintegral_mono
      intro j
      exact hstep j
    _ = 1 := by simp

lemma LinUCBProof.potential_lintegral_le_one {k d : Nat} (arms : Fin k → Fin d → Real)
    (θ x : Fin d → Real) (ν : StochasticBandit k) (hν : IsLinearBandit arms θ ν)
    (π : BanditPolicy k) (n : Nat) :
    (∫⁻ h, ENNReal.ofReal (potential arms θ x h) ∂banditMeasure ν π n) ≤ 1 := by
  induction n with
  | zero => simp [banditMeasure, potential]
  | succ n ih =>
    have hf := (measurable_potential (n := n + 1) arms θ x).ennreal_ofReal
    rw [banditMeasure, lintegral_map hf measurable_banditHistorySnoc]
    rw [Measure.lintegral_compProd (f := fun p : BanditHistory k n × (Fin k × Real) =>
      ENNReal.ofReal (potential arms θ x (Fin.snoc p.1 p.2))) (by
        simpa only [Function.comp_def] using hf.comp measurable_banditHistorySnoc)]
    apply le_trans (lintegral_mono fun h => ?_) ih
    have hp : 0 ≤ potential arms θ x h := (Real.exp_pos _).le
    have hsplit (z : Fin k × Real) :
        ENNReal.ofReal (potential arms θ x (Fin.snoc h z)) =
          ENNReal.ofReal (potential arms θ x h) *
            ENNReal.ofReal (Real.exp (increment arms θ x z)) := by
      rw [potential_snoc, ENNReal.ofReal_mul hp]
    rw [lintegral_congr hsplit,
      lintegral_const_mul _ (measurable_increment arms θ x).exp.ennreal_ofReal]
    calc
      _ ≤ ENNReal.ofReal (potential arms θ x h) * 1 :=
        mul_le_mul_right (increment_lintegral_le_one arms θ x ν hν π n h) _
      _ = _ := mul_one _

end LinUCBProof






set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix
open BanditAlgorithm
open scoped ENNReal

section LinUCBProof
open LinUCBProof

noncomputable def LinUCBProof.historyGram {k d n : Nat} (arms : Fin k → Fin d → Real)
    (h : BanditHistory k n) : Matrix (Fin d) (Fin d) Real :=
  ∑ t : Fin n, vecMulVec (arms (h t).1) (arms (h t).1)

noncomputable def LinUCBProof.historyNoise {k d n : Nat} (arms : Fin k → Fin d → Real)
    (θ : Fin d → Real) (h : BanditHistory k n) : Fin d → Real :=
  ∑ t : Fin n, ((h t).2 - arms (h t).1 ⬝ᵥ θ) • arms (h t).1

noncomputable def LinUCBProof.historyDesign {k d n : Nat} (arms : Fin k → Fin d → Real)
    (h : BanditHistory k n) : Matrix (Fin d) (Fin d) Real :=
  1 + historyGram arms h

noncomputable def LinUCBProof.statistic {k d n : Nat} (arms : Fin k → Fin d → Real)
    (θ : Fin d → Real) (h : BanditHistory k n) : Real :=
  historyNoise arms θ h ⬝ᵥ (historyDesign arms h)⁻¹ *ᵥ historyNoise arms θ h -
    Real.log (historyDesign arms h).det

lemma LinUCBProof.historyGram_posSemidef {k d n : Nat} (arms : Fin k → Fin d → Real)
    (h : BanditHistory k n) : (historyGram arms h).PosSemidef := by
  apply Finset.sum_induction _ _ (fun _ _ hx hy => hx.add hy) .zero
  intro t ht
  simpa using posSemidef_vecMulVec_self_star (arms (h t).1)

lemma LinUCBProof.historyDesign_posDef {k d n : Nat} (arms : Fin k → Fin d → Real)
    (h : BanditHistory k n) : (historyDesign arms h).PosDef :=
  Matrix.PosDef.one.add_posSemidef (historyGram_posSemidef arms h)

lemma LinUCBProof.potential_quadratic {k d n : Nat} (arms : Fin k → Fin d → Real)
    (θ x : Fin d → Real) (h : BanditHistory k n) :
    potential arms θ x h = Real.exp
      (x ⬝ᵥ historyNoise arms θ h - 1 / 2 * (x ⬝ᵥ historyGram arms h *ᵥ x)) := by
  unfold potential
  congr 1
  simp only [historyNoise, historyGram, dotProduct_sum, sum_mulVec,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [increment, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (arms (h t).1) x]
  ring

lemma LinUCBProof.finite_selfNormalized_tail {k d : Nat} (arms : Fin k → Fin d → Real)
    (θ : Fin d → Real) (ν : StochasticBandit k) (hν : IsLinearBandit arms θ ν)
    (π : BanditPolicy k) (n : Nat) {δ : Real} (hδ : 0 < δ) :
    banditMeasure ν π n {h | 2 * Real.log (1 / δ) ≤ statistic arms θ h} ≤
      ENNReal.ofReal δ := by
  rcases BanditAlgorithm.isotropic_gaussian_unregularized_quadratic_mixture
      (d := d) (lam := 1) (by norm_num) with ⟨H, hH, hgauss⟩
  letI : IsProbabilityMeasure H := hH
  let M : BanditHistory k n → Real := fun h => ∫ x, potential arms θ x h ∂H
  have hformula (h : BanditHistory k n) :
      Integrable (fun x => potential arms θ x h) H ∧
        M h = Real.exp (1 / 2 * statistic arms θ h) := by
    have h := hgauss (historyNoise arms θ h) (historyGram arms h)
      (historyGram_posSemidef arms h)
    simpa only [M, potential_quadratic, one_smul, one_pow, div_one,
      statistic, historyDesign] using h
  have hj := measurable_potential_joint (n := n) arms θ
  have hM : Measurable M := hj.stronglyMeasurable.integral_prod_left.measurable
  have hmoment : (∫⁻ h, ENNReal.ofReal (M h) ∂banditMeasure ν π n) ≤ 1 := by
    have hconv (h : BanditHistory k n) :
        ENNReal.ofReal (M h) = ∫⁻ x, ENNReal.ofReal (potential arms θ x h) ∂H :=
      ofReal_integral_eq_lintegral_ofReal (hformula h).1
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    calc
      _ = ∫⁻ h, ∫⁻ x, ENNReal.ofReal (potential arms θ x h) ∂H ∂banditMeasure ν π n :=
        lintegral_congr hconv
      _ = ∫⁻ x, ∫⁻ h, ENNReal.ofReal (potential arms θ x h) ∂banditMeasure ν π n ∂H :=
        (lintegral_lintegral_swap hj.ennreal_ofReal.aemeasurable).symm
      _ ≤ ∫⁻ _x, (1 : ENNReal) ∂H :=
        lintegral_mono fun x => potential_lintegral_le_one arms θ x ν hν π n
      _ = 1 := by simp
  have hmark := meas_ge_le_lintegral_div (μ := banditMeasure ν π n)
    (f := fun h => ENNReal.ofReal (M h)) hM.ennreal_ofReal.aemeasurable
    (ne_of_gt (ENNReal.ofReal_pos.mpr (one_div_pos.mpr hδ))) ENNReal.ofReal_ne_top
  calc
    _ ≤ banditMeasure ν π n {h | ENNReal.ofReal (1 / δ) ≤ ENNReal.ofReal (M h)} := by
      apply measure_mono
      intro h hh
      apply ENNReal.ofReal_le_ofReal
      rw [(hformula h).2]
      apply (Real.log_le_iff_le_exp (one_div_pos.mpr hδ)).mp
      change Real.log (1 / δ) ≤ 1 / 2 * statistic arms θ h
      change 2 * Real.log (1 / δ) ≤ statistic arms θ h at hh
      linarith
    _ ≤ (∫⁻ h, ENNReal.ofReal (M h) ∂banditMeasure ν π n) / ENNReal.ofReal (1 / δ) := hmark
    _ ≤ 1 / ENNReal.ofReal (1 / δ) := ENNReal.div_le_div_right hmoment _
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_div_of_pos (one_div_pos.mpr hδ)]
      simp

end LinUCBProof







set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix
open BanditAlgorithm
open scoped ENNReal

section LinUCBProof
open LinUCBProof

def LinUCBProof.failureSet {k d : Nat} (arms : Fin k → Fin d → Real) (θ : Fin d → Real)
    (n : Nat) : Set (BanditHistory k n) :=
  {h | ∃ t : Fin n, 4 * Real.log n ≤
    statistic arms θ (historyPrefix (Nat.le_of_lt t.isLt) h)}

lemma LinUCBProof.failureSet_measure_le {k d : Nat} (arms : Fin k → Fin d → Real)
    (θ : Fin d → Real) (ν : StochasticBandit k) (hν : IsLinearBandit arms θ ν)
    (π : BanditPolicy k) (n : Nat) (hn : 2 ≤ n) :
    banditMeasure ν π n (failureSet arms θ n) ≤ ENNReal.ofReal (1 / n) := by
  have hn0 : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hδ : (0 : Real) < 1 / (n : Real) ^ 2 := by positivity
  have hlog : 2 * Real.log (1 / (1 / (n : Real) ^ 2)) = 4 * Real.log n := by
    rw [one_div_one_div, Real.log_pow]
    ring
  have hprefix (t : Fin n) :
      banditMeasure ν π n {h | 4 * Real.log n ≤
        statistic arms θ (historyPrefix (Nat.le_of_lt t.isLt) h)} ≤
          ENNReal.ofReal (1 / (n : Real) ^ 2) := by
    let bad : Set (BanditHistory k t) := {h | 4 * Real.log n ≤ statistic arms θ h}
    have htail : banditMeasure ν π t bad ≤ ENNReal.ofReal (1 / (n : Real) ^ 2) := by
      simpa only [hlog] using finite_selfNormalized_tail arms θ ν hν π t hδ
    calc
      _ ≤ (banditMeasure ν π n).map (historyPrefix (Nat.le_of_lt t.isLt)) bad :=
        Measure.le_map_apply (measurable_prefix (Nat.le_of_lt t.isLt)).aemeasurable bad
      _ = banditMeasure ν π t bad := by rw [banditMeasure_map_prefix]
      _ ≤ _ := htail
  have hsets : failureSet arms θ n = ⋃ t : Fin n,
      {h | 4 * Real.log n ≤ statistic arms θ (historyPrefix (Nat.le_of_lt t.isLt) h)} := by
    ext h
    simp [failureSet]
  rw [hsets]
  calc
    _ ≤ ∑ t : Fin n, banditMeasure ν π n
        {h | 4 * Real.log n ≤ statistic arms θ (historyPrefix (Nat.le_of_lt t.isLt) h)} :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _t : Fin n, ENNReal.ofReal (1 / (n : Real) ^ 2) :=
      Finset.sum_le_sum fun t _ => hprefix t
    _ = ENNReal.ofReal (1 / n) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      congr 1
      field_simp [hn0.ne']

end LinUCBProof







set_option autoImplicit false

open MeasureTheory

section LinUCBProof
open LinUCBProof

local instance {k : Nat} : MeasurableSpace (Option (Fin k)) := ⊤

lemma LinUCBProof.measurable_list_argmax {Ω : Type} [MeasurableSpace Ω] {k : Nat}
    (f : Ω → Fin k → Real) (hf : ∀ i, Measurable (fun x => f x i))
    (l : List (Fin k)) : Measurable (fun x => l.argmax (f x)) := by
  classical
  apply measurable_to_countable'
  intro o
  cases o with
  | none =>
    change MeasurableSet {x | l.argmax (f x) = none}
    simp only [List.argmax_eq_none]
    by_cases hl : l = [] <;> simp [hl]
  | some i =>
    change MeasurableSet {x | l.argmax (f x) = some i}
    simp_rw [List.argmax_eq_some_iff]
    by_cases hi : i ∈ l
    · simp only [hi, true_and]
      apply MeasurableSet.inter
      · have hm : MeasurableSet
            (⋂ a : Fin k, ⋂ (_ : a ∈ l), {x | f x a ≤ f x i}) :=
          MeasurableSet.iInter fun a => MeasurableSet.iInter fun _ =>
            measurableSet_le (hf a) (hf i)
        simp only [Set.iInter_setOf] at hm
        exact hm
      · have hm : MeasurableSet (⋂ a : Fin k, ⋂ (_ : a ∈ l),
            {x | f x i ≤ f x a → l.idxOf i ≤ l.idxOf a}) := by
          apply MeasurableSet.iInter
          intro a
          apply MeasurableSet.iInter
          intro _
          by_cases hindex : l.idxOf i ≤ l.idxOf a
          · simp [hindex]
          · simpa [hindex, not_le] using measurableSet_lt (hf a) (hf i)
        simp only [Set.iInter_setOf] at hm
        exact hm
    · simp [hi]

noncomputable def LinUCBProof.chooseArm {k : Nat} (hk : 0 < k) (f : Fin k → Real) : Fin k :=
  ((List.finRange k).argmax f).getD ⟨0, hk⟩

lemma LinUCBProof.measurable_chooseArm {Ω : Type} [MeasurableSpace Ω] {k : Nat} (hk : 0 < k)
    (f : Ω → Fin k → Real) (hf : ∀ i, Measurable (fun x => f x i)) :
    Measurable (fun x => chooseArm hk (f x)) := by
  exact (measurable_of_countable
    (fun o : Option (Fin k) => o.getD ⟨0, hk⟩)).comp
      (measurable_list_argmax f hf (List.finRange k))

lemma LinUCBProof.chooseArm_max {k : Nat} (hk : 0 < k) (f : Fin k → Real) (i : Fin k) :
    f i ≤ f (chooseArm hk f) := by
  classical
  cases he : (List.finRange k).argmax f with
  | none =>
    have hl : List.finRange k = [] := List.argmax_eq_none.mp he
    have hlen := congrArg List.length hl
    simp only [List.length_finRange, List.length_nil] at hlen
    omega
  | some j =>
    simp only [chooseArm, he, Option.getD_some]
    exact List.le_of_mem_argmax (by simp) he

end LinUCBProof


-- Accepted Harry_Xu submission 83bbfab0-2275-4f96-a9cc-7fe2be9f9eb2.








open Matrix

section BanditAlgorithm
open BanditAlgorithm

private lemma BanditAlgorithm.det_add_vecMulVec {d : ℕ}
    (V : Matrix (Fin d) (Fin d) ℝ) (hV : V.PosDef) (u : Fin d → ℝ) :
    (V + vecMulVec u u).det =
      V.det * (1 + u ⬝ᵥ V⁻¹ *ᵥ u) := by
  rw [vecMulVec_eq Unit,
    Matrix.det_add_replicateCol_mul_replicateRow
      (hV.isUnit.map Matrix.detMonoidHom)]
  congr 2
  rw [Matrix.det_unique]
  change
    (1 + ∑ j, (∑ i, u i * V⁻¹ i j) * u j) =
      1 + ∑ i, u i * ∑ j, V⁻¹ i j * u j
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma BanditAlgorithm.regularizedDesignMatrixSeq_zero {d : ℕ} (lam : ℝ)
    (a : ℕ → Fin d → ℝ) :
    regularizedDesignMatrixSeq d lam a 0 =
      lam • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  simp [regularizedDesignMatrixSeq, regularizedDesignMatrix]

private lemma BanditAlgorithm.regularizedDesignMatrixSeq_succ {d t : ℕ} (lam : ℝ)
    (a : ℕ → Fin d → ℝ) :
    regularizedDesignMatrixSeq d lam a (t + 1) =
      regularizedDesignMatrixSeq d lam a t +
        vecMulVec (a (t + 1)) (a (t + 1)) := by
  simp only [regularizedDesignMatrixSeq, regularizedDesignMatrix,
    Finset.sum_range_succ, Finset.sum_const_zero, Finset.sum_add_distrib]
  abel

private lemma BanditAlgorithm.regularizedDesignMatrixSeq_posDef {d t : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (a : ℕ → Fin d → ℝ) :
    (regularizedDesignMatrixSeq d lam a t).PosDef := by
  rw [regularizedDesignMatrixSeq, regularizedDesignMatrix]
  exact (Matrix.PosDef.one.smul hlam).add_posSemidef
    (Matrix.posSemidef_sum (Finset.range t)
      fun i _ ↦ by simpa using Matrix.posSemidef_vecMulVec_self_star (a (i + 1)))

private lemma BanditAlgorithm.min_one_le_two_log_one_add {u : ℝ} (hu : 0 ≤ u) :
    min 1 u ≤ 2 * Real.log (1 + u) := by
  have hden : 0 < u + 2 := by linarith
  have hseries := Exp3ConcentrationC5.log_lower hu
  have hmid : min 1 u ≤ 4 * u / (u + 2) := by
    rw [le_div_iff₀ hden]
    by_cases h : u ≤ 1
    · rw [min_eq_right h]
      nlinarith
    · rw [min_eq_left (le_of_not_ge h)]
      nlinarith
  calc
    min 1 u ≤ 4 * u / (u + 2) := hmid
    _ = 2 * (2 * u / (u + 2)) := by ring
    _ ≤ 2 * Real.log (1 + u) :=
      mul_le_mul_of_nonneg_left hseries (by norm_num : (0 : ℝ) ≤ 2)

private lemma BanditAlgorithm.log_det_ratio_eq_sum {d n : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (a : ℕ → Fin d → ℝ) :
    Real.log
        ((regularizedDesignMatrixSeq d lam a n).det /
          (regularizedDesignMatrixSeq d lam a 0).det) =
      ∑ t ∈ Finset.range n,
        Real.log
          (1 + a (t + 1) ⬝ᵥ
            (regularizedDesignMatrixSeq d lam a t)⁻¹ *ᵥ a (t + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      let V := regularizedDesignMatrixSeq d lam a n
      let u := a (n + 1)
      have hV : V.PosDef := regularizedDesignMatrixSeq_posDef hlam a
      have hV0 : (regularizedDesignMatrixSeq d lam a 0).PosDef :=
        regularizedDesignMatrixSeq_posDef hlam a
      have hq : 0 ≤ u ⬝ᵥ V⁻¹ *ᵥ u := by
        simpa using hV.inv.posSemidef.dotProduct_mulVec_nonneg u
      have hdet :
          (regularizedDesignMatrixSeq d lam a (n + 1)).det =
            V.det * (1 + u ⬝ᵥ V⁻¹ *ᵥ u) := by
        rw [regularizedDesignMatrixSeq_succ]
        exact det_add_vecMulVec V hV u
      rw [hdet]
      have hratio :
          V.det * (1 + u ⬝ᵥ V⁻¹ *ᵥ u) /
              (regularizedDesignMatrixSeq d lam a 0).det =
            (V.det / (regularizedDesignMatrixSeq d lam a 0).det) *
              (1 + u ⬝ᵥ V⁻¹ *ᵥ u) := by ring
      rw [hratio, Real.log_mul]
      · rw [ih, Finset.sum_range_succ]
      · exact div_ne_zero hV.det_pos.ne' hV0.det_pos.ne'
      · positivity

private lemma BanditAlgorithm.elliptical_sum_le_log_det {d n : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (a : ℕ → Fin d → ℝ) :
    ∑ t ∈ Finset.range n,
        min 1 (a (t + 1) ⬝ᵥ
          (regularizedDesignMatrixSeq d lam a t)⁻¹ *ᵥ a (t + 1)) ≤
      2 * Real.log
        ((regularizedDesignMatrixSeq d lam a n).det /
          (regularizedDesignMatrixSeq d lam a 0).det) := by
  rw [log_det_ratio_eq_sum hlam a, Finset.mul_sum]
  gcongr with t ht
  exact min_one_le_two_log_one_add <| by
    simpa using
      (regularizedDesignMatrixSeq_posDef (t := t) hlam a).inv.posSemidef
        |>.dotProduct_mulVec_nonneg (a (t + 1))

private lemma BanditAlgorithm.det_le_pow_trace_div {d : ℕ} (hd : 0 < d)
    {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) :
    V.det ≤ (V.trace / d) ^ d := by
  let e : Fin d → ℝ := hV.isHermitian.eigenvalues
  have he : ∀ i ∈ (Finset.univ : Finset (Fin d)), 0 ≤ e i :=
    fun i _ ↦ hV.eigenvalues_pos i |>.le
  have hamgm := Real.geom_mean_le_arith_mean
    (Finset.univ : Finset (Fin d)) (fun _ : Fin d ↦ (1 : ℝ)) e
    (by simp) (by simpa using hd) he
  simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hamgm
  change
    (∏ i, hV.isHermitian.eigenvalues i) ^ ((d : ℝ)⁻¹) ≤
      (∑ i, hV.isHermitian.eigenvalues i) / d at hamgm
  have hdet : V.det = ∏ i, hV.isHermitian.eigenvalues i := by
    simpa using hV.isHermitian.det_eq_prod_eigenvalues
  have htrace : V.trace = ∑ i, hV.isHermitian.eigenvalues i := by
    simpa using hV.isHermitian.trace_eq_sum_eigenvalues
  rw [← hdet, ← htrace] at hamgm
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hV.det_pos.le _) hamgm d
  simpa [Real.rpow_inv_natCast_pow hV.det_pos.le (Nat.ne_of_gt hd)] using hp

private lemma BanditAlgorithm.regularizedDesignMatrixSeq_trace {d n : ℕ} (lam : ℝ)
    (a : ℕ → Fin d → ℝ) :
    (regularizedDesignMatrixSeq d lam a n).trace =
      d * lam + ∑ t ∈ Finset.range n, a (t + 1) ⬝ᵥ a (t + 1) := by
  simp [regularizedDesignMatrixSeq, regularizedDesignMatrix,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum,
    Matrix.trace_vecMulVec, Matrix.trace_one, Fintype.card_fin]
  ring

private lemma BanditAlgorithm.regularizedDesignMatrixSeq_trace_le {d n : ℕ} (lam L : ℝ)
    (a : ℕ → Fin d → ℝ)
    (ha : ∀ t ∈ Finset.range n,
      Real.sqrt (a (t + 1) ⬝ᵥ a (t + 1)) ≤ L) :
    (regularizedDesignMatrixSeq d lam a n).trace ≤ d * lam + n * L ^ 2 := by
  rw [regularizedDesignMatrixSeq_trace]
  gcongr
  calc
    ∑ t ∈ Finset.range n, a (t + 1) ⬝ᵥ a (t + 1)
        ≤ ∑ _t ∈ Finset.range n, L ^ 2 := by
          gcongr with t ht
          have hq : 0 ≤ a (t + 1) ⬝ᵥ a (t + 1) := by
            exact Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _
          have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) (ha t ht) 2
          simpa [Real.sq_sqrt hq] using hs
    _ = n * L ^ 2 := by simp

private lemma BanditAlgorithm.regularized_log_det_ratio_le {d n : ℕ} (hd : 0 < d)
    {lam L : ℝ} (hlam : 0 < lam) (a : ℕ → Fin d → ℝ)
    (ha : ∀ t ∈ Finset.range n,
      Real.sqrt (a (t + 1) ⬝ᵥ a (t + 1)) ≤ L) :
    Real.log
        ((regularizedDesignMatrixSeq d lam a n).det /
          (regularizedDesignMatrixSeq d lam a 0).det) ≤
      d * Real.log ((d * lam + n * L ^ 2) / (d * lam)) := by
  let V := regularizedDesignMatrixSeq d lam a n
  have hV : V.PosDef := regularizedDesignMatrixSeq_posDef hlam a
  have hV0 : (regularizedDesignMatrixSeq d lam a 0).PosDef :=
    regularizedDesignMatrixSeq_posDef hlam a
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have htrace := regularizedDesignMatrixSeq_trace_le lam L a ha
  have havg :
      V.trace / d ≤ (d * lam + n * L ^ 2) / d :=
    div_le_div_of_nonneg_right htrace hdR.le
  have havg0 : 0 ≤ V.trace / d := by
    exact div_nonneg hV.trace_pos.le hdR.le
  have hdet :
      V.det ≤ ((d * lam + n * L ^ 2) / d) ^ d :=
    (det_le_pow_trace_div hd hV).trans
      (pow_le_pow_left₀ havg0 havg d)
  have hdet0 :
      (regularizedDesignMatrixSeq d lam a 0).det = lam ^ d := by
    rw [regularizedDesignMatrixSeq_zero, Matrix.det_smul,
      Fintype.card_fin, Matrix.det_one, mul_one]
  have hden : 0 < lam ^ d := pow_pos hlam d
  have hratio :
      V.det / (regularizedDesignMatrixSeq d lam a 0).det ≤
        ((d * lam + n * L ^ 2) / (d * lam)) ^ d := by
    have hrhs :
        ((d * lam + n * L ^ 2) / (d * lam)) ^ d =
          (((d * lam + n * L ^ 2) / d) ^ d) / lam ^ d := by
      rw [div_pow, div_pow, mul_pow]
      field_simp
    rw [hdet0, hrhs]
    exact (div_le_div_iff_of_pos_right hden).2 hdet
  have hleft :
      0 < V.det / (regularizedDesignMatrixSeq d lam a 0).det :=
    div_pos hV.det_pos hV0.det_pos
  have hbase :
      0 < (d * lam + n * L ^ 2) / (d * lam) := by
    have hdl : 0 < (d : ℝ) * lam := mul_pos hdR hlam
    have hnL : 0 ≤ (n : ℝ) * L ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    exact div_pos (add_pos_of_pos_of_nonneg hdl hnL) hdl
  have hlog := Real.log_le_log hleft hratio
  simpa [Real.log_pow] using hlog

private lemma BanditAlgorithm.inverse_weighted_cauchy {d : ℕ}
    {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef)
    (a w : Fin d → ℝ) :
    (a ⬝ᵥ w) ^ 2 ≤
      (a ⬝ᵥ V⁻¹ *ᵥ a) * (w ⬝ᵥ V *ᵥ w) := by
  let B := Matrix.toBilin' V⁻¹
  have hBnonneg : ∀ z, 0 ≤ B z z := by
    intro z
    simpa [B, Matrix.toBilin'_apply'] using
      hV.inv.posSemidef.dotProduct_mulVec_nonneg z
  have hBsymm : LinearMap.IsSymm B := by
    constructor
    intro z y
    simp only [B, Matrix.toBilin'_apply', RingHom.id_apply,
      dotProduct, Matrix.mulVec]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hsymm : V⁻¹ i j = V⁻¹ j i := by
      simpa using hV.inv.isHermitian.apply j i
    rw [hsymm]
    ring
  have hcs := B.apply_sq_le_of_symm hBnonneg hBsymm a (V *ᵥ w)
  have hcancel : V⁻¹ *ᵥ (V *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul V (hV.isUnit.map Matrix.detMonoidHom),
      Matrix.one_mulVec]
  simpa [B, Matrix.toBilin'_apply', hcancel, dotProduct_comm] using hcs


end BanditAlgorithm


section BanditAlgorithm
open BanditAlgorithm

lemma BanditAlgorithm.linucb_inverse_weighted_cauchy {d : Nat}
    {V : Matrix (Fin d) (Fin d) Real} (hV : V.PosDef) (a w : Fin d → Real) :
    (a ⬝ᵥ w) ^ 2 ≤ (a ⬝ᵥ V⁻¹ *ᵥ a) * (w ⬝ᵥ V *ᵥ w) :=
  inverse_weighted_cauchy hV a w

lemma BanditAlgorithm.linucb_elliptical_sum {d n : Nat} (a : Nat → Fin d → Real) :
    ∑ t ∈ Finset.range n,
        min 1 (a (t + 1) ⬝ᵥ (regularizedDesignMatrixSeq d 1 a t)⁻¹ *ᵥ a (t + 1)) ≤
      2 * Real.log (regularizedDesignMatrixSeq d 1 a n).det := by
  simpa [regularizedDesignMatrixSeq_zero] using
    elliptical_sum_le_log_det (lam := 1) (by norm_num) a

lemma BanditAlgorithm.linucb_log_det_bound {d n : Nat} (hd : 0 < d) {L : Real}
    (a : Nat → Fin d → Real)
    (ha : ∀ t ∈ Finset.range n, Real.sqrt (a (t + 1) ⬝ᵥ a (t + 1)) ≤ L) :
    Real.log (regularizedDesignMatrixSeq d 1 a n).det ≤
      d * Real.log ((d + n * L ^ 2) / d) := by
  simpa [regularizedDesignMatrixSeq_zero] using
    regularized_log_det_ratio_le hd (lam := 1) (by norm_num) a ha

end BanditAlgorithm





set_option autoImplicit false

open Matrix

section EllipsoidProof

lemma EllipsoidProof.quadratic_symm {d : Nat} {K : Matrix (Fin d) (Fin d) Real}
    (hK : K.IsHermitian) (x y : Fin d → Real) :
    x ⬝ᵥ K *ᵥ y = y ⬝ᵥ K *ᵥ x := by
  have hxy : x ᵥ* K = K *ᵥ x := by
    have h := vecMul_conjTranspose K x
    rw [hK.eq] at h
    simpa using h
  rw [dotProduct_mulVec, hxy, dotProduct_comm]

lemma EllipsoidProof.quadratic_triangle {d : Nat} {K : Matrix (Fin d) (Fin d) Real}
    (hK : K.PosSemidef) (x y : Fin d → Real) :
    Real.sqrt ((x + y) ⬝ᵥ K *ᵥ (x + y)) ≤
      Real.sqrt (x ⬝ᵥ K *ᵥ x) + Real.sqrt (y ⬝ᵥ K *ᵥ y) := by
  let c : PreInnerProductSpace.Core Real (Fin d → Real) :=
    { inner := fun x y => x ⬝ᵥ K *ᵥ y
      conj_inner_symm := fun x y => by
        simpa using quadratic_symm hK.isHermitian y x
      re_inner_nonneg := fun x => by
        simpa using hK.dotProduct_mulVec_nonneg x
      add_left := fun x y z => add_dotProduct x y (K *ᵥ z)
      smul_left := fun x y r => by simp [smul_dotProduct] }
  have hxy := InnerProductSpace.Core.norm_inner_le_norm (c := c) x y
  change |x ⬝ᵥ K *ᵥ y| ≤ Real.sqrt (x ⬝ᵥ K *ᵥ x) *
    Real.sqrt (y ⬝ᵥ K *ᵥ y) at hxy
  have hx : 0 ≤ x ⬝ᵥ K *ᵥ x := by simpa using hK.dotProduct_mulVec_nonneg x
  have hy : 0 ≤ y ⬝ᵥ K *ᵥ y := by simpa using hK.dotProduct_mulVec_nonneg y
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hxy' := (le_abs_self (x ⬝ᵥ K *ᵥ y)).trans hxy
  simp only [mulVec_add, add_dotProduct, dotProduct_add]
  rw [quadratic_symm hK.isHermitian y x]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]

lemma EllipsoidProof.gram_posSemidef {d : Nat} (a : Nat → Fin d → Real) (t : Nat) :
    (∑ s ∈ Finset.range t, vecMulVec (a s) (a s)).PosSemidef := by
  apply Finset.sum_induction _ _ (fun _ _ hx hy => hx.add hy) .zero
  intro s hs
  simpa using Matrix.posSemidef_vecMulVec_self_star (a s)

lemma EllipsoidProof.ridge_bound {d : Nat} {lam : Real} (hlam : 0 < lam)
    (G : Matrix (Fin d) (Fin d) Real) (hG : G.PosSemidef)
    (S θ : Fin d → Real) :
    let K := lam • (1 : Matrix (Fin d) (Fin d) Real) + G
    let e := K⁻¹ *ᵥ S - lam • (K⁻¹ *ᵥ θ)
    Real.sqrt (e ⬝ᵥ K *ᵥ e) ≤
      Real.sqrt lam * Real.sqrt (θ ⬝ᵥ θ) + Real.sqrt (S ⬝ᵥ K⁻¹ *ᵥ S) := by
  dsimp only
  let K := lam • (1 : Matrix (Fin d) (Fin d) Real) + G
  have hK : K.PosDef := (Matrix.PosDef.one.smul hlam).add_posSemidef hG
  have hdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit
  have hcancel (x : Fin d → Real) : K *ᵥ (K⁻¹ *ᵥ x) = x := by
    rw [mulVec_mulVec, mul_nonsing_inv K hdet, one_mulVec]
  have hfirst : (K⁻¹ *ᵥ S) ⬝ᵥ K *ᵥ (K⁻¹ *ᵥ S) = S ⬝ᵥ K⁻¹ *ᵥ S := by
    rw [hcancel, dotProduct_comm]
  have hsecond : (-(lam • (K⁻¹ *ᵥ θ))) ⬝ᵥ K *ᵥ (-(lam • (K⁻¹ *ᵥ θ))) =
      lam ^ 2 * (θ ⬝ᵥ K⁻¹ *ᵥ θ) := by
    simp only [mulVec_neg, mulVec_smul, neg_dotProduct, dotProduct_neg,
      smul_dotProduct, dotProduct_smul, hcancel, smul_eq_mul]
    rw [dotProduct_comm (K⁻¹ *ᵥ θ) θ]
    ring
  have hbias : lam ^ 2 * (θ ⬝ᵥ K⁻¹ *ᵥ θ) ≤ lam * (θ ⬝ᵥ θ) := by
    let u := K⁻¹ *ᵥ θ
    have hu : K *ᵥ u = θ := hcancel θ
    have hquad : lam * (u ⬝ᵥ u) ≤ θ ⬝ᵥ u := by
      have hnonneg := hG.dotProduct_mulVec_nonneg u
      have hidentity : u ⬝ᵥ K *ᵥ u = lam * (u ⬝ᵥ u) + u ⬝ᵥ G *ᵥ u := by
        simp [K, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul]
      rw [hu, dotProduct_comm u θ] at hidentity
      simp only [star_trivial] at hnonneg
      linarith
    have hnorm : 0 ≤ (θ - lam • u) ⬝ᵥ (θ - lam • u) := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hexpand : (θ - lam • u) ⬝ᵥ (θ - lam • u) =
        θ ⬝ᵥ θ - 2 * lam * (θ ⬝ᵥ u) + lam ^ 2 * (u ⬝ᵥ u) := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
        smul_eq_mul]
      rw [dotProduct_comm u θ]
      ring
    rw [hexpand] at hnorm
    have hscaled := mul_le_mul_of_nonneg_left hquad hlam.le
    have hbound : lam * (θ ⬝ᵥ u) ≤ θ ⬝ᵥ θ := by nlinarith
    have hscaled2 := mul_le_mul_of_nonneg_left hbound hlam.le
    change lam ^ 2 * (θ ⬝ᵥ u) ≤ lam * (θ ⬝ᵥ θ)
    nlinarith
  have hsqrt : Real.sqrt (lam ^ 2 * (θ ⬝ᵥ K⁻¹ *ᵥ θ)) ≤
      Real.sqrt lam * Real.sqrt (θ ⬝ᵥ θ) := by
    calc
      _ ≤ Real.sqrt (lam * (θ ⬝ᵥ θ)) := Real.sqrt_le_sqrt hbias
      _ = _ := Real.sqrt_mul hlam.le _
  have htriangle := quadratic_triangle hK.posSemidef (K⁻¹ *ᵥ S)
    (-(lam • (K⁻¹ *ᵥ θ)))
  rw [hfirst, hsecond] at htriangle
  change Real.sqrt ((K⁻¹ *ᵥ S - lam • (K⁻¹ *ᵥ θ)) ⬝ᵥ
    K *ᵥ (K⁻¹ *ᵥ S - lam • (K⁻¹ *ᵥ θ))) ≤
      Real.sqrt lam * Real.sqrt (θ ⬝ᵥ θ) + Real.sqrt (S ⬝ᵥ K⁻¹ *ᵥ S)
  simp only [← sub_eq_add_neg] at htriangle
  linarith

lemma EllipsoidProof.estimator_error {Ω : Type} {d : Nat} {lam : Real} (hlam : 0 < lam)
    (A : Nat → Ω → Fin d → Real) (η X : Nat → Ω → Real) (θ : Fin d → Real)
    (hX : ∀ t ω, X (t + 1) ω = θ ⬝ᵥ A (t + 1) ω + η (t + 1) ω)
    (t : Nat) (ω : Ω) :
    let K := BanditAlgorithm.regularizedDesignMatrix d lam A t ω
    BanditAlgorithm.regularizedLeastSquares d lam A X t ω - θ =
      K⁻¹ *ᵥ BanditAlgorithm.selfNormalizedSum d η A t ω - lam • (K⁻¹ *ᵥ θ) := by
  let G := ∑ s ∈ Finset.range t, vecMulVec (A (s + 1) ω) (A (s + 1) ω)
  let K := BanditAlgorithm.regularizedDesignMatrix d lam A t ω
  have hG : G.PosSemidef := gram_posSemidef (fun s => A (s + 1) ω) t
  have hK : K.PosDef := (Matrix.PosDef.one.smul hlam).add_posSemidef hG
  have hdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit
  have hcancel : K⁻¹ *ᵥ (K *ᵥ θ) = θ := by
    rw [mulVec_mulVec, nonsing_inv_mul K hdet, one_mulVec]
  have hsum : (∑ s ∈ Finset.range t, X (s + 1) ω • A (s + 1) ω) =
      G *ᵥ θ + BanditAlgorithm.selfNormalizedSum d η A t ω := by
    simp only [G, sum_mulVec, vecMulVec_mulVec, BanditAlgorithm.selfNormalizedSum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    rw [hX, add_smul, dotProduct_comm θ (A (s + 1) ω)]
    simp only [op_smul_eq_smul]
  have hGθ : G *ᵥ θ = K *ᵥ θ - lam • θ := by
    simp [K, BanditAlgorithm.regularizedDesignMatrix, G, add_mulVec, smul_mulVec]
  change K⁻¹ *ᵥ (∑ s ∈ Finset.range t, X (s + 1) ω • A (s + 1) ω) - θ = _
  rw [hsum, hGθ, mulVec_add, mulVec_sub, mulVec_smul, hcancel]
  abel

end EllipsoidProof




set_option autoImplicit false

section LinUCBProof
open LinUCBProof

lemma LinUCBProof.logarithmic_budget (d n L : Real) (hd : 1 ≤ d) (hn : 2 ≤ n) (hL : 1 ≤ L) :
    let B := d * Real.log ((d + n * L ^ 2) / d)
    let beta := (1 + Real.sqrt (4 * Real.log n + B)) ^ 2
    1 ≤ beta ∧
      Real.sqrt (8 * n * beta * B) + 1 ≤ 18 * d * Real.sqrt n * Real.log (n * L) := by
  let z := Real.log (n * L)
  let B := d * Real.log ((d + n * L ^ 2) / d)
  let R := 4 * Real.log n + B
  let beta := (1 + Real.sqrt R) ^ 2
  have hd0 : 0 < d := by linarith
  have hn0 : 0 < n := by linarith
  have hL0 : 0 < L := by linarith
  have hnL : n ≤ n * L := by nlinarith
  have hnL2 : 2 ≤ n * L := hn.trans hnL
  have hlog2 : (1 / 2 : Real) ≤ Real.log 2 := by
    have h := Exp3ConcentrationC5.log_lower (show (0 : Real) ≤ 1 by norm_num)
    norm_num at h
    linarith
  have hz : (1 / 2 : Real) ≤ z :=
    hlog2.trans (Real.log_le_log (by norm_num) hnL2)
  have hz0 : 0 ≤ z := by linarith
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlognz : Real.log n ≤ z := Real.log_le_log hn0 hnL
  have hratio1 : 1 ≤ (d + n * L ^ 2) / d := by
    apply (le_div_iff₀ hd0).mpr
    nlinarith [sq_nonneg L]
  have hratio2 : (d + n * L ^ 2) / d ≤ (n * L) ^ 2 := by
    have hdiv : n * L ^ 2 / d ≤ n * L ^ 2 :=
      div_le_self (mul_nonneg hn0.le (sq_nonneg L)) hd
    have hnp : n + 1 ≤ n ^ 2 := by nlinarith
    have hscaled := mul_le_mul_of_nonneg_right hnp (sq_nonneg L)
    have hLs : 1 ≤ L ^ 2 := by nlinarith
    have hidentity : (d + n * L ^ 2) / d = 1 + n * L ^ 2 / d := by
      field_simp
    rw [hidentity]
    nlinarith
  have hB0 : 0 ≤ B := mul_nonneg hd0.le (Real.log_nonneg hratio1)
  have hB : B ≤ 2 * d * z := by
    have hlog := Real.log_le_log (lt_of_lt_of_le zero_lt_one hratio1) hratio2
    rw [Real.log_pow] at hlog
    have h := mul_le_mul_of_nonneg_left hlog hd0.le
    change d * Real.log ((d + n * L ^ 2) / d) ≤ 2 * d * z
    dsimp only [z] at *
    nlinarith
  have hdz : z ≤ d * z := by nlinarith
  have hdzhalf : (1 / 2 : Real) ≤ d * z := hz.trans hdz
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR : R ≤ 6 * d * z := by dsimp [R]; linarith
  have hbeta1 : 1 ≤ beta := by
    dsimp [beta]
    nlinarith [Real.sqrt_nonneg R]
  have hbeta : beta ≤ 16 * d * z := by
    dsimp [beta]
    nlinarith [Real.sq_sqrt hR0, sq_nonneg (Real.sqrt R - 1)]
  have hproduct : 8 * n * beta * B ≤ 8 * n * (16 * d * z) * (2 * d * z) := by
    gcongr
  have hroot : Real.sqrt (8 * n * beta * B) ≤ 16 * d * Real.sqrt n * z := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hidentity : (16 * d * Real.sqrt n * z) ^ 2 =
        8 * n * (16 * d * z) * (2 * d * z) := by
      simp only [mul_pow, Real.sq_sqrt hn0.le]
      ring
    rw [hidentity]
    exact hproduct
  have hsqrtn : 1 ≤ Real.sqrt n := by
    simpa using Real.sqrt_le_sqrt (show (1 : Real) ≤ n by linarith)
  have hds : 1 ≤ d * Real.sqrt n := by nlinarith
  have hscale := mul_le_mul_of_nonneg_right hds hz0
  change 1 ≤ beta ∧ Real.sqrt (8 * n * beta * B) + 1 ≤
    18 * d * Real.sqrt n * z
  refine ⟨hbeta1, ?_⟩
  nlinarith

end LinUCBProof





set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix
open BanditAlgorithm

section LinUCBProof
open LinUCBProof

local instance {d : Nat} : MeasurableSpace (Matrix (Fin d) (Fin d) Real) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → Real))

local instance {d : Nat} : BorelSpace (Matrix (Fin d) (Fin d) Real) :=
  inferInstanceAs (BorelSpace (Fin d → Fin d → Real))

noncomputable def LinUCBProof.historyRewardSum {k d n : Nat} (arms : Fin k → Fin d → Real)
    (h : BanditHistory k n) : Fin d → Real :=
  ∑ t : Fin n, (h t).2 • arms (h t).1

noncomputable def LinUCBProof.historyEstimator {k d n : Nat} (arms : Fin k → Fin d → Real)
    (h : BanditHistory k n) : Fin d → Real :=
  (historyDesign arms h)⁻¹ *ᵥ historyRewardSum arms h

noncomputable def LinUCBProof.armVariance {k d n : Nat} (arms : Fin k → Fin d → Real)
    (h : BanditHistory k n) (j : Fin k) : Real :=
  arms j ⬝ᵥ (historyDesign arms h)⁻¹ *ᵥ arms j

noncomputable def LinUCBProof.upperIndex {k d n : Nat} (arms : Fin k → Fin d → Real)
    (beta : Real) (h : BanditHistory k n) (j : Fin k) : Real :=
  arms j ⬝ᵥ historyEstimator arms h + Real.sqrt beta * Real.sqrt (armVariance arms h j)

lemma LinUCBProof.measurable_historyDesign {k d n : Nat} (arms : Fin k → Fin d → Real) :
    Measurable (historyDesign (n := n) arms) := by
  classical
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [historyDesign, historyGram, Matrix.add_apply, Matrix.sum_apply,
    vecMulVec_apply]
  apply measurable_const.add
  apply Finset.measurable_sum
  intro t ht
  exact ((measurable_of_countable (fun a : Fin k => arms a i)).comp
    (measurable_pi_apply t).fst).mul
      ((measurable_of_countable (fun a : Fin k => arms a j)).comp
        (measurable_pi_apply t).fst)

lemma LinUCBProof.measurable_matrix_inverse {d : Nat} :
    Measurable (fun A : Matrix (Fin d) (Fin d) Real => A⁻¹) := by
  have hdet : Measurable (fun A : Matrix (Fin d) (Fin d) Real => A.det) :=
    continuous_id.matrix_det.measurable
  have hadj : Measurable (fun A : Matrix (Fin d) (Fin d) Real => A.adjugate) :=
    continuous_id.matrix_adjugate.measurable
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Pi.smul_def', Pi.inv_apply]
    using hdet.inv.smul hadj

lemma LinUCBProof.measurable_historyRewardSum {k d n : Nat} (arms : Fin k → Fin d → Real) :
    Measurable (historyRewardSum (n := n) arms) := by
  classical
  apply measurable_pi_lambda
  intro i
  simp only [historyRewardSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.measurable_sum
  intro t ht
  exact (measurable_pi_apply t).snd.mul
    ((measurable_of_countable (fun a : Fin k => arms a i)).comp
      (measurable_pi_apply t).fst)

lemma LinUCBProof.measurable_historyEstimator {k d n : Nat} (arms : Fin k → Fin d → Real) :
    Measurable (historyEstimator (n := n) arms) := by
  have hV := measurable_matrix_inverse.comp (measurable_historyDesign (n := n) arms)
  have hy := measurable_historyRewardSum (n := n) arms
  apply measurable_pi_lambda
  intro i
  unfold historyEstimator Matrix.mulVec dotProduct
  apply Finset.measurable_sum
  intro j hj
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hV)).mul
    ((measurable_pi_apply j).comp hy)

lemma LinUCBProof.measurable_armVariance {k d n : Nat} (arms : Fin k → Fin d → Real) (j : Fin k) :
    Measurable (fun h : BanditHistory k n => armVariance arms h j) := by
  have hV := measurable_matrix_inverse.comp (measurable_historyDesign (n := n) arms)
  unfold armVariance Matrix.mulVec dotProduct
  apply Finset.measurable_sum
  intro i hi
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro l hl
  exact ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp hV)).mul_const _

lemma LinUCBProof.measurable_upperIndex {k d n : Nat} (arms : Fin k → Fin d → Real)
    (beta : Real) (j : Fin k) :
    Measurable (fun h : BanditHistory k n => upperIndex arms beta h j) := by
  unfold upperIndex
  apply Measurable.add
  · unfold dotProduct
    apply Finset.measurable_sum
    intro i hi
    exact measurable_const.mul ((measurable_pi_apply i).comp
      (measurable_historyEstimator arms))
  · exact measurable_const.mul (measurable_armVariance arms j).sqrt

noncomputable def LinUCBProof.indexPolicy {k d : Nat} (hk : 0 < k)
    (arms : Fin k → Fin d → Real) (beta : Real) : BanditPolicy k where
  select n := Kernel.deterministic (fun h : BanditHistory k n =>
    chooseArm hk (upperIndex arms beta h))
      (measurable_chooseArm hk _ (measurable_upperIndex arms beta))
  markov _ := inferInstance

lemma LinUCBProof.armVariance_nonneg {k d n : Nat} (arms : Fin k → Fin d → Real)
    (h : BanditHistory k n) (j : Fin k) : 0 ≤ armVariance arms h j :=
  (historyDesign_posDef arms h).inv.posSemidef.dotProduct_mulVec_nonneg _

end LinUCBProof





set_option autoImplicit false

open Matrix BanditAlgorithm

section LinUCBProof
open LinUCBProof

noncomputable def LinUCBProof.historyActions {k d n : Nat} (arms : Fin k → Fin d → Real)
    (h : BanditHistory k n) (s : Nat) : Fin d → Real :=
  if hs : s - 1 < n then arms (h ⟨s - 1, hs⟩).1 else 0

lemma LinUCBProof.historyActions_succ {k d n : Nat} (arms : Fin k → Fin d → Real)
    (h : BanditHistory k n) {s : Nat} (hs : s < n) :
    historyActions arms h (s + 1) = arms (h ⟨s, hs⟩).1 := by
  simp [historyActions, hs]

lemma LinUCBProof.historyDesign_eq_seq {k d t n : Nat} (arms : Fin k → Fin d → Real)
    (h : BanditHistory k n) (ht : t ≤ n) :
    historyDesign arms (historyPrefix ht h) =
      regularizedDesignMatrixSeq d 1 (historyActions arms h) t := by
  classical
  simp only [historyDesign, historyGram, regularizedDesignMatrixSeq,
    regularizedDesignMatrix, one_smul]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [historyActions, historyPrefix, Fin.castLE, Nat.lt_of_lt_of_le i.isLt ht]

lemma LinUCBProof.history_log_det_bound {k d t n : Nat} (hd : 0 < d)
    (arms : Fin k → Fin d → Real) (h : BanditHistory k t) {L : Real}
    (hL : ∀ j, Real.sqrt (arms j ⬝ᵥ arms j) ≤ L) (ht : t ≤ n) :
    Real.log (historyDesign arms h).det ≤ d * Real.log ((d + n * L ^ 2) / d) := by
  have hdR : (0 : Real) < d := Nat.cast_pos.mpr hd
  have hfirst := linucb_log_det_bound hd (historyActions arms h) (fun s hs => by
    rw [historyActions_succ arms h (Finset.mem_range.mp hs)]
    exact hL _)
  rw [← historyDesign_eq_seq arms h (le_refl t), prefix_self] at hfirst
  apply hfirst.trans
  apply mul_le_mul_of_nonneg_left _ hdR.le
  apply Real.log_le_log
  · exact div_pos (add_pos_of_pos_of_nonneg hdR (by positivity)) hdR
  · apply div_le_div_of_nonneg_right _ hdR.le
    gcongr

lemma LinUCBProof.history_estimator_error {k d n : Nat} (arms : Fin k → Fin d → Real)
    (theta : Fin d → Real) (h : BanditHistory k n) :
    historyEstimator arms h - theta =
      (historyDesign arms h)⁻¹ *ᵥ historyNoise arms theta h -
        (historyDesign arms h)⁻¹ *ᵥ theta := by
  let K := historyDesign arms h
  have hK := historyDesign_posDef arms h
  have hdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit
  have hcancel : K⁻¹ *ᵥ (K *ᵥ theta) = theta := by
    rw [mulVec_mulVec, nonsing_inv_mul K hdet, one_mulVec]
  have hsum : historyRewardSum arms h =
      historyGram arms h *ᵥ theta + historyNoise arms theta h := by
    simp only [historyRewardSum, historyGram, sum_mulVec, vecMulVec_mulVec,
      historyNoise, ← Finset.sum_add_distrib, op_smul_eq_smul]
    apply Finset.sum_congr rfl
    intro t ht
    rw [← add_smul]
    congr 1
    ring
  have hG : historyGram arms h *ᵥ theta = K *ᵥ theta - theta := by
    simp [K, historyDesign, add_mulVec]
  change K⁻¹ *ᵥ historyRewardSum arms h - theta = _
  rw [hsum, hG, mulVec_add, mulVec_sub, hcancel]
  abel

lemma LinUCBProof.finite_confidence {k d t n : Nat} (hd : 0 < d) (hn : 2 ≤ n)
    (arms : Fin k → Fin d → Real) (theta : Fin d → Real) (h : BanditHistory k t)
    {L : Real} (hL : ∀ j, Real.sqrt (arms j ⬝ᵥ arms j) ≤ L)
    (htheta : Real.sqrt (theta ⬝ᵥ theta) ≤ 1) (ht : t ≤ n)
    (hstat : statistic arms theta h < 4 * Real.log n) :
    (historyEstimator arms h - theta) ⬝ᵥ historyDesign arms h *ᵥ
        (historyEstimator arms h - theta) ≤
      (1 + Real.sqrt (4 * Real.log n + d * Real.log ((d + n * L ^ 2) / d))) ^ 2 := by
  let Q := historyNoise arms theta h ⬝ᵥ
    (historyDesign arms h)⁻¹ *ᵥ historyNoise arms theta h
  have hQ : 0 ≤ Q := (historyDesign_posDef arms h).inv.posSemidef.dotProduct_mulVec_nonneg _
  have hlog := history_log_det_bound hd arms h hL ht
  have hupper : Q ≤ 4 * Real.log n + d * Real.log ((d + n * L ^ 2) / d) := by
    unfold statistic at hstat
    dsimp only [Q]
    linarith
  have hridge := EllipsoidProof.ridge_bound (lam := 1) (by norm_num)
    (historyGram arms h) (historyGram_posSemidef arms h) (historyNoise arms theta h) theta
  have hridge' : Real.sqrt ((historyEstimator arms h - theta) ⬝ᵥ historyDesign arms h *ᵥ
      (historyEstimator arms h - theta)) ≤ Real.sqrt (theta ⬝ᵥ theta) + Real.sqrt Q := by
    rw [history_estimator_error]
    simpa only [one_smul, Real.sqrt_one, one_mul, historyDesign, Q] using hridge
  have hsqrt := Real.sqrt_le_sqrt hupper
  have hnorm : Real.sqrt ((historyEstimator arms h - theta) ⬝ᵥ historyDesign arms h *ᵥ
      (historyEstimator arms h - theta)) ≤
      1 + Real.sqrt (4 * Real.log n + d * Real.log ((d + n * L ^ 2) / d)) := by
    change Real.sqrt Q ≤ _ at hsqrt
    linarith
  have he : 0 ≤ (historyEstimator arms h - theta) ⬝ᵥ historyDesign arms h *ᵥ
      (historyEstimator arms h - theta) :=
    (historyDesign_posDef arms h).posSemidef.dotProduct_mulVec_nonneg _
  simpa only [Real.sq_sqrt he] using
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hnorm 2

end LinUCBProof





set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm

section LinUCBProof
open LinUCBProof

lemma LinUCBProof.deterministic_step_arm_ae {k : Nat} (nu : StochasticBandit k)
    (pi : BanditPolicy k) (m : Nat) (h : BanditHistory k m) (a : Fin k)
    (hselect : (pi.select m) h = Measure.dirac a) :
    ∀ᵐ z ∂banditStepKernel nu pi m h, z.1 = a := by
  rw [ae_iff]
  have hms : MeasurableSet {z : Fin k × Real | z.1 ≠ a} :=
    measurable_fst (measurableSet_singleton a).compl
  rw [banditStepKernel, Kernel.compProd_apply hms, hselect,
    lintegral_dirac' _ (measurable_of_countable _)]
  simp

lemma LinUCBProof.deterministic_last_arm_ae {k : Nat} (nu : StochasticBandit k)
    (pi : BanditPolicy k) (m : Nat) (f : BanditHistory k m → Fin k)
    (hf : Measurable f) (hselect : ∀ h, (pi.select m) h = Measure.dirac (f h)) :
    ∀ᵐ h ∂banditMeasure nu pi (m + 1),
      (h (Fin.last m)).1 = f (historyPrefix (Nat.le_succ m) h) := by
  have hms : MeasurableSet {h : BanditHistory k (m + 1) |
      (h (Fin.last m)).1 = f (historyPrefix (Nat.le_succ m) h)} :=
    measurableSet_eq_fun (measurable_pi_apply (Fin.last m)).fst
      (hf.comp (measurable_prefix _))
  rw [banditMeasure,
    ae_map_iff measurable_banditHistorySnoc.aemeasurable hms]
  have hp : MeasurableSet {p : BanditHistory k m × (Fin k × Real) | p.2.1 = f p.1} :=
    measurableSet_eq_fun measurable_snd.fst (hf.comp measurable_fst)
  have hae := Measure.ae_compProd_of_ae_ae (μ := banditMeasure nu pi m)
    (κ := banditStepKernel nu pi m) hp
    (Filter.Eventually.of_forall fun h =>
      deterministic_step_arm_ae nu pi m h (f h) (hselect h))
  filter_upwards [hae] with p hp
  simpa only [Fin.snoc_last, prefix_snoc _ (le_refl m), prefix_self,
    Function.id_def] using hp

lemma LinUCBProof.indexPolicy_support {k d : Nat} (hk : 0 < k)
    (arms : Fin k → Fin d → Real) (beta : Real) (nu : StochasticBandit k) (n : Nat) :
    ∀ᵐ h ∂banditMeasure nu (indexPolicy hk arms beta) n,
      ∀ t : Fin n, (h t).1 =
        chooseArm hk (upperIndex arms beta (historyPrefix (Nat.le_of_lt t.isLt) h)) := by
  rw [ae_all_iff]
  intro t
  have hm := deterministic_last_arm_ae nu (indexPolicy hk arms beta) t
    (fun h => chooseArm hk (upperIndex arms beta h))
    (measurable_chooseArm hk _ (measurable_upperIndex arms beta))
    (fun h => by simp [indexPolicy, Kernel.deterministic_apply])
  have ht : (t : Nat) + 1 ≤ n := t.isLt
  rw [← banditMeasure_map_prefix nu (indexPolicy hk arms beta) ht] at hm
  have hmap := ae_of_ae_map (measurable_prefix ht).aemeasurable hm
  filter_upwards [hmap] with h hh
  have hprefix : historyPrefix (Nat.le_succ (t : Nat)) (historyPrefix ht h) =
      historyPrefix (Nat.le_of_lt t.isLt) h := by
    funext i
    rfl
  rw [hprefix] at hh
  exact hh

end LinUCBProof





set_option autoImplicit false

open Matrix BanditAlgorithm

section LinUCBProof
open LinUCBProof

lemma LinUCBProof.index_error_bound {k d n : Nat} (arms : Fin k → Fin d → Real)
    (theta : Fin d → Real) (h : BanditHistory k n) {beta : Real} (hbeta : 0 ≤ beta)
    (hconf : (historyEstimator arms h - theta) ⬝ᵥ historyDesign arms h *ᵥ
      (historyEstimator arms h - theta) ≤ beta) (j : Fin k) :
    |arms j ⬝ᵥ historyEstimator arms h - arms j ⬝ᵥ theta| ≤
      Real.sqrt beta * Real.sqrt (armVariance arms h j) := by
  have hcs := linucb_inverse_weighted_cauchy (historyDesign_posDef arms h)
    (arms j) (historyEstimator arms h - theta)
  have hq := armVariance_nonneg arms h j
  have hs : (arms j ⬝ᵥ historyEstimator arms h - arms j ⬝ᵥ theta) ^ 2 ≤
      armVariance arms h j * beta := by
    rw [dotProduct_sub] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_left hconf hq)
  apply abs_le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, Real.sq_sqrt hbeta, Real.sq_sqrt hq]
  nlinarith

lemma LinUCBProof.upperIndex_gap_bound {k d n : Nat} (hk : 0 < k)
    (arms : Fin k → Fin d → Real) (theta : Fin d → Real) (h : BanditHistory k n)
    {beta : Real} (hbeta : 0 ≤ beta)
    (hconf : (historyEstimator arms h - theta) ⬝ᵥ historyDesign arms h *ᵥ
      (historyEstimator arms h - theta) ≤ beta) (i : Fin k) :
    let j := chooseArm hk (upperIndex arms beta h)
    arms i ⬝ᵥ theta - arms j ⬝ᵥ theta ≤
      2 * Real.sqrt beta * Real.sqrt (armVariance arms h j) := by
  dsimp only
  let j := chooseArm hk (upperIndex arms beta h)
  have hi := abs_le.mp (index_error_bound arms theta h hbeta hconf i)
  have hj := abs_le.mp (index_error_bound arms theta h hbeta hconf j)
  have hmax := chooseArm_max hk (upperIndex arms beta h) i
  change upperIndex arms beta h i ≤ upperIndex arms beta h j at hmax
  unfold upperIndex at hmax
  change _ ≤ 2 * Real.sqrt beta * Real.sqrt (armVariance arms h j)
  linarith

noncomputable def LinUCBProof.bestArm {k d : Nat} (hk : 0 < k)
    (arms : Fin k → Fin d → Real) (theta : Fin d → Real) : Fin k :=
  chooseArm hk (fun j => arms j ⬝ᵥ theta)

noncomputable def LinUCBProof.historyGapSum {k d n : Nat} (hk : 0 < k)
    (arms : Fin k → Fin d → Real) (theta : Fin d → Real)
    (h : BanditHistory k n) : Real :=
  ∑ t : Fin n, (arms (bestArm hk arms theta) - arms (h t).1) ⬝ᵥ theta

lemma LinUCBProof.historyGapSum_bounds {k d n : Nat} (hk : 0 < k)
    (arms : Fin k → Fin d → Real) (theta : Fin d → Real) (h : BanditHistory k n)
    (hgap : ∀ i j, theta ⬝ᵥ (arms i - arms j) ≤ 1) :
    0 ≤ historyGapSum hk arms theta h ∧ historyGapSum hk arms theta h ≤ n := by
  constructor
  · apply Finset.sum_nonneg
    intro t ht
    rw [sub_dotProduct]
    exact sub_nonneg.mpr (chooseArm_max hk (fun j => arms j ⬝ᵥ theta) (h t).1)
  · calc
      _ ≤ ∑ _t : Fin n, (1 : Real) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [dotProduct_comm]
        exact hgap _ _
      _ = n := by simp

lemma LinUCBProof.squared_gap_bound {r q beta : Real} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hq : 0 ≤ q) (hbeta : 1 ≤ beta)
    (hucb : r ≤ 2 * Real.sqrt beta * Real.sqrt q) :
    r ^ 2 ≤ 4 * beta * min 1 q := by
  by_cases hq1 : q ≤ 1
  · rw [min_eq_right hq1]
    have hs := pow_le_pow_left₀ hr hucb 2
    simp only [mul_pow, Real.sq_sqrt (show 0 ≤ beta by linarith), Real.sq_sqrt hq] at hs
    nlinarith
  · rw [min_eq_left (le_of_not_ge hq1), mul_one]
    have hs : r ^ 2 ≤ (1 : Real) := by
      simpa only [one_pow] using pow_le_pow_left₀ hr hr1 2
    linarith

end LinUCBProof





set_option autoImplicit false

open Matrix BanditAlgorithm

section LinUCBProof
open LinUCBProof

lemma LinUCBProof.history_regret_bound {k d n : Nat} (hd : 0 < d) (hk : 0 < k)
    (arms : Fin k → Fin d → Real) (theta : Fin d → Real) (h : BanditHistory k n)
    {L beta : Real} (hL : ∀ j, Real.sqrt (arms j ⬝ᵥ arms j) ≤ L) (hbeta : 1 ≤ beta)
    (hgap : ∀ i j, theta ⬝ᵥ (arms i - arms j) ≤ 1)
    (hselect : ∀ t : Fin n, (h t).1 =
      chooseArm hk (upperIndex arms beta (historyPrefix (Nat.le_of_lt t.isLt) h)))
    (hconf : ∀ t : Fin n,
      let p := historyPrefix (Nat.le_of_lt t.isLt) h
      (historyEstimator arms p - theta) ⬝ᵥ historyDesign arms p *ᵥ
        (historyEstimator arms p - theta) ≤ beta) :
    historyGapSum hk arms theta h ≤
      Real.sqrt (8 * n * beta * (d * Real.log ((d + n * L ^ 2) / d))) := by
  classical
  let r : Fin n → Real := fun t =>
    (arms (bestArm hk arms theta) - arms (h t).1) ⬝ᵥ theta
  let q : Fin n → Real := fun t =>
    armVariance arms (historyPrefix (Nat.le_of_lt t.isLt) h) (h t).1
  have hbeta0 : 0 ≤ beta := by linarith
  have hr0 (t : Fin n) : 0 ≤ r t := by
    dsimp only [r]
    rw [sub_dotProduct]
    exact sub_nonneg.mpr (chooseArm_max hk (fun i => arms i ⬝ᵥ theta) (h t).1)
  have hr1 (t : Fin n) : r t ≤ 1 := by
    dsimp only [r]
    rw [dotProduct_comm]
    exact hgap _ _
  have hrq (t : Fin n) : r t ≤ 2 * Real.sqrt beta * Real.sqrt (q t) := by
    have hu := upperIndex_gap_bound hk arms theta
      (historyPrefix (Nat.le_of_lt t.isLt) h) hbeta0 (hconf t) (bestArm hk arms theta)
    dsimp only at hu
    rw [← hselect t] at hu
    simpa only [r, q, sub_dotProduct] using hu
  have hsq (t : Fin n) : r t ^ 2 ≤ 4 * beta * min 1 (q t) :=
    squared_gap_bound (hr0 t) (hr1 t) (armVariance_nonneg _ _ _) hbeta (hrq t)
  have hqeq (t : Fin n) : q t =
      historyActions arms h (t + 1) ⬝ᵥ
        (regularizedDesignMatrixSeq d 1 (historyActions arms h) t)⁻¹ *ᵥ
          historyActions arms h (t + 1) := by
    rw [historyActions_succ arms h t.isLt,
      ← historyDesign_eq_seq arms h (Nat.le_of_lt t.isLt)]
    rfl
  have helliptic := linucb_elliptical_sum (n := n) (historyActions arms h)
  rw [← Fin.sum_univ_eq_sum_range,
    ← historyDesign_eq_seq arms h (le_refl n), prefix_self] at helliptic
  have hsumq : ∑ t : Fin n, min 1 (q t) ≤
      2 * (d * Real.log ((d + n * L ^ 2) / d)) := by
    simp_rw [← hqeq] at helliptic
    exact helliptic.trans (mul_le_mul_of_nonneg_left
      (history_log_det_bound hd arms h hL (le_refl n)) (by norm_num))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin n)) (fun _ => (1 : Real)) r
  have hcs' : (∑ t : Fin n, r t) ^ 2 ≤ (n : Real) * ∑ t : Fin n, r t ^ 2 := by
    simpa using hcs
  have hsum : (∑ t : Fin n, r t ^ 2) ≤ 4 * beta * ∑ t : Fin n, min 1 (q t) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun t ht => hsq t
  have hfinal : (∑ t : Fin n, r t) ^ 2 ≤
      8 * n * beta * (d * Real.log ((d + n * L ^ 2) / d)) := by
    calc
      _ ≤ (n : Real) * ∑ t : Fin n, r t ^ 2 := hcs'
      _ ≤ (n : Real) * (4 * beta * ∑ t : Fin n, min 1 (q t)) := by gcongr
      _ ≤ (n : Real) * (4 * beta * (2 * (d * Real.log ((d + n * L ^ 2) / d)))) := by
        gcongr
      _ = _ := by ring
  exact Real.le_sqrt_of_sq_le hfinal

end LinUCBProof


-- Accepted MKPynnic submission cdf45b26-c875-4abc-836c-d40d8b44fafc.


/-!
Direct-proof work for Lattimore--Szepesvári, Lemma 4.5, printed p. 63:
the canonical reward drawn after selecting arm `i` has conditional mean `μ_i`.
-/

open MeasureTheory ProbabilityTheory

section BanditAlgorithm
open BanditAlgorithm

theorem BanditAlgorithm.banditRewardKernel_apply_rfl' {k : ℕ} (ν : StochasticBandit k) (i : Fin k) :
    banditRewardKernel ν i = ν.P i := rfl

theorem BanditAlgorithm.stepKernel_centered_integrable_test {k : ℕ} (ν : StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditPolicy k) (n : ℕ)
    (h : BanditHistory k n) :
    Integrable (fun z : Fin k × ℝ ↦ z.2 - banditArmMean ν z.1)
      (banditStepKernel ν π n h) := by
  rw [banditStepKernel]
  apply (ProbabilityTheory.integrable_compProd_iff (by fun_prop)).2
  constructor
  · exact Filter.Eventually.of_forall fun i ↦ by
      have hsub : Integrable (fun y : ℝ ↦ y - banditArmMean ν i) (ν.P i) :=
        (hInt i).sub (integrable_const (banditArmMean ν i))
      simpa [banditRewardKernel_apply_rfl'] using hsub
  · exact Integrable.of_finite

theorem BanditAlgorithm.stepKernel_integral_centered_test {k : ℕ} (ν : StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditPolicy k) (n : ℕ)
    (h : BanditHistory k n) :
    ∫ z : Fin k × ℝ, (z.2 - banditArmMean ν z.1) ∂(banditStepKernel ν π n h) = 0 := by
  have hz := stepKernel_centered_integrable_test ν hInt π n h
  rw [banditStepKernel] at hz ⊢
  rw [ProbabilityTheory.integral_compProd hz]
  apply integral_eq_zero_of_ae
  filter_upwards [] with i
  change (∫ y : ℝ, y - banditArmMean ν i ∂(ν.P i)) = 0
  have hy : Integrable (fun y : ℝ ↦ y) (ν.P i) := hInt i
  rw [integral_sub hy (integrable_const _)]
  simp [banditArmMean]

theorem BanditAlgorithm.joint_centered_step_integrable_test {k : ℕ} (ν : StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditPolicy k) (n : ℕ) :
    Integrable
      (fun p : BanditHistory k n × (Fin k × ℝ) ↦
        p.2.2 - banditArmMean ν p.2.1)
      ((banditMeasure ν π n).compProd (banditStepKernel ν π n)) := by
  let moment : Fin k → ℝ := fun i ↦ ∫ y, |y - banditArmMean ν i| ∂(ν.P i)
  let C : ℝ := ∑ i, moment i
  apply (Measure.integrable_compProd_iff (by fun_prop)).2
  constructor
  · exact Filter.Eventually.of_forall fun h ↦
      stepKernel_centered_integrable_test ν hInt π n h
  · apply Integrable.of_mem_Icc 0 C
    · exact ((by fun_prop : StronglyMeasurable
        (fun p : BanditHistory k n × (Fin k × ℝ) ↦
          |p.2.2 - banditArmMean ν p.2.1|))).integral_kernel_prod_right'.aemeasurable
    · exact Filter.Eventually.of_forall fun h ↦ by
        constructor
        · exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun z ↦ abs_nonneg _)
        · have hz := (stepKernel_centered_integrable_test ν hInt π n h).norm
          have hcond :
              (∫ z : Fin k × ℝ, |z.2 - banditArmMean ν z.1|
                ∂(banditStepKernel ν π n h)) =
              ∫ i : Fin k, moment i ∂(π.select n h) := by
            rw [banditStepKernel] at hz ⊢
            change (∫ z : Fin k × ℝ, ‖z.2 - banditArmMean ν z.1‖
              ∂((π.select n).compProd
                ((banditRewardKernel ν).comap Prod.snd measurable_snd)) h) = _
            rw [ProbabilityTheory.integral_compProd hz]
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun i ↦ by rfl
          change (∫ z : Fin k × ℝ, |z.2 - banditArmMean ν z.1|
            ∂(banditStepKernel ν π n h)) ≤ C
          rw [hcond]
          calc
            (∫ i : Fin k, moment i ∂(π.select n h)) ≤
                ∫ _i : Fin k, C ∂(π.select n h) := by
              apply integral_mono_ae Integrable.of_finite (integrable_const _)
              exact Filter.Eventually.of_forall fun i ↦ by
                dsimp [C]
                apply Finset.single_le_sum
                · intro j hj
                  dsimp [moment]
                  exact integral_nonneg_of_ae
                    (Filter.Eventually.of_forall fun y ↦ abs_nonneg _)
                · simp
            _ = C := by simp

theorem BanditAlgorithm.expected_centered_sum_zero_test {k : ℕ} (ν : StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditPolicy k) (n : ℕ) :
    Integrable (fun h : BanditHistory k n ↦
      ∑ t, ((h t).2 - banditArmMean ν (h t).1)) (banditMeasure ν π n) ∧
    ∫ h, (∑ t, ((h t).2 - banditArmMean ν (h t).1))
      ∂(banditMeasure ν π n) = 0 := by
  let centered : (m : ℕ) → BanditHistory k m → ℝ :=
    fun m h ↦ ∑ t, ((h t).2 - banditArmMean ν (h t).1)
  have centered_measurable : ∀ m : ℕ, Measurable (centered m) := by
    intro m
    dsimp [centered]
    apply Finset.measurable_sum
    intro t ht
    exact (measurable_snd.comp (measurable_pi_apply t)).sub
      ((measurable_of_countable (banditArmMean ν)).comp
        (measurable_fst.comp (measurable_pi_apply t)))
  have hmain : ∀ m : ℕ,
      Integrable (centered m) (banditMeasure ν π m) ∧
        ∫ h, centered m h ∂(banditMeasure ν π m) = 0 := by
    intro m
    induction m with
    | zero => simp [centered]
    | succ m ihm =>
        let μ := banditMeasure ν π m
        let κ := banditStepKernel ν π m
        let snoc : BanditHistory k m × (Fin k × ℝ) → BanditHistory k (m + 1) :=
          fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2
        have hsnoc : Measurable snoc := measurable_banditHistorySnoc
        have hrewrite : (fun p ↦ centered (m + 1) (snoc p)) =
            fun p ↦ centered m p.1 + (p.2.2 - banditArmMean ν p.2.1) := by
          funext p
          simp [centered, snoc, Fin.sum_univ_castSucc]
          ring
        have hold : Integrable
            (fun p : BanditHistory k m × (Fin k × ℝ) ↦ centered m p.1)
            (μ.compProd κ) := by
          have hi : Integrable (centered m) (Measure.map Prod.fst (μ.compProd κ)) := by
            change Integrable (centered m) ((μ.compProd κ).fst)
            rw [Measure.fst_compProd]
            exact ihm.1
          exact hi.comp_aemeasurable measurable_fst.aemeasurable
        have hnew : Integrable
            (fun p : BanditHistory k m × (Fin k × ℝ) ↦
              p.2.2 - banditArmMean ν p.2.1) (μ.compProd κ) :=
          joint_centered_step_integrable_test ν hInt π m
        have hsum := hold.add hnew
        have hcomp : Integrable (centered (m + 1) ∘ snoc) (μ.compProd κ) := by
          change Integrable (fun p ↦ centered (m + 1) (snoc p)) (μ.compProd κ)
          rw [hrewrite]
          exact hsum
        constructor
        · rw [banditMeasure]
          apply (integrable_map_measure (centered_measurable (m + 1)).aestronglyMeasurable
            hsnoc.aemeasurable).2
          exact hcomp
        · rw [banditMeasure,
            integral_map hsnoc.aemeasurable (centered_measurable (m + 1)).aestronglyMeasurable]
          change (∫ p, centered (m + 1) (snoc p) ∂(μ.compProd κ)) = 0
          rw [hrewrite]
          rw [integral_add hold hnew]
          rw [Measure.integral_compProd hold, Measure.integral_compProd hnew]
          simp [μ, κ, ihm.2, stepKernel_integral_centered_test ν hInt π m]
  exact hmain n


end BanditAlgorithm






set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm

section LinUCBProof
open LinUCBProof

lemma LinUCBProof.measurable_historyGapSum {k d n : Nat} (hk : 0 < k)
    (arms : Fin k → Fin d → Real) (theta : Fin d → Real) :
    Measurable (historyGapSum (n := n) hk arms theta) := by
  unfold historyGapSum
  apply Finset.measurable_sum
  intro t ht
  exact (measurable_of_countable (fun j : Fin k =>
    (arms (bestArm hk arms theta) - arms j) ⬝ᵥ theta)).comp
      (measurable_pi_apply t).fst

lemma LinUCBProof.integrable_historyGapSum {k d n : Nat} (hk : 0 < k)
    (arms : Fin k → Fin d → Real) (theta : Fin d → Real)
    (hgap : ∀ i j, theta ⬝ᵥ (arms i - arms j) ≤ 1)
    (nu : StochasticBandit k) (pi : BanditPolicy k) :
    Integrable (historyGapSum (n := n) hk arms theta) (banditMeasure nu pi n) := by
  apply Integrable.of_mem_Icc (0 : Real) n
  · exact (measurable_historyGapSum hk arms theta).aemeasurable
  · exact Filter.Eventually.of_forall fun h => historyGapSum_bounds hk arms theta h hgap

lemma LinUCBProof.optimalMean_eq_best {k d : Nat} (hk : 0 < k)
    (arms : Fin k → Fin d → Real) (theta : Fin d → Real) (nu : StochasticBandit k)
    (hnu : IsLinearBandit arms theta nu) :
    banditOptimalMean nu = arms (bestArm hk arms theta) ⬝ᵥ theta := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  unfold banditOptimalMean
  apply le_antisymm
  · apply ciSup_le
    intro j
    rw [hnu.1 j]
    exact chooseArm_max hk (fun i => arms i ⬝ᵥ theta) j
  · rw [← hnu.1 (bestArm hk arms theta)]
    exact le_ciSup (Finite.bddAbove_range _) _

lemma LinUCBProof.expected_regret_eq_gapSum {k d n : Nat} (hk : 0 < k)
    (arms : Fin k → Fin d → Real) (theta : Fin d → Real)
    (hgap : ∀ i j, theta ⬝ᵥ (arms i - arms j) ≤ 1)
    (nu : StochasticBandit k) (hnu : IsLinearBandit arms theta nu) (pi : BanditPolicy k) :
    banditRegret nu pi n = ∫ h, historyGapSum hk arms theta h ∂banditMeasure nu pi n := by
  have hg := integrable_historyGapSum (n := n) hk arms theta hgap nu pi
  have hc := expected_centered_sum_zero_test nu hnu.2.1 pi n
  have heq (h : BanditHistory k n) :
      (∑ t : Fin n, (h t).2) =
        ((n : Real) * (arms (bestArm hk arms theta) ⬝ᵥ theta) -
          historyGapSum hk arms theta h) +
          ∑ t : Fin n, ((h t).2 - banditArmMean nu (h t).1) := by
    simp only [historyGapSum, sub_dotProduct, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp_rw [hnu.1]
    ring
  unfold banditRegret
  rw [optimalMean_eq_best hk arms theta nu hnu]
  simp_rw [heq]
  have hadd := integral_add
    ((integrable_const ((n : Real) * (arms (bestArm hk arms theta) ⬝ᵥ theta))).sub hg) hc.1
  simp only [Pi.sub_apply] at hadd
  rw [hadd, integral_sub (integrable_const _) hg, hc.2]
  simp

lemma LinUCBProof.expected_gap_bound {k d n : Nat} (hk : 0 < k)
    (arms : Fin k → Fin d → Real) (theta : Fin d → Real)
    (hgap : ∀ i j, theta ⬝ᵥ (arms i - arms j) ≤ 1)
    (nu : StochasticBandit k) (pi : BanditPolicy k) (hn : 0 < n)
    {bad : Set (BanditHistory k n)} {R : Real} (hR : 0 ≤ R)
    (hbad : banditMeasure nu pi n bad ≤ ENNReal.ofReal (1 / n))
    (hgood : ∀ᵐ h ∂banditMeasure nu pi n,
      h ∉ bad → historyGapSum hk arms theta h ≤ R) :
    (∫ h, historyGapSum hk arms theta h ∂banditMeasure nu pi n) ≤ R + 1 := by
  let mu := banditMeasure nu pi n
  let B := toMeasurable mu bad
  have hB : MeasurableSet B := measurableSet_toMeasurable mu bad
  have hsub : bad ⊆ B := subset_toMeasurable mu bad
  have hmeasure : mu B ≤ ENNReal.ofReal (1 / n) := by
    simpa only [B, measure_toMeasurable] using hbad
  let upper : BanditHistory k n → Real := fun h =>
    R + (n : Real) * B.indicator (fun _ => 1) h
  have hupper : Integrable upper mu :=
    (integrable_const R).add ((integrable_const (1 : Real)).indicator hB |>.const_mul n)
  have hbound : ∀ᵐ h ∂mu, historyGapSum hk arms theta h ≤ upper h := by
    filter_upwards [hgood] with h hh
    by_cases hb : h ∈ B
    · have hn' := (historyGapSum_bounds hk arms theta h hgap).2
      simp only [upper, Set.indicator_of_mem hb, Pi.one_apply, mul_one]
      linarith
    · have hnot : h ∉ bad := fun hbad' => hb (hsub hbad')
      simpa only [upper, Set.indicator_of_notMem hb, mul_zero, add_zero] using hh hnot
  have hint := integral_mono_ae
    (integrable_historyGapSum hk arms theta hgap nu pi) hupper hbound
  have hnR : (0 : Real) < n := Nat.cast_pos.mpr hn
  have hreal : mu.real B ≤ 1 / n := by
    have hm := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
    simpa only [Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 : Real) / n)]
      using hm
  calc
    _ ≤ ∫ h, upper h ∂mu := hint
    _ = R + (n : Real) * mu.real B := by
      dsimp only [upper]
      rw [integral_add (integrable_const R)
        ((integrable_const (1 : Real)).indicator hB |>.const_mul n), integral_const_mul]
      simp [integral_indicator_const, hB]
    _ ≤ R + (n : Real) * (1 / n) := by gcongr
    _ = R + 1 := by field_simp

end LinUCBProof






set_option autoImplicit false

open Matrix MeasureTheory ProbabilityTheory BanditAlgorithm LinUCBProof

theorem solution :
    ∃ C : Real, 0 < C ∧
      ∀ (d k n : Nat) (L : Real), 0 < d → 0 < k → 2 ≤ n → 1 ≤ L →
        ∀ arms : Fin k → Fin d → Real,
          (∀ j, Real.sqrt (arms j ⬝ᵥ arms j) ≤ L) →
          ∃ pi : BanditPolicy k,
            ∀ (theta : Fin d → Real) (nu : StochasticBandit k),
              IsLinearBandit arms theta nu →
              Real.sqrt (theta ⬝ᵥ theta) ≤ 1 →
              (∀ i j : Fin k, theta ⬝ᵥ (arms i - arms j) ≤ 1) →
              banditRegret nu pi n ≤
                C * d * Real.sqrt n * Real.log (n * L) := by
  refine ⟨18, by norm_num, ?_⟩
  intro d k n L hd hk hn hL arms harms
  let B : Real := d * Real.log ((d + n * L ^ 2) / d)
  let beta : Real := (1 + Real.sqrt (4 * Real.log n + B)) ^ 2
  have hbudget := logarithmic_budget (d : Real) n L
    (by exact_mod_cast hd) (by exact_mod_cast hn) hL
  change 1 ≤ beta ∧ Real.sqrt (8 * n * beta * B) + 1 ≤
    18 * d * Real.sqrt n * Real.log (n * L) at hbudget
  refine ⟨indexPolicy hk arms beta, ?_⟩
  intro theta nu hnu htheta hgap
  have hfail := failureSet_measure_le arms theta nu hnu (indexPolicy hk arms beta) n hn
  have hsupport := indexPolicy_support hk arms beta nu n
  have hgood : ∀ᵐ h ∂banditMeasure nu (indexPolicy hk arms beta) n,
      h ∉ failureSet arms theta n →
        historyGapSum hk arms theta h ≤ Real.sqrt (8 * n * beta * B) := by
    filter_upwards [hsupport] with h hselect
    intro hnot
    apply history_regret_bound hd hk arms theta h harms hbudget.1 hgap hselect
    intro t
    have hstat : statistic arms theta (historyPrefix (Nat.le_of_lt t.isLt) h) <
        4 * Real.log n := by
      apply lt_of_not_ge
      intro hge
      exact hnot ⟨t, hge⟩
    exact finite_confidence hd hn arms theta
      (historyPrefix (Nat.le_of_lt t.isLt) h) harms htheta
      (Nat.le_of_lt t.isLt) hstat
  rw [expected_regret_eq_gapSum hk arms theta hgap nu hnu]
  exact (expected_gap_bound hk arms theta hgap nu (indexPolicy hk arms beta)
    (by omega) (Real.sqrt_nonneg _) hfail hgood).trans hbudget.2

