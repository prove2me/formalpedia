-- Prove2me | solution 2 for GaussianMatrix.inverse_wishart_spectral_moment
-- status  : ACCEPTED   (prove)
-- author  : @ShouqiaoWang
-- created : 2026-10-30T13:17:07.193953+00:00
-- url     : https://prove2.me/submissions/2c83627d-6f52-4a47-9e0f-14330a988a83

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_block_law
import Theorems.Thm_GaussianMatrix_rotation_invariance
import Theorems.Thm_GaussianMatrix_inverse_wishart_diag_law
import Theorems.Thm_GaussianMatrix_chi_square_neg_moment

-- Local proof component: MomentTools

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
open Real Set

/-- The product of `m` standard Gaussians has density `∏ᵢ φ(xᵢ)` w.r.t. Lebesgue measure. -/
lemma r1_pi_gauss (m : ℕ) :
    Measure.pi (fun _ : Fin m => gaussianReal 0 1)
      = volume.withDensity
          (fun x : Fin m → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  refine Measure.pi_eq (μ := fun _ : Fin m => gaussianReal 0 1) fun s hs => ?_
  have hS : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hS, ← lintegral_indicator hS]
  have hind : ∀ x : Fin m → ℝ,
      (Set.univ.pi s).indicator (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) x
        = ENNReal.ofReal (∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)]
      simp
  simp_rw [hind]
  have hint : Integrable (fun x : Fin m → ℝ => ∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i))
      volume := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun i => (s i).indicator (gaussianPDFReal 0 1))
      (fun i => (integrable_gaussianPDFReal 0 1).indicator (hs i))
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun x => Finset.prod_nonneg fun i _ =>
      Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _)]
  rw [integral_fintype_prod_volume_eq_prod, ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg fun y =>
      Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero, integral_indicator (hs i)]

lemma r1_prod_pdf {m : ℕ} (x : Fin m → ℝ) :
    ∏ i, gaussianPDFReal 0 1 (x i)
      = (Real.sqrt (2 * π))⁻¹ ^ m * Real.exp (-(∑ i, x i ^ 2) / 2) := by
  simp only [gaussianPDFReal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum]
  congr 2
  · simp
  · simp only [sub_zero, NNReal.coe_one, mul_one, neg_div]
    rw [Finset.sum_neg_distrib, Finset.sum_div]

lemma r1_sum_sq_ofLp {m : ℕ} (y : EuclideanSpace ℝ (Fin m)) :
    ∑ i, (WithLp.ofLp y) i ^ 2 = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

/-- Polar coordinates for a radial function of a standard Gaussian vector. -/
lemma r1_radial (m : ℕ) (hm : 1 ≤ m) (φ : ℝ → ℝ) :
    ∫ x, φ (Real.sqrt (∑ i, x i ^ 2)) ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = m * (volume : Measure (EuclideanSpace ℝ (Fin m))).real (Metric.ball 0 1)
        * ((Real.sqrt (2 * π))⁻¹ ^ m
          * ∫ y in Ioi (0 : ℝ), y ^ (m - 1) * (Real.exp (-y ^ 2 / 2) * φ y)) := by
  rw [r1_pi_gauss, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _),
    smul_eq_mul, r1_prod_pdf]
  rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).integral_comp']
  simp only [MeasurableEquiv.toLp_symm_apply]
  simp_rw [r1_sum_sq_ofLp, Real.sqrt_sq (norm_nonneg _)]
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : Nontrivial (EuclideanSpace ℝ (Fin m)) := inferInstance
  have := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin m)))
    (fun r => (Real.sqrt (2 * π))⁻¹ ^ m * Real.exp (-r ^ 2 / 2) * φ r)
  rw [this, finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul]
  simp_rw [smul_eq_mul]
  have e : ∀ y : ℝ, y ^ (m - 1) * ((Real.sqrt (2 * π))⁻¹ ^ m * Real.exp (-y ^ 2 / 2) * φ y)
      = (Real.sqrt (2 * π))⁻¹ ^ m * (y ^ (m - 1) * (Real.exp (-y ^ 2 / 2) * φ y)) := fun y => by
    ring
  simp_rw [e]
  rw [integral_const_mul]
  ring


lemma gm_radial_power_integral {d : ℕ} (hd : 1 ≤ d) (q : ℝ) (hq : 0 ≤ q) :
    ∫ x : Fin d → ℝ, (∑ i, x i ^ 2) ^ q ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      = 2 ^ q * Real.Gamma ((d : ℝ) / 2 + q) / Real.Gamma ((d : ℝ) / 2) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd]; norm_num
  let C : ℝ := d * (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball 0 1)
      * (Real.sqrt (2 * π))⁻¹ ^ d
  have eval (a : ℝ) (ha : 0 ≤ a) :
      (∫ y in Ioi (0 : ℝ), y ^ (d - 1) * (Real.exp (-y ^ 2 / 2) * y ^ (2 * a)))
        = 2 ^ ((d : ℝ) / 2 + a) / 2 * Real.Gamma ((d : ℝ) / 2 + a) := by
    have he := integral_rpow_mul_exp_neg_mul_rpow (p := 2)
      (q := (d : ℝ) - 1 + 2 * a) (b := 1 / 2)
      (by norm_num) (by linarith) (by norm_num)
    calc
      _ = ∫ y in Ioi (0 : ℝ), y ^ ((d : ℝ) - 1 + 2 * a) *
          Real.exp (-(1 / 2 : ℝ) * y ^ (2 : ℝ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        have hy0 : 0 < y := hy
        dsimp only
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
          Real.rpow_add hy0, ← hcast, Real.rpow_natCast]
        norm_num only [Nat.cast_ofNat, Real.rpow_two]
        ring_nf
      _ = _ := by
        rw [he]
        have heq : ((d : ℝ) - 1 + 2 * a + 1) / 2 = (d : ℝ) / 2 + a := by ring
        rw [heq]
        have hpow : (1 / 2 : ℝ) ^ (-((d : ℝ) - 1 + 2 * a + 1) / 2) =
            2 ^ ((d : ℝ) / 2 + a) := by
          rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
          congr 1; ring
        rw [hpow]
        ring
  have hnorm := r1_radial d hd (fun _ => (1 : ℝ))
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one] at hnorm
  have hzero := eval 0 (le_refl 0)
  simp only [mul_zero, Real.rpow_zero, mul_one, add_zero] at hzero
  rw [hzero] at hnorm
  have hnorm' : C * (2 ^ ((d : ℝ) / 2) / 2 * Real.Gamma ((d : ℝ) / 2)) = 1 := by
    dsimp [C]; nlinarith [hnorm]
  have hrad := r1_radial d hd (fun y => y ^ (2 * q))
  have hsimp (x : Fin d → ℝ) : (Real.sqrt (∑ i, x i ^ 2)) ^ (2 * q) = (∑ i, x i ^ 2) ^ q := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    congr 1; ring
  simp_rw [hsimp] at hrad
  rw [eval q hq] at hrad
  rw [hrad]
  have hg : Real.Gamma ((d : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hp : (2 : ℝ) ^ ((d : ℝ) / 2) ≠ 0 := by positivity
  rw [Real.rpow_add (by norm_num)]
  dsimp [C] at hnorm'
  field_simp
  convert congrArg (fun x : ℝ => 2 * x) hnorm' using 1 <;> ring

lemma gm_radial_power_integrable {d : ℕ} (hd : 1 ≤ d) (q : ℝ) (hq : 0 ≤ q) :
    Integrable (fun x : Fin d → ℝ => (∑ i, x i ^ 2) ^ q)
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
  apply Integrable.of_integral_ne_zero
  rw [gm_radial_power_integral hd q hq]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 := Real.Gamma_pos_of_pos (show 0 < (d : ℝ) / 2 + q by linarith)
  have h2 := Real.Gamma_pos_of_pos (show 0 < (d : ℝ) / 2 by positivity)
  positivity

lemma gm_radial_power_lintegral {d : ℕ} (hd : 1 ≤ d) (q : ℝ) (hq : 0 ≤ q) :
    ∫⁻ x : Fin d → ℝ, ENNReal.ofReal ((∑ i, x i ^ 2) ^ q)
      ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      = ENNReal.ofReal (2 ^ q * Real.Gamma ((d : ℝ) / 2 + q) / Real.Gamma ((d : ℝ) / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gm_radial_power_integrable hd q hq),
    gm_radial_power_integral hd q hq]
  exact Filter.Eventually.of_forall fun x => Real.rpow_nonneg
    (Finset.sum_nonneg fun i _ => sq_nonneg _) _

end GaussianMatrix

-- Local proof component: QuadraticMoments

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
open scoped Matrix.Norms.L2Operator
open Matrix

/-- A standard Gaussian vector mapped by `Vᵀ`, with `V` having orthonormal columns, is a
standard Gaussian vector (the case `t = 1` of `block_law`, reshaped). -/
lemma rl_vec_law {m d : ℕ} (V : Matrix (Fin m) (Fin d) ℝ) (hV : Vᵀ * V = 1) :
    Measure.map (fun g : Fin m → ℝ => Vᵀ *ᵥ g) (Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
  -- column-vector embedding and its inverse
  have hι : ∀ p : ℕ, MeasurePreserving
      (fun (g : Fin p → ℝ) (a : Fin p) => (MeasurableEquiv.funUnique (Fin 1) ℝ).symm (g a))
      (Measure.pi fun _ : Fin p => gaussianReal 0 1) (gaussianMatrix p 1) := fun p =>
    measurePreserving_pi _ _ fun _ => (measurePreserving_funUnique (gaussianReal 0 1) (Fin 1)).symm
  have hev : ∀ p : ℕ, MeasurePreserving
      (fun (G : Fin p → Fin 1 → ℝ) (a : Fin p) => MeasurableEquiv.funUnique (Fin 1) ℝ (G a))
      (gaussianMatrix p 1) (Measure.pi fun _ : Fin p => gaussianReal 0 1) := fun p =>
    measurePreserving_pi _ _ fun _ => measurePreserving_funUnique (gaussianReal 0 1) (Fin 1)
  have hB := block_law (t := 1) V hV
  have hFm : Measurable (fun G : Fin m → Fin 1 → ℝ => Matrix.of.symm (Vᵀ * Matrix.of G)) := by
    refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hfun : (fun g : Fin m → ℝ => Vᵀ *ᵥ g) =
      (fun (G : Fin d → Fin 1 → ℝ) (a : Fin d) => MeasurableEquiv.funUnique (Fin 1) ℝ (G a)) ∘
      (fun G : Fin m → Fin 1 → ℝ => Matrix.of.symm (Vᵀ * Matrix.of G)) ∘
      (fun (g : Fin m → ℝ) (a : Fin m) => (MeasurableEquiv.funUnique (Fin 1) ℝ).symm (g a)) := by
    funext g a
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, MeasurableEquiv.funUnique]
  rw [hfun, ← Measure.map_map (hev d).measurable (hFm.comp (hι m).measurable),
    ← Measure.map_map hFm (hι m).measurable, (hι m).map_eq, hB, (hev d).map_eq]

lemma gm_quad_transform {r : ℕ} (U A : Matrix (Fin r) (Fin r) ℝ) (z : Fin r → ℝ) :
    (U *ᵥ z) ⬝ᵥ (A *ᵥ (U *ᵥ z)) = z ⬝ᵥ ((Uᵀ * A * U) *ᵥ z) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm]

lemma gm_norm_eq_max_eigenvalue {r : ℕ} (hr : 1 ≤ r)
    (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosSemidef) :
    ∃ i : Fin r, specNorm A = hA.isHermitian.eigenvalues i := by
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ hA.isHermitian.eigenvalues
    Finset.univ_nonempty
  refine ⟨i, ?_⟩
  have hn : specNorm A = ‖hA.isHermitian.eigenvalues‖ := by
    unfold specNorm
    conv_lhs => rw [hA.isHermitian.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      l2_opNorm_diagonal, RCLike.ofReal_real_eq_id, Function.id_comp]
  rw [hn]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (hA.eigenvalues_nonneg i)).2
    intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg j)]
    exact hi j (Finset.mem_univ j)
  · have := norm_le_pi_norm hA.isHermitian.eigenvalues i
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)] using this

lemma gm_coordinate_moment {r : ℕ} (i : Fin r) (q : ℝ) (hq : 0 ≤ q) :
    ∫⁻ z : Fin r → ℝ, ENNReal.ofReal ((z i ^ 2) ^ q)
      ∂(Measure.pi fun _ : Fin r => gaussianReal 0 1)
      = ENNReal.ofReal (2 ^ q * Real.Gamma (1 / 2 + q) / Real.Gamma (1 / 2)) := by
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal ((x ^ 2) ^ q)) := by fun_prop
  rw [(measurePreserving_eval (fun _ : Fin r => gaussianReal 0 1) i).lintegral_comp hm]
  have h := (measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) 0).lintegral_comp hm
  rw [← h]
  simpa using gm_radial_power_lintegral (d := 1) (by omega) q hq

lemma gm_quad_moment_lower {r : ℕ} (hr : 1 ≤ r)
    (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosSemidef) (q : ℝ) (hq : 0 ≤ q) :
    ENNReal.ofReal (specNorm A ^ q) *
      ENNReal.ofReal (2 ^ q * Real.Gamma (1 / 2 + q) / Real.Gamma (1 / 2))
      ≤ ∫⁻ z : Fin r → ℝ, ENNReal.ofReal ((z ⬝ᵥ (A *ᵥ z)) ^ q)
        ∂(Measure.pi fun _ : Fin r => gaussianReal 0 1) := by
  obtain ⟨i, hi⟩ := gm_norm_eq_max_eigenvalue hr A hA
  let U : Matrix (Fin r) (Fin r) ℝ := hA.isHermitian.eigenvectorUnitary
  have hU : Uᵀ * U = 1 := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hU' : U * Uᵀ = 1 := (mul_eq_one_comm).mp hU
  have hdiag : Uᵀ * A * U = Matrix.diagonal hA.isHermitian.eigenvalues := by
    simpa only [Unitary.conjStarAlgAut_star_apply, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, Function.id_comp]
      using hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hm : Measurable (fun z : Fin r → ℝ => ENNReal.ofReal ((z ⬝ᵥ (A *ᵥ z)) ^ q)) := by
    fun_prop
  have hmp : MeasurePreserving (fun z : Fin r → ℝ => U *ᵥ z)
      (Measure.pi fun _ : Fin r => gaussianReal 0 1)
      (Measure.pi fun _ : Fin r => gaussianReal 0 1) := by
    refine ⟨by fun_prop, ?_⟩
    simpa using rl_vec_law Uᵀ (by simpa using hU')
  rw [← hmp.lintegral_comp hm]
  have heq (z : Fin r → ℝ) : (U *ᵥ z) ⬝ᵥ (A *ᵥ (U *ᵥ z)) =
      ∑ j, hA.isHermitian.eigenvalues j * z j ^ 2 := by
    rw [gm_quad_transform, hdiag]
    simp only [mulVec_diagonal, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [heq]
  rw [← gm_coordinate_moment i q hq, ← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_mono
  intro z
  dsimp only
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (show 0 ≤ specNorm A from norm_nonneg A) q), hi,
    ← Real.mul_rpow (hA.eigenvalues_nonneg i) (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow (mul_nonneg (hA.eigenvalues_nonneg i) (sq_nonneg _)) _ hq
  exact Finset.single_le_sum (fun j _ => mul_nonneg (hA.eigenvalues_nonneg j) (sq_nonneg _))
    (Finset.mem_univ i)

end GaussianMatrix

-- Local proof component: InverseQuadratic

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix
namespace GaussianMatrix

lemma gm_exists_orthogonal {r : ℕ} (i : Fin r) (v : Fin r → ℝ)
    (hv : ‖WithLp.toLp 2 v‖ = 1) :
    ∃ U : Matrix (Fin r) (Fin r) ℝ, Uᵀ * U = 1 ∧ U *ᵥ Pi.single i 1 = v := by
  let b := EuclideanSpace.basisFun (Fin r) ℝ
  let f := (ℝ ∙ (b i - WithLp.toLp 2 v))ᗮ.reflection
  have hf : f (b i) = WithLp.toLp 2 v := by
    apply Submodule.reflection_sub
    rw [b.orthonormal.1 i, hv]
  let U : Matrix (Fin r) (Fin r) ℝ := b.toBasis.toMatrix (b.map f)
  refine ⟨U, ?_, ?_⟩
  · have := b.toMatrix_orthonormalBasis_mem_unitary (b.map f)
    simpa only [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] using this
  · ext j
    simp only [mulVec_single_one, Matrix.col_apply, U, Module.Basis.toMatrix_apply, OrthonormalBasis.map_apply,
      hf, b]
    rfl

lemma gm_inv_gram_rotate {r k : ℕ} (U : Matrix (Fin r) (Fin r) ℝ)
    (hU : Uᵀ * U = 1) (G : Matrix (Fin r) (Fin k) ℝ) :
    ((Uᵀ * G) * (Uᵀ * G)ᵀ)⁻¹ = Uᵀ * (G * Gᵀ)⁻¹ * U := by
  have hU' : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hi : U⁻¹ = Uᵀ := inv_eq_left_inv hU
  have hit : Uᵀ⁻¹ = U := inv_eq_left_inv hU'
  rw [transpose_mul, transpose_transpose]
  rw [show Uᵀ * G * (Gᵀ * U) = Uᵀ * (G * Gᵀ) * U by simp [Matrix.mul_assoc]]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hi, hit, Matrix.mul_assoc]
lemma iwdl_measurable_inv_entry {r k : ℕ} (i j : Fin r) :
    Measurable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j) := by
  have hc : Continuous (fun G : Fin r → Fin k → ℝ => Matrix.of G * (Matrix.of G)ᵀ) :=
    Continuous.matrix_mul continuous_id (Continuous.matrix_transpose continuous_id)
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (hc.matrix_det.measurable.inv).mul (hc.matrix_adjugate.matrix_elem i j).measurable

lemma gm_inv_diag_lintegral {r k : ℕ} (hrk : r ≤ k) (i : Fin r)
    (q : ℝ) (hq : 0 ≤ q) (hqd : q < (k - r + 1 : ℕ) / (2 : ℝ)) :
    ∫⁻ G : Fin r → Fin k → ℝ,
      ENNReal.ofReal (((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i) ^ q) ∂gaussianMatrix r k
      = ENNReal.ofReal (Real.Gamma ((k - r + 1 : ℕ) / (2 : ℝ) - q) /
        (2 ^ q * Real.Gamma ((k - r + 1 : ℕ) / (2 : ℝ)))) := by
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ q)) := by fun_prop
  rw [← lintegral_map hm (iwdl_measurable_inv_entry i i), inverse_wishart_diag_law hrk i,
    lintegral_map hm (by fun_prop)]
  have hn := chi_square_neg_moment (d := k - r + 1) q hq hqd
  rw [← ofReal_integral_eq_lintegral_ofReal hn.1, hn.2]
  exact Filter.Eventually.of_forall fun x => Real.rpow_nonneg
    (inv_nonneg.mpr (Finset.sum_nonneg fun j _ => sq_nonneg _)) _

lemma gm_inv_unit_quad_lintegral {r k : ℕ} (hrk : r ≤ k) (i : Fin r)
    (v : Fin r → ℝ) (hv : ‖WithLp.toLp 2 v‖ = 1)
    (q : ℝ) (hq : 0 ≤ q) (hqd : q < (k - r + 1 : ℕ) / (2 : ℝ)) :
    ∫⁻ G : Fin r → Fin k → ℝ,
      ENNReal.ofReal ((v ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ v)) ^ q) ∂gaussianMatrix r k
      = ENNReal.ofReal (Real.Gamma ((k - r + 1 : ℕ) / (2 : ℝ) - q) /
        (2 ^ q * Real.Gamma ((k - r + 1 : ℕ) / (2 : ℝ)))) := by
  obtain ⟨U, hU, hUv⟩ := gm_exists_orthogonal i v hv
  let R : (Fin r → Fin k → ℝ) → (Fin r → Fin k → ℝ) := fun G => Matrix.of.symm (Uᵀ * Matrix.of G)
  have hmp : MeasurePreserving R (gaussianMatrix r k) (gaussianMatrix r k) := by
    refine ⟨by
      dsimp [R]
      refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
      simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
      fun_prop, ?_⟩
    simpa [R] using rotation_invariance Uᵀ (1 : Matrix (Fin k) (Fin k) ℝ)
      (by simpa using mul_eq_one_comm.mp hU) (by simp)
  have heq (G : Fin r → Fin k → ℝ) :
      v ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ v) =
        (Matrix.of (R G) * (Matrix.of (R G))ᵀ)⁻¹ i i := by
    change v ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ v) =
      ((Uᵀ * Matrix.of G) * (Uᵀ * Matrix.of G)ᵀ)⁻¹ i i
    rw [gm_inv_gram_rotate U hU, ← hUv, gm_quad_transform]
    simp [dotProduct, mulVec, Pi.single_apply]
  simp_rw [heq]
  rw [hmp.lintegral_comp ((iwdl_measurable_inv_entry i i).pow_const q |>.ennreal_ofReal),
    gm_inv_diag_lintegral hrk i q hq hqd]
lemma gm_inv_quad_lintegral {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k)
    (v : Fin r → ℝ) (q : ℝ) (hq : 0 < q) (hqd : q < (k - r + 1 : ℕ) / (2 : ℝ)) :
    ∫⁻ G : Fin r → Fin k → ℝ,
      ENNReal.ofReal ((v ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ v)) ^ q) ∂gaussianMatrix r k
      = ENNReal.ofReal ((∑ i, v i ^ 2) ^ q) *
        ENNReal.ofReal (Real.Gamma ((k - r + 1 : ℕ) / (2 : ℝ) - q) /
          (2 ^ q * Real.Gamma ((k - r + 1 : ℕ) / (2 : ℝ)))) := by
  by_cases hv0 : v = 0
  · subst v
    simp [Real.zero_rpow hq.ne']
  let c : ℝ := ‖WithLp.toLp 2 v‖
  have hc : 0 < c := norm_pos_iff.mpr (by simpa using hv0)
  let w : Fin r → ℝ := c⁻¹ • v
  have hw : ‖WithLp.toLp 2 w‖ = 1 := by
    change ‖c⁻¹ • (WithLp.toLp 2 v)‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    exact inv_mul_cancel₀ hc.ne'
  have hv : v = c • w := by
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hc2 : c ^ 2 = ∑ i, v i ^ 2 := (r1_sum_sq_ofLp (WithLp.toLp 2 v)).symm
  have heq (G : Fin r → Fin k → ℝ) :
      ENNReal.ofReal ((v ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ v)) ^ q) =
        ENNReal.ofReal ((∑ i, v i ^ 2) ^ q) *
          ENNReal.ofReal ((w ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ w)) ^ q) := by
    have hM : (Matrix.of G * (Matrix.of G)ᵀ)⁻¹.PosSemidef := by
      apply Matrix.PosSemidef.inv
      simpa only [conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_self_mul_conjTranspose (Matrix.of G)
    have hn : 0 ≤ w ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ w) := by
      simpa using hM.dotProduct_mulVec_nonneg w
    conv_lhs => rw [hv, mulVec_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]
    rw [show c * (c * (w ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ w))) =
      c ^ 2 * (w ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ w)) by ring,
      Real.mul_rpow (sq_nonneg c) hn, hc2,
      ENNReal.ofReal_mul (Real.rpow_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) q)]
  simp_rw [heq]
  rw [lintegral_const_mul _ (by
    apply Measurable.ennreal_ofReal
    apply Measurable.pow_const
    simp only [dotProduct, mulVec]
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul
      (Finset.measurable_sum _ fun j _ => (iwdl_measurable_inv_entry i j).mul_const _)),
    gm_inv_unit_quad_lintegral hrk ⟨0, hr⟩ w hw q hq.le hqd]

end GaussianMatrix

-- Local proof component: SpectralMomentBound

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator
namespace GaussianMatrix

lemma gm_measurable_spec_inv {r k : ℕ} :
    Measurable (fun G : Fin r → Fin k → ℝ => specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹) := by
  have h1 : Measurable (fun G : Fin r → Fin k → ℝ =>
      Matrix.of.symm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹) := by
    refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    exact iwdl_measurable_inv_entry a b
  have h2 : Continuous (fun M : Fin r → Fin r → ℝ => specNorm (Matrix.of M)) :=
    continuous_norm.comp continuous_id
  exact h2.measurable.comp h1

lemma gm_spec_weighted_lintegral {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k)
    (q : ℝ) (hq : 0 < q) (hqd : q < (k - r + 1 : ℕ) / (2 : ℝ)) :
    (∫⁻ G : Fin r → Fin k → ℝ,
      ENNReal.ofReal (specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ q) ∂gaussianMatrix r k) *
        ENNReal.ofReal (2 ^ q * Real.Gamma (1 / 2 + q) / Real.Gamma (1 / 2))
      ≤ ENNReal.ofReal (2 ^ q * Real.Gamma ((r : ℝ) / 2 + q) / Real.Gamma ((r : ℝ) / 2)) *
        ENNReal.ofReal (Real.Gamma ((k - r + 1 : ℕ) / (2 : ℝ) - q) /
          (2 ^ q * Real.Gamma ((k - r + 1 : ℕ) / (2 : ℝ)))) := by
  have hm : Measurable (fun z : (Fin r → Fin k → ℝ) × (Fin r → ℝ) =>
      ENNReal.ofReal ((z.2 ⬝ᵥ ((Matrix.of z.1 * (Matrix.of z.1)ᵀ)⁻¹ *ᵥ z.2)) ^ q)) := by
    apply Measurable.ennreal_ofReal
    apply Measurable.pow_const
    simp only [dotProduct, Matrix.mulVec]
    apply Finset.measurable_sum
    intro i _
    apply Measurable.mul (by fun_prop)
    apply Finset.measurable_sum
    intro j _
    exact ((iwdl_measurable_inv_entry i j).comp measurable_fst).mul (by fun_prop)
  rw [← lintegral_mul_const _ (gm_measurable_spec_inv.pow_const q |>.ennreal_ofReal)]
  calc
    _ ≤ ∫⁻ G : Fin r → Fin k → ℝ, ∫⁻ z : Fin r → ℝ,
        ENNReal.ofReal ((z ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ z)) ^ q)
        ∂(Measure.pi fun _ : Fin r => gaussianReal 0 1) ∂gaussianMatrix r k := by
      apply lintegral_mono
      intro G
      apply gm_quad_moment_lower hr _ _ q hq.le
      apply Matrix.PosSemidef.inv
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_self_mul_conjTranspose (Matrix.of G)
    _ = _ := by
      rw [lintegral_lintegral_swap hm.aemeasurable]
      simp_rw [gm_inv_quad_lintegral hr hrk _ q hq hqd]
      rw [lintegral_mul_const _ (by fun_prop), gm_radial_power_lintegral hr q hq.le]

lemma gm_spec_gamma_lintegral {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k)
    (q : ℝ) (hq : 0 < q) (hqd : q < (k - r + 1 : ℕ) / (2 : ℝ)) :
    ∫⁻ G : Fin r → Fin k → ℝ,
      ENNReal.ofReal (specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ q) ∂gaussianMatrix r k
      ≤ ENNReal.ofReal ((2 ^ q * Real.Gamma ((r : ℝ) / 2 + q) / Real.Gamma ((r : ℝ) / 2)) *
        (Real.Gamma ((k - r + 1 : ℕ) / (2 : ℝ) - q) /
          (2 ^ q * Real.Gamma ((k - r + 1 : ℕ) / (2 : ℝ)))) /
        (2 ^ q * Real.Gamma (1 / 2 + q) / Real.Gamma (1 / 2))) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h1 : 0 < 2 ^ q * Real.Gamma (1 / 2 + q) / Real.Gamma (1 / 2) := by
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 2 + q by linarith)
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    positivity
  have h2 : 0 ≤ 2 ^ q * Real.Gamma ((r : ℝ) / 2 + q) / Real.Gamma ((r : ℝ) / 2) := by
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < (r : ℝ) / 2 + q by positivity)
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < (r : ℝ) / 2 by positivity)
    positivity
  have h3 : 0 ≤ Real.Gamma ((k - r + 1 : ℕ) / (2 : ℝ) - q) /
          (2 ^ q * Real.Gamma ((k - r + 1 : ℕ) / (2 : ℝ))) := by
    have := Real.Gamma_pos_of_pos (sub_pos.mpr hqd)
    have := Real.Gamma_pos_of_pos (show 0 < (k - r + 1 : ℕ) / (2 : ℝ) by linarith)
    positivity
  have h := gm_spec_weighted_lintegral hr hrk q hq hqd
  have hh := mul_le_mul_of_nonneg_right h (show (0 : ENNReal) ≤ (ENNReal.ofReal (2 ^ q * Real.Gamma (1 / 2 + q) / Real.Gamma (1 / 2)))⁻¹ from zero_le)
  rw [mul_assoc, ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr h1) ENNReal.ofReal_ne_top,
    mul_one] at hh
  rw [ENNReal.ofReal_div_of_pos h1, ENNReal.ofReal_mul h2, div_eq_mul_inv]
  exact hh

end GaussianMatrix

-- Local proof component: MomentNumerics

open MeasureTheory Real intervalIntegral
namespace GaussianMatrix

noncomputable def gmRise (a : ℝ) (q : ℕ) : ℝ := ∏ i ∈ Finset.range q, (a + 2 * i)

lemma gmRise_pos {a : ℝ} (ha : 0 < a) (q : ℕ) : 0 < gmRise a q := by
  exact Finset.prod_pos fun i _ => by positivity

lemma gmRise_succ (a : ℝ) (q : ℕ) : gmRise a (q + 1) = gmRise a q * (a + 2 * q) := by
  exact Finset.prod_range_succ _ _

lemma gm_log_factorial (n : ℕ) :
    (n : ℝ) * log (n + 1) - n ≤ log (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (0 : ℝ) < n + 1 := by positivity
    have h := log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 2) / (n + 1) by positivity)
    rw [log_div (by positivity) hn.ne'] at h
    have h' := mul_le_mul_of_nonneg_left h hn.le
    have he : ((n : ℝ) + 1) * (((n : ℝ) + 2) / (n + 1) - 1) = 1 := by field_simp; ring
    rw [he] at h'
    rw [Nat.factorial_succ, Nat.cast_mul, log_mul (by positivity) (by positivity)]
    push_cast
    rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
    nlinarith

lemma gm_factorial_lower (n : ℕ) :
    (((n : ℝ) + 1) / exp 1) ^ n ≤ (n.factorial : ℝ) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [← log_le_log_iff (by positivity) (by positivity), log_pow,
    log_div hn.ne' (exp_pos 1).ne', log_exp]
  nlinarith [gm_log_factorial n]

lemma gm_log_midpoint {a : ℝ} (ha : 0 < a) :
    (a + 2) * log (a + 2) - a * log a - 2 ≤ 2 * log (a + 1) := by
  have hm : 0 < a + 1 := by linarith
  have h := intervalIntegral.integral_mono_on (a := a) (b := a + 2) (by linarith)
    intervalIntegral.intervalIntegrable_log'
    (show IntervalIntegrable (fun x : ℝ => log (a + 1) + (x / (a + 1) - 1)) volume a (a + 2)
      from (by fun_prop : Continuous _).intervalIntegrable _ _) (fun x hx => ?_)
  · rw [integral_log, intervalIntegral.integral_add
      (intervalIntegrable_const) ((intervalIntegrable_id.div_const _).sub intervalIntegrable_const),
      intervalIntegral.integral_sub (intervalIntegrable_id.div_const _) intervalIntegrable_const,
      intervalIntegral.integral_const, intervalIntegral.integral_const,
      intervalIntegral.integral_div, integral_id] at h
    simp only [smul_eq_mul] at h
    have he : (a + 2 - a) * log (a + 1) +
        (((a + 2) ^ 2 - a ^ 2) / 2 / (a + 1) - (a + 2 - a) * 1) = 2 * log (a + 1) := by
      field_simp; ring
    rw [he] at h
    linarith
  · have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have hlog := log_le_sub_one_of_pos (div_pos hx0 hm)
    rw [log_div hx0.ne' hm.ne'] at hlog
    linarith

lemma gm_odd_log_lower (q : ℕ) :
    (q : ℝ) * (log (2 * q) - 1) ≤ log (gmRise 1 q) := by
  induction q with
  | zero => simp [gmRise]
  | succ q ih =>
    by_cases hq : q = 0
    · subst q
      norm_num [gmRise]
      have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    · have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
      have h := gm_log_midpoint (a := 2 * q) (by positivity)
      rw [gmRise_succ, log_mul (gmRise_pos (by norm_num : (0 : ℝ) < 1) q).ne' (by positivity)]
      push_cast
      rw [show (2 : ℝ) * (q + 1) = 2 * q + 2 by ring,
        show (1 : ℝ) + 2 * q = 2 * q + 1 by ring]
      nlinarith

lemma gm_odd_lower (q : ℕ) : (2 * (q : ℝ) / exp 1) ^ q ≤ gmRise 1 q := by
  by_cases hq : q = 0
  · subst q; simp [gmRise]
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  rw [← log_le_log_iff (by positivity) (gmRise_pos (by norm_num) q), log_pow,
    log_div (by positivity) (exp_pos 1).ne', log_exp]
  exact gm_odd_log_lower q

lemma gm_prod_range_add_le (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    ∏ i ∈ Finset.range (n + 1), (r + i) ≤ ((2 * r + n) / 2) ^ (n + 1) := by
  set M := (2 * r + n) / 2 with hM
  have hpos : ∀ i ∈ Finset.range (n + 1), 0 ≤ r + (i : ℝ) := fun i _ => by positivity
  have hP : 0 ≤ ∏ i ∈ Finset.range (n + 1), (r + (i : ℝ)) := Finset.prod_nonneg hpos
  have hMpos : 0 ≤ M := by rw [hM]; positivity
  have hrefl : ∏ i ∈ Finset.range (n + 1), (r + ((n - i : ℕ) : ℝ))
      = ∏ i ∈ Finset.range (n + 1), (r + (i : ℝ)) := by
    have := Finset.prod_range_reflect (fun i : ℕ => r + (i : ℝ)) (n + 1)
    simpa using this
  have hsq : (∏ i ∈ Finset.range (n + 1), (r + (i : ℝ))) ^ 2 ≤ (M ^ (n + 1)) ^ 2 := by
    rw [sq]
    calc (∏ i ∈ Finset.range (n + 1), (r + (i : ℝ))) * ∏ i ∈ Finset.range (n + 1), (r + (i : ℝ))
        = (∏ i ∈ Finset.range (n + 1), (r + (i : ℝ)))
            * ∏ i ∈ Finset.range (n + 1), (r + ((n - i : ℕ) : ℝ)) := by rw [hrefl]
      _ = ∏ i ∈ Finset.range (n + 1), ((r + (i : ℝ)) * (r + ((n - i : ℕ) : ℝ))) :=
          (Finset.prod_mul_distrib).symm
      _ ≤ ∏ _i ∈ Finset.range (n + 1), M ^ 2 := by
          apply Finset.prod_le_prod
          · intro i _; positivity
          · intro i hi
            have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
            rw [Nat.cast_sub hin, hM]
            nlinarith [sq_nonneg ((i : ℝ) - ((n : ℝ) - i))]
      _ = (M ^ (n + 1)) ^ 2 := by rw [Finset.prod_const, Finset.card_range, ← pow_mul,
            ← pow_mul, mul_comm]
  exact (pow_le_pow_iff_left₀ hP (pow_nonneg hMpos _) two_ne_zero).1 hsq
lemma gmRise_le {a : ℝ} (ha : 0 ≤ a) (q : ℕ) : gmRise a q ≤ (a + q) ^ q := by
  cases q with
  | zero => simp [gmRise]
  | succ n =>
    have h := gm_prod_range_add_le (a / 2) (by positivity) n
    have he : gmRise a (n + 1) = 2 ^ (n + 1) * ∏ i ∈ Finset.range (n + 1), (a / 2 + i) := by
      have hc : (2 : ℝ) ^ (n + 1) = ∏ _i ∈ Finset.range (n + 1), (2 : ℝ) := by simp
      rw [gmRise, hc, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      ring
    rw [he]
    calc
      _ ≤ 2 ^ (n + 1) * ((2 * (a / 2) + n) / 2) ^ (n + 1) := by gcongr
      _ = (a + n) ^ (n + 1) := by rw [← mul_pow]; congr 1; ring
      _ ≤ (a + (n + 1 : ℕ)) ^ (n + 1) := by push_cast; gcongr; linarith

lemma gmRise_gamma {a : ℝ} (ha : 0 < a) (q : ℕ) :
    2 ^ q * Gamma (a / 2 + q) / Gamma (a / 2) = gmRise a q := by
  have hg : Gamma (a / 2) ≠ 0 := (Gamma_pos_of_pos (by positivity)).ne'
  induction q with
  | zero => simp [gmRise, hg]
  | succ q ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Gamma_add_one (by positivity), pow_succ, gmRise_succ]
    calc
      _ = (2 ^ q * Gamma (a / 2 + q) / Gamma (a / 2)) * (a + 2 * q) := by ring
      _ = _ := by rw [ih]

lemma gmRise_one_two (q : ℕ) : gmRise 1 q * gmRise 2 q = ((2 * q).factorial : ℝ) := by
  induction q with
  | zero => simp [gmRise]
  | succ q ih =>
    rw [gmRise_succ, gmRise_succ, show 2 * (q + 1) = (2 * q + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    calc
      _ = (gmRise 1 q * gmRise 2 q) * ((2 * q + 1) * (2 * q + 2)) := by ring
      _ = _ := by rw [ih]; ring

lemma gm_even_numeric {a : ℝ} (ha : 0 ≤ a) {q : ℕ} (hq : 1 ≤ q) :
    gmRise a q / (gmRise 1 q * gmRise 1 q) ≤
      (exp 1 ^ 2 * (a + q) / ((2 * q) ^ 2)) ^ q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hl := gm_odd_lower q
  have hpos : 0 < gmRise 1 q := gmRise_pos (by norm_num) q
  calc
    _ ≤ (a + q) ^ q / ((2 * (q : ℝ) / exp 1) ^ q * (2 * (q : ℝ) / exp 1) ^ q) := by
      apply div_le_div₀ (by positivity) (gmRise_le ha q) (by positivity)
      exact mul_self_le_mul_self (by positivity) hl
    _ = _ := by
      rw [← mul_pow, ← div_pow]
      congr 1
      field_simp <;> ring

lemma gm_odd_numeric {a : ℝ} (ha : 0 ≤ a) (q : ℕ) :
    gmRise a q / (gmRise 1 q * gmRise 2 q) ≤
      (exp 1 ^ 2 * (a + q) / (2 * q + 1) ^ 2) ^ q := by
  rw [gmRise_one_two]
  have hl := gm_factorial_lower (2 * q)
  have hn : (0 : ℝ) < ((2 * q).factorial : ℝ) := by positivity
  calc
    _ ≤ (a + q) ^ q / (((2 * q : ℕ) + 1 : ℝ) / exp 1) ^ (2 * q) := by
      apply div_le_div₀ (by positivity) (gmRise_le ha q) (by positivity) hl
    _ = _ := by
      push_cast
      rw [pow_mul, ← div_pow]
      congr 1
      field_simp <;> ring

end GaussianMatrix

-- Local proof component: Finish

open MeasureTheory ProbabilityTheory Real
open scoped Matrix Matrix.Norms.L2Operator
namespace GaussianMatrix

lemma gm_spec_rise_even {r q : ℕ} (hr : 1 ≤ r) (hq : 1 ≤ q) :
    ∫⁻ G : Fin r → Fin (r + 2 * q) → ℝ,
      ENNReal.ofReal (specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ q) ∂gaussianMatrix r (r + 2 * q)
      ≤ ENNReal.ofReal (gmRise r q / (gmRise 1 q * gmRise 1 q)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hd : ((r + 2 * q - r + 1 : ℕ) : ℝ) / 2 = 1 / 2 + q := by
    rw [Nat.add_sub_cancel_left]; push_cast; ring
  have h := gm_spec_gamma_lintegral hr (show r ≤ r + 2 * q by omega) (q : ℝ) hqR
    (by rw [hd]; linarith)
  simp only [Real.rpow_natCast, hd] at h
  rw [gmRise_gamma hrR q, show (1 / 2 : ℝ) + q - q = 1 / 2 by ring,
    gmRise_gamma (by norm_num : (0 : ℝ) < 1) q] at h
  have hn : Gamma (1 / 2) / (2 ^ q * Gamma (1 / 2 + q)) = (gmRise 1 q)⁻¹ := by
    rw [← gmRise_gamma (by norm_num : (0 : ℝ) < 1) q]
    simp [div_eq_mul_inv, mul_comm]
  rw [hn] at h
  convert h using 1
  congr 1
  field_simp

lemma gm_spec_rise_odd {r q : ℕ} (hr : 1 ≤ r) (hq : 1 ≤ q) :
    ∫⁻ G : Fin r → Fin (r + 2 * q + 1) → ℝ,
      ENNReal.ofReal (specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ q) ∂gaussianMatrix r (r + 2 * q + 1)
      ≤ ENNReal.ofReal (gmRise r q / (gmRise 1 q * gmRise 2 q)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hd : ((r + 2 * q + 1 - r + 1 : ℕ) : ℝ) / 2 = 1 + q := by
    rw [show r + 2 * q + 1 - r + 1 = 2 * q + 2 by omega]; push_cast; ring
  have h := gm_spec_gamma_lintegral hr (show r ≤ r + 2 * q + 1 by omega) (q : ℝ) hqR
    (by rw [hd]; linarith)
  simp only [Real.rpow_natCast, hd] at h
  rw [gmRise_gamma hrR q, show (1 : ℝ) + q - q = 1 by ring,
    gmRise_gamma (by norm_num : (0 : ℝ) < 1) q] at h
  have hn : Gamma 1 / (2 ^ q * Gamma (1 + q)) = (gmRise 2 q)⁻¹ := by
    rw [← gmRise_gamma (by norm_num : (0 : ℝ) < 2) q]
    norm_num only [show (2 : ℝ) / 2 = 1 by norm_num]
    simp [div_eq_mul_inv, mul_comm]
  rw [hn] at h
  convert h using 1
  congr 1
  field_simp
lemma gm_spec_endpoint {r k : ℕ} (hr : 1 ≤ r) (hrk : r + 2 ≤ k) :
    ∫⁻ G : Fin r → Fin k → ℝ,
      ENNReal.ofReal (specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ ((k-r)/2)) ∂gaussianMatrix r k
      ≤ ENNReal.ofReal ((exp 1 ^ 2 * ((k : ℝ) + r) / (2 * ((k : ℝ) - r) ^ 2)) ^ ((k-r)/2)) := by
  let q := (k-r)/2
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hk : k = r + 2 * q ∨ k = r + 2 * q + 1 := by dsimp [q]; omega
  change (∫⁻ G : Fin r → Fin k → ℝ,
      ENNReal.ofReal (specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ q) ∂gaussianMatrix r k) ≤ _
  change _ ≤ ENNReal.ofReal ((exp 1 ^ 2 * ((k : ℝ) + r) / (2 * ((k : ℝ) - r) ^ 2)) ^ q)
  rcases hk with hk | hk
  · rw [hk]
    apply (gm_spec_rise_even hr hq).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (exp 1 ^ 2 * ((r : ℝ) + q) / (2 * q) ^ 2) ^ q := gm_even_numeric (by positivity) hq
      _ = _ := by
        congr 1
        push_cast
        field_simp
        ring
  · rw [hk]
    apply (gm_spec_rise_odd hr hq).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (exp 1 ^ 2 * ((r : ℝ) + q) / (2 * q + 1) ^ 2) ^ q := gm_odd_numeric (by positivity) q
      _ ≤ _ := by
        apply pow_le_pow_left₀ (by positivity)
        push_cast
        rw [show (r : ℝ) + 2 * q + 1 - r = 2 * q + 1 by ring]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        have hE := sq_pos_of_pos (exp_pos 1)
        nlinarith [sq_pos_of_pos (show 0 < 2 * (q : ℝ) + 1 by positivity)]

lemma gm_lower_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) {p q : ℕ}
    (hp : 1 ≤ p) (hpq : p ≤ q) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∫⁻ x, ENNReal.ofReal (f x ^ q) ∂μ ≤ ENNReal.ofReal (C ^ q)) :
    Integrable (fun x => f x ^ p) μ ∧ ∫ x, f x ^ p ∂μ ≤ C ^ p := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have heq (n : ℕ) (hn0 : n ≠ 0) :
      eLpNorm f (n : ENNReal) μ =
        (∫⁻ x, ENNReal.ofReal (f x ^ n) ∂μ) ^ (1 / (n : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast hn0) (by simp)]
    simp only [ENNReal.toReal_natCast]
    congr 1
    apply lintegral_congr
    intro x
    rw [Real.enorm_eq_ofReal (hn x), ENNReal.rpow_natCast, ENNReal.ofReal_pow (hn x)]
  have hqp : eLpNorm f (p : ENNReal) μ ≤ eLpNorm f (q : ENNReal) μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (by exact_mod_cast hpq) hf.aestronglyMeasurable
  have hqC : eLpNorm f (q : ENNReal) μ ≤ ENNReal.ofReal C := by
    rw [heq q (by omega)]
    have h := ENNReal.rpow_le_rpow hbound (show 0 ≤ 1 / (q : ℝ) by positivity)
    rw [ENNReal.ofReal_pow hC, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      mul_one_div_cancel hq0, ENNReal.rpow_one] at h
    exact h
  have hpC := ENNReal.rpow_le_rpow (hqp.trans hqC) (show (0 : ℝ) ≤ p by positivity)
  rw [heq p (by omega), ← ENNReal.rpow_mul, one_div_mul_cancel hp0, ENNReal.rpow_one,
    ENNReal.rpow_natCast, ← ENNReal.ofReal_pow hC] at hpC
  have hnn : 0 ≤ᵐ[μ] (fun x => f x ^ p) := Filter.Eventually.of_forall fun x => pow_nonneg (hn x) _
  refine ⟨⟨(hf.pow_const p).aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn]
    exact hpC.trans_lt ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn (hf.pow_const p).aestronglyMeasurable]
    simpa only [ENNReal.toReal_ofReal (pow_nonneg hC p)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hpC

end GaussianMatrix

open GaussianMatrix

theorem solution {r k p : ℕ} (hp : 1 ≤ p) (hp18 : p ≤ 18)
    (hrk : r + 2 * p ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ p)
      (gaussianMatrix r k) ∧
    ∫ G, specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ p ∂(gaussianMatrix r k)
      ≤ (Real.exp 1 ^ 2 * ((k : ℝ) + r) / (2 * ((k : ℝ) - r) ^ 2)) ^ p := by
  by_cases hr : r = 0
  · subst r
    have hzero (G : Fin 0 → Fin k → ℝ) : specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ = 0 := by
      change ‖(Matrix.of G * (Matrix.of G)ᵀ)⁻¹‖ = 0
      rw [Subsingleton.elim ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹) 0, norm_zero]
    simp_rw [hzero, zero_pow (show p ≠ 0 by omega)]
    exact ⟨integrable_zero _ _ _, by simp; positivity⟩
  · have hr1 : 1 ≤ r := by omega
    exact gm_lower_moment (gaussianMatrix r k)
      (fun G => specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹)
      gm_measurable_spec_inv (fun G => norm_nonneg _) hp (by omega) _ (by positivity)
      (gm_spec_endpoint hr1 (by omega))
