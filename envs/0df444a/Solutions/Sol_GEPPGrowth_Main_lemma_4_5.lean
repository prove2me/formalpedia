-- Prove2me | solution 1 for GEPPGrowth.Main.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T22:00:14.469993+00:00
-- url     : https://prove2.me/submissions/6af9ff51-2358-4593-80d4-cb239713635b

import Mathlib
import Definitions.Def_GEPPGrowth_Main_Process
import Theorems.Thm_MeasureTheory_lintegral_fintype_prod_eq_prod

open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators Matrix ENNReal

noncomputable section

namespace GEPP45

open GEPPGrowth.Main

/-- Density of `N(0, I_k)` on `Fin k → ℝ`. -/
def gdens (k : ℕ) (x : Fin k → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (-(k : ℝ) / 2) * Real.exp (-(∑ i, x i ^ 2) / 2))

lemma measurable_gdens {k : ℕ} : Measurable (gdens k) := by
  unfold gdens; exact Measurable.ennreal_ofReal (by fun_prop)

/-- The standard Gaussian on `Fin d → ℝ`. -/
abbrev gam (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi (fun _ : Fin d => gaussianReal 0 1)

lemma gauss_pi (k : ℕ) : gam k = volume.withDensity (gdens k) := by
  have hg : ∀ x : Fin k → ℝ, gdens k x = ∏ i, gaussianPDF 0 1 (x i) := by
    intro x
    simp only [gdens, gaussianPDF, gaussianPDFReal]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    congr 1
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    · rw [NNReal.coe_one, mul_one, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_neg_one,
        ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
      congr 1; ring
    · rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
      simp [neg_div]
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : (Set.univ.pi s).indicator (gdens k) =
      fun x => ∏ i, (s i).indicator (gaussianPDF 0 1) (x i) := by
    funext x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx, hg x]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i (Set.mem_univ _)) _).symm
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [hind, volume_pi, lintegral_fintype_prod_eq_prod (fun _ => (s _).indicator _)
    (fun i => (measurable_gaussianPDF 0 1).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply 0 one_ne_zero, lintegral_indicator (hs i)]

open scoped MatrixOrder in
lemma normal_eq_map (d : ℕ) (S : Mat d) : normal S = (gam d).map (fun y => CFC.sqrt S *ᵥ y) := by
  unfold normal multivariateGaussian
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext y i
  simp

open scoped MatrixOrder in
lemma normal_one (d : ℕ) : normal (1 : Mat d) = gam d := by
  rw [normal_eq_map, CFC.sqrt_one]
  simp [Matrix.one_mulVec, Measure.map_id']

/-- Image of the standard Gaussian under an invertible matrix, on a measurable set. -/
lemma map_mulVec_apply (d : ℕ) (M N : Mat d) (hNM : N * M = 1) {A : Set (Vec d)}
    (hA : MeasurableSet A) :
    (gam d).map (fun y => M *ᵥ y) A =
      ENNReal.ofReal |M.det|⁻¹ * ∫⁻ x in A, gdens d (N *ᵥ x) := by
  have hM : Measurable (fun y : Vec d => M *ᵥ y) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  have hdet : M.det ≠ 0 := by
    intro h
    have h' := congrArg Matrix.det hNM
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at h'
    exact zero_ne_one h'
  rw [Measure.map_apply hM hA, gauss_pi, withDensity_apply _ (hM hA),
    ← lintegral_indicator (hM hA)]
  have hQ : Measurable (A.indicator (fun x => gdens d (N *ᵥ x))) :=
    (measurable_gdens.comp (Matrix.toLin' N).continuous_of_finiteDimensional.measurable).indicator hA
  have h1 : ((fun y => M *ᵥ y) ⁻¹' A).indicator (gdens d) =
      fun y => A.indicator (fun x => gdens d (N *ᵥ x)) (M *ᵥ y) := by
    funext y
    simp only [Set.indicator, Set.mem_preimage, Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
    rfl
  rw [h1, ← lintegral_map hQ hM]
  have h2 : Measure.map (fun y => M *ᵥ y) (volume : Measure (Vec d)) =
      ENNReal.ofReal |M.det|⁻¹ • volume := by
    have := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Vec d)))
      (f := Matrix.toLin' M) (by rwa [LinearMap.det_toLin'])
    rw [LinearMap.det_toLin', abs_inv] at this
    exact this
  rw [h2, lintegral_smul_measure, lintegral_indicator hA, smul_eq_mul]

open scoped Matrix.Norms.L2Operator in
open scoped MatrixOrder in
/-- `S = R R` with `R = √S`; the facts about `R` the comparison needs. -/
lemma sqrt_facts (d : ℕ) (S : Mat d) (hS : S.PosDef) :
    ∃ R : Mat d, normal S = (gam d).map (fun y => R *ᵥ y) ∧ R⁻¹ * R = 1 ∧
      R.det = Real.sqrt S.det ∧ ∀ x : Vec d, ∑ i, (R⁻¹ *ᵥ x) i ^ 2 ≤ ‖S⁻¹‖ * ∑ i, x i ^ 2 := by
  set R := CFC.sqrt S with hRdef
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hRt : Rᴴ = R := (CFC.sqrt_nonneg S).isSelfAdjoint
  have hdet : R.det = Real.sqrt S.det := by
    rw [hRdef, hS.posSemidef.det_sqrt]
    simp [RCLike.sqrt_eq_ite]
  have hdpos : 0 < R.det := by rw [hdet]; exact Real.sqrt_pos.2 hS.det_pos
  refine ⟨R, normal_eq_map d S, Matrix.nonsing_inv_mul R (isUnit_iff_ne_zero.2 hdpos.ne'), hdet, ?_⟩
  intro x
  have hRinv : (R⁻¹)ᴴ = R⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hRt]
  have hnorm : ‖R⁻¹‖ * ‖R⁻¹‖ = ‖S⁻¹‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hRinv, ← Matrix.mul_inv_rev, hRR]
  have h := Matrix.l2_opNorm_mulVec R⁻¹ ((EuclideanSpace.equiv (Fin d) ℝ).symm x)
  have hsq : ∀ v : Vec d, ∑ i, v i ^ 2 = ‖(EuclideanSpace.equiv (Fin d) ℝ).symm v‖ ^ 2 := by
    intro v
    rw [EuclideanSpace.norm_sq_eq]
    simp
  rw [hsq, hsq x]
  calc _ ≤ (‖R⁻¹‖ * ‖(EuclideanSpace.equiv (Fin d) ℝ).symm x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by rw [← hnorm]; ring

lemma gdens_anti (d : ℕ) (x y : Vec d) (h : ∑ i, x i ^ 2 ≤ ∑ i, y i ^ 2) :
    gdens d y ≤ gdens d x := by
  unfold gdens
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.2
  linarith

end GEPP45

open scoped Matrix.Norms.L2Operator in
open GEPPGrowth.Main GEPP45 in
theorem solution (d : ℕ) (S : Mat d) (hS : S.PosDef) (E : Set (Vec d)) (hE : Conic E) :
    (1 / (Real.rpow (GaussianMatrix.specNorm S⁻¹) ((d:ℝ)/2) * Real.sqrt S.det)) *
      prob (normal (1 : Mat d)) E ≤ prob (normal S) E := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rcases Set.eq_empty_or_nonempty E with rfl | hne
    · simp [prob]
    rw [Subsingleton.eq_univ_of_nonempty hne]
    simp [prob, GaussianMatrix.specNorm]
  set c : ℝ := 1 / (Real.rpow (GaussianMatrix.specNorm S⁻¹) ((d:ℝ)/2) * Real.sqrt S.det) with hc
  set lam := GaussianMatrix.specNorm S⁻¹ with hlam
  have hdetS : 0 < S.det := hS.det_pos
  have hlam_pos : 0 < lam := by
    have hne : S⁻¹ ≠ 0 := by
      intro h0
      have h0' := congrArg Matrix.det h0
      have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      rw [Matrix.det_zero, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h0'
      exact (inv_ne_zero hdetS.ne') h0'
    show 0 < ‖S⁻¹‖
    exact norm_pos_iff.2 hne
  have hc0 : 0 ≤ c := by
    rw [hc]; exact div_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg hlam_pos.le _) (Real.sqrt_nonneg _))
  set s := Real.sqrt lam with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 hlam_pos
  set t := s⁻¹ with ht_def
  have ht : t ≠ 0 := inv_ne_zero hs.ne'
  -- the measure inequality on measurable sets
  have key : ∀ A, MeasurableSet A →
      ENNReal.ofReal c * (gam d).map (fun y => t • y) A ≤ normal S A := by
    intro A hA
    obtain ⟨R, hRdef, hRR, hRdet, hquad⟩ := sqrt_facts d S hS
    have h1 : (fun y : Vec d => t • y) = fun y => (t • (1 : Mat d)) *ᵥ y := by
      funext y; rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 : (s • (1 : Mat d)) * (t • (1 : Mat d)) = 1 := by
      rw [smul_mul_smul_comm, ht_def, mul_inv_cancel₀ hs.ne', one_smul, one_mul]
    rw [h1, map_mulVec_apply d _ _ h2 hA, hRdef, map_mulVec_apply d _ _ hRR hA, ← mul_assoc,
      ← ENNReal.ofReal_mul hc0]
    have hconst : c * |(t • (1 : Mat d)).det|⁻¹ = |R.det|⁻¹ := by
      have hpow : lam.rpow ((d:ℝ)/2) = s ^ d := by
        show lam ^ ((d:ℝ)/2) = _
        rw [hs_def, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hlam_pos.le]
        congr 1; ring
      have hsqrt : 0 < Real.sqrt S.det := Real.sqrt_pos.2 hdetS
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hRdet, hc, hpow, ht_def,
        inv_pow, abs_inv, abs_of_pos (pow_pos hs d), inv_inv, abs_of_pos hsqrt]
      field_simp
    rw [hconst]
    gcongr with x
    apply gdens_anti
    calc ∑ i, (R⁻¹ *ᵥ x) i ^ 2 ≤ lam * ∑ i, x i ^ 2 := hquad x
      _ = ∑ i, ((s • (1 : Mat d)) *ᵥ x) i ^ 2 := by
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]
        simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
        rw [hs_def, Real.sq_sqrt hlam_pos.le]
  have hle : ENNReal.ofReal c • (gam d).map (fun y => t • y) ≤ normal S :=
    Measure.le_iff.2 fun A hA => by simpa using key A hA
  have hE' := Measure.le_iff'.1 hle E
  let e := (Homeomorph.smulOfNeZero (α := Vec d) t ht).toMeasurableEquiv
  have hmap : (gam d).map (fun y => t • y) E = gam d E := by
    have h1 : (gam d).map (fun y => t • y) = (gam d).map e := rfl
    rw [h1, e.map_apply]
    congr 1
    ext x
    constructor
    · intro hx
      have := hE _ hx s hs
      have h2 : (fun i => s * (e x) i) = x := by
        funext i
        change s * (t * x i) = x i
        rw [ht_def, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
      rwa [h2] at this
    · intro hx
      exact hE _ hx t (inv_pos.2 hs)
  rw [Measure.smul_apply, hmap, smul_eq_mul] at hE'
  rw [normal_one, prob, prob]
  calc c * (gam d E).toReal = (ENNReal.ofReal c * gam d E).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0]
    _ ≤ (normal S E).toReal := ENNReal.toReal_mono (measure_ne_top _ _) hE'
