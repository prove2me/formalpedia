-- Prove2me | solution 1 for BornVolume.map_ratioN_momentMap_fsMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:38.067164+00:00
-- url     : https://prove2.me/submissions/8132c65b-f79a-477c-9b96-fe17682f129f

module
public import Definitions.Def_BornVolumeLean_Volume_GaussianCPN
public import Definitions.Def_BornVolumeLean_Volume_MomentMap
public import Definitions.Def_BornVolumeLean_Volume_MomentRatioUniformN
public import Definitions.Def_BornVolumeLean_Volume_MomentBridgeN
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Theorems.Thm_BornVolume_pi_gaussianReal_prod_singleton_zero
public import Theorems.Thm_BornVolume_blockSqNormCurry_map_pi
public import Theorems.Thm_BornVolume_euclidean_norm_sq_eq_sum
public import Theorems.Thm_BornVolume_gaussianCPN_eq_fubiniStudy
public import Theorems.Thm_BornVolume_momentMap_measurable
public import Theorems.Thm_BornVolume_ratioSqNorm_map_expHalf_pi
public import Theorems.Thm_Projectivization_momentMap_mk
public import Theorems.Thm_Projectivization_momentMap_sum_eq_one


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (p₀ : CPN (M + 1)) :
    Measure.map (fun p : CPN (M + 1) => ratioN (fun i => momentMap p i)) (fsMeasure p₀)
      = (Nat.factorial M : ℝ≥0∞) • volume.restrict openSimplexFree := by
  have : NeZero (M + 1) := ⟨Nat.succ_ne_zero M⟩
  have hratio_meas : Measurable (ratioN (M := M)) := by
    unfold ratioN
    apply measurable_pi_iff.mpr; intro k
    exact (measurable_pi_apply _).div
      (Finset.measurable_sum Finset.univ (fun i _ => measurable_pi_apply i))
  have hmoment_meas : Measurable (fun p : CPN (M + 1) => fun i => momentMap p i) := by
    apply measurable_pi_iff.mpr; intro i; exact momentMap_measurable i
  have hblock_meas : Measurable (fun y : (Fin (M + 1) × Fin 2) → ℝ =>
      fun i => (y (i, 0)) ^ 2 + (y (i, 1)) ^ 2) := by
    apply measurable_pi_iff.mpr; intro i; fun_prop
  rw [← ratioSqNorm_map_expHalf_pi, ← blockSqNormCurry_map_pi,
    Measure.map_map hratio_meas hblock_meas,
    ← gaussianCPN_eq_fubiniStudy p₀, gaussianCPN, gaussianHN,
    show (fun p : CPN (M + 1) => ratioN (fun i => momentMap p i))
        = ratioN ∘ (fun p => fun i => momentMap p i) from rfl,
    Measure.map_map (hratio_meas.comp hmoment_meas) (measurable_gaussianProjN p₀),
    Measure.map_map ((hratio_meas.comp hmoment_meas).comp (measurable_gaussianProjN p₀))
      coordsN.continuous.measurable,
    ← map_pi_eq_stdGaussian,
    Measure.map_map (((hratio_meas.comp hmoment_meas).comp (measurable_gaussianProjN p₀)).comp
      coordsN.continuous.measurable) (by fun_prop)]
  refine Measure.map_congr ?_
  have hae : ∀ᵐ y ∂(Measure.pi (fun _ : Fin (M + 1) × Fin 2 => gaussianReal 0 1)),
      y ≠ (0 : (Fin (M + 1) × Fin 2) → ℝ) := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    rw [show {a : (Fin (M + 1) × Fin 2) → ℝ | a = 0} = {(0 : (Fin (M + 1) × Fin 2) → ℝ)} from by
        ext a; simp]
    exact pi_gaussianReal_prod_singleton_zero
  filter_upwards [hae] with y hy
  simp only [Function.comp_apply]
  set v : EuclideanSpace ℂ (Fin (M + 1)) := coordsN (WithLp.toLp 2 y) with hvdef
  have hv0 : v ≠ 0 := by
    rw [hvdef]; intro h; apply hy
    have hz : (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin (M + 1) × Fin 2)) = 0 :=
      coordsN.injective (by rw [h, map_zero])
    simpa using congrArg (WithLp.equiv 2 ((Fin (M + 1) × Fin 2) → ℝ)) hz
  rw [gaussianProjN, dif_neg hv0]
  -- Per-coordinate: `‖v i‖² = y(i,0)² + y(i,1)²`, and `∑ᵢ ‖v i‖² = ‖v‖²`.
  have hvival : ∀ i, ‖v i‖ ^ 2 = (y (i, 0)) ^ 2 + (y (i, 1)) ^ 2 := by
    intro i
    have hvieq : v i = ((y (i, 0) : ℂ) + (y (i, 1) : ℂ) * Complex.I) := rfl
    rw [hvieq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
  have hsum : ∑ i, ((y (i, 0)) ^ 2 + (y (i, 1)) ^ 2) = ‖v‖ ^ 2 := by
    rw [euclidean_norm_sq_eq_sum]
    exact (Finset.sum_congr rfl (fun i _ => (hvival i).symm))
  -- The two ratio maps agree coordinatewise (both normalise to `‖v(castSucc k)‖²/‖v‖²`).
  funext k
  simp only [ratioN]
  rw [momentMap_mk v hv0 (Fin.castSucc k), momentMap_sum_eq_one (Projectivization.mk ℂ v hv0),
    div_one, ← hvival (Fin.castSucc k), ← hsum]
end BornVolume
