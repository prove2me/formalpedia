-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.rootCOV_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:11:03.778461+00:00
-- url     : https://prove2.me/submissions/53cfc183-df41-47c3-9f29-0e0e5eb28811

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourthWeightDensityOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JacobianAeNonzero
import Theorems.Thm_Formalism_FourierDecayAlt_P_RootChangeOfVariables_jac
import Theorems.Thm_Formalism_FourierDecayAlt_P_RootChangeOfVariables_ae_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt MeasureTheory
open scoped ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open RootChangeOfVariables
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.RootCOV := by
  intro s φ hs hφ
  have hs0 : s ≠ 0 := by omega
  haveI : NeZero s := ⟨hs0⟩

  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℂ → ℂ, ρ = fun D => D ^ ((s : ℂ)⁻¹) := ⟨_, rfl⟩
  have hρn : ∀ D, ρ D ^ s = D := fun D => by rw [hρ]; exact Complex.cpow_nat_inv_pow D hs0
  have hρm : Measurable ρ := by rw [hρ]; exact measurable_id.pow_const _
  set S : Set ℂ := {z | z ^ s ≠ 0 ∧ ρ (z ^ s) = z} with hS
  have hSm : MeasurableSet S := by
    apply MeasurableSet.inter
    · exact (measurableSet_singleton (0 : ℂ)).compl.preimage (measurable_id.pow_const s)
    · exact measurableSet_eq_fun (hρm.comp (measurable_id.pow_const s)) measurable_id
  have hS0 : ∀ z ∈ S, z ≠ 0 := fun z hz e => hz.1 (by rw [e]; exact zero_pow hs0)

  obtain ⟨wt, hwt⟩ : ∃ wt : ℂ → ℝ≥0∞, wt = fun z => ENNReal.ofReal (((s : ℕ) : ℝ) ^ 2 * ‖z‖ ^ (2 * (s - 1))) :=
    ⟨_, rfl⟩
  have hwtm : Measurable wt := by
    rw [hwt]; exact Measurable.ennreal_ofReal (measurable_const.mul ((continuous_norm.pow _).measurable))

  have hL : ∀ ψ : ℂ → ℝ≥0∞, ∫⁻ D, ψ (ρ D) = ∫⁻ z in S, wt z * ψ z := by
    intro ψ
    have himg : (fun z : ℂ => z ^ s) '' S = {D : ℂ | D ≠ 0} := by
      ext D; constructor
      · rintro ⟨z, hz, rfl⟩; exact hz.1
      · intro hD
        refine ⟨ρ D, ⟨?_, ?_⟩, hρn D⟩
        · rw [hρn]; exact hD
        · rw [hρn]
    have hinj : Set.InjOn (fun z : ℂ => z ^ s) S := by
      intro z1 h1 z2 h2 e
      rw [← h1.2, ← h2.2]; simp only at e; rw [e]
    have hder : ∀ z ∈ S, HasFDerivWithinAt (fun z : ℂ => z ^ s)
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ((s : ℂ) * z ^ (s - 1))).restrictScalars ℝ) S z :=
      fun z _ => ((hasDerivAt_pow s z).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    have step1 : ∫⁻ D, ψ (ρ D) = ∫⁻ D in {D : ℂ | D ≠ 0}, ψ (ρ D) := by
      rw [Measure.restrict_eq_self_of_ae_mem ae_ne_zero]
    rw [step1, ← himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm hder hinj]
    apply setLIntegral_congr_fun hSm
    intro z hz
    dsimp only
    rw [jac, hz.2, hwt]
    congr 2
    rw [abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_mul, map_pow, Complex.normSq_natCast,
      Complex.normSq_eq_norm_sq, ← pow_mul, sq]

  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / s) with hζ
  have hprim : IsPrimitiveRoot ζ s := Complex.isPrimitiveRoot_exp s hs0
  have hζn : ∀ j, ‖ζ ^ j‖ = 1 := fun j => by rw [norm_pow, hprim.norm'_eq_one hs0, one_pow]
  have hζ0 : ∀ j, ζ ^ j ≠ 0 := fun j h => by have := hζn j; rw [h, norm_zero] at this; exact zero_ne_one this
  have hrot : ∀ (j : ℕ) (G : ℂ → ℝ≥0∞), ∫⁻ z in S, G (ζ ^ j * z) = ∫⁻ y in (fun z => ζ ^ j * z) '' S, G y := by
    intro j G
    have hder : ∀ z ∈ S, HasFDerivWithinAt (fun z : ℂ => ζ ^ j * z)
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (ζ ^ j * 1)).restrictScalars ℝ) S z :=
      fun z _ => (((hasDerivAt_id z).const_mul (ζ ^ j)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    have hinj : Set.InjOn (fun z : ℂ => ζ ^ j * z) S := fun z1 _ z2 _ e => mul_left_cancel₀ (hζ0 j) e
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm hder hinj]
    apply setLIntegral_congr_fun hSm
    intro z _
    dsimp only
    rw [jac, mul_one, Complex.normSq_eq_norm_sq, hζn, one_pow, abs_one, ENNReal.ofReal_one, one_mul]

  have hroots : ∀ D, ((Polynomial.nthRoots s D).map φ).sum = ∑ j ∈ Finset.range s, φ (ζ ^ j * ρ D) := by
    intro D
    rw [hprim.nthRoots_eq (hρn D), Multiset.map_map]
    rfl
  simp only [hroots]
  have hmeas : ∀ j ∈ Finset.range s, Measurable (fun D => φ (ζ ^ j * ρ D)) :=
    fun j _ => hφ.comp (measurable_const.mul hρm)
  rw [lintegral_finset_sum _ hmeas]
  have hterm : ∀ j ∈ Finset.range s, ∫⁻ D, φ (ζ ^ j * ρ D) =
      ∫⁻ y in (fun z => ζ ^ j * z) '' S, wt y * φ y := by
    intro j _
    rw [hL (fun z => φ (ζ ^ j * z)), ← hrot j (fun y => wt y * φ y)]
    apply setLIntegral_congr_fun hSm
    intro z _
    simp only [hwt, norm_mul, hζn, one_mul]
  rw [Finset.sum_congr rfl hterm]
  have hTm : ∀ j, MeasurableSet ((fun z => ζ ^ j * z) '' S) := fun j =>
    (MeasurableEquiv.mulLeft₀ (ζ ^ j) (hζ0 j)).measurableSet_image.mpr hSm
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range s)) (fun j => (fun z => ζ ^ j * z) '' S) := by
    intro j hj j' hj' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨z, hz, rfl⟩ ⟨z', hz', e⟩
    have h1 : ∀ i : ℕ, (ζ ^ i) ^ s = 1 := fun i => by
      rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    have hpow : z' ^ s = z ^ s := by
      have := congrArg (fun t => t ^ s) e
      simp only [mul_pow, h1, one_mul] at this
      exact this
    have hzz : z' = z := by rw [← hz'.2, ← hz.2, hpow]
    rw [hzz] at e
    have := mul_right_cancel₀ (hS0 z hz) e
    exact hne (hprim.pow_inj (Finset.mem_range.mp hj') (Finset.mem_range.mp hj) this).symm
  rw [← lintegral_biUnion_finset hdisj (fun j _ => hTm j)]
  have hunion : (⋃ j ∈ Finset.range s, (fun z => ζ ^ j * z) '' S) = {y : ℂ | y ≠ 0} := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨j, _, z, hz, rfl⟩
      exact mul_ne_zero (hζ0 j) (hS0 z hz)
    · intro hy
      set z0 := ρ (y ^ s) with hz0
      have hz0n : z0 ^ s = y ^ s := hρn _
      have hz0S : z0 ∈ S := ⟨by rw [hz0n]; exact pow_ne_zero s hy, by rw [hz0n]⟩
      have hz00 := hS0 z0 hz0S
      have h1 : (y / z0) ^ s = 1 := by rw [div_pow, hz0n, div_self (pow_ne_zero s hy)]
      obtain ⟨j, hj, hjeq⟩ := hprim.eq_pow_of_pow_eq_one h1
      exact ⟨j, hj, z0, hz0S, by rw [hjeq]; field_simp⟩
  rw [hunion, Measure.restrict_eq_self_of_ae_mem ae_ne_zero, hwt]
end Formalism.FourierDecayAlt.P
