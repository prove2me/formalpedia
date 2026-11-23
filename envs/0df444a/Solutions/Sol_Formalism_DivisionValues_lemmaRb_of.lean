-- Prove2me | solution 1 for Formalism.DivisionValues.lemmaRb_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:18.658469+00:00
-- url     : https://prove2.me/submissions/4753cb9a-2c9e-4385-a157-c10b9dc54aff

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjTransposeEqOfPosDef
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SpecDet
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DeterminantCauchySchwarz
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaSecond
import Theorems.Thm_Formalism_DivisionValues_Rb_tw_apply
import Theorems.Thm_Formalism_DivisionValues_Rb_plc_plc
import Theorems.Thm_Formalism_DivisionValues_Rb_Cmap
import Theorems.Thm_Formalism_DivisionValues_Rb_gramStd
import Theorems.Thm_Formalism_DivisionValues_Rb_gramR_std
import Theorems.Thm_Formalism_DivisionValues_Rb_metMat_posDef
import Theorems.Thm_Formalism_DivisionValues_Rb_Qd_place
import Theorems.Thm_Formalism_DivisionValues_Rb_Qd_place_re
import Theorems.Thm_Formalism_DivisionValues_Rb_place_ineq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Rb
namespace Formalism.DivisionValues
theorem _root_.solution (hPF : ProdFormula) (hCS : DetCS) (hLB : LcvBasis) (hIC : IdxChange)
    (hVB : ValBasic) (hGC : GramChange) (hFC : FinsumConj) : LemmaRb := by
  intro K _ _ _ _ K0 hK0 v0 hv0 n D H hH hHpos P hP XQ hXQ M hM e he
  classical

  have hΛ : Submodule.IsLattice K (matLat P M) := by
    refine ⟨(Submodule.IsLattice.fg (self := hM)).map _, ?_⟩
    have : ((matLat P M : Submodule (𝓞 K) (Fin D → K)) : Set (Fin D → K)) =
        (Matrix.mulVecLin P) '' (M : Set (Fin n → K)) := by
      rw [matLat, Submodule.map_coe]
      rfl
    rw [this, Submodule.span_image, Submodule.IsLattice.span_eq_top (self := hM), Submodule.map_top,
      LinearMap.range_eq_top]
    exact hP

  have hli : LinearIndependent K (fun i => (Pi.single i 1 : Fin D → K)) := by
    have : (fun i => (Pi.single i 1 : Fin D → K)) = ⇑(Pi.basisFun K (Fin D)) := by
      funext i; simp [Pi.basisFun_apply]
    rw [this]
    exact (Pi.basisFun K (Fin D)).linearIndependent
  obtain ⟨hfin, hlcv⟩ := hLB K D XQ (fun v => (hXQ v).1) (matLat P M) hΛ _ hli

  have hG : gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K)) = (P * H⁻¹ * Pᴴ).det⁻¹ := by
    rw [gramR_std, quotGram, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hc : (P * H⁻¹ * Pᴴ).det ≠ 0 := by
    have htw0 : tw v0.embedding = v0.embedding := by
      ext a
      rw [tw_apply, hv0, starRingEnd_self_apply]
    have h0 : v0.embedding (P * H⁻¹ * Pᴴ).det = Qd P H v0.embedding := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, Cmap, htw0]
      rfl
    rw [Qd_place P H XQ hXQ v0] at h0
    have hne : ((metMat XQ v0).det)⁻¹ ≠ 0 :=
      inv_ne_zero (metMat_posDef XQ v0 (hXQ v0).1).det_pos.ne'
    intro hz
    rw [hz, map_zero] at h0
    exact hne h0.symm
  have hG0 : gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K)) ≠ 0 := by
    rw [hG]; exact inv_ne_zero hc
  obtain ⟨hGfin, hGpf⟩ := hPF K _ hG0

  have hpt : ∀ v : InfinitePlace K,
      Real.log (metMat XQ v).det.re + Real.log (metMat XQ (plc v)).det.re ≤
        2 * Real.log ‖v.embedding (gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K)))‖ := by
    intro v
    have hr := (Qd_place_re P H XQ hXQ v).2
    have hr' := (Qd_place_re P H XQ hXQ (plc v)).2
    have hi := place_ineq hCS K0 hK0 H hH hHpos P XQ hXQ hc v
    have e2 : 2 * Real.log ‖v.embedding (gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K)))‖ =
        Real.log ((‖v.embedding (P * H⁻¹ * Pᴴ).det‖ ^ 2)⁻¹) := by
      rw [hG, map_inv₀, norm_inv, Real.log_inv, Real.log_inv, Real.log_pow]
      push_cast
      ring
    rw [e2, ← Real.log_mul hr.ne' hr'.ne']
    exact Real.log_le_log (mul_pos hr hr') hi
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hpt v)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hperm : ∑ v : InfinitePlace K, Real.log (metMat XQ (plc v)).det.re =
      ∑ v : InfinitePlace K, Real.log (metMat XQ v).det.re :=
    Equiv.sum_comp (Function.Involutive.toPerm _ plc_plc) (fun v => Real.log (metMat XQ v).det.re)
  rw [hperm] at hsum
  have hmean : ∑ v, Real.log (gram XQ v (fun i => (Pi.single i 1 : Fin D → K))).det.re ≤
      ∑ v : InfinitePlace K,
        Real.log ‖v.embedding (gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K)))‖ := by
    simp only [gramStd]
    linarith
  have hinf : (2 / (finrank ℚ K : ℝ)) *
      ∑ v, Real.log (gram XQ v (fun i => (Pi.single i 1 : Fin D → K))).det.re ≤
      ∑ᶠ w, lw w * (vw w (gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K))) : ℝ) := by
    rw [← hGpf]
    exact mul_le_mul_of_nonneg_left hmean (by positivity)

  have hloc : ∀ w : HeightOneSpectrum (𝓞 K),
      lw w * (vw w (gramR (quotGram P H) (e w)) : ℝ) =
        lw w * (vw w (gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K))) : ℝ) +
        lw w * (idx w (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin D → K))))
          (matLat P M) : ℝ) +
        lw (conjPl w) * (idx (conjPl w)
          (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin D → K))))
          (matLat P M) : ℝ) := by
    intro w
    obtain ⟨hmul, hstar, hlw, -, -, -, -⟩ := hVB K w
    let γ : Matrix (Fin D) (Fin D) K := Matrix.of fun k i => e w i k
    have hew : (fun i => ∑ k, γ k i • (Pi.single k (1 : K) : Fin D → K)) = e w := by
      funext i j
      simp [γ, Finset.sum_apply, Pi.single_apply]
    have hdet : γ.det ≠ 0 := by
      have hu : IsUnit (Matrix.of (e w)) :=
        Matrix.linearIndependent_rows_iff_isUnit.mp (he w).1
      have : γ = (Matrix.of (e w))ᵀ := by ext k i; rfl
      rw [this, Matrix.det_transpose]
      exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
    have hlb : IsLocBasis (matLat P M) w (fun i => ∑ k, γ k i • (Pi.single k (1 : K) : Fin D → K)) := by
      rw [hew]; exact he w
    obtain ⟨hi1, hi2⟩ := hIC K D (matLat P M) hΛ _ hli w γ hlb
    have hgc : gramR (quotGram P H) (e w) =
        star γ.det * γ.det * gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K)) := by
      rw [← hew]
      exact hGC K D D _ _ γ
    rw [hgc, hmul _ _ (mul_ne_zero (star_ne_zero.mpr hdet) hdet) hG0,
      hmul _ _ (star_ne_zero.mpr hdet) hdet, hstar, hi1, hi2, hlw]
    push_cast
    ring
  have hinj : Function.Injective (conjPl : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K)) :=
    fun a b h => by rw [← (hVB K a).2.2.2.1, h, (hVB K b).2.2.2.1]
  have hfc : (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw (conjPl w) * (idx (conjPl w)
      (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin D → K)))) (matLat P M) : ℝ)).Finite :=
    hfin.preimage hinj.injOn
  have hfun : (fun w => lw w * (vw w (gramR (quotGram P H) (e w)) : ℝ)) = fun w =>
      lw w * (vw w (gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K))) : ℝ) +
        lw w * (idx w (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin D → K))))
          (matLat P M) : ℝ) +
        lw (conjPl w) * (idx (conjPl w)
          (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin D → K))))
          (matLat P M) : ℝ) := funext hloc
  have hfin2 := (hGfin.union hfin).subset (Function.support_add _ _)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (hfin2.union hfc).subset (Function.support_add _ _)
  · rw [hfun, finsum_add_distrib hfin2 hfc, finsum_add_distrib hGfin hfin,
      hFC K (fun w => lw w * (idx w
        (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin D → K)))) (matLat P M) : ℝ)),
      hlcv]
    linarith [hinf]
end Formalism.DivisionValues
