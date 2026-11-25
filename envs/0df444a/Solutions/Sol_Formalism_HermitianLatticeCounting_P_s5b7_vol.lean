-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_vol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:03:28.246565+00:00
-- url     : https://prove2.me/submissions/6278e7df-788a-458f-a52a-ec83a5c8a634

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_exists_iso
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_radial
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_A_closed
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_mp
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_slice
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_real_ineq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (R : ℝ) (hR : 0 < R) : ∀ (r d : ℕ), r ≤ d → ∀ t : ℝ, 0 ≤ t →
    volume (s5b7_A R d r t) ≤ ENNReal.ofReal (t ^ (2 * (d - r)) * R ^ (2 * r ^ 2) *
      Real.pi ^ (r * d) / ((d - r).factorial : ℝ) ^ r) := by
  intro r
  induction r with
  | zero =>
    intro d _ t ht
    by_cases h1 : 1 ≤ t
    · calc volume (s5b7_A R d 0 t) ≤ volume (univ : Set (Fin 0 → EuclideanSpace ℂ (Fin d))) :=
            measure_mono (subset_univ _)
        _ = 1 := by rw [Measure.volume_pi_eq_dirac 0]; simp
        _ ≤ _ := by
            rw [← ENNReal.ofReal_one]
            apply ENNReal.ofReal_le_ofReal
            simp only [pow_zero, mul_one, zero_mul, div_one, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
              not_false_eq_true, zero_pow]
            exact one_le_pow₀ h1
    · have : s5b7_A R d 0 t = ∅ := by
        ext a
        simp only [s5b7_A, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro _
        simpa using h1
      rw [this]; simp
  | succ r ih =>
    intro d hd t ht
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have hr : r ≤ d := by omega
    have hs' : d + 1 - (r + 1) = d - r := by omega
    rw [hs']
    set s := d - r with hs
    let e := MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (r + 1) => EuclideanSpace ℂ (Fin (d + 1))) 0
    have he : MeasurePreserving e := volume_preserving_piFinSuccAbove
      (fun _ : Fin (r + 1) => EuclideanSpace ℂ (Fin (d + 1))) 0
    have hAm : MeasurableSet (s5b7_A R (d + 1) (r + 1) t) := (s5b7_A_closed _ _ _ _).measurableSet
    have hes : ∀ (x : EuclideanSpace ℂ (Fin (d + 1))) (a' : Fin r → EuclideanSpace ℂ (Fin (d + 1))),
        e.symm (x, a') = Fin.cons x a' := by
      intro x a'
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      exact Fin.insertNth_zero' x a'
    have hvol : volume (s5b7_A R (d + 1) (r + 1) t) =
        ∫⁻ x, volume (Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t)) := by
      rw [← (he.symm e).measure_preimage hAm.nullMeasurableSet, Measure.volume_eq_prod,
        Measure.prod_apply (e.symm.measurable hAm)]
    rw [hvol]
    set C1 : ℝ := (R ^ 2 * Real.pi) ^ r * (t ^ (2 * s) * R ^ (2 * r ^ 2) * Real.pi ^ (r * d) /
        (s.factorial : ℝ) ^ r) with hC1def
    have hC1 : 0 ≤ C1 := by positivity
    have hbound : ∀ᵐ x : EuclideanSpace ℂ (Fin (d + 1)),
        volume (Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t)) ≤
          ENNReal.ofReal C1 * ENNReal.ofReal (if ‖x‖ ≤ R then (‖x‖ ^ (2 * s))⁻¹ else 0) := by
      have h0 : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin (d + 1)))) ∈ ae volume :=
        compl_mem_ae_iff.mpr (measure_singleton 0)
      filter_upwards [h0] with x hx
      have hx : x ≠ 0 := hx
      by_cases hxR : ‖x‖ ≤ R
      · rw [if_pos hxR]
        have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
        obtain ⟨Φ, hΦ⟩ := s5b7_exists_iso d (((‖x‖⁻¹ : ℝ) : ℂ) • x) (by
          rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hx0.ne'])
        set S : Set ((Fin r → ℂ) × (Fin r → EuclideanSpace ℂ (Fin d))) :=
          (Set.pi univ fun _ => Metric.closedBall (0 : ℂ) R) ×ˢ s5b7_A R d r (t / ‖x‖) with hS
        have hsub : Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t) ⊆
            (fun a : Fin r → EuclideanSpace ℂ (Fin (d + 1)) =>
              ((fun b => (Φ (a b)).ofLp.1), (fun b => (Φ (a b)).ofLp.2))) ⁻¹' S := by
          intro a' ha'
          have ha'' : (Fin.cons x a' : Fin (r + 1) → EuclideanSpace ℂ (Fin (d + 1))) ∈
              s5b7_A R (d + 1) (r + 1) t := by
            rw [← hes]; exact ha'
          obtain ⟨h1, h2⟩ := s5b7_slice R d r t x hx Φ hΦ a' ha''
          exact ⟨fun b _ => by simpa using h1 b, h2⟩
        have hSm : MeasurableSet S :=
          (MeasurableSet.univ_pi fun _ => Metric.isClosed_closedBall.measurableSet).prod
            (s5b7_A_closed _ _ _ _).measurableSet
        have hball : volume (Set.pi univ fun _ : Fin r => Metric.closedBall (0 : ℂ) R) =
            ENNReal.ofReal ((R ^ 2 * Real.pi) ^ r) := by
          rw [volume_pi_pi]
          simp only [Complex.volume_closedBall, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_pow hR.le]
          congr 2
          exact (ENNReal.ofReal_coe_nnreal (p := NNReal.pi)).symm
        calc volume (Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t))
            ≤ volume ((fun a : Fin r → EuclideanSpace ℂ (Fin (d + 1)) =>
              ((fun b => (Φ (a b)).ofLp.1), (fun b => (Φ (a b)).ofLp.2))) ⁻¹' S) :=
              measure_mono hsub
          _ = volume S := (s5b7_mp d r Φ).measure_preimage hSm.nullMeasurableSet
          _ = volume (Set.pi univ fun _ : Fin r => Metric.closedBall (0 : ℂ) R) *
                volume (s5b7_A R d r (t / ‖x‖)) := by
              rw [hS, Measure.volume_eq_prod, Measure.prod_prod]
          _ ≤ ENNReal.ofReal ((R ^ 2 * Real.pi) ^ r) *
                ENNReal.ofReal ((t / ‖x‖) ^ (2 * s) * R ^ (2 * r ^ 2) * Real.pi ^ (r * d) /
                  (s.factorial : ℝ) ^ r) := by
              rw [hball]
              gcongr
              exact ih d hr _ (by positivity)
          _ = ENNReal.ofReal C1 * ENNReal.ofReal ((‖x‖ ^ (2 * s))⁻¹) := by
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC1]
              congr 1
              rw [hC1def, div_pow]
              field_simp
      · have : Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t) = ∅ := by
          ext a'
          simp only [mem_preimage, mem_empty_iff_false, iff_false]
          rw [hes]
          intro h
          exact hxR (by simpa using h.1 0)
        rw [this]; simp
    calc ∫⁻ x, volume (Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t))
        ≤ ∫⁻ x : EuclideanSpace ℂ (Fin (d + 1)),
            ENNReal.ofReal C1 * ENNReal.ofReal (if ‖x‖ ≤ R then (‖x‖ ^ (2 * s))⁻¹ else 0) :=
          lintegral_mono_ae hbound
      _ = ENNReal.ofReal C1 * ∫⁻ x : EuclideanSpace ℂ (Fin (d + 1)),
            ENNReal.ofReal (if ‖x‖ ≤ R then (‖x‖ ^ (2 * s))⁻¹ else 0) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal C1 * ENNReal.ofReal
            (Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1)) := by
          rw [hs, s5b7_radial d r hr R hR]
      _ = ENNReal.ofReal (C1 *
            (Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1))) :=
          (ENNReal.ofReal_mul hC1).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (s5b7_real_ineq R t hR ht r d s (Nat.sub_le d r))
end Formalism.HermitianLatticeCounting.P
