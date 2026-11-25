-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.latticeHerglotzBound_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:26:07.774433+00:00
-- url     : https://prove2.me/submissions/8ca673fe-5390-4cb8-ae92-7d7ad815951d

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PairingTriangular
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PairingConjugationLemmas__d_sub_6e4cc9e6dfa7
import Theorems.Thm_Formalism_FourierDecayAlt_P_PairingConjugationLemmas_eD_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_PairingConjugationLemmas_Tl_emb
import Theorems.Thm_Formalism_FourierDecayAlt_P_PairingConjugationLemmas_vol_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PairingConjugationLemmas_covol_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_herglotz_lower_semicontinuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open MeasureTheory Filter Topology Finset Module Formalism.FourierDecayAlt.crystallineComparison Formalism.FourierDecayAlt.P.PairingConjugationLemmas
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.crystallineComparison.LatticeHerglotzBound := by
  intro f La _ _ N A hN0 hlsc hint hPD hsum z₀ S hS
  obtain ⟨c, hcpos, hc⟩ := vol_eq La
  have hcR : (0 : ℝ) < c := hcpos
  have hcov := covol_eq La c hc
  set T := Tl La with hT

  have hint_tr : ∀ g : V f → ℂ, ∫ z, g z = (c : ℂ) * ∫ y, g (T y) := by
    intro g
    rw [hc, integral_smul_nnreal_measure, (Tl_emb La).integral_map, NNReal.smul_def, Complex.real_smul]

  set N' : (Fin (finrank ℤ La) → ℝ) → ℝ := fun y => N (T y) with hN'
  set A' : (Fin (finrank ℤ La) → ℤ) → ℂ := fun m => A (ψd La m) / (c : ℂ) with hA'
  have hN'0 : ∀ y, 0 ≤ N' y := fun y => hN0 _
  have hlsc' : LowerSemicontinuous N' := hlsc.comp T.continuous
  have hint' : Integrable N' := by
    have h1 : Integrable N (Measure.map T volume) := by
      have := hint.smul_measure_nnreal (c := c⁻¹)
      rwa [hc, smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul] at this
    exact ((Tl_emb La).integrable_map_iff).1 h1
  have hk : ∀ m : Fin (finrank ℤ La) → ℤ,
      (∫ y, (N' y : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ∑ j, ((m j : ℝ) : ℂ) * (y j : ℂ))) + A' m =
        (crystallineComparison.fourier N (ψd La m) + A (ψd La m)) / (c : ℂ) := by
    intro m
    have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hcR.ne'
    have h1 : crystallineComparison.fourier N (ψd La m) = (c : ℂ) *
        ∫ y, (N' y : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ∑ j, ((m j : ℝ) : ℂ) * (y j : ℂ)) := by
      unfold crystallineComparison.fourier
      rw [hint_tr]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
      simp only [hN']
      rw [psi_ψd_Tl]
    rw [h1, hA']
    field_simp
  have hPD' : ∀ (S0 : Finset (Fin (finrank ℤ La) → ℤ)) (c0 : (Fin (finrank ℤ La) → ℤ) → ℂ),
      0 ≤ (∑ σ ∈ S0, ∑ σ' ∈ S0, A' (σ - σ') * c0 σ * starRingEnd ℂ (c0 σ')).re := by
    intro S0 c0
    have hinj := ψd_inj La
    have h := hPD (S0.image (ψd La)) (c0 ∘ Function.invFun (ψd La)) (by
      intro σ hσ
      obtain ⟨m, _, rfl⟩ := Finset.mem_image.1 hσ
      exact ψd_mem La m)
    have hsi : ∀ F : V f → ℂ, ∑ x ∈ S0.image (ψd La), F x = ∑ m ∈ S0, F (ψd La m) :=
      fun F => Finset.sum_image (by intro x _ y _ h; exact hinj h)
    simp only [hsi] at h
    simp only [Function.comp_apply, Function.leftInverse_invFun hinj _, ← ψd_sub] at h
    have e : (∑ σ ∈ S0, ∑ σ' ∈ S0, A' (σ - σ') * c0 σ * starRingEnd ℂ (c0 σ')) =
        (∑ σ ∈ S0, ∑ σ' ∈ S0, A (ψd La (σ - σ')) * c0 σ * starRingEnd ℂ (c0 σ')) / ((c : ℝ) : ℂ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun σ' _ => ?_)
      rw [hA']
      ring
    rw [e, Complex.div_ofReal_re]
    exact div_nonneg h hcR.le
  have hsum' : Summable (fun m : Fin (finrank ℤ La) → ℤ =>
      ‖(∫ y, (N' y : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ∑ j, ((m j : ℝ) : ℂ) * (y j : ℂ))) + A' m‖) := by
    simp_rw [hk]
    have h := (Equiv.summable_iff (eD La)).2 hsum
    refine (h.div_const (c : ℝ)).congr (fun m => ?_)
    simp only [Function.comp_apply, eD_apply, norm_div]
    congr 1
    simp

  set z₀' := T.symm z₀ with hz₀'
  let κ : V f → (Fin (finrank ℤ La) → ℤ) := fun z j => ⌊(bR La).repr (z - z₀) j⌋
  have hκ : ∀ z ∈ S, (fun j => ((κ z j : ℤ) : ℝ)) = T.symm (z - z₀) := by
    intro z hz
    have hm := (mem_iff La (z - z₀)).1 (hS z hz)
    rw [hT, Tl_symm_apply]
    funext j
    obtain ⟨n, hn⟩ := hm j
    simp only [κ, ← hn, algebraMap_int_eq, eq_intCast, Int.floor_intCast]
  have hκinj : ∀ x ∈ S, ∀ y ∈ S, κ x = κ y → x = y := by
    intro x hx y hy h
    have h1 := hκ x hx
    rw [h, hκ y hy] at h1
    have h2 := T.symm.injective h1
    simpa using h2.symm
  have H := Formalism.FourierDecayAlt.P.herglotz_lower_semicontinuous (finrank ℤ La) N' A' hN'0 hlsc' hint' hPD' hsum' z₀' (S.image κ)
  rw [Finset.sum_image (by intro x hx y hy h; exact hκinj x hx y hy h)] at H
  have hL : ∀ z ∈ S, N' (fun j => z₀' j + ((κ z j : ℤ) : ℝ)) = N z := by
    intro z hz
    have e1 : (fun j => z₀' j + ((κ z j : ℤ) : ℝ)) = z₀' + T.symm (z - z₀) := by
      rw [← hκ z hz]
      rfl
    simp only [hN']
    rw [e1, map_add, hz₀', ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
    congr 1
    abel
  rw [Finset.sum_congr rfl hL] at H
  have hR : (∑' m : Fin (finrank ℤ La) → ℤ,
      ‖(∫ y, (N' y : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ∑ j, ((m j : ℝ) : ℂ) * (y j : ℂ))) + A' m‖) =
      (∑' σ : dualSet La, ‖crystallineComparison.fourier N σ + A (σ : V f)‖) / (c : ℝ) := by
    simp_rw [hk]
    rw [← Equiv.tsum_eq (eD La), ← tsum_div_const]
    refine tsum_congr (fun m => ?_)
    rw [eD_apply, norm_div]
    congr 1
    simp
  rw [hR, le_div_iff₀ hcR] at H
  rw [hcov]
  linarith
end Formalism.FourierDecayAlt.P
