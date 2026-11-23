-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.cutNormEval_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:10.855599+00:00
-- url     : https://prove2.me/submissions/a9a90aa7-8164-475a-a472-2af5e513c135

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedVectorChoices
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_finite_cosets
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_out_sub_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_card_reps
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_intLat_eq_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_mean_prod
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
namespace Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
theorem _root_.solution : CutNormEval := by
  intro hCM hPL K _ _ _ R ψ hD hn s F Om Lc D hOc z₁ hz₁ h hh h' hh'
  classical
  obtain ⟨hPlat, _, hvol⟩ := hPL K R ψ hD hn D.L₂ D.lat₂
  have hfin := finite_cosets (perp ψ D.L₂) hPlat.1 Om hOc
  set T := hfin.toFinset with hT
  set f := NsK R ψ s h h' with hf
  set c : ℂ := ((D.A.card : ℂ) * (D.B.card : ℂ))⁻¹ with hc
  have hcc : conj c = c := by
    rw [hc, map_inv₀, map_mul, Complex.conj_natCast, Complex.conj_natCast]

  have hv : (volL R (perp ψ D.L₂) : ℂ) = (D.A.card : ℂ)⁻¹ := by
    have h1 : volL R D.L₂ = (D.A.card : ℝ) := by
      unfold volL
      rw [← card_reps D.L₂ R.toAddSubgroup D.A D.repsA, AddSubgroup.relIndex_eq_one.2 D.le₂]
      simp
    rw [h1] at hvol
    have : volL R (perp ψ D.L₂) = (D.A.card : ℝ)⁻¹ := eq_inv_of_mul_eq_one_right hvol
    rw [this]; push_cast; rfl

  have step : ∀ p p' : K × K, ψ (-(z₁ * (p.1 + p.2))) * conj (ψ (-(z₁ * (p'.1 + p'.2)))) *
      intLat R (perp ψ D.L₂) Om (fun z => f z * ψ (z * ((p.1 + p.2) - (p'.1 + p'.2)))) =
      (volL R (perp ψ D.L₂) : ℂ) * ∑ y ∈ T, f (Quotient.out y) *
        (ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)) *
          conj (ψ (((Quotient.out y : K) - z₁) * (p'.1 + p'.2)))) := by
    intro p p'
    rw [intLat_eq_sum R _ Om hfin, mul_left_comm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    have : ψ (-(z₁ * (p.1 + p.2))) * ψ (-(-(z₁ * (p'.1 + p'.2)))) *
        ψ ((Quotient.out y : K) * ((p.1 + p.2) - (p'.1 + p'.2))) =
        ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)) *
          ψ (-(((Quotient.out y : K) - z₁) * (p'.1 + p'.2))) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1; ring
    rw [hD.unitary, hD.unitary, ← this]
    ring
  simp only [step]
  have swap : ∑ p ∈ D.A ×ˢ D.B, ∑ p' ∈ D.A ×ˢ D.B, (volL R (perp ψ D.L₂) : ℂ) *
      ∑ y ∈ T, f (Quotient.out y) * (ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)) *
          conj (ψ (((Quotient.out y : K) - z₁) * (p'.1 + p'.2)))) =
      (volL R (perp ψ D.L₂) : ℂ) * ∑ y ∈ T, f (Quotient.out y) *
        ((∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2))) *
          conj (∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)))) := by
    simp only [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [map_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
  rw [swap]
  have ind : ∀ y ∈ T, c * ∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)) =
      if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then 1 else 0 := by
    intro y hy
    rw [hT, Set.Finite.mem_toFinset] at hy
    exact mean_prod hCM R ψ D.L₁ D.L₂ D.A D.B D.le₁ D.le₂ D.repsA D.repsB _
      ((perp ψ D.L₁).sub_mem (D.omPerp _ hy) (D.omPerp _ hz₁))
  have e3 : c ^ 2 * ((volL R (perp ψ D.L₂) : ℂ) * ∑ y ∈ T, f (Quotient.out y) *
        ((∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2))) *
          conj (∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2))))) =
      (volL R (perp ψ D.L₂) : ℂ) * ∑ y ∈ T, f (Quotient.out y) *
        (if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then 1 else 0) := by
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    have h1 := ind y hy
    have h3 : (if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then (1 : ℂ) else 0) =
        (if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then (1 : ℂ) else 0) *
          conj (if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then (1 : ℂ) else 0) := by
      split_ifs <;> simp
    rw [h3, ← h1, map_mul, hcc]
    ring
  rw [e3, hv]
  congr 1
  have hout := out_sub_mem (perp ψ D.L₂) z₁
  have houteq : (Quotient.out ((z₁ : K) : K ⧸ perp ψ D.L₂) : K) =
      z₁ + ((Quotient.out ((z₁ : K) : K ⧸ perp ψ D.L₂) : K) - z₁) := by ring
  rw [Finset.sum_eq_single ((z₁ : K) : K ⧸ perp ψ D.L₂)]
  · rw [if_pos hout, mul_one, houteq]
    exact D.nsInv h hh h' hh' z₁ hz₁ _ hout
  · intro y _ hy
    rw [if_neg, mul_zero]
    intro hm
    apply hy
    rw [← QuotientAddGroup.out_eq' y, QuotientAddGroup.eq]
    have := (perp ψ D.L₂).neg_mem hm
    simpa [sub_eq_add_neg, add_comm] using this
  · intro hn'
    exfalso
    apply hn'
    rw [hT, Set.Finite.mem_toFinset]
    show (Quotient.out ((z₁ : K) : K ⧸ perp ψ D.L₂) : K) ∈ Om
    rw [houteq]
    exact D.omStable z₁ hz₁ _ hout
end Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
