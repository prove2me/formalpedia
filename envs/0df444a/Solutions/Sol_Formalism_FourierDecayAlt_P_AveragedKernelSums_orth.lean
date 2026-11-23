-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AveragedKernelSums.orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:38.107432+00:00
-- url     : https://prove2.me/submissions/67364fb7-7954-44d3-80b6-6ce79d1621bf

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_psi_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_mem_out
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
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



set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.AveragedKernelSums
open Formalism.FourierDecayAlt.P.A5x6
variable {K : Type} [CommRing K] {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.AveragedKernelSums
theorem _root_.solution (hψ : ∀ r ∈ R, ψ r = 1) {P : AddSubgroup K} (hRP : R.toAddSubgroup ≤ P)
    (Tf : Finset (K ⧸ R.toAddSubgroup)) (hTf : ∀ x, x ∈ Tf ↔ Quotient.out x ∈ P) {c z₀ : K}
    (hc : c ∈ R) (hz : z₀ ∈ P) (hne : ψ (z₀ * c) ≠ 1) :
    ∑ x ∈ Tf, ψ (Quotient.out x * c) = 0 := by
  have hx : ∀ x : K ⧸ R.toAddSubgroup, x + ((z₀ : K) : K ⧸ R.toAddSubgroup) =
      ((Quotient.out x + z₀ : K) : K ⧸ R.toAddSubgroup) := by
    intro x
    rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
  have hs : ∑ x ∈ Tf, ψ (Quotient.out (x + ((z₀ : K) : K ⧸ R.toAddSubgroup)) * c) =
      ∑ x ∈ Tf, ψ (Quotient.out x * c) := by
    refine Finset.sum_equiv (Equiv.addRight ((z₀ : K) : K ⧸ R.toAddSubgroup)) ?_ ?_
    · intro x
      show x ∈ Tf ↔ x + ((z₀ : K) : K ⧸ R.toAddSubgroup) ∈ Tf
      rw [hTf, hTf, hx, mem_out hRP, P.add_mem_cancel_right hz]
    · intro x _
      rfl
  have hv : ∀ x : K ⧸ R.toAddSubgroup,
      ψ (Quotient.out (x + ((z₀ : K) : K ⧸ R.toAddSubgroup)) * c) =
        ψ (Quotient.out x * c) * ψ (z₀ * c) := by
    intro x
    rw [hx, psi_out hψ hc, add_mul, AddChar.map_add_eq_mul]
  simp only [hv] at hs
  rw [← Finset.sum_mul] at hs
  have h0 : (∑ x ∈ Tf, ψ (Quotient.out x * c)) * (ψ (z₀ * c) - 1) = 0 := by
    rw [mul_sub, hs, mul_one, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hne
end Formalism.FourierDecayAlt.P.AveragedKernelSums
