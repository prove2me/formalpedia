-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.gauss_abs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:45.844073+00:00
-- url     : https://prove2.me/submissions/bab7e40b-08ef-4e0a-8eb0-a20034545f01

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
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
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x6
open Formalism.FourierDecayAlt.P.A5x5
namespace Formalism.FourierDecayAlt.P.A6x6
theorem _root_.solution {H : Type} [AddCommGroup H] [Fintype H] (F : H → ℂ) (B : H → H → ℂ)
    (hF : ∀ y w, F (y + w) = F y * F w * B y w)
    (hn : ∀ y, F y * conj (F y) = 1)
    (hB : ∀ w y y', B (y + y') w = B y w * B y' w)
    (hB0 : ∀ w, B 0 w = 1)
    (h1 : ∀ w, (∀ y, B y w = 1) → F w = 1) :
    (∑ y, F y) * conj (∑ y, F y) =
      (Nat.card H : ℂ) * (Nat.card {w : H // ∀ y, B y w = 1} : ℂ) := by
  classical
  have hχ : ∀ w, ∑ z, B z w = if ∀ y, B y w = 1 then (Fintype.card H : ℂ) else 0 := by
    intro w
    let χ : AddChar H ℂ := ⟨fun y => B y w, hB0 w, hB w⟩
    have h := AddChar.sum_eq_ite χ
    have e : χ = 0 ↔ ∀ y, B y w = 1 := by
      rw [DFunLike.ext_iff]; rfl
    simp only [e] at h
    exact h
  calc (∑ y, F y) * conj (∑ y, F y) = ∑ z, ∑ y, F y * conj (F z) := by
        rw [map_sum, Finset.sum_mul_sum, Finset.sum_comm]
    _ = ∑ z, ∑ w, F (z + w) * conj (F z) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        exact (Fintype.sum_equiv (Equiv.addLeft z) _ _ fun w => rfl).symm
    _ = ∑ z, ∑ w, F w * B z w := by
        refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
        rw [hF]; linear_combination (F w * B z w) * hn z
    _ = ∑ w, F w * ∑ z, B z w := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ = ∑ w, if ∀ y, B y w = 1 then (Fintype.card H : ℂ) else 0 := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hχ]; split_ifs with h
        · rw [h1 w h, one_mul]
        · simp
    _ = _ := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card,
          Nat.card_eq_fintype_card, Fintype.card_subtype, mul_comm]
end Formalism.FourierDecayAlt.P.A6x6
