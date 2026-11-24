-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.phase_function_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:25:53.540042+00:00
-- url     : https://prove2.me/submissions/0c0a20dd-bebd-461b-b76b-23611c9287e5

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hs_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hs_zero_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_Rw
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_coef
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hs_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_word_adj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hs_listSum_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hs_listSum_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_integral_listSum
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_len_le_order
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_rho

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.B5
namespace _root_.Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B.StepPhAdj := by
  intro k r Wp Wq _ _ _ _ _ _ D UU Θ _hUU hsm hcom F F' hF hF' _hsF hsF' hIC p hp
  have hf : CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) (rho D p F) := ckOn_rho D hp hF
  have hφ : ∀ T ∈ Θ, CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) (fun x => T.coefAdj x (F' x)) :=
    fun T hT => ckOn_coef (hsm T hT).2 hF' hsF'
  have hleft : Ph D (opApply Θ F) F' p = ∫ g : Mt k r, (Θ.map fun T =>
      hsInner (Rw T.word (rho D p F) (Matrix.of g)) (T.coefAdj (Matrix.of g) (F' (Matrix.of g)))).sum ∂D.μG := by
    unfold Ph
    apply integral_congr_ae
    filter_upwards [haar_ae D.haarG] with g hg
    by_cases hgU : (Matrix.of g : Mat k r) ∈ UU
    · rw [← hcom p hp F (ckOn_mono (by exact_mod_cast Nat.le_add_right _ _) hF) _ hgU]
      unfold opApply
      rw [hs_listSum_left]
      simp only [DTerm.adj_id]
    · have h0 : F' (Matrix.of g) = 0 := by
        by_contra hne
        exact hgU (hsF' (subset_closure ⟨hg, hne⟩))
      rw [h0, hs_zero_right]
      simp [hs_zero_right]
  have hright : Ph D F (opAdj Θ F') p = ∫ g : Mt k r, (Θ.map fun T => (-1 : ℂ) ^ T.word.length *
      hsInner (rho D p F (Matrix.of g))
        (Rw T.word.reverse (fun x => T.coefAdj x (F' x)) (Matrix.of g))).sum ∂D.μG := by
    unfold Ph
    congr 1
    funext g
    unfold opAdj
    rw [hs_listSum_right]
    congr 1
    apply List.map_congr_left
    intro T _
    rw [hs_smul_right]
    simp
  have hlen : ∀ T ∈ Θ, T.word.length + 1 ≤ opOrder Θ + 5 := fun T hT => by
    have := len_le_order Θ hT; omega
  have hIl : ∀ T ∈ Θ, Integrable (fun g : Mt k r =>
      hsInner (Rw T.word (rho D p F) (Matrix.of g)) (T.coefAdj (Matrix.of g) (F' (Matrix.of g)))) D.μG := by
    intro T hT
    refine hs_integrable D (B := fun x => T.coefAdj x (F' x))
      (ckOn_continuousOn (ckOn_Rw hf T.word T.word_lie 0 (by have := hlen T hT; omega)))
      (ckOn_continuousOn (hφ T hT)) ?_
    simpa [Rw] using hIC p hp T hT 0 0 le_rfl (Nat.zero_le _)
  have hIr : ∀ T ∈ Θ, Integrable (fun g : Mt k r => (-1 : ℂ) ^ T.word.length *
      hsInner (rho D p F (Matrix.of g))
        (Rw T.word.reverse (fun x => T.coefAdj x (F' x)) (Matrix.of g))) D.μG := by
    intro T hT
    refine (hs_integrable D (ckOn_continuousOn hf)
      (ckOn_continuousOn (ckOn_Rw (hφ T hT) T.word.reverse
        (fun X hX => T.word_lie X (List.mem_reverse.1 hX)) 0
        (by have := hlen T hT; simp only [List.length_reverse]; omega))) ?_).const_mul _
    simpa [Rw] using hIC p hp T hT T.word.length T.word.length le_rfl le_rfl
  rw [hleft, hright, (integral_listSum D.μG Θ _ hIl).2, (integral_listSum D.μG Θ _ hIr).2]
  congr 1
  apply List.map_congr_left
  intro T hT
  have := word_adj D T.word T.word_lie (hlen T hT) hf (hφ T hT) (hIC p hp T hT) T.word.length le_rfl
  rw [this, integral_const_mul]
  simp [Rw]
end _root_.Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P.B5
