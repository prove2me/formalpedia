-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.word_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:03:28.425879+00:00
-- url     : https://prove2.me/submissions/f521de0b-33e0-4072-a830-daa78ae2aa20

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_RdV
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_Rw
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hs_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ibp
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_ibp


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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B5
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (w : List (Mat k r)) (hw : ∀ X ∈ w, inLie k r X) {N : ℕ}
    (hN : w.length + 1 ≤ N) {f φ : Mat k r → (Wq →L[ℂ] Wp)} (hf : CkOn (N : ℕ∞) (GV k r) f)
    (hφ : CkOn (N : ℕ∞) (GV k r) φ)
    (hI : ∀ i j : ℕ, i ≤ j → j ≤ w.length → Integrable (fun g : Mt k r =>
      ‖Rw (w.take i).reverse φ (Matrix.of g)‖ * ‖Rw (w.drop j) f (Matrix.of g)‖) D.μG)
    (j : ℕ) (hj : j ≤ w.length) :
    (∫ g : Mt k r, hsInner (Rw w f (Matrix.of g)) (φ (Matrix.of g)) ∂D.μG) =
      (-1) ^ j * ∫ g : Mt k r, hsInner (Rw (w.drop j) f (Matrix.of g))
        (Rw (w.take j).reverse φ (Matrix.of g)) ∂D.μG := by
  induction j with
  | zero =>
    simp only [List.drop_zero, List.take_zero, List.reverse_nil, pow_zero, one_mul]
    rfl
  | succ j ih =>
    have hjl : j < w.length := by omega
    have hX : inLie k r w[j] := hw _ (List.getElem_mem hjl)
    have hd : w.drop j = w[j] :: w.drop (j + 1) := List.drop_eq_getElem_cons hjl
    have ht : (w.take (j + 1)).reverse = w[j] :: (w.take j).reverse := by
      rw [List.take_succ, List.getElem?_eq_getElem hjl]
      simp
    have hwd : ∀ Y ∈ w.drop (j + 1), inLie k r Y := fun Y hY => hw Y (List.mem_of_mem_drop hY)
    have hwt : ∀ Y ∈ (w.take j).reverse, inLie k r Y :=
      fun Y hY => hw Y (List.mem_of_mem_take (List.mem_reverse.1 hY))
    have h1 : CkOn 1 (GV k r) (Rw (w.drop (j + 1)) f) := by
      have h0 := ckOn_Rw hf (w.drop (j + 1)) hwd 1 (by simp; omega)
      exact_mod_cast h0
    have h2 : CkOn 1 (GV k r) (Rw (w.take j).reverse φ) := by
      have h0 := ckOn_Rw hφ ((w.take j).reverse) hwt 1 (by simp; omega)
      exact_mod_cast h0
    have c1 := ckOn_continuousOn h1
    have c2 := ckOn_continuousOn h2
    have c3 := ckOn_continuousOn (ckOn_RdV (m := 0) hX (by simpa using h1))
    have c4 := ckOn_continuousOn (ckOn_RdV (m := 0) hX (by simpa using h2))
    have i0 := hs_integrable D c1 c2 (hI j (j + 1) (by omega) (by omega))
    have hI1 := hI j j le_rfl (by omega)
    rw [hd] at hI1
    have i1 := hs_integrable D c3 c2 hI1
    have hI2 := hI (j + 1) (j + 1) le_rfl (by omega)
    rw [ht] at hI2
    have i2 := hs_integrable D c1 c4 hI2
    have key := ibp D hX h1 h2 i0 i1 i2
    rw [ih (by omega), hd, ht]
    have key' : (∫ g : Mt k r, hsInner (Rw (w[j] :: w.drop (j + 1)) f (Matrix.of g))
        (Rw (w.take j).reverse φ (Matrix.of g)) ∂D.μG) =
        -∫ g : Mt k r, hsInner (Rw (w.drop (j + 1)) f (Matrix.of g))
          (Rw (w[j] :: (w.take j).reverse) φ (Matrix.of g)) ∂D.μG := key
    rw [key']
    ring
end Formalism.FourierDecayAlt.P.B5
