-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.fibre_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:12.0478+00:00
-- url     : https://prove2.me/submissions/aaaf3a8a-7463-46b9-bd18-4642d51e18a2

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_base_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_fib_core
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
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
noncomputable section
variable {K : Type} [CommRing K] (R : Subring K)
open Classical
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (ψ : AddChar K ℂ) (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (hun : ∀ x : K, conj (ψ x) = ψ (-x))
    (hfin : ∀ (m : ℕ) (Z : Matrix (Fin m) (Fin m) K), IsInt R Z → IsUnit Z.det →
      Finite (coker R Z))
    (h h' : Point K) (s : ℕ) (t t' : Kˣ) (k : ℕ) (hh : h.1.sum = h'.1.sum) (hk : h.1.sum ≤ k)
    (hks : k + 2 ≤ h.1.sum + s)
    (Q : Finset (Cos R (addBlock h s t) × Cos R (addBlock h' s t')))
    (hQ : ∀ q, q ∈ Q ↔ IsInt R (orbZ (addBlock h s t) (rep R q.1)) ∧
      IsInt R (orbZ (addBlock h' s t') (rep R q.2))) (y) (y') :
    ∑ q ∈ Q with (kap R k (addBlock h s t) q.1 = y ∧ kap R k (addBlock h' s t') q.2 = y'),
      (badN R k (addBlock h s t) (addBlock h' s t') q : ℂ) *
        (phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))) = 0 := by
  have hs : 1 ≤ s := by omega
  have hsum : (addBlock h s t).1.sum = h.1.sum + s := by simp [addBlock]
  have hsum' : (addBlock h' s t').1.sum = h'.1.sum + s := by simp [addBlock]
  exact fib_core R ψ hsd hun hfin (addBlock h s t) (addBlock h' s t') k (by rw [hsum, hsum', hh])
    (by rw [hsum]; exact hks) Q hQ y y'
    (fun a b ha hb => base_last R k h s t hs hk y a b ha hb)
    (fun a b ha hb => base_last R k h' s t' hs (hh ▸ hk) y' a b ha hb)
end Formalism.FourierDecayAlt.P.A5x9
