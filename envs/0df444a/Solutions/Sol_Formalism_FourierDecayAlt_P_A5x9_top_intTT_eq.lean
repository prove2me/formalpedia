-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.top_intTT_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:39.18077+00:00
-- url     : https://prove2.me/submissions/bfea6fca-fd8f-479d-968c-deffdb45730d

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
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
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (ψ : AddChar K ℂ) (k₁ : ℕ) (w w' : Point K)
    (Q : Finset (Cos R w × Cos R w'))
    (hQ : ∀ q, q ∈ Q ↔ IsInt R (orbZ w (rep R q.1)) ∧ IsInt R (orbZ w' (rep R q.2))) :
    intTT R ψ k₁ w w' = ∑ q ∈ Q,
      (Nat.card {φ : coker R (orbZ w (rep R q.1)) ≃ₗ[R] coker R (orbZ w' (rep R q.2)) //
        φ ∈ isoZZ R (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) ∧
        InTT R k₁ (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) φ} : ℂ) *
      (phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))) := by
  unfold intTT
  rw [finsum_eq_sum_of_support_subset (s := Q)]
  · refine Finset.sum_congr rfl fun q hq => ?_
    rw [if_pos ((hQ q).1 hq), mul_assoc]
  · intro q hq
    by_contra hn
    apply hq
    have hn' : ¬ (IsInt R (orbZ w (rep R q.1)) ∧ IsInt R (orbZ w' (rep R q.2))) :=
      fun hh => hn (Finset.mem_coe.2 ((hQ q).2 hh))
    simp only
    rw [if_neg hn', zero_mul, zero_mul]
end Formalism.FourierDecayAlt.P.A5x9
