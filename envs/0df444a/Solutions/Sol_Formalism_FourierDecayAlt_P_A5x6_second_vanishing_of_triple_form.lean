-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x6.second_vanishing_of_triple_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:45.300837+00:00
-- url     : https://prove2.me/submissions/48bc64d1-f656-4272-9189-fbc9e105e2a9

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_addBlock_sum
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
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6
namespace Formalism.FourierDecayAlt.P.A5x6
theorem _root_.solution (hTF : TripleForm) (hAvg : AvgClaim) (hEnd : TTEnd) : BlockKernelSupport := by
  intro K _ _ _ R ψ hL s hs h h' t t' hsz hN
  have hKp : Kp R ψ (addBlock h s t) (addBlock h' s t') ≠ 0 := by
    intro h0; apply hN; simp [Ns, h0]
  have e1 : (addBlock h s t).1.sum = (h.1.sum + (s - 1)) + 1 := by rw [addBlock_sum]; omega
  have e2 : (addBlock h' s t').1.sum = (h.1.sum + (s - 1)) + 1 := by rw [addBlock_sum]; omega
  rw [hTF K R ψ _ _ _ e1 e2] at hKp
  have desc : ∀ d, d + 1 ≤ s → intTT R ψ (h.1.sum + d) (addBlock h s t) (addBlock h' s t') =
      intTT R ψ h.1.sum (addBlock h s t) (addBlock h' s t') := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      rw [← ih (by omega)]
      exact hAvg K R ψ hL h h' s t t' (h.1.sum + d) hsz (by omega) (by omega)
  rw [desc (s - 1) (by omega)] at hKp
  unfold intTT at hKp
  by_contra hcon
  apply hKp
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  split_ifs with hI
  · have : IsEmpty {φ : coker R (orbZ (addBlock h s t) (rep R q.1)) ≃ₗ[R]
        coker R (orbZ (addBlock h' s t') (rep R q.2)) //
        φ ∈ isoZZ R (orbZ (addBlock h s t) (rep R q.1)) (orbZ (addBlock h' s t') (rep R q.2)) ∧
        InTT R h.1.sum (orbZ (addBlock h s t) (rep R q.1))
          (orbZ (addBlock h' s t') (rep R q.2)) φ} := by
      constructor
      rintro ⟨φ, hφ, hT⟩
      exact hcon (hEnd K R h h' s t t' hsz hs _ _ _ _ (rep R q.1).1.2.1 (rep R q.1).2.2
        (rep R q.2).1.2.1 (rep R q.2).2.2 φ hφ hT)
    simp [Nat.card_of_isEmpty]
  · simp
end Formalism.FourierDecayAlt.P.A5x6
