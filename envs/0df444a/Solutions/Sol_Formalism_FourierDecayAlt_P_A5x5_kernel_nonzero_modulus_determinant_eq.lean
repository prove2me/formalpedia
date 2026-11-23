-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.kernel_nonzero_modulus_determinant_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:23.335823+00:00
-- url     : https://prove2.me/submissions/db6ac3dd-2edd-4c07-a725-bb4985b66320

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_cokernel_finite_card_eq_inv_modulus
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_det_orbZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_isUnit_det_pt
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


attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply

set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {R : Subring K}
variable [TopologicalSpace K] [IsTopologicalRing K] {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution (hd : LocalDatum K R ψ) (w w' : Point K) (h : Kp R ψ w w' ≠ 0) :
    modK R (pt w.1 w.2).det = modK R (pt w'.1 w'.2).det := by
  obtain ⟨q, hq⟩ : ∃ q, pairTerm R ψ w w' q ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (finsum_eq_zero_of_forall_eq_zero hc)
  unfold pairTerm at hq
  by_cases hc : IsInt R (orbZ w (rep R q.1)) ∧ IsInt R (orbZ w' (rep R q.2))
  swap
  · rw [if_neg hc, zero_mul, zero_mul] at hq
    exact absurd rfl hq
  rw [if_pos hc] at hq
  have hcard : Nat.card (isoZZ R (orbZ w (rep R q.1)) (orbZ w' (rep R q.2))) ≠ 0 := by
    intro h0
    apply hq
    rw [h0]
    simp
  obtain ⟨⟨φ, -⟩⟩ := (Nat.card_ne_zero.mp hcard).1
  have hZ : IsUnit (orbZ w (rep R q.1)).det := by
    rw [det_orbZ]
    exact isUnit_det_pt _ _
  have hZ' : IsUnit (orbZ w' (rep R q.2)).det := by
    rw [det_orbZ]
    exact isUnit_det_pt _ _
  have e1 := (cokernel_finite_card_eq_inv_modulus hd _ _ hc.1 hZ).2
  have e2 := (cokernel_finite_card_eq_inv_modulus hd _ _ hc.2 hZ').2
  have e3 : Nat.card (coker R (orbZ w (rep R q.1))) = Nat.card (coker R (orbZ w' (rep R q.2))) :=
    Nat.card_congr φ.toEquiv
  rw [e3, e2, det_orbZ, det_orbZ] at e1
  exact (inv_inj.mp e1).symm
end Formalism.FourierDecayAlt.P.A5x5
