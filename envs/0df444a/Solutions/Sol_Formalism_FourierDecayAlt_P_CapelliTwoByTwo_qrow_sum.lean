-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliTwoByTwo.qrow_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:35:39.460433+00:00
-- url     : https://prove2.me/submissions/b586510e-581a-4a33-a6c1-59d1e8f6d26d

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliTwoByTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_map_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.CapelliTwoByTwo
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.CapelliTwoByTwo
theorem _root_.solution (y x : Fin (2 * r + k + 1) → ℂ) (Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ)
    (j : Fin (mdim k r (Fin.last r))) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    ∑ d, qrow k r y x Bs j (bvec (posL k r (Fin.last r) d)) * v (posL k r (Fin.last r) d) = qrow k r y x Bs j v := by
  have hl1 : ∀ v w u, herm (Hpk k r) (v + w) u = herm (Hpk k r) v u + herm (Hpk k r) w u := by
    intro v w u
    simp [herm, Matrix.mulVec_add, dotProduct_add]
  have hl2 : ∀ (c : ℂ) v u, herm (Hpk k r) (c • v) u = c * herm (Hpk k r) v u := by
    intro c v u
    simp [herm, Matrix.mulVec_smul, dotProduct_smul]
  let Lq : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := qrow k r y x Bs j
      map_add' := fun v w => by
        unfold qrow
        split_ifs
        · rw [hl1, hl1]
          ring
        · rw [hl1, hl1]
          ring
        · rw [hl1]
      map_smul' := fun c v => by
        show qrow k r y x Bs j (c • v) = c • qrow k r y x Bs j v
        unfold qrow
        split_ifs
        · rw [hl2, hl2, smul_eq_mul]
          ring
        · rw [hl2, hl2, smul_eq_mul]
          ring
        · rw [hl2, smul_eq_mul] }
  have hv' : v = ∑ d, v (posL k r (Fin.last r) d) • bvec (posL k r (Fin.last r) d) := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, bvec, smul_eq_mul, Pi.single_apply]
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · have hd0 : i.val - r < mdim k r (Fin.last r) := by
        simp only [mdim, Fin.val_last, Nat.sub_self, mul_zero, zero_add]
        omega
      rw [Finset.sum_eq_single ⟨i.val - r, hd0⟩]
      · have hp : posL k r (Fin.last r) ⟨i.val - r, hd0⟩ = i := by
          ext
          simp only [posL, Fin.val_last]
          omega
        rw [hp, if_pos rfl, mul_one]
      · intro b _ hb
        rw [if_neg, mul_zero]
        intro h
        apply hb
        ext
        have h2 := congrArg Fin.val h
        simp only [posL, Fin.val_last] at h2 ⊢
        omega
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [hv i (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro d _
      rw [if_neg, mul_zero]
      intro h
      apply hi
      have hd := d.isLt
      simp only [mdim, Fin.val_last, Nat.sub_self, mul_zero, zero_add] at hd
      rw [h]
      simp only [posL, Fin.val_last]
      omega
  calc ∑ d, qrow k r y x Bs j (bvec (posL k r (Fin.last r) d)) * v (posL k r (Fin.last r) d)
      = Lq (∑ d, v (posL k r (Fin.last r) d) • bvec (posL k r (Fin.last r) d)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [map_smul, smul_eq_mul, mul_comm]
        rfl
    _ = qrow k r y x Bs j v := by
        rw [← hv']
        rfl
end Formalism.FourierDecayAlt.P.CapelliTwoByTwo
