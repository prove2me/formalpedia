-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AnisotropicColumnSums.sum_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:34:05.256547+00:00
-- url     : https://prove2.me/submissions/57c45e93-9d08-4683-bd5a-b55928fa2b7d

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
open Formalism.FourierDecayAlt.P.AnisotropicColumnSums
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.AnisotropicColumnSums
theorem _root_.solution {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (w : Fin (2 * r + k + 1) → ℂ) :
    ∑ d, herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) w * v (posL k r (Fin.last r) d) = herm (Hpk k r) v w := by
  have hinj : ∀ c c' : Fin (mdim k r (Fin.last r)), posL k r (Fin.last r) c = posL k r (Fin.last r) c' → c = c' := by
    intro c c' h
    ext
    simp only [posL, Fin.ext_iff] at h
    omega
  have hsurj : ∀ p, Qx2.inV k r (Fin.last r) p → ∃ c, posL k r (Fin.last r) c = p := by
    intro p hp
    simp only [Qx2.inV, Fin.val_last] at hp
    refine ⟨⟨p.val - r, ?_⟩, ?_⟩
    · simp only [mdim, Fin.val_last]
      omega
    · ext
      simp only [posL, Fin.val_last]
      omega
  have hv' : v = ∑ d, v (posL k r (Fin.last r) d) • bvec (posL k r (Fin.last r) d) := by
    ext q
    simp only [Finset.sum_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hq : Qx2.inV k r (Fin.last r) q
    · obtain ⟨d0, rfl⟩ := hsurj q hq
      rw [Fintype.sum_eq_single d0]
      · simp
      · intro d hd
        have hne : posL k r (Fin.last r) d0 ≠ posL k r (Fin.last r) d := fun h => hd (hinj _ _ h).symm
        simp [hne]
    · rw [Finset.sum_eq_zero]
      · apply hv
        simp only [Qx2.inV, Fin.val_last] at hq
        omega
      · intro d _
        have hne : q ≠ posL k r (Fin.last r) d := by
          rintro rfl
          apply hq
          have hd := d.isLt
          simp only [Qx2.inV, posL, mdim, Fin.val_last] at hd ⊢
          omega
        simp [hne]
  conv_rhs => rw [hv']
  unfold herm
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring
end Formalism.FourierDecayAlt.P.AnisotropicColumnSums
