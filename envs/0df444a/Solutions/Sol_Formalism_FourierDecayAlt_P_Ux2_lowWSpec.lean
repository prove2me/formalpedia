-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.lowWSpec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:12:55.798258+00:00
-- url     : https://prove2.me/submissions/3b3a85c9-c3dd-45b5-8972-c50dd19e7c9d

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kL_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_lower_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_permutationMatrix_conj_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_lowW_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {p : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution : LowWSpec := by
  intro p σ l
  constructor
  · rintro ⟨hl, hc⟩
    rw [lower_iff] at hl hc
    refine ⟨fun q => l q.1.1 q.1.2, ?_⟩
    ext a b
    rw [lowW_apply]
    rcases lt_trichotomy a b with h | h | h
    · simp [hl.2 a b (kL_lt.mpr h), ne_of_lt h, not_lt.mpr h.le]
    · subst h; simp [hl.1]
    · by_cases hs : σ.symm b < σ.symm a
      · simp [h, hs, ne_of_gt h]
      · have hs' : σ.symm a < σ.symm b :=
          lt_of_le_of_ne (not_lt.mp hs) (fun e => ne_of_gt h (σ.symm.injective e))
        have := hc.2 (σ.symm a) (σ.symm b) (kL_lt.mpr hs')
        rw [permutationMatrix_conj_apply] at this
        simp at this
        simp [this, hs, ne_of_gt h]
  · rintro ⟨v, rfl⟩
    rw [lower_iff, lower_iff]
    refine ⟨⟨fun i => by simp [lowW_apply], fun a b hab => ?_⟩,
      ⟨fun i => by simp [permutationMatrix_conj_apply, lowW_apply], fun a b hab => ?_⟩⟩
    · rw [kL_lt] at hab; simp [lowW_apply, ne_of_lt hab, not_lt.mpr hab.le]
    · rw [kL_lt] at hab; rw [permutationMatrix_conj_apply, lowW_apply]
      simp [σ.injective.ne (ne_of_lt hab), not_lt.mpr hab.le]
end Formalism.FourierDecayAlt.P.Ux2
