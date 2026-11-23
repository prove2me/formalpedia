-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.bigZ_int_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:54.168899+00:00
-- url     : https://prove2.me/submissions/06730bc2-f8d1-4db8-8e86-bb3cc7901263

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_blkM_isInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iA_spec
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iC_spec
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mk_eq_zero
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] (R : Subring K) {m : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution {N : ℕ} (hN : N = m + 1) (Z : Matrix (Fin m) (Fin m) K) (hZ : IsInt R Z)
    (hd : IsUnit Z.det) (α : coker R Z →ₗ[R] KR R) (β : coker R Z) (c : K) :
    IsInt R (bigZ hN Z (outV R (iA R Z α)) (outV R (iC R Z β)) c) ↔
      α β = -(Submodule.Quotient.mk c : KR R) := by
  obtain ⟨b, hb, hβ⟩ := iC_spec R Z hZ hd β
  unfold bigZ
  rw [blkM_isInt]
  have h1 : ∀ i, (Z *ᵥ outV R (iC R Z β)) i ∈ R := by
    intro i; rw [← hb, P.coeLin_apply]; exact (b i).2
  have h2 : ∀ j, (outV R (iA R Z α) ᵥ* Z) j ∈ R := by
    intro j
    have h3 : (Submodule.Quotient.mk (fun i => (⟨Z i j, hZ i j⟩ : R)) : coker R Z) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero, P.mem_latZ]
      refine ⟨Pi.single j 1, ?_⟩
      funext i
      rw [P.coeLin_apply]
      have : coeLin R (Pi.single j 1 : Fin m → R) = Pi.single j 1 := by
        funext k
        rw [P.coeLin_apply]
        by_cases hk : k = j
        · subst hk; simp
        · simp [hk]
      rw [this, mulVec_single_one]
      rfl
    have h4 := iA_spec R Z α (fun i => (⟨Z i j, hZ i j⟩ : R))
    rw [h3, map_zero, eq_comm, A5x3.mk_eq_zero] at h4
    convert h4 using 1
    simp only [vecMul, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [P.coeLin_apply]
  have h5 : α β = Submodule.Quotient.mk (outV R (iA R Z α) ⬝ᵥ Z *ᵥ outV R (iC R Z β)) := by
    rw [← hb, ← iA_spec, hβ]
  rw [h5, eq_neg_iff_add_eq_zero, ← Submodule.Quotient.mk_add, A5x3.mk_eq_zero]
  exact ⟨fun h => h.2.2.2, fun h => ⟨hZ, h1, h2, h⟩⟩
end Formalism.FourierDecayAlt.P.A5x8
