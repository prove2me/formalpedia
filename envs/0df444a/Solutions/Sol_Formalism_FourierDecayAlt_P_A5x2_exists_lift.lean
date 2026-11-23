-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:04.193976+00:00
-- url     : https://prove2.me/submissions/cd61a59f-6685-4107-bc60-4d3a05fa30ac

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamTil_fin
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamTil_big
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_liftR_map
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
variable {R}
variable (R)
namespace Formalism.FourierDecayAlt.P.A5x2
theorem _root_.solution (Z Z' : Matrix (Fin n) (Fin n) K) (hZ' : IsInt R Z') (hd' : IsUnit Z'.det)
    (φ : coker R Z ≃ₗ[R] coker R Z') (k : ℕ) (hT : InTTeq R k Z Z' φ) (v : Fin n → R) :
    ∃ v', LiftRel R k Z Z' φ v v' := by
  obtain ⟨v0, hv0⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk v))
  have h1 : ∀ a : Fin n, ∃ r : R, k ≤ a.val →
      (r : K) = lamTil R Z' a.val v0 - lamTil R Z a.val v := by
    intro a
    by_cases hk : k ≤ a.val
    · have := hT a.val hk a.2 v v0 hv0.symm
      simp only [lamN, LinearMap.comp_apply, Submodule.mkQ_apply] at this
      rw [Submodule.Quotient.eq] at this
      obtain ⟨r, hr⟩ := this
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose ρ hρ using h1
  let z : Fin n → R := liftR R Z' hZ' *ᵥ ρ
  have hz : coeLin R z = Z' *ᵥ coeLin R ρ := by rw [coeLin_mulVec, liftR_map]
  refine ⟨v0 - z, ?_, ?_⟩
  · rw [Submodule.Quotient.mk_sub, hv0]
    have : (Submodule.Quotient.mk z : coker R Z') = 0 := by
      rw [Submodule.Quotient.mk_eq_zero, mem_latZ]; exact ⟨ρ, hz.symm⟩
    rw [this, sub_zero]
  · intro j hj
    by_cases hjn : j < n
    · have e := lamTil_fin R Z' ⟨j, hjn⟩ z
      rw [hz, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd', Matrix.one_mulVec,
        coeLin_apply] at e
      have h2 := hρ ⟨j, hjn⟩ hj
      simp only at e h2
      rw [map_sub, e, h2]; ring
    · rw [lamTil_big R Z' j (by omega), lamTil_big R Z j (by omega)]; rfl
end Formalism.FourierDecayAlt.P.A5x2
