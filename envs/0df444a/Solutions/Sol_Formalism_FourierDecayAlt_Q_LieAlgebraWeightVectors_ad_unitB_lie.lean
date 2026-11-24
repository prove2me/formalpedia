-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_unitB_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:14:06.718622+00:00
-- url     : https://prove2.me/submissions/cbed9f54-204d-464b-8904-4738e751039e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBCtMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBLie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpart1_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpart2_lie
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_herm_symm
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_unitB_kill

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx2
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}
private theorem herm_bvec_eq_zero_of_inWb {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w)
    (j : Fin (2 * r + k + 1)) (hj : j.val < r ∨ r + k < j.val) : herm (Hpk k r) (bvec j) w = 0 := by
  unfold herm
  have hcol : Hpk k r *ᵥ bvec j = fun i => Hpk k r i j := by
    ext i; simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
  rw [hcol]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i.val < r ∨ r + k < i.val
  · simp [hw i hi]
  · push_neg at hi
    have h0 : Hpk k r i j = 0 := by
      unfold Hpk
      rw [if_neg (by omega), if_neg (by omega),
        if_neg (by rintro ⟨_, _, h⟩; have := congrArg Fin.val h; omega)]
    simp [h0]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
end
end

set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx2
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {g : Mx k r} {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hBs : IsFrameOf k r [g⁻¹ *ᵥ z] Bs) (a b : Fin m) :
    (inLieLev k r (Fin.last r) (hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b)) ∧
      inLieLev k r (Fin.last r) (hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b))) ∧
    (hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ (g⁻¹ *ᵥ z) = 0 ∧
      hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ (g⁻¹ *ᵥ z) = 0) := by
  obtain ⟨hW, _, hO⟩ := hBs
  have hk : ∀ v, (∀ c, herm (Hpk k r) v (Bs c) = 0) →
      hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ v = 0 ∧
        hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ v = 0 :=
    fun v hv => ad_unitB_kill Bs a b (hv a) (hv b)
  have hz : ∀ c, herm (Hpk k r) (g⁻¹ *ᵥ z) (Bs c) = 0 := by
    intro c
    rw [ad_herm_symm, hO c _ (List.mem_singleton_self _)]
    simp
  have he : ∀ a' : Fin r, (∀ c, herm (Hpk k r) (bvec (eI k r a')) (Bs c) = 0) ∧
      (∀ c, herm (Hpk k r) (bvec (esI k r a')) (Bs c) = 0) := fun a' =>
    ⟨fun c => herm_bvec_eq_zero_of_inWb (hW c) _ (Or.inl (by simp only [eI]; exact a'.isLt)),
      fun c => herm_bvec_eq_zero_of_inWb (hW c) _ (Or.inr (by simp only [esI]; have := a'.isLt; omega))⟩
  exact ⟨⟨⟨hpart1_lie _, fun a' _ => ⟨(hk _ (he a').1).1, (hk _ (he a').2).1⟩⟩,
    ⟨hpart2_lie _, fun a' _ => ⟨(hk _ (he a').1).2, (hk _ (he a').2).2⟩⟩⟩, (hk _ hz).1, (hk _ hz).2⟩
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
