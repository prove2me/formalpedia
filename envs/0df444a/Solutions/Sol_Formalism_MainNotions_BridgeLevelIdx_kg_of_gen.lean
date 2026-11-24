-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLevelIdx.kg_of_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:01:26.832229+00:00
-- url     : https://prove2.me/submissions/13e5d081-4cef-4fc1-8f7d-f5851847e035

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelIdx
import Theorems.Thm_Formalism_MainNotions_BridgeLevelIdx_lf_csmul
import Theorems.Thm_Formalism_MainNotions_BridgeLevelIdx_kset_mulVec
import Theorems.Thm_Formalism_MainNotions_BridgeLevelIdx_kset_inv_mulVec
import Theorems.Thm_Formalism_MainNotions_BridgeLevelIdx_kset_mul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelIdx
open MeasureTheory Formalism.MainNotions.S Matrix
open scoped ENNReal TensorProduct
variable (I : AutInst)
variable {I}
namespace Formalism.MainNotions.BridgeLevelIdx
theorem _root_.solution {g : ℕ} {m : ℕ} {l : Fin m → (Fin I.n → I.E ⊗[I.F] Af I.F)}
    (hgen : ∀ y ∈ I.Lf, ∃ (a : Fin m → IntAf I.F I.E) (z : Fin I.n → I.E ⊗[I.F] Af I.F), z ∈ I.Lf ∧
      y = ∑ j, (a j : I.E ⊗[I.F] Af I.F) • l j + (g : I.E ⊗[I.F] Af I.F) • z)
    {x x' : I.Gf} (hx : x ∈ I.Kset) (hx' : x' ∈ I.Kset)
    (hd : ∀ j, ∃ w ∈ I.Lf, (I.fmat x' - I.fmat x) *ᵥ l j = (g : I.E ⊗[I.F] Af I.F) • w) :
    x⁻¹ * x' ∈ I.Kg g := by
  refine ⟨kset_mul hx hx', fun y hy => ?_⟩
  set D := I.fmat x' - I.fmat x with hD

  have hDy : ∃ w ∈ I.Lf, D *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • w := by
    obtain ⟨a, z, hz, rfl⟩ := hgen y hy
    have hsum : ∀ s : Finset (Fin m), ∃ w ∈ I.Lf,
        D *ᵥ (∑ j ∈ s, (a j : I.E ⊗[I.F] Af I.F) • l j) = (g : I.E ⊗[I.F] Af I.F) • w := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨0, I.Lf.zero_mem, by simp⟩
      | insert j s hj ih =>
        obtain ⟨w, hw, e⟩ := ih
        obtain ⟨w', hw', e'⟩ := hd j
        refine ⟨(a j : I.E ⊗[I.F] Af I.F) • w' + w, I.Lf.add_mem (lf_csmul _ hw') hw, ?_⟩
        rw [Finset.sum_insert hj, Matrix.mulVec_add, Matrix.mulVec_smul, e, e', smul_add, smul_comm]
    obtain ⟨w, hw, e⟩ := hsum Finset.univ
    refine ⟨w + D *ᵥ z, I.Lf.add_mem hw ?_, ?_⟩
    · rw [hD, Matrix.sub_mulVec]
      exact I.Lf.sub_mem (kset_mulVec hx' hz) (kset_mulVec hx hz)
    · rw [Matrix.mulVec_add, e, Matrix.mulVec_smul, smul_add]
  obtain ⟨w, hw, e⟩ := hDy
  refine ⟨I.fmat x⁻¹ *ᵥ w, kset_inv_mulVec hx hw, ?_⟩
  have hm : I.fmat (x⁻¹ * x') - 1 = I.fmat x⁻¹ * D := by
    have h1 : I.fmat (x⁻¹ * x') = I.fmat x⁻¹ * I.fmat x' := by
      simp only [AutInst.fmat, Subgroup.coe_mul, Units.val_mul]
    have h2 : I.fmat x⁻¹ * I.fmat x = 1 := by
      simp only [AutInst.fmat, Subgroup.coe_inv, Units.inv_mul]
    rw [hD, Matrix.mul_sub, h1, h2]
  rw [hm, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_smul]
end Formalism.MainNotions.BridgeLevelIdx
