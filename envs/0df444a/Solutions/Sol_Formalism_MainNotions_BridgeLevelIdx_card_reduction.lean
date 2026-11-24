-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLevelIdx.card_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:20:15.714994+00:00
-- url     : https://prove2.me/submissions/8c9c6a45-1c3b-4e00-af32-bbc9887d79ad

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelIdx
import Theorems.Thm_Formalism_MainNotions_BridgeLevelIdx_kset_mulVec
import Theorems.Thm_Formalism_MainNotions_BridgeLevelIdx_kg_of_gen
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
theorem _root_.solution {g : ℕ} (hg : 1 ≤ g) (hG : LevelGen I g) :
    ∃ (α : Type) (_ : Fintype α) (ρ : I.Gf → α), Fintype.card α ≤ g ^ (2 * I.n ^ 2 * I.f) ∧
      ∀ x ∈ I.Kset, ∀ x' ∈ I.Kset, ρ x = ρ x' → x⁻¹ * x' ∈ I.Kg g := by
  classical
  obtain ⟨m, l, S, hm, hS, hl, hgen, hrep⟩ := hG
  obtain ⟨s0, hs0, -⟩ := hrep 0 I.Lf.zero_mem
  let r : (Fin I.n → I.E ⊗[I.F] Af I.F) → S := fun v =>
    if h : v ∈ I.Lf then ⟨(hrep v h).choose, (hrep v h).choose_spec.1⟩ else ⟨s0, hs0⟩
  have hr : ∀ v ∈ I.Lf, ∃ z ∈ I.Lf, v = (r v : Fin I.n → I.E ⊗[I.F] Af I.F) + (g : I.E ⊗[I.F] Af I.F) • z := by
    intro v hv
    simp only [r, dif_pos hv]
    exact (hrep v hv).choose_spec.2
  refine ⟨Fin m → S, inferInstance, fun x j => r (I.fmat x *ᵥ l j), ?_, ?_⟩
  · rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    calc S.card ^ m ≤ (g ^ (2 * I.f * I.n)) ^ m := Nat.pow_le_pow_left hS m
      _ ≤ (g ^ (2 * I.f * I.n)) ^ I.n := Nat.pow_le_pow_right (pow_pos (by omega) _) hm
      _ = g ^ (2 * I.n ^ 2 * I.f) := by rw [← pow_mul]; congr 1; ring
  · intro x hx x' hx' hρ
    refine kg_of_gen hgen hx hx' fun j => ?_
    have e : r (I.fmat x *ᵥ l j) = r (I.fmat x' *ᵥ l j) := congrFun hρ j
    obtain ⟨z, hz, ez⟩ := hr _ (kset_mulVec hx (hl j))
    obtain ⟨z', hz', ez'⟩ := hr _ (kset_mulVec hx' (hl j))
    refine ⟨z' - z, I.Lf.sub_mem hz' hz, ?_⟩
    rw [Matrix.sub_mulVec, ez, ez', e, smul_sub]
    abel
end Formalism.MainNotions.BridgeLevelIdx
