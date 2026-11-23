-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.cyclic_of_socle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:41.812799+00:00
-- url     : https://prove2.me/submissions/6e6f505a-3ca2-4a69-ac36-7f85aaca37d5

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_succ
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_succ
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_tt_pow_n
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_zero_zero
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_zero_succ
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_succ_zero
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_succ_succ

set_option autoImplicit false
open Polynomial Matrix
open Formalism Formalism.CyclotomicNorms
noncomputable section
open Formalism.CyclotomicNorms.residueMatrixData
variable {K' : Type} [Field K'] {n : ℕ}
local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)
namespace Formalism.CyclotomicNorms.residueMatrixData
theorem _root_.solution {a : ℕ} (N : Submodule (TruncK K' n) (Fin a → TruncK K' n))
    (hN : Module.finrank K' ↥(N ⊓ LinearMap.ker ((TT) • LinearMap.id :
          (Fin a → TruncK K' n) →ₗ[TruncK K' n] (Fin a → TruncK K' n))) ≤ 1) :
    ∃ x, N = Submodule.span (TruncK K' n) {x} := by
  classical
  set S := N ⊓ LinearMap.ker ((TT) • LinearMap.id :
    (Fin a → TruncK K' n) →ₗ[TruncK K' n] (Fin a → TruncK K' n)) with hS
  have memS : ∀ y, y ∈ S ↔ y ∈ N ∧ (TT) • y = 0 := by
    intro y; simp [hS]
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hN
  have hex : ∃ h : ℕ, ∀ y ∈ N, (TT) ^ h • y = 0 := ⟨n, fun y _ => by rw [tt_pow_n, zero_smul]⟩
  by_cases hz : Nat.find hex = 0
  · refine ⟨0, ?_⟩
    have h0 := Nat.find_spec hex
    rw [hz] at h0
    rw [Submodule.span_singleton_eq_bot.mpr rfl, eq_bot_iff]
    intro y hy
    simpa using h0 y hy
  obtain ⟨h, hh⟩ := Nat.exists_eq_succ_of_ne_zero hz
  have hspec : ∀ y ∈ N, (TT) ^ (h + 1) • y = 0 := by
    have := Nat.find_spec hex; rw [hh] at this; exact this
  have hmin : ¬ ∀ y ∈ N, (TT) ^ h • y = 0 := Nat.find_min hex (by omega)
  obtain ⟨x, hxN, hx⟩ : ∃ x ∈ N, (TT) ^ h • x ≠ 0 := by
    by_contra hc
    apply hmin
    intro y hy
    by_contra hy'
    exact hc ⟨y, hy, hy'⟩
  refine ⟨x, le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr hxN)⟩
  have hw : (TT) ^ h • x ∈ S :=
    (memS _).mpr ⟨N.smul_mem _ hxN, by rw [← mul_smul, ← pow_succ']; exact hspec x hxN⟩
  obtain ⟨c2, hc2⟩ := hv ⟨_, hw⟩
  have e2 : c2 • (v : Fin a → TruncK K' n) = (TT) ^ h • x := by
    rw [← Submodule.coe_smul_of_tower, hc2]
  have hc2ne : c2 ≠ 0 := by
    rintro rfl; apply hx; rw [← e2, zero_smul]
  have key : ∀ m : ℕ, ∀ y ∈ N, (TT) ^ m • y = 0 → y ∈ Submodule.span (TruncK K' n) {x} := by
    intro m
    induction m with
    | zero => intro y _ hy; rw [pow_zero, one_smul] at hy; rw [hy]; exact Submodule.zero_mem _
    | succ m ih =>
      intro y hy h0
      by_cases hz : (TT) ^ m • y = 0
      · exact ih y hy hz
      have hmh : m ≤ h := by
        by_contra hlt
        apply hz
        rw [← Nat.sub_add_cancel (not_le.mp hlt : h + 1 ≤ m), pow_add, mul_smul, hspec y hy, smul_zero]
      have hz' : (TT) ^ m • y ∈ S :=
        (memS _).mpr ⟨N.smul_mem _ hy, by rw [← mul_smul, ← pow_succ']; exact h0⟩
      obtain ⟨c1, hc1⟩ := hv ⟨_, hz'⟩
      have e1 : c1 • (v : Fin a → TruncK K' n) = (TT) ^ m • y := by
        rw [← Submodule.coe_smul_of_tower, hc1]
      have hy'N : y - (c1 / c2) • ((TT) ^ (h - m) • x) ∈ N :=
        N.sub_mem hy (N.smul_of_tower_mem _ (N.smul_mem _ hxN))
      have hy' : (TT) ^ m • (y - (c1 / c2) • ((TT) ^ (h - m) • x)) = 0 := by
        rw [smul_sub, smul_comm ((TT) ^ m) (c1 / c2), ← mul_smul, ← pow_add, Nat.add_sub_cancel' hmh,
          ← e1, ← e2, smul_smul, div_mul_cancel₀ _ hc2ne, sub_self]
      have hmem := ih _ hy'N hy'
      have hyeq : y = (y - (c1 / c2) • ((TT) ^ (h - m) • x)) + (c1 / c2) • ((TT) ^ (h - m) • x) := by
        rw [sub_add_cancel]
      rw [hyeq]
      exact Submodule.add_mem _ hmem (Submodule.smul_of_tower_mem _ _
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
  intro y hy
  exact key (h + 1) y hy (hspec y hy)
end Formalism.CyclotomicNorms.residueMatrixData
