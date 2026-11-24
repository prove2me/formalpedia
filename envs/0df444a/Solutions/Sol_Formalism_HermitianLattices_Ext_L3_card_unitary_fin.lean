-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.card_unitary_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:34.805316+00:00
-- url     : https://prove2.me/submissions/3c407391-dfbb-4832-9049-b6845c48c3d5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryFin
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_card_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_card_herm_norm_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ

set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution {k : Type*} [Field k] [Fintype k] (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x)
    (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2) (m : ℕ) :
    (Nat.card {X : Matrix (Fin m) (Fin m) k // (X.map σ).transpose * X = 1} : ℝ) =
      (q : ℝ) ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (1 - (-(q : ℝ))⁻¹ ^ j) := by
  have hq0 : (q : ℝ) ≠ 0 := by
    have h1 : 0 < Fintype.card k := Fintype.card_pos
    rw [hq] at h1
    have : q ≠ 0 := by
      rintro rfl
      simp at h1
    exact_mod_cast this
  induction m with
  | zero =>
    have : Nat.card {X : Matrix (Fin 0) (Fin 0) k // (X.map σ).transpose * X = 1} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⟨1, Subsingleton.elim _ _⟩⟩⟩
    rw [this]
    simp
  | succ m ih =>
    have h1 := FiniteUnitaryColumns.card_succ (m := m) σ hσ hne
    have h2 := card_herm_norm_eq σ hσ hne q hq (m + 1) (by omega) 1 (map_one σ) one_ne_zero
    have h2' : (Nat.card {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} : ℝ) =
        (q : ℝ) ^ m * ((q : ℝ) ^ (m + 1) - (-1) ^ (m + 1)) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h2
      simpa using this
    have h1' : (Nat.card {X : Matrix (Fin (m + 1)) (Fin (m + 1)) k //
        (X.map σ).transpose * X = 1} : ℝ) =
        (Nat.card {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} : ℝ) *
          (Nat.card {X : Matrix (Fin m) (Fin m) k // (X.map σ).transpose * X = 1} : ℝ) := by
      exact_mod_cast h1
    rw [h1', h2', ih, Finset.prod_Icc_succ_top (by omega)]
    have h3 : (q : ℝ) ^ ((m + 1) ^ 2) = (q : ℝ) ^ (m ^ 2) * ((q : ℝ) ^ m * (q : ℝ) ^ (m + 1)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring
    have h4 : (q : ℝ) ^ (m + 1) * (1 - (-(q : ℝ))⁻¹ ^ (m + 1)) =
        (q : ℝ) ^ (m + 1) - (-1) ^ (m + 1) := by
      have : (-(q : ℝ))⁻¹ = (-1) * (q : ℝ)⁻¹ := by
        rw [neg_mul, one_mul, inv_neg]
      rw [this, mul_pow, mul_sub, mul_one, mul_left_comm, ← mul_pow, mul_inv_cancel₀ hq0, one_pow,
        mul_one]
    rw [h3, ← h4]
    ring
end Formalism.HermitianLattices.Ext.L3
