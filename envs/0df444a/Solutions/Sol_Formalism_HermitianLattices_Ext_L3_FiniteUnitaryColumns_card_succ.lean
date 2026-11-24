-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.card_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:35.3648+00:00
-- url     : https://prove2.me/submissions/77e3c97b-de1b-4902-aee4-edc2a3700e60

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryFin
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_cj_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_cj_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_cj_cj
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_exists_col
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_unitary
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_eq_emb
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
open Matrix
variable {k : Type*} [Field k]
namespace Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
theorem _root_.solution {m : ℕ} (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) :
    Nat.card {X : Matrix (Fin (m + 1)) (Fin (m + 1)) k // cj σ X * X = 1} =
      Nat.card {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} *
        Nat.card {X : Matrix (Fin m) (Fin m) k // cj σ X * X = 1} := by
  choose g hg hgc using fun x : {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} =>
    exists_col σ hσ hne x.1 x.2
  have hg' : ∀ x, g x * cj σ (g x) = 1 := fun x => mul_eq_one_comm.mp (hg x)
  have hcol : ∀ x (Y : Matrix (Fin m) (Fin m) k) i, (g x * emb Y) i 0 = x.1 i := by
    intro x Y i
    simp [Matrix.mul_apply, Fin.sum_univ_succ, hgc]
  let Φ : {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} ×
      {X : Matrix (Fin m) (Fin m) k // cj σ X * X = 1} →
      {X : Matrix (Fin (m + 1)) (Fin (m + 1)) k // cj σ X * X = 1} := fun p =>
    ⟨g p.1 * emb p.2.1, by
      rw [cj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (cj σ (g p.1)), hg, Matrix.one_mul]
      exact emb_unitary σ _ p.2.2⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨x, Y⟩ ⟨x', Y'⟩ h
      have h1 : g x * emb Y.1 = g x' * emb Y'.1 := congrArg Subtype.val h
      have hxx : x = x' := by
        apply Subtype.ext
        funext i
        rw [← hcol x Y.1 i, h1, hcol]
      subst hxx
      have h2 : emb Y.1 = emb Y'.1 := by
        have := congrArg (fun M => cj σ (g x) * M) h1
        simpa only [← Matrix.mul_assoc, hg, Matrix.one_mul] using this
      have hYY : Y = Y' := by
        apply Subtype.ext
        ext i j
        exact congrFun (congrFun h2 i.succ) j.succ
      rw [hYY]
    · rintro ⟨X, hX⟩
      have hx : ∑ i, σ (X i 0) * X i 0 = 1 := by
        have := congrFun (congrFun hX 0) 0
        simpa [Matrix.mul_apply, cj_apply] using this
      set x : {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} := ⟨fun i => X i 0, hx⟩ with hxdef
      set Z := cj σ (g x) * X with hZ
      have hZu : cj σ Z * Z = 1 := by
        rw [hZ, cj_mul, cj_cj σ hσ, Matrix.mul_assoc, ← Matrix.mul_assoc (g x), hg',
          Matrix.one_mul, hX]
      have hZc : ∀ i, Z i 0 = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i 0 := by
        intro i
        rw [← hg x, hZ]
        simp only [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hgc x l]
      obtain ⟨hE, hU⟩ := eq_emb σ Z hZu (by rw [hZc]; simp)
        (fun i => by rw [hZc]; simp [Fin.succ_ne_zero i])
      refine ⟨(x, ⟨_, hU⟩), Subtype.ext ?_⟩
      change g x * emb (Z.submatrix Fin.succ Fin.succ) = X
      rw [← hE, hZ, ← Matrix.mul_assoc, hg', Matrix.one_mul]
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective Φ hΦ)).symm
end Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
