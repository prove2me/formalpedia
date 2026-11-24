-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_chi_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:50:07.669886+00:00
-- url     : https://prove2.me/submissions/0a0d4d43-5174-4eef-aa0b-37acb2944fdf

import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Theorems.Thm_Formalism_UG_P_fIwasawa_ordL_unit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.UG Matrix
namespace Formalism.UG.P
section FIwasawaFinal
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable (σ : L →+* L) {n m : ℕ} (q : ℕ) (α : Fin m → ℂ)
private lemma blockTriangular_mul_diag (B C : Matrix (Fin n) (Fin n) L)
    (hB : B.BlockTriangular id) (hC : C.BlockTriangular id) (i : Fin n) :
    (B * C) i i = B i i * C i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hB (show id k < id i from h), zero_mul]
    · rw [hC (show id i < id k from h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h
private lemma GL_inv_blockTriangular (g : GL (Fin n) L)
    (hg : (g : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hg
private lemma KU_entries_valuation_le_one (g : GU σ n) (hg : g ∈ KU σ n) (i j : Fin n) :
    Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 ∧
    Valued.v ((((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 := by
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf, Formalism.UG.intPts, Subgroup.mem_inf] at hg
  obtain ⟨g', hg'⟩ := MonoidHom.mem_range.mp hg.2
  rw [← hg', ← map_inv]
  refine ⟨?_, ?_⟩
  · exact (Valuation.mem_integer_iff _ _).mp ((g' : Matrix (Fin n) (Fin n) (intL L)) i j).2
  · exact (Valuation.mem_integer_iff _ _).mp
      (((g'⁻¹ : GL (Fin n) (intL L)) : Matrix (Fin n) (Fin n) (intL L)) i j).2
end FIwasawaFinal
end Formalism.UG.P
end

set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable (σ : L →+* L) {n m : ℕ} (q : ℕ) (α : Fin m → ℂ)
namespace Formalism.UG.P
theorem _root_.solution (b : GU σ n)
    (hb : ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id) (hk : b ∈ KU σ n) :
    chiDeltaU q α b = 1 := by
  have hbinv := GL_inv_blockTriangular (b : GL (Fin n) L) hb
  unfold Formalism.UG.chiDeltaU
  apply Finset.prod_eq_one
  intro i _
  split_ifs with h
  · have h0 : ordL (((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩) = 0 := by
      apply fIwasawa_ordL_unit _ ((((b : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩)
        (KU_entries_valuation_le_one σ b hk _ _).1 (KU_entries_valuation_le_one σ b hk _ _).2
      rw [← blockTriangular_mul_diag _ _ hbinv hb, Units.inv_mul]
      exact Matrix.one_apply_eq _
    rw [h0]
    simp
  · rfl
end Formalism.UG.P
