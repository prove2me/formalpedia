-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5a4_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:47.421282+00:00
-- url     : https://prove2.me/submissions/b278f068-db1c-417b-b01e-904a01aec334

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {K : Type} [Field K] [Fintype K] (M : ℕ) (x : Fin (M + 1) → K)
    (hx : x ≠ 0) (c : K) :
    Nat.card {y : Fin (M + 1) → K // ∑ i, x i * y i = c} = Fintype.card K ^ M := by
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by
    by_contra h; exact hx (funext fun i => by_contra fun hi => h ⟨i, hi⟩)
  have e : {y : Fin (M + 1) → K // ∑ i, x i * y i = c} ≃ (Fin M → K) :=
    { toFun := fun y j => y.1 (i0.succAbove j)
      invFun := fun w => ⟨Fin.insertNth i0 ((c - ∑ j, x (i0.succAbove j) * w j) / x i0) w, by
        rw [Fin.sum_univ_succAbove _ i0]
        simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        field_simp; ring⟩
      left_inv := by
        rintro ⟨y, hy⟩
        apply Subtype.ext
        simp only
        rw [Fin.insertNth_eq_iff]
        refine ⟨?_, rfl⟩
        rw [Fin.sum_univ_succAbove _ i0] at hy
        rw [← hy]; field_simp; ring
      right_inv := by
        intro w; ext j; simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
end Formalism.HermitianLatticeCounting.P
