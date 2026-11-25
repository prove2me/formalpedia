-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.unique_lifting_property
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:05:45.896107+00:00
-- url     : https://prove2.me/submissions/3854a4c8-13bd-472c-bc8b-f328a7cc28b3

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_Final_LocalIntegralStructure_cofactorVec


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
theorem _root_.solution : UniqueLift := by
  intro K _ r Z c hD hc1 hc
  obtain ⟨hw, hwl⟩ := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.cofactorVec K r Z
  set Dr := (Z.submatrix Fin.castSucc Fin.castSucc).det with hDr
  have key : ∀ b, c b = Z.adjugate (Fin.last r) b / Dr := by
    let d : Fin (r + 1) → K := fun b => c b - Z.adjugate (Fin.last r) b / Dr
    have hdl : d (Fin.last r) = 0 := by simp [d, hc1, hwl, div_self hD]
    have hd : ∀ a, a ≠ Fin.last r → ∑ b, d b * Z b a = 0 := by
      intro a ha
      have h1 := hw a
      rw [if_neg ha] at h1
      simp only [d, sub_mul, Finset.sum_sub_distrib, hc a ha, div_mul_eq_mul_div, ← Finset.sum_div, h1]
      simp
    have hz : Matrix.vecMul (fun i : Fin r => d i.castSucc) (Z.submatrix Fin.castSucc Fin.castSucc) = 0 := by
      ext a
      have := hd a.castSucc (Fin.castSucc_ne_last a)
      rw [Fin.sum_univ_castSucc, hdl, zero_mul, add_zero] at this
      simpa [Matrix.vecMul, dotProduct] using this
    have h0 := Matrix.eq_zero_of_vecMul_eq_zero hD hz
    intro b
    have : d b = 0 := by
      refine Fin.lastCases hdl (fun i => ?_) b
      exact congrFun h0 i
    exact sub_eq_zero.mp this
  refine ⟨key, ?_⟩
  have h1 := hw (Fin.last r)
  rw [if_pos rfl] at h1
  simp only [key, div_mul_eq_mul_div, ← Finset.sum_div, h1]
end Formalism.HermitianLatticeCounting.P
