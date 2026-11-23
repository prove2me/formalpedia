-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.tb_iff_ta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:43.970278+00:00
-- url     : https://prove2.me/submissions/13b0a99a-0ce9-449c-88c4-30552aa68d7c

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_quadM
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_conj_quad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
variable {α : Type}
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution (F : Finset α) (k : α → α → ℂ) : TB.PSDOn F k ↔ TA.PSDOn F k := by
  classical
  unfold TB.PSDOn TA.PSDOn
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨hH, hp⟩
    refine ⟨?_, ?_⟩
    · intro x hx y hy
      have := congrFun (congrFun hH ⟨y, hy⟩) ⟨x, hx⟩
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def] at this
      exact this.symm
    · intro a
      have := hp (fun x : F => a x)
      rw [quadM] at this
      exact (Complex.le_def.1 this).1
  · rintro ⟨hh, hp⟩
    refine ⟨?_, ?_⟩
    · ext x y
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
      exact (hh y y.2 x x.2).symm
    · intro x
      let a : α → ℂ := fun z => if h : z ∈ F then x ⟨z, h⟩ else 0
      have hx : x = fun z : F => a z := by
        ext z; simp [a]
      rw [hx, quadM]
      rw [Complex.le_def]
      refine ⟨hp a, ?_⟩
      have := conj_quad F k hh a
      rw [Complex.conj_eq_iff_im] at this
      simpa using this.symm
end Formalism.FourierDecayAlt.P.Jx8
