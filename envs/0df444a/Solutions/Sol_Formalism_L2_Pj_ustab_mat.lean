-- Prove2me | solution 1 for Formalism.L2.Pj.ustab_mat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:50.271202+00:00
-- url     : https://prove2.me/submissions/95e56535-448f-4fb6-935c-e6dbfe3fb6b7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace Formalism.L2.Pj
theorem _root_.solution {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} {γ : GL (Fin r) E}
    (h : IsUStab G Λ γ) :
    (γ : Matrix (Fin r) (Fin r) E)ᵀ * G * (γ : Matrix (Fin r) (Fin r) E).map cc = G := by
  ext k l
  have h1 := h.1 (Pi.single k 1) (Pi.single l 1)
  have hR : herm G (Pi.single k 1) (Pi.single l 1) = G k l := by
    have hs : ∀ b, cc ((Pi.single l (1 : E) : Fin r → E) b) = (Pi.single l (1 : E) : Fin r → E) b := by
      intro b
      by_cases hb : b = l <;> simp [hb, cc]
    simp only [herm, hs]
    simp [Pi.single_apply]
  have hL : herm G (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (Pi.single k 1))
      (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (Pi.single l 1)) =
      ((γ : Matrix (Fin r) (Fin r) E)ᵀ * G * (γ : Matrix (Fin r) (Fin r) E).map cc) k l := by
    simp only [herm, Matrix.mulVec_single_one, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [← hL, h1, hR]
end Formalism.L2.Pj
