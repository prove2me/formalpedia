-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.peel_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:32:04.834392+00:00
-- url     : https://prove2.me/submissions/46979ef7-1e7f-4281-8acb-6339ddc9af7c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPolynomialExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_peel_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_expansion_last_column


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution {n m : ℕ} (I : Ideal A) (E : Fin n → Fin n → A) {ι : Type} [Fintype ι] (η : ι → ℂ)
    (a : Fin (m + 1) → Fin n) (b0 : Fin m → Fin n) (bw : ι → Fin n) (u κ : ℂ)
    (hT : ∀ l, (∑ w, η w • Tm E (u - (m : ℂ)) (a l) (bw w)) - algebraMap ℂ A (if l = Fin.last m then κ else 0) ∈ I) :
    (∑ w, η w • qminor E a (Fin.snoc (α := fun _ => Fin n) b0 (bw w)) u) - κ • qminor E (a ∘ Fin.castSucc) b0 u ∈ I := by
  have hexp : ∀ w, qminor E a (Fin.snoc (α := fun _ => Fin n) b0 (bw w)) u =
      ∑ l : Fin (m + 1), ((((-1 : ℤ) ^ (m + (l : ℕ)) : ℤ) : A)) *
        (qminor E (a ∘ l.succAbove) b0 u * Tm E (u - (m : ℂ)) (a l) (bw w)) := by
    intro w
    rw [Formalism.FourierDecayAlt.P.expansion_last_column A n m E a (Fin.snoc (α := fun _ => Fin n) b0 (bw w)) u]
    congr 1; ext l
    have h1 : (Fin.snoc (α := fun _ => Fin n) b0 (bw w) : Fin (m + 1) → Fin n) ∘ Fin.castSucc = b0 := by
      funext x; simp [Fin.snoc_castSucc]
    rw [h1, Fin.snoc_last]
  simp_rw [hexp]
  have := peel_core I η (fun l => qminor E (a ∘ l.succAbove) b0 u) (fun l w => Tm E (u - (m : ℂ)) (a l) (bw w)) κ hT
  simpa [Fin.succAbove_last] using this
end Formalism.FourierDecayAlt.P.SignAntidiagonal
