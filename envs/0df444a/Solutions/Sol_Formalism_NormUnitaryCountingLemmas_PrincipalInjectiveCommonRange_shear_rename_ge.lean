-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.shear_rename_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:11:16.224457+00:00
-- url     : https://prove2.me/submissions/6f0b73ef-4691-4c6b-9f75-44154e4ead5b

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearHypothesisTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
variable {R : Type*} [CommRing R]
namespace Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
theorem _root_.solution {N N' n : ℕ} (hN : N ≤ N') (i j : Fin N') (hj : N ≤ (j : ℕ)) :
    (shear R i j).comp (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2))) =
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin N' × Fin n) R)
        (Polynomial (MvPolynomial (Fin N' × Fin n) R))).comp
        (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2))) := by
  apply MvPolynomial.algHom_ext
  intro p
  have e1 : Fin.castLE hN p.1 ≠ j := by
    intro e; have := congrArg Fin.val e; simp at this; omega
  simp [shear, e1]
end Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
