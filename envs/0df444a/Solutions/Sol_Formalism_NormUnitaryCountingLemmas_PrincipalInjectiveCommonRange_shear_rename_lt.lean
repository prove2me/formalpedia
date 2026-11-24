-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.shear_rename_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:11:18.149814+00:00
-- url     : https://prove2.me/submissions/0c99e1a9-80c6-4934-b9cd-4794b1e8f831

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
theorem _root_.solution {N N' n : ℕ} (hN : N ≤ N') (i j : Fin N') (hi : (i : ℕ) < N)
    (hj : (j : ℕ) < N) :
    (shear R i j).comp (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2))) =
      (Polynomial.mapAlgHom (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2)))).comp
        (shear R (⟨i, hi⟩ : Fin N) ⟨j, hj⟩) := by
  apply MvPolynomial.algHom_ext
  intro p
  have e1 : (Fin.castLE hN p.1 = j) ↔ (p.1 = ⟨j, hj⟩) := by simp [Fin.ext_iff]
  have e2 : Fin.castLE hN (⟨i, hi⟩ : Fin N) = i := by ext; simp
  simp [shear, Polynomial.coe_mapAlgHom, e1]
  split_ifs <;> simp
end Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
