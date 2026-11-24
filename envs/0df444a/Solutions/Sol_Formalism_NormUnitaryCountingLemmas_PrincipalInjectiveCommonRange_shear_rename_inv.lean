-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.shear_rename_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:34:17.012483+00:00
-- url     : https://prove2.me/submissions/b35c6a7c-be9e-4634-9450-9d686d274eea

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearHypothesisTwo
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_PrincipalInjectiveCommonRange_shear_rename_lt
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_PrincipalInjectiveCommonRange_shear_rename_ge

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
theorem _root_.solution {N N' n : ℕ} (hN : N ≤ N') (F : MvPolynomial (Fin N × Fin n) R)
    (hF : ∀ i j : Fin N, i < j → shear R i j F = Polynomial.C F) (i j : Fin N') (hij : i < j) :
    shear R i j (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2)) F) =
      Polynomial.C (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2)) F) := by
  by_cases hj : (j : ℕ) < N
  · have hi : (i : ℕ) < N := lt_trans hij hj
    have := AlgHom.congr_fun (shear_rename_lt (R := R) (n := n) hN i j hi hj) F
    simp only [AlgHom.comp_apply] at this
    rw [this, hF _ _ (Fin.mk_lt_mk.mpr hij), Polynomial.coe_mapAlgHom,
      Polynomial.map_C]
    rfl
  · have := AlgHom.congr_fun (shear_rename_ge (R := R) (n := n) hN i j (not_lt.mp hj)) F
    simpa [Polynomial.algebraMap_apply] using this
end Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
