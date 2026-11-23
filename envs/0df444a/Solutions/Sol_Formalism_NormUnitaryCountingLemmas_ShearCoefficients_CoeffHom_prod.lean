-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.ShearCoefficients.CoeffHom.prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:04.310432+00:00
-- url     : https://prove2.me/submissions/9c622d70-9335-40e0-bbf3-6a2371ee2b43

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_CoeffHom_mul
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_CoeffHom_one

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
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.ShearCoefficients
variable {R : Type*} [CommRing R]
variable {σ M : Type*} [AddCommMonoid M] {wt : σ → M}
namespace Formalism.NormUnitaryCountingLemmas.ShearCoefficients
namespace CoeffHom
theorem _root_.solution {ι : Type*} (s : Finset ι) (P : ι → Polynomial (MvPolynomial σ R))
    (a : ι → M) (h : ∀ x ∈ s, CoeffHom wt (a x) (P x)) :
    CoeffHom wt (∑ x ∈ s, a x) (∏ x ∈ s, P x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CoeffHom.one (R := R) (wt := wt)
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact (h x (Finset.mem_insert_self _ _)).mul
      (ih fun y hy => h y (Finset.mem_insert_of_mem hy))
end CoeffHom
end Formalism.NormUnitaryCountingLemmas.ShearCoefficients
