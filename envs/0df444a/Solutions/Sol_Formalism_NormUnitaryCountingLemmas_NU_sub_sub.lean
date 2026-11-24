-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.NU.sub_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:11:09.153165+00:00
-- url     : https://prove2.me/submissions/b04881c1-176b-4e49-91d9-619e0aae86fb

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.NU
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
namespace Formalism.NormUnitaryCountingLemmas.NU
theorem _root_.solution (V : Matrix σ σ ℂ) (hV : V * star V = 1) (F : MvPolynomial σ ℂ) :
    sub (star V) (sub V F) = F := by
  have key : (sub (star V)).comp (sub V) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, sub, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
      AlgHom.id_apply]
    simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← map_sum]
    have h2 : ∀ k, ∑ l, V i l * star V l k = (1 : Matrix σ σ ℂ) i k := fun k => by
      rw [← hV, Matrix.mul_apply]
    simp_rw [h2, Matrix.one_apply]
    simp
  simpa using AlgHom.congr_fun key F
end Formalism.NormUnitaryCountingLemmas.NU
