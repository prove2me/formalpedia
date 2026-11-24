-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.exists_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:55:14.192973+00:00
-- url     : https://prove2.me/submissions/d4b716a9-30d5-40b0-a0ff-ff8b2abe012c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_eq_of_prod_eq
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_rho_anti
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_ty_ext
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_Pp_OK
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_eval_xPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {P : M.Par} (hP : P.OK) :
    ∃ Y₀ : ℂ, Function.Injective (fun σ : M.Ty (Pp P) => M.xC (Pp P) σ Y₀) := by
  classical
  have gPp : ∀ i ∈ Icc 1 ((Pp P).k - 1), (Pp P).lo i ≤ (Pp P).hi i := (Pp_OK hP).gap
  have hne : ∀ σ σ' : M.Ty (Pp P), σ ≠ σ' → cb_xPoly (Pp P) σ - cb_xPoly (Pp P) σ' ≠ 0 := by
    intro σ σ' hss h0
    apply hss
    have hx : ∀ Y, M.xC (Pp P) σ Y = M.xC (Pp P) σ' Y := by
      intro Y
      rw [← cb_eval_xPoly, ← cb_eval_xPoly, sub_eq_zero.mp h0]
    have e := cb_eq_of_prod_eq (n := (Pp P).k - 1) (cb_rho_anti _ gPp σ) (cb_rho_anti _ gPp σ') hx
    exact cb_ty_ext _ (fun j => e _ (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩))
  obtain ⟨Y₀, hY⟩ := Infinite.exists_notMem_finset
    ((Finset.univ : Finset (M.Ty (Pp P) × M.Ty (Pp P))).biUnion
      (fun p => if p.1 = p.2 then ∅ else (cb_xPoly (Pp P) p.1 - cb_xPoly (Pp P) p.2).roots.toFinset))
  refine ⟨Y₀, fun σ σ' h => ?_⟩
  by_contra hss
  apply hY
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine ⟨(σ, σ'), ?_⟩
  rw [if_neg hss, Multiset.mem_toFinset, Polynomial.mem_roots (hne σ σ' hss), Polynomial.IsRoot.def,
    Polynomial.eval_sub, cb_eval_xPoly, cb_eval_xPoly, sub_eq_zero]
  exact h
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
