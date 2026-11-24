-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.hasDerivAt_epart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:46:33.43485+00:00
-- url     : https://prove2.me/submissions/444182c5-8b25-4226-8f82-2a67d1ef178d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtCvs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtEpart
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_Rw_cons__735539f794a9
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_ckOn_Rw_top
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) {X : Mat k r} (hX : inLie k r X) {g : Mat k r} (hg : g ∈ GPos D) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ Y ∈ e.2, inLie k r Y) →
      HasDerivAt (fun s => C6.Epart fib es (crv (false, X) g s))
        (∑ i : Fin es.length, C6.Epart fib (es.set i ((es.get i).1, X :: (es.get i).2)) g) 0 := by
  intro es
  induction es with
  | nil =>
    intro _
    simp only [C6.Epart, List.map_nil, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact hasDerivAt_const _ _
  | cons e es ih =>
    intro hes
    have h1 : HasDerivAt (fun s => Rw e.2 (fib e.1) (crv (false, X) g s)) (Rw (X :: e.2) (fib e.1) g) 0 := by
      rw [Rw_cons']
      exact CkOn_diff (x := (false, X)) hX
        (sCkOn_mono le_top (ckOn_Rw_top (hfib e.1) (hes e (by simp)))) hg hg.1
    have h2 := ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    have h3 := h1.mul h2
    show HasDerivAt (fun s => Rw e.2 (fib e.1) (crv (false, X) g s) * C6.Epart fib es (crv (false, X) g s)) _ 0
    refine h3.congr_deriv ?_
    have key : ∀ f : Fin (e :: es).length → C6.EndH Wp Wq,
        ∑ i, f i = f ⟨0, by simp⟩ + ∑ i : Fin es.length, f i.succ := fun f => Fin.sum_univ_succ f
    rw [key, crv_zero]
    simp [C6.Epart, Finset.mul_sum]
end Formalism.FourierDecayAlt.P.MinorPolynomials
