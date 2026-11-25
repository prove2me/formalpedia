-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.hasDerivAt_cv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:58:37.137304+00:00
-- url     : https://prove2.me/submissions/99807af3-eb0b-4347-94f5-dcbfa63c6197

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtCvs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtEpart
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_hasDerivAt_epart
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_list_sum_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_dscal_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_hasDerivAt_cvs


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
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) {X : Mat k r} (hX : inLie k r X) {g : Mat k r} (hg : g ∈ GPos D)
    (t : CT k r nf) (hnz : ∀ l, (t.a l ≠ 0 ∨ t.b l ≠ 0) → Dmin k r D.z D.z' g l ≠ 0)
    (hG : t.c ≠ 0 → ((Gf k r D.z D.z' g : ℝ) : ℂ) ≠ 0) (hes : ∀ e ∈ t.es, ∀ Y ∈ e.2, inLie k r Y) :
    HasDerivAt (fun s => cv D fib t (crv (false, X) g s)) (((dco D X t).map fun t' => cv D fib t' g).sum) 0 := by
  have h1 := hasDerivAt_cvs D X g t hnz hG
  have h2 := hasDerivAt_epart D fib hfib hX hg t.es hes
  have h3 := h1.smul h2
  show HasDerivAt (fun s => cvs D t (crv (false, X) g s) • C6.Epart fib t.es (crv (false, X) g s)) _ 0
  refine h3.congr_deriv ?_
  rw [crv_zero, dco, List.map_append, List.sum_append, add_comm]
  symm
  congr 1
  · rw [← list_sum_smul]
    exact congrArg List.sum (List.map_congr_left (fun t' ht' => by simp only [cv, dscal_es D X t t' ht']))
  · simp only [dfib, List.map_ofFn, List.sum_ofFn, Function.comp_def, cv, cvs, Finset.smul_sum]
end Formalism.FourierDecayAlt.P.MinorPolynomials
