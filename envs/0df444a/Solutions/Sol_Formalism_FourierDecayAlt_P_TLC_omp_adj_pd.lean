-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TLC.omp_adj_pd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:31:07.533041+00:00
-- url     : https://prove2.me/submissions/32ac74bd-cded-4c8e-a998-cab1e732231c

import Definitions.Def_Formalism_HermitianCurvature_StatementTL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OmpCofLPd
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_zhat_star_pd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TLC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TLC
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg r (fun g => star (adjugate (Zhat k r z z' g) a b)) := by
  have e : (fun g => star (adjugate (Zhat k r z z' g) a b)) = fun g =>
      (fun _ => ((-1 : ℂ) ^ ((b : ℕ) + (a : ℕ)))) g *
        (((Zhat k r z z' g).submatrix b.succAbove a.succAbove)ᴴ).det := by
    funext g
    rw [adjugate_fin_succ_eq_det_submatrix, star_mul', det_conjTranspose, star_pow, star_neg, star_one]
  rw [e]
  have := pd_mul (pd_const (N := 2 * r + k + 1) ((-1 : ℂ) ^ ((b : ℕ) + (a : ℕ))) 0)
    (pd_det (l := r) (fun g => ((Zhat k r z z' g).submatrix b.succAbove a.succAbove)ᴴ) fun c d => by
      simpa [conjTranspose_apply] using zhat_star_pd k r z z' _ _)
  simpa using this
end Formalism.FourierDecayAlt.P.TLC
