-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:29:09.730788+00:00
-- url     : https://prove2.me/submissions/74bcafe7-ec92-4321-b588-ce09fa52e3cb

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MvPolynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
variable {N : ℕ}
namespace Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
theorem _root_.solution {l : ℕ} (M : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin l) (Fin l) ℂ)
    (h : ∀ a b, U.IsPolyDeg 1 (fun g => M g a b)) : U.IsPolyDeg l (fun g => (M g).det) := by
  have key : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin l))),
      U.IsPolyDeg l (fun g => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M g (σ i) i) := by
    intro σ _
    have h1 := pd_mul (pd_const (N := N) ((Equiv.Perm.sign σ : ℤ) : ℂ) 0)
      (pd_prod (Finset.univ : Finset (Fin l)) (fun i _ => h (σ i) i))
    refine pd_mono ?_ h1
    simp
  have h2 := pd_sum _ key
  simpa [Matrix.det_apply'] using h2
end Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
