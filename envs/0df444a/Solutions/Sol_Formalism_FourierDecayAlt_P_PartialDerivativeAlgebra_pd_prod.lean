-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:22:59.617082+00:00
-- url     : https://prove2.me/submissions/6cfae316-8533-466d-ad6f-b075ce57e837

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_mul

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
theorem _root_.solution {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg (s.card * a) (fun g => ∏ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pd_const (N := N) 1 0
  | insert x s hx ih =>
    have h1 := pd_mul (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hc : (insert x s).card * a = a + s.card * a := by
      rw [Finset.card_insert_of_notMem hx]; ring
    rw [hc]
    simpa [Finset.prod_insert hx] using h1
end Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
