-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.H1OnPoints.shear_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:11:16.014484+00:00
-- url     : https://prove2.me/submissions/492d498e-440d-4622-869a-64285d3a0553

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NatDegreeAevalLe

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
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.H1OnPoints
variable {R : Type*} [CommRing R]
namespace Formalism.NormUnitaryCountingLemmas.H1OnPoints
theorem _root_.solution {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} (i j : Fin N)
    (y : Fin N × Fin n → S) (s : S) (G : MvPolynomial (Fin N × Fin n) R) :
    Polynomial.eval₂ (aeval y).toRingHom s (shear R i j G) =
      aeval (fun p => y p + if p.1 = j then s * y (i, p.2) else 0) G := by
  induction G using MvPolynomial.induction_on with
  | C a =>
    simp [shear, Polynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, Polynomial.eval₂_add, hp, hq]
  | mul_X p q hp =>
    simp only [map_mul, Polynomial.eval₂_mul, hp]
    congr 1
    simp only [shear, aeval_X]
    split_ifs <;> simp <;> ring
end Formalism.NormUnitaryCountingLemmas.H1OnPoints
