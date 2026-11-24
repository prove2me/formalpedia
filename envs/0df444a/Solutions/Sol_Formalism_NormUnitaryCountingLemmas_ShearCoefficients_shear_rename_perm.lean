-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.ShearCoefficients.shear_rename_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:11:25.776149+00:00
-- url     : https://prove2.me/submissions/e19dde0a-79a2-41f8-8f39-719721ed2b31

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients

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
namespace Formalism.NormUnitaryCountingLemmas.ShearCoefficients
theorem _root_.solution {N n : ℕ} (i j : Fin N) (σ : Equiv.Perm (Fin n))
    (F : MvPolynomial (Fin N × Fin n) R) :
    shear R i j (rename (fun p : Fin N × Fin n => (p.1, σ p.2)) F) =
      Polynomial.map (rename (R := R) (fun p : Fin N × Fin n => (p.1, σ p.2))).toRingHom
        (shear R i j F) := by
  have key : (shear R i j).comp (rename (fun p : Fin N × Fin n => (p.1, σ p.2))) =
      (Polynomial.mapAlgHom (rename (fun p : Fin N × Fin n => (p.1, σ p.2)))).comp
        (shear R i j) := by
    apply MvPolynomial.algHom_ext
    intro p
    by_cases h : p.1 = j <;> simp [shear, h]
  have h := congrArg (fun φ => φ F) key
  simpa [Polynomial.coe_mapAlgHom] using h
end Formalism.NormUnitaryCountingLemmas.ShearCoefficients
