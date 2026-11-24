-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.dscal_es
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:18:34.505836+00:00
-- url     : https://prove2.me/submissions/c79301ad-8463-4eb9-9c7c-49c198b384a6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtCvs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtEpart

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (t : CT k r nf) :
    ∀ t' ∈ dscal D X t, t'.es = t.es := by
  intro t' ht'
  simp only [dscal, List.mem_append, List.mem_singleton, List.mem_ofFn, Set.mem_range] at ht'
  rcases ht' with ((h | ⟨m, h⟩) | ⟨m, h⟩) | h <;> subst h <;> (try split_ifs) <;> rfl
end Formalism.FourierDecayAlt.P.MinorPolynomials
