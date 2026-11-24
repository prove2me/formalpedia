-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.coeff_zero_ne_zero_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:52.475341+00:00
-- url     : https://prove2.me/submissions/b0dadd35-9229-4ec6-988d-bf64d1e4f20f

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRFrobOrbitIrred
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSamePartCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CoeffZeroNeZeroOfIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {f : K[X]} (hi : Irreducible f) (hd : 2 ≤ f.natDegree) :
    f.coeff 0 ≠ 0 := by
  intro h0
  have hX : (X : K[X]) ∣ f := Polynomial.X_dvd_iff.2 h0
  have hass := Polynomial.irreducible_X.associated_of_dvd hi hX
  have hdeg := Polynomial.degree_eq_degree_of_associated hass
  rw [Polynomial.degree_X] at hdeg
  have : f.natDegree = 1 := Polynomial.natDegree_eq_of_degree_eq_some hdeg.symm
  omega
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
