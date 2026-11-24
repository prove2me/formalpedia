-- Prove2me | solution 1 for Formalism.GM.term_natDegree_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:02.890806+00:00
-- url     : https://prove2.me/submissions/a5dfdcbf-b431-4887-accf-e23fb53d98d9

import Definitions.Def_Formalism_MahlerMeasure_Statement
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
namespace Formalism.GM
theorem _root_.solution {K : Type*} [CommRing K] (u : ℤˣ) (p : K[X]) (N : ℕ)
    (hp : p.natDegree ≤ N) :
    (u • p).natDegree ≤ N ∧ (u • p).coeff N = u • p.coeff N := by
  refine ⟨?_, ?_⟩
  · rw [Units.smul_def]
    exact (Polynomial.natDegree_smul_le _ _).trans hp
  · rw [Units.smul_def, Units.smul_def, Polynomial.coeff_smul]
end Formalism.GM
