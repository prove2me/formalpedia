-- Prove2me | solution 1 for Formalism.CountingSumsFrames.zero_mem_translateLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:12.523972+00:00
-- url     : https://prove2.me/submissions/94bb6073-6611-4ec5-8e88-507df2f0418c

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (L : Set (PolXY K k)) (h0 : (0 : PolXY K k) ∈ L) (g : GL (Fin k) K) :
    (0 : PolXY K k) ∈ latOf g L := ⟨0, h0, map_zero _⟩
end Formalism.CountingSumsFrames
