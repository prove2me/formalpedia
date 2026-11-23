-- Prove2me | solution 1 for Formalism.CountingSumsFrames.smul_mem_translateLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:57.711836+00:00
-- url     : https://prove2.me/submissions/47f23020-0edc-43b1-82ed-75132e49272e

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
theorem _root_.solution (R : Subring K) (L : Set (PolXY K k)) (hs : ∀ r ∈ R, ∀ f ∈ L, r • f ∈ L) (g : GL (Fin k) K)
    (r : K) (hr : r ∈ R) (f : PolXY K k) (hf : f ∈ latOf g L) : r • f ∈ latOf g L := by
  obtain ⟨a, ha, rfl⟩ := hf
  exact ⟨r • a, hs r hr a ha, map_smul _ _ _⟩
end Formalism.CountingSumsFrames
