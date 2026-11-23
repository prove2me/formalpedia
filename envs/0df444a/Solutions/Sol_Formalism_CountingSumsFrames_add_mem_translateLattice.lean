-- Prove2me | solution 1 for Formalism.CountingSumsFrames.add_mem_translateLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:17.793538+00:00
-- url     : https://prove2.me/submissions/0bb415f8-f2b7-4468-ad49-0a674480a04f

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
theorem _root_.solution (L : Set (PolXY K k)) (hadd : ∀ f g, f ∈ L → g ∈ L → f + g ∈ L) (g : GL (Fin k) K)
    (f f' : PolXY K k) (hf : f ∈ latOf g L) (hf' : f' ∈ latOf g L) : f + f' ∈ latOf g L := by
  obtain ⟨a, ha, rfl⟩ := hf
  obtain ⟨b, hb, rfl⟩ := hf'
  exact ⟨a + b, hadd a b ha hb, map_add _ _ _⟩
end Formalism.CountingSumsFrames
