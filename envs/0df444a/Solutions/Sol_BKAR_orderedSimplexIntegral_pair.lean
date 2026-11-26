-- Prove2me | solution 1 for BKAR.orderedSimplexIntegral_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:20:29.029031+00:00
-- url     : https://prove2.me/submissions/47b7be93-1154-4e58-ad2b-3cf444d62e6c

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex

set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (e₁ e₂ : Edge V) (f : List ℝ → ℝ) :
    orderedSimplexIntegral [e₁, e₂] f =
      ∫ t₁ in 0..(1 : ℝ), ∫ t₂ in 0..t₁, f [t₁, t₂] :=
  rfl
end BKAR
