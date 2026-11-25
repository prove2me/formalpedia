-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals.comap_comap_invol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:03:59.64551+00:00
-- url     : https://prove2.me/submissions/e92d8e5d-6df5-421b-9ee5-e666d4c9537c

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondVariant_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NotIsPrimeMapOfSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
variable {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B} {σ : B →+* B}
namespace Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (P : Ideal B) : (P.comap σ).comap σ = P := by
  ext x
  simp only [Ideal.mem_comap, hσ]
end Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
