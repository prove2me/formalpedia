-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals.comap_eq_map_invol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:07:11.686968+00:00
-- url     : https://prove2.me/submissions/182591a9-3838-4bc9-9666-d3ab1877bd98

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondVariant_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NotIsPrimeMapOfSplit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_surj_of_invol

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
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (P : Ideal B) : P.comap σ = P.map σ := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_map_iff_of_surjective σ (surj_of_invol hσ)]
  constructor
  · exact fun hx => ⟨σ x, hx, hσ x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [hσ]
end Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
