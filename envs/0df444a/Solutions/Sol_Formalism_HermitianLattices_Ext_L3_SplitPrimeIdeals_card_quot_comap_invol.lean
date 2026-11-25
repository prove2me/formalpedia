-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals.card_quot_comap_invol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:03:55.933537+00:00
-- url     : https://prove2.me/submissions/73a8e8d8-7c0f-4fa4-b88e-6b94551d9748

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
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (P : Ideal B) :
    Nat.card (B ⧸ P.comap σ) = Nat.card (B ⧸ P) := by
  let e : B ≃+* B := RingEquiv.ofBijective σ
    ⟨Function.Involutive.injective hσ, surj_of_invol hσ⟩
  refine Nat.card_congr (Ideal.quotientEquiv (P.comap σ) P e ?_).toEquiv
  exact (Ideal.map_comap_of_surjective σ (surj_of_invol hσ) P).symm
end Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
