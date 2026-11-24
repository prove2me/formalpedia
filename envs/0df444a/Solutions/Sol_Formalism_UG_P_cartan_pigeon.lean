-- Prove2me | solution 1 for Formalism.UG.P.cartan_pigeon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:11.369297+00:00
-- url     : https://prove2.me/submissions/24bf7809-27dc-475c-9aa1-6fe724c4b30c

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (O : Subring L) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
namespace Formalism.UG.P
theorem _root_.solution {m : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    ∃ j, j ≤ i ∧ i ≤ σ j := by
  by_contra hne
  push_neg at hne
  have hmaps : Set.MapsTo σ (Finset.Iic i : Set (Fin m)) (Finset.Iio i : Set (Fin m)) := by
    intro j hj
    simp only [Finset.coe_Iic, Finset.coe_Iio, Set.mem_Iic, Set.mem_Iio] at hj ⊢
    exact hne j hj
  have hc := Finset.card_le_card_of_injOn σ hmaps σ.injective.injOn
  simp at hc
end Formalism.UG.P
