-- Prove2me | solution 1 for Formalism.UG.P.satake_idx_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:24:41.936705+00:00
-- url     : https://prove2.me/submissions/3314c5f4-9852-4614-a86f-d9b6c21e4b04

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
import Theorems.Thm_Formalism_UG_P_satakePairs_card
import Theorems.Thm_Formalism_UG_P_satake_card_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
  {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (hu : IsUnifV F v ϖ)
include hu
namespace Formalism.UG.P
theorem _root_.solution [Fintype (satakeRes (Ov F v) ⟨ϖ, hϖ⟩)] (j : ℕ) :
    Nat.card (SatakeIdx v hϖ (n := n) j) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard j, qV F v ^ satakeInv Finset.univ S := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fun, satakePairs_card]
  rw [← Nat.card_eq_fintype_card, satake_card_res v hϖ hu]
  symm
  apply Finset.sum_subtype
  intro S
  simp [Finset.mem_powersetCard]
end Formalism.UG.P
