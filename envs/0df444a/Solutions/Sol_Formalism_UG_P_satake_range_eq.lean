-- Prove2me | solution 1 for Formalism.UG.P.satake_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:43:39.442019+00:00
-- url     : https://prove2.me/submissions/ff62a37e-54e6-4828-9729-b86691669748

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
import Theorems.Thm_Formalism_UG_P_satake_Tset_right
import Theorems.Thm_Formalism_UG_P_satake_cosets_card
import Theorems.Thm_Formalism_UG_P_satakeB_mem
import Theorems.Thm_Formalism_UG_P_satakeB_inj
import Theorems.Thm_Formalism_UG_P_satake_idx_card

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
namespace Formalism.UG.P
theorem _root_.solution [Fintype (satakeRes (Ov F v) ⟨ϖ, hϖ⟩)] (hTjCosets : TjCosets) {j : ℕ}
    (hj : j ≤ n) :
    Set.range (fun i : SatakeIdx v hϖ (n := n) j =>
      ((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion F)) :
        GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v))) =
    {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) | x.out ∈ satakeTset v ϖ j} := by
  obtain ⟨hfin, hcard⟩ := satake_cosets_card v hTjCosets hϖ hu hj
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ hfin
  · rintro _ ⟨i, rfl⟩
    obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul (GLint (Fin n) (Ov F v)) (satakeB v hϖ hu i)
    change (Quotient.out (((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion F)) :
        GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v)))) ∈ satakeTset v ϖ j
    have e : (Quotient.out (((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion F)) :
        GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v)))) = satakeB v hϖ hu i * κ := hκ
    rw [e]
    exact satake_Tset_right v (satakeB_mem v hϖ hu i) κ.2
  · rw [hcard, Set.ncard_range_of_injective (satakeB_inj v hϖ hu), satake_idx_card v hϖ hu j]
end Formalism.UG.P
