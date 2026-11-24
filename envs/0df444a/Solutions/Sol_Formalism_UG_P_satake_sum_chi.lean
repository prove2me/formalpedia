-- Prove2me | solution 1 for Formalism.UG.P.satake_sum_chi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:24:09.526584+00:00
-- url     : https://prove2.me/submissions/8fa63efe-7605-40f5-b4c2-2918c70cd2e0

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
import Theorems.Thm_Formalism_UG_P_satake_exponent
import Theorems.Thm_Formalism_UG_P_satake_chiDelta_B
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
namespace Formalism.UG.P
theorem _root_.solution [Fintype (satakeRes (Ov F v) ⟨ϖ, hϖ⟩)] (α : Fin n → ℂ) (j : ℕ) :
    ∑ i : SatakeIdx v hϖ (n := n) j, chiDelta F v α (satakeB v hϖ hu i) =
      (qV F v : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) * Multiset.esymm (Multiset.map α Finset.univ.val) j := by
  rw [Fintype.sum_sigma]
  simp_rw [satake_chiDelta_B v hϖ hu α]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, satakePairs_card]
  rw [← Nat.card_eq_fintype_card, satake_card_res v hϖ hu, Finset.esymm_map_val, Finset.mul_sum]
  rw [← Finset.sum_subtype (Finset.univ.powersetCard j) (p := fun S : Finset (Fin n) => S.card = j)
    (f := fun S => (qV F v ^ satakeInv Finset.univ S) • ∏ a ∈ S,
      (α a * (qV F v : ℂ) ^ (-(((n : ℂ) - 1 - 2 * (a : ℂ)) / 2)))) (fun S => by
        simp [Finset.mem_powersetCard])]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hc := (Finset.mem_powersetCard.1 hS).2
  rw [nsmul_eq_mul, Nat.cast_pow, satake_exponent v α S, hc]
end Formalism.UG.P
