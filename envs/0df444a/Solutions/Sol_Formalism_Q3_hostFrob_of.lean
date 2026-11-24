-- Prove2me | solution 1 for Formalism.Q3.hostFrob_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:32:09.110807+00:00
-- url     : https://prove2.me/submissions/059269b3-42f0-43e8-aaa4-4458ab1fc8d0

import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostFrob
import Theorems.Thm_Formalism_Q3_hostFrob_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.Q3
namespace Formalism.Q3
theorem _root_.solution (hF : MQFrob) (hH : HostGalois) (hK : KroneckerMeaning) : HostFrob := by
  intro q hq E _ _ α hα p _ hpq P _ _
  have hGal := hH q hq E α hα
  have : IsGalois ℚ E := hGal.1
  have : Finite (𝓞 E ⧸ P) := by
    have hpb : span {(p : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb P)
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(E/ℚ) P
  refine ⟨⟨τ, hτ⟩, fun σ => ⟨fun H i => hostFrob_val hF hK q hq E α hα p hpq P σ H i,
    fun h => ?_⟩⟩
  have hτv := hostFrob_val hF hK q hq E α hα p hpq P τ hτ
  have : σ = τ := hGal.2.2.1.1 (funext fun i => Units.ext ((h i).trans (hτv i).symm))
  subst this
  exact hτ
end Formalism.Q3
