-- Prove2me | solution 1 for Formalism.IndefR.Eqv.G5.adl_eq_zero_of_mem_nbhd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:04:52.218431+00:00
-- url     : https://prove2.me/submissions/9e1467b1-81da-4f30-8302-2f022a59f155

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompactAdele
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IntAdCpctOpen
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_AdlEqZeroOfMemNbhd
import Theorems.Thm_Formalism_IndefR_Eqv_G5_adl_exists_place_ge_one
import Theorems.Thm_Formalism_IndefR_Eqv_G5_adl_norm_algebraMap

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
open Formalism Formalism.IndefR Formalism.IndefR.Eqv Formalism.IndefR.Eqv.G5
variable {F : Type} [Field F] [NumberField F]
open scoped AdeleRing
namespace Formalism.IndefR.Eqv.G5
theorem _root_.solution (a : F) (ha : algebraMap F (AdeleRing (𝓞 F) F) a ∈ adlNbhd F) : a = 0 := by
  obtain ⟨hinf, hfin⟩ := ha
  obtain ⟨r, hr⟩ : ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = a := by
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have hv := hfin v
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hv
    have e : (algebraMap F (AdeleRing (𝓞 F) F) a).2 v = (a : v.adicCompletion F) := rfl
    rw [e, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    exact hv
  by_contra ha0
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply ha0
    rw [← hr, map_zero]
  obtain ⟨w, hw⟩ := adl_exists_place_ge_one r hr0
  have h1 := hinf w
  have e1 : (algebraMap F (AdeleRing (𝓞 F) F) a).1 w = (algebraMap F (InfiniteAdeleRing F) a) w := rfl
  rw [e1, adl_norm_algebraMap, ← hr] at h1
  have h2 : w (r : F) < 1 := h1
  linarith
end Formalism.IndefR.Eqv.G5
