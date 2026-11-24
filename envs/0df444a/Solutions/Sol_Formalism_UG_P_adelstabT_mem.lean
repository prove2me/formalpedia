-- Prove2me | solution 1 for Formalism.UG.P.adelstabT_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:22:57.754242+00:00
-- url     : https://prove2.me/submissions/bc48d82c-8766-499a-92e4-22861e663b6a

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
import Theorems.Thm_Formalism_UG_P_adelstabT_tmul
import Theorems.Thm_Formalism_UG_P_adelstab_trace_int
import Theorems.Thm_Formalism_UG_P_levelaf_decomp
import Theorems.Thm_Formalism_UG_P_levelaf_int_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.UG.P
theorem _root_.solution {s : 𝒜} (hs : s ∈ 𝒮) : adelstabT F E s ∈ intAd F := by
  obtain ⟨r, hr, rfl⟩ := levelaf_decomp (fun j => Module.finBasis ℤ (𝓞 E) j)
    (Module.Basis.span_eq _) hs
  rw [map_sum]
  refine sum_mem fun j _ => ?_
  rw [adelstabT_tmul]
  obtain ⟨t, ht⟩ := adelstab_trace_int (F := F) (Module.finBasis ℤ (𝓞 E) j)
  rw [← ht, ← IsScalarTower.algebraMap_apply]
  exact mul_mem (levelaf_int_mem t) (hr j)
end Formalism.UG.P
