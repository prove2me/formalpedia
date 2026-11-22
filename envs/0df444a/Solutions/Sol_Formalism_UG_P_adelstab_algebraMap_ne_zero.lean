-- Prove2me | solution 1 for Formalism.UG.P.adelstab_algebraMap_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:04:01.29582+00:00
-- url     : https://prove2.me/submissions/6cbc7440-a394-4768-ab92-7a3e695d3413

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab

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
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.UG.P
theorem _root_.solution (d : 𝓞 F) (hd : d ≠ 0) : algebraMap (𝓞 F) E d ≠ 0 := by
  intro h
  apply hd
  first
  | exact (FaithfulSMul.algebraMap_injective (𝓞 F) E) (h.trans (map_zero _).symm)
  | (rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, map_eq_zero_iff _ (algebraMap F E).injective] at h
     exact IsFractionRing.injective (𝓞 F) F (h.trans (map_zero _).symm))
  | simpa using h
end Formalism.UG.P
