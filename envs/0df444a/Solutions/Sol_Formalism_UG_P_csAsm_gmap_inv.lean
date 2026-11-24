-- Prove2me | solution 1 for Formalism.UG.P.csAsm_gmap_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:38:03.087057+00:00
-- url     : https://prove2.me/submissions/e037193e-2dc1-4aba-9601-f171ec4c605e

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LevelSubgroupFiniteAdelicStandard
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsAsmHformSmulRight
import Theorems.Thm_Formalism_UG_P_csAsm_gmap_mul
import Theorems.Thm_Formalism_UG_P_csAsm_gmap_one

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
open Formalism.UG Formalism.UG.CS
namespace Formalism.UG.P
theorem _root_.solution {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (a : V ≃ₗ[K] V)
    (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap a⁻¹ (Formalism.HermitianLatticesTheory.gmap a L) = L := by
  rw [← csAsm_gmap_mul, inv_mul_cancel, csAsm_gmap_one]
end Formalism.UG.P
