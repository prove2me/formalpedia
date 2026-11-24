-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.localizedQuotients.form_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:45.138113+00:00
-- url     : https://prove2.me/submissions/7189e2ed-f60d-4353-9bce-eb57516f026a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_localizedQuotients_star___0cafaf6bb2bd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.localizedQuotients
open LocalSpans idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.localizedQuotients
theorem _root_.solution (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (a b : 𝓞 F) (x y : V) :
    h (ι a • x) (ι b • y) = algebraMap (𝓞 K) K (ι (a * b)) * h x y := by
  rw [← algebraMap_smul K (ι a), ← algebraMap_smul K (ι b), map_smul, map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul, starRingEnd_apply, star_ι hF, map_mul, map_mul]
  ring
end Formalism.HermitianLattices.Ext.L3.localizedQuotients
