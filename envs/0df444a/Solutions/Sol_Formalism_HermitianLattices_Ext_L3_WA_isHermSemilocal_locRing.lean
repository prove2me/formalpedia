-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.isHermSemilocal_locRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:28.929361+00:00
-- url     : https://prove2.me/submissions/17c85f1a-286d-484f-9b2f-63847242b879

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapNeZeroOfMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsHermSemilocalLocRing
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_principal_locRing
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_unit_or_locRing
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_frac_locRing
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_star_mem_locRing
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_unram_locRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.WA
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)}
    (hp : p.IsMaximal) : IsHermSemilocal (locRing p) where
  star_mem := fun _ ha => star_mem_locRing hp.isPrime ha
  frac := frac_locRing p
  unram := unram_locRing hK hp
  principal := principal_locRing hK hp
  unit_or := fun a ha κ hκ μ hna hμ => unit_or_locRing hp.isPrime a ha κ hκ μ hna hμ
end Formalism.HermitianLattices.Ext.L3.WA
