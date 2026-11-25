-- Prove2me | solution 1 for Formalism.MainNotions.N.Br.iota_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:32:14.815176+00:00
-- url     : https://prove2.me/submissions/36ad9f1c-3b9f-41f5-aa8a-04ca76d65963

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Theorems.Thm_P2M_Formalism_MainNotions_N_Br___cont_43903f940a18

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.WeaklyAdmissibleFiltrations Module
noncomputable section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations Module
open Formalism Formalism.MainNotions Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.N.Br
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
variable {N} (L : LocTheory) (nbr : NBr N) (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E))
  (hw : w ∈ placesOver H.E (N.l i))
namespace Formalism.MainNotions.N.Br
theorem _root_.solution : Continuous (iota nbr i w hw) := ι_cont (nbr i w hw)
end Formalism.MainNotions.N.Br
