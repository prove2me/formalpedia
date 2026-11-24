-- Prove2me | solution 1 for Formalism.MainNotions.N.Br.PD_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:57:15.301807+00:00
-- url     : https://prove2.me/submissions/6beaf2a8-aac2-49c3-8efe-ba0169879875

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound

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
theorem _root_.solution : (PD L nbr i w hw).p = N.l i := (L (N.l i)).PD_p _
end Formalism.MainNotions.N.Br
