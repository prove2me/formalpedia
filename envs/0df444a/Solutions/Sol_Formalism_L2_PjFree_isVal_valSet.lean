-- Prove2me | solution 1 for Formalism.L2.PjFree.isVal_valSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:11:17.475799+00:00
-- url     : https://prove2.me/submissions/dacc2e7e-4e22-4950-a1ba-86264d4b2084

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RulInst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
import Theorems.Thm_Formalism_L2_PjFree_isVal_vAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.PjFree
open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
  (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop)
variable {Xo c cls}
namespace Formalism.L2.PjFree
theorem _root_.solution (la : HeightOneSpectrum (𝓞 c.F)) : ∀ v ∈ valSet Xo c cls la, IsVal la v := by
  rintro v ⟨y, rfl⟩
  exact isVal_vAt y
end Formalism.L2.PjFree
