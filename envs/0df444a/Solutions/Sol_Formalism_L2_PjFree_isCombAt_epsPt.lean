-- Prove2me | solution 1 for Formalism.L2.PjFree.isCombAt_epsPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:44.34346+00:00
-- url     : https://prove2.me/submissions/1f717768-8153-4c95-a271-57a708bf4f07

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Theorems.Thm_Formalism_L2_PjFree_epsPt_left

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
open Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open scoped WithZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace Formalism.L2.PjFree
theorem _root_.solution {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsTanAt x (v j)) (a : Fin m → S) :
    IsCombAt x v a ((List.ofFn fun i => epsPt (hv i) (a i)).prod.left) :=
  ⟨fun i => epsPt (hv i) (a i), fun i => epsPt_left (hv i) (a i), rfl⟩
end Formalism.L2.PjFree
