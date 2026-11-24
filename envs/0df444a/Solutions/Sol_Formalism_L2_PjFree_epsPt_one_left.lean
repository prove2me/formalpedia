-- Prove2me | solution 1 for Formalism.L2.PjFree.epsPt_one_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:40.756256+00:00
-- url     : https://prove2.me/submissions/b333fbb8-711e-4407-b44c-a13709f8d257

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
theorem _root_.solution {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) : (epsPt hv 1).left = v := by
  rw [epsPt_left]
  have h1 : epsMul (1 : S) = RingHom.id _ := by
    ext x <;> simp [epsMul]
  rw [h1]
  show Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ v = v
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
end Formalism.L2.PjFree
