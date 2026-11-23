-- Prove2me | solution 1 for Formalism.L2.PjFree.algPtLa_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:29.024025+00:00
-- url     : https://prove2.me/submissions/cb094b95-413d-4138-877f-88ba0c07cc9f

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree

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
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace Formalism.L2.PjFree
theorem _root_.solution (hN : XoNumPt Xo c) (hL : LocFld) : AlgPtLa Xo c := by
  intro la
  obtain ⟨L, _, _, j, x, hx⟩ := hN
  obtain ⟨T, k, e, hO, hF⟩ := hL c.F L j la
  refine ⟨T, k.comp j, e, hO, hF, spMap k ≫ x, ?_⟩
  have hx' : x ≫ Xo.s = spMap (j.comp (IntermediateField.inclusion c.le).toRingHom) := hx
  show (spMap k ≫ x) ≫ Xo.s = spMap ((k.comp j).comp (IntermediateField.inclusion c.le).toRingHom)
  rw [Category.assoc, hx']
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl
end Formalism.L2.PjFree
