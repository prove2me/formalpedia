-- Prove2me | solution 1 for Formalism.L2.PjFree.epsPt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:41.559556+00:00
-- url     : https://prove2.me/submissions/2cb150dc-853e-4ca3-83e8-c52c1a545bb1

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
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) : epsPt hv 0 = 1 := by
  have hm : (1 : tEps x ⟶ Xo.univ.t.G) =
      (Over.homMk (spMap (algebraMap S (DualNumber S))) (by rfl) : tEps x ⟶ Over.mk x) ≫ 1 := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc]
    congr 1
  have he : epsMul (0 : S) = (algebraMap S (DualNumber S)).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
    first
      | (ext d <;> simp [epsMul])
      | (refine RingHom.ext fun d => TrivSqZeroExt.ext ?_ ?_ <;>
          simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])
      | (refine RingHom.ext fun d => TrivSqZeroExt.ext ?_ ?_ <;>
          simp [epsMul, TrivSqZeroExt.map, TrivSqZeroExt.algebraMap_eq_inl])
  apply Over.OverMorphism.ext
  rw [hm, Over.comp_left]
  show (epsPt hv 0).left = spMap (algebraMap S (DualNumber S)) ≫ (1 : Over.mk x ⟶ Xo.univ.t.G).left
  rw [← hv.2, epsPt_left, ← Category.assoc, spMap_comp', he]
end Formalism.L2.PjFree
