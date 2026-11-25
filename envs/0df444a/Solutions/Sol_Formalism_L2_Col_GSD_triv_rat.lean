-- Prove2me | solution 1 for Formalism.L2.Col.GSD.triv_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:07:31.013808+00:00
-- url     : https://prove2.me/submissions/504425e3-1bb7-429e-a3e3-53c5f11fb0e1

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_DIV_CSD_pairOne_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.GSD
variable (K)
namespace Formalism.L2.Col.GSD
theorem _root_.solution (G D : Type) [Group G] [MulAction G D] : (GSD.triv K G D).Rat where
  pair_rat := by
    intro (i : Unit) (j : Unit)
    show CSD.pairOne K ((Basis.singleton Unit K) i) ((Basis.singleton Unit K) j) ∈ cmMax K
    rw [CSD.pairOne_apply, Basis.singleton_apply, star_one, one_mul]
    exact (cmMax K).one_mem
  act_rat := by
    intro g (i : Unit) (j : Unit)
    show (Basis.singleton Unit K).repr ((1 : Module.End K K) ((Basis.singleton Unit K) j)) i ∈ cmMax K
    rw [Module.End.one_apply, Basis.repr_self]
    cases i; cases j
    simp
  pos := by
    intro v
    have : ((GSD.triv K G D).gramV.map v.embedding) = (1 : Matrix Unit Unit ℂ) := by
      ext (i : Unit) (j : Unit)
      show v.embedding (CSD.pairOne K ((Basis.singleton Unit K) i) ((Basis.singleton Unit K) j)) = _
      rw [CSD.pairOne_apply, Basis.singleton_apply, star_one, one_mul, map_one]
      rfl
    rw [this]
    exact Matrix.PosDef.one
end Formalism.L2.Col.GSD
