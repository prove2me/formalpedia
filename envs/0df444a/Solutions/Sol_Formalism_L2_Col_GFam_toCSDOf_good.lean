-- Prove2me | solution 1 for Formalism.L2.Col.GFam.toCSDOf_good
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:02.963932+00:00
-- url     : https://prove2.me/submissions/aaa46e1d-ca05-4d10-83b2-9d8718e6c690

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_toCSDOf_good


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
open Formalism.L2.Col.GFam
variable (F : GFam K)
namespace Formalism.L2.Col.GFam
theorem _root_.solution {n : ℕ} [Nonempty F.β] (G : F.Good n) (s : ∀ b, (F.mem b).Sec) :
    (F.toCSDOf (fun b => (G b).ok) s).Good n where
  symm := (G (Classical.arbitrary F.β)).symm
  nondeg := (G (Classical.arbitrary F.β)).nondeg
  inv := fun c γ x y => ((F.mem c.1).toCSDOf_good (G c.1) (s c.1)).inv c.2 γ x y
  nab_lat := fun c => (G c.1).nab_lat _
  del_le := fun c => (G c.1).del_le _
  del_stable := fun c γ y hy => ((F.mem c.1).toCSDOf_good (G c.1) (s c.1)).del_stable c.2 γ y hy
  s_pos := (G (Classical.arbitrary F.β)).s_pos
  dual_le := fun c => (G c.1).dual_le _
  del_dual := fun c => (G c.1).del_dual _
end Formalism.L2.Col.GFam
