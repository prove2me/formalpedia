-- Prove2me | solution 1 for Formalism.L2.Col.GSD.card_stab_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:15.129577+00:00
-- url     : https://prove2.me/submissions/1898ac44-6a97-4b49-b06a-967fea1c3445

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas

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
variable (S : GSD K)
namespace Formalism.L2.Col.GSD
theorem _root_.solution (g : S.G) (d : S.D) :
    Nat.card (MulAction.stabilizer S.G (g • d)) = Nat.card (MulAction.stabilizer S.G d) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨g⁻¹ * (x : S.G) * g, ?_⟩
      invFun := fun y => ⟨g * (y : S.G) * g⁻¹, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun y => ?_ }
  · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, MulAction.mem_stabilizer_iff.mp x.2, inv_smul_smul]
  · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul, MulAction.mem_stabilizer_iff.mp y.2]
  · exact Subtype.ext (by simp [mul_assoc])
  · exact Subtype.ext (by simp [mul_assoc])
end Formalism.L2.Col.GSD
