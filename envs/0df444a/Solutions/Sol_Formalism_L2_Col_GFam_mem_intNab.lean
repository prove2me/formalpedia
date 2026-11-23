-- Prove2me | solution 1 for Formalism.L2.Col.GFam.mem_intNab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:58.348397+00:00
-- url     : https://prove2.me/submissions/e9fdd1a1-c932-4c1d-839b-7eea1a19db3c

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
open Formalism.L2.Col.GFam
variable (F : GFam K)
namespace Formalism.L2.Col.GFam
theorem _root_.solution (φ : F.Forms) : φ ∈ F.intNab ↔ ∀ b, φ b ∈ (F.mem b).intNab := by
  unfold intNab
  rw [Submodule.mem_pi]
  exact ⟨fun H b => H b (Set.mem_univ b), fun H b _ => H b⟩
end Formalism.L2.Col.GFam
