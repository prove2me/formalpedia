-- Prove2me | solution 1 for Formalism.L2.Col.fibre_card_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:54:16.558298+00:00
-- url     : https://prove2.me/submissions/bd7896f2-5806-4a01-a58a-7f69a4256d24

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
variable {G D D₀ : Type} [Group G] [MulAction G D] [MulAction G D₀] (pr : D → D₀)
  (hpr : ∀ (g : G) (d : D), pr (g • d) = g • pr d)
namespace Formalism.L2.Col
theorem _root_.solution (x : D₀) (y : fibre pr hpr x) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer G x) y) = Nat.card (MulAction.stabilizer G (y : D)) := by
  have h1 : ∀ γ : MulAction.stabilizer (MulAction.stabilizer G x) y,
      ((γ : MulAction.stabilizer G x) : G) ∈ MulAction.stabilizer G (y : D) := fun γ =>
    MulAction.mem_stabilizer_iff.mpr (congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp γ.2))
  have hy : pr (y : D) = x := y.2
  have h2 : ∀ g : MulAction.stabilizer G (y : D), (g : G) ∈ MulAction.stabilizer G x := by
    intro g
    have hg : (g : G) • (y : D) = y := MulAction.mem_stabilizer_iff.mp g.2
    refine MulAction.mem_stabilizer_iff.mpr ?_
    calc (g : G) • x = (g : G) • pr (y : D) := by rw [hy]
      _ = pr ((g : G) • (y : D)) := (hpr _ _).symm
      _ = pr (y : D) := by rw [hg]
      _ = x := hy
  have h3 : ∀ g : MulAction.stabilizer G (y : D),
      (⟨(g : G), h2 g⟩ : MulAction.stabilizer G x) ∈ MulAction.stabilizer (MulAction.stabilizer G x) y := fun g =>
    MulAction.mem_stabilizer_iff.mpr (Subtype.ext (MulAction.mem_stabilizer_iff.mp g.2))
  exact Nat.card_congr ⟨fun γ => ⟨_, h1 γ⟩, fun g => ⟨_, h3 g⟩, fun γ => rfl, fun g => rfl⟩
end Formalism.L2.Col
