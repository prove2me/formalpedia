-- Prove2me | solution 1 for ContinuumHypothesis.Constructible.models_AC
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-24T01:41:02.715986+00:00
-- url     : https://prove2.me/submissions/9c2ac23b-f343-4f3f-bf91-c3230ba7c160

import Definitions.Def_CH_ConstructibleAC_Library15
import Definitions.Def_CH_Constructible
import Mathlib.Data.List.Shortlex
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Sigma.Lex
import Mathlib.Data.Sum.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Tactic.FinCases

/-!
# Adaptation of Zike Liu's constructible-universe Choice proof

Original formalization: Copyright (c) 2026 Zike Liu, Apache-2.0.
Source: https://github.com/05-02-07/lean-constructible-universe
Commit: 7f5a7d03d63d9769172f17350bbe8303996e5b53.
All original per-file copyright notices are retained below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

This credit concerns the Prove2Me adaptation and semantic bridge. The original
well-ordering formalization is by Zike Liu, credited above and in each source section.
-/

set_option autoImplicit false


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Bounding -/
section CUAdapterModule5
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Stage bounds in the constructible hierarchy

This file collects the external bounding facts used to turn set-indexed
families of constructible sets into constructions inside one level of `L`.
The index type of the members of a `ZFSet` is small, so a family of witnesses
in `Ordinal.{u}` has a supremum in the same universe.
-/


open Set

universe u

namespace Constructible

section ZFC









/-- Every member of a constructible set is bounded by one constructible level. -/
theorem exists_LStage_for_constructible_members {a : ZFSet.{u}} (ha : a ∈ L) :
    ∃ α : Ordinal.{u}, ∀ x ∈ a, x ∈ LStageZF α :=
  exists_LStage_for_members fun _x hx => mem_L_of_mem hx ha

end ZFC

end Constructible
end CUAdapterModule5



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalWellOrder -/
section CUAdapterModule49
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Internal well-orders and Choice in the constructible universe

An external Lean relation is not enough to prove Choice inside `L`: its graph
must itself be represented by a constructible set.  This file isolates that
requirement.  A constructible set `r` represents the relation
`x <_r y` when the Kuratowski pair `⟨x,y⟩` belongs to `r`.

We prove that if every constructible set is well-orderable by such a
constructible graph, then `L` satisfies the disjoint-family form of Choice and
hence Mathlib's canonical first-order theory ZFC. The proposition
`ModelsInternalWellOrdering` is the interface used to derive these results.
-/


open Set

universe u

namespace Constructible

namespace Delta0Formula

/-! ## Bounded absoluteness for the proper class `L` -/





end Delta0Formula

namespace Model

/-! ## Relations represented by constructible graphs -/











/-! ## The object-language graph predicate -/















/-! ## Unique minima from an internal well-order -/

/-- Every nonempty subset of an internally well-ordered set has a unique minimum. -/
theorem exists_unique_graph_minimum {a r x : LCarrier.{u}}
    (hwo : InternallyWellOrders r a)
    (hxsub : forall z : LCarrier.{u}, z.1 ∈ x.1 -> z.1 ∈ a.1)
    (hxne : exists z : LCarrier.{u}, z.1 ∈ x.1) :
    exists y : LCarrier.{u},
      (y.1 ∈ x.1 /\
        forall z : LCarrier.{u}, z.1 ∈ x.1 -> Not (GraphRel r z y)) /\
      forall y' : LCarrier.{u},
        (y'.1 ∈ x.1 /\
          forall z : LCarrier.{u}, z.1 ∈ x.1 ->
            Not (GraphRel r z y')) ->
        y' = y := by
  let candidates : Set (InternalCarrier a) :=
    {z | z.1.1 ∈ x.1}
  have hcandidates : candidates.Nonempty := by
    rcases hxne with ⟨z, hzx⟩
    exact ⟨⟨z, hxsub z hzx⟩, hzx⟩
  letI : IsWellOrder (InternalCarrier a) (graphRelOn r a) := hwo
  let minimum : InternalCarrier a :=
    (IsWellFounded.wf : WellFounded (graphRelOn r a)).min
      candidates hcandidates
  have hminimumMem : minimum ∈ candidates :=
    (IsWellFounded.wf : WellFounded (graphRelOn r a)).min_mem
      candidates hcandidates
  have hminimum : forall z : LCarrier.{u}, z.1 ∈ x.1 ->
      Not (GraphRel r z minimum.1) := by
    intro z hzx hzlt
    let za : InternalCarrier a := ⟨z, hxsub z hzx⟩
    exact
      (IsWellFounded.wf : WellFounded (graphRelOn r a)).not_lt_min
        candidates (show za ∈ candidates from hzx) hzlt
  refine ⟨minimum.1, ⟨hminimumMem, hminimum⟩, ?_⟩
  · intro y' hy'
    let y'a : InternalCarrier a := ⟨y', hxsub y' hy'.1⟩
    rcases trichotomous_of (graphRelOn r a) y'a minimum with
      hy'lt | heq | hminlt
    · exact False.elim (hminimum y' hy'.1 hy'lt)
    · exact congrArg (fun z : InternalCarrier a => z.1) heq
    · exact False.elim (hy'.2 minimum.1 hminimumMem hminlt)

/-! ## Choice and ZFC -/

/-- Internal well-ordering of every constructible set implies Choice in `L`. -/
theorem lCarrier_modelsChoice_of_internalWellOrdering
    (hwo : ModelsInternalWellOrdering.{u}) :
    FirstOrder.SetTheory.ModelsChoice LCarrier.{u} := by
  intro family hnonempty hdisjoint
  let unionFamily : LCarrier.{u} := sUnionLCarrier family
  rcases hwo unionFamily with ⟨r, hr⟩
  have hmin : forall x : LCarrier.{u}, x.1 ∈ family.1 ->
      (exists y : LCarrier.{u}, y.1 ∈ x.1) ->
      exists y : LCarrier.{u},
        (y.1 ∈ x.1 /\
          forall z : LCarrier.{u}, z.1 ∈ x.1 ->
            Not (GraphRel r z y)) /\
        forall y' : LCarrier.{u},
          (y'.1 ∈ x.1 /\
            forall z : LCarrier.{u}, z.1 ∈ x.1 ->
              Not (GraphRel r z y')) ->
          y' = y := by
    intro x hxfamily hxne
    apply exists_unique_graph_minimum hr
    · intro z hzx
      exact (mem_sUnionLCarrier_iff family z).mpr
        ⟨x, hxfamily, hzx⟩
    · exact hxne
  let params : Tuple LCarrier.{u} 2 := ![family, r]
  rcases exists_separationLCarrier graphLeastMemberPredicate
      params unionFamily with
    ⟨choiceSet, hchoiceSet⟩
  refine ⟨choiceSet, ?_⟩
  intro x hxfamily
  rcases hmin x hxfamily (hnonempty x hxfamily) with
    ⟨y, ⟨hyx, hymin⟩, hyunique⟩
  refine ⟨y, hyx, ?_, ?_⟩
  · apply (hchoiceSet y).mpr
    refine ⟨?_, ?_⟩
    · exact (mem_sUnionLCarrier_iff family y).mpr
        ⟨x, hxfamily, hyx⟩
    · apply (satisfies_graphLeastMemberPredicate
        (snoc params y)).mpr
      refine ⟨x, ?_, hyx, ?_⟩
      · simpa [params, snoc_eq_finSnoc] using hxfamily
      · simpa [params, snoc_eq_finSnoc] using hymin
  · intro z hzx hzchoice
    have hzSelected := (hchoiceSet z).mp hzchoice
    rcases (satisfies_graphLeastMemberPredicate
        (snoc params z)).mp hzSelected.2 with
      ⟨x', hx'family, hzx', hzmin⟩
    have hxx' : x = x' := by
      by_contra hne
      exact hdisjoint x hxfamily x'
        (by simpa [params, snoc_eq_finSnoc] using hx'family) hne z hzx hzx'
    subst x'
    apply hyunique z
    refine ⟨hzx, ?_⟩
    simpa [params, snoc_eq_finSnoc] using hzmin



end Model

end Constructible
end CUAdapterModule49



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageInternalOrder -/
section CUAdapterModule79
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# From internally represented stage orders to Choice

Every constructible set is contained in some level `L_alpha`.  Consequently,
it is enough to construct, for every level, a well-order whose Kuratowski-pair
graph is itself a member of `L`.  This file proves that reduction and states
the exact internalization obligation for the external birth-layer order from
`StageOrder`.
-/


open Set

universe u

namespace Constructible

namespace Model











/-- Restricting an internally represented stage well-order preserves it. -/
theorem internallyWellOrders_of_stage
    {a : LCarrier.{u}} {alpha : Ordinal.{u}}
    (ha : forall x : ZFSet.{u}, x ∈ a.1 -> x ∈ LStageZF alpha)
    {r : LCarrier.{u}}
    (hr : IsWellOrder (LStageCarrier alpha) (stageGraphRel r alpha)) :
    InternallyWellOrders r a := by
  let stageEmbedding : InternalCarrier a -> LStageCarrier alpha :=
    fun x => ⟨x.1.1, ha x.1.1 x.2⟩
  have hinclude : Function.Injective stageEmbedding := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : LStageCarrier alpha => z.1) hxy
  change IsWellOrder (InternalCarrier a)
    (InvImage (stageGraphRel r alpha) stageEmbedding)
  letI : IsWellOrder (LStageCarrier alpha) (stageGraphRel r alpha) := hr
  exact
    { wf := InvImage.wf stageEmbedding
        (IsWellFounded.wf : WellFounded (stageGraphRel r alpha))
      trichotomous :=
        (InvImage.trichotomous (r := stageGraphRel r alpha)
          hinclude).trichotomous }

/-- Internally represented well-orders of all levels give them for all sets. -/
theorem modelsInternalWellOrdering_of_allStages
    (hstage : AllStagesInternallyWellOrdered.{u}) :
    ModelsInternalWellOrdering.{u} := by
  intro a
  rcases exists_LStage_for_constructible_members a.2 with
    ⟨alpha, halpha⟩
  rcases hstage alpha with ⟨r, hr⟩
  exact ⟨r, internallyWellOrders_of_stage halpha hr⟩

/-- Stage graph internalization is sufficient for Choice in `L`. -/
theorem lCarrier_modelsChoice_of_allStagesInternallyWellOrdered
    (hstage : AllStagesInternallyWellOrdered.{u}) :
    FirstOrder.SetTheory.ModelsChoice LCarrier.{u} :=
  lCarrier_modelsChoice_of_internalWellOrdering
    (modelsInternalWellOrdering_of_allStages hstage)



/-! ## Alternative conditional birth-layer route

This section gives a conditional reduction through an externally specified
birth-layer order. The model theorem in `StageHistoryGraphSystem.lean` is
independent of this interface and constructs coherent internal graphs through
stage histories.
-/











end Model

end Constructible
end CUAdapterModule79



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.CoherentStageGraphExtension -/
section CUAdapterModule96
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Adjoining one graph to a coherent stage system

Successor and limit constructions both produce a graph at one new ordinal,
together with support, agreement, and initial-segment facts relative to all
earlier stages.  This file packages that common interface and proves that
adjoining such a graph preserves the complete coherent-system invariant.
-/


open Set

universe u

namespace Constructible.Model

noncomputable section













/-- Adjoining a valid extension preserves well-ordering, support, coherence,
and all earlier initial segments. -/
theorem coherentStageGraphSystem_append
    (alpha : Ordinal.{u})
    (graphs : Set.Iio alpha → LCarrier.{u})
    (hsystem : CoherentStageGraphSystem alpha graphs)
    (extension : StageGraphExtension alpha graphs) :
    CoherentStageGraphSystem (Order.succ alpha)
      (appendStageGraph alpha graphs extension.nextRelation) := by
  refine
    { wellOrders := ?_
      supported := ?_
      coherent := ?_
      initial := ?_ }
  · intro beta
    by_cases hbeta : beta.1 < alpha
    · simpa only [appendStageGraph, dif_pos hbeta] using
        hsystem.wellOrders ⟨beta.1, hbeta⟩
    · have hbetaLe : beta.1 ≤ alpha :=
        Order.lt_succ_iff.mp beta.2
      have hbetaEq : beta.1 = alpha :=
        le_antisymm hbetaLe (le_of_not_gt hbeta)
      have happend :
          appendStageGraph alpha graphs extension.nextRelation beta =
            extension.nextRelation := by
        rw [appendStageGraph, dif_neg hbeta]
      rw [happend, hbetaEq]
      exact extension.wellOrders
  · intro beta x y hxy
    by_cases hbeta : beta.1 < alpha
    · have hxyEarlier :
          GraphRel (graphs ⟨beta.1, hbeta⟩) x y := by
        simpa only [appendStageGraph, dif_pos hbeta] using hxy
      exact hsystem.supported ⟨beta.1, hbeta⟩ x y hxyEarlier
    · have hbetaLe : beta.1 ≤ alpha :=
        Order.lt_succ_iff.mp beta.2
      have hbetaEq : beta.1 = alpha :=
        le_antisymm hbetaLe (le_of_not_gt hbeta)
      have hxyTop : GraphRel extension.nextRelation x y := by
        simpa only [appendStageGraph, dif_neg hbeta] using hxy
      simpa only [hbetaEq] using extension.supported x y hxyTop
  · intro beta gamma hbetaGamma x y hx hy
    by_cases hgamma : gamma.1 < alpha
    · have hbeta : beta.1 < alpha :=
        lt_of_le_of_lt hbetaGamma hgamma
      simpa only [appendStageGraph, dif_pos hbeta, dif_pos hgamma] using
        hsystem.coherent
          ⟨beta.1, hbeta⟩ ⟨gamma.1, hgamma⟩
          hbetaGamma x y hx hy
    · have hgammaLe : gamma.1 ≤ alpha :=
        Order.lt_succ_iff.mp gamma.2
      have hgammaEq : gamma.1 = alpha :=
        le_antisymm hgammaLe (le_of_not_gt hgamma)
      by_cases hbeta : beta.1 < alpha
      · simpa only [appendStageGraph, dif_pos hbeta, dif_neg hgamma] using
          extension.agreesOnEarlier ⟨beta.1, hbeta⟩ x y hx hy
      · simp only [appendStageGraph, dif_neg hbeta, dif_neg hgamma]
  · intro beta gamma hbetaGamma x y hx hy hgraph
    by_cases hgamma : gamma.1 < alpha
    · have hbeta : beta.1 < alpha :=
        lt_of_le_of_lt hbetaGamma hgamma
      have hgraphEarlier :
          GraphRel (graphs ⟨gamma.1, hgamma⟩) y x := by
        simpa only [appendStageGraph, dif_pos hgamma] using hgraph
      exact hsystem.initial
        ⟨beta.1, hbeta⟩ ⟨gamma.1, hgamma⟩
        hbetaGamma x y hx hy hgraphEarlier
    · have hgammaLe : gamma.1 ≤ alpha :=
        Order.lt_succ_iff.mp gamma.2
      have hgammaEq : gamma.1 = alpha :=
        le_antisymm hgammaLe (le_of_not_gt hgamma)
      by_cases hbeta : beta.1 < alpha
      · have hgraphTop : GraphRel extension.nextRelation y x := by
          simpa only [appendStageGraph, dif_neg hgamma] using hgraph
        have hyTop : y.1 ∈ LStageZF alpha := by
          simpa only [hgammaEq] using hy
        exact extension.earlierIsInitial
          ⟨beta.1, hbeta⟩ x y hx hyTop hgraphTop
      · have hbetaLe : beta.1 ≤ alpha :=
          hbetaGamma.trans hgammaLe
        have hbetaEq : beta.1 = alpha :=
          le_antisymm hbetaLe (le_of_not_gt hbeta)
        simpa only [hbetaEq, hgammaEq] using hy





/-! ## The zero and successor extensions -/















end

end Constructible.Model
end CUAdapterModule96



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryGraphSystem -/
section CUAdapterModule98
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The coherent graph system generated by stage histories

The local extension theorem is iterated over all ordinals.  At a limit bound,
each required pair of graphs already occurs together in the coherent system
through the successor of the later index.
-/


open Set

universe u

namespace Constructible.Model

noncomputable section

/-- Restricting the global graph assignment to a successor bound is the same
as appending the graph at its last index. -/
theorem historyStageGraphs_succ_eq_append (alpha : Ordinal.{u}) :
    historyStageGraphs (Order.succ alpha) =
      appendStageGraph alpha (historyStageGraphs alpha)
        (stageHistoryData alpha).relation := by
  funext beta
  by_cases hbeta : beta.1 < alpha
  · rw [appendStageGraph, dif_pos hbeta]
    rfl
  · have hbetaLe : beta.1 ≤ alpha :=
      Order.lt_succ_iff.mp (Set.mem_Iio.mp beta.2)
    have hbetaEq : beta.1 = alpha :=
      le_antisymm hbetaLe (le_of_not_gt hbeta)
    rw [appendStageGraph, dif_neg hbeta]
    exact congrArg (fun ordinal => (stageHistoryData ordinal).relation)
      hbetaEq



/-- The internally recursive stage graphs form a coherent system below every
ordinal bound. -/
theorem historyStageGraphs_coherent (bound : Ordinal.{u}) :
    CoherentStageGraphSystem bound (historyStageGraphs bound) := by
  induction bound using Ordinal.limitRecOn with
  | zero =>
      refine
        { wellOrders := ?_
          supported := ?_
          coherent := ?_
          initial := ?_ }
      · intro beta
        exact (not_lt_of_ge bot_le (Set.mem_Iio.mp beta.2)).elim
      · intro beta
        exact (not_lt_of_ge bot_le (Set.mem_Iio.mp beta.2)).elim
      · intro beta
        exact (not_lt_of_ge bot_le (Set.mem_Iio.mp beta.2)).elim
      · intro beta
        exact (not_lt_of_ge bot_le (Set.mem_Iio.mp beta.2)).elim
  | add_one alpha ih =>
      rw [← Order.succ_eq_add_one]
      let extensionData := historyStageGraphExtension alpha ih
      have happend : CoherentStageGraphSystem (Order.succ alpha)
          (appendStageGraph alpha (historyStageGraphs alpha)
            extensionData.extension.nextRelation) :=
        coherentStageGraphSystem_append alpha
          (historyStageGraphs alpha) ih extensionData.extension
      rw [extensionData.nextRelation_eq] at happend
      rw [← historyStageGraphs_succ_eq_append alpha] at happend
      exact happend
  | limit limit hl ih =>
      refine
        { wellOrders := ?_
          supported := ?_
          coherent := ?_
          initial := ?_ }
      · intro beta
        have hsucc : Order.succ beta.1 < limit :=
          hl.succ_lt (Set.mem_Iio.mp beta.2)
        have hlocal :=
          (ih (Order.succ beta.1) hsucc).wellOrders
            (lastStageIndex beta.1)
        simpa only [historyStageGraphs_last, historyStageGraphs_apply,
          lastStageIndex_val] using hlocal
      · intro beta x y hxy
        have hsucc : Order.succ beta.1 < limit :=
          hl.succ_lt (Set.mem_Iio.mp beta.2)
        have hlocal :=
          (ih (Order.succ beta.1) hsucc).supported
            (lastStageIndex beta.1) x y
        apply hlocal
        simpa only [historyStageGraphs_apply, lastStageIndex_val] using hxy
      · intro beta gamma hbetaGamma x y hx hy
        have hsucc : Order.succ gamma.1 < limit :=
          hl.succ_lt (Set.mem_Iio.mp gamma.2)
        let beta' : Set.Iio (Order.succ gamma.1) :=
          ⟨beta.1, lt_of_le_of_lt hbetaGamma (Order.lt_succ gamma.1)⟩
        let gamma' : Set.Iio (Order.succ gamma.1) :=
          lastStageIndex gamma.1
        have hlocal :=
          (ih (Order.succ gamma.1) hsucc).coherent
            beta' gamma' hbetaGamma x y hx hy
        simpa only [historyStageGraphs, beta', gamma',
          lastStageIndex_val] using hlocal
      · intro beta gamma hbetaGamma x y hx hy hgraph
        have hsucc : Order.succ gamma.1 < limit :=
          hl.succ_lt (Set.mem_Iio.mp gamma.2)
        let beta' : Set.Iio (Order.succ gamma.1) :=
          ⟨beta.1, lt_of_le_of_lt hbetaGamma (Order.lt_succ gamma.1)⟩
        let gamma' : Set.Iio (Order.succ gamma.1) :=
          lastStageIndex gamma.1
        have hlocal :=
          (ih (Order.succ gamma.1) hsucc).initial
            beta' gamma' hbetaGamma x y hx hy
        apply hlocal
        simpa only [historyStageGraphs, gamma',
          lastStageIndex_val] using hgraph

/-- Every constructible stage has an internally represented well-order. -/
theorem allStagesInternallyWellOrdered_of_historyData :
    AllStagesInternallyWellOrdered.{u} := by
  intro ordinal
  refine ⟨(stageHistoryData ordinal).relation, ?_⟩
  have hsystem := historyStageGraphs_coherent (Order.succ ordinal)
  have hnext :
      InternallyWellOrders (stageHistoryData ordinal).relation
        (stageLCarrier ordinal) := by
    simpa only [historyStageGraphs_last, lastStageIndex_val] using
      hsystem.wellOrders (lastStageIndex ordinal)
  let stageEquiv :
      LStageCarrier ordinal ≃
        InternalCarrier (stageLCarrier ordinal) :=
    Godel.RudimentaryTerm.zfCarrierInternalEquiv
      (stageLCarrier ordinal)
  change IsWellOrder (LStageCarrier ordinal)
    (InvImage
      (graphRelOn (stageHistoryData ordinal).relation
        (stageLCarrier ordinal)) stageEquiv)
  letI : IsWellOrder
      (InternalCarrier (stageLCarrier ordinal))
      (graphRelOn (stageHistoryData ordinal).relation
        (stageLCarrier ordinal)) := hnext
  exact
    { wf := InvImage.wf stageEquiv
        (IsWellFounded.wf : WellFounded
          (graphRelOn (stageHistoryData ordinal).relation
            (stageLCarrier ordinal)))
      trichotomous :=
        (InvImage.trichotomous
          (r := graphRelOn (stageHistoryData ordinal).relation
            (stageLCarrier ordinal))
          stageEquiv.injective).trichotomous }

/-- The recursively constructed stage orders give Choice inside `L`. -/
theorem lCarrier_modelsChoice_of_historyData :
    FirstOrder.SetTheory.ModelsChoice LCarrier.{u} :=
  lCarrier_modelsChoice_of_allStagesInternallyWellOrdered
    allStagesInternallyWellOrdered_of_historyData



end

end Constructible.Model
end CUAdapterModule98



/-! # Bridge to the existing Prove2Me constructible universe -/


namespace ContinuumHypothesis.Constructible
open FirstOrder FirstOrder.Language
noncomputable section
open Classical
set_option Elab.async false





































 theorem carrier_choice_of_native
    (hAC : ChoiceOn _root_.Constructible.Model.LCarrier.{0} Subtype.val) :
    ChoiceOn Carrier Subtype.val := by
  intro a hnonempty hdisjoint
  let e := nativeCarrierEquiv
  have hn (x : _root_.Constructible.Model.LCarrier.{0}) (hx : x.val ∈ (e a).val) :
      ∃ y : _root_.Constructible.Model.LCarrier.{0}, y.val ∈ x.val := by
    obtain ⟨y, hy⟩ := hnonempty (e.symm x) hx
    exact ⟨e y, hy⟩
  have hd (x : _root_.Constructible.Model.LCarrier.{0}) (hx : x.val ∈ (e a).val)
      (y : _root_.Constructible.Model.LCarrier.{0}) (hy : y.val ∈ (e a).val)
      (hne : x ≠ y) (z : _root_.Constructible.Model.LCarrier.{0})
      (hz : z.val ∈ x.val) : z.val ∉ y.val := by
    exact hdisjoint (e.symm x) hx (e.symm y) hy
      (fun h => hne (e.symm.injective h)) (e.symm z) hz
  obtain ⟨c, hc⟩ := hAC (e a) hn hd
  refine ⟨e.symm c, fun x hx => ?_⟩
  obtain ⟨y, hy, hyc, hu⟩ := hc (e x) hx
  refine ⟨e.symm y, hy, hyc, fun z hz hzc => ?_⟩
  exact e.injective ((hu (e z) hz hzc).trans (e.apply_symm_apply y).symm)

 theorem realize_all {M : Type*} [setLang.Structure M]
    (v : ℕ → M) (i : ℕ) (φ : SFormula) :
    Formula.Realize (SFormula.all i φ) v ↔ ∀ z : M, Formula.Realize φ (Function.update v i z) := by
  rw [SFormula.all, Formula.realize_iAlls]
  simp only [Formula.realize_relabel]
  have heq (u : Unit → M) :
      (Sum.elim v u) ∘ (fun j => if j = i then Sum.inr () else Sum.inl j) =
        Function.update v i (u ()) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  simp only [heq]
  constructor
  · intro h z
    exact h (fun _ => z)
  · intro h u
    exact h (u ())

 theorem realize_ex {M : Type*} [setLang.Structure M]
    (v : ℕ → M) (i : ℕ) (φ : SFormula) :
    Formula.Realize (SFormula.ex i φ) v ↔ ∃ z : M, Formula.Realize φ (Function.update v i z) := by
  rw [SFormula.ex, Formula.realize_iExs]
  simp only [Formula.realize_relabel]
  have heq (u : Unit → M) :
      (Sum.elim v u) ∘ (fun j => if j = i then Sum.inr () else Sum.inl j) =
        Function.update v i (u ()) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  simp only [heq]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u (), hu⟩
  · rintro ⟨z, hz⟩
    exact ⟨fun _ => z, hz⟩

 theorem close_of_all (φ : SFormula) (h : ∀ v : ℕ → Carrier, Formula.Realize φ v) :
    Carrier ⊨ SFormula.close φ := by
  change Formula.Realize (SFormula.close φ) (default : Empty → Carrier)
  rw [SFormula.close, Formula.realize_iAlls]
  intro v
  exact Formula.realize_relabel.mpr (h _)

@[simp]  theorem realize_mem (v : ℕ → Carrier) (i j : ℕ) :
    Formula.Realize (SFormula.mem i j) v ↔ (v i).val ∈ (v j).val := by rfl

@[simp]  theorem realize_eq (v : ℕ → Carrier) (i j : ℕ) :
    Formula.Realize (SFormula.eq i j) v ↔ v i = v j := by rfl

 theorem choice_sentence_of_carrier_choice
    (hChoice : ChoiceOn Carrier Subtype.val) :
    Carrier ⊨ acSentence := by
  apply close_of_all
  intro v
  rw [SFormula.choice, realize_all]
  intro a
  rw [Formula.realize_imp, Formula.realize_inf]
  rintro ⟨hn, hd⟩
  have hn' : ∀ x : Carrier, x.val ∈ a.val → ∃ y : Carrier, y.val ∈ x.val := by
    simpa [-Subtype.forall, -Subtype.exists, realize_all, realize_ex, Function.update_apply] using hn
  have hd' : ∀ x y : Carrier, x.val ∈ a.val → y.val ∈ a.val → x ≠ y →
      ∀ z : Carrier, z.val ∈ x.val → z.val ∉ y.val := by
    simpa [-Subtype.forall, -Subtype.exists, realize_all, realize_ex, Function.update_apply, and_assoc] using hd
  obtain ⟨c, hc⟩ := hChoice a hn' (fun x hx y hy hne => hd' x y hx hy hne)
  rw [realize_ex]
  refine ⟨c, ?_⟩
  simpa [-Subtype.forall, -Subtype.exists, realize_all, realize_ex, Function.update_apply, and_assoc] using hc




end
end ContinuumHypothesis.Constructible

theorem solution : ContinuumHypothesis.Constructible.Carrier ⊨ ContinuumHypothesis.acSentence := by
  apply ContinuumHypothesis.Constructible.choice_sentence_of_carrier_choice
  apply ContinuumHypothesis.Constructible.carrier_choice_of_native
  exact _root_.Constructible.Model.lCarrier_modelsChoice_of_historyData

