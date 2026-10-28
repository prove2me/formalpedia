-- Prove2me | solution 1 for Constructible.ContinuumFormula.hartogsStageBound_lCarrier
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T00:09:49.365889+00:00
-- url     : https://prove2.me/submissions/c362ddd6-5970-4838-a552-620102d1e6b7

import Definitions.Def_CH_ConstructibleGCH_Library25
import Theorems.Thm_Constructible_ContinuumFormula_hartogsStageBound_of_pointwise_stage_injects
import Theorems.Thm_Constructible_ContinuumFormula_injects_infiniteCardinalSquare_lCarrier

/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 2000000

/- Source module: Solutions.Work_CUGCH_Hartogs -/
section GCHSource_Work_CUGCH_Hartogs
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# Internal injections and Hartogs numbers

This file formulates Hartogs' construction entirely inside a membership
structure.  Injections are represented by sets of Kuratowski pairs, so an
injection in `LCarrier` is required to have a graph which itself belongs to
`L`.  Ambient cardinal comparison is used only to show that the search for
an obstruction is nonempty; the least obstruction and its specification use
only internally represented injection graphs.
-/

section

universe u

open scoped Cardinal

namespace Constructible.ContinuumFormula

/-! ## Semantic relations -/























private theorem Injects.cardinalMk_le
    {A : Type u} {E : A → A → Prop} {domain codomain : A}
    (h : Injects E domain codomain) :
    #(RelationCarrier E domain) ≤ #(RelationCarrier E codomain) := by
  rcases h with ⟨graph, hgraph⟩
  exact Cardinal.mk_le_of_injective hgraph.toFun_injective





/-! ## The internal Hartogs number of a constructible set -/







private theorem ordinalLCarrier_isVonNeumannOrdinal (alpha : Ordinal.{u}) :
    IsVonNeumannOrdinal Constructible.Model.lCarrierMem
      (Constructible.Model.ordinalLCarrier alpha) :=
  (isVonNeumannOrdinal_lCarrier_iff _).mpr
    (ZFSet.isOrdinal_toZFSet alpha)

private theorem not_injects_externalHartogsBound
    (base : Constructible.Model.LCarrier.{u}) :
    ¬Injects Constructible.Model.lCarrierMem
      (Constructible.Model.ordinalLCarrier (externalHartogsBound base))
      base := by
  intro hinjects
  have hinternal := hinjects.cardinalMk_le
  change
    #(Constructible.Model.InternalCarrier
        (Constructible.Model.ordinalLCarrier (externalHartogsBound base))) ≤
      #(Constructible.Model.InternalCarrier base) at hinternal
  have hraw :
      #(ZFCarrier
          (Constructible.Model.ordinalLCarrier
            (externalHartogsBound base)).1) ≤
        #(ZFCarrier base.1) := by
    calc
      #(ZFCarrier
          (Constructible.Model.ordinalLCarrier
            (externalHartogsBound base)).1) =
          #(Constructible.Model.InternalCarrier
            (Constructible.Model.ordinalLCarrier
              (externalHartogsBound base))) :=
        Cardinal.mk_congr
          (Constructible.Godel.RudimentaryTerm.zfCarrierInternalEquiv
            (Constructible.Model.ordinalLCarrier
              (externalHartogsBound base)))
      _ ≤ #(Constructible.Model.InternalCarrier base) := hinternal
      _ = #(ZFCarrier base.1) :=
        Cardinal.mk_congr
          (Constructible.Godel.RudimentaryTerm.zfCarrierInternalEquiv base).symm
  have hlift :
      Cardinal.lift
          ((externalHartogsBound base).toZFSet.card) ≤
        Cardinal.lift (base.1.card) := by
    simpa only [Constructible.Model.ordinalLCarrier_val,
      ZFSet.cardinalMk_coe_sort] using hraw
  have hcard :
      (externalHartogsBound base).card ≤ base.1.card := by
    rw [Ordinal.card_toZFSet] at hlift
    exact Cardinal.lift_le.mp hlift
  rw [externalHartogsBound, Cardinal.card_ord] at hcard
  exact (Order.lt_succ base.1.card).2 hcard



private theorem internalHartogsObstructions_nonempty
    (base : Constructible.Model.LCarrier.{u}) :
    (internalHartogsObstructions base).Nonempty := by
  exact ⟨externalHartogsBound base,
    not_injects_externalHartogsBound base⟩





private theorem internalHartogsOrdinal_is_obstruction
    (base : Constructible.Model.LCarrier.{u}) :
    internalHartogsOrdinal base ∈ internalHartogsObstructions base := by
  exact csInf_mem (internalHartogsObstructions_nonempty base)

/-- The least obstruction has exactly the internal Hartogs property. -/
private theorem internalHartogsLCarrier_isHartogsNumber
    (base : Constructible.Model.LCarrier.{u}) :
    IsHartogsNumber Constructible.Model.lCarrierMem base
      (internalHartogsLCarrier base) := by
  refine ⟨ordinalLCarrier_isVonNeumannOrdinal _, ?_, ?_⟩
  · exact internalHartogsOrdinal_is_obstruction base
  · intro alpha halpha
    obtain ⟨beta, hbeta, hvalue⟩ :=
      Ordinal.mem_toZFSet_iff.mp halpha
    have halphaEq :
        alpha = Constructible.Model.ordinalLCarrier beta := by
      apply Subtype.ext
      exact hvalue.symm
    rw [halphaEq]
    by_contra hnotInjects
    have hle : internalHartogsOrdinal base ≤ beta :=
      csInf_le' hnotInjects
    exact (not_le_of_gt hbeta) hle



/-! ## Object-language formulas -/

















end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_Hartogs

/- Source module: Solutions.Work_CUGCH_InternalInjections -/
section GCHSource_Work_CUGCH_InternalInjections
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Internally represented injections in the constructible universe

This file develops the elementary algebra of injection graphs whose graph is
itself an element of `L`.  In particular, inverse and composite graphs are
obtained by Separation from fixed first-order definitions.  No ambient
function is used as a witness for an internal injection.
-/

section

universe u

namespace Constructible.ContinuumFormula

/-! ## Absoluteness of Kuratowski graph semantics -/







/-! ## Definable identity, converse, and composition graphs -/

























private theorem exists_identityGraph_lCarrier
    (domain : Constructible.Model.LCarrier.{u}) :
    ∃ graph : Constructible.Model.LCarrier.{u},
      IsGraphBetween Constructible.Model.lCarrierMem graph domain domain ∧
        ∀ x y : Constructible.Model.LCarrier.{u},
          GraphValue Constructible.Model.lCarrierMem graph x y ↔
            x.1 ∈ domain.1 ∧ y = x := by
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      identityGraphPredicate
      (fun i : Fin 0 => Fin.elim0 i) domain with
    ⟨graph, hsupport, hrelation⟩
  have hvalue : ∀ x y : Constructible.Model.LCarrier.{u},
      GraphValue Constructible.Model.lCarrierMem graph x y ↔
        x.1 ∈ domain.1 ∧ y = x := by
    intro x y
    rw [graphValue_lCarrier_iff_graphRel, hrelation]
    constructor
    · rintro ⟨hx, _hy, hxy⟩
      exact ⟨hx, (satisfies_identityGraphPredicate x y).mp hxy |>.symm⟩
    · rintro ⟨hx, hxy⟩
      subst y
      exact ⟨hx, hx, (satisfies_identityGraphPredicate x x).mpr rfl⟩
  refine ⟨graph, ?_, hvalue⟩
  intro pair hpair
  rcases hsupport pair hpair with
    ⟨x, y, hx, hy, hpairEq, hxy⟩
  refine ⟨x, hx, y, hy, ?_⟩
  exact (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq

private theorem injects_refl_lCarrier
    (domain : Constructible.Model.LCarrier.{u}) :
    Injects Constructible.Model.lCarrierMem domain domain := by
  rcases exists_identityGraph_lCarrier domain with
    ⟨graph, hbetween, hvalue⟩
  refine ⟨graph, hbetween, ?_, ?_⟩
  · intro x hx
    refine ⟨x, hx, (hvalue x x).mpr ⟨hx, rfl⟩, ?_⟩
    intro z _hz hzValue
    exact (hvalue x z).mp hzValue |>.2
  · intro y _hy x hx hxy z hz hzy
    have hyx : y = x := (hvalue x y).mp hxy |>.2
    have hyz : y = z := (hvalue z y).mp hzy |>.2
    exact hyz.symm.trans hyx

private theorem injects_of_subset_lCarrier
    {domain codomain : Constructible.Model.LCarrier.{u}}
    (hsubset : ∀ x : Constructible.Model.LCarrier.{u},
      x.1 ∈ domain.1 → x.1 ∈ codomain.1) :
    Injects Constructible.Model.lCarrierMem domain codomain := by
  rcases exists_identityGraph_lCarrier domain with
    ⟨graph, hbetween, hvalue⟩
  refine ⟨graph, ?_, ?_, ?_⟩
  · intro pair hpair
    rcases hbetween pair hpair with ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hsubset y hy, hxy⟩
  · intro x hx
    refine ⟨x, hsubset x hx, (hvalue x x).mpr ⟨hx, rfl⟩, ?_⟩
    intro z _hz hzValue
    exact (hvalue x z).mp hzValue |>.2
  · intro y _hy x hx hxy z hz hzy
    have hyx : y = x := (hvalue x y).mp hxy |>.2
    have hyz : y = z := (hvalue z y).mp hzy |>.2
    exact hyz.symm.trans hyx

private theorem exists_compositionGraph_lCarrier
    {first second domain middle codomain :
      Constructible.Model.LCarrier.{u}}
    (hfirst : IsGraphBetween Constructible.Model.lCarrierMem
      first domain middle)
    (hsecond : IsGraphBetween Constructible.Model.lCarrierMem
      second middle codomain) :
    ∃ graph : Constructible.Model.LCarrier.{u},
      IsGraphBetween Constructible.Model.lCarrierMem
        graph domain codomain ∧
      ∀ x y : Constructible.Model.LCarrier.{u},
        GraphValue Constructible.Model.lCarrierMem graph x y ↔
          ∃ z : Constructible.Model.LCarrier.{u},
            GraphValue Constructible.Model.lCarrierMem first x z ∧
              GraphValue Constructible.Model.lCarrierMem second z y := by
  let container := unionLCarrier domain codomain
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      compositionGraphPredicate ![first, second] container with
    ⟨graph, hsupport, hrelation⟩
  have hvalue : ∀ x y : Constructible.Model.LCarrier.{u},
      GraphValue Constructible.Model.lCarrierMem graph x y ↔
        ∃ z : Constructible.Model.LCarrier.{u},
          GraphValue Constructible.Model.lCarrierMem first x z ∧
            GraphValue Constructible.Model.lCarrierMem second z y := by
    intro x y
    rw [graphValue_lCarrier_iff_graphRel, hrelation]
    constructor
    · rintro ⟨_hx, _hy, hformula⟩
      exact (satisfies_compositionGraphPredicate first second x y).mp
        hformula
    · rintro ⟨z, hxz, hzy⟩
      have hx := (hfirst.graphValue_mem_lCarrier hxz).1
      have hy := (hsecond.graphValue_mem_lCarrier hzy).2
      refine ⟨?_, ?_, ?_⟩
      · exact (mem_unionLCarrier_iff domain codomain x).mpr (Or.inl hx)
      · exact (mem_unionLCarrier_iff domain codomain y).mpr (Or.inr hy)
      · exact (satisfies_compositionGraphPredicate first second x y).mpr
          ⟨z, hxz, hzy⟩
  refine ⟨graph, ?_, hvalue⟩
  intro pair hpair
  rcases hsupport pair hpair with
    ⟨x, y, _hxContainer, _hyContainer, hpairEq, hformula⟩
  rcases (satisfies_compositionGraphPredicate first second x y).mp
      hformula with ⟨z, hxz, hzy⟩
  have hx := (hfirst.graphValue_mem_lCarrier hxz).1
  have hy := (hsecond.graphValue_mem_lCarrier hzy).2
  exact ⟨x, hx, y, hy,
    (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq⟩

private theorem Injects.trans_lCarrier
    {domain middle codomain : Constructible.Model.LCarrier.{u}}
    (hfirst : Injects Constructible.Model.lCarrierMem domain middle)
    (hsecond : Injects Constructible.Model.lCarrierMem middle codomain) :
    Injects Constructible.Model.lCarrierMem domain codomain := by
  rcases hfirst with ⟨first, hfirst⟩
  rcases hsecond with ⟨second, hsecond⟩
  rcases exists_compositionGraph_lCarrier hfirst.1 hsecond.1 with
    ⟨graph, hbetween, hvalue⟩
  refine ⟨graph, hbetween, ?_, ?_⟩
  · intro x hx
    rcases hfirst.2.1 x hx with ⟨y, hy, hxy, hyUnique⟩
    rcases hsecond.2.1 y hy with ⟨z, hz, hyz, hzUnique⟩
    refine ⟨z, hz, (hvalue x z).mpr ⟨y, hxy, hyz⟩, ?_⟩
    intro z' hz' hxz'
    rcases (hvalue x z').mp hxz' with ⟨y', hxy', hy'z'⟩
    have hy' := (hfirst.1.graphValue_mem_lCarrier hxy').2
    have hyEq : y' = y := hyUnique y' hy' hxy'
    subst y'
    exact hzUnique z' hz' hy'z'
  · intro z hz x hx hxz x' hx' hx'z
    rcases (hvalue x z).mp hxz with ⟨y, hxy, hyz⟩
    rcases (hvalue x' z).mp hx'z with ⟨y', hx'y', hy'z⟩
    have hy := (hfirst.1.graphValue_mem_lCarrier hxy).2
    have hy' := (hfirst.1.graphValue_mem_lCarrier hx'y').2
    have hyEq : y' = y :=
      hsecond.2.2 z hz y hy hyz y' hy' hy'z
    subst y'
    exact hfirst.2.2 y hy x hx hxy x' hx' hx'y'





/-! ## Hartogs numbers are internal cardinals -/



end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalInjections

/- Source module: Solutions.Work_CUGCH_InternalCardinalUnion -/
section GCHSource_Work_CUGCH_InternalCardinalUnion
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Internally represented injections for indexed unions

This file isolates the graph-theoretic core of the cardinal union argument.
All functions in the statement are represented by actual constructible sets.
In particular, the family of fiber injections is an input graph rather than
an ambient choice function.
-/

section

universe u

namespace Constructible.ContinuumFormula



private theorem IsInjection.toIsFunctionGraph
    {A : Type u} {E : A -> A -> Prop}
    {graph domain codomain : A}
    (h : IsInjection E graph domain codomain) :
    IsFunctionGraph E graph domain codomain :=
  ⟨h.1, h.2.1⟩

private theorem IsFunctionGraph.graphValue_unique
    {A : Type u} {E : A -> A -> Prop}
    {graph domain codomain x y z : A}
    (h : IsFunctionGraph E graph domain codomain)
    (hx : E x domain) (hy : E y codomain) (hz : E z codomain)
    (hxy : GraphValue E graph x y) (hxz : GraphValue E graph x z) :
    y = z := by
  rcases h.2 x hx with ⟨value, hvalue, hxvalue, hunique⟩
  exact (hunique y hy hxy).trans (hunique z hz hxz).symm













/-! ## Conditional internal family interfaces -/





private theorem CardinalUnionRel.mem_sUnion_prod_lCarrier
    {selector indexedFamily injectionFamily index family graphFamily kappa
      x output : Constructible.Model.LCarrier.{u}}
    (hselector : IsFunctionGraph Constructible.Model.lCarrierMem
      selector (Constructible.Model.sUnionLCarrier family) index)
    (hfamilies : IsFiberInjectionFamily Constructible.Model.lCarrierMem
      indexedFamily injectionFamily index family graphFamily kappa)
    (hrel : CardinalUnionRel Constructible.Model.lCarrierMem
      selector indexedFamily injectionFamily x output) :
    x.1 ∈ (Constructible.Model.sUnionLCarrier family).1 /\
      output.1 ∈ (Constructible.Model.prodLCarrier index kappa).1 := by
  rcases hrel with
    ⟨i, fiber, injection, value, hselect, hfiber, hinjection,
      hvalue, houtput⟩
  have hxUnion := (hselector.1.graphValue_mem_lCarrier hselect).1
  have hiIndex := (hselector.1.graphValue_mem_lCarrier hselect).2
  have hinjects := hfamilies.2.2 i fiber injection
    hiIndex hfiber hinjection
  have hvalueKappa :=
    (hinjects.1.graphValue_mem_lCarrier hvalue).2
  have houtputRaw :=
    (isKuratowskiPairOf_lCarrier_iff output i value).mp houtput
  refine ⟨hxUnion, ?_⟩
  change output.1 ∈ ZFSet.prod index.1 kappa.1
  rw [houtputRaw, ZFSet.pair_mem_prod]
  exact ⟨hiIndex, hvalueKappa⟩

/-- The combined relation has a constructible graph supported on the union
and the internal Cartesian product. -/
private theorem exists_cardinalUnionGraph_lCarrier
    {selector indexedFamily injectionFamily index family graphFamily kappa :
      Constructible.Model.LCarrier.{u}}
    (hselector : IsFunctionGraph Constructible.Model.lCarrierMem
      selector (Constructible.Model.sUnionLCarrier family) index)
    (hfamilies : IsFiberInjectionFamily Constructible.Model.lCarrierMem
      indexedFamily injectionFamily index family graphFamily kappa) :
    exists graph : Constructible.Model.LCarrier.{u},
      IsGraphBetween Constructible.Model.lCarrierMem graph
        (Constructible.Model.sUnionLCarrier family)
        (Constructible.Model.prodLCarrier index kappa) /\
        forall x output : Constructible.Model.LCarrier.{u},
          GraphValue Constructible.Model.lCarrierMem graph x output <->
            CardinalUnionRel Constructible.Model.lCarrierMem
              selector indexedFamily injectionFamily x output := by
  let domain := Constructible.Model.sUnionLCarrier family
  let codomain := Constructible.Model.prodLCarrier index kappa
  let container := unionLCarrier domain codomain
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      cardinalUnionPredicate ![selector, indexedFamily, injectionFamily]
      container with
    ⟨graph, hsupport, hgraph⟩
  have hvalue : forall x output : Constructible.Model.LCarrier.{u},
      GraphValue Constructible.Model.lCarrierMem graph x output <->
        CardinalUnionRel Constructible.Model.lCarrierMem
          selector indexedFamily injectionFamily x output := by
    intro x output
    rw [graphValue_lCarrier_iff_graphRel, hgraph]
    constructor
    · rintro ⟨_hxContainer, _houtputContainer, hformula⟩
      exact (satisfies_cardinalUnionRelation
        selector indexedFamily injectionFamily x output).mp hformula
    · intro hrel
      have hmem := CardinalUnionRel.mem_sUnion_prod_lCarrier
        hselector hfamilies hrel
      refine ⟨?_, ?_, ?_⟩
      · exact (mem_unionLCarrier_iff domain codomain x).mpr
          (Or.inl hmem.1)
      · exact (mem_unionLCarrier_iff domain codomain output).mpr
          (Or.inr hmem.2)
      · exact (satisfies_cardinalUnionRelation
          selector indexedFamily injectionFamily x output).mpr hrel
  refine ⟨graph, ?_, hvalue⟩
  intro pair hpair
  rcases hsupport pair hpair with
    ⟨x, output, _hxContainer, _houtputContainer, hpairEq, hformula⟩
  have hrel := (satisfies_cardinalUnionRelation
    selector indexedFamily injectionFamily x output).mp hformula
  have hmem := CardinalUnionRel.mem_sUnion_prod_lCarrier
    hselector hfamilies hrel
  exact ⟨x, hmem.1, output, hmem.2,
    (isKuratowskiPairOf_lCarrier_iff pair x output).mpr hpairEq⟩

/-- An internally selected family of internal fiber injections combines to
an internal injection from the union into `index x kappa`. -/
private theorem injects_sUnion_to_prod_lCarrier
    {selector indexedFamily injectionFamily index family graphFamily kappa :
      Constructible.Model.LCarrier.{u}}
    (hselector : SelectsContainingFiber Constructible.Model.lCarrierMem
      selector (Constructible.Model.sUnionLCarrier family) index indexedFamily)
    (hfamilies : IsFiberInjectionFamily Constructible.Model.lCarrierMem
      indexedFamily injectionFamily index family graphFamily kappa) :
    Injects Constructible.Model.lCarrierMem
      (Constructible.Model.sUnionLCarrier family)
      (Constructible.Model.prodLCarrier index kappa) := by
  rcases exists_cardinalUnionGraph_lCarrier hselector.1 hfamilies with
    ⟨combined, hbetween, hvalue⟩
  refine ⟨combined, hbetween, ?_, ?_⟩
  · intro x hxUnion
    rcases hselector.1.2 x hxUnion with
      ⟨i, hiIndex, hselect, _hiUnique⟩
    rcases hfamilies.1.2 i hiIndex with
      ⟨fiber, hfiberFamily, hindexed, _hfiberUnique⟩
    rcases hfamilies.2.1.2 i hiIndex with
      ⟨injection, hinjectionGraphFamily, hinjectionAt,
        _hinjectionUnique⟩
    rcases hselector.2 x i hxUnion hselect with
      ⟨selectedFiber, hselectedFiber, hxSelectedFiber⟩
    have hselectedFiberFamily :=
      (hfamilies.1.1.graphValue_mem_lCarrier hselectedFiber).2
    have hselectedEq : selectedFiber = fiber :=
      hfamilies.1.graphValue_unique hiIndex
        hselectedFiberFamily hfiberFamily hselectedFiber hindexed
    subst selectedFiber
    have hinjects := hfamilies.2.2 i fiber injection
      hiIndex hindexed hinjectionAt
    rcases hinjects.2.1 x hxSelectedFiber with
      ⟨value, hvalueKappa, hxvalue, _hvalueUnique⟩
    let output := Constructible.Model.orderedPairLCarrier i value
    have houtputProduct :
        output.1 ∈ (Constructible.Model.prodLCarrier index kappa).1 := by
      change ZFSet.pair i.1 value.1 ∈ ZFSet.prod index.1 kappa.1
      rw [ZFSet.pair_mem_prod]
      exact ⟨hiIndex, hvalueKappa⟩
    have houtputPair :
        IsKuratowskiPairOf Constructible.Model.lCarrierMem output i value :=
      (isKuratowskiPairOf_lCarrier_iff output i value).mpr rfl
    refine ⟨output, houtputProduct,
      (hvalue x output).mpr
        ⟨i, fiber, injection, value, hselect, hindexed,
          hinjectionAt, hxvalue, houtputPair⟩, ?_⟩
    intro other hotherProduct hxother
    rcases (hvalue x other).mp hxother with
      ⟨i', fiber', injection', value', hselect', hindexed',
        hinjectionAt', hxvalue', hotherPair⟩
    have hi'Index :=
      (hselector.1.1.graphValue_mem_lCarrier hselect').2
    have hiEq : i' = i :=
      hselector.1.graphValue_unique hxUnion
        hi'Index hiIndex hselect' hselect
    subst i'
    have hfiber'Family :=
      (hfamilies.1.1.graphValue_mem_lCarrier hindexed').2
    have hfiberEq : fiber' = fiber :=
      hfamilies.1.graphValue_unique hiIndex
        hfiber'Family hfiberFamily hindexed' hindexed
    subst fiber'
    have hinjection'GraphFamily :=
      (hfamilies.2.1.1.graphValue_mem_lCarrier hinjectionAt').2
    have hinjectionEq : injection' = injection :=
      hfamilies.2.1.graphValue_unique hiIndex
        hinjection'GraphFamily hinjectionGraphFamily
        hinjectionAt' hinjectionAt
    subst injection'
    have hvalue'Kappa :=
      (hinjects.1.graphValue_mem_lCarrier hxvalue').2
    have hvalueEq : value' = value :=
      hinjects.toIsFunctionGraph.graphValue_unique hxSelectedFiber
        hvalue'Kappa hvalueKappa hxvalue' hxvalue
    subst value'
    apply Subtype.ext
    simpa only [output, Constructible.Model.orderedPairLCarrier_val] using
      (isKuratowskiPairOf_lCarrier_iff other i value).mp hotherPair
  · intro output houtputProduct x hxUnion hxoutput z hzUnion hzoutput
    rcases (hvalue x output).mp hxoutput with
      ⟨i, fiber, injection, value, hselectX, hindexedI,
        hinjectionI, hxvalue, houtputI⟩
    rcases (hvalue z output).mp hzoutput with
      ⟨j, fiber', injection', value', hselectZ, hindexedJ,
        hinjectionJ, hzvalue, houtputJ⟩
    have hpairI :=
      (isKuratowskiPairOf_lCarrier_iff output i value).mp houtputI
    have hpairJ :=
      (isKuratowskiPairOf_lCarrier_iff output j value').mp houtputJ
    have hcoordinates := ZFSet.pair_inj.mp (hpairI.symm.trans hpairJ)
    have hij : i = j := Subtype.ext hcoordinates.1
    have hvalues : value = value' := Subtype.ext hcoordinates.2
    subst j
    subst value'
    have hiIndex :=
      (hselector.1.1.graphValue_mem_lCarrier hselectX).2
    have hfiberFamily :=
      (hfamilies.1.1.graphValue_mem_lCarrier hindexedI).2
    have hfiber'Family :=
      (hfamilies.1.1.graphValue_mem_lCarrier hindexedJ).2
    have hfiberEq : fiber' = fiber :=
      hfamilies.1.graphValue_unique hiIndex
        hfiber'Family hfiberFamily hindexedJ hindexedI
    subst fiber'
    have hinjectionGraphFamily :=
      (hfamilies.2.1.1.graphValue_mem_lCarrier hinjectionI).2
    have hinjection'GraphFamily :=
      (hfamilies.2.1.1.graphValue_mem_lCarrier hinjectionJ).2
    have hinjectionEq : injection' = injection :=
      hfamilies.2.1.graphValue_unique hiIndex
        hinjection'GraphFamily hinjectionGraphFamily
        hinjectionJ hinjectionI
    subst injection'
    have hinjects := hfamilies.2.2 i fiber injection
      hiIndex hindexedI hinjectionI
    have hxFiber := (hinjects.1.graphValue_mem_lCarrier hxvalue).1
    have hzFiber := (hinjects.1.graphValue_mem_lCarrier hzvalue).1
    have hvalueKappa :=
      (hinjects.1.graphValue_mem_lCarrier hxvalue).2
    exact hinjects.2.2 value hvalueKappa
      x hxFiber hxvalue z hzFiber hzvalue

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalCardinalUnion

/- Source module: Solutions.Work_CUGCH_InternalStageCardinalUnion -/
section GCHSource_Work_CUGCH_InternalStageCardinalUnion
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The internally represented family of constructible stages

This file supplies the stage-family part of the standard cardinal estimate at
a limit level.  Replacement constructs the actual set of earlier stages, and
Separation constructs the actual graph sending an ordinal index to its stage.
Consequently the generic indexed-union theorem can be applied without taking
an externally indexed family as an internal graph.

The remaining inputs to the limit-cardinal argument are stated explicitly:
an internal selector choosing a containing stage, an internal family of
injection graphs for the fibers, and (when the final target is an ordinal
cardinal) the appropriate internal product absorption.  No ambient cardinal
comparison is converted into any of these graph witnesses.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## A stage-valued functional relation -/











/-! ## Replacement of the earlier stages -/







/-- At a nonzero limit, the union of the internally represented earlier-stage
family is exactly the limit stage itself. -/
private theorem sUnion_stageValueFamily_eq_stageLCarrier
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit) :
    Constructible.Model.sUnionLCarrier (stageValueFamily limit) =
      stageLCarrier limit := by
  apply Constructible.Model.lCarrier_extensionality
  intro z
  rw [Constructible.Model.mem_sUnionLCarrier_iff]
  constructor
  · rintro ⟨stage, hstageFamily, hzStage⟩
    rcases (mem_stageValueFamily_iff limit stage).mp hstageFamily with
      ⟨ordinal, hordinal, rfl⟩
    change z.1 ∈ LStageZF limit
    exact (mem_LStageZF_limit_iff hl).mpr
      ⟨ordinal, hordinal, hzStage⟩
  · intro hzLimit
    change z.1 ∈ LStageZF limit at hzLimit
    rcases (mem_LStageZF_limit_iff hl).mp hzLimit with
      ⟨ordinal, hordinal, hzStage⟩
    refine ⟨stageLCarrier ordinal, ?_, hzStage⟩
    exact (mem_stageValueFamily_iff limit
      (stageLCarrier ordinal)).mpr ⟨ordinal, hordinal, rfl⟩

/-! ## The internally represented index-to-stage graph -/

















/-- The stage graph is a total internally represented function from the
ordinal index to the Replacement-generated family of earlier stages. -/
private theorem stageValueGraph_isFunctionGraph (bound : Ordinal.{u}) :
    IsFunctionGraph LMem (stageValueGraph bound)
      (ordinalLCarrier bound) (stageValueFamily bound) := by
  constructor
  · intro pair hpair
    have hmem :=
      (Constructible.Model.mem_canonicalDefinableRelationGraph_iff
        boundedStageValueAtFormula
        (snoc Constructible.Model.stageHistoryFixedParameters
          (ordinalLCarrier bound))
        (stageValueGraphSupport bound) pair).mp hpair
    rcases hmem with
      ⟨index, stage, _hindexSupport, _hstageSupport,
        hpairEq, hformula⟩
    have hbounded :=
      (satisfies_boundedStageValueAtFormula
        (ordinalLCarrier bound) index stage).mp hformula
    rcases Constructible.Model.exists_eq_ordinalLCarrier_of_mem
        hbounded.1 with ⟨ordinal, hordinal, rfl⟩
    have hstageEq : stage = stageLCarrier ordinal :=
      (stageValueAt_ordinal_iff ordinal stage).mp hbounded.2
    have hstageFamily : stage.1 ∈ (stageValueFamily bound).1 := by
      rw [hstageEq]
      exact (mem_stageValueFamily_iff bound
        (stageLCarrier ordinal)).mpr ⟨ordinal, hordinal, rfl⟩
    refine ⟨ordinalLCarrier ordinal,
      (ordinalLCarrier_mem_ordinalLCarrier_iff bound ordinal).mpr hordinal,
      stage, hstageFamily, ?_⟩
    exact (isKuratowskiPairOf_lCarrier_iff
      pair (ordinalLCarrier ordinal) stage).mpr hpairEq
  · intro index hindex
    rcases Constructible.Model.exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    refine ⟨stageLCarrier ordinal, ?_, ?_, ?_⟩
    · exact (mem_stageValueFamily_iff bound
        (stageLCarrier ordinal)).mpr ⟨ordinal, hordinal, rfl⟩
    · apply (graphValue_stageValueGraph_iff bound
        (ordinalLCarrier ordinal) (stageLCarrier ordinal)).mpr
      exact ⟨(ordinalLCarrier_mem_ordinalLCarrier_iff
          bound ordinal).mpr hordinal,
        (stageValueAt_ordinal_iff ordinal
          (stageLCarrier ordinal)).mpr rfl⟩
    · intro other _hotherFamily hother
      exact (stageValueAt_ordinal_iff ordinal other).mp
        ((graphValue_stageValueGraph_iff bound
          (ordinalLCarrier ordinal) other).mp hother).2

/-! ## The standard limit-cardinal step -/

/-- The exact internal limit step.  The indexed family of stages and its
functionality are now canonical.  The hypotheses retain only the genuinely
separate graph obligations: selecting a containing fiber and internally
collecting the fiber injections. -/
private theorem injects_limitStage_to_prod_of_internalFamilies
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit)
    {kappa selector injectionFamily graphFamily : LCarrier.{u}}
    (hselector : SelectsContainingFiber LMem selector
      (stageLCarrier limit) (ordinalLCarrier limit)
      (stageValueGraph limit))
    (hinjectionFamily : IsFunctionGraph LMem injectionFamily
      (ordinalLCarrier limit) graphFamily)
    (hinjections : forall ordinal : Ordinal.{u}, ordinal < limit ->
      forall injection : LCarrier.{u},
        GraphValue LMem injectionFamily
          (ordinalLCarrier ordinal) injection ->
        IsInjection LMem injection (stageLCarrier ordinal) kappa) :
    Injects LMem (stageLCarrier limit)
      (Constructible.Model.prodLCarrier
        (ordinalLCarrier limit) kappa) := by
  have hfibers : IsFiberInjectionFamily LMem
      (stageValueGraph limit) injectionFamily
      (ordinalLCarrier limit) (stageValueFamily limit)
      graphFamily kappa := by
    refine ⟨stageValueGraph_isFunctionGraph limit,
      hinjectionFamily, ?_⟩
    intro index fiber injection hindex hfiber hinjection
    rcases Constructible.Model.exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    have hfiberEq : fiber = stageLCarrier ordinal :=
      (stageValueAt_ordinal_iff ordinal fiber).mp
        ((graphValue_stageValueGraph_iff limit
          (ordinalLCarrier ordinal) fiber).mp hfiber).2
    subst fiber
    exact hinjections ordinal hordinal injection hinjection
  have hselectorUnion : SelectsContainingFiber LMem selector
      (Constructible.Model.sUnionLCarrier (stageValueFamily limit))
      (ordinalLCarrier limit) (stageValueGraph limit) := by
    simpa only [sUnion_stageValueFamily_eq_stageLCarrier hl] using hselector
  have hinjects := injects_sUnion_to_prod_lCarrier
    hselectorUnion hfibers
  simpa only [sUnion_stageValueFamily_eq_stageLCarrier hl] using hinjects



end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalStageCardinalUnion

/- Source module: Solutions.Work_CUGCH_CanonicalLimitStageSelector -/
section GCHSource_Work_CUGCH_CanonicalLimitStageSelector
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The canonical containing-stage selector at a limit

For an element of a nonzero limit stage, this file selects the least earlier
stage containing it.  The selector is an actual constructible graph obtained
by Separation from a fixed first-order formula.  The external `firstStage`
operation appears only in the proof that this graph is total and single
valued; it is not used as an internal graph witness.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## A stage contains an element -/









/-- At a canonical ordinal index, containment is ordinary membership in the
corresponding constructible stage. -/
private theorem stageContains_ordinal_iff
    (x : LCarrier.{u}) (ordinal : Ordinal.{u}) :
    StageContains x (ordinalLCarrier ordinal) ↔
      x.1 ∈ LStageZF ordinal := by
  constructor
  · rintro ⟨stage, hstage, hx⟩
    rw [(stageValueAt_ordinal_iff ordinal stage).mp hstage] at hx
    exact hx
  · intro hx
    exact ⟨stageLCarrier ordinal,
      (stageValueAt_ordinal_iff ordinal
        (stageLCarrier ordinal)).mpr rfl, hx⟩

/-! ## Least containing indices -/













/-! ## The Separation-generated selector graph -/





/-- An element of a nonzero limit stage has first occurrence strictly below
that limit. -/
private theorem firstStage_lt_of_mem_limitStage
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit)
    (x : LCarrier.{u}) (hx : x.1 ∈ (stageLCarrier limit).1) :
    firstStage x.1 x.2 < limit := by
  change x.1 ∈ LStageZF limit at hx
  rcases (mem_LStageZF_limit_iff hl).mp hx with
    ⟨ordinal, hordinal, hxOrdinal⟩
  exact (firstStage_le x.2 hxOrdinal).trans_lt hordinal

/-- The least-containing-stage graph is a total internally represented
function from the limit stage to its ordinal index set. -/
private theorem leastContainingStageGraph_isFunctionGraph
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit) :
    IsFunctionGraph LMem (leastContainingStageGraph limit)
      (stageLCarrier limit) (ordinalLCarrier limit) := by
  constructor
  · intro pair hpair
    have hmem :=
      (Constructible.Model.mem_canonicalDefinableRelationGraph_iff
        leastContainingStageFormula
        (snoc Constructible.Model.stageHistoryFixedParameters
          (ordinalLCarrier limit))
        (stageLCarrier limit) pair).mp hpair
    rcases hmem with
      ⟨x, index, hx, _hindexStage, hpairEq, hformula⟩
    have hleast :=
      (satisfies_leastContainingStageFormula
        (ordinalLCarrier limit) x index).mp hformula
    exact ⟨x, hx, index, hleast.1,
      (isKuratowskiPairOf_lCarrier_iff pair x index).mpr hpairEq⟩
  · intro x hx
    let alpha := firstStage x.1 x.2
    have halphaLimit : alpha < limit :=
      firstStage_lt_of_mem_limitStage hl x hx
    have hcontains : StageContains x (ordinalLCarrier alpha) :=
      (stageContains_ordinal_iff x alpha).mpr
        (mem_LStageZF_firstStage x.1 x.2)
    have hminimal : forall earlier : LCarrier.{u},
        earlier.1 ∈ (ordinalLCarrier alpha).1 ->
          Not (StageContains x earlier) := by
      intro earlier hearlier
      rcases Constructible.Model.exists_eq_ordinalLCarrier_of_mem
          hearlier with ⟨delta, hdelta, rfl⟩
      rw [stageContains_ordinal_iff]
      exact not_mem_LStageZF_of_lt_firstStage x.2 hdelta
    have hleast : IsLeastContainingStage
        (ordinalLCarrier limit) x (ordinalLCarrier alpha) :=
      ⟨(ordinalLCarrier_mem_ordinalLCarrier_iff
          limit alpha).mpr halphaLimit,
        hcontains, hminimal⟩
    refine ⟨ordinalLCarrier alpha, hleast.1,
      (graphValue_leastContainingStageGraph_iff
        limit x (ordinalLCarrier alpha)).mpr ⟨hx, hleast⟩, ?_⟩
    intro other _hotherBound hotherGraph
    have hotherLeast :=
      (graphValue_leastContainingStageGraph_iff
        limit x other).mp hotherGraph |>.2
    rcases Constructible.Model.exists_eq_ordinalLCarrier_of_mem
        hotherLeast.1 with ⟨gamma, _hgammaLimit, rfl⟩
    have hxGamma : x.1 ∈ LStageZF gamma :=
      (stageContains_ordinal_iff x gamma).mp hotherLeast.2.1
    have halphaGamma : alpha <= gamma :=
      firstStage_le x.2 hxGamma
    have hgammaAlpha : gamma <= alpha := by
      by_contra hnot
      have halphaLtGamma : alpha < gamma := lt_of_not_ge hnot
      have halphaMem :
          (ordinalLCarrier alpha).1 ∈ (ordinalLCarrier gamma).1 :=
        (ordinalLCarrier_mem_ordinalLCarrier_iff gamma alpha).mpr
          halphaLtGamma
      exact (hotherLeast.2.2 (ordinalLCarrier alpha) halphaMem)
        hcontains
    exact congrArg ordinalLCarrier
      (le_antisymm hgammaAlpha halphaGamma)

/-- The canonical graph has exactly the selector contract consumed by the
internal cardinal-union theorem. -/
private theorem leastContainingStageGraph_selectsContainingFiber
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit) :
    SelectsContainingFiber LMem
      (leastContainingStageGraph limit)
      (stageLCarrier limit) (ordinalLCarrier limit)
      (stageValueGraph limit) := by
  constructor
  · exact leastContainingStageGraph_isFunctionGraph hl
  · intro x index hx hselect
    have hleast :=
      (graphValue_leastContainingStageGraph_iff
        limit x index).mp hselect |>.2
    rcases hleast.2.1 with ⟨stage, hstageValue, hxStage⟩
    exact ⟨stage,
      (graphValue_stageValueGraph_iff limit index stage).mpr
        ⟨hleast.1, hstageValue⟩,
      hxStage⟩

/-! ## Limit and Hartogs corollaries with the selector discharged -/

/-- Once the internal family of fiber injections is supplied, the canonical
selector completes the limit-union injection into `limit x kappa`. -/
private theorem injects_limitStage_to_prod_of_internalInjectionFamily
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit)
    {kappa injectionFamily graphFamily : LCarrier.{u}}
    (hinjectionFamily : IsFunctionGraph LMem injectionFamily
      (ordinalLCarrier limit) graphFamily)
    (hinjections : forall ordinal : Ordinal.{u}, ordinal < limit ->
      forall injection : LCarrier.{u},
        GraphValue LMem injectionFamily
          (ordinalLCarrier ordinal) injection ->
        IsInjection LMem injection (stageLCarrier ordinal) kappa) :
    Injects LMem (stageLCarrier limit)
      (Constructible.Model.prodLCarrier
        (ordinalLCarrier limit) kappa) := by
  exact injects_limitStage_to_prod_of_internalFamilies hl
    (leastContainingStageGraph_selectsContainingFiber hl)
    hinjectionFamily hinjections



end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_CanonicalLimitStageSelector

/- Source module: Solutions.Work_CUGCH_InternalProductInjections -/
section GCHSource_Work_CUGCH_InternalProductInjections
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Products of internally represented injections

The Cartesian product of two injections is represented here by an actual
constructible Kuratowski graph.  Its graph is obtained by Separation from a
fixed formula which decodes the input pair, applies the two input graphs, and
encodes the output pair.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## Formula and exact semantics -/













/-! ## Membership consequences -/

private theorem ProductInjectionRel.mem_products_lCarrier
    {first second leftDomain leftCodomain rightDomain rightCodomain
      input output : LCarrier.{u}}
    (hfirst : IsGraphBetween LMem first leftDomain leftCodomain)
    (hsecond : IsGraphBetween LMem second rightDomain rightCodomain)
    (hrel : ProductInjectionRel LMem first second input output) :
    input.1 ∈ (prodLCarrier leftDomain rightDomain).1 /\
      output.1 ∈ (prodLCarrier leftCodomain rightCodomain).1 := by
  rcases hrel with
    ⟨left, right, imageLeft, imageRight,
      hinput, hleft, hright, houtput⟩
  have hleftMem := hfirst.graphValue_mem_lCarrier hleft
  have hrightMem := hsecond.graphValue_mem_lCarrier hright
  have hinputEq :=
    (isKuratowskiPairOf_lCarrier_iff input left right).mp hinput
  have houtputEq :=
    (isKuratowskiPairOf_lCarrier_iff
      output imageLeft imageRight).mp houtput
  constructor
  · change input.1 ∈ ZFSet.prod leftDomain.1 rightDomain.1
    rw [hinputEq, ZFSet.pair_mem_prod]
    exact ⟨hleftMem.1, hrightMem.1⟩
  · change output.1 ∈ ZFSet.prod leftCodomain.1 rightCodomain.1
    rw [houtputEq, ZFSet.pair_mem_prod]
    exact ⟨hleftMem.2, hrightMem.2⟩

/-! ## The product graph -/

private theorem exists_productInjectionGraph_lCarrier
    {first second leftDomain leftCodomain rightDomain rightCodomain :
      LCarrier.{u}}
    (hfirst : IsInjection LMem first leftDomain leftCodomain)
    (hsecond : IsInjection LMem second rightDomain rightCodomain) :
    exists graph : LCarrier.{u},
      IsGraphBetween LMem graph
        (prodLCarrier leftDomain rightDomain)
        (prodLCarrier leftCodomain rightCodomain) /\
        forall input output : LCarrier.{u},
          GraphValue LMem graph input output <->
            ProductInjectionRel LMem first second input output := by
  let domain := prodLCarrier leftDomain rightDomain
  let codomain := prodLCarrier leftCodomain rightCodomain
  let support := unionLCarrier domain codomain
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      productInjectionFormula ![first, second] support with
    ⟨graph, hsupport, hrelation⟩
  have hvalue : forall input output : LCarrier.{u},
      GraphValue LMem graph input output <->
        ProductInjectionRel LMem first second input output := by
    intro input output
    rw [graphValue_lCarrier_iff_graphRel, hrelation]
    constructor
    · rintro ⟨_hinputSupport, _houtputSupport, hformula⟩
      exact (satisfies_productInjectionRelation
        first second input output).mp hformula
    · intro hrel
      have hmem := hrel.mem_products_lCarrier hfirst.1 hsecond.1
      refine ⟨?_, ?_, ?_⟩
      · exact (mem_unionLCarrier_iff domain codomain input).mpr
          (Or.inl hmem.1)
      · exact (mem_unionLCarrier_iff domain codomain output).mpr
          (Or.inr hmem.2)
      · exact (satisfies_productInjectionRelation
          first second input output).mpr hrel
  refine ⟨graph, ?_, hvalue⟩
  intro pair hpair
  rcases hsupport pair hpair with
    ⟨input, output, _hinputSupport, _houtputSupport,
      hpairEq, hformula⟩
  have hrel := (satisfies_productInjectionRelation
    first second input output).mp hformula
  have hmem := hrel.mem_products_lCarrier hfirst.1 hsecond.1
  exact ⟨input, hmem.1, output, hmem.2,
    (isKuratowskiPairOf_lCarrier_iff pair input output).mpr hpairEq⟩

/-! ## Injectivity -/

/-- Internally represented injections are closed under Cartesian product. -/
private theorem injects_prod_of_injects_lCarrier
    {leftDomain leftCodomain rightDomain rightCodomain : LCarrier.{u}}
    (hleft : Injects LMem leftDomain leftCodomain)
    (hright : Injects LMem rightDomain rightCodomain) :
    Injects LMem
      (prodLCarrier leftDomain rightDomain)
      (prodLCarrier leftCodomain rightCodomain) := by
  rcases hleft with ⟨first, hfirst⟩
  rcases hright with ⟨second, hsecond⟩
  rcases exists_productInjectionGraph_lCarrier hfirst hsecond with
    ⟨graph, hbetween, hvalue⟩
  refine ⟨graph, hbetween, ?_, ?_⟩
  · intro input hinput
    rcases ZFSet.mem_prod.mp hinput with
      ⟨leftRaw, hleftRaw, rightRaw, hrightRaw, hinputRaw⟩
    let left : LCarrier.{u} :=
      ⟨leftRaw, Constructible.mem_L_of_mem hleftRaw leftDomain.2⟩
    let right : LCarrier.{u} :=
      ⟨rightRaw, Constructible.mem_L_of_mem hrightRaw rightDomain.2⟩
    have hinputEq : input = orderedPairLCarrier left right := by
      apply Subtype.ext
      exact hinputRaw
    rcases hfirst.2.1 left hleftRaw with
      ⟨imageLeft, himageLeft, hleftValue, hleftUnique⟩
    rcases hsecond.2.1 right hrightRaw with
      ⟨imageRight, himageRight, hrightValue, hrightUnique⟩
    let output := orderedPairLCarrier imageLeft imageRight
    have houtput : output.1 ∈
        (prodLCarrier leftCodomain rightCodomain).1 := by
      change ZFSet.pair imageLeft.1 imageRight.1 ∈
        ZFSet.prod leftCodomain.1 rightCodomain.1
      rw [ZFSet.pair_mem_prod]
      exact ⟨himageLeft, himageRight⟩
    have hinputPair :
        IsKuratowskiPairOf LMem input left right := by
      apply (isKuratowskiPairOf_lCarrier_iff input left right).mpr
      rw [hinputEq]
      rfl
    have houtputPair :
        IsKuratowskiPairOf LMem output imageLeft imageRight :=
      (isKuratowskiPairOf_lCarrier_iff
        output imageLeft imageRight).mpr rfl
    have hrel : ProductInjectionRel LMem first second input output :=
      ⟨left, right, imageLeft, imageRight,
        hinputPair, hleftValue, hrightValue, houtputPair⟩
    refine ⟨output, houtput, (hvalue input output).mpr hrel, ?_⟩
    intro other _hother hinputOther
    rcases (hvalue input other).mp hinputOther with
      ⟨left', right', imageLeft', imageRight',
        hinput', hleftValue', hrightValue', hother⟩
    have hinputCoordinates := ZFSet.pair_inj.mp
      (((isKuratowskiPairOf_lCarrier_iff input left right).mp
        hinputPair).symm.trans
        ((isKuratowskiPairOf_lCarrier_iff input left' right').mp hinput'))
    have hleftEq : left' = left := Subtype.ext hinputCoordinates.1.symm
    have hrightEq : right' = right := Subtype.ext hinputCoordinates.2.symm
    subst left'
    subst right'
    have himageLeft' :=
      (hfirst.1.graphValue_mem_lCarrier hleftValue').2
    have himageRight' :=
      (hsecond.1.graphValue_mem_lCarrier hrightValue').2
    have himageLeftEq : imageLeft' = imageLeft :=
      hleftUnique imageLeft' himageLeft' hleftValue'
    have himageRightEq : imageRight' = imageRight :=
      hrightUnique imageRight' himageRight' hrightValue'
    subst imageLeft'
    subst imageRight'
    apply Subtype.ext
    simpa only [output, orderedPairLCarrier_val] using
      (isKuratowskiPairOf_lCarrier_iff
        other imageLeft imageRight).mp hother
  · intro output houtput input hinput hinputValue
      other hother hotherValue
    rcases (hvalue input output).mp hinputValue with
      ⟨left, right, imageLeft, imageRight,
        hinputPair, hleftValue, hrightValue, houtputPair⟩
    rcases (hvalue other output).mp hotherValue with
      ⟨left', right', imageLeft', imageRight',
        hotherPair, hleftValue', hrightValue', houtputPair'⟩
    have houtputCoordinates := ZFSet.pair_inj.mp
      (((isKuratowskiPairOf_lCarrier_iff
          output imageLeft imageRight).mp houtputPair).symm.trans
        ((isKuratowskiPairOf_lCarrier_iff
          output imageLeft' imageRight').mp houtputPair'))
    have himageLeftEq : imageLeft' = imageLeft :=
      Subtype.ext houtputCoordinates.1.symm
    have himageRightEq : imageRight' = imageRight :=
      Subtype.ext houtputCoordinates.2.symm
    subst imageLeft'
    subst imageRight'
    have hleftDomain :=
      (hfirst.1.graphValue_mem_lCarrier hleftValue).1
    have hleftDomain' :=
      (hfirst.1.graphValue_mem_lCarrier hleftValue').1
    have hrightDomain :=
      (hsecond.1.graphValue_mem_lCarrier hrightValue).1
    have hrightDomain' :=
      (hsecond.1.graphValue_mem_lCarrier hrightValue').1
    have himageLeftMem :=
      (hfirst.1.graphValue_mem_lCarrier hleftValue).2
    have himageRightMem :=
      (hsecond.1.graphValue_mem_lCarrier hrightValue).2
    have hleftEq : left' = left :=
      hfirst.2.2 imageLeft himageLeftMem
        left hleftDomain hleftValue left' hleftDomain' hleftValue'
    have hrightEq : right' = right :=
      hsecond.2.2 imageRight himageRightMem
        right hrightDomain hrightValue right' hrightDomain' hrightValue'
    subst left'
    subst right'
    apply Subtype.ext
    exact ((isKuratowskiPairOf_lCarrier_iff other left right).mp
      hotherPair).trans
        ((isKuratowskiPairOf_lCarrier_iff input left right).mp
          hinputPair).symm

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalProductInjections

/- Source module: Solutions.Work_CUGCH_InternalStageInjectionFamily -/
section GCHSource_Work_CUGCH_InternalStageInjectionFamily
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Collecting internal stage injections by Replacement

`CanonicalLimitStageSelector` reduces the limit-stage cardinal argument to a
single constructible function graph which assigns an injection graph to every
earlier stage.  This file records the exact formula-level input needed to
construct that family by Replacement.

The remaining mathematical obligation is deliberately visible as
`InternalStageInjectionFormulaData`: one fixed first-order formula must have a
unique output at every ordinal below the limit, and that output must really be
an internal injection from the corresponding constructible stage.  An
external cardinal estimate, or an externally chosen family of maps, does not
inhabit this structure.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## A formula-functional Replacement graph and its range -/



/-! ## The exact uniform-stage interface -/



/-- A uniform formula satisfying the preceding interface is collected into
the exact internal family consumed by the limit-stage union theorem. -/
private theorem exists_internalStageInjectionFamily_of_formulaData
    {limit : Ordinal.{u}} {kappa : LCarrier.{u}}
    (data : InternalStageInjectionFormulaData limit kappa) :
    exists injectionFamily graphFamily : LCarrier.{u},
      IsFunctionGraph LMem injectionFamily
        (ordinalLCarrier limit) graphFamily /\
      forall ordinal : Ordinal.{u}, ordinal < limit ->
        forall injection : LCarrier.{u},
          GraphValue LMem injectionFamily
            (ordinalLCarrier ordinal) injection ->
          IsInjection LMem injection (stageLCarrier ordinal) kappa := by
  rcases exists_replacementFunctionGraphAndRangeLCarrier
      data.formula data.params (ordinalLCarrier limit)
      data.existsUnique_output with
    ⟨injectionFamily, graphFamily, hfamily, _hrange, hvalue⟩
  refine ⟨injectionFamily, graphFamily, hfamily, ?_⟩
  intro ordinal hordinal injection hinjection
  apply data.output_isInjection ordinal hordinal injection
  exact (hvalue (ordinalLCarrier ordinal) injection).mp hinjection |>.2

/-! ## Exact connection to the Hartogs stage bound -/



end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalStageInjectionFamily

/- Source module: Solutions.Work_CUGCH_CanonicalStageInjectionFamily -/
section GCHSource_Work_CUGCH_CanonicalStageInjectionFamily
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Canonical internal injection families for constructible stages

Assume that every `L_alpha`, for `alpha < limit`, has an internally
represented injection into `kappa`.  All such graphs are subsets of
`L_limit x kappa`, so the genuine internal powerset of that product is a
single set bounding every candidate.

A fixed first-order formula obtains `L_alpha` through the already internal
`stageValueGraph limit`, and selects the least candidate injection graph in
the canonical witness order on the bounding powerset.  Replacement over the
internal ordinal `limit` then produces the actual family graph.  External
ordinal decoding is used only to prove totality and correctness of this fixed
formula; it is not used as the collected family.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model
open Constructible.FiniteSequenceZF

noncomputable section

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## A common internal bound for all candidate graphs -/







/-! ## Candidate sets -/









/-! ## The fixed canonical-selection formula -/











/-! ## Existence and uniqueness of the canonical graph -/





/-! ## Formula data and the internally collected family -/



/-- Replacement constructs the genuine indexed family and its range. -/
private theorem exists_canonicalStageInjectionFamily
    (limit : Ordinal.{u}) (kappa : LCarrier.{u})
    (hinjects : ∀ ordinal : Ordinal.{u}, ordinal < limit →
      Injects LMem (stageLCarrier ordinal) kappa) :
    ∃ injectionFamily graphFamily : LCarrier.{u},
      IsFunctionGraph LMem injectionFamily
        (ordinalLCarrier limit) graphFamily ∧
      ∀ ordinal : Ordinal.{u}, ordinal < limit →
        ∀ injection : LCarrier.{u},
          GraphValue LMem injectionFamily
            (ordinalLCarrier ordinal) injection →
          IsInjection LMem injection (stageLCarrier ordinal) kappa :=
  exists_internalStageInjectionFamily_of_formulaData
    (canonicalStageInjectionFormulaData limit kappa hinjects)

/-! ## The exact Hartogs interface -/



end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_CanonicalStageInjectionFamily

/- Source module: Solutions.Work_CUGCH_InternalFiniteTupleInjection -/
section GCHSource_Work_CUGCH_InternalFiniteTupleInjection
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# An internal injection for all finite tuples

Let `a` inject into an infinite internal cardinal `kappa`, and let
`kappa x kappa` inject into `kappa`.  A finite tuple is folded from left to
right with the latter injection.  Its arity is folded into the result once
more, so tuples of different lengths have different codes.

The fold is described by one first-order formula.  Its finite history is an
actual member of `L`, and Separation therefore produces one genuine
Kuratowski graph for the injection.  No externally chosen family of graphs
is used as the represented function.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible
open Constructible.Model
open Constructible.FiniteSequenceZF

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## The uniform finite-fold formula -/





































/-! ## Raw functionality and the two finite inductions -/

/-- Two set-theoretic function graphs with the same underlying set have the
same domain. -/
private theorem isFunc_domain_eq
    {left right codomain graph : ZFSet.{u}}
    (hleft : ZFSet.IsFunc left codomain graph)
    (hright : ZFSet.IsFunc right codomain graph) :
    left = right := by
  apply ZFSet.ext
  intro index
  constructor
  · intro hindex
    rcases hleft.2 index hindex with ⟨value, hvalue, _⟩
    exact (ZFSet.pair_mem_prod.mp (hright.1 hvalue)).1
  · intro hindex
    rcases hright.2 index hindex with ⟨value, hvalue, _⟩
    exact (ZFSet.pair_mem_prod.mp (hleft.1 hvalue)).1

/-- A `ZFSet.IsFunc` graph has at most one value at every displayed input. -/
private theorem isFunc_raw_value_unique
    {domain codomain graph index left right : ZFSet.{u}}
    (hfunc : ZFSet.IsFunc domain codomain graph)
    (hleft : ZFSet.pair index left ∈ graph)
    (hright : ZFSet.pair index right ∈ graph) :
    left = right := by
  have hindex : index ∈ domain :=
    (ZFSet.pair_mem_prod.mp (hfunc.1 hleft)).1
  rcases hfunc.2 index hindex with
    ⟨value, _hvalue, hvalueUnique⟩
  exact (hvalueUnique left hleft).trans
    (hvalueUnique right hright).symm

/-- Raw membership in an internal injection graph has unique output. -/
private theorem injection_raw_output_unique
    {graph domain codomain x left right : LCarrier.{u}}
    (hinjection : IsInjection LMem graph domain codomain)
    (hleft : ZFSet.pair x.1 left.1 ∈ graph.1)
    (hright : ZFSet.pair x.1 right.1 ∈ graph.1) :
    left = right := by
  have hleftValue : GraphValue LMem graph x left :=
    (graphValue_lCarrier_iff_graphRel graph x left).mpr hleft
  have hrightValue : GraphValue LMem graph x right :=
    (graphValue_lCarrier_iff_graphRel graph x right).mpr hright
  have hleftMem :=
    hinjection.1.graphValue_mem_lCarrier hleftValue
  have hrightMem :=
    hinjection.1.graphValue_mem_lCarrier hrightValue
  exact hinjection.toIsFunctionGraph.graphValue_unique
    hleftMem.1 hleftMem.2 hrightMem.2 hleftValue hrightValue

/-- Raw membership in an internal injection graph has unique input. -/
private theorem injection_raw_input_unique
    {graph domain codomain left right output : LCarrier.{u}}
    (hinjection : IsInjection LMem graph domain codomain)
    (hleft : ZFSet.pair left.1 output.1 ∈ graph.1)
    (hright : ZFSet.pair right.1 output.1 ∈ graph.1) :
    left = right := by
  have hleftValue : GraphValue LMem graph left output :=
    (graphValue_lCarrier_iff_graphRel graph left output).mpr hleft
  have hrightValue : GraphValue LMem graph right output :=
    (graphValue_lCarrier_iff_graphRel graph right output).mpr hright
  have hleftMem :=
    hinjection.1.graphValue_mem_lCarrier hleftValue
  have hrightMem :=
    hinjection.1.graphValue_mem_lCarrier hrightValue
  exact (hinjection.2.2 output hleftMem.2
    left hleftMem.1 hleftValue
    right hrightMem.1 hrightValue).symm

private theorem natCode_mem_succ_of_mem
    {n : Nat} {index : ZFSet.{u}}
    (hindex : index ∈ (natCode n : ZFSet.{u})) :
    index ∈ (natCode (n + 1) : ZFSet.{u}) := by
  rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt
      index n).mp hindex with ⟨i, hi, rfl⟩
  exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
    (natCode i) (n + 1)).mpr ⟨i, Nat.lt_succ_of_lt hi, rfl⟩

/--
Forward induction through two valid fold histories: for a fixed input tuple,
the values displayed at the final index agree.
-/
private theorem finiteTupleFold_final_unique
    {a kappa aInjection squareInjection tuple
      firstHistory secondHistory zero : LCarrier.{u}}
    (haInjection : IsInjection LMem aInjection a kappa)
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa)
    (htupleFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ tuple.1 →
        ZFSet.pair index right ∈ tuple.1 →
        left = right)
    (hfirstHistoryFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ firstHistory.1 →
        ZFSet.pair index right ∈ firstHistory.1 →
        left = right)
    (hsecondHistoryFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ secondHistory.1 →
        ZFSet.pair index right ∈ secondHistory.1 →
        left = right)
    (hzeroValue : zero.1 = (natCode 0 : ZFSet.{u}))
    (hfirstZero : ZFSet.pair zero.1 zero.1 ∈ firstHistory.1)
    (hsecondZero : ZFSet.pair zero.1 zero.1 ∈ secondHistory.1)
    (n : Nat)
    (hfirstStep : FiniteTupleFoldStep aInjection squareInjection
      tuple firstHistory
        (TextbookNatFormula.textbookNatCodeLCarrier n))
    (hsecondStep : FiniteTupleFoldStep aInjection squareInjection
      tuple secondHistory
        (TextbookNatFormula.textbookNatCodeLCarrier n))
    {firstValue secondValue : LCarrier.{u}}
    (hfirstValue :
      ZFSet.pair (natCode n) firstValue.1 ∈ firstHistory.1)
    (hsecondValue :
      ZFSet.pair (natCode n) secondValue.1 ∈ secondHistory.1) :
    firstValue = secondValue := by
  induction n generalizing firstValue secondValue with
  | zero =>
      apply Subtype.ext
      have hfirstRaw : firstValue.1 = zero.1 := by
        apply hfirstHistoryFunctional hfirstValue
        simpa only [hzeroValue] using hfirstZero
      have hsecondRaw : secondValue.1 = zero.1 := by
        apply hsecondHistoryFunctional hsecondValue
        simpa only [hzeroValue] using hsecondZero
      exact hfirstRaw.trans hsecondRaw.symm
  | succ n ih =>
      let index : LCarrier.{u} :=
        TextbookNatFormula.textbookNatCodeLCarrier n
      have hindex :
          index.1 ∈
            (TextbookNatFormula.textbookNatCodeLCarrier (n + 1)).1 := by
        change (natCode n : ZFSet.{u}) ∈ natCode (n + 1)
        exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
          (natCode n) (n + 1)).mpr ⟨n, Nat.lt_succ_self n, rfl⟩
      rcases hfirstStep index hindex with
        ⟨firstIndexSucc, firstEntry, firstEntryCode,
          firstCurrent, firstNext, firstPair,
          hfirstSucc, hfirstEntry, hfirstEntryCode,
          hfirstCurrent, hfirstNext, hfirstPair, hfirstSquare⟩
      rcases hsecondStep index hindex with
        ⟨secondIndexSucc, secondEntry, secondEntryCode,
          secondCurrent, secondNext, secondPair,
          hsecondSucc, hsecondEntry, hsecondEntryCode,
          hsecondCurrent, hsecondNext, hsecondPair, hsecondSquare⟩
      have hfirstNextAt :
          ZFSet.pair (natCode (n + 1)) firstNext.1 ∈ firstHistory.1 := by
        have hsucc :
            firstIndexSucc.1 = (natCode (n + 1) : ZFSet.{u}) :=
          hfirstSucc.trans (FiniteSequenceZF.natCode_succ_eq_insert n).symm
        simpa only [hsucc] using hfirstNext
      have hsecondNextAt :
          ZFSet.pair (natCode (n + 1)) secondNext.1 ∈
            secondHistory.1 := by
        have hsucc :
            secondIndexSucc.1 = (natCode (n + 1) : ZFSet.{u}) :=
          hsecondSucc.trans (FiniteSequenceZF.natCode_succ_eq_insert n).symm
        simpa only [hsucc] using hsecondNext
      have hfirstValueNext : firstValue = firstNext := by
        apply Subtype.ext
        exact hfirstHistoryFunctional hfirstValue hfirstNextAt
      have hsecondValueNext : secondValue = secondNext := by
        apply Subtype.ext
        exact hsecondHistoryFunctional hsecondValue hsecondNextAt
      have hfirstStepRestricted : FiniteTupleFoldStep
          aInjection squareInjection tuple firstHistory
          (TextbookNatFormula.textbookNatCodeLCarrier n) := by
        intro earlier hearlier
        exact hfirstStep earlier (natCode_mem_succ_of_mem hearlier)
      have hsecondStepRestricted : FiniteTupleFoldStep
          aInjection squareInjection tuple secondHistory
          (TextbookNatFormula.textbookNatCodeLCarrier n) := by
        intro earlier hearlier
        exact hsecondStep earlier (natCode_mem_succ_of_mem hearlier)
      have hcurrentEq : firstCurrent = secondCurrent :=
        ih hfirstStepRestricted hsecondStepRestricted
          hfirstCurrent hsecondCurrent
      have hentryRaw : firstEntry.1 = secondEntry.1 :=
        htupleFunctional hfirstEntry hsecondEntry
      have hentryEq : firstEntry = secondEntry :=
        Subtype.ext hentryRaw
      subst secondEntry
      have hentryCodeEq : firstEntryCode = secondEntryCode :=
        injection_raw_output_unique haInjection
          hfirstEntryCode hsecondEntryCode
      subst secondEntryCode
      subst secondCurrent
      have hpairEq : firstPair = secondPair := by
        apply Subtype.ext
        exact hfirstPair.trans hsecondPair.symm
      subst secondPair
      have hnextEq : firstNext = secondNext :=
        injection_raw_output_unique hsquareInjection
          hfirstSquare hsecondSquare
      exact hfirstValueNext.trans (hnextEq.trans hsecondValueNext.symm)

/--
Backward induction through two fold histories: equality of the final fold
values recovers every entry of the two input tuples.
-/
private theorem finiteTupleFold_entries_unique
    {a kappa aInjection squareInjection
      firstTuple secondTuple firstHistory secondHistory : LCarrier.{u}}
    (haInjection : IsInjection LMem aInjection a kappa)
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa)
    (hfirstTupleFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ firstTuple.1 →
        ZFSet.pair index right ∈ firstTuple.1 →
        left = right)
    (hsecondTupleFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ secondTuple.1 →
        ZFSet.pair index right ∈ secondTuple.1 →
        left = right)
    (hfirstHistoryFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ firstHistory.1 →
        ZFSet.pair index right ∈ firstHistory.1 →
        left = right)
    (hsecondHistoryFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ secondHistory.1 →
        ZFSet.pair index right ∈ secondHistory.1 →
        left = right)
    (n : Nat)
    (hfirstStep : FiniteTupleFoldStep aInjection squareInjection
      firstTuple firstHistory
        (TextbookNatFormula.textbookNatCodeLCarrier n))
    (hsecondStep : FiniteTupleFoldStep aInjection squareInjection
      secondTuple secondHistory
        (TextbookNatFormula.textbookNatCodeLCarrier n))
    {firstFinal secondFinal : LCarrier.{u}}
    (hfirstFinal :
      ZFSet.pair (natCode n) firstFinal.1 ∈ firstHistory.1)
    (hsecondFinal :
      ZFSet.pair (natCode n) secondFinal.1 ∈ secondHistory.1)
    (hfinalEq : firstFinal = secondFinal) :
    ∀ i : Nat, i < n →
      ∀ firstEntry secondEntry : LCarrier.{u},
        ZFSet.pair (natCode i) firstEntry.1 ∈ firstTuple.1 →
        ZFSet.pair (natCode i) secondEntry.1 ∈ secondTuple.1 →
        firstEntry = secondEntry := by
  induction n generalizing firstFinal secondFinal with
  | zero =>
      intro i hi
      exact (Nat.not_lt_zero i hi).elim
  | succ n ih =>
      let index : LCarrier.{u} :=
        TextbookNatFormula.textbookNatCodeLCarrier n
      have hindex :
          index.1 ∈
            (TextbookNatFormula.textbookNatCodeLCarrier (n + 1)).1 := by
        change (natCode n : ZFSet.{u}) ∈ natCode (n + 1)
        exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
          (natCode n) (n + 1)).mpr ⟨n, Nat.lt_succ_self n, rfl⟩
      rcases hfirstStep index hindex with
        ⟨firstIndexSucc, firstEntry, firstEntryCode,
          firstCurrent, firstNext, firstPair,
          hfirstSucc, hfirstEntry, hfirstEntryCode,
          hfirstCurrent, hfirstNext, hfirstPair, hfirstSquare⟩
      rcases hsecondStep index hindex with
        ⟨secondIndexSucc, secondEntry, secondEntryCode,
          secondCurrent, secondNext, secondPair,
          hsecondSucc, hsecondEntry, hsecondEntryCode,
          hsecondCurrent, hsecondNext, hsecondPair, hsecondSquare⟩
      have hfirstNextAt :
          ZFSet.pair (natCode (n + 1)) firstNext.1 ∈ firstHistory.1 := by
        have hsucc :
            firstIndexSucc.1 = (natCode (n + 1) : ZFSet.{u}) :=
          hfirstSucc.trans (FiniteSequenceZF.natCode_succ_eq_insert n).symm
        simpa only [hsucc] using hfirstNext
      have hsecondNextAt :
          ZFSet.pair (natCode (n + 1)) secondNext.1 ∈
            secondHistory.1 := by
        have hsucc :
            secondIndexSucc.1 = (natCode (n + 1) : ZFSet.{u}) :=
          hsecondSucc.trans (FiniteSequenceZF.natCode_succ_eq_insert n).symm
        simpa only [hsucc] using hsecondNext
      have hfirstFinalNext : firstFinal = firstNext := by
        apply Subtype.ext
        exact hfirstHistoryFunctional hfirstFinal hfirstNextAt
      have hsecondFinalNext : secondFinal = secondNext := by
        apply Subtype.ext
        exact hsecondHistoryFunctional hsecondFinal hsecondNextAt
      have hnextEq : firstNext = secondNext :=
        hfirstFinalNext.symm.trans (hfinalEq.trans hsecondFinalNext)
      have hsecondSquare' :
          ZFSet.pair secondPair.1 firstNext.1 ∈ squareInjection.1 := by
        rw [hnextEq]
        exact hsecondSquare
      have hfoldInputEq : firstPair = secondPair :=
        injection_raw_input_unique hsquareInjection
          hfirstSquare hsecondSquare'
      have hfoldCoordinates : firstCurrent.1 = secondCurrent.1 ∧
          firstEntryCode.1 = secondEntryCode.1 := by
        apply ZFSet.pair_inj.mp
        exact hfirstPair.symm.trans
          (congrArg Subtype.val hfoldInputEq |>.trans hsecondPair)
      have hcurrentEq : firstCurrent = secondCurrent :=
        Subtype.ext hfoldCoordinates.1
      have hentryCodeEq : firstEntryCode = secondEntryCode :=
        Subtype.ext hfoldCoordinates.2
      subst secondEntryCode
      have hentryEq : firstEntry = secondEntry :=
        injection_raw_input_unique haInjection
          hfirstEntryCode hsecondEntryCode
      have hfirstStepRestricted : FiniteTupleFoldStep
          aInjection squareInjection firstTuple firstHistory
          (TextbookNatFormula.textbookNatCodeLCarrier n) := by
        intro earlier hearlier
        exact hfirstStep earlier (natCode_mem_succ_of_mem hearlier)
      have hsecondStepRestricted : FiniteTupleFoldStep
          aInjection squareInjection secondTuple secondHistory
          (TextbookNatFormula.textbookNatCodeLCarrier n) := by
        intro earlier hearlier
        exact hsecondStep earlier (natCode_mem_succ_of_mem hearlier)
      intro i hi leftEntry rightEntry hleftEntry hrightEntry
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hiEarlier | rfl
      · exact ih hfirstStepRestricted hsecondStepRestricted
          hfirstCurrent hsecondCurrent hcurrentEq
          i hiEarlier leftEntry rightEntry hleftEntry hrightEntry
      · have hleftEq : leftEntry = firstEntry := by
          apply Subtype.ext
          exact hfirstTupleFunctional hleftEntry hfirstEntry
        have hrightEq : rightEntry = secondEntry := by
          apply Subtype.ext
          exact hsecondTupleFunctional hrightEntry hsecondEntry
        exact hleftEq.trans (hentryEq.trans hrightEq.symm)

/-! ## Semantic uniqueness of the fold relation -/

private theorem finiteTupleFoldRel_output_unique
    {zero a kappa aInjection squareInjection tuple
      firstOutput secondOutput : LCarrier.{u}}
    (hzeroValue : zero.1 = (natCode 0 : ZFSet.{u}))
    (haInjection : IsInjection LMem aInjection a kappa)
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa)
    (hfirst : FiniteTupleFoldRel omegaLCarrier zero a kappa
      aInjection squareInjection tuple firstOutput)
    (hsecond : FiniteTupleFoldRel omegaLCarrier zero a kappa
      aInjection squareInjection tuple secondOutput) :
    firstOutput = secondOutput := by
  rcases hfirst with
    ⟨firstArity, hfirstArityOmega, firstAritySucc, hfirstSucc,
      firstHistory, hfirstTuple, hfirstHistory, hfirstZero, hfirstStep,
      firstCurrent, firstPair, hfirstCurrent, hfirstPair, hfirstOutput⟩
  rcases hsecond with
    ⟨secondArity, _hsecondArityOmega, secondAritySucc, hsecondSucc,
      secondHistory, hsecondTuple, hsecondHistory, hsecondZero, hsecondStep,
      secondCurrent, secondPair, hsecondCurrent, hsecondPair, hsecondOutput⟩
  have harityRaw : firstArity.1 = secondArity.1 :=
    isFunc_domain_eq hfirstTuple hsecondTuple
  have harityEq : firstArity = secondArity :=
    Subtype.ext harityRaw
  subst secondArity
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode
      firstArity.1).mp hfirstArityOmega with ⟨n, harityValue⟩
  have harityEqNat :
      firstArity =
        TextbookNatFormula.textbookNatCodeLCarrier n := by
    apply Subtype.ext
    exact harityValue
  subst firstArity
  have hfirstHistoryFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ firstHistory.1 →
        ZFSet.pair index right ∈ firstHistory.1 →
        left = right :=
    fun {_index _left _right} hleft hright =>
      isFunc_raw_value_unique hfirstHistory hleft hright
  have hsecondHistoryFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ secondHistory.1 →
        ZFSet.pair index right ∈ secondHistory.1 →
        left = right :=
    fun {_index _left _right} hleft hright =>
      isFunc_raw_value_unique hsecondHistory hleft hright
  have htupleFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ tuple.1 →
        ZFSet.pair index right ∈ tuple.1 →
        left = right :=
    fun {_index _left _right} hleft hright =>
      isFunc_raw_value_unique hfirstTuple hleft hright
  have hcurrentEq : firstCurrent = secondCurrent :=
    finiteTupleFold_final_unique haInjection hsquareInjection
      htupleFunctional hfirstHistoryFunctional hsecondHistoryFunctional
      hzeroValue hfirstZero hsecondZero n hfirstStep hsecondStep
      hfirstCurrent hsecondCurrent
  subst secondCurrent
  have hpairEq : firstPair = secondPair := by
    apply Subtype.ext
    exact hfirstPair.trans hsecondPair.symm
  subst secondPair
  exact injection_raw_output_unique hsquareInjection
    hfirstOutput hsecondOutput

private theorem finiteTupleFoldRel_input_unique
    {zero a kappa aInjection squareInjection
      firstTuple secondTuple output : LCarrier.{u}}
    (haInjection : IsInjection LMem aInjection a kappa)
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa)
    (hfirst : FiniteTupleFoldRel omegaLCarrier zero a kappa
      aInjection squareInjection firstTuple output)
    (hsecond : FiniteTupleFoldRel omegaLCarrier zero a kappa
      aInjection squareInjection secondTuple output) :
    firstTuple = secondTuple := by
  rcases hfirst with
    ⟨firstArity, hfirstArityOmega, firstAritySucc, hfirstSucc,
      firstHistory, hfirstTupleFunc, hfirstHistoryFunc, _hfirstZero,
      hfirstStep, firstCurrent, firstPair, hfirstCurrent,
      hfirstPair, hfirstOutput⟩
  rcases hsecond with
    ⟨secondArity, _hsecondArityOmega, secondAritySucc, hsecondSucc,
      secondHistory, hsecondTupleFunc, hsecondHistoryFunc, _hsecondZero,
      hsecondStep, secondCurrent, secondPair, hsecondCurrent,
      hsecondPair, hsecondOutput⟩
  have hfinalPairEq : firstPair = secondPair :=
    injection_raw_input_unique hsquareInjection
      hfirstOutput hsecondOutput
  have hcoordinates : firstArity.1 = secondArity.1 ∧
      firstCurrent.1 = secondCurrent.1 := by
    apply ZFSet.pair_inj.mp
    exact hfirstPair.symm.trans
      (congrArg Subtype.val hfinalPairEq |>.trans hsecondPair)
  have harityEq : firstArity = secondArity :=
    Subtype.ext hcoordinates.1
  have hcurrentEq : firstCurrent = secondCurrent :=
    Subtype.ext hcoordinates.2
  subst secondArity
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode
      firstArity.1).mp hfirstArityOmega with ⟨n, harityValue⟩
  have harityEqNat :
      firstArity =
        TextbookNatFormula.textbookNatCodeLCarrier n := by
    apply Subtype.ext
    exact harityValue
  subst firstArity
  have hfirstTupleFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ firstTuple.1 →
        ZFSet.pair index right ∈ firstTuple.1 →
        left = right :=
    fun {_index _left _right} hleft hright =>
      isFunc_raw_value_unique hfirstTupleFunc hleft hright
  have hsecondTupleFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ secondTuple.1 →
        ZFSet.pair index right ∈ secondTuple.1 →
        left = right :=
    fun {_index _left _right} hleft hright =>
      isFunc_raw_value_unique hsecondTupleFunc hleft hright
  have hfirstHistoryFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ firstHistory.1 →
        ZFSet.pair index right ∈ firstHistory.1 →
        left = right :=
    fun {_index _left _right} hleft hright =>
      isFunc_raw_value_unique hfirstHistoryFunc hleft hright
  have hsecondHistoryFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ secondHistory.1 →
        ZFSet.pair index right ∈ secondHistory.1 →
        left = right :=
    fun {_index _left _right} hleft hright =>
      isFunc_raw_value_unique hsecondHistoryFunc hleft hright
  have hentries :=
    finiteTupleFold_entries_unique haInjection hsquareInjection
      hfirstTupleFunctional hsecondTupleFunctional
      hfirstHistoryFunctional hsecondHistoryFunctional
      n hfirstStep hsecondStep hfirstCurrent hsecondCurrent hcurrentEq
  rcases exists_textbookTupleGraph_eq_of_isFunc hfirstTupleFunc with
    ⟨firstEntries, hfirstGraph⟩
  rcases exists_textbookTupleGraph_eq_of_isFunc hsecondTupleFunc with
    ⟨secondEntries, hsecondGraph⟩
  have hentryTuples : firstEntries = secondEntries := by
    funext i
    let firstEntry : LCarrier.{u} :=
      ⟨(firstEntries i).1,
        mem_L_of_mem (firstEntries i).2 a.2⟩
    let secondEntry : LCarrier.{u} :=
      ⟨(secondEntries i).1,
        mem_L_of_mem (secondEntries i).2 a.2⟩
    have hfirstEntry :
        ZFSet.pair (natCode i.1) firstEntry.1 ∈ firstTuple.1 := by
      rw [← hfirstGraph]
      exact textbookTupleGraph_value firstEntries i
    have hsecondEntry :
        ZFSet.pair (natCode i.1) secondEntry.1 ∈ secondTuple.1 := by
      rw [← hsecondGraph]
      exact textbookTupleGraph_value secondEntries i
    exact Subtype.ext (congrArg (fun x : LCarrier.{u} => x.1)
      (hentries i.1 i.2 firstEntry secondEntry
        hfirstEntry hsecondEntry))
  apply Subtype.ext
  exact hfirstGraph.symm.trans
    ((congrArg textbookTupleGraph hentryTuples).trans hsecondGraph)

/-! ## A genuine finite history for every tuple -/





private theorem finiteTupleFoldValues_succ
    {a kappa aInjection squareInjection : LCarrier.{u}}
    {n i : Nat}
    (haInjection : IsInjection LMem aInjection a kappa)
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa)
    (zero : RelationCarrier LMem kappa)
    (entries : Fin n → RelationCarrier LMem a)
    (hi : i < n) :
    finiteTupleFoldValues
        haInjection hsquareInjection zero entries (i + 1) =
      hsquareInjection.toFun
        (finiteTupleProductPoint kappa
          (finiteTupleFoldValues
            haInjection hsquareInjection zero entries i)
          (haInjection.toFun (entries ⟨i, hi⟩))) := by
  simp only [finiteTupleFoldValues, hi, dite_true]

private theorem exists_finiteTupleFoldRel
    {a kappa aInjection squareInjection tuple : LCarrier.{u}}
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa)
    (haInjection : IsInjection LMem aInjection a kappa)
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa)
    (htuple : tuple.1 ∈ (internalFiniteTupleSpaces a).1) :
    ∃ output : LCarrier.{u},
      output.1 ∈ kappa.1 ∧
        FiniteTupleFoldRel omegaLCarrier
          (TextbookNatFormula.textbookNatCodeLCarrier 0)
          a kappa aInjection squareInjection tuple output := by
  rcases (mem_internalFiniteTupleSpaces_iff a tuple).mp htuple with
    ⟨n, htupleSpace⟩
  have htupleFunc :
      ZFSet.IsFunc (natCode n) a.1 tuple.1 := by
    apply mem_textbookTupleSpace_iff.mp
    simpa only [finiteTupleSpaceLCarrier_val] using htupleSpace
  rcases exists_textbookTupleGraph_eq_of_isFunc htupleFunc with
    ⟨rawEntries, htupleGraph⟩
  let entries : Fin n → RelationCarrier LMem a :=
    fun i =>
      ⟨⟨(rawEntries i).1,
          mem_L_of_mem (rawEntries i).2 a.2⟩,
        (rawEntries i).2⟩
  have hnatOmega (m : Nat) :
      (TextbookNatFormula.textbookNatCodeLCarrier m).1 ∈
        (omegaLCarrier : LCarrier.{u}).1 := by
    change (natCode m : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode m)).mpr ⟨m, rfl⟩
  let natInKappa (m : Nat) : RelationCarrier LMem kappa :=
    ⟨TextbookNatFormula.textbookNatCodeLCarrier m,
      homega _ (hnatOmega m)⟩
  let values : Nat → RelationCarrier LMem kappa :=
    finiteTupleFoldValues haInjection hsquareInjection
      (natInKappa 0) entries
  let historyEntries : Tuple (ZFCarrier kappa.1) (n + 1) :=
    fun i => ⟨(values i.1).1.1, (values i.1).2⟩
  let history : LCarrier.{u} :=
    ⟨textbookTupleGraph historyEntries,
      textbookTupleGraph_mem_L kappa.2 historyEntries⟩
  let arity : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier n
  let aritySucc : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier (n + 1)
  let finalPairPoint : RelationCarrier LMem (prodLCarrier kappa kappa) :=
    finiteTupleProductPoint kappa (natInKappa n) (values n)
  let outputPoint : RelationCarrier LMem kappa :=
    hsquareInjection.toFun finalPairPoint
  let output : LCarrier.{u} := outputPoint.1
  refine ⟨output, outputPoint.2, ?_⟩
  refine ⟨arity, hnatOmega n, aritySucc, ?_, history, ?_⟩
  · change (natCode (n + 1) : ZFSet.{u}) =
      insert (natCode n) (natCode n)
    exact FiniteSequenceZF.natCode_succ_eq_insert n
  · refine ⟨htupleFunc, ?_, ?_, ?_, ?_⟩
    · simpa only [history, aritySucc,
        TextbookNatFormula.textbookNatCodeLCarrier_val] using
        textbookTupleGraph_isFunc historyEntries
    · have hzeroHistory :=
        textbookTupleGraph_value historyEntries
          (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
      simpa only [history, historyEntries, values,
        finiteTupleFoldValues, natInKappa,
        TextbookNatFormula.textbookNatCodeLCarrier_val] using hzeroHistory
    · intro index hindex
      rcases (mem_natCode_iff_exists_fin index.1 n).mp
          (by simpa only [arity,
            TextbookNatFormula.textbookNatCodeLCarrier_val] using
              hindex) with
        ⟨i, hindexValue⟩
      have hindexEq :
          index =
            TextbookNatFormula.textbookNatCodeLCarrier i.1 := by
        apply Subtype.ext
        exact hindexValue
      subst index
      let indexSucc : LCarrier.{u} :=
        TextbookNatFormula.textbookNatCodeLCarrier (i.1 + 1)
      let entry : LCarrier.{u} := (entries i).1
      let entryCode : LCarrier.{u} :=
        (haInjection.toFun (entries i)).1
      let current : LCarrier.{u} := (values i.1).1
      let next : LCarrier.{u} := (values (i.1 + 1)).1
      let pairPoint : RelationCarrier LMem (prodLCarrier kappa kappa) :=
        finiteTupleProductPoint kappa
          (values i.1) (haInjection.toFun (entries i))
      let pair : LCarrier.{u} := pairPoint.1
      refine ⟨indexSucc, entry, entryCode, current, next, pair,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · change (natCode (i.1 + 1) : ZFSet.{u}) =
          insert (natCode i.1) (natCode i.1)
        exact FiniteSequenceZF.natCode_succ_eq_insert i.1
      · have hentry :=
          textbookTupleGraph_value rawEntries i
        rw [htupleGraph] at hentry
        simpa only [entry, entries,
          TextbookNatFormula.textbookNatCodeLCarrier_val] using hentry
      · have hentryCodeValue :=
          haInjection.toFun_graphValue (entries i)
        exact (graphValue_lCarrier_iff_graphRel
          aInjection entry entryCode).mp (by
            simpa only [entry, entryCode] using hentryCodeValue)
      · have hcurrentHistory :=
          textbookTupleGraph_value historyEntries
            (⟨i.1, Nat.lt_succ_of_lt i.2⟩ : Fin (n + 1))
        simpa only [history, historyEntries, current,
          TextbookNatFormula.textbookNatCodeLCarrier_val] using
          hcurrentHistory
      · have hnextHistory :=
          textbookTupleGraph_value historyEntries
            (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1))
        simpa only [history, historyEntries, next, indexSucc,
          TextbookNatFormula.textbookNatCodeLCarrier_val] using
          hnextHistory
      · rfl
      · have hsquareValue :=
          hsquareInjection.toFun_graphValue pairPoint
        have hsquareRaw :=
          (graphValue_lCarrier_iff_graphRel
            squareInjection pair
              (hsquareInjection.toFun pairPoint).1).mp (by
                simpa only [pair, pairPoint] using hsquareValue)
        have hvaluesSucc :
            values (i.1 + 1) =
              hsquareInjection.toFun pairPoint := by
          simpa only [values, pairPoint] using
            finiteTupleFoldValues_succ
              haInjection hsquareInjection
              (natInKappa 0) entries i.2
        simpa only [next, hvaluesSucc,
          Constructible.Model.GraphRel] using hsquareRaw
    · refine ⟨(values n).1, finalPairPoint.1, ?_, ?_, ?_⟩
      · have hfinalHistory :=
          textbookTupleGraph_value historyEntries
            (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))
        simpa only [history, historyEntries, arity,
          TextbookNatFormula.textbookNatCodeLCarrier_val] using
          hfinalHistory
      · rfl
      · have houtputValue :=
          hsquareInjection.toFun_graphValue finalPairPoint
        exact (graphValue_lCarrier_iff_graphRel
          squareInjection finalPairPoint.1 output).mp (by
            simpa only [output, outputPoint] using houtputValue)

/-! ## Replacement constructs the complete injection graph -/

private theorem finiteTupleFoldRel_output_mem
    {zero a kappa aInjection squareInjection tuple output :
      LCarrier.{u}}
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa)
    (hrel : FiniteTupleFoldRel omegaLCarrier zero a kappa
      aInjection squareInjection tuple output) :
    output.1 ∈ kappa.1 := by
  rcases hrel with
    ⟨arity, _harityOmega, aritySucc, _hsucc, history,
      _htuple, _hhistory, _hzero, _hstep,
      current, pair, _hcurrent, _hpair, houtput⟩
  have hvalue : GraphValue LMem squareInjection pair output :=
    (graphValue_lCarrier_iff_graphRel
      squareInjection pair output).mpr houtput
  exact (hsquareInjection.1.graphValue_mem_lCarrier hvalue).2

private theorem finiteTupleFoldGraph_assignment
    (omega zero a kappa aInjection squareInjection tuple output :
      LCarrier.{u}) :
    snoc (snoc
      ![omega, zero, a, kappa, aInjection, squareInjection]
      tuple) output =
      ![omega, zero, a, kappa, aInjection, squareInjection,
        tuple, output] := by
  simp only [snoc_eq_finSnoc, Matrix.Fin.snoc_vecCons,
    Matrix.Fin.snoc_vecEmpty]

/--
Given genuine internal injections `a → kappa` and
`kappa × kappa → kappa`, Replacement constructs one genuine internal
injection from all finite tuples over `a` into `kappa`.
-/
private theorem injects_internalFiniteTupleSpaces_of_square_lCarrier
    {a kappa aInjection squareInjection : LCarrier.{u}}
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa)
    (haInjection : IsInjection LMem aInjection a kappa)
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa) :
    Injects LMem (internalFiniteTupleSpaces a) kappa := by
  let zero : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier 0
  let domain : LCarrier.{u} := internalFiniteTupleSpaces a
  let params : Tuple LCarrier.{u} 6 :=
    ![omegaLCarrier, zero, a, kappa, aInjection, squareInjection]
  have hzeroValue : zero.1 = (natCode 0 : ZFSet.{u}) :=
    TextbookNatFormula.textbookNatCodeLCarrier_val 0
  have hfun : ∀ tuple : LCarrier.{u}, tuple.1 ∈ domain.1 →
      ∃! output : LCarrier.{u},
        FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
          (snoc (snoc params tuple) output) := by
    intro tuple htuple
    rcases exists_finiteTupleFoldRel homega haInjection
        hsquareInjection htuple with
      ⟨output, _houtputKappa, houtput⟩
    refine ⟨output, ?_, ?_⟩
    · change FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
        (snoc (snoc params tuple) output)
      rw [show snoc (snoc params tuple) output =
          ![omegaLCarrier, zero, a, kappa, aInjection,
            squareInjection, tuple, output] by
        simpa only [params] using finiteTupleFoldGraph_assignment
          omegaLCarrier zero a kappa aInjection squareInjection
          tuple output]
      exact (satisfies_finiteTupleFoldRelationFormula
        omegaLCarrier zero a kappa aInjection squareInjection
        tuple output).mpr houtput
    · intro other hother
      have hother' :
          FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
            ![omegaLCarrier, zero, a, kappa, aInjection,
              squareInjection, tuple, other] := by
        rw [← finiteTupleFoldGraph_assignment
          omegaLCarrier zero a kappa aInjection squareInjection
          tuple other]
        simpa only [params] using hother
      have hotherRel :=
        (satisfies_finiteTupleFoldRelationFormula
          omegaLCarrier zero a kappa aInjection squareInjection
          tuple other).mp hother'
      exact finiteTupleFoldRel_output_unique hzeroValue
        haInjection hsquareInjection hotherRel houtput
  rcases Constructible.Model.exists_replacementFunctionGraphLCarrier
      finiteTupleFoldRelationFormula params domain hfun with
    ⟨graph, hgraph⟩
  have hvalue : ∀ tuple output : LCarrier.{u},
      GraphValue LMem graph tuple output ↔
        tuple.1 ∈ domain.1 ∧
          FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
            (snoc (snoc params tuple) output) := by
    intro tuple output
    constructor
    · rintro ⟨pair, hpairGraph, hpairTO⟩
      rcases (hgraph pair.1).mp hpairGraph with
        ⟨tuple', htuple', output', houtput', hpairEq⟩
      have hpairTORaw :=
        (isKuratowskiPairOf_lCarrier_iff
          pair tuple output).mp hpairTO
      have hcoordinates := ZFSet.pair_inj.mp
        (hpairEq.symm.trans hpairTORaw)
      have htupleEq : tuple' = tuple :=
        Subtype.ext hcoordinates.1
      have houtputEq : output' = output :=
        Subtype.ext hcoordinates.2
      subst tuple'
      subst output'
      exact ⟨htuple', houtput'⟩
    · rintro ⟨htuple, houtput⟩
      let pair := orderedPairLCarrier tuple output
      refine ⟨pair, ?_, ?_⟩
      · apply (hgraph pair.1).mpr
        exact ⟨tuple, htuple, output, houtput, rfl⟩
      · exact (isKuratowskiPairOf_lCarrier_iff
          pair tuple output).mpr rfl
  have hbetween : IsGraphBetween LMem graph domain kappa := by
    intro pair hpairGraph
    rcases (hgraph pair.1).mp hpairGraph with
      ⟨tuple, htuple, output, houtput, hpairEq⟩
    have houtput' :
        FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
          ![omegaLCarrier, zero, a, kappa, aInjection,
            squareInjection, tuple, output] := by
      rw [← finiteTupleFoldGraph_assignment
        omegaLCarrier zero a kappa aInjection squareInjection
        tuple output]
      simpa only [params] using houtput
    have hrel :=
      (satisfies_finiteTupleFoldRelationFormula
        omegaLCarrier zero a kappa aInjection squareInjection
        tuple output).mp houtput'
    have houtputKappa :=
      finiteTupleFoldRel_output_mem hsquareInjection hrel
    exact ⟨tuple, htuple, output, houtputKappa,
      (isKuratowskiPairOf_lCarrier_iff
        pair tuple output).mpr hpairEq⟩
  refine ⟨graph, hbetween, ?_, ?_⟩
  · intro tuple htuple
    rcases hfun tuple htuple with
      ⟨output, houtput, houtputUnique⟩
    have houtput' :
        FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
          ![omegaLCarrier, zero, a, kappa, aInjection,
            squareInjection, tuple, output] := by
      rw [← finiteTupleFoldGraph_assignment
        omegaLCarrier zero a kappa aInjection squareInjection
        tuple output]
      simpa only [params] using houtput
    have hrel :=
      (satisfies_finiteTupleFoldRelationFormula
        omegaLCarrier zero a kappa aInjection squareInjection
        tuple output).mp houtput'
    have houtputKappa :=
      finiteTupleFoldRel_output_mem hsquareInjection hrel
    refine ⟨output, houtputKappa,
      (hvalue tuple output).mpr ⟨htuple, houtput⟩, ?_⟩
    intro other _hotherKappa htupleOther
    apply houtputUnique other
    exact (hvalue tuple other).mp htupleOther |>.2
  · intro output _houtputKappa tuple htuple htupleOutput
      other hother hotherOutput
    have htupleFormula :=
      (hvalue tuple output).mp htupleOutput |>.2
    have hotherFormula :=
      (hvalue other output).mp hotherOutput |>.2
    have htupleFormula' :
        FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
          ![omegaLCarrier, zero, a, kappa, aInjection,
            squareInjection, tuple, output] := by
      rw [← finiteTupleFoldGraph_assignment
        omegaLCarrier zero a kappa aInjection squareInjection
        tuple output]
      simpa only [params] using htupleFormula
    have hotherFormula' :
        FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
          ![omegaLCarrier, zero, a, kappa, aInjection,
            squareInjection, other, output] := by
      rw [← finiteTupleFoldGraph_assignment
        omegaLCarrier zero a kappa aInjection squareInjection
        other output]
      simpa only [params] using hotherFormula
    have htupleRel :=
      (satisfies_finiteTupleFoldRelationFormula
        omegaLCarrier zero a kappa aInjection squareInjection
        tuple output).mp htupleFormula'
    have hotherRel :=
      (satisfies_finiteTupleFoldRelationFormula
        omegaLCarrier zero a kappa aInjection squareInjection
        other output).mp hotherFormula'
    exact finiteTupleFoldRel_input_unique
      haInjection hsquareInjection hotherRel htupleRel



end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalFiniteTupleInjection

/- Source module: Solutions.Work_CUGCH_InternalFunctionRangeInjection -/
section GCHSource_Work_CUGCH_InternalFunctionRangeInjection
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# Internal injections from function ranges

For a represented function graph whose displayed codomain is its actual
range, the canonical constructible well-order selects the least preimage of
each range element.  Replacement collects these selections into an actual
right-inverse graph in `L`, yielding an internal injection of the range into
the original domain.
-/

section

universe u

namespace Constructible

noncomputable section

namespace Model

open ContinuumFormula

local notation "LMem" => lCarrierMem

/-! ## Fibers and their canonical minima -/













/-- The inverse-minimum formula has exactly one output at every covered
range value. -/
private theorem existsUnique_inverseMinimumFormula
    (graph domain range value : LCarrier.{u})
    (hcovered : forall y : LCarrier.{u}, y.1 ∈ range.1 ->
      exists x : LCarrier.{u}, x.1 ∈ domain.1 /\
        GraphValue LMem graph x y)
    (hvalue : value.1 ∈ range.1) :
    ExistsUnique fun input : LCarrier.{u} =>
      FOFormula.Satisfies LMem inverseMinimumFormula
        ![graph, domain, canonicalWitnessOrder domain, value, input] := by
  let fiber := inverseFiberLCarrier graph domain value
  have hfiberSubset : forall z : LCarrier.{u}, z.1 ∈ fiber.1 ->
      z.1 ∈ (canonicalWitnessStage domain).1 := by
    intro z hz
    exact seed_subset_canonicalWitnessStage domain
      ((mem_inverseFiberLCarrier_iff graph domain value z).mp hz).1
  have hfiberNonempty : exists z : LCarrier.{u}, z.1 ∈ fiber.1 := by
    rcases hcovered value hvalue with ⟨z, hzDomain, hzValue⟩
    refine ⟨z, (mem_inverseFiberLCarrier_iff
      graph domain value z).mpr ⟨hzDomain, ?_⟩⟩
    exact (ContinuumFormula.graphValue_lCarrier_iff_graphRel
      graph z value).mp hzValue
  rcases exists_unique_graph_minimum
      (canonicalWitnessOrder_internallyWellOrders domain)
      hfiberSubset hfiberNonempty with
    ⟨minimum, hminimum, hminimumUnique⟩
  refine ⟨minimum, ?_, ?_⟩
  · apply (satisfies_inverseMinimumFormula
      graph domain (canonicalWitnessOrder domain) value minimum).mpr
    have hminimumFiber :=
      (mem_inverseFiberLCarrier_iff
        graph domain value minimum).mp hminimum.1
    exact ⟨hminimumFiber.1, hminimumFiber.2, fun other hother hgraph =>
      hminimum.2 other
        ((mem_inverseFiberLCarrier_iff
          graph domain value other).mpr ⟨hother, hgraph⟩)⟩
  · intro other hother
    apply hminimumUnique other
    have hotherData :=
      (satisfies_inverseMinimumFormula
        graph domain (canonicalWitnessOrder domain) value other).mp hother
    refine ⟨(mem_inverseFiberLCarrier_iff
      graph domain value other).mpr ⟨hotherData.1, hotherData.2.1⟩, ?_⟩
    intro z hzFiber
    have hzData := (mem_inverseFiberLCarrier_iff
      graph domain value z).mp hzFiber
    exact hotherData.2.2 z hzData.1 hzData.2

/-! ## The represented inverse injection -/

private theorem inverseMinimumAssignment
    (graph domain order value input : LCarrier.{u}) :
    snoc (snoc ![graph, domain, order] value) input =
      ![graph, domain, order, value, input] := by
  funext i
  fin_cases i <;> rfl

/-- A represented function onto its displayed range admits an internally
represented injection of that range back into the original domain. -/
private theorem injects_range_into_domain_of_functionGraph
    (graph domain range : LCarrier.{u})
    (hfunction : ContinuumFormula.IsFunctionGraph LMem
      graph domain range)
    (hcovered : forall y : LCarrier.{u}, y.1 ∈ range.1 ->
      exists x : LCarrier.{u}, x.1 ∈ domain.1 /\
        GraphValue LMem graph x y) :
    Injects LMem range domain := by
  let order := canonicalWitnessOrder domain
  let params : Tuple LCarrier.{u} 3 := ![graph, domain, order]
  have hformulaUnique : forall value : LCarrier.{u},
      value.1 ∈ range.1 ->
        ExistsUnique fun input : LCarrier.{u} =>
          FOFormula.Satisfies LMem inverseMinimumFormula
            (snoc (snoc params value) input) := by
    intro value hvalue
    simpa only [params, order, inverseMinimumAssignment] using
      existsUnique_inverseMinimumFormula
        graph domain range value hcovered hvalue
  rcases exists_replacementFunctionGraphLCarrier
      inverseMinimumFormula params range hformulaUnique with
    ⟨inverse, hinverse⟩
  have hgraphValue (value input : LCarrier.{u}) :
      GraphValue LMem inverse value input <->
        value.1 ∈ range.1 /\
          FOFormula.Satisfies LMem inverseMinimumFormula
            ![graph, domain, order, value, input] := by
    constructor
    · rintro ⟨pair, hpairInverse, hpairValue⟩
      rcases (hinverse pair.1).mp hpairInverse with
        ⟨value', hvalue', input', hinput', hpairEq⟩
      have hpairValueRaw :=
        (ContinuumFormula.isKuratowskiPairOf_lCarrier_iff
          pair value input).mp hpairValue
      have hcoordinates := ZFSet.pair_inj.mp
        (hpairEq.symm.trans hpairValueRaw)
      have hvalueEq : value' = value := Subtype.ext hcoordinates.1
      have hinputEq : input' = input := Subtype.ext hcoordinates.2
      subst value'
      subst input'
      exact ⟨hvalue', by
        simpa only [params, order, inverseMinimumAssignment] using hinput'⟩
    · rintro ⟨hvalue, hinput⟩
      let pair := orderedPairLCarrier value input
      refine ⟨pair, ?_, ?_⟩
      · apply (hinverse pair.1).mpr
        refine ⟨value, hvalue, input, ?_, rfl⟩
        simpa only [params, order, inverseMinimumAssignment] using hinput
      · exact (ContinuumFormula.isKuratowskiPairOf_lCarrier_iff
          pair value input).mpr rfl
  refine ⟨inverse, ?_, ?_, ?_⟩
  · intro pair hpairInverse
    rcases (hinverse pair.1).mp hpairInverse with
      ⟨value, hvalue, input, hinputFormula, hpairEq⟩
    have hinput :=
      (satisfies_inverseMinimumFormula
        graph domain order value input).mp (by
          simpa only [params, order, inverseMinimumAssignment] using
            hinputFormula) |>.1
    exact ⟨value, hvalue, input, hinput,
      (ContinuumFormula.isKuratowskiPairOf_lCarrier_iff
        pair value input).mpr hpairEq⟩
  · intro value hvalue
    rcases hformulaUnique value hvalue with
      ⟨input, hinputFormula, hinputUnique⟩
    have hinput :=
      (satisfies_inverseMinimumFormula
        graph domain order value input).mp (by
          simpa only [params, order, inverseMinimumAssignment] using
            hinputFormula) |>.1
    refine ⟨input, hinput, (hgraphValue value input).mpr
      ⟨hvalue, by
        simpa only [params, order, inverseMinimumAssignment] using
          hinputFormula⟩, ?_⟩
    intro other hotherDomain hotherValue
    apply hinputUnique other
    have hotherFormula := (hgraphValue value other).mp hotherValue |>.2
    simpa only [params, order, inverseMinimumAssignment] using hotherFormula
  · intro input hinput value hvalue hvalueInput other hother hotherInput
    have hvalueOriginal : GraphValue LMem graph input value := by
      apply (ContinuumFormula.graphValue_lCarrier_iff_graphRel
        graph input value).mpr
      exact (satisfies_inverseMinimumFormula
        graph domain order value input).mp
          ((hgraphValue value input).mp hvalueInput).2 |>.2.1
    have hotherOriginal : GraphValue LMem graph input other := by
      apply (ContinuumFormula.graphValue_lCarrier_iff_graphRel
        graph input other).mpr
      exact (satisfies_inverseMinimumFormula
        graph domain order other input).mp
          ((hgraphValue other input).mp hotherInput).2 |>.2.1
    exact hfunction.graphValue_unique hinput hvalue hother
      hvalueOriginal hotherOriginal |>.symm

end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_InternalFunctionRangeInjection

/- Source module: Solutions.Work_CUGCH_InternalDefZFInjection -/
section GCHSource_Work_CUGCH_InternalDefZFInjection
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/








/-!
# An internal cardinal bound for `DefZF`

This file internalizes the textbook coding of a definable subset by

`<arity, <prefixGraph, formulaCode>>`.

The candidate triples form a genuine internal set.  Separation retains
exactly the triples that define a section, and Replacement constructs the
actual Kuratowski graph from valid triples to their sections.  The range is
proved extensionally equal to `DefZF a`; no external enumeration or external
cardinal comparison is used as the graph witness.
-/

section

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## The positive-arity reverse bridge -/







namespace ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## One fixed formula for a coded section -/









/-! ## The separated domain of valid codes -/















/-! ## Functionality of the coded-section relation -/





/-! ## Soundness of every represented output -/



/-! ## Completeness of the coded candidates -/



/-! ## Replacement and the genuine internal `DefZF` set -/













/-! ## The internal cardinal injection -/

/-- The separated valid-code domain injects into its full candidate set. -/
private theorem injects_internalDefZFCandidateDomain_container_lCarrier
    (a : LCarrier.{u}) :
    Injects LMem (internalDefZFCandidateDomain a)
      (internalDefZFCandidateContainer a) := by
  apply injects_of_subset_lCarrier
  intro candidate hcandidate
  exact (mem_internalDefZFCandidateDomain_iff
    a candidate).mp hcandidate |>.1

/--
The textbook one-step cardinal bound, represented entirely by internal
Kuratowski graphs:

* `a` injects into `kappa`;
* the internal omega is a subset of `kappa`;
* `kappa x kappa` injects into `kappa`;
* therefore the genuine internally represented `DefZF a` injects into
  `kappa`.
-/
private theorem injects_DefZFLCarrier_lCarrier
    {a kappa : LCarrier.{u}}
    (ha : Injects LMem a kappa)
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa)
    (hsquare : Injects LMem
      (prodLCarrier kappa kappa) kappa) :
    Injects LMem (DefZFLCarrier a) kappa := by
  rcases ha with ⟨aInjection, haInjection⟩
  rcases hsquare with ⟨squareInjection, hsquareInjection⟩
  have hsquare' : Injects LMem
      (prodLCarrier kappa kappa) kappa :=
    ⟨squareInjection, hsquareInjection⟩
  have homegaInjection :
      Injects LMem (omegaLCarrier : LCarrier.{u}) kappa :=
    injects_of_subset_lCarrier homega
  have hfiniteTuples :
      Injects LMem (internalFiniteTupleSpaces a) kappa :=
    injects_internalFiniteTupleSpaces_of_square_lCarrier
      homega haInjection hsquareInjection
  have hprefixCodeProduct :
      Injects LMem
        (prodLCarrier (internalFiniteTupleSpaces a) omegaLCarrier)
        (prodLCarrier kappa kappa) :=
    injects_prod_of_injects_lCarrier
      hfiniteTuples homegaInjection
  have hprefixCode :
      Injects LMem
        (prodLCarrier (internalFiniteTupleSpaces a) omegaLCarrier)
        kappa :=
    hprefixCodeProduct.trans_lCarrier hsquare'
  have hcandidateProduct :
      Injects LMem
        (prodLCarrier omegaLCarrier
          (prodLCarrier (internalFiniteTupleSpaces a) omegaLCarrier))
        (prodLCarrier kappa kappa) :=
    injects_prod_of_injects_lCarrier
      homegaInjection hprefixCode
  have hcontainer :
      Injects LMem (internalDefZFCandidateContainer a) kappa := by
    apply Injects.trans_lCarrier
      (middle := prodLCarrier kappa kappa)
    · simpa only [internalDefZFCandidateContainer] using
        hcandidateProduct
    · exact hsquare'
  have hdomain :
      Injects LMem (internalDefZFCandidateDomain a) kappa :=
    (injects_internalDefZFCandidateDomain_container_lCarrier a).trans_lCarrier
      hcontainer
  let data : InternalDefZFData a := internalDefZFData a
  have hcovered : ∀ output : LCarrier.{u},
      output.1 ∈ data.range.1 →
        ∃ candidate : LCarrier.{u},
          candidate.1 ∈ (internalDefZFCandidateDomain a).1 ∧
            GraphValue LMem data.graph candidate output := by
    intro output houtput
    rcases (data.mem_range_iff output).mp houtput with
      ⟨candidate, hcandidate, hformula⟩
    exact ⟨candidate, hcandidate,
      (data.graphValue_iff candidate output).mpr
        ⟨hcandidate, hformula⟩⟩
  have hrangeDomain :
      Injects LMem data.range (internalDefZFCandidateDomain a) :=
    Model.injects_range_into_domain_of_functionGraph
      data.graph (internalDefZFCandidateDomain a) data.range
      data.isFunctionGraph hcovered
  have hrangeKappa : Injects LMem data.range kappa :=
    hrangeDomain.trans_lCarrier hdomain
  simpa only [DefZFLCarrier, data] using hrangeKappa



end ContinuumFormula

end

end Constructible

end
end GCHSource_Work_CUGCH_InternalDefZFInjection

/- Source module: Solutions.Work_CUGCH_InternalLStageInjection -/
section GCHSource_Work_CUGCH_InternalLStageInjection
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Internal cardinal bounds for constructible stages

This file carries out the standard transfinite induction below the Hartogs
ordinal of an internal infinite cardinal.

* The zero stage is empty.
* At a successor, the previous-stage injection and the internal square
  absorption are passed to the genuine `DefZF` injection.
* At a nonzero limit, Replacement collects the earlier injection graphs.
  The canonical least-containing-stage selector injects the union into
  `limit x kappa`; Hartogs supplies `limit -> kappa`, and the internal square
  injection absorbs the product.

No externally indexed family is used as the graph witness at a limit.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/--
Every constructible stage strictly below the Hartogs ordinal of an internal
infinite cardinal internally injects into that cardinal.
-/
private theorem injects_stageLCarrier_below_internalHartogs_lCarrier
    (kappa : LCarrier.{u})
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa) :
    ∀ ordinal : Ordinal.{u},
      ordinal < internalHartogsOrdinal kappa →
        Injects LMem (stageLCarrier ordinal) kappa := by
  have hsquare :
      Injects LMem (prodLCarrier kappa kappa) kappa :=
    injects_infiniteCardinalSquare_lCarrier hcardinal homega
  have hhartogs :=
    internalHartogsLCarrier_isHartogsNumber kappa
  intro ordinal
  induction ordinal using Ordinal.limitRecOn with
  | zero =>
      intro _hzero
      apply injects_of_subset_lCarrier
      intro x hx
      change x.1 ∈ LStageZF (0 : Ordinal.{u}) at hx
      rw [LStageZF_zero] at hx
      exact (ZFSet.notMem_empty x.1 hx).elim
  | add_one ordinal ih =>
      intro hsuccessor
      have hordinal :
          ordinal < internalHartogsOrdinal kappa :=
        (Order.lt_succ ordinal).trans hsuccessor
      have hprevious :
          Injects LMem (stageLCarrier ordinal) kappa :=
        ih hordinal
      have hdef :
          Injects LMem (DefZFLCarrier (stageLCarrier ordinal)) kappa :=
        injects_DefZFLCarrier_lCarrier hprevious homega hsquare
      have hdomain :
          stageLCarrier (Order.succ ordinal) =
            DefZFLCarrier (stageLCarrier ordinal) := by
        apply Subtype.ext
        simp only [stageLCarrier_val, LStageZF_succ,
          DefZFLCarrier_val]
      rw [← Order.succ_eq_add_one, hdomain]
      exact hdef
  | limit limit hlimit ih =>
      intro hlimitHartogs
      have hpointwise : ∀ earlier : Ordinal.{u}, earlier < limit →
          Injects LMem (stageLCarrier earlier) kappa := by
        intro earlier hearlier
        exact ih earlier hearlier
          (hearlier.trans hlimitHartogs)
      rcases exists_canonicalStageInjectionFamily
          limit kappa hpointwise with
        ⟨injectionFamily, graphFamily, hinjectionFamily, hinjections⟩
      have hlimitProduct :
          Injects LMem (stageLCarrier limit)
            (prodLCarrier (ordinalLCarrier limit) kappa) :=
        injects_limitStage_to_prod_of_internalInjectionFamily
          hlimit hinjectionFamily hinjections
      have hlimitMem :
          (ordinalLCarrier limit).1 ∈
            (internalHartogsLCarrier kappa).1 := by
        change (ordinalLCarrier limit).1 ∈
          (ordinalLCarrier
            (internalHartogsOrdinal kappa)).1
        exact (ordinalLCarrier_mem_ordinalLCarrier_iff
          (internalHartogsOrdinal kappa) limit).mpr
            hlimitHartogs
      have hlimitKappa :
          Injects LMem (ordinalLCarrier limit) kappa :=
        hhartogs.2.2 (ordinalLCarrier limit) hlimitMem
      have hproduct :
          Injects LMem
            (prodLCarrier (ordinalLCarrier limit) kappa)
            (prodLCarrier kappa kappa) :=
        injects_prod_of_injects_lCarrier hlimitKappa
          (injects_refl_lCarrier kappa)
      exact hlimitProduct.trans_lCarrier
        (hproduct.trans_lCarrier hsquare)

/--
The full Hartogs-stage bound required by the condensation-to-GCH argument.
-/
private theorem hartogsStageBound_lCarrier_gchProof09
    (kappa : LCarrier.{u})
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa) :
    HartogsStageBound kappa :=
  hartogsStageBound_of_pointwise_stage_injects
    kappa hcardinal homega
      (injects_stageLCarrier_below_internalHartogs_lCarrier
        kappa hcardinal homega)

end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalLStageInjection

universe u

theorem solution : ∀ (kappa : Constructible.Model.LCarrier.{u}),
  @Constructible.ContinuumFormula.IsCardinal.{u + 1} Constructible.Model.LCarrier.{u}
      Constructible.Model.lCarrierMem.{u} kappa →
    @Constructible.ContinuumFormula.IsSubsetOf.{u + 1} Constructible.Model.LCarrier.{u}
        Constructible.Model.lCarrierMem.{u} Constructible.Model.omegaLCarrier.{u} kappa →
      Constructible.ContinuumFormula.HartogsStageBound.{u} kappa :=
  @Constructible.ContinuumFormula.hartogsStageBound_lCarrier_gchProof09.{u}
