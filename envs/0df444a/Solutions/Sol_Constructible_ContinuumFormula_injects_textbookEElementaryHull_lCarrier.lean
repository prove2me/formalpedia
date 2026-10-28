-- Prove2me | solution 1 for Constructible.ContinuumFormula.injects_textbookEElementaryHull_lCarrier
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T00:27:39.504991+00:00
-- url     : https://prove2.me/submissions/95ef537e-ab95-48a9-a045-775b38d1a7c0

import Definitions.Def_CH_ConstructibleGCH_HullIteration
import Theorems.Thm_Constructible_ContinuumFormula_injects_infiniteCardinalSquare_lCarrier
import Theorems.Thm_Constructible_ContinuumFormula_injects_textbookEUniformWitnessStage_lCarrier

/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 2000000

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

/- Source module: Solutions.Work_CUGCH_InternalInfiniteCardinalAbsorption -/
section GCHSource_Work_CUGCH_InternalInfiniteCardinalAbsorption
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Finite absorption by an internally infinite constructible set

This file carries out the standard Hilbert-hotel argument with actual graphs
belonging to `L`.  If `omega` is a subset of a constructible set `kappa`, the
definable map which shifts the natural numbers and fixes every other element
is an internal injection `kappa -> kappa` whose range omits the empty set.
Consequently an internal injection into `kappa` can be extended over one
fresh point.

No ambient function or cardinal comparison is used as an internal witness.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## The internal omega shift -/







/-- The successor of a member of the standard omega is again in omega. -/
private theorem successorLCarrier_mem_omegaLCarrier
    (x : LCarrier.{u}) (hx : x.1 ∈ omegaLCarrier.1) :
    (successorLCarrier x).1 ∈ omegaLCarrier.1 :=
  Constructible.Model.omegaLCarrier_isInductiveSet.2 x hx

/-- The omega shift takes members of any `kappa` containing omega back into
`kappa`. -/
private theorem OmegaShift.mem_of_omega_subset
    {kappa x y : LCarrier.{u}}
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hx : x.1 ∈ kappa.1) (hshift : OmegaShift x y) :
    y.1 ∈ kappa.1 := by
  rcases hshift with hnat | hfixed
  · rw [hnat.2]
    exact homega _ (successorLCarrier_mem_omegaLCarrier x hnat.1)
  · simpa only [hfixed.2] using hx

/-- The omega shift is a genuine injection. -/
private theorem OmegaShift.injective
    {x y z : LCarrier.{u}}
    (hxy : OmegaShift x y) (hzy : OmegaShift z y) :
    z = x := by
  rcases hxy with hxn | hxf <;> rcases hzy with hzn | hzf
  · have hsucc : successorLCarrier x = successorLCarrier z :=
      hxn.2.symm.trans hzn.2
    apply Subtype.ext
    apply insert_self_injective
    exact (congrArg Subtype.val hsucc).symm
  · have hyOmega : y.1 ∈ omegaLCarrier.1 := by
      rw [hxn.2]
      exact successorLCarrier_mem_omegaLCarrier x hxn.1
    rw [hzf.2] at hyOmega
    exact (hzf.1 hyOmega).elim
  · have hyOmega : y.1 ∈ omegaLCarrier.1 := by
      rw [hzn.2]
      exact successorLCarrier_mem_omegaLCarrier z hzn.1
    rw [hxf.2] at hyOmega
    exact (hxf.1 hyOmega).elim
  · exact hzf.2.symm.trans hxf.2

/-- The empty set is omitted by the omega shift. -/
private theorem OmegaShift.ne_emptyLCarrier
    {x : LCarrier.{u}} : ¬ OmegaShift x emptyLCarrier := by
  intro hshift
  rcases hshift with hnat | hfixed
  · have hxMemSucc : x.1 ∈ (successorLCarrier x).1 := by
      rw [successorLCarrier_val, ZFSet.mem_insert_iff]
      exact Or.inl rfl
    rw [← hnat.2] at hxMemSucc
    exact not_mem_emptyLCarrier x hxMemSucc
  · apply hfixed.1
    rw [← hfixed.2]
    exact empty_mem_omegaLCarrier

/-- Separation produces the internal omega-shift graph on `kappa`.  The
result records both its exact value semantics and the omitted empty value. -/
private theorem exists_omegaShiftInjection_lCarrier
    (kappa : LCarrier.{u})
    (homega : IsSubsetOf LMem omegaLCarrier kappa) :
    ∃ graph : LCarrier.{u},
      IsInjection LMem graph kappa kappa ∧
        (∀ x y : LCarrier.{u},
          GraphValue LMem graph x y ↔
            x.1 ∈ kappa.1 ∧ OmegaShift x y) ∧
          ∀ x : LCarrier.{u},
            ¬GraphValue LMem graph x emptyLCarrier := by
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      omegaShiftFormula ![omegaLCarrier] kappa with
    ⟨graph, hsupport, hrelation⟩
  have hvalue : ∀ x y : LCarrier.{u},
      GraphValue LMem graph x y ↔
        x.1 ∈ kappa.1 ∧ OmegaShift x y := by
    intro x y
    rw [graphValue_lCarrier_iff_graphRel, hrelation]
    constructor
    · rintro ⟨hx, _hy, hformula⟩
      exact ⟨hx,
        (satisfies_omegaShiftFormula omegaLCarrier x y).mp hformula⟩
    · rintro ⟨hx, hshift⟩
      exact ⟨hx, hshift.mem_of_omega_subset homega hx,
        (satisfies_omegaShiftFormula omegaLCarrier x y).mpr hshift⟩
  have hbetween : IsGraphBetween LMem graph kappa kappa := by
    intro pair hpair
    rcases hsupport pair hpair with
      ⟨x, y, hx, hy, hpairEq, _hformula⟩
    exact ⟨x, hx, y, hy,
      (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq⟩
  have hinjection : IsInjection LMem graph kappa kappa := by
    refine ⟨hbetween, ?_, ?_⟩
    · intro x hx
      by_cases hnat : x.1 ∈ omegaLCarrier.1
      · let y := successorLCarrier x
        have hshift : OmegaShift x y := Or.inl ⟨hnat, rfl⟩
        refine ⟨y, hshift.mem_of_omega_subset homega hx,
          (hvalue x y).mpr ⟨hx, hshift⟩, ?_⟩
        intro z _hz hzValue
        rcases (hvalue x z).mp hzValue with ⟨_hx, hzShift⟩
        rcases hzShift with hsucc | hfixed
        · exact hsucc.2
        · exact (hfixed.1 hnat).elim
      · refine ⟨x, hx,
          (hvalue x x).mpr ⟨hx, Or.inr ⟨hnat, rfl⟩⟩, ?_⟩
        intro z _hz hzValue
        rcases (hvalue x z).mp hzValue with ⟨_hx, hzShift⟩
        rcases hzShift with hsucc | hfixed
        · exact (hnat hsucc.1).elim
        · exact hfixed.2
    · intro y _hy x hx hxy z hz hzy
      exact OmegaShift.injective (hvalue x y |>.mp hxy).2
        (hvalue z y |>.mp hzy).2
  refine ⟨graph, hinjection, hvalue, ?_⟩
  intro x hxEmpty
  exact OmegaShift.ne_emptyLCarrier (hvalue x emptyLCarrier |>.mp hxEmpty).2

/-! ## Composition and adjoining a fresh point -/







/-- The composition graph constructed by Separation carries the composite
injection, together with its exact graph-value semantics. -/
private theorem exists_compositionInjection_lCarrier
    {first second domain middle codomain : LCarrier.{u}}
    (hfirst : IsInjection LMem first domain middle)
    (hsecond : IsInjection LMem second middle codomain) :
    ∃ graph : LCarrier.{u},
      IsInjection LMem graph domain codomain ∧
        ∀ x y : LCarrier.{u},
          GraphValue LMem graph x y ↔
            ∃ z : LCarrier.{u},
              GraphValue LMem first x z ∧
                GraphValue LMem second z y := by
  rcases exists_compositionGraph_lCarrier hfirst.1 hsecond.1 with
    ⟨graph, hbetween, hvalue⟩
  have hinjection : IsInjection LMem graph domain codomain := by
    refine ⟨hbetween, ?_, ?_⟩
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
  exact ⟨graph, hinjection, hvalue⟩

/-- Inserting one new graph value extends an injection across a fresh point,
provided the new value was omitted by the old graph. -/
private theorem IsInjection.insert_fresh_lCarrier
    {graph domain codomain point value : LCarrier.{u}}
    (hgraph : IsInjection LMem graph domain codomain)
    (hpoint : point.1 ∉ domain.1)
    (hvalue : value.1 ∈ codomain.1)
    (homit : ∀ x : LCarrier.{u},
      ¬GraphValue LMem graph x value) :
    IsInjection LMem
      (Constructible.Model.insertGraphValue graph point value)
      (adjoinLCarrier domain point) codomain := by
  have hbetween : IsGraphBetween LMem
      (Constructible.Model.insertGraphValue graph point value)
      (adjoinLCarrier domain point) codomain := by
    intro pair hpair
    rcases (Constructible.Model.mem_insertGraphValue_iff
      graph point value pair).mp hpair with hnew | hold
    · subst pair
      exact ⟨point,
        (mem_adjoinLCarrier_iff domain point point).mpr (Or.inl rfl),
        value, hvalue,
        (isKuratowskiPairOf_lCarrier_iff
          (orderedPairLCarrier point value) point value).mpr rfl⟩
    · rcases hgraph.1 pair hold with ⟨x, hx, y, hy, hpairXY⟩
      exact ⟨x,
        (mem_adjoinLCarrier_iff domain point x).mpr (Or.inr hx),
        y, hy, hpairXY⟩
  refine ⟨hbetween, ?_, ?_⟩
  · intro x hx
    rcases (mem_adjoinLCarrier_iff domain point x).mp hx with
      hnew | hold
    · subst x
      refine ⟨value, hvalue,
        (Constructible.Model.graphValue_insertGraphValue_iff
          graph point value point value).mpr
            (Or.inr ⟨rfl, rfl⟩), ?_⟩
      intro z _hz hzGraph
      rcases (Constructible.Model.graphValue_insertGraphValue_iff
        graph point value point z).mp hzGraph with hold | hnew
      · have hpointDomain :=
          (hgraph.1.graphValue_mem_lCarrier hold).1
        exact (hpoint hpointDomain).elim
      · exact hnew.2
    · rcases hgraph.2.1 x hold with ⟨y, hy, hxy, hyUnique⟩
      refine ⟨y, hy,
        (Constructible.Model.graphValue_insertGraphValue_iff
          graph point value x y).mpr (Or.inl hxy), ?_⟩
      intro z hz hxz
      rcases (Constructible.Model.graphValue_insertGraphValue_iff
        graph point value x z).mp hxz with holdValue | hnew
      · exact hyUnique z hz holdValue
      · have hpointDomain : point.1 ∈ domain.1 := by
          rw [← hnew.1]
          exact hold
        exact (hpoint hpointDomain).elim
  · intro y hy x _hx hxy z _hz hzy
    rcases (Constructible.Model.graphValue_insertGraphValue_iff
      graph point value x y).mp hxy with hxyOld | hxyNew <;>
      rcases (Constructible.Model.graphValue_insertGraphValue_iff
        graph point value z y).mp hzy with hzyOld | hzyNew
    · have hxDomain := (hgraph.1.graphValue_mem_lCarrier hxyOld).1
      have hzDomain := (hgraph.1.graphValue_mem_lCarrier hzyOld).1
      exact hgraph.2.2 y hy x hxDomain hxyOld z hzDomain hzyOld
    · have hxyValue : GraphValue LMem graph x value := by
        rw [← hzyNew.2]
        exact hxyOld
      exact (homit x hxyValue).elim
    · have hzyValue : GraphValue LMem graph z value := by
        rw [← hxyNew.2]
        exact hzyOld
      exact (homit z hzyValue).elim
    · exact hzyNew.1.trans hxyNew.1.symm

/-- If `kappa` contains omega, any internal injection `domain -> kappa`
extends to `domain union {point}` when `point` is fresh. -/
private theorem injects_adjoin_fresh_of_omega_subset_lCarrier
    {domain kappa point : LCarrier.{u}}
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hpoint : point.1 ∉ domain.1)
    (hinjects : Injects LMem domain kappa) :
    Injects LMem (adjoinLCarrier domain point) kappa := by
  rcases hinjects with ⟨first, hfirst⟩
  rcases exists_omegaShiftInjection_lCarrier kappa homega with
    ⟨shift, hshift, _hshiftValue, hshiftOmits⟩
  rcases exists_compositionInjection_lCarrier hfirst hshift with
    ⟨composite, hcomposite, hcompositeValue⟩
  have hcompositeOmits : ∀ x : LCarrier.{u},
      ¬GraphValue LMem composite x emptyLCarrier := by
    intro x hxEmpty
    rcases (hcompositeValue x emptyLCarrier).mp hxEmpty with
      ⟨middle, _hxMiddle, hmiddleEmpty⟩
    exact hshiftOmits middle hmiddleEmpty
  exact ⟨Constructible.Model.insertGraphValue
      composite point emptyLCarrier,
    hcomposite.insert_fresh_lCarrier hpoint
      (homega emptyLCarrier empty_mem_omegaLCarrier)
      hcompositeOmits⟩





end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalInfiniteCardinalAbsorption

/- Source module: Solutions.Work_CUGCH_ParametricUniformOmegaFamily -/
section GCHSource_Work_CUGCH_ParametricUniformOmegaFamily
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Parameterized internal omega families

This is the parameterized form of `UniformOmegaFamilySpec`.  A fixed tuple of
constructible parameters is passed to one object-language formula with layout
`[params,index,value]`.  Replacement over the actual internal omega produces
both the represented function graph and its range, and internal union then
collects all stages.
-/

section

universe u

namespace Constructible.Model

open Constructible.ContinuumFormula
open Constructible.FiniteSequenceZF

noncomputable section

local notation "LMem" => lCarrierMem













private theorem value_subset_parametricUniformOmegaUnion
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (n : Nat) :
    (spec.value n).1 ⊆ (parametricUniformOmegaUnion spec).1 := by
  intro z hz
  let zL : LCarrier.{u} :=
    ⟨z, mem_L_of_mem hz (spec.value n).2⟩
  exact (mem_parametricUniformOmegaUnion_iff spec zL).mpr ⟨n, hz⟩

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_ParametricUniformOmegaFamily

/- Source module: Solutions.Work_CUGCH_ParametricUniformOmegaSelector -/
section GCHSource_Work_CUGCH_ParametricUniformOmegaSelector
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# The least-stage selector for a uniform omega family

For an internally represented omega-indexed family, this file constructs the
actual Kuratowski graph which sends an element of the union to the least
natural-number index of a family member containing it.  The graph is obtained
by Separation from one fixed first-order formula.  External minimization on
`Nat` is used only to prove totality and uniqueness of that internal graph.
-/

section

universe u

namespace Constructible.Model

open Constructible.ContinuumFormula
open Constructible.FiniteSequenceZF

noncomputable section

local notation "LMem" => lCarrierMem



















private theorem canonical_family_value
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (n : Nat) :
    GraphValue LMem (parametricUniformOmegaFamilyData spec).graph
      (natLCarrier n) (spec.value n) := by
  apply ((parametricUniformOmegaFamilyData spec).graphValue_iff
    (natLCarrier n) (spec.value n)).mpr
  constructor
  · change (natCode n : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode n)).mpr ⟨n, rfl⟩
  · exact (spec.realizes n (spec.value n)).mpr rfl

private theorem value_eq_of_family_graphValue
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    {index fiber : LCarrier.{u}} (hindex : index.1 ∈ omegaLCarrier.1)
    (hvalue : GraphValue LMem
      (parametricUniformOmegaFamilyData spec).graph index fiber) :
    exists n : Nat, index = natLCarrier n /\ fiber = spec.value n := by
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
      hindex with ⟨n, hindexCode⟩
  have hindexEq : index = natLCarrier n := Subtype.ext hindexCode
  subst index
  have hfiberFamily :=
    (parametricUniformOmegaFamilyData spec).isFunctionGraph.1
      |>.graphValue_mem_lCarrier hvalue |>.2
  have hcanonicalFamily :=
    (parametricUniformOmegaFamilyData spec).isFunctionGraph.1
      |>.graphValue_mem_lCarrier (canonical_family_value spec n) |>.2
  have hfiberEq :=
    (parametricUniformOmegaFamilyData spec).isFunctionGraph.graphValue_unique
      (by
        change (natCode n : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet
        exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode n)).mpr ⟨n, rfl⟩)
      hfiberFamily hcanonicalFamily hvalue (canonical_family_value spec n)
  exact ⟨n, rfl, hfiberEq⟩

/-- The least-index graph is a total internally represented function from
the omega union into the internal natural numbers. -/
private theorem parametricUniformOmegaSelectorGraph_isFunctionGraph
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount) :
    IsFunctionGraph LMem (parametricUniformOmegaSelectorGraph spec)
      (parametricUniformOmegaUnion spec) omegaLCarrier := by
  classical
  constructor
  · intro pair hpair
    rcases (mem_canonicalDefinableRelationGraph_iff
        leastUniformOmegaFamilyIndexFormula
        ![(parametricUniformOmegaFamilyData spec).graph, omegaLCarrier]
        (parametricUniformOmegaSelectorSupport spec) pair).mp hpair with
      ⟨element, index, _helementSupport, _hindexSupport,
        hpairEq, hformula⟩
    rw [least_index_assignment,
      satisfies_leastUniformOmegaFamilyIndexFormula] at hformula
    have hgraph :=
      (graphValue_parametricUniformOmegaSelectorGraph_iff
        spec element index).mpr ⟨?_, hformula⟩
    · exact ⟨element,
        (graphValue_parametricUniformOmegaSelectorGraph_iff
          spec element index).mp hgraph |>.1,
        index, hformula.1,
        (isKuratowskiPairOf_lCarrier_iff pair element index).mpr hpairEq⟩
    · rcases hformula.2.1 with ⟨fiber, hvalue, helement⟩
      have hfiberFamily :=
        (parametricUniformOmegaFamilyData spec).isFunctionGraph.1
          |>.graphValue_mem_lCarrier hvalue |>.2
      rcases (parametricUniformOmegaFamilyData spec).mem_family_iff fiber |>.mp
          hfiberFamily with ⟨n, rfl⟩
      exact (mem_parametricUniformOmegaUnion_iff spec element).mpr
        ⟨n, helement⟩
  · intro element helement
    have hexists : exists n : Nat, element.1 ∈ (spec.value n).1 :=
      (mem_parametricUniformOmegaUnion_iff spec element).mp helement
    let first : Nat := Nat.find hexists
    have hfirst : element.1 ∈ (spec.value first).1 := Nat.find_spec hexists
    let index := natLCarrier first
    have hindexOmega : index.1 ∈ omegaLCarrier.1 := by
      change (natCode first : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode first)).mpr ⟨first, rfl⟩
    have hcontains : exists fiber : LCarrier.{u},
        GraphValue LMem (parametricUniformOmegaFamilyData spec).graph
          index fiber /\ element.1 ∈ fiber.1 :=
      ⟨spec.value first, canonical_family_value spec first, hfirst⟩
    have hminimal : forall earlier : LCarrier.{u},
        earlier.1 ∈ index.1 ->
          Not (exists fiber : LCarrier.{u},
            GraphValue LMem (parametricUniformOmegaFamilyData spec).graph
              earlier fiber /\ element.1 ∈ fiber.1) := by
      intro earlier hearlier
      rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt
        earlier.1 first).mp hearlier with ⟨j, hj, hearlierCode⟩
      rintro ⟨fiber, hvalue, helementFiber⟩
      have hearlierOmega : earlier.1 ∈ omegaLCarrier.1 := by
        change earlier.1 ∈ Ordinal.omega0.toZFSet
        rw [hearlierCode]
        exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode j)).mpr ⟨j, rfl⟩
      rcases value_eq_of_family_graphValue spec hearlierOmega hvalue with
        ⟨k, hearlierEq, hfiberEq⟩
      have hjk : j = k := by
        apply natCode_injective
        exact hearlierCode.symm.trans (congrArg Subtype.val hearlierEq)
      subst k
      rw [hfiberEq] at helementFiber
      exact (Nat.not_lt_of_ge (Nat.find_min' hexists helementFiber)) hj
    have hleast : IsLeastUniformOmegaFamilyIndex
        (parametricUniformOmegaFamilyData spec).graph
        omegaLCarrier element index :=
      ⟨hindexOmega, hcontains, hminimal⟩
    refine ⟨index, hindexOmega,
      (graphValue_parametricUniformOmegaSelectorGraph_iff
        spec element index).mpr ⟨helement, hleast⟩, ?_⟩
    intro other hotherOmega hotherGraph
    have hotherLeast :=
      (graphValue_parametricUniformOmegaSelectorGraph_iff
        spec element other).mp hotherGraph |>.2
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode other.1).mp
        hotherOmega with ⟨m, hotherCode⟩
    have hotherEq : other = natLCarrier m := Subtype.ext hotherCode
    subst other
    rcases hotherLeast.2.1 with ⟨fiber, hfamilyValue, helementFiber⟩
    rcases value_eq_of_family_graphValue spec hotherLeast.1 hfamilyValue with
      ⟨k, hindexEq, hfiberEq⟩
    have hmk : m = k := by
      apply natCode_injective
      exact congrArg Subtype.val hindexEq
    subst k
    rw [hfiberEq] at helementFiber
    have hfirstLe : first <= m := Nat.find_min' hexists helementFiber
    have hmLe : m <= first := by
      by_contra hnot
      have hfirstLt : first < m := Nat.lt_of_not_ge hnot
      have hfirstMem :
          (natLCarrier first).1 ∈ (natLCarrier m).1 :=
        (IndexedSequenceZF.mem_natCode_iff_exists_lt
          (natCode first) m).mpr ⟨first, hfirstLt, rfl⟩
      exact (hotherLeast.2.2 (natLCarrier first) hfirstMem)
        ⟨spec.value first, canonical_family_value spec first, hfirst⟩
    exact congrArg natLCarrier (Nat.le_antisymm hmLe hfirstLe)

/-- The canonical least-index graph supplies exactly the selector contract
used by the internal cardinal-union construction. -/
private theorem parametricUniformOmegaSelectorGraph_selectsContainingFiber
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount) :
    SelectsContainingFiber LMem
      (parametricUniformOmegaSelectorGraph spec)
      (parametricUniformOmegaUnion spec) omegaLCarrier
      (parametricUniformOmegaFamilyData spec).graph := by
  constructor
  · exact parametricUniformOmegaSelectorGraph_isFunctionGraph spec
  · intro element index helement hselect
    have hleast :=
      (graphValue_parametricUniformOmegaSelectorGraph_iff
        spec element index).mp hselect |>.2
    exact hleast.2.1

/-- An internally collected family of stage injections combines to an
injection of the whole omega union into `omega x kappa`. -/
private theorem injects_parametricUniformOmegaUnion_to_prod_of_injectionFamily
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    {kappa injectionFamily graphFamily : LCarrier.{u}}
    (hinjectionFamily : IsFunctionGraph LMem injectionFamily
      omegaLCarrier graphFamily)
    (hinjections : forall n : Nat, forall injection : LCarrier.{u},
      GraphValue LMem injectionFamily (natLCarrier n) injection ->
        IsInjection LMem injection (spec.value n) kappa) :
    Injects LMem (parametricUniformOmegaUnion spec)
      (prodLCarrier omegaLCarrier kappa) := by
  have hfibers : IsFiberInjectionFamily LMem
      (parametricUniformOmegaFamilyData spec).graph
      injectionFamily omegaLCarrier
      (parametricUniformOmegaFamilyData spec).family
      graphFamily kappa := by
    refine ⟨(parametricUniformOmegaFamilyData spec).isFunctionGraph,
      hinjectionFamily, ?_⟩
    intro index fiber injection hindex hfiber hinjection
    rcases value_eq_of_family_graphValue spec hindex hfiber with
      ⟨n, hindexEq, hfiberEq⟩
    subst index
    subst fiber
    exact hinjections n injection hinjection
  have hinjects := injects_sUnion_to_prod_lCarrier
    (parametricUniformOmegaSelectorGraph_selectsContainingFiber spec)
    hfibers
  simpa only [parametricUniformOmegaUnion] using hinjects

/-- If `kappa` contains omega and absorbs its square, the internally
collected omega union is bounded by `kappa`. -/
private theorem injects_parametricUniformOmegaUnion_of_injectionFamily
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    {kappa injectionFamily graphFamily : LCarrier.{u}}
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hsquare : Injects LMem (prodLCarrier kappa kappa) kappa)
    (hinjectionFamily : IsFunctionGraph LMem injectionFamily
      omegaLCarrier graphFamily)
    (hinjections : forall n : Nat, forall injection : LCarrier.{u},
      GraphValue LMem injectionFamily (natLCarrier n) injection ->
        IsInjection LMem injection (spec.value n) kappa) :
    Injects LMem (parametricUniformOmegaUnion spec) kappa := by
  have homegaInjection : Injects LMem omegaLCarrier kappa :=
    injects_of_subset_lCarrier homega
  have hkappaInjection : Injects LMem kappa kappa :=
    injects_refl_lCarrier kappa
  have hproduct : Injects LMem
      (prodLCarrier omegaLCarrier kappa)
      (prodLCarrier kappa kappa) :=
    injects_prod_of_injects_lCarrier homegaInjection hkappaInjection
  exact (injects_parametricUniformOmegaUnion_to_prod_of_injectionFamily
    spec hinjectionFamily hinjections).trans_lCarrier
      (hproduct.trans_lCarrier hsquare)

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_ParametricUniformOmegaSelector

/- Source module: Solutions.Work_CUGCH_ParametricUniformOmegaInjectionFamily -/
section GCHSource_Work_CUGCH_ParametricUniformOmegaInjectionFamily
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Canonically collecting injections along a uniform omega family

Suppose every value of a uniformly definable omega family has some internally
represented injection into `kappa`.  This file does not externally choose
those graphs.  It bounds all candidate graphs by the genuine internal
powerset of `H x kappa`, selects the least candidate in the canonical stage
order by one fixed first-order formula, and applies Replacement over the
internal omega.  The result is the actual indexed family of injection graphs
needed by the cardinal-union argument.
-/

section

universe u

namespace Constructible.Model

open Constructible.ContinuumFormula
open Constructible.FiniteSequenceZF

noncomputable section

local notation "LMem" => lCarrierMem







/-! ## Candidate sets for the minimum argument -/









/-! ## The fixed formula selecting the canonical graph -/





















/-! ## Existence, uniqueness, and Replacement -/

private theorem injection_graph_mem_power
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa : LCarrier.{u}) (n : Nat)
    {graph : LCarrier.{u}}
    (hgraph : IsInjection LMem graph (spec.value n) kappa) :
    graph.1 ∈ (parametricUniformOmegaInjectionPower spec kappa).1 := by
  apply (mem_parametricUniformOmegaInjectionPower_iff
    spec kappa graph).mpr
  intro pairRaw hpair
  let pair : LCarrier.{u} :=
    ⟨pairRaw, mem_L_of_mem hpair graph.2⟩
  have hbetween := hgraph.1 pair hpair
  rcases hbetween with ⟨input, hinput, output, houtput, hpairs⟩
  have hinputUnion := value_subset_parametricUniformOmegaUnion spec n hinput
  apply ZFSet.mem_prod.mpr
  exact ⟨input.1, hinputUnion, output.1, houtput,
    (isKuratowskiPairOf_lCarrier_iff pair input output).mp hpairs⟩

/-- If the displayed family value has an internal injection, the fixed
formula has exactly one output: the canonical least such graph. -/
private theorem canonicalUniformOmegaInjectionFormula_existsUnique
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa : LCarrier.{u}) (n : Nat)
    (hinjects : Injects LMem (spec.value n) kappa) :
    ExistsUnique fun injection : LCarrier.{u} =>
      FOFormula.Satisfies LMem
        (canonicalUniformOmegaInjectionFormula spec.formula)
        (snoc
          (snoc (canonicalUniformOmegaInjectionParams spec kappa)
            (natLCarrier n))
          injection) := by
  let stage := spec.value n
  let power := parametricUniformOmegaInjectionPower spec kappa
  let candidates := uniformOmegaInjectionCandidates spec kappa stage
  have hcandidatesSubset : forall graph : LCarrier.{u},
      graph.1 ∈ candidates.1 ->
        graph.1 ∈ (canonicalWitnessStage power).1 := by
    intro graph hgraph
    exact seed_subset_canonicalWitnessStage power
      ((mem_uniformOmegaInjectionCandidates_iff
        spec kappa stage graph).mp hgraph).1
  have hcandidatesNonempty : exists graph : LCarrier.{u},
      graph.1 ∈ candidates.1 := by
    rcases hinjects with ⟨graph, hgraph⟩
    exact ⟨graph, (mem_uniformOmegaInjectionCandidates_iff
      spec kappa stage graph).mpr
        ⟨injection_graph_mem_power spec kappa n hgraph, hgraph⟩⟩
  rcases exists_unique_graph_minimum
      (canonicalWitnessOrder_internallyWellOrders power)
      hcandidatesSubset hcandidatesNonempty with
    ⟨minimum, hminimum, hminimumUnique⟩
  refine ⟨minimum, ?_, ?_⟩
  · apply (satisfies_canonicalUniformOmegaInjectionFormula
      spec kappa (natLCarrier n) minimum).mpr
    refine ⟨stage, (spec.realizes n stage).mpr rfl, ?_⟩
    have hcandidate := (mem_uniformOmegaInjectionCandidates_iff
      spec kappa stage minimum).mp hminimum.1
    exact ⟨hcandidate.1, hcandidate.2, fun other hotherPower hotherInjection =>
      hminimum.2 other
        ((mem_uniformOmegaInjectionCandidates_iff
          spec kappa stage other).mpr
            ⟨hotherPower, hotherInjection⟩)⟩
  · intro other hother
    have hotherSemantic :=
      (satisfies_canonicalUniformOmegaInjectionFormula
        spec kappa (natLCarrier n) other).mp hother
    rcases hotherSemantic with
      ⟨otherStage, hotherStage, hotherPower,
        hotherInjection, hotherMinimal⟩
    have hotherStageEq : otherStage = stage :=
      (spec.realizes n otherStage).mp hotherStage
    subst otherStage
    apply hminimumUnique other
    exact ⟨(mem_uniformOmegaInjectionCandidates_iff
        spec kappa stage other).mpr
          ⟨hotherPower, hotherInjection⟩,
      fun z hz =>
        hotherMinimal z
          ((mem_uniformOmegaInjectionCandidates_iff
            spec kappa stage z).mp hz).1
          ((mem_uniformOmegaInjectionCandidates_iff
            spec kappa stage z).mp hz).2⟩



/-- Replacement produces the genuine family graph from pointwise internal
injections. -/
private theorem exists_parametricUniformOmegaInjectionFamilyData
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa : LCarrier.{u})
    (hinjects : forall n : Nat, Injects LMem (spec.value n) kappa) :
    Nonempty (ParametricUniformOmegaInjectionFamilyData spec kappa) := by
  let params := canonicalUniformOmegaInjectionParams spec kappa
  have hfun : forall index : LCarrier.{u}, index.1 ∈ omegaLCarrier.1 ->
      ExistsUnique fun injection : LCarrier.{u} =>
        FOFormula.Satisfies LMem
          (canonicalUniformOmegaInjectionFormula spec.formula)
          (snoc (snoc params index) injection) := by
    intro index hindex
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
        hindex with ⟨n, hindexCode⟩
    have hindexEq : index = natLCarrier n := Subtype.ext hindexCode
    subst index
    simpa only [params] using
      canonicalUniformOmegaInjectionFormula_existsUnique
        spec kappa n (hinjects n)
  rcases exists_replacementFunctionGraphAndRangeLCarrier
      (canonicalUniformOmegaInjectionFormula spec.formula)
      params omegaLCarrier hfun with
    ⟨injectionFamily, graphFamily, hfamily, _hrange, hvalue⟩
  refine ⟨{
    injectionFamily := injectionFamily
    graphFamily := graphFamily
    isFunctionGraph := hfamily
    values_areInjections := ?_
  }⟩
  intro n injection hinjection
  have hformula := (hvalue (natLCarrier n) injection).mp hinjection |>.2
  have hsemantic :=
    (satisfies_canonicalUniformOmegaInjectionFormula
      spec kappa (natLCarrier n) injection).mp <| by
        simpa only [params] using hformula
  rcases hsemantic with
    ⟨stage, hstage, _hinjectionPower, hinjectionGraph, _hminimal⟩
  have hstageEq : stage = spec.value n :=
    (spec.realizes n stage).mp hstage
  simpa only [hstageEq] using hinjectionGraph



/-- With the standard infinite-cardinal absorption hypotheses, the omega
union itself injects into `kappa`. -/
private theorem injects_parametricUniformOmegaUnion_of_pointwise
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa : LCarrier.{u})
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hsquare : Injects LMem (prodLCarrier kappa kappa) kappa)
    (hinjects : forall n : Nat, Injects LMem (spec.value n) kappa) :
    Injects LMem (parametricUniformOmegaUnion spec) kappa := by
  rcases exists_parametricUniformOmegaInjectionFamilyData
      spec kappa hinjects with ⟨data⟩
  exact injects_parametricUniformOmegaUnion_of_injectionFamily
    spec homega hsquare data.isFunctionGraph data.values_areInjections

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_ParametricUniformOmegaInjectionFamily

/- Source module: Solutions.Work_CUGCH_TextbookEUniformWitnessCardinality -/
section GCHSource_Work_CUGCH_TextbookEUniformWitnessCardinality
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/







/-!
# Cardinal control for the textbook E witness hull

This file follows the standard countable-language Skolem-hull estimate with
internally represented graphs at every step.  The task set and all finite
parameter tuples inject into an infinite internal cardinal.  The inverse of
the Replacement graph injects its range back into the request domain, and a
tagged binary-union graph retains the preceding stage.  Finite induction gives
the pointwise bounds; canonical least selection and Replacement then collect
the injection family used to bound the genuine internal omega union.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model
open Constructible.FiniteSequenceZF

noncomputable section

local notation "LMem" => Constructible.Model.lCarrierMem











/-- The genuine internal omega union of witness stages injects into the same
infinite cardinal. -/
private theorem injects_textbookEUniformWitnessOmegaUnion_lCarrier
    {seed U kappa : LCarrier.{u}}
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hseed : Injects LMem seed kappa) :
    Injects LMem (textbookEUniformWitnessOmegaUnion seed U) kappa := by
  let spec := textbookEUniformWitnessOmegaFamilySpec seed U
  have hsquare : Injects LMem (prodLCarrier kappa kappa) kappa :=
    injects_infiniteCardinalSquare_lCarrier hcardinal homega
  have hpointwise : forall n : Nat, Injects LMem (spec.value n) kappa := by
    intro n
    simpa only [spec, textbookEUniformWitnessOmegaFamilySpec_value] using
      injects_textbookEUniformWitnessStage_lCarrier
        hcardinal homega hseed n
  simpa only [textbookEUniformWitnessOmegaUnion, spec] using
    injects_parametricUniformOmegaUnion_of_pointwise
      spec kappa homega hsquare hpointwise

/-- Adjoining one distinguished parameter to an infinite cardinal preserves
the bound. -/
private theorem injects_textbookEElementaryHullSeed_lCarrier
    (kappa x : LCarrier.{u})
    (homega : IsSubsetOf LMem omegaLCarrier kappa) :
    Injects LMem (textbookEElementaryHullSeed kappa x) kappa := by
  by_cases hx : x.1 ∈ kappa.1
  · apply injects_of_subset_lCarrier
    intro z hz
    let zL : LCarrier.{u} :=
      ⟨z, mem_L_of_mem hz (textbookEElementaryHullSeed kappa x).2⟩
    rcases (mem_adjoinLCarrier_iff kappa x zL).mp hz with hzx | hzkappa
    · have hzEq : z = x.1 := congrArg Subtype.val hzx
      simpa only [hzEq] using hx
    · exact hzkappa
  · exact injects_adjoin_fresh_of_omega_subset_lCarrier
      homega hx (injects_refl_lCarrier kappa)

/-- The concrete fully elementary textbook E hull is cardinal-controlled. -/
private theorem injects_textbookEElementaryHull_lCarrier_gchProof12
    (kappa x : LCarrier.{u})
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem omegaLCarrier kappa) :
    Injects LMem (textbookEElementaryHull kappa x) kappa := by
  simpa only [textbookEElementaryHull] using
    injects_textbookEUniformWitnessOmegaUnion_lCarrier
      hcardinal homega
      (injects_textbookEElementaryHullSeed_lCarrier kappa x homega)



end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_TextbookEUniformWitnessCardinality

universe u

theorem solution : ∀ (kappa x : Constructible.Model.LCarrier.{u}),
  @Constructible.ContinuumFormula.IsCardinal.{u + 1} Constructible.Model.LCarrier.{u}
      Constructible.Model.lCarrierMem.{u} kappa →
    @Constructible.ContinuumFormula.IsSubsetOf.{u + 1} Constructible.Model.LCarrier.{u}
        Constructible.Model.lCarrierMem.{u} Constructible.Model.omegaLCarrier.{u} kappa →
      @Constructible.ContinuumFormula.Injects.{u + 1} Constructible.Model.LCarrier.{u}
        Constructible.Model.lCarrierMem.{u} (Constructible.ContinuumFormula.textbookEElementaryHull.{u} kappa x) kappa :=
  @Constructible.ContinuumFormula.injects_textbookEElementaryHull_lCarrier_gchProof12.{u}
