-- Prove2me | solution 1 for Constructible.ContinuumFormula.injects_textbookEUniformWitnessRequestDomain_lCarrier
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T00:01:05.979171+00:00
-- url     : https://prove2.me/submissions/592a42a1-2c39-4a0b-9911-f95cc943fce8

import Definitions.Def_CH_ConstructibleGCH_Library26
import Theorems.Thm_Constructible_ContinuumFormula_injects_infiniteCardinalSquare_lCarrier

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

/-- The standard infinite-cardinal form: the square injection is supplied by
the internal theorem `kappa × kappa ↪ kappa`. -/
private theorem injects_internalFiniteTupleSpaces_lCarrier
    {a kappa : LCarrier.{u}}
    (ha : Injects LMem a kappa)
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa) :
    Injects LMem (internalFiniteTupleSpaces a) kappa := by
  rcases ha with ⟨aInjection, haInjection⟩
  rcases injects_infiniteCardinalSquare_lCarrier
      hcardinal homega with
    ⟨squareInjection, hsquareInjection⟩
  exact injects_internalFiniteTupleSpaces_of_square_lCarrier
    homega haInjection hsquareInjection

end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalFiniteTupleInjection

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

private theorem natLCarrier_mem_omega (n : Nat) :
    (natLCarrier n).1 ∈ (omegaLCarrier : LCarrier.{u}).1 := by
  change (natCode n : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet
  exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
    (natCode n)).mpr ⟨n, rfl⟩

/-- The internal task set `omega x (omega \ {0})` is bounded by every
internal infinite cardinal. -/
private theorem injects_textbookEWitnessTaskDomain_lCarrier
    {kappa : LCarrier.{u}}
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hsquare : Injects LMem (prodLCarrier kappa kappa) kappa) :
    Injects LMem textbookEWitnessTaskDomain kappa := by
  have htaskSquare : Injects LMem textbookEWitnessTaskDomain
      (prodLCarrier kappa kappa) := by
    apply injects_of_subset_lCarrier
    intro task htask
    rcases (mem_textbookEWitnessTaskDomain_iff task.1).mp htask with
      ⟨code, arity, htaskEq⟩
    change task.1 ∈ ZFSet.prod kappa.1 kappa.1
    rw [htaskEq, ZFSet.pair_mem_prod]
    exact ⟨homega (natLCarrier code) (natLCarrier_mem_omega code),
      homega (natLCarrier (arity + 1))
        (natLCarrier_mem_omega (arity + 1))⟩
  exact htaskSquare.trans_lCarrier hsquare

/-- The request domain for one simultaneous witness step injects into the
controlling cardinal. -/
private theorem injects_textbookEUniformWitnessRequestDomain_lCarrier_gchProof10
    {seed kappa : LCarrier.{u}}
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hseed : Injects LMem seed kappa) :
    Injects LMem (textbookEUniformWitnessRequestDomain seed) kappa := by
  have hsquare : Injects LMem (prodLCarrier kappa kappa) kappa :=
    injects_infiniteCardinalSquare_lCarrier hcardinal homega
  have htasks : Injects LMem textbookEWitnessTaskDomain kappa :=
    injects_textbookEWitnessTaskDomain_lCarrier homega hsquare
  have htuples : Injects LMem (internalFiniteTupleSpaces seed) kappa :=
    injects_internalFiniteTupleSpaces_lCarrier hseed hcardinal homega
  have hrequestSquare : Injects LMem
      (textbookEUniformWitnessRequestDomain seed)
      (prodLCarrier kappa kappa) := by
    simpa only [textbookEUniformWitnessRequestDomain] using
      injects_prod_of_injects_lCarrier htasks htuples
  exact hrequestSquare.trans_lCarrier hsquare













end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_TextbookEUniformWitnessCardinality

universe u

theorem solution : ∀ {seed kappa : Constructible.Model.LCarrier.{u}},
  @Constructible.ContinuumFormula.IsCardinal.{u + 1} Constructible.Model.LCarrier.{u}
      Constructible.Model.lCarrierMem.{u} kappa →
    @Constructible.ContinuumFormula.IsSubsetOf.{u + 1} Constructible.Model.LCarrier.{u}
        Constructible.Model.lCarrierMem.{u} Constructible.Model.omegaLCarrier.{u} kappa →
      @Constructible.ContinuumFormula.Injects.{u + 1} Constructible.Model.LCarrier.{u}
          Constructible.Model.lCarrierMem.{u} seed kappa →
        @Constructible.ContinuumFormula.Injects.{u + 1} Constructible.Model.LCarrier.{u}
          Constructible.Model.lCarrierMem.{u} (Constructible.Model.textbookEUniformWitnessRequestDomain.{u} seed) kappa :=
  @Constructible.ContinuumFormula.injects_textbookEUniformWitnessRequestDomain_lCarrier_gchProof10.{u}
