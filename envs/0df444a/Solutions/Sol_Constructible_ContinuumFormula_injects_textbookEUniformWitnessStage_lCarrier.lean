-- Prove2me | solution 1 for Constructible.ContinuumFormula.injects_textbookEUniformWitnessStage_lCarrier
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T00:11:46.201912+00:00
-- url     : https://prove2.me/submissions/f4411c76-57e2-4031-9915-5112a5b7dd62

import Definitions.Def_CH_ConstructibleGCH_HullIteration
import Theorems.Thm_Constructible_ContinuumFormula_injects_infiniteCardinalSquare_lCarrier
import Theorems.Thm_Constructible_ContinuumFormula_injects_textbookEUniformWitnessRequestDomain_lCarrier

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

/- Source module: Solutions.Work_CUGCH_InternalBinaryUnionInjection -/
section GCHSource_Work_CUGCH_InternalBinaryUnionInjection
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Internally represented injections for binary unions

The standard cardinal estimate for one Skolem step uses the fact that a
finite union of sets of size at most an infinite cardinal again has size at
most that cardinal.  This file proves the binary case with an actual
Kuratowski graph in `L`.

The two summands are tagged by the internal natural numbers zero and one.
The resulting graph maps the union into `kappa x kappa`; a supplied internal
square-absorption graph then gives the desired injection into `kappa`.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section













/-- The tagged relation is represented by a genuine internal injection into
`kappa x kappa`. -/
private theorem injects_binaryUnion_into_square_lCarrier
    {left right kappa : LCarrier.{u}}
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hleft : Injects LMem left kappa)
    (hright : Injects LMem right kappa) :
    Injects LMem (unionLCarrier left right) (prodLCarrier kappa kappa) := by
  rcases hleft with ⟨first, hfirst⟩
  rcases hright with ⟨second, hsecond⟩
  let zero : LCarrier.{u} := natLCarrier 0
  let one : LCarrier.{u} := natLCarrier 1
  let domain := unionLCarrier left right
  let codomain := prodLCarrier kappa kappa
  let support := unionLCarrier domain codomain
  have hzeroOmega : zero.1 ∈ omegaLCarrier.1 := by
    change (FiniteSequenceZF.natCode 0 : ZFSet.{u}) ∈
      Ordinal.omega0.toZFSet
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr <|
      Exists.intro 0 rfl
  have honeOmega : one.1 ∈ omegaLCarrier.1 := by
    change (FiniteSequenceZF.natCode 1 : ZFSet.{u}) ∈
      Ordinal.omega0.toZFSet
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr <|
      Exists.intro 1 rfl
  have hzeroKappa : zero.1 ∈ kappa.1 := homega zero hzeroOmega
  have honeKappa : one.1 ∈ kappa.1 := homega one honeOmega
  have hzeroOne : zero ≠ one := by
    intro h
    have hcode :
        (FiniteSequenceZF.natCode 0 : ZFSet.{u}) =
          FiniteSequenceZF.natCode 1 := congrArg Subtype.val h
    exact Nat.zero_ne_one (FiniteSequenceZF.natCode_injective hcode)
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      taggedUnionInjectionFormula ![left, right, first, second, zero, one]
      support with
    ⟨graph, hsupport, hrelation⟩
  have hvalue : forall input output : LCarrier.{u},
      GraphValue LMem graph input output <->
        TaggedUnionInjectionRel LMem
          left right first second zero one input output := by
    intro input output
    rw [graphValue_lCarrier_iff_graphRel, hrelation]
    constructor
    · rintro ⟨_hinputSupport, _houtputSupport, hformula⟩
      exact (satisfies_taggedUnionInjectionRelation
        left right first second zero one input output).mp hformula
    · intro hrel
      have hinputDomain : input.1 ∈ domain.1 := by
        rcases hrel with hrel | hrel
        · exact (mem_unionLCarrier_iff left right input).mpr <| Or.inl hrel.1
        · exact (mem_unionLCarrier_iff left right input).mpr <| Or.inr hrel.2.1
      have houtputCodomain : output.1 ∈ codomain.1 := by
        rcases hrel with hrel | hrel
        · rcases hrel.2 with ⟨image, himage, hpair⟩
          have himageKappa := hfirst.1.graphValue_mem_lCarrier himage |>.2
          have houtput := (isKuratowskiPairOf_lCarrier_iff
            output zero image).mp hpair
          change output.1 ∈ ZFSet.prod kappa.1 kappa.1
          rw [houtput, ZFSet.pair_mem_prod]
          exact And.intro hzeroKappa himageKappa
        · rcases hrel.2.2 with ⟨image, himage, hpair⟩
          have himageKappa := hsecond.1.graphValue_mem_lCarrier himage |>.2
          have houtput := (isKuratowskiPairOf_lCarrier_iff
            output one image).mp hpair
          change output.1 ∈ ZFSet.prod kappa.1 kappa.1
          rw [houtput, ZFSet.pair_mem_prod]
          exact And.intro honeKappa himageKappa
      refine And.intro
        ((mem_unionLCarrier_iff domain codomain input).mpr <| Or.inl hinputDomain) <|
        And.intro
          ((mem_unionLCarrier_iff domain codomain output).mpr <| Or.inr houtputCodomain) ?_
      exact (satisfies_taggedUnionInjectionRelation
        left right first second zero one input output).mpr hrel
  have hbetween : IsGraphBetween LMem graph domain codomain := by
    intro pair hpair
    rcases hsupport pair hpair with
      ⟨input, output, _hinputSupport, _houtputSupport, hpairEq, hformula⟩
    have hrel := (satisfies_taggedUnionInjectionRelation
      left right first second zero one input output).mp hformula
    have hmem : input.1 ∈ domain.1 ∧ output.1 ∈ codomain.1 := by
      rcases hrel with hrel | hrel
      · have hx := hfirst.1.graphValue_mem_lCarrier hrel.2.choose_spec.1
        exact And.intro
          ((mem_unionLCarrier_iff left right input).mpr <| Or.inl hrel.1)
          (by
            have hp := (isKuratowskiPairOf_lCarrier_iff
              output zero hrel.2.choose).mp hrel.2.choose_spec.2
            change output.1 ∈ ZFSet.prod kappa.1 kappa.1
            rw [hp, ZFSet.pair_mem_prod]
            exact And.intro hzeroKappa hx.2)
      · have hx := hsecond.1.graphValue_mem_lCarrier hrel.2.2.choose_spec.1
        exact And.intro
          ((mem_unionLCarrier_iff left right input).mpr <| Or.inr hrel.2.1)
          (by
            have hp := (isKuratowskiPairOf_lCarrier_iff
              output one hrel.2.2.choose).mp hrel.2.2.choose_spec.2
            change output.1 ∈ ZFSet.prod kappa.1 kappa.1
            rw [hp, ZFSet.pair_mem_prod]
            exact And.intro honeKappa hx.2)
    exact Exists.intro input <| And.intro hmem.1 <|
      Exists.intro output <| And.intro hmem.2 <|
        (isKuratowskiPairOf_lCarrier_iff pair input output).mpr hpairEq
  refine Exists.intro graph <| And.intro hbetween <| And.intro ?_ ?_
  · intro input hinput
    rcases (mem_unionLCarrier_iff left right input).mp hinput with
      hinputLeft | hinputRight
    · rcases hfirst.2.1 input hinputLeft with
        ⟨image, himageKappa, himage, himageUnique⟩
      let output := orderedPairLCarrier zero image
      have houtput : output.1 ∈ codomain.1 := by
        change ZFSet.pair zero.1 image.1 ∈ ZFSet.prod kappa.1 kappa.1
        rw [ZFSet.pair_mem_prod]
        exact And.intro hzeroKappa himageKappa
      refine Exists.intro output <| And.intro houtput <|
        And.intro ((hvalue input output).mpr <| Or.inl <|
          And.intro hinputLeft <| Exists.intro image <|
            And.intro himage <|
              (isKuratowskiPairOf_lCarrier_iff output zero image).mpr rfl) ?_
      intro other _hother hinputOther
      rcases (hvalue input other).mp hinputOther with hotherLeft | hotherRight
      · rcases hotherLeft.2 with ⟨otherImage, hotherImage, hotherPair⟩
        have hotherImageKappa :=
          hfirst.1.graphValue_mem_lCarrier hotherImage |>.2
        have himageEq := himageUnique otherImage hotherImageKappa hotherImage
        subst otherImage
        apply Subtype.ext
        exact ((isKuratowskiPairOf_lCarrier_iff other zero image).mp
          hotherPair).trans rfl.symm
      · exact (hotherRight.1 hinputLeft).elim
    · by_cases hinputLeft : input.1 ∈ left.1
      · rcases hfirst.2.1 input hinputLeft with
          ⟨image, himageKappa, himage, himageUnique⟩
        let output := orderedPairLCarrier zero image
        have houtput : output.1 ∈ codomain.1 := by
          change ZFSet.pair zero.1 image.1 ∈ ZFSet.prod kappa.1 kappa.1
          rw [ZFSet.pair_mem_prod]
          exact And.intro hzeroKappa himageKappa
        refine Exists.intro output <| And.intro houtput <|
          And.intro ((hvalue input output).mpr <| Or.inl <|
            And.intro hinputLeft <| Exists.intro image <|
              And.intro himage <|
                (isKuratowskiPairOf_lCarrier_iff output zero image).mpr rfl) ?_
        intro other _hother hinputOther
        rcases (hvalue input other).mp hinputOther with hotherLeft | hotherRight
        · rcases hotherLeft.2 with ⟨otherImage, hotherImage, hotherPair⟩
          have hotherImageKappa :=
            hfirst.1.graphValue_mem_lCarrier hotherImage |>.2
          have himageEq := himageUnique otherImage hotherImageKappa hotherImage
          subst otherImage
          exact Subtype.ext <|
            ((isKuratowskiPairOf_lCarrier_iff other zero image).mp
              hotherPair).trans rfl.symm
        · exact (hotherRight.1 hinputLeft).elim
      · rcases hsecond.2.1 input hinputRight with
          ⟨image, himageKappa, himage, himageUnique⟩
        let output := orderedPairLCarrier one image
        have houtput : output.1 ∈ codomain.1 := by
          change ZFSet.pair one.1 image.1 ∈ ZFSet.prod kappa.1 kappa.1
          rw [ZFSet.pair_mem_prod]
          exact And.intro honeKappa himageKappa
        refine Exists.intro output <| And.intro houtput <|
          And.intro ((hvalue input output).mpr <| Or.inr <|
            And.intro hinputLeft <| And.intro hinputRight <|
              Exists.intro image <| And.intro himage <|
                (isKuratowskiPairOf_lCarrier_iff output one image).mpr rfl) ?_
        intro other _hother hinputOther
        rcases (hvalue input other).mp hinputOther with hotherLeft | hotherRight
        · exact (hinputLeft hotherLeft.1).elim
        · rcases hotherRight.2.2 with ⟨otherImage, hotherImage, hotherPair⟩
          have hotherImageKappa :=
            hsecond.1.graphValue_mem_lCarrier hotherImage |>.2
          have himageEq := himageUnique otherImage hotherImageKappa hotherImage
          subst otherImage
          exact Subtype.ext <|
            ((isKuratowskiPairOf_lCarrier_iff other one image).mp
              hotherPair).trans rfl.symm
  · intro output _houtput input hinput hinputOutput other hother hotherOutput
    rcases (hvalue input output).mp hinputOutput with hinputLeft | hinputRight <;>
      rcases (hvalue other output).mp hotherOutput with hotherLeft | hotherRight
    · rcases hinputLeft.2 with ⟨inputImage, hinputImage, hinputPair⟩
      rcases hotherLeft.2 with ⟨otherImage, hotherImage, hotherPair⟩
      have hpairs := ZFSet.pair_inj.mp <|
        ((isKuratowskiPairOf_lCarrier_iff output zero inputImage).mp
          hinputPair).symm.trans
        ((isKuratowskiPairOf_lCarrier_iff output zero otherImage).mp hotherPair)
      have himageEq : inputImage = otherImage := Subtype.ext hpairs.2
      subst otherImage
      exact hfirst.2.2 inputImage
        (hfirst.1.graphValue_mem_lCarrier hinputImage |>.2)
        input hinputLeft.1 hinputImage other hotherLeft.1 hotherImage
    · rcases hinputLeft.2 with ⟨inputImage, _hinputImage, hinputPair⟩
      rcases hotherRight.2.2 with ⟨otherImage, _hotherImage, hotherPair⟩
      have hpairs := ZFSet.pair_inj.mp <|
        ((isKuratowskiPairOf_lCarrier_iff output zero inputImage).mp
          hinputPair).symm.trans
        ((isKuratowskiPairOf_lCarrier_iff output one otherImage).mp hotherPair)
      exact (hzeroOne <| Subtype.ext hpairs.1).elim
    · rcases hinputRight.2.2 with ⟨inputImage, _hinputImage, hinputPair⟩
      rcases hotherLeft.2 with ⟨otherImage, _hotherImage, hotherPair⟩
      have hpairs := ZFSet.pair_inj.mp <|
        ((isKuratowskiPairOf_lCarrier_iff output one inputImage).mp
          hinputPair).symm.trans
        ((isKuratowskiPairOf_lCarrier_iff output zero otherImage).mp hotherPair)
      exact (hzeroOne <| (Subtype.ext hpairs.1).symm).elim
    · rcases hinputRight.2.2 with ⟨inputImage, hinputImage, hinputPair⟩
      rcases hotherRight.2.2 with ⟨otherImage, hotherImage, hotherPair⟩
      have hpairs := ZFSet.pair_inj.mp <|
        ((isKuratowskiPairOf_lCarrier_iff output one inputImage).mp
          hinputPair).symm.trans
        ((isKuratowskiPairOf_lCarrier_iff output one otherImage).mp hotherPair)
      have himageEq : inputImage = otherImage := Subtype.ext hpairs.2
      subst otherImage
      exact hsecond.2.2 inputImage
        (hsecond.1.graphValue_mem_lCarrier hinputImage |>.2)
        input hinputRight.2.1 hinputImage other hotherRight.2.1 hotherImage

/-- Binary unions preserve an internal infinite-cardinal bound. -/
private theorem injects_binaryUnion_lCarrier
    {left right kappa : LCarrier.{u}}
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hsquare : Injects LMem (prodLCarrier kappa kappa) kappa)
    (hleft : Injects LMem left kappa)
    (hright : Injects LMem right kappa) :
    Injects LMem (unionLCarrier left right) kappa :=
  (injects_binaryUnion_into_square_lCarrier homega hleft hright).trans_lCarrier
    hsquare

end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalBinaryUnionInjection

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







/-- One uniform witness step preserves an internal infinite-cardinal bound.
The range estimate is obtained by reversing the actual Replacement graph. -/
private theorem injects_textbookEUniformWitnessStep_lCarrier
    {seed U kappa : LCarrier.{u}}
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hseed : Injects LMem seed kappa) :
    Injects LMem (textbookEUniformWitnessStep seed U) kappa := by
  let data := textbookEUniformWitnessReplacementData seed U
  have hrequest : Injects LMem
      (textbookEUniformWitnessRequestDomain seed) kappa :=
    injects_textbookEUniformWitnessRequestDomain_lCarrier
      hcardinal homega hseed
  have hrangeDomain : Injects LMem data.range
      (textbookEUniformWitnessRequestDomain seed) :=
    injects_range_into_domain_of_functionGraph
      data.graph (textbookEUniformWitnessRequestDomain seed) data.range
      data.isFunctionGraph data.rangeCovered
  have hrange : Injects LMem data.range kappa :=
    hrangeDomain.trans_lCarrier hrequest
  have hsquare : Injects LMem (prodLCarrier kappa kappa) kappa :=
    injects_infiniteCardinalSquare_lCarrier hcardinal homega
  have hunionEq :
      Constructible.Model.unionLCarrier seed data.range =
        Constructible.ContinuumFormula.unionLCarrier seed data.range := by
    apply Constructible.Model.lCarrier_extensionality
    intro z
    rw [Constructible.Model.mem_unionLCarrier_iff,
      Constructible.ContinuumFormula.mem_unionLCarrier_iff]
  rw [textbookEUniformWitnessStep, hunionEq]
  exact injects_binaryUnion_lCarrier homega hsquare hseed hrange

/-- Every finite stage of the simultaneous iteration has a genuine internal
injection into `kappa`. -/
private theorem injects_textbookEUniformWitnessStage_lCarrier_gchProof11
    {seed U kappa : LCarrier.{u}}
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hseed : Injects LMem seed kappa) :
    forall n : Nat,
      Injects LMem (textbookEUniformWitnessStage seed U n) kappa := by
  intro n
  induction n with
  | zero => simpa only [textbookEUniformWitnessStage_zero] using hseed
  | succ n ih =>
      simpa only [textbookEUniformWitnessStage_succ] using
        injects_textbookEUniformWitnessStep_lCarrier
          hcardinal homega ih









end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_TextbookEUniformWitnessCardinality

universe u

theorem solution : ∀ {seed U kappa : Constructible.Model.LCarrier.{u}},
  @Constructible.ContinuumFormula.IsCardinal.{u + 1} Constructible.Model.LCarrier.{u}
      Constructible.Model.lCarrierMem.{u} kappa →
    @Constructible.ContinuumFormula.IsSubsetOf.{u + 1} Constructible.Model.LCarrier.{u}
        Constructible.Model.lCarrierMem.{u} Constructible.Model.omegaLCarrier.{u} kappa →
      @Constructible.ContinuumFormula.Injects.{u + 1} Constructible.Model.LCarrier.{u}
          Constructible.Model.lCarrierMem.{u} seed kappa →
        ∀ (n : Nat),
          @Constructible.ContinuumFormula.Injects.{u + 1} Constructible.Model.LCarrier.{u}
            Constructible.Model.lCarrierMem.{u} (Constructible.Model.textbookEUniformWitnessStage.{u} seed U n) kappa :=
  @Constructible.ContinuumFormula.injects_textbookEUniformWitnessStage_lCarrier_gchProof11.{u}
