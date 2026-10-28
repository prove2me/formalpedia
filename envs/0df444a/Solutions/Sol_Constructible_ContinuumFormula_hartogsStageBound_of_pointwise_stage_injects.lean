-- Prove2me | solution 1 for Constructible.ContinuumFormula.hartogsStageBound_of_pointwise_stage_injects
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T00:00:44.108791+00:00
-- url     : https://prove2.me/submissions/c3f96829-e93c-4485-9d57-1a7a10d30e26

import Definitions.Def_CH_ConstructibleGCH_Library21
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













/-- Internal equinumerosity gives an internal injection. -/
private theorem Equinumerous.injects {A : Type u} {E : A → A → Prop}
    {domain codomain : A} (h : Equinumerous E domain codomain) :
    Injects E domain codomain := by
  rcases h with ⟨graph, hgraph⟩
  exact ⟨graph, hgraph.toIsInjection⟩









private theorem Injects.cardinalMk_le
    {A : Type u} {E : A → A → Prop} {domain codomain : A}
    (h : Injects E domain codomain) :
    #(RelationCarrier E domain) ≤ #(RelationCarrier E codomain) := by
  rcases h with ⟨graph, hgraph⟩
  exact Cardinal.mk_le_of_injective hgraph.toFun_injective



/--
The Hartogs obstruction is an internal cardinal as soon as internally coded
injections can be reversed along a bijection and composed.  Keeping these
hypotheses explicit prevents an ambient function from being mistaken for a
graph which belongs to the membership structure.
-/
private theorem IsHartogsNumber.isCardinal_of
    {A : Type u} {E : A → A → Prop} {base hartogs : A}
    (h : IsHartogsNumber E base hartogs)
    (reverse : ∀ {x y : A}, Equinumerous E x y → Injects E y x)
    (comp : ∀ {x y z : A},
      Injects E x y → Injects E y z → Injects E x z) :
    IsCardinal E hartogs := by
  refine ⟨h.1, ?_⟩
  intro alpha halpha heq
  exact h.2.1 (comp (reverse heq) (h.2.2 alpha halpha))

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

private theorem exists_converseGraph_lCarrier
    {graph domain codomain : Constructible.Model.LCarrier.{u}}
    (hgraph : IsGraphBetween Constructible.Model.lCarrierMem
      graph domain codomain) :
    ∃ converse : Constructible.Model.LCarrier.{u},
      IsGraphBetween Constructible.Model.lCarrierMem
        converse codomain domain ∧
      ∀ x y : Constructible.Model.LCarrier.{u},
        GraphValue Constructible.Model.lCarrierMem converse x y ↔
          GraphValue Constructible.Model.lCarrierMem graph y x := by
  let container := unionLCarrier codomain domain
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      converseGraphPredicate ![graph] container with
    ⟨converse, hsupport, hrelation⟩
  have hvalue : ∀ x y : Constructible.Model.LCarrier.{u},
      GraphValue Constructible.Model.lCarrierMem converse x y ↔
        GraphValue Constructible.Model.lCarrierMem graph y x := by
    intro x y
    rw [graphValue_lCarrier_iff_graphRel, hrelation]
    constructor
    · rintro ⟨_hx, _hy, hformula⟩
      exact (satisfies_converseGraphPredicate graph x y).mp hformula
    · intro hyx
      have hmem := hgraph.graphValue_mem_lCarrier hyx
      refine ⟨?_, ?_, ?_⟩
      · exact (mem_unionLCarrier_iff codomain domain x).mpr
          (Or.inl hmem.2)
      · exact (mem_unionLCarrier_iff codomain domain y).mpr
          (Or.inr hmem.1)
      · exact (satisfies_converseGraphPredicate graph x y).mpr hyx
  refine ⟨converse, ?_, hvalue⟩
  intro pair hpair
  rcases hsupport pair hpair with
    ⟨x, y, _hxContainer, _hyContainer, hpairEq, hformula⟩
  have hyx := (satisfies_converseGraphPredicate graph x y).mp hformula
  have hmem := hgraph.graphValue_mem_lCarrier hyx
  exact ⟨x, hmem.2, y, hmem.1,
    (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq⟩

private theorem Equinumerous.symm_lCarrier
    {domain codomain : Constructible.Model.LCarrier.{u}}
    (h : Equinumerous Constructible.Model.lCarrierMem domain codomain) :
    Equinumerous Constructible.Model.lCarrierMem codomain domain := by
  rcases h with ⟨graph, hgraph⟩
  rcases exists_converseGraph_lCarrier hgraph.1 with
    ⟨converse, hbetween, hvalue⟩
  refine ⟨converse, hbetween, ?_, ?_⟩
  · intro x hx
    rcases hgraph.2.2 x hx with ⟨y, hy, hyx, hyUnique⟩
    refine ⟨y, hy, (hvalue x y).mpr hyx, ?_⟩
    intro z hz hxz
    exact hyUnique z hz ((hvalue x z).mp hxz)
  · intro y hy
    rcases hgraph.2.1 y hy with ⟨x, hx, hyx, hxUnique⟩
    refine ⟨x, hx, (hvalue x y).mpr hyx, ?_⟩
    intro z hz hzy
    exact hxUnique z hz ((hvalue z y).mp hzy)

/-! ## Hartogs numbers are internal cardinals -/

private theorem internalHartogsLCarrier_isCardinal
    (base : Constructible.Model.LCarrier.{u}) :
    IsCardinal Constructible.Model.lCarrierMem
      (internalHartogsLCarrier base) := by
  apply (internalHartogsLCarrier_isHartogsNumber base).isCardinal_of
  · intro x y hxy
    exact hxy.symm_lCarrier.injects
  · intro x y z hxy hyz
    exact hxy.trans_lCarrier hyz

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalInjections

/- Source module: Solutions.Work_CUGCH_HartogsSuccessor -/
section GCHSource_Work_CUGCH_HartogsSuccessor
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Hartogs numbers as successor cardinals

This file isolates the one use of the internal Cantor--Schroeder--Bernstein
theorem needed to identify the Hartogs number of an internal cardinal with
its successor cardinal.  Until an unconditional internal CSB construction is
available, the relevant antisymmetry property is kept as an explicit
hypothesis.
-/

section

universe u

namespace Constructible.ContinuumFormula





/-- A cardinal belongs to its internal Hartogs number. -/
private theorem IsHartogsNumber.base_mem_lCarrier
    {base hartogs : Constructible.Model.LCarrier.{u}}
    (hhartogs : IsHartogsNumber Constructible.Model.lCarrierMem base hartogs)
    (hbase : IsCardinal Constructible.Model.lCarrierMem base) :
    Constructible.Model.lCarrierMem base hartogs := by
  obtain ⟨alpha, rfl⟩ :=
    exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal base hbase.1
  obtain ⟨beta, rfl⟩ :=
    exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal hartogs hhartogs.1
  change
    (Constructible.Model.ordinalLCarrier alpha).1 ∈
      (Constructible.Model.ordinalLCarrier beta).1
  rw [Constructible.Model.ordinalLCarrier_mem_ordinalLCarrier_iff]
  by_contra hnotlt
  have hle : beta <= alpha := le_of_not_gt hnotlt
  apply hhartogs.2.1
  apply injects_of_subset_lCarrier
  intro z hz
  obtain ⟨gamma, hgamma, hvalue⟩ := Ordinal.mem_toZFSet_iff.mp hz
  apply Ordinal.mem_toZFSet_iff.mpr
  exact ⟨gamma, lt_of_lt_of_le hgamma hle, hvalue⟩





/-! ## Unconditional specialization to `LCarrier` -/







end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_HartogsSuccessor

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

/-- At the Hartogs index, the selector no longer appears among the remaining
interfaces. -/
private theorem injects_hartogsStage_of_internal_injectionFamily
    (kappa : LCarrier.{u})
    (hlimit : Order.IsSuccLimit (internalHartogsOrdinal kappa))
    {injectionFamily graphFamily : LCarrier.{u}}
    (hinjectionFamily : IsFunctionGraph LMem injectionFamily
      (internalHartogsLCarrier kappa) graphFamily)
    (hinjections : forall ordinal : Ordinal.{u},
      ordinal < internalHartogsOrdinal kappa ->
      forall injection : LCarrier.{u},
        GraphValue LMem injectionFamily
          (ordinalLCarrier ordinal) injection ->
        IsInjection LMem injection (stageLCarrier ordinal) kappa)
    (hproduct : Injects LMem
      (Constructible.Model.prodLCarrier
        (internalHartogsLCarrier kappa) kappa)
      (internalHartogsLCarrier kappa)) :
    Injects LMem
      (stageLCarrier (internalHartogsOrdinal kappa))
      (internalHartogsLCarrier kappa) := by
  exact (injects_limitStage_to_prod_of_internalInjectionFamily hlimit
    hinjectionFamily hinjections).trans_lCarrier hproduct

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

/-- A set containing omega internally absorbs one von Neumann successor. -/
private theorem injects_successor_of_omega_subset_lCarrier
    {domain kappa : LCarrier.{u}}
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hinjects : Injects LMem domain kappa) :
    Injects LMem (successorLCarrier domain) kappa := by
  have hfresh : domain.1 ∉ domain.1 := ZFSet.mem_irrefl domain.1
  simpa only [adjoin_self_eq_successorLCarrier] using
    injects_adjoin_fresh_of_omega_subset_lCarrier
      homega hfresh hinjects

/-- Ordinal specialization of one-point absorption. -/
private theorem injects_successorOrdinal_of_omega_subset_lCarrier
    {alpha : Ordinal.{u}} {kappa : LCarrier.{u}}
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hinjects : Injects LMem (ordinalLCarrier alpha) kappa) :
    Injects LMem (ordinalLCarrier (Order.succ alpha)) kappa := by
  simpa only [successorLCarrier_ordinalLCarrier] using
    injects_successor_of_omega_subset_lCarrier homega hinjects

end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalInfiniteCardinalAbsorption

/- Source module: Solutions.Work_CUGCH_HartogsLimit -/
section GCHSource_Work_CUGCH_HartogsLimit
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The Hartogs ordinal of an internally infinite cardinal is a limit

The proof is the standard successor-shift argument.  A cardinal base belongs
to its Hartogs ordinal, excluding zero.  If the Hartogs ordinal were
`alpha + 1`, its defining property would provide an internal injection
`alpha -> kappa`; finite absorption then extends this to
`alpha + 1 -> kappa`, contradicting the Hartogs obstruction.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-- The internal Hartogs ordinal of an internal cardinal is nonzero. -/
private theorem internalHartogsOrdinal_ne_zero_of_isCardinal
    (kappa : LCarrier.{u})
    (hkappa : IsCardinal LMem kappa) :
    internalHartogsOrdinal kappa ≠ 0 := by
  intro hzero
  have hkappaMem : kappa.1 ∈ (internalHartogsLCarrier kappa).1 :=
    (internalHartogsLCarrier_isHartogsNumber kappa).base_mem_lCarrier
      hkappa
  have hhartogsEmpty :
      internalHartogsLCarrier kappa = emptyLCarrier := by
    simp only [internalHartogsLCarrier, hzero, ordinalLCarrier_zero]
  rw [hhartogsEmpty] at hkappaMem
  exact not_mem_emptyLCarrier kappa hkappaMem

/-- If `kappa` contains omega, its internal Hartogs ordinal cannot be a
successor. -/
private theorem internalHartogsOrdinal_ne_successor_of_omega_subset
    (kappa : LCarrier.{u})
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (alpha : Ordinal.{u}) :
    internalHartogsOrdinal kappa ≠ Order.succ alpha := by
  intro hsuccessor
  have hhartogs := internalHartogsLCarrier_isHartogsNumber kappa
  have halphaMem :
      (ordinalLCarrier alpha).1 ∈
        (internalHartogsLCarrier kappa).1 := by
    change (ordinalLCarrier alpha).1 ∈
      (ordinalLCarrier (internalHartogsOrdinal kappa)).1
    apply (ordinalLCarrier_mem_ordinalLCarrier_iff
      (internalHartogsOrdinal kappa) alpha).mpr
    rw [hsuccessor]
    exact Order.lt_succ alpha
  have halphaInjects :
      Injects LMem (ordinalLCarrier alpha) kappa :=
    hhartogs.2.2 (ordinalLCarrier alpha) halphaMem
  have hsuccessorInjects :
      Injects LMem (ordinalLCarrier (Order.succ alpha)) kappa :=
    injects_successorOrdinal_of_omega_subset_lCarrier
      homega halphaInjects
  apply hhartogs.2.1
  simpa only [internalHartogsLCarrier, hsuccessor] using
    hsuccessorInjects

/-- The internal Hartogs ordinal of an internally infinite cardinal is a
nonzero limit ordinal. -/
private theorem internalHartogsOrdinal_isSuccLimit
    (kappa : LCarrier.{u})
    (hkappa : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem omegaLCarrier kappa) :
    Order.IsSuccLimit (internalHartogsOrdinal kappa) := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit
      (internalHartogsOrdinal kappa) with
    hzero | ⟨alpha, hsuccessor⟩ | hlimit
  · exact (internalHartogsOrdinal_ne_zero_of_isCardinal
      kappa hkappa hzero).elim
  · exact (internalHartogsOrdinal_ne_successor_of_omega_subset
      kappa homega alpha hsuccessor.symm).elim
  · exact hlimit

end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_HartogsLimit

/- Source module: Solutions.Work_CUGCH_InternalInfiniteCardinalSquare -/
section GCHSource_Work_CUGCH_InternalInfiniteCardinalSquare
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/







/-!
# Squares of internal infinite cardinals

This file completes the standard maximum-lexicographic proof that an infinite
initial ordinal absorbs its square.  The induction is taken over the ambient
presentation of the ordinal, but every injection used in the conclusion and
in every induction step is witnessed by an actual Kuratowski graph in `L`.

For a point of the maximum-lexicographic order on `kappa x kappa`, its strict
initial segment lies in `bound x bound` for some `bound < kappa`.  In the
uncountable step, an internal cardinal representative `lambda` of
`bound union omega` is still below `kappa`; the induction hypothesis absorbs
`lambda x lambda`.  Initiality of `kappa` then prevents the order type of the
whole square from exceeding `kappa`.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section















/-- If `kappa` is internally infinite, its Hartogs cardinal absorbs
`Hartogs(kappa) x kappa`. -/
private theorem injects_internalHartogsProduct_internalHartogs_lCarrier
    (kappa : LCarrier.{u})
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa) :
    Injects LMem
      (prodLCarrier (internalHartogsLCarrier kappa) kappa)
      (internalHartogsLCarrier kappa) := by
  let hartogs := internalHartogsLCarrier kappa
  have hhartogsCardinal : IsCardinal LMem hartogs :=
    internalHartogsLCarrier_isCardinal kappa
  have hkappaHartogs : kappa.1 ∈ hartogs.1 :=
    (internalHartogsLCarrier_isHartogsNumber kappa).base_mem_lCarrier
      hcardinal
  have homegaHartogs : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) hartogs := by
    intro z hz
    exact hhartogsCardinal.1.1 kappa hkappaHartogs z (homega z hz)
  have hhartogsSquare : Injects LMem
      (prodLCarrier hartogs hartogs) hartogs :=
    injects_infiniteCardinalSquare_lCarrier
      hhartogsCardinal homegaHartogs
  have hhartogsSelf : Injects LMem hartogs hartogs :=
    injects_of_subset_lCarrier (fun _ hz => hz)
  have hkappaToHartogs : Injects LMem kappa hartogs := by
    apply injects_of_subset_lCarrier
    intro z hz
    exact hhartogsCardinal.1.1 kappa hkappaHartogs z hz
  exact (injects_prod_of_injects_lCarrier
    hhartogsSelf hkappaToHartogs).trans_lCarrier hhartogsSquare

end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalInfiniteCardinalSquare

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

/-- Once the uniform stage-injection formula has been constructed, all
remaining selector, union, and product steps yield the Hartogs stage bound.
The formula data is the sole remaining premise in this theorem. -/
private theorem hartogsStageBound_of_internalStageInjectionFormulaData
    (kappa : LCarrier.{u})
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa)
    (data : InternalStageInjectionFormulaData
      (internalHartogsOrdinal kappa) kappa) :
    HartogsStageBound kappa := by
  rcases exists_internalStageInjectionFamily_of_formulaData data with
    ⟨injectionFamily, graphFamily, hfamily, hinjections⟩
  exact injects_hartogsStage_of_internal_injectionFamily kappa
    (internalHartogsOrdinal_isSuccLimit kappa hcardinal homega)
    hfamily hinjections
    (injects_internalHartogsProduct_internalHartogs_lCarrier
      kappa hcardinal homega)

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





/-! ## The exact Hartogs interface -/

/--
The canonical family removes the formula-uniformity obligation from the
Hartogs bound.  The pointwise stage bound remains explicit; proving it
requires the separate zero/successor/limit transfinite cardinal induction.
-/
private theorem hartogsStageBound_of_pointwise_stage_injects_gchProof08
    (kappa : LCarrier.{u})
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hinjects : ∀ ordinal : Ordinal.{u},
      ordinal < internalHartogsOrdinal kappa →
        Injects LMem (stageLCarrier ordinal) kappa) :
    HartogsStageBound kappa :=
  hartogsStageBound_of_internalStageInjectionFormulaData
    kappa hcardinal homega
      (canonicalStageInjectionFormulaData
        (internalHartogsOrdinal kappa) kappa hinjects)

end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_CanonicalStageInjectionFamily

universe u

theorem solution : ∀ (kappa : Constructible.Model.LCarrier.{u}),
  @Constructible.ContinuumFormula.IsCardinal.{u + 1} Constructible.Model.LCarrier.{u}
      Constructible.Model.lCarrierMem.{u} kappa →
    @Constructible.ContinuumFormula.IsSubsetOf.{u + 1} Constructible.Model.LCarrier.{u}
        Constructible.Model.lCarrierMem.{u} Constructible.Model.omegaLCarrier.{u} kappa →
      (∀ (ordinal : Ordinal.{u}),
          @LT.lt.{u + 1} Ordinal.{u}
              (@Preorder.toLT.{u + 1} Ordinal.{u}
                (@PartialOrder.toPreorder.{u + 1} Ordinal.{u} Ordinal.partialOrder.{u}))
              ordinal (Constructible.ContinuumFormula.internalHartogsOrdinal.{u} kappa) →
            @Constructible.ContinuumFormula.Injects.{u + 1} Constructible.Model.LCarrier.{u}
              Constructible.Model.lCarrierMem.{u} (Constructible.Model.stageLCarrier.{u} ordinal) kappa) →
        Constructible.ContinuumFormula.HartogsStageBound.{u} kappa :=
  @Constructible.ContinuumFormula.hartogsStageBound_of_pointwise_stage_injects_gchProof08.{u}
