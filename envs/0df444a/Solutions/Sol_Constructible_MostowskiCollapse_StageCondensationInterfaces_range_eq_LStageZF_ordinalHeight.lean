-- Prove2me | solution 1 for Constructible.MostowskiCollapse.StageCondensationInterfaces.range_eq_LStageZF_ordinalHeight
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-25T23:53:08.562605+00:00
-- url     : https://prove2.me/submissions/be9ed3c6-8151-431b-adfb-f85cf9140e4f

import Definitions.Def_CH_ConstructibleGCH_Library04

/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 2000000

/- Source module: Solutions.Work_ConstructibleGCH_ReuseBase -/
section GCHSource_Work_ConstructibleGCH_ReuseBase
set_option autoImplicit false












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


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Def -/
section CUAdapterModule0
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The relation-algebra definition of `Def`

This file formalizes the relation-algebra presentation of first-order
definability:

* `D 0 A n` consists of the atomic membership and equality relations;
* `D (k+1) A n` is closed under complement, intersection, and existential
  projection, using relations from stage `k`;
* `Df A n` is the union of all finite stages;
* `definablePowerset A` consists of the sections of relations in `Df` obtained
  by fixing finitely many parameters.

Here the underlying set `a` is represented by a Lean type `A`, equipped with
the binary relation which plays the role of membership.  Thus `Tuple A n` is
the type-theoretic counterpart of `a^n`.
-/


open Set

universe u

namespace Constructible











/-! ## An independent syntax and satisfaction relation -/



namespace FOFormula























/-! ### Variable management -/

















/-! ### Bounded quantifiers -/









end FOFormula

section Atomic

variable {A : Type u} (E : A → A → Prop)

































/-! ### Equivalence with first-order formula semantics -/





























end Atomic

/-! ## Specialization to Mathlib's ZFC universe -/

section ZFC

/-!
### An internal `ZFSet` version of the definable-powerset operation

The following construction uses the powerset and separation operations of
`ZFSet`.  Consequently `DefZF a` is itself a genuine ZFC set, not merely an
external Lean predicate on `ZFSet`.
-/











private theorem representZFSubset_subset (a : ZFSet.{u})
    (s : Set (ZFCarrier a)) : representZFSubset a s ⊆ a := by
  intro x hx
  exact (mem_representZFSubset_iff a s x).mp hx |>.1















/-! ### Basic structural properties of `DefZF` -/





















/-!
### The internally represented constructible hierarchy

Every value of `LStageZF` is an actual `ZFSet`.  At a limit ordinal `l`, the
index type `Set.Iio l` is small in universe `u`; `replacementRangeZF` first
forms the range of the preceding levels as a ZFC set and `limitUnionZF` then
applies internal union.  This use of `ZFSet.image` is the ambient,
metatheoretic Replacement step in the standard external recursion defining
`L`.  Mathlib's class `ZFSet.Definable` means that a function lifts to `PSet`;
it does not assert object-language first-order definability in `L`.
-/













































































end ZFC

end Constructible
end CUAdapterModule0


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Delta0 -/
section CUAdapterModule1
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Bounded formulas for the constructible hierarchy

This file introduces an intrinsically scoped syntax for `Δ₀` formulas in the
language of set theory.  Quantifiers are bounded syntactically.  The syntax is
translated to `Constructible.FOFormula`, and its semantics is proved absolute
between a transitive `ZFSet` and the ambient `ZFSet` universe.
-/


universe u

namespace Constructible











namespace Delta0Formula































/-! ## Absoluteness -/

















end Delta0Formula

end Constructible
end CUAdapterModule1


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Godel -/
section CUAdapterModule2
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Gödel operations and rudimentary closure

This file implements the standard Jensen--Devlin basis `F₀, ..., F₈` of
rudimentary (Gödel) operations on Mathlib's internal `ZFSet` universe.  Tuples
are right-associated Kuratowski pairs:

`⟨x, y, z⟩ = ⟨x, ⟨y, z⟩⟩`.

The resulting `rudimentaryClosure U` starts from `U ∪ {U}`.  The candidate
Gödel presentation of the definable powerset is then

`powerset U ∩ rudimentaryClosure U`.

Its equality with `Constructible.DefZF U` for transitive `U` is deliberately
not built into the definition; it is a theorem to be established separately.
-/


open Set

universe u

namespace Constructible.Godel

















































































































end Constructible.Godel
end CUAdapterModule2


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Delta0Godel -/
section CUAdapterModule3
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Bounded formulas for Gödel operations

This file supplies reusable `Δ₀` formulas for the finite set encodings used
by the Jensen--Devlin Gödel operations.  All coordinate conventions are
intrinsically checked by the `Fin` indices.
-/


open Set

universe u

namespace Constructible.Delta0Formula









































end Constructible.Delta0Formula

namespace Constructible.Godel

open Constructible.Delta0Formula

/-!
The fixed assignment convention for the following formulas is `![q,x,y]`:
coordinate `0` is the candidate member and coordinates `1,2` are the two
arguments of the Gödel operation.
-/



















































end Constructible.Godel
end CUAdapterModule3


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Delta0GodelGraph -/
section CUAdapterModule4
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Bounded graph formulas for the Gödel operations

Membership in every Jensen--Devlin operation is `Δ₀`.  This file strengthens
that result to formulas for the full graphs `out = Fᵢ(x,y)`, using only bounded
quantifiers in both containment directions.
-/


open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula









/-! All graph formulas below use the fixed assignment `![out,x,y]`. -/



















































end Constructible.Godel
end CUAdapterModule4


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











end ZFC

end Constructible
end CUAdapterModule5


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Ordinals -/
section CUAdapterModule6
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Ordinals in the constructible universe

The property of being a von Neumann ordinal is expressed by a bounded
first-order formula.  Its absoluteness to a transitive level lets us prove,
simultaneously, that the ordinal elements of `LStageZF α` have rank below `α`
and that `α.toZFSet` is contained in that level.
-/


open Set

universe u

namespace Constructible

section ZFC

namespace OrdinalFormula













end OrdinalFormula











end ZFC

end Constructible
end CUAdapterModule6


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteSequenceZF -/
section CUAdapterModule7
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Finite sequences as ZF sets

This file gives a small, structural encoding of finite lists of `ZFSet`s.
The payload is a chain of Kuratowski ordered pairs terminated by the empty
set.  The public sequence code also stores the von Neumann ordinal coding of
the list length.

The construction is deliberately recursive.  In particular, it does not use
an external image and therefore its constructibility proof only needs the
already established closure of `L` under ordered pairs.
-/


universe u

namespace Constructible

namespace FiniteSequenceZF































end FiniteSequenceZF

end Constructible
end CUAdapterModule7


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.IndexedSequenceZF -/
section CUAdapterModule8
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Indexed finite-sequence codes

The structural list code in `FiniteSequenceZF` is convenient for recursion.
For first-order definitions of lexicographic order, however, direct access to
the entry at an internal natural-number index is more useful.  This file codes
a list by the finite graph

`{ <xs[i], i> | i < xs.length }`

and stores its length alongside that graph.  This indexed-sequence encoding
uses pairs `<output,input>`.  It is intentionally distinct from Mathlib's
`ZFSet.IsFunc` convention, whose function graphs use `<input,output>`.
-/


universe u

namespace Constructible



namespace IndexedSequenceZF

open FiniteSequenceZF























end IndexedSequenceZF

end Constructible
end CUAdapterModule8


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Rudimentary -/
section CUAdapterModule9
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Formal terms for rudimentary closure

The closure in `Godel.lean` is defined by finite iteration.  This
file gives the equivalent finite term syntax.  The generic theorem applies to
any internally represented seed; its specialization to `U ∪ {U}` uses `none`
for the generator `U` and `some x` for a parameter `x ∈ U`.
-/


universe u v

namespace Constructible.Godel



namespace RudimentaryTerm

variable {α β : Type u}

















end RudimentaryTerm

















end Constructible.Godel
end CUAdapterModule9


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryCode -/
section CUAdapterModule10
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Canonical codes for rudimentary terms

A term is encoded in prefix form.  An application token stores the lengths of
both encoded subterms, making the code unambiguously decodable.  Shortlex on
these finite token lists gives a well-order whenever the variable labels are
well-ordered.  Consequently every value in a rudimentary closure has a unique
least representing term.
-/


universe u

namespace Constructible.Godel

namespace RudimentaryTerm











/-! ## The structural well-order -/













/-! ## Least representations -/













end RudimentaryTerm

end Constructible.Godel
end CUAdapterModule10


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryTermZFCode -/
section CUAdapterModule11
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Internal ZF codes for rudimentary terms

This file encodes the external inductive syntax `RudimentaryTerm alpha` by
genuine `ZFSet`s.  A variable encoding `rho` supplies the internal code for
each variable:

* `var a` is coded by the triple `⟨0, rho a, ∅⟩`;
* `app i left right` is coded by
  `⟨1, i, ⟨code left, code right⟩⟩`.

All pairs and triples are Kuratowski pairs.  The encoding is injective when
`rho` is injective, and its values are constructible when the variable codes
are constructible.
-/


universe u v

namespace Constructible.Godel

namespace RudimentaryTerm

noncomputable section





























end

end RudimentaryTerm

end Constructible.Godel
end CUAdapterModule11


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryPrefixZFCode -/
section CUAdapterModule12
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Internal ZF codes for rudimentary prefix syntax

`RudimentaryTerm.code` is an external Lean list of prefix tokens.  This file
turns each token into a genuine `ZFSet`, then applies
`FiniteSequenceZF.sequenceCode` to internalize the whole finite prefix list.

Variable tokens carry the actual value of `rudimentaryGenerator`: `none` is
coded by `U`, while `some x` is coded by `x`.  These values are distinct by
foundation because every such `x` belongs to `U`.  Operation tokens carry the
operation index and the two subterm-code lengths.

This file only establishes faithful internal coding and constructibility.  It
does not internalize the shortlex comparison or term evaluation relation.
-/


universe u

namespace Constructible.Godel

namespace RudimentaryTerm

noncomputable section





















end


end RudimentaryTerm

end Constructible.Godel
end CUAdapterModule12


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.DefWellOrder -/
section CUAdapterModule13
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A well-order on one definability step

Every member of `godelDef U` has a least rudimentary term representing it,
relative to a well-order of the generators `Option (ZFCarrier U)`.  Distinct
sets have distinct least terms because evaluating such a term recovers the
set.  Pulling the structural term order back along this injection therefore
well-orders `godelDef U`.
-/


universe u

namespace Constructible.Godel

open RudimentaryTerm













end Constructible.Godel
end CUAdapterModule13


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryGraph -/
section CUAdapterModule14
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# First-order graph formulas for rudimentary terms

Every rudimentary term with finitely many variables has an exact graph formula
in the ambient `ZFSet` universe.  Terms over an arbitrary variable type are
first reified using one finite parameter slot for each variable occurrence.

The application case below deliberately uses two unrestricted existential
quantifiers.  Thus the resulting formula is an ambient first-order graph; it
does not assert that all intermediate term values belong to a prescribed
transitive set.
-/


universe u v

namespace Constructible.Godel

open Constructible.Delta0Formula

namespace RudimentaryTerm

























end RudimentaryTerm

end Constructible.Godel
end CUAdapterModule14


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Simple -/
section CUAdapterModule15
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The bounded-section interface for the Gödel/Def bridge

The ambient graph of a composed rudimentary term may use intermediate values
outside a transitive carrier `U`.  The bridge to `DefZF U` therefore targets a
stronger certificate: an ambient `Δ₀` formula defining membership in the final
set, using only genuine members of `U` as parameters.

The substitution and generated-formula modules produce `Delta0Section` values;
`Delta0Section.mem_DefZF` is the final absoluteness step.
-/


universe u

namespace Constructible

open Delta0Formula





namespace Godel





end Godel

end Constructible
end CUAdapterModule15


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.FormulaGodel -/
section CUAdapterModule16
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Formula relations as rudimentary sets

This module compiles every internally scoped first-order formula over a
transitive `ZFSet` into a rudimentary relation set.  Taking a parameter fiber
then proves the formula-to-Gödel inclusion for `Def(U)`.
-/


open Set

universe u

namespace Constructible.Godel





































namespace RelationRep















































end RelationRep



end Constructible.Godel
end CUAdapterModule16


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.SimpleSubstitution -/
section CUAdapterModule17
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Strong-simple substitution

This file implements the substitution machinery for the inclusion
`godelDef U ⊆ DefZF U`.

The key point is that a membership section is not stable under composition.
This file develops complete elimination cases for set difference, internal
union, and unordered pairing, together with the generic composition and
simultaneous-substitution machinery used by the remaining primitive operations.
-/


open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

variable {n m k : Nat}



namespace DiffExpr







end DiffExpr





































/-! ## A second complete case: internal union (`F₅`) -/



namespace UnionExpr







end UnionExpr







































/-! ## A third complete case: unordered pairing (`F₀`) -/



namespace PairExpr



end PairExpr







































/-! ## Checked composition -/





/-! ## Eliminating the distinguished universe constant -/

namespace EraseUniverse

















end EraseUniverse











/-! ## Simultaneous substitutions and genuine term composition -/















end Constructible.Godel
end CUAdapterModule17


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.SimplePairSets -/
section CUAdapterModule18
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Simplicity of ordered pairs and pair sets

This file proves strong simplicity for Kuratowski ordered pairing and for the pair-set operations
used in the Gödel basis.
-/

open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

variable {n m k : Nat}

section

/-! ## Ordered pairing is simple -/








/-! ## Eliminating a last-coordinate ordered-pair value -/













/-! ## A shared expression compiler for `F₂` and `F₇` -/



namespace PairSetKind









end PairSetKind



namespace PairSetExpr







end PairSetExpr





















































end

end Constructible.Godel
end CUAdapterModule18


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.SimpleComposition -/
section CUAdapterModule19
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Composition of simple set functions

This file proves that strong simplicity is preserved by unary and binary composition. The tuple
renamings below arrange arguments and intermediate values for the corresponding bounded formulas.
-/


universe u

namespace Constructible.Godel



















end Constructible.Godel
end CUAdapterModule19


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.SimpleTerms -/
section CUAdapterModule20
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Simplicity of rudimentary terms

This file lifts simplicity from the basic Gödel operations to arbitrary finite rudimentary terms
and reifies their parameters over an internal carrier.
-/


universe u

namespace Constructible.Godel















end Constructible.Godel
end CUAdapterModule20


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.SimpleCompiler -/
section CUAdapterModule21
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Compiling simple set functions

This file packages the data needed to eliminate a binary set-valued operation from bounded
formulas and proves the generic correctness lemmas for that elimination procedure.
-/


open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

variable {n m k : Nat}





namespace ValueExpr











end ValueExpr





























end Constructible.Godel
end CUAdapterModule21


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.SimpleGenerated -/
section CUAdapterModule22
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Generated bounded formulas for simple set functions

This file derives reusable elimination formulas from `SimpleValueSpec` and proves the resulting
strong-simplicity theorem for ternary membership descriptions.
-/


open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

variable {n : Nat}

















end Constructible.Godel
end CUAdapterModule22


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.SimpleF3F4 -/
section CUAdapterModule23
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Simplicity of the Gödel operations F3 and F4

This file instantiates the generic simple-function compiler for the two operations that extract
triple components from Kuratowski-pair encodings.
-/


open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

variable {n : Nat}



namespace TripleSetKind









end TripleSetKind



























end Constructible.Godel
end CUAdapterModule23


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.SimpleF6F8 -/
section CUAdapterModule24
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Simplicity of the Gödel operations F6 and F8

This file instantiates the generic simple-function compiler for component extraction, fibers, and
the remaining bounded pair-component operation represented here by F6 and F8.
-/


open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

variable {n : Nat}























/-! ## Fibers are simple -/

















/-! ## F8 is a bounded image by the simple fiber operation -/













end Constructible.Godel
end CUAdapterModule24


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Equivalence -/
section CUAdapterModule25
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Equivalence of formula and rudimentary definability

This file proves Jensen's equivalence between first-order definable subsets of a transitive set
and the powerset-bounded closure under the nine basic Gödel operations.
-/


open Set

universe u

namespace Constructible.Godel













end Constructible.Godel
end CUAdapterModule25


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryConstructible -/
section CUAdapterModule26
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Constructibility of rudimentary term values

Every primitive Gödel operation preserves constructibility. The proof first
shows that all members of an operation value are constructible, bounds those
members together with the two operands in one constructible stage, and then
uses the existing bounded definition of the operation to place its value in
the next stage.

It follows by structural induction that a rudimentary term whose generators
belong to `L` also evaluates to an element of `L`.
-/


open Set

universe u v

namespace Constructible

namespace Godel











namespace RudimentaryTerm



end RudimentaryTerm





end Godel

end Constructible
end CUAdapterModule26


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackProgram -/
section CUAdapterModule27
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Postfix stack programs for rudimentary evaluation

Prefix tree codes are useful for structural arguments, but a uniform
first-order evaluator would have to parse arbitrary subtree boundaries.  A
postfix stack program has a local transition semantics instead:

* a variable token pushes its generator value;
* an operation token pops the right and left operands and pushes their value.

The token lists still carry a Shortlex well-order. Hence every value in one
Gödel-definability step has a least evaluating program, and these least
programs give a well-order of that step. The local transition semantics admits
internalization by a finite set-coded execution trace.
-/


universe u v

namespace Constructible.Godel

namespace RudimentaryTerm















/-! ## The structural program well-order -/









/-! ## Least programs representing definable values -/

















end RudimentaryTerm

end Constructible.Godel
end CUAdapterModule27


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackProgramZFCode -/
section CUAdapterModule28
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Internal codes for rudimentary stack programs

Postfix program tokens and whole instruction lists are encoded by genuine
`ZFSet`s.  Variable tokens carry their generator value; operation tokens carry
the finite ordinal operation index.  Whole programs use the indexed sequence
encoding, which is tailored to a first-order execution-trace predicate.
-/


universe u

namespace Constructible.Godel

namespace RudimentaryTerm

noncomputable section

















end

end RudimentaryTerm

end Constructible.Godel
end CUAdapterModule28


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackStepFormula -/
section CUAdapterModule29
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A first-order transition formula for rudimentary stack programs

The fixed parameter layout is

`[U, varTag, appTag, empty, op0, ..., op8, token, input, output]`.

The last three coordinates are the instruction and the two stack states.  A
variable instruction pushes its generator.  An operation instruction pops the
right and left operands, applies the selected Gödel operation, and pushes the
result.  Stack states use `FiniteSequenceZF.listCode`, whose cons constructor
is precisely a Kuratowski pair.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

open Constructible.Delta0Formula

/-! ## Fixed indices -/



















/-! ## Variable and operation branches -/











/-! ## Assignments and semantics -/















































end Constructible.Godel.RudimentaryTerm
end CUAdapterModule29


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackStepDecode -/
section CUAdapterModule30
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Decoding arbitrary satisfying stack-step codes

The basic semantic theorem for `stackStepFormula` was first stated on genuine
token and stack codes.  Whole-program soundness also needs the converse shape:
starting from a genuine input stack code, every arbitrary raw token/output pair
accepted by the formula must decode to a real instruction and a real output
stack.  This file proves exactly that fact.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

open FiniteSequenceZF





end Constructible.Godel.RudimentaryTerm
end CUAdapterModule30


/- Original module: ConstructibleUniverse.ModelTheory.SetTheory.Basic -/
section CUAdapterModule31
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/


/-!
# The First-Order Language of Set Theory

This file defines the first-order language with a single binary relation symbol
for membership. Equality is provided by first-order logic itself.

## Main Definitions

- `FirstOrder.Language.setTheory` is the first-order language of set theory.
- `FirstOrder.Language.Term.mem` is the atomic formula asserting membership between two terms.
- `FirstOrder.Language.setTheoryStructure` interprets membership as a binary relation.
-/


universe u v

namespace FirstOrder.Language

open Structure

variable {M : Type u} {α : Type v} {n : ℕ}













end FirstOrder.Language
end CUAdapterModule31


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Semantics -/
section CUAdapterModule32
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/


/-!
# Semantics for formulas in the language of set theory

This file provides relation-parametric term evaluation and formula realization
for Mathlib's first-order language of set theory.

The relation-parametric semantics below uses `BoundedFormula Empty n`: there are no
named free variables, and the `n` variables currently in scope are interpreted
by an assignment `Fin n -> A`.
-/


universe u

namespace Constructible

namespace Model

















end Model

end Constructible
end CUAdapterModule32


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Model -/
section CUAdapterModule33
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The first-order structure carried by the constructible universe

This file connects the formula syntax used to construct `L` with Mathlib's
general model-theory API.  The language has no function symbols and one binary
relation symbol, interpreted as membership.

The existing `Constructible.FOFormula n` treats all `n` variables uniformly
and appends a bound variable at the end of a tuple.  Mathlib's
`BoundedFormula Empty n` has exactly the same convention, so the translation
below does not need a variable permutation.
-/


open Set

universe u

namespace Constructible

namespace Model

/-! ## Raw-domain semantics for external classes -/

































section ArbitraryStructure

variable {A : Type u} (E : A -> A -> Prop)













end ArbitraryStructure

/-!
## `DefZF` through Mathlib formulas
-/





end Model

end Constructible
end CUAdapterModule33


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteSequenceComparison -/
section CUAdapterModule34
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Bounded comparison formulas for finite-sequence codes

The von Neumann codes used for lengths are ordered by membership, so their
strict comparison has a fixed atomic formula.  We also package the
lexicographic comparison of an operation token's three numeric components.

The equal-length branch of shortlex for `FiniteSequenceZF.sequenceCode` is
handled by the indexed-sequence validity and lookup infrastructure developed
in the companion modules.  The formulas below provide the reusable numeric
and lexicographic components used by those constructions.
-/


universe u

namespace Constructible

namespace FiniteSequenceZF

/-! ## Natural-number codes -/















end FiniteSequenceZF

namespace Godel.RudimentaryTerm

/-! ## Numeric operation-token payloads -/













end Godel.RudimentaryTerm

end Constructible
end CUAdapterModule34


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.IndexedSequenceValidity -/
section CUAdapterModule35
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Validity and decoding of indexed finite-sequence codes

The indexed representation is useful only if object-language predicates cannot
accept spurious infinite or non-functional graphs as finite programs.  This
file supplies a fixed first-order validity predicate and proves two
representation theorems:

* every genuine `sequenceCode xs` is valid;
* every valid code represents one actual finite Lean list.

The representing graph is allowed to contain irrelevant extra elements.  At
each index below the recorded length, however, it must contain exactly one
value. Every predicate consuming this representation inspects only those
indexed values, so this is the precise invariant required for sound decoding.
-/


universe u

namespace Constructible.IndexedSequenceZF

open FiniteSequenceZF

/-! ## Natural members of omega and finite ordinals -/





/-! ## The fixed first-order predicate -/









/-
Assignment layout in the innermost context:

`[omega, sequence, length, graph, index, value, other]`.
-/













/-! ## External representation and decoding -/









end Constructible.IndexedSequenceZF
end CUAdapterModule35


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackTrace -/
section CUAdapterModule36
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Finite execution traces for rudimentary stack programs

The object-language evaluator quantifies over a set-coded finite trace. This
file isolates the corresponding external machine theorem: successful
evaluation is equivalent to a finite chain of local `runStackToken` steps.
It also records constructibility of every state and of the indexed trace code.
-/


universe u v

namespace Constructible.Godel.RudimentaryTerm

/-! ## Recursive traces and their endpoint semantics -/















/-! ## Indexed characterization -/









/-! ## Constructibility of successful traces -/









end Constructible.Godel.RudimentaryTerm
end CUAdapterModule36


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackTraceDecode -/
section CUAdapterModule37
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Decoding raw formula-certified stack traces

Starting from a genuine input stack code, the one-step decoding theorem can
be iterated along raw token and state-code lists.  This reconstructs an actual
typed stack program and an `ExecutionTrace`.  Conversely, encoding any real
execution trace makes every adjacent triple satisfy `stackStepFormula`.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

open FiniteSequenceZF

noncomputable section



















end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule37


/- Original module: ConstructibleUniverse.ModelTheory.SetTheory.ZF -/
section CUAdapterModule38
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/


/-!
# The First-Order Theory ZF

This file defines the Zermelo--Fraenkel axioms in the first-order language of set theory.
The Separation and Replacement schemes range over all formulas in that language, with finitely
many free variables.

## Main definitions

- `FirstOrder.SetTheory.ZFAxiom` indexes the finite axioms and the two axiom schemes.
- `FirstOrder.SetTheory.ZFAxiom.toSentence` is the sentence associated with a ZF axiom.
- `FirstOrder.SetTheory.ZFAxiom.toProp` gives the usual semantics of each axiom.
- `FirstOrder.Language.Theory.ZF` is the first-order theory of ZF.
-/


universe u

namespace FirstOrder.SetTheory

open Language Language.BoundedFormula Language.Structure
open scoped FirstOrder



/-! The following relabellings make the de Bruijn variable order in the two schemes explicit. -/













































end FirstOrder.SetTheory
end CUAdapterModule38


/- Original module: ConstructibleUniverse.ModelTheory.SetTheory.ZFC -/
section CUAdapterModule39
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/


/-!
# The First-Order Theory ZFC

This file extends the first-order theory `Language.Theory.ZF` by the Axiom of Choice. We use the
standard disjoint-family formulation: every pairwise disjoint family of nonempty sets has a set
meeting each member of the family in exactly one element.

## Main definitions

- `FirstOrder.SetTheory.choiceSentence` is the Axiom of Choice in the language of set theory.
- `FirstOrder.SetTheory.ModelsChoice` is its usual disjoint-family semantics.
- `FirstOrder.Language.Theory.ZFC` is ZF together with `choiceSentence`.
- `FirstOrder.Language.Theory.model_ZFC_iff` characterizes models of ZFC.
-/


universe u

namespace FirstOrder.SetTheory

open Language Language.BoundedFormula Language.Structure
open scoped FirstOrder



















end FirstOrder.SetTheory
end CUAdapterModule39


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.BasicAxioms -/
section CUAdapterModule40
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The elementary set axioms in the constructible universe

This file records the axioms which follow immediately from transitivity and
the basic closure properties of `L`.  They are stated on `Model.LCarrier`, so
they connect directly to the sentences in the membership language.
-/


open Set

universe u

namespace Constructible.Model

















end Constructible.Model
end CUAdapterModule40


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Infinity -/
section CUAdapterModule41
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Infinity in the constructible universe

The standard von Neumann code `omega0.toZFSet` is constructible.  Its ordinal
membership characterization immediately gives the empty element and closure
under von Neumann successor.
-/


universe u

namespace Constructible.Model









end Constructible.Model
end CUAdapterModule41


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.PowerSet -/
section CUAdapterModule42
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The internal powerset axiom for the constructible universe

The ambient powerset of a constructible set need not itself be constructible.
The powerset computed by `L` contains exactly those ambient subsets which are
constructible.  We first bound all such subsets in one level and then define
the required collection over that level.

This is the standard inner-model proof using the ambient set
`P(a) intersect L`.  Here that ambient set is constructed by Mathlib's
predicate-valued `ZFSet.sep`.  The resulting membership theorem is exact, but
this operation should not be confused with an already formalized invocation
of an object-language formula defining `L` in an arbitrary ZFC model.
-/


open Set

universe u

namespace Constructible

section ZFC











end ZFC

end Constructible
end CUAdapterModule42


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Reflection -/
section CUAdapterModule43
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Formula reflection for the constructible hierarchy

For a fixed first-order formula and a starting level, this file constructs an
omega-chain of levels.  At every successor step, witnesses for all existential
subformulas with parameters in the current level are added.  The union level
is then closed under the relevant witnesses, so the Tarski--Vaught induction
shows that the formula has the same truth value there as in the full class
`L`.

The witness selector below lives in Lean's ambient classical metatheory.  It
is used only to obtain ordinal bounds in this semantic proof and is not an
internally represented choice function of `L`.  Consequently this file
implements the standard reflection argument for the concrete `ZFSet`
universe; it is not by itself a syntactic reflection proof over an arbitrary
model of ZF.
-/


open Set

universe u

namespace Constructible

section ZFC

open Model

































































end ZFC

end Constructible
end CUAdapterModule43


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Separation -/
section CUAdapterModule44
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Full Separation in the constructible universe

For a formula with constructible parameters and a constructible set `a`, a
reflecting level turns truth in the proper class `L` into ordinary
first-order truth over one internal stage.  The corresponding definable
subset of that stage lies in its `DefZF`; intersecting it with `a` gives the
required Separation set.
-/


open Set

universe u

namespace Constructible

section ZFC









end ZFC

end Constructible
end CUAdapterModule44


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Collection -/
section CUAdapterModule45
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Collection in the constructible universe

Ambient choice selects one constructible witness for each member of the
given internal set.  Since that index type is small, the occurrence levels of
all selected witnesses have a supremum.  The corresponding constructible
stage is itself an element of `L` and collects every selected witness.

The selected family is a function in Lean's classical metatheory, not a
function graph assumed to belong to `L`.  Thus there is no circular use of
the target Axiom of Choice.  A proof parameterized over arbitrary ZF models
would instead have to internalize the corresponding rank-bounding or
Collection argument.
-/


universe u

namespace Constructible

section ZFC







end ZFC

end Constructible
end CUAdapterModule45


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Replacement -/
section CUAdapterModule46
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Replacement in the constructible universe

Collection first gives a constructible set containing a value for every
input.  Full Separation then cuts out the exact range.  The formula
`replacementRangeFormula phi` expresses that its last variable is related by
`phi` to some member of the set parameter immediately preceding it.
-/


universe u

namespace Constructible

section ZFC

namespace Model



end Model

















end ZFC

end Constructible
end CUAdapterModule46


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.ZFModel -/
section CUAdapterModule47
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The constructible universe is a model of ZF

This file packages the closure, reflection, bounding, and ordinal results for
the constructible universe into Mathlib's canonical first-order theory of ZF.
The Separation and Replacement schemes range over every formula in
`FirstOrder.Language.setTheory`.
-/


universe u

namespace Constructible.Model



end Constructible.Model
end CUAdapterModule47


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Choice -/
section CUAdapterModule48
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The Axiom of Choice for the constructible universe

The canonical model-theoretic ZFC API supplies the disjoint-family formulation
of Choice. This file proves that a definable relation giving unique minima to
all nonempty constructible sets produces the required choice sets in `L`.
-/


universe u

namespace Constructible

namespace Model



end Model

namespace ChoiceSyntax

/-! ## Selecting minima -/









end ChoiceSyntax

namespace Model





end Model

end Constructible
end CUAdapterModule48


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



/-! ## Choice and ZFC -/





end Model

end Constructible
end CUAdapterModule49


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteOrdinalSuccessorFormula -/
section CUAdapterModule50
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A bounded formula for von Neumann successor

This file defines an arity-polymorphic bounded formula saying that one
coordinate is the von Neumann successor of another.  The formula is used for
the transition from index `k` to index `k + 1` in internally coded execution
traces.
-/


open Set

universe u

namespace Constructible

namespace Delta0Formula















end Delta0Formula

namespace FiniteSequenceZF













end FiniteSequenceZF

end Constructible
end CUAdapterModule50


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.IndexedSequenceOrderFormula -/
section CUAdapterModule51
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# First-order comparison of indexed finite-sequence codes

This file gives fixed object-language formulas for reading the indexed graph
stored by `IndexedSequenceZF.sequenceCode`, comparing prefixes, and building
shortlex comparisons. It uses the indexed representation throughout.
-/


universe u

namespace Constructible.IndexedSequenceZF

open FiniteSequenceZF

/-! ## Indexed access -/





















/-! ## Equal prefixes -/















/-! ## Shortlex -/









/-
For `tokenLt : FOFormula (parameterCount + 2)`, the two last coordinates are
the compared values.  The resulting shortlex formula has layout

`[token parameters..., omega, leftSequence, rightSequence]`.
-/











































end Constructible.IndexedSequenceZF
end CUAdapterModule51


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.IndexedSequenceLookup -/
section CUAdapterModule52
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Lookup semantics for represented indexed sequences

The access formula checks both that the requested index is below the recorded
length and that the corresponding graph pair is present.  Thus irrelevant
extra graph elements allowed by `Represents` cannot create out-of-range
lookups, and lookup is exactly equivalent to retrieving an entry of the
represented Lean list.
-/


universe u

namespace Constructible.IndexedSequenceZF

open FiniteSequenceZF











end Constructible.IndexedSequenceZF
end CUAdapterModule52


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackTraceStepFormula -/
section CUAdapterModule53
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# One indexed transition of a rudimentary stack trace

The outer assignment layout is

`[U, varTag, appTag, empty, op0, ..., op8, program, trace, index]`.

The formula appends witnesses `token`, `input`, `succ`, and `output`.  It reads
the token and input state at `index`, verifies that `succ` is the finite
ordinal successor of `index`, reads the output state at `succ`, and applies
`stackStepFormula` to the decoded transition.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

/-! ## Fixed coordinates and renamings -/













/-! ## Formula -/



















/-! ## Raw semantics -/





/-! ## Genuine indexed sequence codes -/







end Constructible.Godel.RudimentaryTerm
end CUAdapterModule53


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackProgramEvalFormula -/
section CUAdapterModule54
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A fixed first-order evaluator for postfix rudimentary programs

Evaluation is certified by an internally quantified finite sequence of stack
states.  Both program and trace satisfy the indexed-sequence validity
predicate; their recorded lengths differ by one; the first trace state is the
empty stack; the final state is the singleton result stack; and every program
index satisfies `traceStepFormula`.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF

/-! ## Fixed layout and renamings -/

/-
The free layout is

`[U,varTag,appTag,empty,op0,...,op8,omega,program,result]`.

Thus the three final indices are `13,14,15`.  The evaluator then quantifies
`trace, programLength, traceLength, finalStack`, at indices `16,...,19`.
-/



















/-! ## Formula -/











/-! ## Assignment computations -/

































/-! ## Raw semantic normal form -/



end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule54


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackTraceEndpoints -/
section CUAdapterModule55
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Endpoint semantics of raw formula-certified stack traces

For a genuine typed program, existence of a raw formula chain from the empty
stack code to the singleton output-stack code is exactly successful execution
of that program.  Soundness uses raw-chain decoding and injectivity of both
token and stack-state encodings; completeness encodes the canonical execution
trace of a successful run.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

open FiniteSequenceZF

noncomputable section



end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule55


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackProgramEvalSemantics -/
section CUAdapterModule56
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Semantic correctness of the fixed postfix-program evaluator

The evaluator accepts arbitrary indexed-sequence representations, not only
the canonical graph produced by `sequenceCode`. This ensures correctness when
program codes are quantified over by a first-order formula.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open FiniteSequenceZF
open IndexedSequenceZF











end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule56


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryTokenOrderFormula -/
section CUAdapterModule57
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A formula for the generator-token order

This file internalizes the variable-token branch of
`RudimentaryTerm.codeTokenRel`, where the distinguished generator `U` comes
first and ordinary generators are compared by membership of their Kuratowski
pair in an internal relation graph `r`.

The free-variable layout of `generatorTokenLtFormula` is

`[U, r, zeroTag, leftCode, rightCode]`.

The formula uses two unrestricted witnesses for the decoded generator
payloads.  All structural checks on those witnesses are bounded formulas.
For actual variable tokens, `zeroTag` is instantiated by the empty set, which
is both `varTag` and the third component of the token code.

`RudimentaryStackTokenOrderFormula` combines this branch with operation-token
and mixed-token comparisons to obtain the full token order.
-/


universe u

namespace Constructible.Godel

namespace RudimentaryTerm

noncomputable section

























end


end RudimentaryTerm

end Constructible.Godel
end CUAdapterModule57


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackTokenOrderFormula -/
section CUAdapterModule58
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A first-order formula for the postfix stack-token order

The free-variable layout of `stackTokenLtFormula` is

`[U, r, varTag, appTag, empty, leftCode, rightCode]`.

Two unrestricted witnesses decode the payloads of the two token codes.  The
bounded body is the disjunction of the three possible strict-order branches:

* two variable tokens, ordered by `generatorTokenRel U r`;
* a variable token followed by an operation token;
* two operation tokens, ordered by membership of their finite ordinal codes.

There is deliberately no operation-variable branch.  On genuine
`stackTokenZFCode`s, the formula is exactly `stackTokenRel
(generatorTokenRel U r)`.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

/-! ## Formula -/











/-! ## Exact semantics on genuine token codes -/





end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule58


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackProgramOrderFormula -/
section CUAdapterModule59
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A first-order Shortlex order on postfix stack-program codes

The generic indexed-sequence comparison formula is specialized to the fixed
stack-token formula.  The resulting object-language relation has exactly the
external `stackProgramRel` semantics on genuine program codes.
-/


universe u v

namespace Constructible

/-! ## Mapping lemmas for structural list orders -/





namespace Godel.RudimentaryTerm

noncomputable section

open IndexedSequenceZF

/-! ## The specialized formula -/







end

end Godel.RudimentaryTerm

end Constructible
end CUAdapterModule59


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackProgramOrderAbsolute -/
section CUAdapterModule60
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Absoluteness of the postfix-program order on genuine codes

`stackProgramLtFormula` contains unrestricted witnesses for decoded lengths,
graphs, entries, and token payloads.  Consequently it is not a bounded formula
and no blanket absoluteness theorem applies.  This file supplies constructible
witnesses for genuine program codes and proves the restricted semantics
directly.
-/


open Set

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open IndexedSequenceZF
open FiniteSequenceZF









/-! ## Component formulas over `LCarrier` -/

local notation "LMem" => Model.lCarrierMem





















/-! ## Token comparison over `LCarrier` -/









/-! ## Program comparison over `LCarrier` -/











end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule60


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackStepAbsolute -/
section CUAdapterModule61
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Absoluteness of one rudimentary stack-machine step

The ambient correctness theorem for `stackStepFormula` quantifies over all
`ZFSet`s.  This file packages its fixed assignment in `LCarrier` and proves
the corresponding correctness theorem when all stack entries are
constructible. The results are stated using both subtype semantics and the
raw-domain semantics `Model.SatisfiesIn L`.
-/


open Set

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section



















end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule61


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackProgramEvalAbsolute -/
section CUAdapterModule62
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Absoluteness of the fixed postfix-program evaluator

The ambient evaluator accepts arbitrary finite indexed codes.  For the
constructible universe we need more: every unbounded witness used by an
evaluation certificate must itself belong to `L`.  This file proves the
restricted semantics for genuine program codes by projecting restricted
certificates to the ambient universe and, conversely, by encoding the
canonical execution trace of a successful run.
-/


open Set

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF
open Constructible.FiniteSequenceZF

local notation "LMem" => Model.lCarrierMem





/-! ## One-way projection to the ambient universe -/



















/-! ## Genuine evaluator assignments -/





















/-! ## Constructible canonical traces -/

























































end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule62


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryParameters -/
section CUAdapterModule63
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Fixed parameters for constructible-stage histories

All local history rules share thirteen fixed constructible parameters.  The
remaining four coordinates are `(history, index, stage, relation)`.
-/


universe u

namespace Constructible.Model

noncomputable section























end

end Constructible.Model
end CUAdapterModule63


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryBaseFormula -/
section CUAdapterModule64
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The zero-state clause for constructible-stage histories

In the shared layout `(fixed13, history, index, stage, relation)`, the zero
rule requires all three state coordinates other than the ignored history to
be the empty set.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem





end

end Constructible.Model
end CUAdapterModule64


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.DefinableRelationGraph -/
section CUAdapterModule65
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Constructible graphs of definable relations

A binary relation given by one fixed first-order formula is not merely an
external Lean predicate.  On a constructible domain, Full Separation produces
an actual Kuratowski-pair graph which belongs to `L`.

The separating set is taken from a sufficiently large constructible stage.
This avoids assuming in advance that the ambient product `d x d` itself is
constructible.
-/


universe u

namespace Constructible

namespace Model





end Model

namespace DefinableRelationGraph

/-!
The input formula has layout `(params, x, y)`.  Under the two witnesses in
`graphFormula`, the larger layout is `(params, domain, pair, x, y)`.
-/



















end DefinableRelationGraph

namespace Model









end Model

end Constructible
end CUAdapterModule65


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryEntry -/
section CUAdapterModule66
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Constructible codes for stage-history entries

A stage history records triples `(index, stage, relation)`.  This file gives
the constructible triple code and a four-variable first-order lookup formula
whose semantics is exact in `LCarrier`.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem







/-!
The free-variable layout of `historyEntryFormula` is
`(history, index, stage, relation)`.  The existentially bound last variable
is the encoded triple itself.
-/



















end

end Constructible.Model
end CUAdapterModule66


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryLimitFormula -/
section CUAdapterModule67
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The limit-state clause for constructible-stage histories

At a limit index, both the stage and its coherent order graph are internal
unions of their earlier values.  The formulas here express those two
extensional union clauses using only membership and the verified history-entry
predicate.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-!
All formulas in this file have the outer layout
`(history, index, stage, relation)`.

After binding a candidate member `z`, the union witness layout is
`(history, index, stage, relation, z, earlierIndex, earlierStage,
earlierRelation)`.
-/















end

end Constructible.Model
end CUAdapterModule67


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalDefinableRelationGraph -/
section CUAdapterModule68
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Canonical graphs of formula-defined relations

The existential graph construction is sufficient for Separation, but a
transfinite recursion needs a graph uniquely determined by its inputs.  This
file separates directly inside the constructible Cartesian square and keeps
the resulting exact membership specification.
-/


universe u

namespace Constructible.Model

noncomputable section

/-! ## An object-language formula specifying the exact output graph -/

























end

end Constructible.Model
end CUAdapterModule68


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.InitialSegmentOrder -/
section CUAdapterModule69
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Extending a well-order by a final block

This file contains the order-theoretic device used to keep successive
constructible-stage orders coherent.  A carrier is split into an old part
and its complement.  The old part is ordered first, the new part second.
Thus the old part is an initial segment by construction.
-/


universe u

namespace Constructible

noncomputable section















end

end Constructible
end CUAdapterModule69


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryLeastProgramFormula -/
section CUAdapterModule70
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The least-successful-program order on rudimentary values

This file combines the fixed postfix-program evaluator with the fixed
Shortlex program order.  The free-variable layout is

`[U, varTag, appTag, empty, op0, ..., op8, omega, relation, left, right]`.

The first fifteen coordinates are parameters.  The final two coordinates are
the values being compared, so the formula can be passed directly to the
definable-relation graph construction.  Internally it says

`exists p, Eval(p, left) and forall q, Eval(q, right) -> ProgramLt(p, q)`.

When the program order is a well-order and both values have successful
programs, this is equivalent to comparing their least successful programs.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF

/-! ## Fixed layout and assignments -/











/-! ## Renamings -/









/-! ## Formula -/



/-! ## Assignment computations -/







/-! ## Ambient raw semantic normal form -/



end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule70


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackProgramOrderRepresented -/
section CUAdapterModule71
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Program order on arbitrary valid indexed representations

The first-order order formula compares the finite sequence represented by a
code.  It must therefore be insensitive to harmless extra graph entries in a
valid code, rather than being correct only for `sequenceCode` itself.
-/


open Set

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open IndexedSequenceZF
open FiniteSequenceZF

local notation "LMem" => Model.lCarrierMem





/-! ## Constructible witnesses for represented sequences -/



















/-! ## Restricted Shortlex on arbitrary representations -/









end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule71


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryLeastProgramSemantics -/
section CUAdapterModule72
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Semantics of the least-successful-program value order

The formula from `RudimentaryLeastProgramFormula` quantifies over arbitrary
set codes.  Evaluator satisfaction first decodes such a code to a genuine
postfix program; represented-code invariance of the program-order formula then
compares those decoded programs.  This proves that the formula is exactly the
existing `defCarrierStackRel` defined using `leastStackProgram`.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF

/-! ## Assignment compatibility -/



/-! ## Minimality of successful programs -/





/-! ## Exact ambient semantics -/



end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule72


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.MinimalStage -/
section CUAdapterModule73
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Minimal constructible stages

Every constructible set has a least stage at which it occurs.  That stage is
never zero or a limit, hence is a successor.  Its predecessor is the canonical
stage over which the set receives a `DefZF` (equivalently, Gödel-operation)
representation.
-/


open Set

universe u

namespace Constructible

































end Constructible
end CUAdapterModule73


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageOrder -/
section CUAdapterModule74
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# External birth-layer orders for constructible stages

This file decomposes each constructible stage into the disjoint layers of
sets born at earlier ordinals.  A well-order on each layer can then be combined
lexicographically and transported back to the stage carrier.

All orders in this file are external Lean relations.  No claim is made here
that their graphs are internally represented `ZFSet`s or belong to `L`.
-/


open Set

universe u v

namespace Constructible

/-! ## Birth layers -/





namespace BornAt













end BornAt





/-! ## The local least-term order -/





/-! ## Decomposing a stage by birth ordinal -/

















/-! ## Lexicographically combining external layer orders -/











end Constructible
end CUAdapterModule74


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalStageOrder -/
section CUAdapterModule75
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Canonical external orders on constructible stages

The order on a birth layer must use the already constructed order on the
preceding stage, rather than an unrelated application of external Choice.
This file performs that well-founded recursion on the birth ordinal.

The resulting relations are still external Lean predicates.  Their
Kuratowski-pair graphs must subsequently be shown constructible; no such
internalization claim is made here.
-/


open Set

universe u

namespace Constructible

/-! ## Adding the distinguished stage generator -/







/-! ## Simultaneous stage/layer recursion -/













end Constructible
end CUAdapterModule75


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryGeneratorInternalOrder -/
section CUAdapterModule76
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Generator orders from internally represented well-orders

An internal relation graph on a constructible set `U` orders
`Model.InternalCarrier U`, while rudimentary programs use
`ZFCarrier U.1` as their ordinary generator type.  These two carriers are
canonically equivalent.  This file transports the represented well-order
across that equivalence, adds the distinguished `none` generator at the
front, and finally lifts the order to postfix stack programs by Shortlex.
-/


universe u

namespace Constructible

namespace Godel

namespace RudimentaryTerm

noncomputable section

















end

end RudimentaryTerm

end Godel

end Constructible
end CUAdapterModule76


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentarySuccessfulProgramOrder -/
section CUAdapterModule77
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Ordering definable values by successful stack programs

This module gives a formula-independent presentation of the canonical order
on one Gödel-definability step. A value `x` precedes `y` when some program
evaluating to `x` precedes every program evaluating to `y`.  Once the
generator relation is a well-order, this is exactly the existing order by
least successful programs, `defCarrierStackRel`.
-/


universe u

namespace Constructible.Godel

namespace RudimentaryTerm

noncomputable section











end

end RudimentaryTerm

end Constructible.Godel
end CUAdapterModule77


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryLeastProgramAbsolute -/
section CUAdapterModule78
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Absoluteness of the least-successful-program value order

The combined least-program formula has unbounded program-code quantifiers.
This file proves its exact semantics in `Model.LCarrier`.  Arbitrary internal
codes are projected to the ambient evaluator and decoded; canonical codes
supply the converse witnesses.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF

local notation "LMem" => Model.lCarrierMem

/-! ## Constructible assignments -/













/-! ## Constructible values of the definability step -/







/-! ## Exact restricted semantics -/





end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule78


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



















/-! ## Alternative conditional birth-layer route

This section gives a conditional reduction through an externally specified
birth-layer order. The model theorem in `StageHistoryGraphSystem.lean` is
independent of this interface and constructs coherent internal graphs through
stage histories.
-/











end Model

end Constructible
end CUAdapterModule79


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentarySuccessorInternalOrder -/
section CUAdapterModule80
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Internally represented well-orders of successor stages

Assume an actual constructible graph internally well-orders `L_alpha`.
The fixed least-successful-program formula then well-orders
`L_(alpha+1) = Def(L_alpha)`.  Full Separation turns that formula-defined
relation into an actual Kuratowski graph belonging to `L`.
-/


universe u

namespace Constructible

namespace Model

noncomputable section



















end

end Model

end Constructible
end CUAdapterModule80


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentarySuccessorExtensionOrder -/
section CUAdapterModule81
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Coherent internally represented successor-stage orders

The raw least-program order need not extend the order on the previous stage.
For limit unions we instead put the old stage first, preserving its given
relation, and order only the genuinely new values by least successful
programs.  The old stage is therefore an initial segment by construction.
-/


universe u

namespace Constructible

namespace Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## The fixed extension formula -/

















/-! ## The corresponding external block order -/

















/-! ## Formula semantics and internalization -/













end

end Model

end Constructible
end CUAdapterModule81


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalSuccessorOrder -/
section CUAdapterModule82
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The canonical coherent successor-stage order

The successor extension formula determines an exact graph by Separation in
the constructible Cartesian square.  Unlike an existential graph witness,
this graph is a genuine function of the preceding stage and relation, which
is the form used by the transfinite recursion.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

















end

end Constructible.Model
end CUAdapterModule82


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryDefOutputFormula -/
section CUAdapterModule83
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A first-order output formula for one Gödel definability step

The fixed stack evaluator recognizes the rudimentary closure of `U`.  Adding
the bounded requirement that the output be a subset of `U` therefore gives a
single first-order definition of `godelDef U`.  This file packages that
definition with an exact `LCarrier` semantics and the unique-output interface
needed by function-form Replacement.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## Successful programs land in the rudimentary closure -/







/-! ## The fixed output formula -/

/-
The outer free-variable layout is

`[U,varTag,appTag,empty,op0,...,op8,omega,nextU]`.

After universally binding `result` and existentially binding `program`, the
evaluator expects `program` before `result`.  The following renaming swaps
those two final coordinates and skips `nextU`.
-/













/-! ## Exactness and uniqueness -/









end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule83


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.SuccessorStageStateFormula -/
section CUAdapterModule84
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A deterministic first-order successor step for stage/order states

A recursion state consists of a constructible domain `U` and a constructible
relation graph `oldRelation`.  Its successor consists of `nextU = godelDef U`
and the canonical graph selected by the coherent successor-order formula on
`nextU`.  Both outputs are specified by one fixed first-order formula.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## Formula and assignments -/

/-
The combined layout is

`[U,varTag,appTag,empty,op0,...,op8,omega,oldRelation,nextU,nextRelation]`.

The `godelDef` output formula omits coordinates `oldRelation` and
`nextRelation`; its final output coordinate is therefore sent to `nextU`.
-/











/-! ## Exact semantics -/





/-! ## Functionality and existence -/







end

end Constructible.Model
end CUAdapterModule84


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistorySuccessorFormula -/
section CUAdapterModule85
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The successor-state clause for constructible-stage histories

The outer layout is `(fixed13, history, index, stage, relation)`.  Three
existential witnesses append `(predecessorIndex, predecessorStage,
predecessorRelation)`.  The existing deterministic successor-state formula
is then renamed into this combined context.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem





















































end

end Constructible.Model
end CUAdapterModule85


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryFunctionality -/
section CUAdapterModule86
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Functionality of stage-history lookup

A stage history is functional at an index when it contains exactly one pair
of stage and relation coordinates at that index.  The formula in this file
expresses that property entirely in the first-order membership language.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-!
The free-variable layout is `(history, index)`.  The first two existential
variables are `(stage, relation)`.  Inside the two universal quantifiers the
layout is

`(history, index, stage, relation, otherStage, otherRelation)`.
-/















end

end Constructible.Model
end CUAdapterModule86


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.ValidStageHistoryFormula -/
section CUAdapterModule87
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A fixed validity formula for constructible-stage histories

The local rule combines the zero, successor, and nonzero-limit clauses in the
shared seventeen-coordinate layout

`(fixed13, history, index, stage, relation)`.

The global validity formula has layout `(fixed13, history, bound)`.  It says
that every index at most `bound` has exactly one history entry, and that its
stage and relation coordinates obey the appropriate local rule.  As in the
indexed-sequence validity predicate, irrelevant extra members of the history
set are permitted; every lookup uses only the total functional part below the
stated bound.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## The unified local rule -/





























/-! ## Total functional validity through a bound -/













































end

end Constructible.Model
end CUAdapterModule87


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryOrdinal -/
section CUAdapterModule88
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Constructible ordinal indices for stage histories

Every ambient ordinal has a canonical von Neumann code in `L`.  Packaging
that code once keeps the history and Replacement interfaces on `LCarrier`.
-/


universe u

namespace Constructible.Model

noncomputable section



















end

end Constructible.Model
end CUAdapterModule88


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageStateAtFormula -/
section CUAdapterModule89
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Fixed output formulas for constructible-stage recursion

The formulas in this file hide a valid history witness and expose the forms
needed by Replacement.  Their thirteen leading coordinates are always the
fixed evaluator parameters.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## A stage/relation state at one index -/































/-! ## A relation-only output for Replacement -/





















/-! ## A canonical triple output for Replacement -/



























end

end Constructible.Model
end CUAdapterModule89


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryOperations -/
section CUAdapterModule90
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Internal operations on constructible stage histories

A history is an actual member of `L`, not an external Lean set.  This file
constructs the internal operation which adjoins one canonical triple and
records its exact lookup behavior.
-/


universe u

namespace Constructible.Model

noncomputable section















end

end Constructible.Model
end CUAdapterModule90


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryReplacement -/
section CUAdapterModule91
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Internal replacement families for constructible-stage recursion

Assuming that every earlier ordinal index has a unique stage/relation state,
the fixed formulas from `StageStateAtFormula` turn the earlier history entries
and relation graphs into actual members of `L` by Replacement.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

























end

end Constructible.Model
end CUAdapterModule91


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageStateUniqueness -/
section CUAdapterModule92
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Uniqueness of ordinal-indexed stage states

The local history rule is deterministic on canonical ordinal indices.  This
file first normalizes the zero, successor, and limit cases, then uses ordinal
induction to compare states coming from different valid internal histories.
-/


universe u

namespace Constructible.Model

noncomputable section



























end

end Constructible.Model
end CUAdapterModule92


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryRecursion -/
section CUAdapterModule93
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Internal transfinite recursion of constructible-stage histories

At every ordinal this file constructs an actual `LCarrier` history together
with its top relation.  The history is valid through the canonical ordinal
index, and its top stage coordinate is exactly `stageLCarrier ordinal`.
-/


universe u

namespace Constructible.Model

noncomputable section











































end

end Constructible.Model
end CUAdapterModule93


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.CoherentLimitOrder -/
section CUAdapterModule94
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Coherent unions of internally represented stage orders

At a limit stage, a union of arbitrary external well-orders is not enough.
This file records the exact coherence and initial-segment hypotheses under
which the union relation well-orders the limit carrier.  If the family of
graphs is itself represented by a constructible set, its internal union is
then the required graph in `L`.
-/


open Set

universe u

namespace Constructible.Model

noncomputable section















/-! ## Internalizing the union graph -/







/-! ## Retaining coherence after the limit step -/







end

end Constructible.Model
end CUAdapterModule94


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageZeroInternalOrder -/
section CUAdapterModule95
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The internally represented order on the zero constructible stage

The carrier of `L_0` is empty, so the empty constructible set represents its
unique strict well-order.
-/


universe u

namespace Constructible.Model



end Constructible.Model
end CUAdapterModule95


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



















/-! ## The zero and successor extensions -/















end

end Constructible.Model
end CUAdapterModule96


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryCoherence -/
section CUAdapterModule97
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Coherence of the internally recursive stage graphs

The relation coordinate of `stageHistoryData` is now assembled into a graph
system.  Successors use the canonical extension theorem and limits use the
internally represented relation family constructed by Replacement.
-/


universe u

namespace Constructible.Model

noncomputable section













end

end Constructible.Model
end CUAdapterModule97


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













end

end Constructible.Model
end CUAdapterModule98



/-! # Bridge to the existing Prove2Me constructible universe -/




end GCHSource_Work_ConstructibleGCH_ReuseBase

/- Source module: Solutions.Work_CUGCH_FiniteFragmentElementarity -/
section GCHSource_Work_CUGCH_FiniteFragmentElementarity
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Elementarity for a finite formula fragment

This file isolates the Tarski--Vaught argument needed by the later Skolem-hull
and condensation construction.  For one fixed formula, `ClosesWithin` asks a
smaller carrier to contain witnesses for every existential subformula, with
parameters from the smaller carrier.  This finite closure condition is enough
to make satisfaction of the formula absolute between the two carriers.

Unlike a full elementary-substructure predicate, this construction does not
quantify over or encode all first-order formulas.  That distinction matters
for the cardinality-controlled hull used in the proof of GCH in `L`.
-/

section

open Set

universe u

namespace Constructible

section ZFC







/-! ## The extensionality fragment -/





/--
Closure under the single distinguishing-member formula makes membership on
`small` extensional, provided `big` is transitive.  This is the exact
extensionality input required for the Mostowski collapse of a finite-fragment
Skolem hull.
-/
private theorem restricted_extensionality_of_closesWithin
    {small big : Set ZFSet.{u}}
    (hsubset : small ⊆ big)
    (htrans : forall x : ZFSet.{u}, x ∈ big ->
      forall z : ZFSet.{u}, z ∈ x -> z ∈ big)
    (hclose : ClosesWithin small big distinguishingMemberFormula)
    {x y : ZFSet.{u}} (hx : x ∈ small) (hy : y ∈ small)
    (hsame : forall z : ZFSet.{u}, z ∈ small -> (z ∈ x <-> z ∈ y)) :
    x = y := by
  by_contra hxy
  have hdifference :
      exists z : ZFSet.{u}, (z ∈ x /\ z ∉ y) \/ (z ∈ y /\ z ∉ x) := by
    by_contra hnone
    apply hxy
    apply ZFSet.ext
    intro z
    by_contra hnotIff
    apply hnone
    by_cases hzx : z ∈ x
    · exact ⟨z, Or.inl ⟨hzx, fun hzy => hnotIff (iff_of_true hzx hzy)⟩⟩
    · have hzy : z ∈ y := by
        by_contra hzy
        exact hnotIff (iff_of_false hzx hzy)
      exact ⟨z, Or.inr ⟨hzy, hzx⟩⟩
  rcases hdifference with ⟨z, hdiff⟩
  have hzBig : z ∈ big := by
    rcases hdiff with hleft | hright
    · exact htrans x (hsubset hx) z hleft.1
    · exact htrans y (hsubset hy) z hright.1
  have hbigExists :
      Model.SatisfiesIn big distinguishingMemberFormula ![x, y] := by
    rw [satisfiesIn_distinguishingMemberFormula]
    exact ⟨z, hzBig, hdiff⟩
  have hparams : forall i, ![x, y] i ∈ small := by
    intro i
    fin_cases i <;> assumption
  rcases hclose.2 ![x, y] hparams hbigExists with
    ⟨w, hwSmall, hwFormula⟩
  have hwdiff : (w ∈ x /\ w ∉ y) \/ (w ∈ y /\ w ∉ x) := by
    classical
    simp only [Model.SatisfiesIn,
      FOFormula.disj, snoc_last, snoc_castSucc,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hwFormula
    tauto
  rcases hwdiff with hleft | hright
  · exact hleft.2 ((hsame w hwSmall).mp hleft.1)
  · exact hright.2 ((hsame w hwSmall).mpr hright.1)

end ZFC

end Constructible

end
end GCHSource_Work_CUGCH_FiniteFragmentElementarity

/- Source module: Solutions.Work_CUGCH_FiniteFragmentSkolemHull -/
section GCHSource_Work_CUGCH_FiniteFragmentSkolemHull
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/







/-!
# Full elementarity and internally represented omega unions

The first part of this file upgrades the one-formula Tarski--Vaught interface
from `FiniteFragmentElementarity` to an external quantification over every
first-order formula.  This is the elementarity notion required by a genuine
Mostowski condensation theorem; closure under one fixed finite fragment is
not substituted for full elementarity.

The second part isolates the internal set construction used by a Skolem-hull
argument.  If one fixed first-order formula uniformly defines an omega-indexed
family of constructible sets, Replacement produces an actual member of `L`
whose members are precisely that family.  Its union is therefore an actual
`ZFSet` in `L`, rather than an external `Set ZFSet`.

This file deliberately does not assert that the full Skolem iteration has
already been constructed.  The implication from closure under all
rudimentary relation sets to elementarity is useful as a semantic comparison,
but that closure predicate is too strong for a cardinal-controlled hull:
nullary singleton relations force the smaller carrier to contain all of `U`.
Consequently a genuine Skolem construction must enumerate only the compiled
relations of first-order formulas; it must not iterate the unrestricted
predicate below.
-/

section

open Set

universe u

namespace Constructible

section ZFC

/-! ## Full Tarski--Vaught closure -/







/-- If satisfaction of every formula is absolute, then `small` contains the
required Tarski--Vaught witnesses for every existential subformula. -/
private theorem closesWithinAll_of_satisfactionAbsolute
    {small big : Set ZFSet.{u}}
    (habsolute : SatisfactionAbsolute small big) :
    ClosesWithinAll small big := by
  intro n phi
  induction phi with
  | mem i j => trivial
  | eq i j => trivial
  | neg phi ih => exact ih
  | conj phi psi ihPhi ihPsi => exact ⟨ihPhi, ihPsi⟩
  | ex phi ih =>
      refine ⟨ih, ?_⟩
      intro s hs hbig
      have hsmall : Model.SatisfiesIn small (.ex phi) s :=
        (habsolute (.ex phi) s hs).mpr hbig
      rcases hsmall with ⟨x, hxSmall, hxFormula⟩
      refine ⟨x, hxSmall, ?_⟩
      apply (habsolute phi (snoc s x) ?_).mp hxFormula
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hxSmall
      · simpa using hs j



/-- Full witness closure supplies the extensionality needed for a Mostowski
collapse whenever the ambient carrier is transitive. -/
private theorem restricted_extensionality_of_closesWithinAll
    {small big : Set ZFSet.{u}}
    (hsubset : small ⊆ big)
    (htrans : forall x : ZFSet.{u}, x ∈ big ->
      forall z : ZFSet.{u}, z ∈ x -> z ∈ big)
    (hclose : ClosesWithinAll small big)
    {x y : ZFSet.{u}} (hx : x ∈ small) (hy : y ∈ small)
    (hsame : forall z : ZFSet.{u}, z ∈ small -> (z ∈ x <-> z ∈ y)) :
    x = y :=
  restricted_extensionality_of_closesWithin hsubset htrans
    (hclose distinguishingMemberFormula) hx hy hsame

/-! ## Full formula closure through rudimentary relation sets -/







/-! ## A uniform omega-indexed Replacement interface -/

namespace Model

open FiniteSequenceZF

local notation "LMem" => lCarrierMem























end Model

end ZFC

end Constructible

end
end GCHSource_Work_CUGCH_FiniteFragmentSkolemHull

/- Source module: Solutions.Work_CUGCH_MostowskiCollapse -/
section GCHSource_Work_CUGCH_MostowskiCollapse
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Mostowski collapse for set-sized membership structures

This file develops the external collapse of membership restricted to a
`ZFSet`.  The recursion is along genuine well-founded membership, while each
recursive image is again packaged as a `ZFSet`.
-/

section

universe u

namespace Constructible.MostowskiCollapse

noncomputable section









/-- The range of the collapse is transitive, independently of
extensionality of the restricted structure. -/
private theorem range_isTransitive (domain : ZFSet.{u}) :
    (range domain).IsTransitive := by
  intro z hz w hw
  rcases mem_range_iff.mp hz with ⟨x, hxdomain, rfl⟩
  rcases mem_collapse_iff.mp hw with
    ⟨y, _hyx, hydomain, hvalue⟩
  exact mem_range_iff.mpr ⟨y, hydomain, hvalue⟩



























end

end Constructible.MostowskiCollapse

end
end GCHSource_Work_CUGCH_MostowskiCollapse

/- Source module: Solutions.Work_CUGCH_MostowskiElementarity -/
section GCHSource_Work_CUGCH_MostowskiElementarity
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Satisfaction through the Mostowski collapse

The Mostowski collapse is not used only as an extensional membership
isomorphism here.  This file proves, by induction on the complete independent
syntax `FOFormula`, that the collapse preserves satisfaction of every formula.
Consequently a fully elementary set-sized hull and its transitive collapse
have exactly the same first-order theory with corresponding parameters.
-/

section

universe u

namespace Constructible.MostowskiCollapse

noncomputable section

private theorem equivRange_comp_snoc
    {domain : ZFSet.{u}} (hextensional : IsExtensional domain)
    {n : Nat}
    (s : Tuple {x : ZFSet.{u} // x ∈ domain} n)
    (x : {x : ZFSet.{u} // x ∈ domain}) :
    (fun i => equivRange hextensional (snoc s x i)) =
      snoc (fun i => equivRange hextensional (s i))
        (equivRange hextensional x) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [snoc_last]
  · simp only [snoc_castSucc]

/-- The Mostowski equivalence preserves satisfaction of every first-order
formula, not merely atomic membership. -/
private theorem satisfies_equivRange_iff
    {domain : ZFSet.{u}} (hextensional : IsExtensional domain)
    {n : Nat} (phi : FOFormula n)
    (s : Tuple {x : ZFSet.{u} // x ∈ domain} n) :
    FOFormula.Satisfies
        (fun x y : {x : ZFSet.{u} // x ∈ domain} => x.1 ∈ y.1)
        phi s ↔
      FOFormula.Satisfies
        (fun x y : {x : ZFSet.{u} // x ∈ range domain} => x.1 ∈ y.1)
        phi (fun i => equivRange hextensional (s i)) := by
  induction phi with
  | mem i j =>
      exact (equivRange_mem_iff hextensional (s i) (s j)).symm
  | eq i j =>
      constructor
      · intro h
        exact congrArg (equivRange hextensional) h
      · intro h
        exact (equivRange hextensional).injective h
  | neg phi ih =>
      exact not_congr (ih s)
  | conj phi psi ihPhi ihPsi =>
      exact and_congr (ihPhi s) (ihPsi s)
  | ex phi ih =>
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨equivRange hextensional x, ?_⟩
        have hmapped := (ih (snoc s x)).mp hx
        simpa only [equivRange_comp_snoc] using hmapped
      · rintro ⟨z, hz⟩
        let x := (equivRange hextensional).symm z
        refine ⟨x, ?_⟩
        apply (ih (snoc s x)).mpr
        have hmapX : equivRange hextensional x = z := by
          exact (equivRange hextensional).apply_symm_apply z
        simpa only [equivRange_comp_snoc, hmapX] using hz

/-- Raw-value form of `satisfies_equivRange_iff`.  The tuple on the right is
obtained by applying the collapse to every entry of the tuple on the left. -/
private theorem satisfiesIn_collapse_iff
    {domain : ZFSet.{u}} (hextensional : IsExtensional domain)
    {n : Nat} (phi : FOFormula n)
    (s : Tuple {x : ZFSet.{u} // x ∈ domain} n) :
    Model.SatisfiesIn (domain : Set ZFSet.{u}) phi
        (fun i => (s i).1) ↔
      Model.SatisfiesIn (range domain : Set ZFSet.{u}) phi
        (fun i => collapse domain (s i).1) := by
  have hdomain := Model.satisfies_subtype_iff_satisfiesIn
    (domain : Set ZFSet.{u}) phi s
  let mapped : Tuple {z : ZFSet.{u} // z ∈ range domain} n :=
    fun i => equivRange hextensional (s i)
  have hrange := Model.satisfies_subtype_iff_satisfiesIn
    (range domain : Set ZFSet.{u}) phi mapped
  have hisomorphism := satisfies_equivRange_iff hextensional phi s
  constructor
  · intro h
    have hsource := hdomain.mpr h
    have htarget := hisomorphism.mp hsource
    have hraw := hrange.mp htarget
    simpa only [mapped, equivRange_apply] using hraw
  · intro h
    apply hdomain.mp
    apply hisomorphism.mpr
    apply hrange.mpr
    simpa only [mapped, equivRange_apply] using h



end

end Constructible.MostowskiCollapse

end
end GCHSource_Work_CUGCH_MostowskiElementarity

/- Source module: Solutions.Work_CUGCH_DefZFCollapse -/
section GCHSource_Work_CUGCH_DefZFCollapse
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Definability and the Mostowski collapse

This file proves the successor-step compatibility needed by constructible
condensation.  If a set-sized membership structure is fully elementary in a
transitive ambient set, then its Mostowski collapse commutes with `DefZF` on
every argument for which both the argument and its definable powerset belong
to the small structure.

The finite tuple of parameters occurring in the definition of a subset is
not assumed to lie in the small structure.  Instead it is bound in one
first-order formula.  Full elementarity pulls witnesses into the small
structure, after which invariance of satisfaction under the collapse applies.
-/

section

open Set

universe u

namespace Constructible

noncomputable section

namespace Model











/-- Relativizing every quantifier to `a` inside a class `M` is satisfaction
over the external intersection `M ∩ a`. -/
private theorem satisfiesIn_toFO_relativize_iff (M : Set ZFSet.{u})
    (a : ZFSet.{u}) {n : Nat} (phi : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (Delta0Formula.relativize phi).toFO
        (tupleCons a s) <->
      SatisfiesIn (M ∩ (a : Set ZFSet.{u})) phi s := by
  induction phi with
  | mem i j => rfl
  | eq i j => rfl
  | neg phi ih =>
      simpa [Delta0Formula.relativize, Delta0Formula.toFO] using
        not_congr (ih s)
  | conj phi psi ihPhi ihPsi =>
      simpa [Delta0Formula.relativize, Delta0Formula.toFO] using
        and_congr (ihPhi s) (ihPsi s)
  | ex phi ih =>
      simp only [Delta0Formula.relativize, Delta0Formula.toFO,
        FOFormula.boundedEx, SatisfiesIn, snoc_tupleCons, ih,
        tupleCons_zero, snoc_last, snoc_castSucc]
      constructor
      · rintro ⟨x, hxM, hxa, hx⟩
        exact ⟨x, ⟨hxM, hxa⟩, hx⟩
      · rintro ⟨x, ⟨hxM, hxa⟩, hx⟩
        exact ⟨x, hxM, hxa, hx⟩

/-- In a transitive ambient set containing `a`, the intersection in the
previous theorem is exactly the genuine carrier of `a`. -/
private theorem satisfiesIn_toFO_relativize_of_isTransitive
    {M a : ZFSet.{u}} (hM : M.IsTransitive) (ha : a ∈ M)
    {n : Nat} (phi : FOFormula n) (s : Tuple (ZFCarrier a) n) :
    SatisfiesIn (M : Set ZFSet.{u})
        (Delta0Formula.relativize phi).toFO
        (tupleCons a (Delta0Formula.val s)) <->
      FOFormula.Satisfies (zfCarrierMem a) phi s := by
  rw [satisfiesIn_toFO_relativize_iff]
  have hinter : (M : Set ZFSet.{u}) ∩ (a : Set ZFSet.{u}) =
      (a : Set ZFSet.{u}) := by
    ext x
    constructor
    · exact fun hx => hx.2
    · intro hxa
      exact ⟨hM.mem_trans hxa ha, hxa⟩
  rw [hinter]
  exact (satisfies_subtype_iff_satisfiesIn
    (a : Set ZFSet.{u}) phi s).symm

end Model

/-! ## One formula saying that a set is a definable section -/



private theorem sectionRelativizeRename_assignment {n : Nat}
    (a y x : ZFSet.{u}) (s : Tuple ZFSet.{u} n) :
    (fun i =>
      snoc (tupleCons a (tupleCons y s)) x
        (sectionRelativizeRename i)) =
      tupleCons a (snoc s x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [sectionRelativizeRename]
  · simp [sectionRelativizeRename]



/-- Exact semantics of `subsetDefinitionFormula` in a transitive ambient
set. -/
private theorem satisfiesIn_subsetDefinitionFormula_iff
    {M a y : ZFSet.{u}} (hM : M.IsTransitive) (ha : a ∈ M)
    {n : Nat} (phi : FOFormula (n + 1))
    (s : Tuple (ZFCarrier a) n) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        (subsetDefinitionFormula phi)
        (tupleCons a (tupleCons y (Delta0Formula.val s))) <->
      ∀ x : ZFCarrier a,
        x.1 ∈ y <->
          FOFormula.Satisfies (zfCarrierMem a) phi (snoc s x) := by
  classical
  simp only [subsetDefinitionFormula, Model.satisfiesIn_boundedAll_iff,
    Model.satisfiesIn_biimp_iff, Model.SatisfiesIn,
    snoc_last, snoc_castSucc, tupleCons_zero,
    Model.satisfiesIn_rename, sectionRelativizeRename_assignment]
  constructor
  · intro h x
    have hxM : x.1 ∈ M := hM.mem_trans x.2 ha
    have hx := h x.1 hxM x.2
    change x.1 ∈ y <->
      Model.SatisfiesIn (M : Set ZFSet.{u})
        (Delta0Formula.relativize phi).toFO
        (tupleCons a (snoc (Delta0Formula.val s) x.1)) at hx
    have hrel := Model.satisfiesIn_toFO_relativize_of_isTransitive
      hM ha phi (snoc s x)
    have hrel' :
        Model.SatisfiesIn (M : Set ZFSet.{u})
          (Delta0Formula.relativize phi).toFO
          (tupleCons a (snoc (Delta0Formula.val s) x.1)) <->
        FOFormula.Satisfies (zfCarrierMem a) phi (snoc s x) := by
      simpa only [Delta0Formula.val_snoc] using hrel
    exact hx.trans hrel'
  · intro h x hxM hxa
    let xa : ZFCarrier a := ⟨x, hxa⟩
    change x ∈ y <->
      Model.SatisfiesIn (M : Set ZFSet.{u})
        (Delta0Formula.relativize phi).toFO
        (tupleCons a (snoc (Delta0Formula.val s) x))
    have hrel := Model.satisfiesIn_toFO_relativize_of_isTransitive
      hM ha phi (snoc s xa)
    have hrel' :
        Model.SatisfiesIn (M : Set ZFSet.{u})
          (Delta0Formula.relativize phi).toFO
          (tupleCons a (snoc (Delta0Formula.val s) x)) <->
        FOFormula.Satisfies (zfCarrierMem a) phi (snoc s xa) := by
      simpa only [xa, Delta0Formula.val_snoc] using hrel
    exact (h xa).trans hrel'.symm

/-! ## Binding all finite parameters in one object-language formula -/



private theorem tuple_snoc_eta {A : Type u} {n : Nat}
    (s : Tuple A (n + 1)) :
    snoc (fun i => s i.castSucc) (s (Fin.last n)) = s := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- Semantics of binding a finite tail of parameters. -/
private theorem satisfiesIn_boundedExistsTail_iff
    (M : Set ZFSet.{u}) (a y : ZFSet.{u}) {n : Nat}
    (phi : FOFormula (n + 2)) :
    Model.SatisfiesIn M (boundedExistsTail n phi) ![a, y] <->
      ∃ s : Tuple ZFSet.{u} n,
        (∀ i, s i ∈ M ∧ s i ∈ a) ∧
        Model.SatisfiesIn M phi
          (tupleCons a (tupleCons y s)) := by
  induction n with
  | zero =>
      rw [boundedExistsTail]
      constructor
      · intro h
        refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
        · intro i
          exact Fin.elim0 i
        · convert h using 1
          funext i
          fin_cases i <;> rfl
      · rintro ⟨s, _hs, h⟩
        convert h using 1
        funext i
        fin_cases i <;> rfl
  | succ n ih =>
      rw [boundedExistsTail]
      rw [ih]
      simp only [Model.satisfiesIn_boundedEx_iff, tupleCons_zero]
      constructor
      · rintro ⟨s, hs, x, hxM, hxa, hx⟩
        refine ⟨snoc s x, ?_, ?_⟩
        · intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using And.intro hxM hxa
          · simpa using hs j
        · simpa only [snoc_tupleCons] using hx
      · rintro ⟨s, hs, hphi⟩
        let pref : Tuple ZFSet.{u} n := fun i => s i.castSucc
        let x : ZFSet.{u} := s (Fin.last n)
        refine ⟨pref, ?_, x, ?_, ?_, ?_⟩
        · intro i
          exact hs i.castSucc
        · exact (hs (Fin.last n)).1
        · exact (hs (Fin.last n)).2
        · have heta : snoc pref x = s := tuple_snoc_eta s
          simpa only [snoc_tupleCons, heta, pref, x] using hphi



/-! ## Asking for a defined subset inside `DefZF a` -/



private theorem definedSubsetWitnessRename_assignment {n : Nat}
    (a d y : ZFSet.{u}) (s : Tuple ZFSet.{u} n) :
    (fun i =>
      snoc (tupleCons a (tupleCons d s)) y
        (definedSubsetWitnessRename i)) =
      tupleCons a (tupleCons y s) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [definedSubsetWitnessRename]
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp only [definedSubsetWitnessRename, Fin.cases_succ,
        Fin.cases_zero, snoc_last, tupleCons_succ, tupleCons_zero]
    · simp [definedSubsetWitnessRename]



private theorem satisfiesIn_existsDefinedSubsetFormula_iff
    (M : Set ZFSet.{u}) (a d : ZFSet.{u}) {n : Nat}
    (phi : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (existsDefinedSubsetFormula phi)
        (tupleCons a (tupleCons d s)) <->
      ∃ y : ZFSet.{u}, y ∈ M ∧ y ∈ d ∧
        Model.SatisfiesIn M (subsetDefinitionFormula phi)
          (tupleCons a (tupleCons y s)) := by
  simp only [existsDefinedSubsetFormula,
    Model.satisfiesIn_boundedEx_iff, Model.satisfiesIn_rename,
    definedSubsetWitnessRename_assignment]
  change (∃ y : ZFSet.{u}, y ∈ M ∧ y ∈ d ∧
      Model.SatisfiesIn M (subsetDefinitionFormula phi)
        (tupleCons a (tupleCons y s))) <-> _
  rfl

namespace MostowskiCollapse

/-- Raw-tuple form of satisfaction invariance under the collapse. -/
private theorem satisfiesIn_collapse_iff_raw {domain : ZFSet.{u}}
    (hextensional : IsExtensional domain) {n : Nat}
    (phi : FOFormula n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ domain) :
    Model.SatisfiesIn (domain : Set ZFSet.{u}) phi s <->
      Model.SatisfiesIn (range domain : Set ZFSet.{u}) phi
        (fun i => collapse domain (s i)) := by
  let sDomain : Tuple {x : ZFSet.{u} // x ∈ domain} n :=
    fun i => ⟨s i, hs i⟩
  simpa only [sDomain] using
    (satisfiesIn_collapse_iff hextensional phi sDomain)

/-- A section definition whose parameters belong to the collapse domain
transports to the corresponding section definition over the collapsed bound.
-/
private theorem exists_collapsedParameters_section
    {domain a y : ZFSet.{u}} (hextensional : IsExtensional domain)
    (ha : a ∈ domain) (hy : y ∈ domain)
    {n : Nat} (phi : FOFormula (n + 1))
    (s : Tuple (ZFCarrier a) n)
    (hs : ∀ i, (s i).1 ∈ domain)
    (hsection :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        (subsetDefinitionFormula phi)
        (tupleCons a (tupleCons y (Delta0Formula.val s)))) :
    ∃ collapsedParams : Tuple (ZFCarrier (collapse domain a)) n,
      (∀ i, (collapsedParams i).1 = collapse domain (s i).1) ∧
      (∀ x : ZFCarrier (collapse domain a),
        x.1 ∈ collapse domain y <->
          FOFormula.Satisfies
            (zfCarrierMem (collapse domain a)) phi
            (snoc collapsedParams x)) := by
  let collapsedParams : Tuple (ZFCarrier (collapse domain a)) n :=
    fun i => ⟨collapse domain (s i).1,
      mem_collapse_iff.mpr ⟨(s i).1, (s i).2, hs i, rfl⟩⟩
  have hentries :
      ∀ i, tupleCons a (tupleCons y (Delta0Formula.val s)) i ∈ domain := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [tupleCons_zero] using ha
    · refine Fin.cases ?_ (fun k => ?_) j
      · simpa only [tupleCons_succ, tupleCons_zero] using hy
      · simp only [tupleCons_succ]
        exact hs k
  have hcollapsed :=
    (satisfiesIn_collapse_iff_raw hextensional
      (subsetDefinitionFormula phi)
      (tupleCons a (tupleCons y (Delta0Formula.val s))) hentries).mp
      hsection
  have hassignment :
      (fun i => collapse domain
        (tupleCons a (tupleCons y (Delta0Formula.val s)) i)) =
      tupleCons (collapse domain a)
        (tupleCons (collapse domain y)
          (Delta0Formula.val collapsedParams)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · rfl
  rw [hassignment] at hcollapsed
  have haRange : collapse domain a ∈ range domain :=
    mem_range_iff.mpr ⟨a, ha, rfl⟩
  have hsemantic :=
    (satisfiesIn_subsetDefinitionFormula_iff
      (range_isTransitive domain) haRange phi collapsedParams).mp
      hcollapsed
  exact ⟨collapsedParams, fun i => rfl, hsemantic⟩

/-- The restricted collapse is monotone in its second argument. -/
private theorem collapse_mono {domain x y : ZFSet.{u}} (hxy : x ⊆ y) :
    collapse domain x ⊆ collapse domain y := by
  intro z hz
  rcases mem_collapse_iff.mp hz with ⟨w, hwx, hwDomain, rfl⟩
  exact mem_collapse_iff.mpr ⟨w, hxy hwx, hwDomain, rfl⟩

/--
The successor step of condensation: a fully elementary set-sized membership
structure inside a transitive ambient set commutes with `DefZF` under its
Mostowski collapse.

The hypotheses that both `a` and `DefZF a` belong to `domain` are essential:
they make the relevant section-existence statements available as formulas
with parameters from the elementary substructure.
-/
private theorem collapse_DefZF_eq_DefZF_collapse
    {domain ambient a : ZFSet.{u}}
    (hsubset : (domain : Set ZFSet.{u}) ⊆
      (ambient : Set ZFSet.{u}))
    (hambient : ambient.IsTransitive)
    (habsolute : SatisfactionAbsolute
      (domain : Set ZFSet.{u}) (ambient : Set ZFSet.{u}))
    (ha : a ∈ domain) (hDef : DefZF a ∈ domain) :
    collapse domain (DefZF a) = DefZF (collapse domain a) := by
  classical
  have haAmbient : a ∈ ambient := hsubset ha
  have hDefAmbient : DefZF a ∈ ambient := hsubset hDef
  have hclose : ClosesWithinAll
      (domain : Set ZFSet.{u}) (ambient : Set ZFSet.{u}) :=
    closesWithinAll_of_satisfactionAbsolute habsolute
  have hextensional : IsExtensional domain := by
    intro x hx y hy hsame
    exact restricted_extensionality_of_closesWithinAll hsubset
      (fun w hw z hzw => hambient.mem_trans hzw hw)
      hclose hx hy hsame
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    rcases mem_collapse_iff.mp hz with
      ⟨y, hyDef, hyDomain, hyCollapse⟩
    rcases mem_DefZF_iff_exists_satisfies.mp hyDef with
      ⟨hya, n, s, phi, hphi⟩
    have hsectionAmbient :
        Model.SatisfiesIn (ambient : Set ZFSet.{u})
          (subsetDefinitionFormula phi)
          (tupleCons a
            (tupleCons y (Delta0Formula.val s))) :=
      (satisfiesIn_subsetDefinitionFormula_iff
        hambient haAmbient phi s).mpr hphi
    have hparameterAmbient :
        ∀ i, Delta0Formula.val s i ∈ (ambient : Set ZFSet.{u}) ∧
          Delta0Formula.val s i ∈ a := by
      intro i
      exact ⟨hambient.mem_trans (s i).2 haAmbient, (s i).2⟩
    have hexAmbient :
        Model.SatisfiesIn (ambient : Set ZFSet.{u})
          (existsParametersDefinitionFormula phi) ![a, y] :=
      (satisfiesIn_boundedExistsTail_iff
        (ambient : Set ZFSet.{u}) a y
        (subsetDefinitionFormula phi)).mpr
        ⟨Delta0Formula.val s, hparameterAmbient, hsectionAmbient⟩
    have hpairDomain : ∀ i, ![a, y] i ∈ domain := by
      intro i
      fin_cases i
      · exact ha
      · exact hyDomain
    have hexDomain :
        Model.SatisfiesIn (domain : Set ZFSet.{u})
          (existsParametersDefinitionFormula phi) ![a, y] :=
      (habsolute (existsParametersDefinitionFormula phi)
        ![a, y] hpairDomain).mpr hexAmbient
    rcases (satisfiesIn_boundedExistsTail_iff
      (domain : Set ZFSet.{u}) a y
      (subsetDefinitionFormula phi)).mp hexDomain with
      ⟨rawParams, hrawParams, hsectionDomain⟩
    let params : Tuple (ZFCarrier a) n :=
      fun i => ⟨rawParams i, (hrawParams i).2⟩
    have hparamsDomain : ∀ i, (params i).1 ∈ domain :=
      fun i => (hrawParams i).1
    have hparamsVal : Delta0Formula.val params = rawParams := by
      funext i
      rfl
    rw [← hparamsVal] at hsectionDomain
    rcases exists_collapsedParameters_section hextensional ha hyDomain
      phi params hparamsDomain hsectionDomain with
      ⟨collapsedParams, _hcollapsedParams, hcollapsedSection⟩
    rw [← hyCollapse]
    apply mem_DefZF_iff_exists_satisfies.mpr
    refine ⟨collapse_mono hya, n, collapsedParams, phi, ?_⟩
    exact hcollapsedSection
  · intro hz
    rcases mem_DefZF_iff_exists_satisfies.mp hz with
      ⟨hza, n, collapsedParams, phi, hphi⟩
    have hpreimages : ∀ i,
        ∃ x : ZFSet.{u}, x ∈ a ∧ x ∈ domain ∧
          collapse domain x = (collapsedParams i).1 := by
      intro i
      exact mem_collapse_iff.mp (collapsedParams i).2
    choose rawParams hrawParamsA hrawParamsDomain
      hrawParamsCollapse using hpreimages
    let params : Tuple (ZFCarrier a) n :=
      fun i => ⟨rawParams i, hrawParamsA i⟩
    let definingClass : Set (ZFCarrier a) :=
      {x | FOFormula.Satisfies (zfCarrierMem a) phi (snoc params x)}
    let y0 : ZFSet.{u} := representZFSubset a definingClass
    have hy0Section : ∀ x : ZFCarrier a,
        x.1 ∈ y0 <->
          FOFormula.Satisfies (zfCarrierMem a) phi (snoc params x) := by
      intro x
      change x.1 ∈ representZFSubset a definingClass <-> _
      rw [mem_representZFSubset_iff]
      constructor
      · rintro ⟨_hxa, hx⟩
        exact hx
      · intro hx
        exact ⟨x.2, hx⟩
    have hy0Def : y0 ∈ DefZF a :=
      mem_DefZF_iff_exists_satisfies.mpr
        ⟨representZFSubset_subset a definingClass,
          n, params, phi, hy0Section⟩
    have hy0Ambient : y0 ∈ ambient :=
      hambient.mem_trans hy0Def hDefAmbient
    have hsectionAmbient :
        Model.SatisfiesIn (ambient : Set ZFSet.{u})
          (subsetDefinitionFormula phi)
          (tupleCons a
            (tupleCons y0 (Delta0Formula.val params))) :=
      (satisfiesIn_subsetDefinitionFormula_iff
        hambient haAmbient phi params).mpr hy0Section
    have hexAmbient :
        Model.SatisfiesIn (ambient : Set ZFSet.{u})
          (existsDefinedSubsetFormula phi)
          (tupleCons a
            (tupleCons (DefZF a) (Delta0Formula.val params))) :=
      (satisfiesIn_existsDefinedSubsetFormula_iff
        (ambient : Set ZFSet.{u}) a (DefZF a) phi
        (Delta0Formula.val params)).mpr
        ⟨y0, hy0Ambient, hy0Def, hsectionAmbient⟩
    have hallDomain : ∀ i,
        tupleCons a (tupleCons (DefZF a)
          (Delta0Formula.val params)) i ∈ domain := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [tupleCons_zero] using ha
      · refine Fin.cases ?_ (fun k => ?_) j
        · simpa only [tupleCons_succ, tupleCons_zero] using hDef
        · simp only [tupleCons_succ]
          exact hrawParamsDomain k
    have hexDomain :
        Model.SatisfiesIn (domain : Set ZFSet.{u})
          (existsDefinedSubsetFormula phi)
          (tupleCons a
            (tupleCons (DefZF a) (Delta0Formula.val params))) :=
      (habsolute (existsDefinedSubsetFormula phi)
        (tupleCons a
          (tupleCons (DefZF a) (Delta0Formula.val params)))
        hallDomain).mpr hexAmbient
    rcases (satisfiesIn_existsDefinedSubsetFormula_iff
      (domain : Set ZFSet.{u}) a (DefZF a) phi
      (Delta0Formula.val params)).mp hexDomain with
      ⟨y, hyDomain, hyDef, hsectionDomain⟩
    rcases exists_collapsedParameters_section hextensional ha hyDomain
      phi params hrawParamsDomain hsectionDomain with
      ⟨transportedParams, htransportedParams, htransportedSection⟩
    have hparamsEq : transportedParams = collapsedParams := by
      funext i
      apply Subtype.ext
      exact (htransportedParams i).trans (hrawParamsCollapse i)
    apply mem_collapse_iff.mpr
    refine ⟨y, hyDef, hyDomain, ?_⟩
    apply ZFSet.ext
    intro w
    by_cases hwa : w ∈ collapse domain a
    · let wa : ZFCarrier (collapse domain a) := ⟨w, hwa⟩
      have hleft := htransportedSection wa
      have hright := hphi wa
      rw [hparamsEq] at hleft
      exact hleft.trans hright.symm
    · constructor
      · intro hwy
        exact (hwa (collapse_mono
          (mem_DefZF_iff_exists_satisfies.mp hyDef).1 hwy)).elim
      · intro hwz
        exact (hwa (hza hwz)).elim

end MostowskiCollapse

end

end Constructible

end
end GCHSource_Work_CUGCH_DefZFCollapse

/- Source module: Solutions.Work_CUGCH_CondensationCore -/
section GCHSource_Work_CUGCH_CondensationCore
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# An abstract core for constructible condensation

This file isolates the final order-theoretic step of a condensation argument.
For a transitive set `M`, `ordinalHeight M` is the supremum of the successors
of the ranks of the ordinal members of `M`.  Consequently, the ordinals in
`M` are exactly the von Neumann codes below this height.

The final theorem identifies `M` with the constructible level at its ordinal
height, under three explicit closure hypotheses:

* ordinal successors of members remain in `M`;
* every member of `M` occurs in a constructible level indexed by an ordinal
  belonging to `M`;
* every constructible level indexed by an ordinal belonging to `M` is itself
  an element of `M`.

These hypotheses are the interface that a later Skolem-hull and Mostowski
collapse development must establish.  No elementarity or collapse theorem is
asserted in this file.
-/

section

open Set

universe u

namespace Constructible

section ZFC



/-- Every ordinal member of `M` has index below `ordinalHeight M`. -/
private theorem lt_ordinalHeight_of_mem {M : ZFSet.{u}} {alpha : Ordinal.{u}}
    (halpha : alpha.toZFSet ∈ M) :
    alpha < ordinalHeight M := by
  classical
  let x : ZFCarrier M := ⟨alpha.toZFSet, halpha⟩
  have hx := Ordinal.le_iSup
    (fun y : ZFCarrier M =>
      if y.1.IsOrdinal then Order.succ y.1.rank else 0) x
  have hsucc : Order.succ alpha ≤ ordinalHeight M := by
    simpa [ordinalHeight, x, ZFSet.isOrdinal_toZFSet] using hx
  exact (Order.lt_succ alpha).trans_le hsucc

/--
For a transitive `M`, every index below its ordinal height is represented by
an ordinal member of `M`.
-/
private theorem ordinal_toZFSet_mem_of_lt_ordinalHeight {M : ZFSet.{u}}
    (htrans : M.IsTransitive) {alpha : Ordinal.{u}}
    (halpha : alpha < ordinalHeight M) :
    alpha.toZFSet ∈ M := by
  classical
  rw [ordinalHeight, Ordinal.lt_iSup_iff] at halpha
  rcases halpha with ⟨x, hx⟩
  by_cases hord : x.1.IsOrdinal
  · simp only [if_pos hord] at hx
    have hle : alpha ≤ x.1.rank := Order.lt_succ_iff.mp hx
    rcases hle.eq_or_lt with heq | hlt
    · have hcode : alpha.toZFSet = x.1 := by
        rw [heq, hord.toZFSet_rank_eq]
      simpa only [hcode] using x.2
    · have hmem : alpha.toZFSet ∈ x.1 := by
        rw [← hord.toZFSet_rank_eq]
        exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hlt
      exact htrans.mem_trans hmem x.2
  · simp only [if_neg hord] at hx
    exact (not_lt_of_ge bot_le hx).elim

/-- In a transitive set, ordinal membership is exactly boundedness by height. -/
private theorem ordinal_toZFSet_mem_iff_lt_ordinalHeight {M : ZFSet.{u}}
    (htrans : M.IsTransitive) (alpha : Ordinal.{u}) :
    alpha.toZFSet ∈ M ↔ alpha < ordinalHeight M := by
  constructor
  · exact lt_ordinalHeight_of_mem
  · exact ordinal_toZFSet_mem_of_lt_ordinalHeight htrans







/--
Successor closure makes every nonzero ordinal height a limit ordinal.  The
zero case is deliberately excluded: it is needed when `M` has no ordinal
members at all.
-/
private theorem ordinalHeight_isSuccLimit_of_ne_zero {M : ZFSet.{u}}
    (htrans : M.IsTransitive) (hsucc : OrdinalSuccessorClosed M)
    (hne : ordinalHeight M ≠ 0) :
    Order.IsSuccLimit (ordinalHeight M) := by
  rw [Ordinal.isSuccLimit_iff]
  refine ⟨hne, Order.isSuccPrelimit_of_succ_lt ?_⟩
  intro alpha halpha
  have halphaM : alpha.toZFSet ∈ M :=
    (ordinal_toZFSet_mem_iff_lt_ordinalHeight htrans alpha).mpr halpha
  exact (ordinal_toZFSet_mem_iff_lt_ordinalHeight htrans
    (Order.succ alpha)).mp (hsucc alpha halphaM)

/-- Stage coverage gives the easy inclusion `M ⊆ L_(ordinalHeight M)`. -/
private theorem subset_LStageZF_ordinalHeight_of_internallyStageCovered
    {M : ZFSet.{u}} (htrans : M.IsTransitive)
    (hcover : InternallyStageCovered M) :
    M ⊆ LStageZF (ordinalHeight M) := by
  intro x hx
  rcases hcover x hx with ⟨alpha, halphaM, hxStage⟩
  exact LStageZF_mono
    ((ordinal_toZFSet_mem_iff_lt_ordinalHeight htrans alpha).mp
      halphaM).le hxStage

/--
If `M` is successor closed and contains all of its internally indexed
constructible levels, then `L_(ordinalHeight M) ⊆ M`.
-/
private theorem LStageZF_ordinalHeight_subset_of_containsInternalLStages
    {M : ZFSet.{u}} (htrans : M.IsTransitive)
    (hsucc : OrdinalSuccessorClosed M)
    (hstages : ContainsInternalLStages M) :
    LStageZF (ordinalHeight M) ⊆ M := by
  intro x hx
  by_cases hzero : ordinalHeight M = 0
  · rw [hzero, LStageZF_zero] at hx
    exact (ZFSet.notMem_empty x hx).elim
  · have hlimit :=
      ordinalHeight_isSuccLimit_of_ne_zero htrans hsucc hzero
    rcases (mem_LStageZF_limit_iff hlimit).mp hx with
      ⟨alpha, halpha, hxStage⟩
    have halphaM : alpha.toZFSet ∈ M :=
      (ordinal_toZFSet_mem_iff_lt_ordinalHeight htrans alpha).mpr halpha
    exact htrans.mem_trans hxStage (hstages alpha halphaM)

/--
Abstract condensation core.  A transitive set satisfying the three explicit
closure conditions above is exactly the constructible level at its ordinal
height.

This is only the last step of condensation.  Applying it to a Mostowski
collapse still requires separate proofs that the collapse satisfies each of
the three hypotheses.
-/
private theorem eq_LStageZF_ordinalHeight_of_condensationCore
    {M : ZFSet.{u}} (htrans : M.IsTransitive)
    (hsucc : OrdinalSuccessorClosed M)
    (hcover : InternallyStageCovered M)
    (hstages : ContainsInternalLStages M) :
    M = LStageZF (ordinalHeight M) := by
  apply SetLike.coe_injective
  exact Set.Subset.antisymm
    (subset_LStageZF_ordinalHeight_of_internallyStageCovered htrans hcover)
    (LStageZF_ordinalHeight_subset_of_containsInternalLStages
      htrans hsucc hstages)

end ZFC

end Constructible

end
end GCHSource_Work_CUGCH_CondensationCore

/- Source module: Solutions.Work_CUGCH_MostowskiCollapseOrdinals -/
section GCHSource_Work_CUGCH_MostowskiCollapseOrdinals
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Ordinals through the Mostowski collapse

This file records the order-theoretic part of constructible condensation.
Restricting membership to an arbitrary domain and collapsing an ambient von
Neumann ordinal still produces a von Neumann ordinal.  If the ordinal itself
belongs to the domain, collapse also commutes with ordinal successor.

The final part packages these structural facts for the three hypotheses used
by `CondensationCore`.  Full satisfaction absoluteness is used only to reflect
the assertion that a preimage is an ordinal; no external cardinal or choice
argument occurs here.
-/

section

open Set
open Constructible.ContinuumFormula

universe u

namespace Constructible.MostowskiCollapse

noncomputable section









/-- Collapse commutes with adjoining a domain element to itself.  This is the
set-theoretic operation underlying ordinal successor. -/
private theorem collapse_insert_self {domain x : ZFSet.{u}}
    (hxdomain : x ∈ domain) :
    collapse domain (insert x x) =
      insert (collapse domain x) (collapse domain x) := by
  apply ZFSet.ext
  intro z
  rw [mem_collapse_iff]
  simp only [ZFSet.mem_insert_iff]
  constructor
  · rintro ⟨y, hy, hydomain, rfl⟩
    rcases hy with rfl | hyx
    · exact Or.inl rfl
    · exact Or.inr (mem_collapse_iff.mpr
        ⟨y, hyx, hydomain, rfl⟩)
  · intro hz
    rcases hz with rfl | hz
    · exact ⟨x, Or.inl rfl, hxdomain, rfl⟩
    · rcases mem_collapse_iff.mp hz with
        ⟨y, hyx, hydomain, rfl⟩
      exact ⟨y, Or.inr hyx, hydomain, rfl⟩

/-- If an ordinal belongs to the restricting domain, collapse commutes with
its von Neumann successor. -/
private theorem collapse_toZFSet_succ {domain : ZFSet.{u}}
    {alpha : Ordinal.{u}} (halpha : alpha.toZFSet ∈ domain) :
    collapse domain (Order.succ alpha).toZFSet =
      (Order.succ (collapseOrdinal domain alpha)).toZFSet := by
  calc
    collapse domain (Order.succ alpha).toZFSet =
        collapse domain (insert alpha.toZFSet alpha.toZFSet) := by
      rw [Order.succ_eq_add_one, Ordinal.toZFSet_add_one]
    _ = insert (collapse domain alpha.toZFSet)
        (collapse domain alpha.toZFSet) := collapse_insert_self halpha
    _ = insert (collapseOrdinal domain alpha).toZFSet
        (collapseOrdinal domain alpha).toZFSet := by
      rw [collapseOrdinal_toZFSet]
    _ = ((collapseOrdinal domain alpha) + 1).toZFSet := by
      rw [Ordinal.toZFSet_add_one]
    _ = (Order.succ (collapseOrdinal domain alpha)).toZFSet := by
      rw [Order.succ_eq_add_one]

/-- Ordinal-valued formulation of `collapse_toZFSet_succ`. -/
private theorem collapseOrdinal_succ {domain : ZFSet.{u}}
    {alpha : Ordinal.{u}} (halpha : alpha.toZFSet ∈ domain) :
    collapseOrdinal domain (Order.succ alpha) =
      Order.succ (collapseOrdinal domain alpha) := by
  apply Ordinal.toZFSet_injective
  rw [collapseOrdinal_toZFSet, collapse_toZFSet_succ halpha]



/-! ## Ordinal reflection through full elementarity -/

/-- Raw restricted satisfaction of the ordinal formula in a transitive set
has its ambient von Neumann meaning. -/
private theorem satisfiesIn_isOrdinal_iff {U : ZFSet.{u}}
    (htransitive : U.IsTransitive) {x : ZFSet.{u}}
    (hxU : x ∈ U) :
    Model.SatisfiesIn (U : Set ZFSet.{u})
        OrdinalFormula.isOrdinal ![x] ↔ x.IsOrdinal := by
  let xU : ZFCarrier U := ⟨x, hxU⟩
  have hbridge := Model.satisfies_subtype_iff_satisfiesIn
    (U : Set ZFSet.{u}) OrdinalFormula.isOrdinal ![xU]
  have hsemantic := OrdinalFormula.satisfies_isOrdinal htransitive xU
  have hvalues : (fun i => (![(xU : ZFCarrier U)] i).1) = ![x] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [hvalues] at hbridge
  exact hbridge.symm.trans hsemantic

/-- Full elementarity identifies ambient ordinals in the source hull with
ambient ordinals in its transitive collapse. -/
private theorem isOrdinal_iff_collapse_isOrdinal_of_satisfactionAbsolute
    {domain big : ZFSet.{u}}
    (hextensional : IsExtensional domain)
    (hsubset : domain ⊆ big)
    (hbigTransitive : big.IsTransitive)
    (habsolute : SatisfactionAbsolute
      (domain : Set ZFSet.{u}) (big : Set ZFSet.{u}))
    {x : ZFSet.{u}} (hxdomain : x ∈ domain) :
    x.IsOrdinal ↔ (collapse domain x).IsOrdinal := by
  let sx : Tuple {y : ZFSet.{u} // y ∈ domain} 1 :=
    ![⟨x, hxdomain⟩]
  have hcollapse := satisfiesIn_collapse_iff hextensional
    OrdinalFormula.isOrdinal sx
  have hsourceValues : (fun i => (sx i).1) = ![x] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  have htargetValues :
      (fun i => collapse domain (sx i).1) =
        ![collapse domain x] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [hsourceValues, htargetValues] at hcollapse
  have hparams : ∀ i, ![x] i ∈ (domain : Set ZFSet.{u}) := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hxdomain
  have habs := habsolute OrdinalFormula.isOrdinal ![x] hparams
  have hbigSem := satisfiesIn_isOrdinal_iff hbigTransitive
    (hsubset hxdomain)
  have hrangeSem := satisfiesIn_isOrdinal_iff
    (range_isTransitive domain)
    (mem_range_iff.mpr ⟨x, hxdomain, rfl⟩)
  exact hbigSem.symm.trans
    (habs.symm.trans (hcollapse.trans hrangeSem))





/-- In a transitive carrier, the generic successor-set formula has its
ambient set-theoretic meaning. -/
private theorem satisfiesIn_successorSetAt_iff {U : ZFSet.{u}}
    (htransitive : U.IsTransitive) {x y : ZFSet.{u}}
    (hxU : x ∈ U) (hyU : y ∈ U) :
    Model.SatisfiesIn (U : Set ZFSet.{u})
        (successorSetAt (1 : Fin 2) (0 : Fin 2)) ![x, y] ↔
      y = insert x x := by
  let xU : ZFCarrier U := ⟨x, hxU⟩
  let yU : ZFCarrier U := ⟨y, hyU⟩
  have hbridge := Model.satisfies_subtype_iff_satisfiesIn
    (U : Set ZFSet.{u})
    (successorSetAt (1 : Fin 2) (0 : Fin 2)) ![xU, yU]
  have hvalues :
      (fun i => (![(xU : ZFCarrier U), yU] i).1) = ![x, y] := by
    funext i
    fin_cases i <;> rfl
  rw [hvalues] at hbridge
  have hsemantic := satisfies_successorSetAt
    (fun a b : ZFCarrier U => a.1 ∈ b.1)
    (1 : Fin 2) (0 : Fin 2) ![xU, yU]
  have hmeaning :
      IsSuccessorSetOf
          (fun a b : ZFCarrier U => a.1 ∈ b.1) yU xU ↔
        y = insert x x := by
    constructor
    · intro h
      apply ZFSet.ext
      intro z
      constructor
      · intro hzy
        have hzU : z ∈ U := htransitive.mem_trans hzy hyU
        have hz : z ∈ y ↔ z ∈ x ∨ z = x := by
          simpa only [xU, yU, Subtype.ext_iff] using h ⟨z, hzU⟩
        exact ZFSet.mem_insert_iff.mpr (Or.comm.mp (hz.mp hzy))
      · intro hzsucc
        rcases ZFSet.mem_insert_iff.mp hzsucc with hzx | hzx
        · subst z
          have hz : x ∈ y ↔ x ∈ x ∨ x = x := by
            simpa only [xU, yU, Subtype.ext_iff] using h xU
          exact hz.mpr (Or.inr rfl)
        · have hzU : z ∈ U := htransitive.mem_trans hzx hxU
          have hz : z ∈ y ↔ z ∈ x ∨ z = x := by
            simpa only [xU, yU, Subtype.ext_iff] using h ⟨z, hzU⟩
          exact hz.mpr (Or.inl hzx)
    · intro hyEq
      subst y
      intro z
      simp only [xU, yU, Subtype.ext_iff]
      rw [ZFSet.mem_insert_iff, or_comm]
  exact hbridge.symm.trans (hsemantic.trans hmeaning)

/-- The von Neumann successor operation on well-founded sets is injective. -/
private theorem insert_self_injective :
    Function.Injective (fun x : ZFSet.{u} => insert x x) := by
  intro x y hxy
  change insert x x = insert y y at hxy
  have hx : x ∈ insert y y := by
    rw [← hxy]
    exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  have hy : y ∈ insert x x := by
    rw [hxy]
    exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  rcases ZFSet.mem_insert_iff.mp hx with h | h
  · exact h
  · rcases ZFSet.mem_insert_iff.mp hy with h' | h'
    · exact h'.symm
    · exact (ZFSet.mem_wf.asymmetric x y h h').elim

/-- Swapped-coordinate form of `satisfiesIn_successorSetAt_iff`. -/
private theorem satisfiesIn_successorSetAt_swap_iff {U : ZFSet.{u}}
    (htransitive : U.IsTransitive) {successor x : ZFSet.{u}}
    (hsuccessorU : successor ∈ U) (hxU : x ∈ U) :
    Model.SatisfiesIn (U : Set ZFSet.{u})
        (successorSetAt (0 : Fin 2) (1 : Fin 2)) ![successor, x] ↔
      successor = insert x x := by
  let successorU : ZFCarrier U := ⟨successor, hsuccessorU⟩
  let xU : ZFCarrier U := ⟨x, hxU⟩
  have hbridge := Model.satisfies_subtype_iff_satisfiesIn
    (U : Set ZFSet.{u})
    (successorSetAt (0 : Fin 2) (1 : Fin 2)) ![successorU, xU]
  have hvalues :
      (fun i => (![(successorU : ZFCarrier U), xU] i).1) =
        ![successor, x] := by
    funext i
    fin_cases i <;> rfl
  rw [hvalues] at hbridge
  have hsemantic := satisfies_successorSetAt
    (fun a b : ZFCarrier U => a.1 ∈ b.1)
    (0 : Fin 2) (1 : Fin 2) ![successorU, xU]
  have hmeaning :
      IsSuccessorSetOf
          (fun a b : ZFCarrier U => a.1 ∈ b.1) successorU xU ↔
        successor = insert x x := by
    constructor
    · intro h
      apply ZFSet.ext
      intro z
      constructor
      · intro hzSuccessor
        have hzU : z ∈ U :=
          htransitive.mem_trans hzSuccessor hsuccessorU
        have hz : z ∈ successor ↔ z ∈ x ∨ z = x := by
          simpa only [successorU, xU, Subtype.ext_iff] using
            h ⟨z, hzU⟩
        exact ZFSet.mem_insert_iff.mpr
          (Or.comm.mp (hz.mp hzSuccessor))
      · intro hzSucc
        rcases ZFSet.mem_insert_iff.mp hzSucc with hzx | hzx
        · subst z
          have hz : x ∈ successor ↔ x ∈ x ∨ x = x := by
            simpa only [successorU, xU, Subtype.ext_iff] using h xU
          exact hz.mpr (Or.inr rfl)
        · have hzU : z ∈ U := htransitive.mem_trans hzx hxU
          have hz : z ∈ successor ↔ z ∈ x ∨ z = x := by
            simpa only [successorU, xU, Subtype.ext_iff] using
              h ⟨z, hzU⟩
          exact hz.mpr (Or.inl hzx)
    · intro hEq
      subst successor
      intro z
      simp only [successorU, xU, Subtype.ext_iff]
      rw [ZFSet.mem_insert_iff, or_comm]
  exact hbridge.symm.trans (hsemantic.trans hmeaning)



/-- Full elementarity pulls the predecessor of an ordinal successor back
into the source domain. -/
private theorem ordinalPredecessor_mem_of_succ_mem
    {domain big : ZFSet.{u}}
    (hsubset : domain ⊆ big)
    (hbigTransitive : big.IsTransitive)
    (habsolute : SatisfactionAbsolute
      (domain : Set ZFSet.{u}) (big : Set ZFSet.{u}))
    {alpha : Ordinal.{u}}
    (hsuccDomain : (Order.succ alpha).toZFSet ∈ domain) :
    alpha.toZFSet ∈ domain := by
  let successor := (Order.succ alpha).toZFSet
  have hsuccessorBig : successor ∈ big := hsubset hsuccDomain
  have halphaSucc : alpha.toZFSet ∈ successor := by
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ alpha)
  have halphaBig : alpha.toZFSet ∈ big :=
    hbigTransitive.mem_trans halphaSucc hsuccessorBig
  have hcanonical : successor = insert alpha.toZFSet alpha.toZFSet := by
    simp only [successor, Order.succ_eq_add_one,
      Ordinal.toZFSet_add_one]
  have hbigSat : Model.SatisfiesIn (big : Set ZFSet.{u})
      predecessorExistsFormula ![successor] := by
    simp only [predecessorExistsFormula, Model.SatisfiesIn]
    refine ⟨alpha.toZFSet, halphaBig, ?_⟩
    have hbody := (satisfiesIn_successorSetAt_swap_iff
      hbigTransitive hsuccessorBig halphaBig).mpr hcanonical
    have hsnoc : snoc ![successor] alpha.toZFSet =
        ![successor, alpha.toZFSet] := by
      funext i
      fin_cases i <;> rfl
    rw [hsnoc]
    exact hbody
  have hparams : ∀ i, ![successor] i ∈
      (domain : Set ZFSet.{u}) := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hsuccDomain
  have hdomainSat : Model.SatisfiesIn (domain : Set ZFSet.{u})
      predecessorExistsFormula ![successor] :=
    (habsolute predecessorExistsFormula ![successor] hparams).mpr hbigSat
  rcases hdomainSat with ⟨x, hxdomain, hxDomainSat⟩
  have hbodyDomain : Model.SatisfiesIn (domain : Set ZFSet.{u})
      (successorSetAt (0 : Fin 2) (1 : Fin 2)) ![successor, x] := by
    have hsnoc : snoc ![successor] x = ![successor, x] := by
      funext i
      fin_cases i <;> rfl
    rw [← hsnoc]
    exact hxDomainSat
  have hbodyParams : ∀ i, ![successor, x] i ∈
      (domain : Set ZFSet.{u}) := by
    intro i
    fin_cases i
    · exact hsuccDomain
    · exact hxdomain
  have hbodyBig : Model.SatisfiesIn (big : Set ZFSet.{u})
      (successorSetAt (0 : Fin 2) (1 : Fin 2)) ![successor, x] :=
    (habsolute (successorSetAt (0 : Fin 2) (1 : Fin 2))
      ![successor, x] hbodyParams).mp hbodyDomain
  have hxSuccessor : successor = insert x x :=
    (satisfiesIn_successorSetAt_swap_iff hbigTransitive
      hsuccessorBig (hsubset hxdomain)).mp hbodyBig
  have hxAlpha : x = alpha.toZFSet :=
    insert_self_injective (hxSuccessor.symm.trans hcanonical)
  simpa only [SetLike.mem_coe, hxAlpha] using hxdomain

/-- In a transitive carrier, existential successor satisfaction is exactly
closure under the actual von Neumann successor. -/
private theorem satisfiesIn_successorExistsFormula_iff
    {U : ZFSet.{u}} (htransitive : U.IsTransitive)
    {x : ZFSet.{u}} (hxU : x ∈ U) :
    Model.SatisfiesIn (U : Set ZFSet.{u})
        successorExistsFormula ![x] ↔ insert x x ∈ U := by
  simp only [successorExistsFormula, Model.SatisfiesIn]
  constructor
  · rintro ⟨y, hyU, hy⟩
    have heq := (satisfiesIn_successorSetAt_iff
      htransitive hxU hyU).mp hy
    simpa only [SetLike.mem_coe, heq] using hyU
  · intro hsuccU
    refine ⟨insert x x, hsuccU, ?_⟩
    exact (satisfiesIn_successorSetAt_iff
      htransitive hxU hsuccU).mpr rfl

/-- Full satisfaction absoluteness pulls ambient successor witnesses into
the source domain.  The ambient carrier need only be transitive and closed
under successors of the relevant source ordinals. -/
private theorem sourceOrdinalSuccessorClosed_of_satisfactionAbsolute
    {domain big : ZFSet.{u}}
    (hsubset : domain ⊆ big)
    (hbigTransitive : big.IsTransitive)
    (habsolute : SatisfactionAbsolute
      (domain : Set ZFSet.{u}) (big : Set ZFSet.{u}))
    (hbigSucc : ∀ ⦃x : ZFSet.{u}⦄, x ∈ domain → x.IsOrdinal →
      insert x x ∈ big) :
    SourceOrdinalSuccessorClosed domain := by
  intro x hxdomain hxOrdinal
  have hparams : ∀ i, ![x] i ∈ (domain : Set ZFSet.{u}) := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hxdomain
  have hbigSat : Model.SatisfiesIn (big : Set ZFSet.{u})
      successorExistsFormula ![x] :=
    (satisfiesIn_successorExistsFormula_iff hbigTransitive
      (hsubset hxdomain)).mpr (hbigSucc hxdomain hxOrdinal)
  have hdomainSat : Model.SatisfiesIn (domain : Set ZFSet.{u})
      successorExistsFormula ![x] :=
    (habsolute successorExistsFormula ![x] hparams).mpr hbigSat
  rcases hdomainSat with ⟨y, hydomain, hySat⟩
  have hxyParams : ∀ i, ![x, y] i ∈ (domain : Set ZFSet.{u}) := by
    intro i
    fin_cases i
    · exact hxdomain
    · exact hydomain
  have hyBigSat : Model.SatisfiesIn (big : Set ZFSet.{u})
      (successorSetAt (1 : Fin 2) (0 : Fin 2)) ![x, y] :=
    (habsolute (successorSetAt (1 : Fin 2) (0 : Fin 2))
      ![x, y] hxyParams).mp hySat
  have hyEq : y = insert x x :=
    (satisfiesIn_successorSetAt_iff hbigTransitive
      (hsubset hxdomain) (hsubset hydomain)).mp hyBigSat
  simpa only [SetLike.mem_coe, ← hyEq] using hydomain

/-- Adjoining a member of a transitive set to itself is a definable subset
of that set. -/
private theorem insert_self_mem_DefZF {a x : ZFSet.{u}}
    (ha : a.IsTransitive) (hx : x ∈ a) :
    insert x x ∈ DefZF a := by
  rw [mem_DefZF_iff_exists_satisfies]
  let xA : ZFCarrier a := ⟨x, hx⟩
  let params : Tuple (ZFCarrier a) 1 := ![xA]
  let phi : FOFormula 2 :=
    FOFormula.disj
      (.mem (Fin.last 1) (Fin.castSucc (0 : Fin 1)))
      (.eq (Fin.last 1) (Fin.castSucc (0 : Fin 1)))
  refine ⟨?_, 1, params, phi, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.mp hz with rfl | hzx
    · exact hx
    · exact ha.mem_trans hzx hx
  · intro z
    change z.1 ∈ insert x x ↔
      FOFormula.Satisfies (zfCarrierMem a) phi (snoc params z)
    simp only [phi, FOFormula.satisfies_disj, FOFormula.Satisfies,
      snoc_last, snoc_castSucc, params, Matrix.cons_val_zero, xA,
      zfCarrierMem, Subtype.ext_iff]
    rw [ZFSet.mem_insert_iff, or_comm]

/-- Every nonzero limit constructible level is closed under adjoining one of
its members to itself. -/
private theorem insert_self_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {x : ZFSet.{u}} (hx : x ∈ LStageZF theta) :
    insert x x ∈ LStageZF theta := by
  rcases (mem_LStageZF_limit_iff htheta).mp hx with
    ⟨alpha, halpha, hxalpha⟩
  apply (mem_LStageZF_limit_iff htheta).mpr
  refine ⟨Order.succ alpha, htheta.succ_lt halpha, ?_⟩
  rw [LStageZF_succ]
  exact insert_self_mem_DefZF (LStageZF_isTransitive alpha) hxalpha

/-- Source closure under ordinal successors descends to the transitive
collapse, provided full elementarity reflects which source elements are
ordinals. -/
private theorem ordinalSuccessorClosed_range_of_satisfactionAbsolute
    {domain big : ZFSet.{u}}
    (hextensional : IsExtensional domain)
    (hsubset : domain ⊆ big)
    (hbigTransitive : big.IsTransitive)
    (habsolute : SatisfactionAbsolute
      (domain : Set ZFSet.{u}) (big : Set ZFSet.{u}))
    (hsucc : SourceOrdinalSuccessorClosed domain) :
    OrdinalSuccessorClosed (range domain) := by
  intro alpha halphaRange
  rcases mem_range_iff.mp halphaRange with
    ⟨x, hxdomain, hcollapse⟩
  have hxOrdinal : x.IsOrdinal :=
    (isOrdinal_iff_collapse_isOrdinal_of_satisfactionAbsolute
      hextensional hsubset hbigTransitive habsolute hxdomain).mpr
      (hcollapse ▸ ZFSet.isOrdinal_toZFSet alpha)
  have hxSuccDomain : insert x x ∈ domain :=
    hsucc hxdomain hxOrdinal
  apply mem_range_iff.mpr
  refine ⟨insert x x, hxSuccDomain, ?_⟩
  rw [collapse_insert_self hxdomain, hcollapse,
    Order.succ_eq_add_one, Ordinal.toZFSet_add_one]

/-- Specialized closure theorem used by constructible condensation: a fully
elementary substructure of a limit `L`-level has a collapse whose ordinals
are closed under successor. -/
private theorem ordinalSuccessorClosed_range_of_elementary_LStage
    {domain : ZFSet.{u}} {theta : Ordinal.{u}}
    (htheta : Order.IsSuccLimit theta)
    (hextensional : IsExtensional domain)
    (hsubset : domain ⊆ LStageZF theta)
    (habsolute : SatisfactionAbsolute
      (domain : Set ZFSet.{u}) (LStageZF theta : Set ZFSet.{u})) :
    OrdinalSuccessorClosed (range domain) := by
  apply ordinalSuccessorClosed_range_of_satisfactionAbsolute
    hextensional hsubset (LStageZF_isTransitive theta) habsolute
  apply sourceOrdinalSuccessorClosed_of_satisfactionAbsolute
    hsubset (LStageZF_isTransitive theta) habsolute
  intro x hxdomain _hxOrdinal
  exact insert_self_mem_LStageZF_of_isSuccLimit htheta
    (hsubset hxdomain)

/-- A source limit ordinal remains a nonzero limit after collapse whenever
the source contains zero and is closed under ordinal successor. -/
private theorem collapseOrdinal_isSuccLimit_of_source_closed
    {domain : ZFSet.{u}} {limit : Ordinal.{u}}
    (hlimit : Order.IsSuccLimit limit)
    (hempty : (∅ : ZFSet.{u}) ∈ domain)
    (hsucc : SourceOrdinalSuccessorClosed domain) :
    Order.IsSuccLimit (collapseOrdinal domain limit) := by
  rw [Ordinal.isSuccLimit_iff]
  constructor
  · have hlimitNe : limit ≠ 0 :=
      (Ordinal.isSuccLimit_iff.mp hlimit).1
    have hzeroLimit : (0 : Ordinal.{u}) < limit :=
      (bot_lt_iff_ne_bot.mpr hlimitNe)
    have hzeroDomain : (0 : Ordinal.{u}).toZFSet ∈ domain := by
      simpa only [Ordinal.toZFSet_zero] using hempty
    have hzeroMem :
        collapse domain (0 : Ordinal.{u}).toZFSet ∈
          collapse domain limit.toZFSet :=
      mem_collapse_iff.mpr
        ⟨(0 : Ordinal.{u}).toZFSet,
          Ordinal.toZFSet_mem_toZFSet_iff.mpr hzeroLimit,
          hzeroDomain, rfl⟩
    have hcollapseZero :
        collapse domain (0 : Ordinal.{u}).toZFSet =
          (0 : Ordinal.{u}).toZFSet := by
      rw [Ordinal.toZFSet_zero]
      apply ZFSet.ext
      intro z
      rw [mem_collapse_iff]
      simp
    have hpositive : (0 : Ordinal.{u}) < collapseOrdinal domain limit := by
      apply Ordinal.toZFSet_mem_toZFSet_iff.mp
      rw [collapseOrdinal_toZFSet]
      rw [← hcollapseZero]
      exact hzeroMem
    exact ne_of_gt hpositive
  · apply Order.isSuccPrelimit_of_succ_lt
    intro gamma hgamma
    have hgammaMem :
        gamma.toZFSet ∈ collapse domain limit.toZFSet := by
      rw [← collapseOrdinal_toZFSet]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hgamma
    rcases mem_collapse_iff.mp hgammaMem with
      ⟨betaCode, hbetaCodeLimit, hbetaCodeDomain,
        hbetaCodeCollapse⟩
    rcases Ordinal.mem_toZFSet_iff.mp hbetaCodeLimit with
      ⟨beta, hbetaLimit, rfl⟩
    have hbetaGamma : collapseOrdinal domain beta = gamma := by
      apply Ordinal.toZFSet_injective
      rw [collapseOrdinal_toZFSet]
      exact hbetaCodeCollapse
    have hbetaSuccDomain : (Order.succ beta).toZFSet ∈ domain := by
      rw [Order.succ_eq_add_one, Ordinal.toZFSet_add_one]
      exact hsucc hbetaCodeDomain (ZFSet.isOrdinal_toZFSet beta)
    have hbetaSuccLimit : Order.succ beta < limit :=
      hlimit.succ_lt hbetaLimit
    have hcollapsedSuccLt :
        collapseOrdinal domain (Order.succ beta) <
          collapseOrdinal domain limit := by
      apply Ordinal.toZFSet_mem_toZFSet_iff.mp
      rw [collapseOrdinal_toZFSet, collapseOrdinal_toZFSet]
      exact mem_collapse_iff.mpr
        ⟨(Order.succ beta).toZFSet,
          Ordinal.toZFSet_mem_toZFSet_iff.mpr hbetaSuccLimit,
          hbetaSuccDomain, rfl⟩
    rw [collapseOrdinal_succ hbetaCodeDomain, hbetaGamma] at hcollapsedSuccLt
    exact hcollapsedSuccLt

/-! ## Constructible stages at limit indices -/









/-- Collapse is compatible with the zeroth constructible stage. -/
private theorem collapseStageCompatibleAt_zero (domain : ZFSet.{u}) :
    CollapseStageCompatibleAt domain 0 := by
  simp [CollapseStageCompatibleAt]

/-- Limit step for constructible-stage collapse.

The forward inclusion uses bounded internal stage witnesses.  For the reverse
inclusion, every ordinal below the collapsed index is automatically the
collapse of a unique domain ordinal below the source index; this follows
directly from `mem_collapse_iff` and needs no choice principle. -/
private theorem collapseStageCompatibleAt_limit
    {domain : ZFSet.{u}} {limit : Ordinal.{u}}
    (himageLimit : Order.IsSuccLimit (collapseOrdinal domain limit))
    (hwitness : HasSmallerInternalLStageWitnesses domain limit)
    (hbelow : ∀ (beta : Ordinal.{u}), beta < limit →
      beta.toZFSet ∈ domain → CollapseStageCompatibleAt domain beta) :
    CollapseStageCompatibleAt domain limit := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    rcases mem_collapse_iff.mp hz with
      ⟨x, hxLimit, hxdomain, rfl⟩
    rcases hwitness hxdomain hxLimit with
      ⟨beta, hbetaLimit, hbetaDomain, hxBeta⟩
    have hxCollapsedBeta :
        collapse domain x ∈ collapse domain (LStageZF beta) :=
      mem_collapse_iff.mpr ⟨x, hxBeta, hxdomain, rfl⟩
    have hxTargetBeta :
        collapse domain x ∈ LStageZF (collapseOrdinal domain beta) := by
      rw [← hbelow beta hbetaLimit hbetaDomain]
      exact hxCollapsedBeta
    apply (mem_LStageZF_limit_iff himageLimit).mpr
    refine ⟨collapseOrdinal domain beta, ?_, hxTargetBeta⟩
    apply Ordinal.toZFSet_mem_toZFSet_iff.mp
    rw [collapseOrdinal_toZFSet, collapseOrdinal_toZFSet]
    exact mem_collapse_iff.mpr
      ⟨beta.toZFSet,
        Ordinal.toZFSet_mem_toZFSet_iff.mpr hbetaLimit,
        hbetaDomain, rfl⟩
  · intro hz
    rcases (mem_LStageZF_limit_iff himageLimit).mp hz with
      ⟨gamma, hgamma, hzGamma⟩
    have hgammaCollapse :
        gamma.toZFSet ∈ collapse domain limit.toZFSet := by
      rw [← collapseOrdinal_toZFSet]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hgamma
    rcases mem_collapse_iff.mp hgammaCollapse with
      ⟨betaCode, hbetaCodeLimit, hbetaCodeDomain,
        hbetaCodeCollapse⟩
    rcases Ordinal.mem_toZFSet_iff.mp hbetaCodeLimit with
      ⟨beta, hbetaLimit, rfl⟩
    have hbetaGamma : collapseOrdinal domain beta = gamma := by
      apply Ordinal.toZFSet_injective
      rw [collapseOrdinal_toZFSet]
      exact hbetaCodeCollapse
    have hzCollapsedBeta :
        z ∈ collapse domain (LStageZF beta) := by
      rw [hbelow beta hbetaLimit hbetaCodeDomain, hbetaGamma]
      exact hzGamma
    rcases mem_collapse_iff.mp hzCollapsedBeta with
      ⟨x, hxBeta, hxdomain, hcollapse⟩
    exact mem_collapse_iff.mpr
      ⟨x, LStageZF_mono hbetaLimit.le hxBeta, hxdomain, hcollapse⟩

/-- Transfinite recursion principle for collapse compatibility.  The
successor case is an explicit interface, while the limit case is discharged
by `collapseStageCompatibleAt_limit`. -/
private theorem collapseStageCompatibleAt_of_zero_succ_limit
    {domain : ZFSet.{u}}
    (hpredecessor : ∀ (alpha : Ordinal.{u}),
      (Order.succ alpha).toZFSet ∈ domain → alpha.toZFSet ∈ domain)
    (hsucc : ∀ (alpha : Ordinal.{u}), alpha.toZFSet ∈ domain →
      (Order.succ alpha).toZFSet ∈ domain →
      CollapseStageCompatibleAt domain alpha →
        CollapseStageCompatibleAt domain (Order.succ alpha))
    (hlimitImage : ∀ (limit : Ordinal.{u}), Order.IsSuccLimit limit →
      limit.toZFSet ∈ domain →
        Order.IsSuccLimit (collapseOrdinal domain limit))
    (hlimitWitness : ∀ (limit : Ordinal.{u}), Order.IsSuccLimit limit →
      limit.toZFSet ∈ domain →
        HasSmallerInternalLStageWitnesses domain limit) :
    ∀ (alpha : Ordinal.{u}), alpha.toZFSet ∈ domain →
      CollapseStageCompatibleAt domain alpha := by
  intro alpha
  induction alpha using Ordinal.limitRecOn with
  | zero =>
      intro _hzero
      exact collapseStageCompatibleAt_zero domain
  | add_one alpha ih =>
      intro hsuccessor
      have halpha : alpha.toZFSet ∈ domain :=
        hpredecessor alpha hsuccessor
      exact hsucc alpha halpha hsuccessor (ih halpha)
  | limit limit hlimit ih =>
      intro hlimitDomain
      apply collapseStageCompatibleAt_limit
        (hlimitImage limit hlimit hlimitDomain)
        (hlimitWitness limit hlimit hlimitDomain)
      intro beta hbeta hbetaDomain
      exact ih beta hbeta hbetaDomain

end

end Constructible.MostowskiCollapse

end
end GCHSource_Work_CUGCH_MostowskiCollapseOrdinals

/- Source module: Solutions.Work_CUGCH_CondensationAssembly -/
section GCHSource_Work_CUGCH_CondensationAssembly
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# The assumption-transparent assembly step for Condensation

This file does not state the standard Condensation Lemma under disguised
hypotheses.  It isolates the last part of its usual proof after the uniform
definability of the hierarchy has supplied the following facts about an
elementary substructure `domain` of a limit level `L_theta`:

* the empty set belongs to `domain`;
* every internally indexed level `L_alpha` belongs to `domain`;
* every member of `domain` occurs in such an internally indexed level;
* at a limit index in `domain`, membership in that level has a witness at a
  smaller index which also belongs to `domain`.

These are explicit fields below.  A later theorem may use this assembly for
the standard result only after deriving every field from ordinary
elementarity at an arbitrary limit level.
-/

section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section



namespace StageCondensationInterfaces

variable {theta : Ordinal.{u}} {domain : ZFSet.{u}}



/-- Full elementarity in a transitive ambient level gives extensionality of
the membership relation restricted to `domain`. -/
private theorem isExtensional (h : StageCondensationInterfaces theta domain) :
    IsExtensional domain := by
  intro x hx y hy hsame
  apply restricted_extensionality_of_closesWithinAll
    h.subset_stage (LStageZF_isTransitive theta)
    (closesWithinAll_of_satisfactionAbsolute h.satisfactionAbsolute)
    hx hy
  intro z hz
  exact hsame z hz

/-- The source ordinals in an elementary substructure of a limit level are
closed under von Neumann successor. -/
private theorem sourceOrdinalSuccessorClosed
    (h : StageCondensationInterfaces theta domain) :
    SourceOrdinalSuccessorClosed domain := by
  apply sourceOrdinalSuccessorClosed_of_satisfactionAbsolute
    h.subset_stage (LStageZF_isTransitive theta)
      h.satisfactionAbsolute
  intro x hxDomain _hxOrdinal
  exact insert_self_mem_LStageZF_of_isSuccLimit h.isLimit
    (h.subset_stage hxDomain)

/-- The three explicit stage interfaces, together with full elementarity,
make collapse commute with every internally indexed constructible level. -/
private theorem collapseStageCompatible
    (h : StageCondensationInterfaces theta domain) :
    ∀ alpha : Ordinal.{u}, alpha.toZFSet ∈ domain →
      CollapseStageCompatibleAt domain alpha := by
  have hpredecessor : ∀ alpha : Ordinal.{u},
      (Order.succ alpha).toZFSet ∈ domain → alpha.toZFSet ∈ domain := by
    intro alpha hsuccessor
    exact ordinalPredecessor_mem_of_succ_mem h.subset_stage
      (LStageZF_isTransitive theta) h.satisfactionAbsolute hsuccessor
  have hsuccessor : ∀ alpha : Ordinal.{u},
      alpha.toZFSet ∈ domain →
      (Order.succ alpha).toZFSet ∈ domain →
      CollapseStageCompatibleAt domain alpha →
        CollapseStageCompatibleAt domain (Order.succ alpha) := by
    intro alpha halpha hnext hcompatible
    have hstage : LStageZF alpha ∈ domain := h.stage_mem alpha halpha
    have hnextStage : DefZF (LStageZF alpha) ∈ domain := by
      rw [← LStageZF_succ]
      exact h.stage_mem (Order.succ alpha) hnext
    change collapse domain (LStageZF (Order.succ alpha)) =
      LStageZF (collapseOrdinal domain (Order.succ alpha))
    rw [LStageZF_succ,
      collapse_DefZF_eq_DefZF_collapse h.subset_stage
        (LStageZF_isTransitive theta) h.satisfactionAbsolute
        hstage hnextStage,
      hcompatible, collapseOrdinal_succ halpha, LStageZF_succ]
  have hlimitImage : ∀ limit : Ordinal.{u},
      Order.IsSuccLimit limit → limit.toZFSet ∈ domain →
        Order.IsSuccLimit (collapseOrdinal domain limit) := by
    intro limit hlimit _hlimitDomain
    exact collapseOrdinal_isSuccLimit_of_source_closed
      hlimit h.empty_mem h.sourceOrdinalSuccessorClosed
  exact collapseStageCompatibleAt_of_zero_succ_limit
    hpredecessor hsuccessor hlimitImage h.smallerStageWitnesses

/-- Stage compatibility transports source stage coverage to the transitive
collapse. -/
private theorem internallyStageCovered_range
    (h : StageCondensationInterfaces theta domain)
    (hstage : ∀ alpha : Ordinal.{u}, alpha.toZFSet ∈ domain →
      CollapseStageCompatibleAt domain alpha) :
    InternallyStageCovered (range domain) := by
  intro z hzRange
  rcases mem_range_iff.mp hzRange with ⟨x, hxDomain, hcollapse⟩
  rcases h.internallyStageCovered x hxDomain with
    ⟨alpha, halphaDomain, hxStage⟩
  refine ⟨collapseOrdinal domain alpha, ?_, ?_⟩
  · apply mem_range_iff.mpr
    exact ⟨alpha.toZFSet, halphaDomain,
      (collapseOrdinal_toZFSet domain alpha).symm⟩
  · have hxCollapsedStage :
        collapse domain x ∈ collapse domain (LStageZF alpha) :=
      mem_collapse_iff.mpr ⟨x, hxStage, hxDomain, rfl⟩
    rw [hstage alpha halphaDomain] at hxCollapsedStage
    simpa only [hcollapse] using hxCollapsedStage

/-- Stage membership and compatibility put every internally indexed level
into the transitive collapse. -/
private theorem containsInternalLStages_range
    (h : StageCondensationInterfaces theta domain)
    (hstage : ∀ alpha : Ordinal.{u}, alpha.toZFSet ∈ domain →
      CollapseStageCompatibleAt domain alpha) :
    ContainsInternalLStages (range domain) := by
  intro alpha halphaRange
  rcases mem_range_iff.mp halphaRange with
    ⟨index, hindexDomain, hindexCollapse⟩
  have hindexOrdinal : index.IsOrdinal :=
    (isOrdinal_iff_collapse_isOrdinal_of_satisfactionAbsolute
      h.isExtensional h.subset_stage (LStageZF_isTransitive theta)
      h.satisfactionAbsolute hindexDomain).mpr
      (hindexCollapse ▸ ZFSet.isOrdinal_toZFSet alpha)
  let beta : Ordinal.{u} := index.rank
  have hindexEq : index = beta.toZFSet :=
    hindexOrdinal.toZFSet_rank_eq.symm
  have hbetaDomain : beta.toZFSet ∈ domain := by
    simpa only [← hindexEq] using hindexDomain
  have hcollapsedBeta : collapseOrdinal domain beta = alpha := by
    apply Ordinal.toZFSet_injective
    rw [collapseOrdinal_toZFSet, ← hindexEq]
    exact hindexCollapse
  apply mem_range_iff.mpr
  refine ⟨LStageZF beta, h.stage_mem beta hbetaDomain, ?_⟩
  rw [hstage beta hbetaDomain, hcollapsedBeta]

/-- Assumption-transparent assembly theorem.  Its conclusion is exactly the
usual Condensation conclusion, while every still-unproved stage-definability
consequence remains visible in `StageCondensationInterfaces`. -/
private theorem range_eq_LStageZF_ordinalHeight_gchProof05
    (h : StageCondensationInterfaces theta domain) :
    range domain = LStageZF (ordinalHeight (range domain)) := by
  let hstage := h.collapseStageCompatible
  apply eq_LStageZF_ordinalHeight_of_condensationCore
  · exact range_isTransitive domain
  · exact ordinalSuccessorClosed_range_of_elementary_LStage
      h.isLimit h.isExtensional h.subset_stage h.satisfactionAbsolute
  · exact h.internallyStageCovered_range hstage
  · exact h.containsInternalLStages_range hstage



end StageCondensationInterfaces

end

end MostowskiCollapse

end Constructible

end
end GCHSource_Work_CUGCH_CondensationAssembly

universe u

theorem solution : ∀ {theta : Ordinal.{u}} {domain : ZFSet.{u}},
  Constructible.MostowskiCollapse.StageCondensationInterfaces.{u} theta domain →
    @Eq.{u + 2} ZFSet.{u} (Constructible.MostowskiCollapse.range.{u} domain)
      (Constructible.LStageZF.{u} (Constructible.ordinalHeight.{u} (Constructible.MostowskiCollapse.range.{u} domain))) :=
  @Constructible.MostowskiCollapse.StageCondensationInterfaces.range_eq_LStageZF_ordinalHeight_gchProof05.{u}
