-- Prove2me | solution 1 for Constructible.ContinuumFormula.injects_infiniteCardinalSquare_lCarrier
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-25T23:57:19.903262+00:00
-- url     : https://prove2.me/submissions/bc7e0298-414b-4bbb-9b56-5cc8671388f7

import Definitions.Def_CH_ConstructibleGCH_Library20

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









/-- Every member of a constructible set is bounded by one constructible level. -/
private theorem exists_LStage_for_constructible_members {a : ZFSet.{u}} (ha : a ∈ L) :
    ∃ α : Ordinal.{u}, ∀ x ∈ a, x ∈ LStageZF α :=
  exists_LStage_for_members fun _x hx => mem_L_of_mem hx ha

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











/-- Restricting an internally represented stage well-order preserves it. -/
private theorem internallyWellOrders_of_stage
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
private theorem modelsInternalWellOrdering_of_allStages
    (hstage : AllStagesInternallyWellOrdered.{u}) :
    ModelsInternalWellOrdering.{u} := by
  intro a
  rcases exists_LStage_for_constructible_members a.2 with
    ⟨alpha, halpha⟩
  rcases hstage alpha with ⟨r, hr⟩
  exact ⟨r, internallyWellOrders_of_stage halpha hr⟩





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







/-- Every constructible stage has an internally represented well-order. -/
private theorem allStagesInternallyWellOrdered_of_historyData :
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





end

end Constructible.Model
end CUAdapterModule98



/-! # Bridge to the existing Prove2Me constructible universe -/




end GCHSource_Work_ConstructibleGCH_ReuseBase

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















/-! ## The internal Hartogs number of a constructible set -/

























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



end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalInjections

/- Source module: Solutions.Work_CUGCH_InternalSchroederBernstein -/
section GCHSource_Work_CUGCH_InternalSchroederBernstein
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Cantor--Schroeder--Bernstein inside the constructible universe

The usual least-closed-subset proof is carried out with Full Separation in
`LCarrier`.  The resulting bijection is then built by the definable relation
graph construction, so its graph is an actual member of `L`.
-/

section

universe u

namespace Constructible.ContinuumFormula

/-! ## Formula semantics for the least closed subset -/











































/-! ## The least closed subset of the domain -/



private theorem sbLeastMember_assignment
    (f g a b x : Constructible.Model.LCarrier.{u}) :
    snoc ![f, g, a, b] x = ![f, g, a, b, x] := by
  funext i
  fin_cases i <;> rfl

private theorem satisfies_sbLeastMemberPredicate
    (f g a b x : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      sbLeastMemberPredicate (snoc ![f, g, a, b] x) <->
      SBLeastMember Constructible.Model.lCarrierMem f g a b x := by
  rw [sbLeastMember_assignment]
  exact satisfies_sbLeastMemberAt
    Constructible.Model.lCarrierMem
      (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (3 : Fin 5) (4 : Fin 5)
      ![f, g, a, b, x]

/-- Full Separation constructs the least subset of `a` which contains the
points outside the range of `g` and is closed under `g o f`. -/
private theorem exists_leastSBClosed_lCarrier
    {f g a b : Constructible.Model.LCarrier.{u}}
    (_hf : IsInjection Constructible.Model.lCarrierMem f a b)
    (hg : IsInjection Constructible.Model.lCarrierMem g b a) :
    exists closed : Constructible.Model.LCarrier.{u},
      SBClosed Constructible.Model.lCarrierMem f g a b closed /\
        forall candidate : Constructible.Model.LCarrier.{u},
          SBClosed Constructible.Model.lCarrierMem f g a b candidate ->
            IsSubsetOf Constructible.Model.lCarrierMem closed candidate := by
  rcases Constructible.Model.exists_separationLCarrier
      sbLeastMemberPredicate ![f, g, a, b] a with
    ⟨closed, hclosed⟩
  have hclosed_iff : forall x : Constructible.Model.LCarrier.{u},
      x.1 ∈ closed.1 <->
        SBLeastMember Constructible.Model.lCarrierMem f g a b x := by
    intro x
    rw [hclosed x, satisfies_sbLeastMemberPredicate]
    simp only [SBLeastMember, and_iff_right_iff_imp]
    exact fun h => h.1
  have hsubset : IsSubsetOf Constructible.Model.lCarrierMem closed a := by
    intro x hx
    exact ((hclosed_iff x).mp hx).1
  have hbase : forall x : Constructible.Model.LCarrier.{u},
      SBBase Constructible.Model.lCarrierMem g a b x -> x.1 ∈ closed.1 := by
    intro x hx
    apply (hclosed_iff x).mpr
    refine ⟨hx.1, ?_⟩
    intro candidate hcandidate
    exact hcandidate.2.1 x hx
  have hstep : forall z : Constructible.Model.LCarrier.{u},
      SBStep Constructible.Model.lCarrierMem f g closed z ->
        z.1 ∈ closed.1 := by
    rintro z ⟨x, hxclosed, y, hfxy, hgyz⟩
    have hzA : z.1 ∈ a.1 :=
      (hg.1.graphValue_mem_lCarrier hgyz).2
    apply (hclosed_iff z).mpr
    refine ⟨hzA, ?_⟩
    intro candidate hcandidate
    apply hcandidate.2.2 z
    refine ⟨x, ?_, y, hfxy, hgyz⟩
    exact ((hclosed_iff x).mp hxclosed).2 candidate hcandidate
  refine ⟨closed, ⟨hsubset, hbase, hstep⟩, ?_⟩
  intro candidate hcandidate x hxclosed
  exact ((hclosed_iff x).mp hxclosed).2 candidate hcandidate



private theorem sbGenerated_assignment
    (f g a b closed x : Constructible.Model.LCarrier.{u}) :
    snoc ![f, g, a, b, closed] x = ![f, g, a, b, closed, x] := by
  funext i
  fin_cases i <;> rfl

private theorem satisfies_sbGeneratedPredicate
    (f g a b closed x : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      sbGeneratedPredicate (snoc ![f, g, a, b, closed] x) <->
      SBGenerated Constructible.Model.lCarrierMem f g a b closed x := by
  rw [sbGenerated_assignment]
  exact satisfies_sbGeneratedAt
    Constructible.Model.lCarrierMem
      (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
      (3 : Fin 6) (4 : Fin 6) (5 : Fin 6)
      ![f, g, a, b, closed, x]

/-- The least closed set is exactly the base together with one image under
`g o f`.  A second Separation instance supplies the closed comparison set
needed for the minimality argument. -/
private theorem mem_leastSBClosed_iff_generated_lCarrier
    {f g a b closed : Constructible.Model.LCarrier.{u}}
    (hg : IsInjection Constructible.Model.lCarrierMem g b a)
    (hclosed : SBClosed Constructible.Model.lCarrierMem f g a b closed)
    (hminimal : forall candidate : Constructible.Model.LCarrier.{u},
      SBClosed Constructible.Model.lCarrierMem f g a b candidate ->
        IsSubsetOf Constructible.Model.lCarrierMem closed candidate)
    (x : Constructible.Model.LCarrier.{u}) :
    x.1 ∈ closed.1 <->
      SBGenerated Constructible.Model.lCarrierMem f g a b closed x := by
  rcases Constructible.Model.exists_separationLCarrier
      sbGeneratedPredicate ![f, g, a, b, closed] a with
    ⟨generated, hgenerated⟩
  have hgenerated_iff : forall z : Constructible.Model.LCarrier.{u},
      z.1 ∈ generated.1 <->
        z.1 ∈ a.1 /\
          SBGenerated Constructible.Model.lCarrierMem
            f g a b closed z := by
    intro z
    rw [hgenerated z, satisfies_sbGeneratedPredicate]
  have hgenerated_subset_closed :
      IsSubsetOf Constructible.Model.lCarrierMem generated closed := by
    intro z hz
    rcases (hgenerated_iff z).mp hz with ⟨_hzA, hzbase | hzstep⟩
    · exact hclosed.2.1 z hzbase
    · exact hclosed.2.2 z hzstep
  have hgenerated_closed :
      SBClosed Constructible.Model.lCarrierMem f g a b generated := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact ((hgenerated_iff z).mp hz).1
    · intro z hzbase
      apply (hgenerated_iff z).mpr
      exact ⟨hzbase.1, Or.inl hzbase⟩
    · rintro z ⟨w, hwgenerated, y, hfwy, hgyz⟩
      have hzA : z.1 ∈ a.1 :=
        (hg.1.graphValue_mem_lCarrier hgyz).2
      apply (hgenerated_iff z).mpr
      refine ⟨hzA, Or.inr ?_⟩
      exact ⟨w, hgenerated_subset_closed w hwgenerated,
        y, hfwy, hgyz⟩
  constructor
  · intro hxclosed
    have hxgenerated := hminimal generated hgenerated_closed x hxclosed
    exact ((hgenerated_iff x).mp hxgenerated).2
  · intro hxgenerated
    rcases hxgenerated with hxbase | hxstep
    · exact hclosed.2.1 x hxbase
    · exact hclosed.2.2 x hxstep

/-! ## The internally represented CSB bijection -/



private theorem sbBijection_assignment
    (f g a closed x y : Constructible.Model.LCarrier.{u}) :
    snoc (snoc ![f, g, a, closed] x) y =
      ![f, g, a, closed, x, y] := by
  funext i
  fin_cases i <;> rfl

private theorem satisfies_sbBijectionPredicate
    (f g a closed x y : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      sbBijectionPredicate (snoc (snoc ![f, g, a, closed] x) y) <->
      SBBijectionRel Constructible.Model.lCarrierMem
        f g a closed x y := by
  rw [sbBijection_assignment]
  exact satisfies_sbBijectionAt
    Constructible.Model.lCarrierMem
      (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
      (3 : Fin 6) (4 : Fin 6) (5 : Fin 6)
      ![f, g, a, closed, x, y]

/-- The piecewise CSB relation has an actual constructible graph. -/
private theorem exists_sbBijectionGraph_lCarrier
    {f g a b closed : Constructible.Model.LCarrier.{u}}
    (hf : IsInjection Constructible.Model.lCarrierMem f a b)
    (hg : IsInjection Constructible.Model.lCarrierMem g b a) :
    exists graph : Constructible.Model.LCarrier.{u},
      IsGraphBetween Constructible.Model.lCarrierMem graph a b /\
        forall x y : Constructible.Model.LCarrier.{u},
          GraphValue Constructible.Model.lCarrierMem graph x y <->
            SBBijectionRel Constructible.Model.lCarrierMem
              f g a closed x y := by
  let container := unionLCarrier a b
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      sbBijectionPredicate ![f, g, a, closed] container with
    ⟨graph, hsupport, hrelation⟩
  have hvalue : forall x y : Constructible.Model.LCarrier.{u},
      GraphValue Constructible.Model.lCarrierMem graph x y <->
        SBBijectionRel Constructible.Model.lCarrierMem
          f g a closed x y := by
    intro x y
    rw [graphValue_lCarrier_iff_graphRel, hrelation]
    constructor
    · rintro ⟨_hxContainer, _hyContainer, hformula⟩
      exact (satisfies_sbBijectionPredicate f g a closed x y).mp hformula
    · intro hpiece
      have hxy : x.1 ∈ a.1 /\ y.1 ∈ b.1 := by
        rcases hpiece with hleft | hright
        · exact hf.1.graphValue_mem_lCarrier hleft.2
        · have hmem := hg.1.graphValue_mem_lCarrier hright.2.2
          exact ⟨hright.1, hmem.1⟩
      refine ⟨?_, ?_, ?_⟩
      · exact (mem_unionLCarrier_iff a b x).mpr (Or.inl hxy.1)
      · exact (mem_unionLCarrier_iff a b y).mpr (Or.inr hxy.2)
      · exact (satisfies_sbBijectionPredicate f g a closed x y).mpr
          hpiece
  refine ⟨graph, ?_, hvalue⟩
  intro pair hpair
  rcases hsupport pair hpair with
    ⟨x, y, _hxContainer, _hyContainer, hpairEq, hformula⟩
  have hpiece :=
    (satisfies_sbBijectionPredicate f g a closed x y).mp hformula
  have hxy : x.1 ∈ a.1 /\ y.1 ∈ b.1 := by
    rcases hpiece with hleft | hright
    · exact hf.1.graphValue_mem_lCarrier hleft.2
    · have hmem := hg.1.graphValue_mem_lCarrier hright.2.2
      exact ⟨hright.1, hmem.1⟩
  exact ⟨x, hxy.1, y, hxy.2,
    (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq⟩

/-- Cantor--Schroeder--Bernstein for internally represented injections.

Both input injections and the resulting bijection are graphs belonging to
`L`; no ambient equivalence is used as a graph witness. -/
private theorem injects_antisymm_lCarrier
    {a b : Constructible.Model.LCarrier.{u}} :
    Injects Constructible.Model.lCarrierMem a b ->
      Injects Constructible.Model.lCarrierMem b a ->
        Equinumerous Constructible.Model.lCarrierMem a b := by
  classical
  rintro ⟨f, hf⟩ ⟨g, hg⟩
  rcases exists_leastSBClosed_lCarrier hf hg with
    ⟨closed, hclosed, hminimal⟩
  have hfixed : forall x : Constructible.Model.LCarrier.{u},
      x.1 ∈ closed.1 <->
        SBGenerated Constructible.Model.lCarrierMem
          f g a b closed x :=
    mem_leastSBClosed_iff_generated_lCarrier hg hclosed hminimal
  rcases exists_sbBijectionGraph_lCarrier
      (closed := closed) hf hg with
    ⟨graph, hbetween, hvalue⟩
  refine ⟨graph, hbetween, ?_, ?_⟩
  · intro x hxA
    by_cases hxClosed : x.1 ∈ closed.1
    · rcases hf.2.1 x hxA with ⟨y, hyB, hfxy, hyUnique⟩
      refine ⟨y, hyB, (hvalue x y).mpr (Or.inl ⟨hxClosed, hfxy⟩), ?_⟩
      intro z hzB hxz
      rcases (hvalue x z).mp hxz with hleft | hright
      · exact hyUnique z hzB hleft.2
      · exact False.elim (hright.2.1 hxClosed)
    · have hxRange : InRange Constructible.Model.lCarrierMem g b x := by
        by_contra hxNotRange
        exact hxClosed (hclosed.2.1 x ⟨hxA, hxNotRange⟩)
      rcases hxRange with ⟨y, hyB, hgyx⟩
      refine ⟨y, hyB,
        (hvalue x y).mpr (Or.inr ⟨hxA, hxClosed, hgyx⟩), ?_⟩
      intro z hzB hxz
      rcases (hvalue x z).mp hxz with hleft | hright
      · exact False.elim (hxClosed hleft.1)
      · exact hg.2.2 x hxA y hyB hgyx z hzB hright.2.2
  · intro y hyB
    rcases hg.2.1 y hyB with ⟨x, hxA, hgyx, hxUnique⟩
    by_cases hxClosed : x.1 ∈ closed.1
    · have hxGenerated := (hfixed x).mp hxClosed
      rcases hxGenerated with hxBase | hxStep
      · exact False.elim (hxBase.2 ⟨y, hyB, hgyx⟩)
      · rcases hxStep with ⟨z, hzClosed, w, hfzw, hgwx⟩
        have hzA := hclosed.1 z hzClosed
        have hwB := (hf.1.graphValue_mem_lCarrier hfzw).2
        have hwy : w = y :=
          (hg.2.2 x hxA w hwB hgwx y hyB hgyx).symm
        have hfzy : GraphValue Constructible.Model.lCarrierMem f z y := by
          simpa only [hwy] using hfzw
        refine ⟨z, hzA,
          (hvalue z y).mpr (Or.inl ⟨hzClosed, hfzy⟩), ?_⟩
        intro q hqA hqy
        rcases (hvalue q y).mp hqy with hleft | hright
        · exact hf.2.2 y hyB z hzA hfzy q hqA hleft.2
        · have hqx := hxUnique q hqA hright.2.2
          subst q
          exact False.elim (hright.2.1 hxClosed)
    · refine ⟨x, hxA,
        (hvalue x y).mpr (Or.inr ⟨hxA, hxClosed, hgyx⟩), ?_⟩
      intro z hzA hzy
      rcases (hvalue z y).mp hzy with hleft | hright
      · have hxNow : x.1 ∈ closed.1 := hclosed.2.2 x
          ⟨z, hleft.1, y, hleft.2, hgyx⟩
        exact False.elim (hxClosed hxNow)
      · exact hxUnique z hzA hright.2.2

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalSchroederBernstein

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



/-- An internal cardinal cannot internally inject into a smaller ordinal.

The inclusion of the smaller ordinal into the cardinal is internally
represented by the identity graph.  Internal CSB would turn injections in
both directions into the forbidden bijection.
-/
private theorem IsCardinal.not_injects_of_mem_lCarrier
    {smaller cardinal : Constructible.Model.LCarrier.{u}}
    (hcardinal : IsCardinal Constructible.Model.lCarrierMem cardinal)
    (hsmaller : Constructible.Model.lCarrierMem smaller cardinal)
    (hantisymm : InternalInjectionAntisymm
      (A := Constructible.Model.LCarrier.{u})
      Constructible.Model.lCarrierMem) :
    Not (Injects Constructible.Model.lCarrierMem cardinal smaller) := by
  intro hback
  have hforward :
      Injects Constructible.Model.lCarrierMem smaller cardinal :=
    injects_of_subset_lCarrier (fun z hz =>
      hcardinal.1.1 smaller hsmaller z hz)
  exact hcardinal.2 smaller hsmaller (hantisymm hforward hback)







/-! ## Unconditional specialization to `LCarrier` -/

/-- The internally constructed Cantor--Schroeder--Bernstein bijection
discharges the antisymmetry interface used above. -/
private theorem internalInjectionAntisymm_lCarrier :
    InternalInjectionAntisymm
      (A := Constructible.Model.LCarrier.{u})
      Constructible.Model.lCarrierMem := by
  intro x y hxy hyx
  exact injects_antisymm_lCarrier hxy hyx





end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_HartogsSuccessor

/- Source module: Solutions.Work_CUGCH_GCHReduction -/
section GCHSource_Work_CUGCH_GCHReduction
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Reduction of GCH in the constructible universe

This file discharges the elementary part of the GCH semantics for
`Model.LCarrier`.  It identifies the standard constructible `omega` with the
least internally inductive set, proves that it is an internal cardinal, and
reduces GCH to the substantive upper-bound theorem for constructible power
sets.

The reduction theorem deliberately keeps that upper bound as an explicit
hypothesis.  In particular, no condensation or small-stage theorem is assumed
implicitly here.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## The internal natural numbers -/





/-! ## Finiteness of the ordinals below `omega` -/



private theorem finiteOrdinalMemberIndex_spec (n : Nat)
    (x : RelationCarrier LMem
      (ordinalLCarrier (n : Ordinal.{u}))) :
    x.1.1 = Constructible.FiniteSequenceZF.natCode
      (finiteOrdinalMemberIndex n x).1 := by
  have hxraw : x.1.1 ∈
      (ordinalLCarrier (n : Ordinal.{u})).1 := x.2
  rw [finiteOrdinalMemberIndex]
  exact (Classical.choose_spec
    (Constructible.IndexedSequenceZF.mem_natCode_iff_exists_lt
      x.1.1 n |>.mp (by
        simpa only [ordinalLCarrier_val,
          Constructible.FiniteSequenceZF.natCode] using hxraw))).2

private theorem finiteOrdinalMemberIndex_injective (n : Nat) :
    Function.Injective (finiteOrdinalMemberIndex.{u} n) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  calc
    x.1.1 = Constructible.FiniteSequenceZF.natCode
        (finiteOrdinalMemberIndex n x).1 :=
      finiteOrdinalMemberIndex_spec n x
    _ = Constructible.FiniteSequenceZF.natCode
        (finiteOrdinalMemberIndex n y).1 := by
      rw [congrArg Fin.val hxy]
    _ = y.1.1 := (finiteOrdinalMemberIndex_spec n y).symm



private theorem omegaNaturalMember_injective :
    Function.Injective (omegaNaturalMember.{u}) := by
  intro m n hmn
  have hraw :
      (m : Ordinal.{u}).toZFSet = (n : Ordinal.{u}).toZFSet :=
    congrArg (fun x => x.1.1) hmn
  exact_mod_cast Ordinal.toZFSet_injective hraw

private theorem not_injects_omega_finiteOrdinal (n : Nat) :
    ¬Injects LMem
      (omegaLCarrier : Constructible.Model.LCarrier.{u})
      (ordinalLCarrier (n : Ordinal.{u})) := by
  rintro ⟨graph, hgraph⟩
  let index := finiteOrdinalMemberIndex.{u} n
  let f : Nat → Fin n := fun k => index (hgraph.toFun (omegaNaturalMember k))
  have hf : Function.Injective f :=
    finiteOrdinalMemberIndex_injective n |>.comp
      (hgraph.toFun_injective.comp omegaNaturalMember_injective)
  exact (not_injective_infinite_finite f) hf

/-- The standard constructible `omega` is an internal initial ordinal.

The conclusion uses the set-coded `Equinumerous` relation.  To exclude a
bijection with a finite ordinal, the proof reverses its internally coded graph
and applies the ordinary finite pigeonhole principle to the induced function;
it does not compare ambient `ZFSet.card`s.
-/
private theorem omegaLCarrier_isCardinal :
    IsCardinal LMem
      (omegaLCarrier : Constructible.Model.LCarrier.{u}) := by
  constructor
  · apply (isVonNeumannOrdinal_lCarrier_iff omegaLCarrier).2
    exact ZFSet.isOrdinal_toZFSet Ordinal.omega0
  · intro alpha halpha hequinumerous
    have halphaRaw : alpha.1 ∈ Ordinal.omega0.toZFSet := by
      simpa only [omegaLCarrier] using halpha
    rcases Constructible.IndexedSequenceZF.mem_omega_iff_exists_natCode
        alpha.1 |>.mp halphaRaw with ⟨n, hn⟩
    have halphaEq :
        alpha = ordinalLCarrier (n : Ordinal.{u}) := by
      apply Subtype.ext
      simpa only [ordinalLCarrier_val,
        Constructible.FiniteSequenceZF.natCode] using hn
    subst alpha
    exact not_injects_omega_finiteOrdinal n
      ((Equinumerous.symm_lCarrier hequinumerous).injects)

/-! ## The exact remaining GCH obligation -/





end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_GCHReduction

/- Source module: Solutions.Work_CUGCH_InternalCardinalRepresentatives -/
section GCHSource_Work_CUGCH_InternalCardinalRepresentatives
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# Internal cardinal representatives

This file constructs the order-type interface needed to turn the internally
represented well-order of a constructible set into an internally represented
bijection with an ordinal.  Every graph appearing in the semantic statements
is an element of `L`; an ambient Lean equivalence is not used as an internal
bijection witness.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## Semantic order-type predicates -/







/-! ## Object-language formulas -/































/-! ## Small carriers and represented bijections -/





















/-! ## The canonical small carrier of a von Neumann ordinal -/

























/-! ## From internal ordinal representatives to internal cardinals -/

/-- Internal equinumerosity is transitive in `LCarrier`.  The proof composes
internal injections in both directions and invokes the already internalized
Cantor--Schroeder--Bernstein construction. -/
private theorem Equinumerous.trans_lCarrier
    {a b c : LCarrier.{u}}
    (hab : Equinumerous LMem a b)
    (hbc : Equinumerous LMem b c) :
    Equinumerous LMem a c := by
  apply injects_antisymm_lCarrier
  · exact hab.injects.trans_lCarrier hbc.injects
  · exact hbc.symm_lCarrier.injects.trans_lCarrier
      hab.symm_lCarrier.injects



/-- An internal ordinal representative makes the candidate class nonempty. -/
private theorem internalOrdinalRepresentatives_nonempty
    (a : LCarrier.{u})
    (h : exists alpha : Ordinal.{u},
      Equinumerous LMem a (ordinalLCarrier alpha)) :
    (internalOrdinalRepresentatives a).Nonempty := by
  rcases h with ⟨alpha, halpha⟩
  exact ⟨alpha, halpha⟩



/-- Whenever an internal ordinal representative exists, the least candidate
is itself still witnessed by an internal bijection. -/
private theorem internalCardinalRepresentativeOrdinal_mem
    (a : LCarrier.{u})
    (h : exists alpha : Ordinal.{u},
      Equinumerous LMem a (ordinalLCarrier alpha)) :
    internalCardinalRepresentativeOrdinal a ∈
      internalOrdinalRepresentatives a := by
  exact csInf_mem (internalOrdinalRepresentatives_nonempty a h)

/-- The least internally represented ordinal equinumerous with `a` is an
internal cardinal.  Minimality is tested only against internally represented
bijections, exactly as required by `IsCardinal LMem`. -/
private theorem internalCardinalRepresentative_isCardinal
    (a : LCarrier.{u})
    (h : exists alpha : Ordinal.{u},
      Equinumerous LMem a (ordinalLCarrier alpha)) :
    IsCardinal LMem
      (ordinalLCarrier (internalCardinalRepresentativeOrdinal a)) := by
  let beta := internalCardinalRepresentativeOrdinal a
  have hbetaCandidate : beta ∈ internalOrdinalRepresentatives a :=
    internalCardinalRepresentativeOrdinal_mem a h
  have haBeta : Equinumerous LMem a (ordinalLCarrier beta) :=
    hbetaCandidate
  constructor
  · exact (isVonNeumannOrdinal_lCarrier_iff
      (ordinalLCarrier beta)).mpr (ZFSet.isOrdinal_toZFSet beta)
  · intro gamma hgamma hgammaBeta
    have hgammaRaw : gamma.1 ∈ beta.toZFSet := by
      change gamma.1 ∈ (ordinalLCarrier beta).1 at hgamma
      simpa only [ordinalLCarrier_val] using hgamma
    rcases Ordinal.mem_toZFSet_iff.mp hgammaRaw with
      ⟨delta, hdeltaBeta, hdeltaValue⟩
    have hgammaEq : gamma = ordinalLCarrier delta := by
      apply Subtype.ext
      exact hdeltaValue.symm
    have haDelta : Equinumerous LMem a (ordinalLCarrier delta) := by
      rw [← hgammaEq]
      exact haBeta.trans_lCarrier hgammaBeta.symm_lCarrier
    have hbetaDelta : beta <= delta :=
      csInf_le' (show delta ∈ internalOrdinalRepresentatives a from haDelta)
    exact (not_le_of_gt hdeltaBeta) hbetaDelta

/-- Every internal ordinal representative therefore yields a genuine
internal cardinal representative. -/
private theorem exists_internalCardinalRepresentative_of_ordinalRepresentative
    (a : LCarrier.{u})
    (h : exists alpha : Ordinal.{u},
      Equinumerous LMem a (ordinalLCarrier alpha)) :
    exists cardinal : LCarrier.{u},
      IsCardinal LMem cardinal /\ Equinumerous LMem a cardinal := by
  exact ⟨ordinalLCarrier (internalCardinalRepresentativeOrdinal a),
    internalCardinalRepresentative_isCardinal a h,
    internalCardinalRepresentativeOrdinal_mem a h⟩

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalCardinalRepresentatives

/- Source module: Solutions.Work_CUGCH_InternalCardinalRepresentativeInterface -/
section GCHSource_Work_CUGCH_InternalCardinalRepresentativeInterface
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The explicit order-type interface for internal cardinal representatives

`ModelsInternalWellOrdering` supplies a constructible graph for a well-order,
but it does not by itself supply the graph of the order-type map.  This file
records the exact missing witness.  Once an internal ordinal and a total,
single-valued, onto interpretation of `memberOrderTypeRelation` are supplied,
the existing Separation/graph theorem constructs the actual Kuratowski graph
in `L`.  No ambient equivalence is used as an internal witness.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## The missing order-type witness -/



/-! ## Internal graph and equinumerosity -/

/--
An `InternalOrderTypeWitness` yields an internally represented bijection from
the domain to its ordinal target.  The graph is obtained by the existing
Separation construction for a fixed first-order relation.
-/
private theorem internalEquinumerous_ordinal_of_orderTypeWitness
    {relation domain : LCarrier.{u}}
    (w : InternalOrderTypeWitness relation domain) :
    exists graph : LCarrier.{u},
      IsBijection LMem graph domain w.ordinal := by
  let params : Tuple LCarrier.{u} 2 := ![relation, domain]
  let container : LCarrier.{u} := unionLCarrier domain w.ordinal
  rcases Model.exists_definableRelationGraph_with_support
      memberOrderTypeRelation params container with
    ⟨graph, hsupport, hgraph⟩
  refine ⟨graph, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro pair hpair
    rcases (hsupport pair hpair) with
      ⟨x, y, hx, hy, hpairEq, hformula⟩
    have hformulaSem :=
      (satisfies_memberOrderTypeRelation relation domain x y).mp hformula
    have hxDomain : x.1 ∈ domain.1 := hformulaSem.1
    have hyOrdinal : y.1 ∈ w.ordinal.1 := w.bounded x y hxDomain hformula
    refine ⟨x, hxDomain, y, hyOrdinal, ?_⟩
    exact (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq
  · intro x hx
    rcases w.total x hx with ⟨y, hyOrdinal, hformula⟩
    refine ⟨y, hyOrdinal, ?_, ?_⟩
    · apply (graphValue_lCarrier_iff_graphRel graph x y).mpr
      exact (hgraph x y).mpr ⟨mem_unionLCarrier_iff domain w.ordinal x |>.mpr (Or.inl hx),
        mem_unionLCarrier_iff domain w.ordinal y |>.mpr (Or.inr hyOrdinal), hformula⟩
    · intro z hz hvalue
      have hzFormula :
          FOFormula.Satisfies LMem memberOrderTypeRelation
            ![relation, domain, x, z] := by
        exact (hgraph x z).mp
          ((graphValue_lCarrier_iff_graphRel graph x z).mp hvalue) |>.2.2
      exact w.unique x y z hx hyOrdinal hz hformula hzFormula |>.symm
  · intro y hy
    rcases w.onto y hy with ⟨x, hx, hformula⟩
    refine ⟨x, hx, ?_, ?_⟩
    · apply (graphValue_lCarrier_iff_graphRel graph x y).mpr
      exact (hgraph x y).mpr ⟨mem_unionLCarrier_iff domain w.ordinal x |>.mpr (Or.inl hx),
        mem_unionLCarrier_iff domain w.ordinal y |>.mpr (Or.inr hy), hformula⟩
    · intro z hz hvalue
      have hzFormula :
          FOFormula.Satisfies LMem memberOrderTypeRelation
            ![relation, domain, z, y] := by
        exact (hgraph z y).mp
          ((graphValue_lCarrier_iff_graphRel graph z y).mp hvalue) |>.2.2
      exact w.injective z x y hz hx hy hzFormula hformula

/-! ## Reduction to the cardinal-representative interface -/

/--
If every internally well-ordered set has the explicit order-type witness
above, then every constructible set has an internal cardinal representative.
The hypothesis is exactly the remaining order-type recursion theorem; it is
not discharged by an external `Equiv`.
-/
private theorem hasInternalCardinalRepresentatives_of_orderTypeWitness
    (h : forall domain : LCarrier.{u},
      exists relation : LCarrier.{u},
        InternallyWellOrders relation domain /\
          Nonempty (InternalOrderTypeWitness relation domain)) :
    HasInternalCardinalRepresentatives.{u} := by
  intro domain
  rcases h domain with ⟨relation, _hwell, ⟨w⟩⟩
  rcases internalEquinumerous_ordinal_of_orderTypeWitness w with
    ⟨graph, hbij⟩
  rcases exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal
      w.ordinal w.ordinal_spec with ⟨alpha, halpha⟩
  have hEquiv : Equinumerous LMem domain (ordinalLCarrier alpha) := by
    rw [← halpha]
    exact ⟨graph, hbij⟩
  exact exists_internalCardinalRepresentative_of_ordinalRepresentative
    domain ⟨alpha, hEquiv⟩

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalCardinalRepresentativeInterface

/- Source module: Solutions.Work_CUGCH_InternalOrderTypeWitnessConstruction -/
section GCHSource_Work_CUGCH_InternalOrderTypeWitnessConstruction
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Constructing the internal order-type witness

The pointwise well-founded induction is assembled into the explicit
`InternalOrderTypeWitness` required by the cardinal-representative interface.
The target is the ordinary order type of the universe-small presentation,
represented by its von Neumann code in `L`.  The formula
`memberOrderTypeRelation` is proved total, bounded, single-valued, injective,
and onto that target.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section





/-- Internal well-orderability now gives internal cardinal representatives,
with no additional order-type-recursion hypothesis. -/
private theorem hasInternalCardinalRepresentatives_of_modelsInternalWellOrdering
    (hwellOrder : ModelsInternalWellOrdering.{u}) :
    HasInternalCardinalRepresentatives.{u} := by
  apply hasInternalCardinalRepresentatives_of_orderTypeWitness
  intro domain
  rcases hwellOrder domain with ⟨relation, hwell⟩
  exact ⟨relation, hwell,
    ⟨canonicalInternalOrderTypeWitness relation domain hwell⟩⟩

/-- The recursively constructed stage well-orders yield internal cardinal
representatives for every constructible set. -/
private theorem hasInternalCardinalRepresentatives_lCarrier :
    HasInternalCardinalRepresentatives.{u} :=
  hasInternalCardinalRepresentatives_of_modelsInternalWellOrdering
    (Constructible.Model.modelsInternalWellOrdering_of_allStages
      Constructible.Model.allStagesInternallyWellOrdered_of_historyData)

end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalOrderTypeWitnessConstruction

/- Source module: Solutions.Work_CUGCH_InternalOrdinalProductOrder -/
section GCHSource_Work_CUGCH_InternalOrdinalProductOrder
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# The maximum-lexicographic order on an internal ordinal square

For a von Neumann ordinal `kappa`, this file constructs the standard order on
`kappa x kappa`: first compare the maximum of the two coordinates, and then
compare the coordinates lexicographically.  The relation is obtained by
Separation from a fixed first-order formula, so its graph is an actual member
of the constructible universe.

This is the well-order used in the usual proof that every infinite cardinal
absorbs its square.  No ambient cardinal comparison is used as an internal
function witness.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## Formula and exact semantics -/







/-- Each input to a membership maximum belongs to the successor of that
maximum. -/
private theorem IsMaximumOf.mem_successor_lCarrier
    {left right maximum : LCarrier.{u}}
    (hmaximum : IsMaximumOf LMem left right maximum) :
    left.1 ∈ (successorLCarrier maximum).1 /\
      right.1 ∈ (successorLCarrier maximum).1 := by
  rw [successorLCarrier_val,
    ZFSet.mem_insert_iff, ZFSet.mem_insert_iff]
  rcases hmaximum with ⟨hleftRight, hmaximum⟩ |
    ⟨hrightLeft, hmaximum⟩
  · rw [hmaximum]
    constructor
    · rcases hleftRight with hmem | heq
      · exact Or.inr hmem
      · exact Or.inl (congrArg Subtype.val heq)
    · exact Or.inl rfl
  · rw [hmaximum]
    exact ⟨Or.inl rfl, Or.inr hrightLeft⟩

/-- Membership maxima are unique. -/
private theorem IsMaximumOf.unique_lCarrier
    {left right first second : LCarrier.{u}}
    (hfirst : IsMaximumOf LMem left right first)
    (hsecond : IsMaximumOf LMem left right second) :
    first = second := by
  rcases hfirst with ⟨hleftRight, hfirst⟩ |
    ⟨hrightLeft, hfirst⟩ <;>
    rcases hsecond with ⟨hleftRight', hsecond⟩ |
      ⟨hrightLeft', hsecond⟩
  · exact hfirst.trans hsecond.symm
  · exfalso
    rcases hleftRight with hmem | heq
    · exact ZFSet.mem_asymm hmem hrightLeft'
    · rw [← heq] at hrightLeft'
      exact ZFSet.mem_irrefl left.1 hrightLeft'
  · exfalso
    rcases hleftRight' with hmem | heq
    · exact ZFSet.mem_asymm hmem hrightLeft
    · rw [← heq] at hrightLeft
      exact ZFSet.mem_irrefl left.1 hrightLeft
  · exact hfirst.trans hsecond.symm

/-- Two members of a von Neumann ordinal have a membership maximum. -/
private theorem exists_maximum_lCarrier_of_mem_ordinal
    {kappa left right : LCarrier.{u}}
    (hkappa : IsVonNeumannOrdinal LMem kappa)
    (hleft : left.1 ∈ kappa.1) (hright : right.1 ∈ kappa.1) :
    exists maximum : LCarrier.{u},
      IsMaximumOf LMem left right maximum := by
  have hkappaRaw : kappa.1.IsOrdinal :=
    (isVonNeumannOrdinal_lCarrier_iff kappa).mp hkappa
  have hleftOrdinal := hkappaRaw.mem hleft
  have hrightOrdinal := hkappaRaw.mem hright
  rcases ZFSet.IsOrdinal.mem_trichotomous hleftOrdinal hrightOrdinal with
    hlt | heq | hgt
  · exact ⟨right, Or.inl ⟨Or.inl hlt, rfl⟩⟩
  · exact ⟨right, Or.inl ⟨Or.inr (Subtype.ext heq), rfl⟩⟩
  · exact ⟨left, Or.inr ⟨hgt, rfl⟩⟩















/-! ## The represented relation -/





/-! ## The external presentation of the internal product -/









/-! ## The represented relation is a well-order -/





/-! ## Bounds for strict initial segments -/



/-- Uniform version of the preceding bound: for a fixed point, one smaller
ordinal square contains its entire strict initial segment. -/
private theorem exists_uniform_bound_for_ordinalPairMaximumLexGraph
    {kappa point : LCarrier.{u}}
    (hkappa : IsVonNeumannOrdinal LMem kappa)
    (hsuccessor : forall bound : LCarrier.{u}, bound.1 ∈ kappa.1 ->
      (successorLCarrier bound).1 ∈ kappa.1)
    (hpoint : point.1 ∈ (prodLCarrier kappa kappa).1) :
    exists bound : LCarrier.{u},
      bound.1 ∈ kappa.1 /\
        forall predecessor : LCarrier.{u},
          predecessor.1 ∈ (prodLCarrier kappa kappa).1 ->
            GraphRel (ordinalPairMaximumLexGraph kappa) predecessor point ->
              predecessor.1 ∈ (prodLCarrier bound bound).1 := by
  have hpointRaw := hpoint
  change point.1 ∈ ZFSet.prod kappa.1 kappa.1 at hpointRaw
  rcases ZFSet.mem_prod.mp hpointRaw with
    ⟨rightFirstRaw, hrightFirst, rightSecondRaw, hrightSecond,
      hpointPair⟩
  let rightFirst : LCarrier.{u} :=
    ⟨rightFirstRaw, Constructible.mem_L_of_mem hrightFirst kappa.2⟩
  let rightSecond : LCarrier.{u} :=
    ⟨rightSecondRaw, Constructible.mem_L_of_mem hrightSecond kappa.2⟩
  rcases exists_maximum_lCarrier_of_mem_ordinal hkappa
      (left := rightFirst) (right := rightSecond)
      hrightFirst hrightSecond with
    ⟨rightMaximum, hrightMaximum⟩
  have hrightMaximumMem : rightMaximum.1 ∈ kappa.1 := by
    rcases hrightMaximum with ⟨_rightLe, hmaximum⟩ |
      ⟨_leftLt, hmaximum⟩
    · rw [hmaximum]
      exact hrightSecond
    · rw [hmaximum]
      exact hrightFirst
  have hrightMaximumOrdinal : rightMaximum.1.IsOrdinal := by
    have hkappaRaw : kappa.1.IsOrdinal :=
      (isVonNeumannOrdinal_lCarrier_iff kappa).mp hkappa
    exact hkappaRaw.mem hrightMaximumMem
  let bound := successorLCarrier rightMaximum
  refine ⟨bound, hsuccessor rightMaximum hrightMaximumMem, ?_⟩
  intro predecessor hpredecessor hpredecessorPoint
  have hrel := (graphRel_ordinalPairMaximumLexGraph_iff
    kappa predecessor point).mp hpredecessorPoint |>.2.2
  rcases hrel with
    ⟨leftFirst, leftSecond, rightFirst', rightSecond',
      leftMaximum, rightMaximum', hleftPair, hrightPair,
      hleftMaximum, hrightMaximum', hcomparison⟩
  have hleftPairEq := (isKuratowskiPairOf_lCarrier_iff
    predecessor leftFirst leftSecond).mp hleftPair
  have hrightPairEq := (isKuratowskiPairOf_lCarrier_iff
    point rightFirst' rightSecond').mp hrightPair
  have hrightCoordinates := ZFSet.pair_inj.mp
    (show ZFSet.pair rightFirst.1 rightSecond.1 =
        ZFSet.pair rightFirst'.1 rightSecond'.1 by
      exact hpointPair.symm.trans hrightPairEq)
  have hrightFirstEq : rightFirst' = rightFirst :=
    Subtype.ext hrightCoordinates.1.symm
  have hrightSecondEq : rightSecond' = rightSecond :=
    Subtype.ext hrightCoordinates.2.symm
  subst rightFirst'
  subst rightSecond'
  have hrightMaximumEq : rightMaximum' = rightMaximum :=
    hrightMaximum'.unique_lCarrier hrightMaximum
  rw [hrightMaximumEq] at hcomparison
  have hmaximumLe :
      leftMaximum.1 ∈ rightMaximum.1 \/ leftMaximum = rightMaximum := by
    rcases hcomparison with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr heq.1
  have promote : forall coordinate : LCarrier.{u},
      coordinate.1 ∈ (successorLCarrier leftMaximum).1 ->
        coordinate.1 ∈ bound.1 := by
    intro coordinate hcoordinate
    rcases hmaximumLe with hlt | heq
    · rw [successorLCarrier_val, ZFSet.mem_insert_iff] at hcoordinate
      change coordinate.1 ∈ (successorLCarrier rightMaximum).1
      rw [successorLCarrier_val, ZFSet.mem_insert_iff]
      rcases hcoordinate with hcoordinateEq | hcoordinateMem
      · apply Or.inr
        rw [hcoordinateEq]
        exact hlt
      · exact Or.inr
          (hrightMaximumOrdinal.mem_trans hcoordinateMem hlt)
    · rw [heq] at hcoordinate
      exact hcoordinate
  have hleftInSuccessor := hleftMaximum.mem_successor_lCarrier
  change predecessor.1 ∈ ZFSet.prod bound.1 bound.1
  rw [hleftPairEq, ZFSet.pair_mem_prod]
  exact ⟨promote leftFirst hleftInSuccessor.1,
    promote leftSecond hleftInSuccessor.2⟩

/-- The canonical order type of every strict initial segment internally
injects into a smaller ordinal square. -/
private theorem canonicalMemberOrderType_injects_smaller_ordinalSquare
    {kappa point : LCarrier.{u}}
    (hkappa : IsVonNeumannOrdinal LMem kappa)
    (hsuccessor : forall bound : LCarrier.{u}, bound.1 ∈ kappa.1 ->
      (successorLCarrier bound).1 ∈ kappa.1)
    (hpoint : point.1 ∈ (prodLCarrier kappa kappa).1) :
    exists bound : LCarrier.{u},
      bound.1 ∈ kappa.1 /\
        Injects LMem
          (canonicalMemberOrderTypeLCarrier
            (ordinalPairMaximumLexGraph kappa)
            (prodLCarrier kappa kappa)
            (ordinalPairMaximumLexGraph_internallyWellOrders kappa hkappa)
            point hpoint)
          (prodLCarrier bound bound) := by
  let relation := ordinalPairMaximumLexGraph kappa
  let domain := prodLCarrier kappa kappa
  let hwell : InternallyWellOrders relation domain :=
    ordinalPairMaximumLexGraph_internallyWellOrders kappa hkappa
  rcases exists_uniform_bound_for_ordinalPairMaximumLexGraph
      hkappa hsuccessor hpoint with
    ⟨bound, hbound, hboundProperty⟩
  have hinitial := canonicalMemberOrderType_isInitial
    relation domain hwell point hpoint
  rcases hinitial with
    ⟨_hordinal, predecessors, hpredecessors, graph, horderIsomorphism⟩
  have hpredecessorsSubset : forall z : LCarrier.{u},
      z.1 ∈ predecessors.1 -> z.1 ∈ (prodLCarrier bound bound).1 := by
    intro z hz
    have hzSemantic := (hpredecessors z).mp hz
    exact hboundProperty z hzSemantic.1
      ((graphValue_lCarrier_iff_graphRel relation z point).mp
        hzSemantic.2)
  have hpredecessorsInject :
      Injects LMem predecessors (prodLCarrier bound bound) :=
    injects_of_subset_lCarrier hpredecessorsSubset
  have horderTypeEquinumerous :
      Equinumerous LMem predecessors
        (canonicalMemberOrderTypeLCarrier relation domain hwell point hpoint) :=
    ⟨graph, horderIsomorphism.1⟩
  refine ⟨bound, hbound, ?_⟩
  change Injects LMem
    (canonicalMemberOrderTypeLCarrier relation domain hwell point hpoint)
    (prodLCarrier bound bound)
  exact horderTypeEquinumerous.symm_lCarrier.injects.trans_lCarrier
    hpredecessorsInject

end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalOrdinalProductOrder

/- Source module: Solutions.Work_CUGCH_InternalOmegaProductAbsorption -/
section GCHSource_Work_CUGCH_InternalOmegaProductAbsorption
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The internally represented injection from omega squared into omega

The graph sends the pair of natural codes `(i,j)` to Wang's prime-power code
`2^i * 3^j`.  The arithmetic is evaluated by the previously verified pure
membership-language formula, and Separation turns that fixed formula into an
actual Kuratowski graph in `L`.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model
open Constructible.FiniteSequenceZF
open Constructible.TextbookNatFormula

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## Formula and exact relation -/















/-- On the product domain, the formula has exactly the advertised numerical
semantics. -/
private theorem OmegaPairCodeRel.exact_of_mem
    {input output : LCarrier.{u}}
    (hinput : input.1 ∈ (prodLCarrier omegaLCarrier omegaLCarrier).1)
    (hrel : OmegaPairCodeRel input output) :
    exists i j : Nat,
      input = orderedPairLCarrier
        (textbookNatCodeLCarrier i) (textbookNatCodeLCarrier j) /\
      output = textbookNatCodeLCarrier (textbookECode i j 0) := by
  rcases hrel with ⟨left, right, hpair, hformula⟩
  have hpairRaw :=
    (isKuratowskiPairOf_lCarrier_iff input left right).mp hpair
  have hcoordinates :
      left.1 ∈ omegaLCarrier.1 /\ right.1 ∈ omegaLCarrier.1 := by
    change input.1 ∈ ZFSet.prod omegaLCarrier.1 omegaLCarrier.1 at hinput
    rw [hpairRaw, ZFSet.pair_mem_prod] at hinput
    exact hinput
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode left.1).mp
      hcoordinates.1 with ⟨i, hi⟩
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode right.1).mp
      hcoordinates.2 with ⟨j, hj⟩
  have hleft : left = textbookNatCodeLCarrier i := Subtype.ext hi
  have hright : right = textbookNatCodeLCarrier j := Subtype.ext hj
  subst left
  subst right
  have houtputRaw : output.1 = natCode (textbookECode i j 0) :=
    (satisfies_textbookECodeFormula_lCarrier_natCode_iff
      i j 0 output).mp hformula
  refine ⟨i, j, ?_, Subtype.ext houtputRaw⟩
  apply Subtype.ext
  exact hpairRaw

/-! ## The internal injection -/

/-- The textbook prime-power pairing is represented by an actual internal
injection `omega x omega -> omega`. -/
private theorem injects_omegaProduct_omega_lCarrier :
    Injects LMem
      (prodLCarrier (omegaLCarrier : LCarrier.{u}) omegaLCarrier)
      omegaLCarrier := by
  let domain : LCarrier.{u} := prodLCarrier omegaLCarrier omegaLCarrier
  let zero : LCarrier.{u} := textbookNatCodeLCarrier 0
  let support : LCarrier.{u} := unionLCarrier domain omegaLCarrier
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      omegaPairCodeFormula ![omegaLCarrier, zero, domain] support with
    ⟨graph, hsupport, hrelation⟩
  have hvalue : forall input output : LCarrier.{u},
      GraphValue LMem graph input output <->
        input.1 ∈ domain.1 /\ OmegaPairCodeRel input output := by
    intro input output
    rw [graphValue_lCarrier_iff_graphRel, hrelation]
    constructor
    · rintro ⟨_hinputSupport, _houtputSupport, hformula⟩
      have hsemantic := (satisfies_omegaPairCodeRelation
        omegaLCarrier zero domain input output).mp hformula
      exact ⟨hsemantic.1, hsemantic.2⟩
    · rintro ⟨hinput, hrel⟩
      rcases hrel.exact_of_mem hinput with ⟨i, j, _hinputEq, houtputEq⟩
      have houtputOmega : output.1 ∈ omegaLCarrier.1 := by
        rw [houtputEq]
        exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode (textbookECode i j 0))).mpr
            ⟨textbookECode i j 0, rfl⟩
      refine ⟨(mem_unionLCarrier_iff domain omegaLCarrier input).mpr
          (Or.inl hinput),
        (mem_unionLCarrier_iff domain omegaLCarrier output).mpr
          (Or.inr houtputOmega), ?_⟩
      exact (satisfies_omegaPairCodeRelation
        omegaLCarrier zero domain input output).mpr ⟨hinput, hrel⟩
  have hbetween : IsGraphBetween LMem graph domain omegaLCarrier := by
    intro pair hpair
    rcases hsupport pair hpair with
      ⟨input, output, _hinputSupport, _houtputSupport,
        hpairEq, hformula⟩
    have hsemantic := (satisfies_omegaPairCodeRelation
      omegaLCarrier zero domain input output).mp hformula
    have hinput : input.1 ∈ domain.1 := hsemantic.1
    have hrel : OmegaPairCodeRel input output := hsemantic.2
    rcases hrel.exact_of_mem hinput with ⟨i, j, _hinputEq, houtputEq⟩
    have houtput : output.1 ∈ omegaLCarrier.1 := by
      rw [houtputEq]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
        ⟨textbookECode i j 0, rfl⟩
    exact ⟨input, hinput, output, houtput,
      (isKuratowskiPairOf_lCarrier_iff pair input output).mpr hpairEq⟩
  refine ⟨graph, hbetween, ?_, ?_⟩
  · intro input hinput
    change input.1 ∈ ZFSet.prod omegaLCarrier.1 omegaLCarrier.1 at hinput
    rcases ZFSet.mem_prod.mp hinput with
      ⟨leftRaw, hleft, rightRaw, hright, hinputRaw⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode leftRaw).mp
      hleft with ⟨i, hi⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode rightRaw).mp
      hright with ⟨j, hj⟩
    let output := textbookNatCodeLCarrier (textbookECode i j 0)
    have houtput : output.1 ∈ omegaLCarrier.1 :=
      (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
        ⟨textbookECode i j 0, rfl⟩
    have hinputEq : input = orderedPairLCarrier
        (textbookNatCodeLCarrier i) (textbookNatCodeLCarrier j) := by
      apply Subtype.ext
      simpa only [hi, hj, orderedPairLCarrier_val,
        textbookNatCodeLCarrier_val] using hinputRaw
    have hrel : OmegaPairCodeRel input output := by
      refine ⟨textbookNatCodeLCarrier i, textbookNatCodeLCarrier j, ?_, ?_⟩
      · apply (isKuratowskiPairOf_lCarrier_iff input
          (textbookNatCodeLCarrier i) (textbookNatCodeLCarrier j)).mpr
        rw [hinputEq]
        rfl
      · exact (satisfies_textbookECodeFormula_lCarrier_natCode_iff
          i j 0 output).mpr rfl
    refine ⟨output, houtput, (hvalue input output).mpr ⟨hinput, hrel⟩, ?_⟩
    intro other _hother hotherValue
    rcases ((hvalue input other).mp hotherValue).2.exact_of_mem hinput with
      ⟨i', j', hinputEq', hotherEq⟩
    have hpairs := ZFSet.pair_inj.mp
      (congrArg Subtype.val (hinputEq.symm.trans hinputEq'))
    have hiEq : i = i' := natCode_injective hpairs.1
    have hjEq : j = j' := natCode_injective hpairs.2
    subst i'
    subst j'
    exact hotherEq.trans rfl
  · intro output houtput input hinput hinputValue
      other hother hotherValue
    rcases ((hvalue input output).mp hinputValue).2.exact_of_mem hinput with
      ⟨i, j, hinputEq, houtputEq⟩
    rcases ((hvalue other output).mp hotherValue).2.exact_of_mem hother with
      ⟨i', j', hotherEq, houtputEq'⟩
    have hcodesRaw := congrArg Subtype.val
      (houtputEq.symm.trans houtputEq')
    have hcodes : textbookECode i j 0 = textbookECode i' j' 0 :=
      natCode_injective hcodesRaw
    have hfields := textbookECode_injective_fields hcodes
    apply hotherEq.trans
    rw [← hfields.1, ← hfields.2.1]
    exact hinputEq.symm

end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalOmegaProductAbsorption

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

private theorem omegaLCarrier_eq_ordinalLCarrier :
    (omegaLCarrier : LCarrier.{u}) = ordinalLCarrier Ordinal.omega0 := by
  apply Subtype.ext
  rfl

private theorem ordinal_le_of_subset_lCarrier
    {alpha beta : Ordinal.{u}}
    (hsubset : IsSubsetOf LMem
      (ordinalLCarrier alpha) (ordinalLCarrier beta)) :
    alpha <= beta := by
  apply Ordinal.toZFSet_subset_toZFSet_iff.mp
  intro z hz
  let zL : LCarrier.{u} :=
    ⟨z, Constructible.mem_L_of_mem hz (ordinalLCarrier alpha).2⟩
  exact hsubset zL hz

private theorem ordinal_subset_lCarrier_of_le
    {alpha beta : Ordinal.{u}} (h : alpha <= beta) :
    IsSubsetOf LMem (ordinalLCarrier alpha) (ordinalLCarrier beta) := by
  intro z hz
  exact Ordinal.toZFSet_monotone h hz

private theorem ordinal_isSuccLimit_of_cardinal_and_omega_lt
    (alpha : Ordinal.{u})
    (hcardinal : IsCardinal LMem (ordinalLCarrier alpha))
    (homega : Ordinal.omega0 < alpha) :
    Order.IsSuccLimit alpha := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit alpha with
    hzero | ⟨beta, hsuccessor⟩ | hlimit
  · rw [hzero] at homega
    exact (not_lt_of_ge (bot_le : (0 : Ordinal.{u}) <= Ordinal.omega0)
      homega).elim
  · have homegaBeta : Ordinal.omega0 <= beta := by
      rw [← Order.lt_succ_iff, hsuccessor]
      exact homega
    have homegaSubset : IsSubsetOf LMem
        (omegaLCarrier : LCarrier.{u}) (ordinalLCarrier beta) := by
      rw [omegaLCarrier_eq_ordinalLCarrier]
      exact ordinal_subset_lCarrier_of_le homegaBeta
    have hbetaSelf : Injects LMem
        (ordinalLCarrier beta) (ordinalLCarrier beta) :=
      injects_of_subset_lCarrier (fun _ hz => hz)
    have hsuccessorBeta : Injects LMem
        (ordinalLCarrier (Order.succ beta)) (ordinalLCarrier beta) :=
      injects_successorOrdinal_of_omega_subset_lCarrier
        homegaSubset hbetaSelf
    have halphaBeta : Injects LMem
        (ordinalLCarrier alpha) (ordinalLCarrier beta) := by
      rw [← hsuccessor]
      exact hsuccessorBeta
    have hbetaMem :
        (ordinalLCarrier beta).1 ∈ (ordinalLCarrier alpha).1 := by
      apply (ordinalLCarrier_mem_ordinalLCarrier_iff alpha beta).mpr
      rw [← hsuccessor]
      exact Order.lt_succ beta
    exact ((hcardinal.not_injects_of_mem_lCarrier hbetaMem
      internalInjectionAntisymm_lCarrier) halphaBeta).elim
  · exact hlimit

private theorem exists_smaller_cardinal_square_bound
    (alpha : Ordinal.{u})
    (hcardinal : IsCardinal LMem (ordinalLCarrier alpha))
    (homegaLt : Ordinal.omega0 < alpha)
    (hlimit : Order.IsSuccLimit alpha)
    (ih : forall beta : Ordinal.{u}, beta < alpha ->
      IsCardinal LMem (ordinalLCarrier beta) ->
      IsSubsetOf LMem (omegaLCarrier : LCarrier.{u})
        (ordinalLCarrier beta) ->
      Injects LMem
        (prodLCarrier (ordinalLCarrier beta) (ordinalLCarrier beta))
        (ordinalLCarrier beta))
    {bound : LCarrier.{u}}
    (hbound : bound.1 ∈ (ordinalLCarrier alpha).1) :
    exists lambda : LCarrier.{u},
      lambda.1 ∈ (ordinalLCarrier alpha).1 /\
        IsCardinal LMem lambda /\
          Injects LMem (prodLCarrier bound bound) lambda := by
  rcases exists_eq_ordinalLCarrier_of_mem hbound with
    ⟨beta, hbeta, rfl⟩
  let gamma : Ordinal.{u} := max beta Ordinal.omega0
  have hgamma : gamma < alpha := by
    exact max_lt hbeta homegaLt
  have hupper : Order.succ gamma < alpha := hlimit.succ_lt hgamma
  let upper : LCarrier.{u} := ordinalLCarrier (Order.succ gamma)
  have hupperMem : upper.1 ∈ (ordinalLCarrier alpha).1 := by
    exact (ordinalLCarrier_mem_ordinalLCarrier_iff
      alpha (Order.succ gamma)).mpr hupper
  let joined : LCarrier.{u} :=
    unionLCarrier (ordinalLCarrier beta) omegaLCarrier
  have hjoinedUpper : forall z : LCarrier.{u},
      z.1 ∈ joined.1 -> z.1 ∈ upper.1 := by
    intro z hz
    rcases (mem_unionLCarrier_iff
      (ordinalLCarrier beta) omegaLCarrier z).mp hz with hz | hz
    · exact Ordinal.toZFSet_monotone
        (le_trans (le_max_left beta Ordinal.omega0)
          (Order.le_succ gamma)) hz
    · exact Ordinal.toZFSet_monotone
        (le_trans (le_max_right beta Ordinal.omega0)
          (Order.le_succ gamma)) hz
  rcases hasInternalCardinalRepresentatives_lCarrier joined with
    ⟨lambda, hlambdaCardinal, hjoinedLambda⟩
  rcases exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal
      lambda hlambdaCardinal.1 with
    ⟨mu, hlambdaEq⟩
  subst lambda
  have hmuAlpha : mu < alpha := by
    by_contra hnot
    have halphaMu : alpha <= mu := le_of_not_gt hnot
    have halphaToMu : Injects LMem
        (ordinalLCarrier alpha) (ordinalLCarrier mu) :=
      injects_of_subset_lCarrier
        (ordinal_subset_lCarrier_of_le halphaMu)
    have hmuToJoined : Injects LMem
        (ordinalLCarrier mu) joined :=
      hjoinedLambda.symm_lCarrier.injects
    have hjoinedToUpper : Injects LMem joined upper :=
      injects_of_subset_lCarrier hjoinedUpper
    have halphaToUpper :=
      (halphaToMu.trans_lCarrier hmuToJoined).trans_lCarrier
        hjoinedToUpper
    exact (hcardinal.not_injects_of_mem_lCarrier hupperMem
      internalInjectionAntisymm_lCarrier) halphaToUpper
  have homegaToJoined : Injects LMem
      (omegaLCarrier : LCarrier.{u}) joined := by
    apply injects_of_subset_lCarrier
    intro z hz
    exact (mem_unionLCarrier_iff
      (ordinalLCarrier beta) omegaLCarrier z).mpr (Or.inr hz)
  have homegaMuLe : Ordinal.omega0 <= mu := by
    by_contra hnot
    have hmuOmega : mu < Ordinal.omega0 := lt_of_not_ge hnot
    have hmuMemOmega :
        (ordinalLCarrier mu).1 ∈ omegaLCarrier.1 := by
      exact (ordinalLCarrier_mem_ordinalLCarrier_iff
        Ordinal.omega0 mu).mpr hmuOmega
    have homegaToMu : Injects LMem
        (omegaLCarrier : LCarrier.{u}) (ordinalLCarrier mu) :=
      homegaToJoined.trans_lCarrier hjoinedLambda.injects
    exact (omegaLCarrier_isCardinal.not_injects_of_mem_lCarrier
      hmuMemOmega internalInjectionAntisymm_lCarrier) homegaToMu
  have homegaMu : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) (ordinalLCarrier mu) := by
    rw [omegaLCarrier_eq_ordinalLCarrier]
    exact ordinal_subset_lCarrier_of_le homegaMuLe
  have hmuSquare : Injects LMem
      (prodLCarrier (ordinalLCarrier mu) (ordinalLCarrier mu))
      (ordinalLCarrier mu) :=
    ih mu hmuAlpha hlambdaCardinal homegaMu
  have hboundToJoined : Injects LMem
      (ordinalLCarrier beta) joined := by
    apply injects_of_subset_lCarrier
    intro z hz
    exact (mem_unionLCarrier_iff
      (ordinalLCarrier beta) omegaLCarrier z).mpr (Or.inl hz)
  have hboundToMu : Injects LMem
      (ordinalLCarrier beta) (ordinalLCarrier mu) :=
    hboundToJoined.trans_lCarrier hjoinedLambda.injects
  have hboundSquareToMuSquare : Injects LMem
      (prodLCarrier (ordinalLCarrier beta) (ordinalLCarrier beta))
      (prodLCarrier (ordinalLCarrier mu) (ordinalLCarrier mu)) :=
    injects_prod_of_injects_lCarrier hboundToMu hboundToMu
  exact ⟨ordinalLCarrier mu,
    (ordinalLCarrier_mem_ordinalLCarrier_iff alpha mu).mpr hmuAlpha,
    hlambdaCardinal,
    hboundSquareToMuSquare.trans_lCarrier hmuSquare⟩

private theorem injects_infiniteCardinalSquare_ordinalLCarrier :
    forall alpha : Ordinal.{u},
      IsCardinal LMem (ordinalLCarrier alpha) ->
      IsSubsetOf LMem (omegaLCarrier : LCarrier.{u})
        (ordinalLCarrier alpha) ->
      Injects LMem
        (prodLCarrier (ordinalLCarrier alpha) (ordinalLCarrier alpha))
        (ordinalLCarrier alpha) := by
  intro alpha
  apply (IsWellFounded.wf :
    WellFounded ((· < ·) : Ordinal.{u} -> Ordinal.{u} -> Prop)).induction
      alpha
  intro alpha ih hcardinal homega
  by_cases halphaOmega : alpha = Ordinal.omega0
  · subst alpha
    simpa only [omegaLCarrier_eq_ordinalLCarrier] using
      injects_omegaProduct_omega_lCarrier
  · have homegaLe : Ordinal.omega0 <= alpha := by
      apply ordinal_le_of_subset_lCarrier
      simpa only [omegaLCarrier_eq_ordinalLCarrier] using homega
    have homegaNe : Not (Ordinal.omega0 = alpha) := by
      intro h
      exact halphaOmega h.symm
    have homegaLt : Ordinal.omega0 < alpha :=
      lt_of_le_of_ne homegaLe homegaNe
    have hlimit : Order.IsSuccLimit alpha :=
      ordinal_isSuccLimit_of_cardinal_and_omega_lt
        alpha hcardinal homegaLt
    let relation := ordinalPairMaximumLexGraph (ordinalLCarrier alpha)
    let domain := prodLCarrier
      (ordinalLCarrier alpha) (ordinalLCarrier alpha)
    let hwell : InternallyWellOrders relation domain :=
      ordinalPairMaximumLexGraph_internallyWellOrders
        (ordinalLCarrier alpha) hcardinal.1
    let tau := canonicalOrderType relation domain hwell
    have hsuccessor : forall bound : LCarrier.{u},
        bound.1 ∈ (ordinalLCarrier alpha).1 ->
          (successorLCarrier bound).1 ∈ (ordinalLCarrier alpha).1 := by
      intro bound hbound
      rcases exists_eq_ordinalLCarrier_of_mem hbound with
        ⟨beta, hbeta, rfl⟩
      rw [successorLCarrier_ordinalLCarrier]
      exact (ordinalLCarrier_mem_ordinalLCarrier_iff
        alpha (Order.succ beta)).mpr (hlimit.succ_lt hbeta)
    have htauLe : tau <= alpha := by
      by_contra hnot
      have halphaTau : alpha < tau := lt_of_not_ge hnot
      rcases exists_member_canonicalOrderType_eq_of_lt
          relation domain hwell halphaTau with
        ⟨point, hpoint, hpointType⟩
      rcases canonicalMemberOrderType_injects_smaller_ordinalSquare
          hcardinal.1 hsuccessor hpoint with
        ⟨bound, hbound, htypeBound⟩
      rcases exists_smaller_cardinal_square_bound
          alpha hcardinal homegaLt hlimit ih hbound with
        ⟨lambda, hlambda, _hlambdaCardinal, hboundLambda⟩
      have halphaBound : Injects LMem
          (ordinalLCarrier alpha) (prodLCarrier bound bound) := by
        simpa only [relation, domain, hwell,
          canonicalMemberOrderTypeLCarrier, hpointType] using htypeBound
      have halphaLambda :=
        halphaBound.trans_lCarrier hboundLambda
      exact (hcardinal.not_injects_of_mem_lCarrier hlambda
        internalInjectionAntisymm_lCarrier) halphaLambda
    let witness := canonicalInternalOrderTypeWitness relation domain hwell
    rcases internalEquinumerous_ordinal_of_orderTypeWitness witness with
      ⟨graph, hgraph⟩
    have hdomainTau : Equinumerous LMem domain (ordinalLCarrier tau) := by
      simpa only [witness, canonicalInternalOrderTypeWitness, tau] using
        (show Equinumerous LMem domain witness.ordinal from ⟨graph, hgraph⟩)
    have htauAlpha : Injects LMem
        (ordinalLCarrier tau) (ordinalLCarrier alpha) :=
      injects_of_subset_lCarrier
        (ordinal_subset_lCarrier_of_le htauLe)
    exact hdomainTau.injects.trans_lCarrier htauAlpha

/-- Every internally infinite initial ordinal has an internally represented
injection from its Cartesian square into itself. -/
private theorem injects_infiniteCardinalSquare_lCarrier_gchProof07
    {kappa : LCarrier.{u}}
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa) :
    Injects LMem (prodLCarrier kappa kappa) kappa := by
  rcases exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal
      kappa hcardinal.1 with
    ⟨alpha, rfl⟩
  exact injects_infiniteCardinalSquare_ordinalLCarrier
    alpha hcardinal homega



end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalInfiniteCardinalSquare

universe u

theorem solution : ∀ {kappa : Constructible.Model.LCarrier.{u}},
  @Constructible.ContinuumFormula.IsCardinal.{u + 1} Constructible.Model.LCarrier.{u}
      Constructible.Model.lCarrierMem.{u} kappa →
    @Constructible.ContinuumFormula.IsSubsetOf.{u + 1} Constructible.Model.LCarrier.{u}
        Constructible.Model.lCarrierMem.{u} Constructible.Model.omegaLCarrier.{u} kappa →
      @Constructible.ContinuumFormula.Injects.{u + 1} Constructible.Model.LCarrier.{u}
        Constructible.Model.lCarrierMem.{u} (Constructible.Model.prodLCarrier.{u} kappa kappa) kappa :=
  @Constructible.ContinuumFormula.injects_infiniteCardinalSquare_lCarrier_gchProof07.{u}
