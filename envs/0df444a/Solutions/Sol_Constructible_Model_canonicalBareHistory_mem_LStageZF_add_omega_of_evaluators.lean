-- Prove2me | solution 1 for Constructible.Model.canonicalBareHistory_mem_LStageZF_add_omega_of_evaluators
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-25T23:45:13.86298+00:00
-- url     : https://prove2.me/submissions/cdf5f74b-edb9-4990-9e9a-511366f378df

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































/-- Earlier levels occur as elements of every strictly later level. -/
private theorem LStageZF_mem_of_lt {α β : Ordinal.{u}} (hαβ : α < β) :
    LStageZF α ∈ LStageZF β := by
  exact LStageZF_mono (Order.succ_le_of_lt hαβ)
    (LStageZF_mem_succ α)













































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

/- Source module: Solutions.Work_CUGCH_BareStageHistory -/
section GCHSource_Work_CUGCH_BareStageHistory
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/







/-!
# Relation-free histories for the constructible hierarchy

This file is a proof tool; it does not define a different constructible
hierarchy.  In ordinary set-theoretic language, a bare history through an
ordinal `a` is a set-coded partial function `h` whose value at every
`i <= a` is a set `S_i`, with

* `S_0 = empty`;
* `S_(i+1) = Def(S_i)`;
* `S_l = union (i < l) S_i` when `l` is a nonzero limit ordinal.

The Lean representation uses Kuratowski pairs: `BareHistoryEntry h i s`
means exactly that `<i,s>` belongs to the internal `ZFSet` underlying `h`.
Unlike `ValidStageHistory`, no canonical well-order relation is stored in an
entry or mentioned by the local recursion rule.

The formula interfaces below use the exact quantifiers displayed by the
semantic predicates.  They still reuse `godelDefOutputFormula` at successor
steps, so their first thirteen coordinates are the existing evaluator
parameters `(varTag, appTag, empty, op0, ..., op8, omega)`.  Consequently this
file, by itself, does not assert that those parameters belong to `L_omega`,
nor does it claim absoluteness in every limit level.  The special `L_omega`
case must be handled separately before this tool can support the unrestricted
Condensation Lemma.
-/

section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## Pair-coded history entries -/















/-! ## The exact zero, successor, and limit clauses -/



















































/-! ## Bounded total functional histories -/



















/-! ## A history-independent stage-output formula -/













/-! ## Full-`L` existence via a relation-forgetting projection -/



















/-! ## Identification with the previously defined hierarchy -/

























/-! ## Raw semantics over a transitive set -/

/-- A bounded formula interpreted with all quantifiers restricted to a
transitive `ZFSet` agrees with ambient bounded satisfaction whenever every
free variable lies in that set. -/
private theorem satisfiesIn_delta0_toFO_absolute
    {U : ZFSet.{u}} (hU : U.IsTransitive) {n : Nat}
    (formula : Delta0Formula n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) formula.toFO s ↔
      Delta0Formula.Satisfies Delta0Formula.ZFMem formula s := by
  let sU : Tuple (ZFCarrier U) n := fun i => ⟨s i, hs i⟩
  calc
    SatisfiesIn (U : Set ZFSet.{u}) formula.toFO s ↔
        SatisfiesIn (U : Set ZFSet.{u}) formula.toFO
          (fun i => (sU i).1) := by rfl
    _ ↔ FOFormula.Satisfies (zfCarrierMem U) formula.toFO sU :=
      (satisfies_subtype_iff_satisfiesIn
        (U : Set ZFSet.{u}) formula.toFO sU).symm
    _ ↔ Delta0Formula.Satisfies (zfCarrierMem U) formula sU :=
      Delta0Formula.satisfies_toFO (zfCarrierMem U) formula sU
    _ ↔ Delta0Formula.Satisfies Delta0Formula.ZFMem formula
          (Delta0Formula.val sU) :=
      Delta0Formula.satisfies_absolute hU formula sU
    _ ↔ Delta0Formula.Satisfies Delta0Formula.ZFMem formula s := by
      rfl





/-- Pair-code equality is bounded-absolute over every transitive carrier
containing its three displayed arguments. -/
private theorem satisfiesIn_kuratowskiPairEqAt_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive) {n : Nat}
    (pair index stage : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u})
        (Delta0Formula.kuratowskiPairEqAt pair index stage).toFO s ↔
      s pair = ZFSet.pair (s index) (s stage) := by
  rw [satisfiesIn_delta0_toFO_absolute hU _ s hs,
    Delta0Formula.satisfies_kuratowskiPairEqAt]

/-- Exact raw semantics of a pair-coded entry inside an arbitrary transitive
set.  The reverse direction needs no Pairing axiom: if the pair belongs to
`history` and `history ∈ U`, transitivity already puts the witness in `U`. -/
private theorem satisfiesIn_bareHistoryEntryAt_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive) {n : Nat}
    (history index stage : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u})
        (bareHistoryEntryAt history index stage) s ↔
      ZFSet.pair (s index) (s stage) ∈ s history := by
  simp only [bareHistoryEntryAt, SatisfiesIn]
  constructor
  · rintro ⟨entry, hentryU, hentry, hpair⟩
    change entry ∈ U at hentryU
    have hentry' : entry ∈ s history := by
      simpa only [snoc_last, snoc_castSucc] using hentry
    have hsSnoc : ∀ i, snoc s entry i ∈ U := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [snoc_last] using hentryU
      · simpa only [snoc_castSucc] using hs j
    have heq := (satisfiesIn_kuratowskiPairEqAt_iff hU
      (Fin.last n) index.castSucc stage.castSucc
      (snoc s entry) hsSnoc).mp hpair
    have heq' : entry = ZFSet.pair (s index) (s stage) := by
      simpa only [snoc_last, snoc_castSucc] using heq
    rw [heq'] at hentry'
    exact hentry'
  · intro hentry
    let entry := ZFSet.pair (s index) (s stage)
    have hentryU : entry ∈ U := hU.mem_trans hentry (hs history)
    refine ⟨entry, ?_, ?_, ?_⟩
    · exact hentryU
    · simpa only [snoc_last, snoc_castSucc] using hentry
    have hsSnoc : ∀ i, snoc s entry i ∈ U := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [snoc_last] using hentryU
      · simpa only [snoc_castSucc] using hs j
    apply (satisfiesIn_kuratowskiPairEqAt_iff hU
      (Fin.last n) index.castSucc stage.castSucc
      (snoc s entry) hsSnoc).mpr
    simp only [snoc_last, snoc_castSucc, entry]





/-- The base formula has no hidden quantifiers: it literally identifies the
index and stage coordinates with coordinate `2` of the supplied prefix. -/
private theorem satisfiesIn_bareHistoryBaseStateFormula_iff
    (U : Set ZFSet.{u}) (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) :
    SatisfiesIn U bareHistoryBaseStateFormula
        (bareHistoryStateRawAssignment fixed history index stage) ↔
      index = fixed (2 : Fin 13) ∧
      stage = fixed (2 : Fin 13) := by
  change
    (bareHistoryStateRawAssignment fixed history index stage (14 : Fin 16) =
      bareHistoryStateRawAssignment fixed history index stage (2 : Fin 16) ∧
    bareHistoryStateRawAssignment fixed history index stage (15 : Fin 16) =
      bareHistoryStateRawAssignment fixed history index stage (2 : Fin 16))
      ↔ _
  change (index = fixed (2 : Fin 13) ∧
    stage = fixed (2 : Fin 13)) ↔ _
  rfl

private theorem satisfiesIn_bare_all_iff
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s ↔
      ∀ x : ZFSet.{u}, x ∈ M →
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

private theorem satisfiesIn_bare_biimp_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.biimp left right) s ↔
      (SatisfiesIn M left s ↔ SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.biimp, FOFormula.imp, FOFormula.disj,
    SatisfiesIn]
  tauto

private theorem satisfiesIn_bare_boundedEx_iff
    (M : Set ZFSet.{u}) {n : Nat} (i : Fin n)
    (formula : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.boundedEx i formula) s ↔
      ∃ x : ZFSet.{u}, x ∈ M ∧ x ∈ s i ∧
        SatisfiesIn M formula (snoc s x) := by
  simp [FOFormula.boundedEx, SatisfiesIn]



/-- First expansion of the limit formula.  This theorem deliberately leaves
the nested entry formula visible; the next theorem applies transitive
bounded absoluteness to identify it with pair membership. -/
private theorem satisfiesIn_bareHistoryLimitStateFormula_components
    (U : Set ZFSet.{u}) (history index stage : ZFSet.{u}) :
    SatisfiesIn U bareHistoryLimitStateFormula
        (bareHistoryLimitRawAssignment history index stage) ↔
      ∀ z : ZFSet.{u}, z ∈ U →
        (z ∈ stage ↔
          ∃ earlierIndex : ZFSet.{u},
            earlierIndex ∈ U ∧ earlierIndex ∈ index ∧
            ∃ earlierStage : ZFSet.{u},
              earlierStage ∈ U ∧
              SatisfiesIn U
                (bareHistoryEntryAt
                  (0 : Fin 6) (4 : Fin 6) (5 : Fin 6))
                ![history, index, stage, z,
                  earlierIndex, earlierStage] ∧
              z ∈ earlierStage) := by
  simp only [bareHistoryLimitStateFormula,
    satisfiesIn_bare_all_iff, satisfiesIn_bare_biimp_iff,
    satisfiesIn_bare_boundedEx_iff, SatisfiesIn,
    bareHistoryLimitRawAssignment]
  rfl



/-- Exact raw semantics of the limit clause over a transitive set. -/
private theorem satisfiesIn_bareHistoryLimitStateFormula_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (history index stage : ZFSet.{u})
    (hhistory : history ∈ U) (hindex : index ∈ U)
    (hstage : stage ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) bareHistoryLimitStateFormula
        (bareHistoryLimitRawAssignment history index stage) ↔
      BareHistoryLimitStateIn (U : Set ZFSet.{u})
        history index stage := by
  rw [satisfiesIn_bareHistoryLimitStateFormula_components]
  constructor
  · intro h z hzU
    have hz := h z hzU
    constructor
    · intro hzStage
      rcases hz.mp hzStage with
        ⟨earlierIndex, hearlierIndexU, hearlierIndex,
          earlierStage, hearlierStageU, hearlierEntry, hzEarlier⟩
      have hs : ∀ i,
          ![history, index, stage, z,
            earlierIndex, earlierStage] i ∈ U := by
        intro i
        fin_cases i <;> assumption
      have hentry := (satisfiesIn_bareHistoryEntryAt_iff hU
        (0 : Fin 6) (4 : Fin 6) (5 : Fin 6)
        ![history, index, stage, z,
          earlierIndex, earlierStage] hs).mp hearlierEntry
      exact ⟨earlierIndex, hearlierIndexU, hearlierIndex,
        earlierStage, hearlierStageU, hentry, hzEarlier⟩

    · rintro ⟨earlierIndex, hearlierIndexU, hearlierIndex,
        earlierStage, hearlierStageU, hearlierEntry, hzEarlier⟩
      apply hz.mpr
      have hs : ∀ i,
          ![history, index, stage, z,
            earlierIndex, earlierStage] i ∈ U := by
        intro i
        fin_cases i <;> assumption
      have hentry := (satisfiesIn_bareHistoryEntryAt_iff hU
        (0 : Fin 6) (4 : Fin 6) (5 : Fin 6)
        ![history, index, stage, z,
          earlierIndex, earlierStage] hs).mpr hearlierEntry
      exact ⟨earlierIndex, hearlierIndexU, hearlierIndex,
        earlierStage, hearlierStageU, hentry, hzEarlier⟩
  · intro h z hzU
    have hz := h z hzU
    constructor
    · intro hzStage
      rcases hz.mp hzStage with
        ⟨earlierIndex, hearlierIndexU, hearlierIndex,
          earlierStage, hearlierStageU, hearlierEntry, hzEarlier⟩
      have hs : ∀ i,
          ![history, index, stage, z,
            earlierIndex, earlierStage] i ∈ U := by
        intro i
        fin_cases i <;> assumption
      have hentry := (satisfiesIn_bareHistoryEntryAt_iff hU
        (0 : Fin 6) (4 : Fin 6) (5 : Fin 6)
        ![history, index, stage, z,
          earlierIndex, earlierStage] hs).mpr hearlierEntry
      exact ⟨earlierIndex, hearlierIndexU, hearlierIndex,
        earlierStage, hearlierStageU, hentry, hzEarlier⟩
    · rintro ⟨earlierIndex, hearlierIndexU, hearlierIndex,
        earlierStage, hearlierStageU, hearlierEntry, hzEarlier⟩
      apply hz.mpr
      have hs : ∀ i,
          ![history, index, stage, z,
            earlierIndex, earlierStage] i ∈ U := by
        intro i
        fin_cases i <;> assumption
      have hentry := (satisfiesIn_bareHistoryEntryAt_iff hU
        (0 : Fin 6) (4 : Fin 6) (5 : Fin 6)
        ![history, index, stage, z,
          earlierIndex, earlierStage] hs).mp hearlierEntry
      exact ⟨earlierIndex, hearlierIndexU, hearlierIndex,
        earlierStage, hearlierStageU, hentry, hzEarlier⟩

/-! ### The isolated successor obligation -/









private theorem bareHistorySuccessorDefRename_fixedRaw (i : Fin 13) :
    bareHistorySuccessorDefRename i.succ.castSucc =
      Fin.castLE (by decide) i := by
  unfold bareHistorySuccessorDefRename
  rw [Fin.lastCases_castSucc, Fin.cases_succ]

private theorem comp_bareHistorySuccessorDefRename_raw
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage predecessorIndex predecessorStage : ZFSet.{u}) :
    (fun i => bareHistorySuccessorWitnessRawAssignment fixed
      history index stage predecessorIndex predecessorStage
      (bareHistorySuccessorDefRename i)) =
      bareGodelDefOutputRawAssignment fixed predecessorStage stage := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · change stage = stage
    rfl
  · refine Fin.cases ?_ (fun i13 => ?_) i14
    · change predecessorStage = predecessorStage
      rfl
    · rw [bareHistorySuccessorDefRename_fixedRaw]
      rw [show Fin.castLE (by decide) i13 =
          i13.castSucc.castSucc.castSucc.castSucc.castSucc by
        apply Fin.ext
        rfl]
      simp only [bareHistorySuccessorWitnessRawAssignment,
        bareHistoryStateRawAssignment,
        bareGodelDefOutputRawAssignment, snoc_castSucc,
        tupleCons_succ]

/-- Raw bounded absoluteness of the von Neumann successor predicate. -/
private theorem satisfiesIn_successorFOAt_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive) {n : Nat}
    (successor predecessor : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u})
        (Delta0Formula.successorFOAt successor predecessor) s ↔
      s successor = insert (s predecessor) (s predecessor) := by
  rw [Delta0Formula.successorFOAt,
    satisfiesIn_delta0_toFO_absolute hU _ s hs,
    Delta0Formula.satisfies_successorAt]



/-- Exact raw semantics of the successor clause over a transitive set. -/
private theorem satisfiesIn_bareHistorySuccessorStateFormula_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hhistory : history ∈ U) (hindex : index ∈ U)
    (hstage : stage ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u})
        bareHistorySuccessorStateFormula
        (bareHistoryStateRawAssignment fixed history index stage) ↔
      BareHistorySuccessorStateIn (U : Set ZFSet.{u}) fixed
        history index stage := by
  simp only [bareHistorySuccessorStateFormula,
    BareHistorySuccessorStateIn, SatisfiesIn]
  apply exists_congr
  intro predecessorIndex
  apply and_congr_right
  intro hpredecessorIndexU
  change predecessorIndex ∈ U at hpredecessorIndexU
  apply exists_congr
  intro predecessorStage
  apply and_congr_right
  intro hpredecessorStageU
  change predecessorStage ∈ U at hpredecessorStageU
  let witness := bareHistorySuccessorWitnessRawAssignment fixed
    history index stage predecessorIndex predecessorStage
  have hwitness : ∀ i, witness i ∈ U := by
    intro i
    refine Fin.lastCases ?_ (fun i16 => ?_) i
    · simpa only [witness, bareHistorySuccessorWitnessRawAssignment,
        snoc_last] using hpredecessorStageU
    · refine Fin.lastCases ?_ (fun i15 => ?_) i16
      · simpa only [witness, bareHistorySuccessorWitnessRawAssignment,
          snoc_castSucc, snoc_last] using hpredecessorIndexU
      · refine Fin.lastCases ?_ (fun i14 => ?_) i15
        · simpa only [witness, bareHistorySuccessorWitnessRawAssignment,
            bareHistoryStateRawAssignment, snoc_castSucc, snoc_last] using
            hstage
        · refine Fin.lastCases ?_ (fun i13 => ?_) i14
          · simpa only [witness,
              bareHistorySuccessorWitnessRawAssignment,
              bareHistoryStateRawAssignment, snoc_castSucc, snoc_last] using
              hindex
          · refine Fin.lastCases ?_ (fun i12 => ?_) i13
            · simpa only [witness,
                bareHistorySuccessorWitnessRawAssignment,
                bareHistoryStateRawAssignment, snoc_castSucc, snoc_last] using
                hhistory
            · simpa only [witness,
                bareHistorySuccessorWitnessRawAssignment,
                bareHistoryStateRawAssignment, snoc_castSucc] using hfixed i12
  change
    (SatisfiesIn (U : Set ZFSet.{u})
        (Delta0Formula.successorFOAt (14 : Fin 18) (16 : Fin 18))
        witness ∧
      SatisfiesIn (U : Set ZFSet.{u})
        (bareHistoryEntryAt
          (13 : Fin 18) (16 : Fin 18) (17 : Fin 18)) witness ∧
      SatisfiesIn (U : Set ZFSet.{u})
        (FOFormula.rename bareHistorySuccessorDefRename
          Godel.RudimentaryTerm.godelDefOutputFormula) witness) ↔ _
  rw [satisfiesIn_successorFOAt_iff hU _ _ witness hwitness,
    satisfiesIn_bareHistoryEntryAt_iff hU _ _ _ witness hwitness,
    satisfiesIn_rename,
    comp_bareHistorySuccessorDefRename_raw]
  rfl

/-! ### The complete raw local-state semantics -/

private theorem satisfiesIn_bare_disj_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.disj left right) s ↔
      SatisfiesIn M left s ∨ SatisfiesIn M right s := by
  classical
  simp only [FOFormula.disj, SatisfiesIn]
  tauto

/-- Raw semantics of the test that the displayed index is zero. -/
private theorem satisfiesIn_bareHistoryIndexIsZeroFormula_iff
    (U : Set ZFSet.{u}) (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) :
    SatisfiesIn U bareHistoryIndexIsZeroFormula
        (bareHistoryStateRawAssignment fixed history index stage) ↔
      index = fixed (2 : Fin 13) := by
  change (index = fixed (2 : Fin 13)) ↔ _
  rfl

/-- Raw semantics of the test that the displayed index is a von Neumann
successor.  The predecessor witness is, exactly as in restricted
satisfaction, required to belong to `U`. -/
private theorem satisfiesIn_bareHistoryIndexHasPredecessorFormula_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hhistory : history ∈ U) (hindex : index ∈ U)
    (hstage : stage ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u})
        bareHistoryIndexHasPredecessorFormula
        (bareHistoryStateRawAssignment fixed history index stage) ↔
      ∃ predecessor : ZFSet.{u}, predecessor ∈ U ∧
        index = insert predecessor predecessor := by
  simp only [bareHistoryIndexHasPredecessorFormula, SatisfiesIn]
  apply exists_congr
  intro predecessor
  apply and_congr_right
  intro hpredecessorU
  change predecessor ∈ U at hpredecessorU
  let witness := snoc
    (bareHistoryStateRawAssignment fixed history index stage) predecessor
  have hwitness : ∀ i, witness i ∈ U := by
    intro i
    refine Fin.lastCases ?_ (fun i15 => ?_) i
    · simpa only [witness, snoc_last] using hpredecessorU
    · refine Fin.lastCases ?_ (fun i14 => ?_) i15
      · simpa only [witness, bareHistoryStateRawAssignment,
          snoc_castSucc, snoc_last] using hstage
      · refine Fin.lastCases ?_ (fun i13 => ?_) i14
        · simpa only [witness, bareHistoryStateRawAssignment,
            snoc_castSucc, snoc_last] using hindex
        · refine Fin.lastCases ?_ (fun i12 => ?_) i13
          · simpa only [witness, bareHistoryStateRawAssignment,
              snoc_castSucc, snoc_last] using hhistory
          · simpa only [witness, bareHistoryStateRawAssignment,
              snoc_castSucc] using hfixed i12
  change
    SatisfiesIn (U : Set ZFSet.{u})
        (Delta0Formula.successorFOAt (14 : Fin 17) (16 : Fin 17))
        witness ↔ _
  rw [satisfiesIn_successorFOAt_iff hU _ _ witness hwitness]
  rfl

private theorem comp_bareHistoryStateRename_raw
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) :
    (fun i => bareHistoryStateRawAssignment fixed history index stage
      (bareHistoryStateRename i)) =
      bareHistoryLimitRawAssignment history index stage := by
  funext i
  fin_cases i <;> rfl





/-- The isolated evaluator-correctness obligation is exactly what turns the
internal successor clause into its usual ambient mathematical reading. -/
private theorem bareHistorySuccessorStateIn_iff_ambient
    {U : ZFSet.{u}} (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) (hstage : stage ∈ U)
    (hcorrect : BareGodelDefOutputCorrectIn U fixed) :
    BareHistorySuccessorStateIn (U : Set ZFSet.{u}) fixed
        history index stage ↔
      BareHistorySuccessorStateAmbientIn (U : Set ZFSet.{u})
        history index stage := by
  simp only [BareHistorySuccessorStateIn,
    BareHistorySuccessorStateAmbientIn]
  apply exists_congr
  intro predecessorIndex
  apply and_congr_right
  intro _hpredecessorIndexU
  apply exists_congr
  intro predecessorStage
  apply and_congr_right
  intro hpredecessorStageU
  change predecessorStage ∈ U at hpredecessorStageU
  rw [hcorrect predecessorStage stage hpredecessorStageU hstage]



/-- Under the explicit evaluator-correctness hypothesis, the internally
relativized local state is the standard ambient recursion state. -/
private theorem bareHistoryLocalStateIn_iff_ambient
    {U : ZFSet.{u}} (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) (hstage : stage ∈ U)
    (hcorrect : BareGodelDefOutputCorrectIn U fixed) :
    BareHistoryLocalStateIn (U : Set ZFSet.{u}) fixed
        history index stage ↔
      BareHistoryLocalStateAmbientIn (U : Set ZFSet.{u}) fixed
        history index stage := by
  simp only [BareHistoryLocalStateIn, BareHistoryLocalStateAmbientIn]
  rw [bareHistorySuccessorStateIn_iff_ambient fixed history index stage
    hstage hcorrect]

/-- Exact restricted semantics of the complete local recursion formula. -/
private theorem satisfiesIn_bareHistoryLocalStateFormula_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hhistory : history ∈ U) (hindex : index ∈ U)
    (hstage : stage ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) bareHistoryLocalStateFormula
        (bareHistoryStateRawAssignment fixed history index stage) ↔
      BareHistoryLocalStateIn (U : Set ZFSet.{u}) fixed
        history index stage := by
  rw [bareHistoryLocalStateFormula, satisfiesIn_bare_disj_iff,
    satisfiesIn_bareHistoryBaseStateFormula_iff,
    satisfiesIn_bare_disj_iff,
    satisfiesIn_bareHistorySuccessorStateFormula_iff hU fixed
      history index stage hfixed hhistory hindex hstage]
  change
    ((index = fixed (2 : Fin 13) ∧ stage = fixed (2 : Fin 13)) ∨
      BareHistorySuccessorStateIn (U : Set ZFSet.{u}) fixed
          history index stage ∨
      ((¬ SatisfiesIn (U : Set ZFSet.{u})
            bareHistoryIndexIsZeroFormula
            (bareHistoryStateRawAssignment fixed history index stage) ∧
          ¬ SatisfiesIn (U : Set ZFSet.{u})
            bareHistoryIndexHasPredecessorFormula
            (bareHistoryStateRawAssignment fixed history index stage)) ∧
        SatisfiesIn (U : Set ZFSet.{u})
          (FOFormula.rename bareHistoryStateRename
            bareHistoryLimitStateFormula)
          (bareHistoryStateRawAssignment fixed history index stage))) ↔ _
  rw [satisfiesIn_bareHistoryIndexIsZeroFormula_iff,
    satisfiesIn_bareHistoryIndexHasPredecessorFormula_iff hU fixed
      history index stage hfixed hhistory hindex hstage,
    satisfiesIn_rename, comp_bareHistoryStateRename_raw,
    satisfiesIn_bareHistoryLimitStateFormula_iff hU
      history index stage hhistory hindex hstage]
  rfl



/-! ### Raw valid histories -/

private theorem satisfiesIn_bare_imp_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.imp left right) s ↔
      (SatisfiesIn M left s → SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.imp, satisfiesIn_bare_disj_iff, SatisfiesIn]
  tauto

private theorem snoc_mem_of_all_mem
    {U : ZFSet.{u}} {n : Nat} (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ U) (x : ZFSet.{u}) (hx : x ∈ U) :
    ∀ i, snoc s x i ∈ U := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [snoc_last] using hx
  · simpa only [snoc_castSucc] using hs j







private theorem bareValidStageHistoryRawAssignment_mem
    {U : ZFSet.{u}} (fixed : Tuple ZFSet.{u} 13)
    (history bound : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hhistory : history ∈ U) (hbound : bound ∈ U) :
    ∀ i, bareValidStageHistoryRawAssignment fixed history bound i ∈ U := by
  exact snoc_mem_of_all_mem _
    (snoc_mem_of_all_mem fixed hfixed history hhistory) bound hbound

private theorem bareValidStageHistoryIndexRawAssignment_mem
    {U : ZFSet.{u}} (fixed : Tuple ZFSet.{u} 13)
    (history bound index : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hhistory : history ∈ U) (hbound : bound ∈ U)
    (hindex : index ∈ U) :
    ∀ i,
      bareValidStageHistoryIndexRawAssignment fixed history bound index i ∈ U := by
  exact snoc_mem_of_all_mem _
    (bareValidStageHistoryRawAssignment_mem fixed history bound
      hfixed hhistory hbound) index hindex

private theorem bareValidStageHistoryStageRawAssignment_mem
    {U : ZFSet.{u}} (fixed : Tuple ZFSet.{u} 13)
    (history bound index stage : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hhistory : history ∈ U) (hbound : bound ∈ U)
    (hindex : index ∈ U) (hstage : stage ∈ U) :
    ∀ i,
      bareValidStageHistoryStageRawAssignment fixed history bound index stage i ∈ U := by
  exact snoc_mem_of_all_mem _
    (bareValidStageHistoryIndexRawAssignment_mem fixed history bound index
      hfixed hhistory hbound hindex) stage hstage

/-- Direct syntactic expansion of the body at one selected index. -/
private theorem satisfiesIn_bareValidStageHistoryIndexBody_components
    (U : Set ZFSet.{u}) (fixed : Tuple ZFSet.{u} 13)
    (history bound index : ZFSet.{u}) :
    SatisfiesIn U bareValidStageHistoryIndexBody
        (bareValidStageHistoryIndexRawAssignment fixed history bound index) ↔
      ∃ stage : ZFSet.{u}, stage ∈ U ∧
        SatisfiesIn U
          (bareHistoryEntryAt
            (13 : Fin 17) (15 : Fin 17) (16 : Fin 17))
          (bareValidStageHistoryStageRawAssignment fixed history bound
            index stage) ∧
        ((∀ otherStage : ZFSet.{u}, otherStage ∈ U →
            SatisfiesIn U
              (bareHistoryEntryAt
                (13 : Fin 18) (15 : Fin 18) (17 : Fin 18))
              (snoc (bareValidStageHistoryStageRawAssignment fixed history
                bound index stage) otherStage) →
            otherStage = stage) ∧
          SatisfiesIn U
            (FOFormula.rename bareValidHistoryLocalRename
              bareHistoryLocalStateFormula)
            (bareValidStageHistoryStageRawAssignment fixed history bound
              index stage)) := by
  simp only [bareValidStageHistoryIndexBody, SatisfiesIn,
    satisfiesIn_bare_all_iff, satisfiesIn_bare_imp_iff,
    bareValidStageHistoryIndexRawAssignment,
    bareValidStageHistoryStageRawAssignment]
  rfl

private theorem comp_bareValidHistoryLocalRename_raw
    (fixed : Tuple ZFSet.{u} 13)
    (history bound index stage : ZFSet.{u}) :
    (fun i =>
      bareValidStageHistoryStageRawAssignment fixed history bound index stage
        (bareValidHistoryLocalRename i)) =
      bareHistoryStateRawAssignment fixed history index stage := by
  funext i
  refine Fin.lastCases ?_ (fun i15 => ?_) i
  · change stage = stage
    rfl
  · refine Fin.lastCases ?_ (fun i14 => ?_) i15
    · change index = index
      rfl
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · change history = history
        rfl
      · rw [bareValidHistoryLocalRename_fixed]
        rw [show Fin.castLE (by decide) i13 =
            i13.castSucc.castSucc.castSucc.castSucc by
          apply Fin.ext
          rfl]
        simp only [bareValidStageHistoryStageRawAssignment,
          bareValidStageHistoryIndexRawAssignment,
          bareValidStageHistoryRawAssignment,
          bareHistoryStateRawAssignment, snoc_castSucc]



/-- Exact raw semantics of the validity body at one selected index. -/
private theorem satisfiesIn_bareValidStageHistoryIndexBody_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (history bound index : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hhistory : history ∈ U) (hbound : bound ∈ U)
    (hindex : index ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) bareValidStageHistoryIndexBody
        (bareValidStageHistoryIndexRawAssignment fixed history bound index) ↔
      BareValidStageHistoryIndexIn (U : Set ZFSet.{u}) fixed
        history index := by
  rw [satisfiesIn_bareValidStageHistoryIndexBody_components]
  constructor
  · rintro ⟨stage, hstageU, hentry, hunique, hlocal⟩
    change stage ∈ U at hstageU
    have hstageAssignment :=
      bareValidStageHistoryStageRawAssignment_mem fixed history bound
        index stage hfixed hhistory hbound hindex hstageU
    have hentry' := (satisfiesIn_bareHistoryEntryAt_iff hU
      (13 : Fin 17) (15 : Fin 17) (16 : Fin 17)
      (bareValidStageHistoryStageRawAssignment fixed history bound
        index stage) hstageAssignment).mp hentry
    have hlocal' :
        SatisfiesIn (U : Set ZFSet.{u}) bareHistoryLocalStateFormula
          (bareHistoryStateRawAssignment fixed history index stage) := by
      rw [satisfiesIn_rename,
        comp_bareValidHistoryLocalRename_raw] at hlocal
      exact hlocal
    refine ⟨stage, ?_, hentry', ?_, ?_⟩
    · exact hstageU
    · intro otherStage hotherStageU hotherEntry
      change otherStage ∈ U at hotherStageU
      apply hunique otherStage
      · exact hotherStageU
      have hotherAssignment := snoc_mem_of_all_mem _ hstageAssignment
        otherStage hotherStageU
      exact (satisfiesIn_bareHistoryEntryAt_iff hU
        (13 : Fin 18) (15 : Fin 18) (17 : Fin 18)
        (snoc (bareValidStageHistoryStageRawAssignment fixed history bound
          index stage) otherStage) hotherAssignment).mpr hotherEntry
    · exact (satisfiesIn_bareHistoryLocalStateFormula_iff hU fixed
        history index stage hfixed hhistory hindex hstageU).mp hlocal'
  · rintro ⟨stage, hstageU, hentry, hunique, hlocal⟩
    change stage ∈ U at hstageU
    have hstageAssignment :=
      bareValidStageHistoryStageRawAssignment_mem fixed history bound
        index stage hfixed hhistory hbound hindex hstageU
    refine ⟨stage, ?_, ?_, ?_, ?_⟩
    · exact hstageU
    · exact (satisfiesIn_bareHistoryEntryAt_iff hU
        (13 : Fin 17) (15 : Fin 17) (16 : Fin 17)
        (bareValidStageHistoryStageRawAssignment fixed history bound
          index stage) hstageAssignment).mpr hentry
    · intro otherStage hotherStageU hotherEntry
      change otherStage ∈ U at hotherStageU
      have hotherAssignment := snoc_mem_of_all_mem _ hstageAssignment
        otherStage hotherStageU
      have hotherEntry' := (satisfiesIn_bareHistoryEntryAt_iff hU
        (13 : Fin 18) (15 : Fin 18) (17 : Fin 18)
        (snoc (bareValidStageHistoryStageRawAssignment fixed history bound
          index stage) otherStage) hotherAssignment).mp hotherEntry
      apply hunique otherStage
      · exact hotherStageU
      · exact hotherEntry'
    · rw [satisfiesIn_rename,
        comp_bareValidHistoryLocalRename_raw]
      exact (satisfiesIn_bareHistoryLocalStateFormula_iff hU fixed
        history index stage hfixed hhistory hindex hstageU).mpr hlocal

/-- Direct expansion of the outer bounded-totality formula.  The outer
universal quantifier ranges over `U`; the displayed disjunction is the
von Neumann condition `index <= bound`. -/
private theorem satisfiesIn_bareValidStageHistoryFormula_components
    (U : Set ZFSet.{u}) (fixed : Tuple ZFSet.{u} 13)
    (history bound : ZFSet.{u}) :
    SatisfiesIn U bareValidStageHistoryFormula
        (bareValidStageHistoryRawAssignment fixed history bound) ↔
      ∀ index : ZFSet.{u}, index ∈ U →
        (index ∈ bound ∨ index = bound) →
          SatisfiesIn U bareValidStageHistoryIndexBody
            (bareValidStageHistoryIndexRawAssignment fixed history bound
              index) := by
  simp only [bareValidStageHistoryFormula, satisfiesIn_bare_all_iff,
    satisfiesIn_bare_imp_iff, satisfiesIn_bare_disj_iff, SatisfiesIn,
    bareValidStageHistoryIndexRawAssignment]
  rfl



/-- Exact raw semantics of a valid bare history over a transitive set. -/
private theorem satisfiesIn_bareValidStageHistoryFormula_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (history bound : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hhistory : history ∈ U) (hbound : bound ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) bareValidStageHistoryFormula
        (bareValidStageHistoryRawAssignment fixed history bound) ↔
      BareValidStageHistoryIn (U : Set ZFSet.{u}) fixed
        history bound := by
  rw [satisfiesIn_bareValidStageHistoryFormula_components]
  constructor
  · intro h index hindexU hindexBound
    change index ∈ U at hindexU
    exact (satisfiesIn_bareValidStageHistoryIndexBody_iff hU fixed
      history bound index hfixed hhistory hbound hindexU).mp
        (h index hindexU hindexBound)
  · intro h index hindexU hindexBound
    change index ∈ U at hindexU
    exact (satisfiesIn_bareValidStageHistoryIndexBody_iff hU fixed
      history bound index hfixed hhistory hbound hindexU).mpr
        (h index hindexU hindexBound)

/-! ### Raw history-independent stage output -/





private theorem bareStageAtRawAssignment_mem
    {U : ZFSet.{u}} (fixed : Tuple ZFSet.{u} 13)
    (index stage : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hindex : index ∈ U) (hstage : stage ∈ U) :
    ∀ i, bareStageAtRawAssignment fixed index stage i ∈ U := by
  exact snoc_mem_of_all_mem _
    (snoc_mem_of_all_mem fixed hfixed index hindex) stage hstage

private theorem comp_bareStageAtValidHistoryRename_raw
    (fixed : Tuple ZFSet.{u} 13)
    (index stage history : ZFSet.{u}) :
    (fun i => bareStageAtHistoryRawAssignment fixed index stage history
      (bareStageAtValidHistoryRename i)) =
      bareValidStageHistoryRawAssignment fixed history index := by
  funext i
  fin_cases i <;> rfl

/-- Direct expansion of the history-independent stage-output formula. -/
private theorem satisfiesIn_bareStageAtFormula_components
    (U : Set ZFSet.{u}) (fixed : Tuple ZFSet.{u} 13)
    (index stage : ZFSet.{u}) :
    SatisfiesIn U bareStageAtFormula
        (bareStageAtRawAssignment fixed index stage) ↔
      ∃ history : ZFSet.{u}, history ∈ U ∧
        SatisfiesIn U
          (FOFormula.rename bareStageAtValidHistoryRename
            bareValidStageHistoryFormula)
          (bareStageAtHistoryRawAssignment fixed index stage history) ∧
        SatisfiesIn U
          (bareHistoryEntryAt
            (15 : Fin 16) (13 : Fin 16) (14 : Fin 16))
          (bareStageAtHistoryRawAssignment fixed index stage history) := by
  simp only [bareStageAtFormula, SatisfiesIn,
    bareStageAtHistoryRawAssignment]



/-- Exact raw semantics of the history-independent stage-output formula over
a transitive set.  This theorem identifies the syntax only with the
internally relativized recursion; it does not assume successor absoluteness. -/
private theorem satisfiesIn_bareStageAtFormula_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (index stage : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hindex : index ∈ U) (hstage : stage ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) bareStageAtFormula
        (bareStageAtRawAssignment fixed index stage) ↔
      BareStageAtIn (U : Set ZFSet.{u}) fixed index stage := by
  rw [satisfiesIn_bareStageAtFormula_components]
  constructor
  · rintro ⟨history, hhistoryU, hvalid, hentry⟩
    change history ∈ U at hhistoryU
    have hbaseAssignment := bareStageAtRawAssignment_mem fixed index stage
      hfixed hindex hstage
    have hhistoryAssignment := snoc_mem_of_all_mem _ hbaseAssignment
      history hhistoryU
    have hvalid' :
        SatisfiesIn (U : Set ZFSet.{u}) bareValidStageHistoryFormula
          (bareValidStageHistoryRawAssignment fixed history index) := by
      rw [satisfiesIn_rename,
        comp_bareStageAtValidHistoryRename_raw] at hvalid
      exact hvalid
    have hentry' := (satisfiesIn_bareHistoryEntryAt_iff hU
      (15 : Fin 16) (13 : Fin 16) (14 : Fin 16)
      (bareStageAtHistoryRawAssignment fixed index stage history)
      hhistoryAssignment).mp hentry
    refine ⟨history, hhistoryU, ?_, hentry'⟩
    exact (satisfiesIn_bareValidStageHistoryFormula_iff hU fixed
      history index hfixed hhistoryU hindex).mp hvalid'
  · rintro ⟨history, hhistoryU, hvalid, hentry⟩
    change history ∈ U at hhistoryU
    have hbaseAssignment := bareStageAtRawAssignment_mem fixed index stage
      hfixed hindex hstage
    have hhistoryAssignment := snoc_mem_of_all_mem _ hbaseAssignment
      history hhistoryU
    refine ⟨history, ?_, ?_, ?_⟩
    · exact hhistoryU
    · rw [satisfiesIn_rename,
        comp_bareStageAtValidHistoryRename_raw]
      exact (satisfiesIn_bareValidStageHistoryFormula_iff hU fixed
        history index hfixed hhistoryU hindex).mpr hvalid
    · exact (satisfiesIn_bareHistoryEntryAt_iff hU
        (15 : Fin 16) (13 : Fin 16) (14 : Fin 16)
        (bareStageAtHistoryRawAssignment fixed index stage history)
        hhistoryAssignment).mpr hentry

/-! ### Soundness of internal ordinal outputs -/





/-- Restrict an internally valid history from a canonical ordinal bound to
any smaller canonical ordinal bound. -/
private theorem BareValidStageHistoryIn.restrictOrdinal
    {U : Set ZFSet.{u}} {fixed : Tuple ZFSet.{u} 13}
    {history : ZFSet.{u}} {alpha beta : Ordinal.{u}}
    (hvalid : BareValidStageHistoryIn U fixed history beta.toZFSet)
    (halpha : alpha ≤ beta) :
    BareValidStageHistoryIn U fixed history alpha.toZFSet := by
  intro index hindexU hindex
  apply hvalid index hindexU
  rcases hindex with hindex | rfl
  · left
    exact Ordinal.toZFSet_monotone halpha hindex
  · rcases halpha.eq_or_lt with rfl | halpha
    · exact Or.inr rfl
    · exact Or.inl (Ordinal.toZFSet_mem_toZFSet_iff.mpr halpha)

/-- Reusing the same internal history and one of its entries gives a stage
witness at every earlier canonical index. -/
private theorem bareStageAtIn_of_validHistory
    {U : Set ZFSet.{u}} {fixed : Tuple ZFSet.{u} 13}
    {history index stage : ZFSet.{u}} {alpha beta : Ordinal.{u}}
    (hhistory : history ∈ U)
    (hindex : index = alpha.toZFSet) (halpha : alpha ≤ beta)
    (hvalid : BareValidStageHistoryIn U fixed history beta.toZFSet)
    (hentry : BareHistoryEntryIn history index stage) :
    BareStageAtIn U fixed index stage := by
  subst index
  exact ⟨history, hhistory, hvalid.restrictOrdinal halpha, hentry⟩

/-- At its bound, internal validity transfers the local recursion rule to any
displayed entry at that bound. -/
private theorem BareValidStageHistoryIn.localState_of_entry
    {U : Set ZFSet.{u}} {fixed : Tuple ZFSet.{u} 13}
    {history bound stage : ZFSet.{u}}
    (hvalid : BareValidStageHistoryIn U fixed history bound)
    (hboundU : bound ∈ U) (hstageU : stage ∈ U)
    (hentry : BareHistoryEntryIn history bound stage) :
    BareHistoryLocalStateIn U fixed history bound stage := by
  rcases hvalid bound hboundU (Or.inr rfl) with
    ⟨chosenStage, _hchosenStageU, _hchosenEntry, hunique, hlocal⟩
  have hstage := hunique stage hstageU hentry
  simpa only [hstage] using hlocal

private theorem empty_ne_insert_self_raw (predecessor : ZFSet.{u}) :
    ¬ (∅ : ZFSet.{u}) = insert predecessor predecessor := by
  intro h
  have hmem : predecessor ∈ (∅ : ZFSet.{u}) := by
    rw [h]
    exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  exact ZFSet.notMem_empty predecessor hmem

/-- A canonical successor ordinal code has exactly its canonical predecessor,
even when the proposed predecessor is an arbitrary raw `ZFSet`. -/
private theorem ordinalToZFSet_successor_predecessor_iff
    (alpha : Ordinal.{u}) (predecessor : ZFSet.{u}) :
    (Order.succ alpha).toZFSet = insert predecessor predecessor ↔
      predecessor = alpha.toZFSet := by
  constructor
  · intro h
    apply insert_self_injective
    rw [← h, Order.succ_eq_add_one]
    exact Ordinal.toZFSet_add_one alpha
  · rintro rfl
    rw [Order.succ_eq_add_one]
    exact Ordinal.toZFSet_add_one alpha

/-- A nonzero limit ordinal code is not the von Neumann successor of any raw
set. -/
private theorem ordinalToZFSet_limit_no_predecessor
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit) :
    ¬ ∃ predecessor : ZFSet.{u},
      limit.toZFSet = insert predecessor predecessor := by
  rintro ⟨predecessor, hsuccessor⟩
  have hpredecessorMem : predecessor ∈ limit.toZFSet := by
    rw [hsuccessor]
    exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  rcases Ordinal.mem_toZFSet_iff.mp hpredecessorMem with
    ⟨beta, _hbeta, hbetaCode⟩
  subst predecessor
  have hcodes : limit.toZFSet = (Order.succ beta).toZFSet := by
    calc
      limit.toZFSet = insert beta.toZFSet beta.toZFSet := hsuccessor
      _ = (Order.succ beta).toZFSet :=
        (ordinalToZFSet_successor_predecessor_iff beta beta.toZFSet).mpr rfl |>.symm
  have hlimit : limit = Order.succ beta :=
    Ordinal.toZFSet_injective hcodes
  exact hl.succ_ne beta hlimit.symm

/-- Soundness of an internally computed ordinal stage in any transitive
carrier.  The hypotheses say exactly that the zero parameter is the actual
empty set and that the internal successor evaluator is correct.  No history
existence, reflection, or elementarity assumption is used. -/
private theorem bareStageAtIn_ordinal_sound_of_transitive
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : BareGodelDefOutputCorrectIn U fixed)
    (ordinal : Ordinal.{u}) :
    ∀ {stage : ZFSet.{u}},
      ordinal.toZFSet ∈ U → stage ∈ U →
      BareStageAtIn (U : Set ZFSet.{u}) fixed ordinal.toZFSet stage →
        stage = LStageZF ordinal := by
  induction ordinal using Ordinal.limitRecOn with
  | zero =>
      intro stage hindexU hstageU hstageAt
      rcases hstageAt with ⟨history, hhistoryU, hvalid, hentry⟩
      have hlocal := hvalid.localState_of_entry hindexU hstageU hentry
      have hlocalAmbient :=
        (bareHistoryLocalStateIn_iff_ambient fixed history
          (0 : Ordinal.{u}).toZFSet stage hstageU hcorrect).mp hlocal
      rcases hlocalAmbient with hbase | hsuccessor | hlimit
      · calc
          stage = fixed (2 : Fin 13) := hbase.2
          _ = (∅ : ZFSet.{u}) := hempty
          _ = LStageZF (0 : Ordinal.{u}) := LStageZF_zero.symm
      · rcases hsuccessor with
          ⟨predecessorIndex, _hpredecessorIndexU,
            _predecessorStage, _hpredecessorStageU,
            hpredecessor, _hentry, _hstage⟩
        have himpossible :
            (∅ : ZFSet.{u}) =
              insert predecessorIndex predecessorIndex := by
          simpa only [Ordinal.toZFSet_zero] using hpredecessor
        exact (empty_ne_insert_self_raw predecessorIndex himpossible).elim
      · have hzero :
            (0 : Ordinal.{u}).toZFSet = fixed (2 : Fin 13) := by
          rw [Ordinal.toZFSet_zero, hempty]
        exact (hlimit.1.1 hzero).elim
  | add_one alpha ih =>
      rw [← Order.succ_eq_add_one]
      intro stage hindexU hstageU hstageAt
      rcases hstageAt with ⟨history, hhistoryU, hvalid, hentry⟩
      have hlocal := hvalid.localState_of_entry hindexU hstageU hentry
      have hlocalAmbient :=
        (bareHistoryLocalStateIn_iff_ambient fixed history
          (Order.succ alpha).toZFSet stage hstageU hcorrect).mp hlocal
      rcases hlocalAmbient with hbase | hsuccessor | hlimit
      · have hcodes :
            (Order.succ alpha).toZFSet =
              (0 : Ordinal.{u}).toZFSet := by
          calc
            (Order.succ alpha).toZFSet = fixed (2 : Fin 13) := hbase.1
            _ = (∅ : ZFSet.{u}) := hempty
            _ = (0 : Ordinal.{u}).toZFSet := Ordinal.toZFSet_zero.symm
        have hordinal : Order.succ alpha = 0 :=
          Ordinal.toZFSet_injective hcodes
        exact (Order.succ_ne_bot alpha hordinal).elim
      · rcases hsuccessor with
          ⟨predecessorIndex, hpredecessorIndexU,
            predecessorStage, hpredecessorStageU,
            hpredecessor, hpredecessorEntry, hstage⟩
        change predecessorIndex ∈ U at hpredecessorIndexU
        change predecessorStage ∈ U at hpredecessorStageU
        have hpredecessorIndex :
            predecessorIndex = alpha.toZFSet :=
          (ordinalToZFSet_successor_predecessor_iff
            alpha predecessorIndex).mp hpredecessor
        subst predecessorIndex
        have hpredecessorAt :
            BareStageAtIn (U : Set ZFSet.{u}) fixed
              alpha.toZFSet predecessorStage :=
          bareStageAtIn_of_validHistory hhistoryU rfl
            (Order.le_succ alpha) hvalid hpredecessorEntry
        have hpredecessorStage :=
          ih hpredecessorIndexU hpredecessorStageU hpredecessorAt
        calc
          stage = Godel.godelDef predecessorStage := hstage
          _ = Godel.godelDef (LStageZF alpha) := by rw [hpredecessorStage]
          _ = Constructible.DefZF (LStageZF alpha) :=
            (Godel.DefZF_eq_godelDef
              (LStageZF_isTransitive alpha)).symm
          _ = LStageZF (Order.succ alpha) := (LStageZF_succ alpha).symm
      · have hpredecessorMem :
            alpha.toZFSet ∈ (Order.succ alpha).toZFSet :=
          Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ alpha)
        have hpredecessorU : alpha.toZFSet ∈ U :=
          hU.mem_trans hpredecessorMem hindexU
        have hpredecessor :
            (Order.succ alpha).toZFSet =
              insert alpha.toZFSet alpha.toZFSet :=
          (ordinalToZFSet_successor_predecessor_iff
            alpha alpha.toZFSet).mpr rfl
        exact (hlimit.1.2
          ⟨alpha.toZFSet, hpredecessorU, hpredecessor⟩).elim
  | limit limit hl ih =>
      intro stage hindexU hstageU hstageAt
      rcases hstageAt with ⟨history, hhistoryU, hvalid, hentry⟩
      have hlocal := hvalid.localState_of_entry hindexU hstageU hentry
      have hlocalAmbient :=
        (bareHistoryLocalStateIn_iff_ambient fixed history
          limit.toZFSet stage hstageU hcorrect).mp hlocal
      rcases hlocalAmbient with hbase | hsuccessor | hlimit
      · have hcodes : limit.toZFSet = (0 : Ordinal.{u}).toZFSet := by
          calc
            limit.toZFSet = fixed (2 : Fin 13) := hbase.1
            _ = (∅ : ZFSet.{u}) := hempty
            _ = (0 : Ordinal.{u}).toZFSet := Ordinal.toZFSet_zero.symm
        have hordinal : limit = 0 := Ordinal.toZFSet_injective hcodes
        exact (hl.ne_bot hordinal).elim
      · rcases hsuccessor with
          ⟨predecessorIndex, _hpredecessorIndexU,
            _predecessorStage, _hpredecessorStageU,
            hpredecessor, _hentry, _hstage⟩
        exact (ordinalToZFSet_limit_no_predecessor hl
          ⟨predecessorIndex, hpredecessor⟩).elim
      · apply ZFSet.ext
        intro z
        constructor
        · intro hz
          have hzU : z ∈ U := hU.mem_trans hz hstageU
          rcases (hlimit.2 z hzU).mp hz with
            ⟨earlierIndex, hearlierIndexU, hearlierIndex,
              earlierStage, hearlierStageU, hearlierEntry, hzEarlier⟩
          change earlierIndex ∈ U at hearlierIndexU
          change earlierStage ∈ U at hearlierStageU
          rcases Ordinal.mem_toZFSet_iff.mp hearlierIndex with
            ⟨earlierOrdinal, hearlierOrdinal, hcode⟩
          have hearlierIndexEq :
              earlierIndex = earlierOrdinal.toZFSet := hcode.symm
          subst earlierIndex
          have hearlierAt :
              BareStageAtIn (U : Set ZFSet.{u}) fixed
                earlierOrdinal.toZFSet earlierStage :=
            bareStageAtIn_of_validHistory hhistoryU rfl
              hearlierOrdinal.le hvalid hearlierEntry
          have hearlierStage := ih earlierOrdinal hearlierOrdinal
            hearlierIndexU hearlierStageU hearlierAt
          apply (mem_LStageZF_limit_iff hl).mpr
          refine ⟨earlierOrdinal, hearlierOrdinal, ?_⟩
          simpa only [hearlierStage] using hzEarlier
        · intro hz
          rcases (mem_LStageZF_limit_iff hl).mp hz with
            ⟨earlierOrdinal, hearlierOrdinal, hzEarlier⟩
          have hearlierIndex :
              earlierOrdinal.toZFSet ∈ limit.toZFSet :=
            Ordinal.toZFSet_mem_toZFSet_iff.mpr hearlierOrdinal
          have hearlierIndexU : earlierOrdinal.toZFSet ∈ U :=
            hU.mem_trans hearlierIndex hindexU
          rcases hvalid earlierOrdinal.toZFSet hearlierIndexU
              (Or.inl hearlierIndex) with
            ⟨earlierStage, hearlierStageU, hearlierEntry,
              _hunique, _hlocal⟩
          change earlierStage ∈ U at hearlierStageU
          have hearlierAt :
              BareStageAtIn (U : Set ZFSet.{u}) fixed
                earlierOrdinal.toZFSet earlierStage :=
            bareStageAtIn_of_validHistory hhistoryU rfl
              hearlierOrdinal.le hvalid hearlierEntry
          have hearlierStageEq := ih earlierOrdinal hearlierOrdinal
            hearlierIndexU hearlierStageU hearlierAt
          have hzEarlierStage : z ∈ earlierStage := by
            simpa only [hearlierStageEq] using hzEarlier
          have hzU : z ∈ U :=
            hU.mem_trans hzEarlierStage hearlierStageU
          apply (hlimit.2 z hzU).mpr
          exact ⟨earlierOrdinal.toZFSet, hearlierIndexU, hearlierIndex,
            earlierStage, hearlierStageU, hearlierEntry, hzEarlierStage⟩



end

end Constructible.Model

end
end GCHSource_Work_CUGCH_BareStageHistory

/- Source module: Solutions.Work_CUGCH_BareStageHistoryBounds -/
section GCHSource_Work_CUGCH_BareStageHistoryBounds
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Local bounds for bounded constructible-stage histories

This file records the elementary closure facts needed before constructing a
stage-only ("bare") history inside a prescribed limit level.  The hypotheses
and conclusions are deliberately local: membership in the proper class `L`
is not used as a substitute for membership in `LStageZF theta`.

The results below do not yet internalize the Replacement family occurring at
a limit step.  In particular, they do not claim that `stageHistoryData alpha`
belongs to every later limit level.
-/

section

universe u v

namespace Constructible

section ZFC

open Set

/-! ## Explicit finite successor bounds -/













/-! ## Local closure under the rudimentary basis -/























/-- The earlier constructible level itself belongs to a later limit level. -/
private theorem LStageZF_mem_LStageZF_of_lt_isSuccLimit
    {alpha theta : Ordinal.{u}} (_htheta : Order.IsSuccLimit theta)
    (halpha : alpha < theta) :
    LStageZF alpha ∈ LStageZF theta :=
  LStageZF_mem_of_lt halpha

/-! ## Local bounds for finite sequence and program codes -/













namespace Godel.RudimentaryTerm













/-! ## Local bounds for successful stack executions -/









end Godel.RudimentaryTerm

namespace Model

/-- Above `omega`, every fixed evaluator parameter really is an element of
the prescribed limit stage. -/
private theorem stageHistoryFixedParameters_mem_LStageZF_of_omega_lt
    {theta : Ordinal.{u}} (homega : Ordinal.omega0 < theta) :
    ∀ i : Fin 13,
      (stageHistoryFixedParameters.{u} i).1 ∈ LStageZF theta := by
  intro i
  rw [← canonicalStageParameters_eq_fixed]
  fin_cases i <;>
    simp only [canonicalStageParameters] <;>
    apply ordinal_toZFSet_mem_LStageZF_of_lt <;>
    first
    | exact homega
    | exact (Ordinal.natCast_lt_omega0 _).trans homega









end Model

end ZFC

end Constructible

end
end GCHSource_Work_CUGCH_BareStageHistoryBounds

/- Source module: Solutions.Work_CUGCH_CanonicalBareHistory -/
section GCHSource_Work_CUGCH_CanonicalBareHistory
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The canonical relation-free constructible-stage history

This file fixes the actual set which later local-absoluteness arguments must
put inside a prescribed constructible level.  For an ordinal `alpha`,
`canonicalBareHistory alpha` is exactly

`{ <beta, L_beta> | beta <= alpha }`.

The definition uses ambient ZF Replacement only to obtain a genuine `ZFSet`.
No constructibility bound is claimed here.  In particular, membership in the
proper class `L` would not by itself imply the local bound required by
Condensation; that bound is a separate theorem.
-/

section

universe u

namespace Constructible.Model

noncomputable section











/-- The through-`bound` history is the below-`bound` graph with precisely the
top pair adjoined. -/
private theorem canonicalBareHistory_eq_insert_top (bound : Ordinal.{u}) :
    canonicalBareHistory bound =
      insert (canonicalBareHistoryPair bound)
        (canonicalBareHistoryBelow bound) := by
  apply ZFSet.ext
  intro entry
  rw [mem_canonicalBareHistory_iff, ZFSet.mem_insert_iff,
    mem_canonicalBareHistoryBelow_iff]
  constructor
  · rintro ⟨ordinal, hordinal, hentry⟩
    rcases hordinal.eq_or_lt with rfl | hordinal
    · exact Or.inl hentry.symm
    · exact Or.inr ⟨ordinal, hordinal, hentry⟩
  · rintro (hentry | ⟨ordinal, hordinal, hentry⟩)
    · exact ⟨bound, le_refl bound, hentry.symm⟩
    · exact ⟨ordinal, hordinal.le, hentry⟩

/-- Passing to a successor only adjoins its new top pair. -/
private theorem canonicalBareHistory_succ (ordinal : Ordinal.{u}) :
    canonicalBareHistory (Order.succ ordinal) =
      insert (canonicalBareHistoryPair (Order.succ ordinal))
        (canonicalBareHistory ordinal) := by
  rw [canonicalBareHistory_eq_insert_top]
  rfl

/-- Exact coordinate form of lookup in the canonical history. -/
private theorem pair_mem_canonicalBareHistory_iff
    {bound : Ordinal.{u}} {index stage : ZFSet.{u}} :
    ZFSet.pair index stage ∈ canonicalBareHistory bound ↔
      ∃ ordinal ≤ bound,
        index = ordinal.toZFSet ∧ stage = LStageZF ordinal := by
  rw [mem_canonicalBareHistory_iff]
  constructor
  · rintro ⟨ordinal, hordinal, hpairs⟩
    have hcoordinates := ZFSet.pair_inj.mp hpairs
    exact ⟨ordinal, hordinal, hcoordinates.1.symm,
      hcoordinates.2.symm⟩
  · rintro ⟨ordinal, hordinal, rfl, rfl⟩
    exact ⟨ordinal, hordinal, rfl⟩

/-- At a fixed index the canonical history has a unique stage coordinate. -/
private theorem canonicalBareHistory_functional
    {bound : Ordinal.{u}} {index stage otherStage : ZFSet.{u}}
    (hstage : ZFSet.pair index stage ∈ canonicalBareHistory bound)
    (hother : ZFSet.pair index otherStage ∈ canonicalBareHistory bound) :
    otherStage = stage := by
  rcases pair_mem_canonicalBareHistory_iff.mp hstage with
    ⟨ordinal, _hordinal, hindex, hstageEq⟩
  rcases pair_mem_canonicalBareHistory_iff.mp hother with
    ⟨otherOrdinal, _hotherOrdinal, hotherIndex, hotherStageEq⟩
  have hordinals : ordinal = otherOrdinal := by
    apply Ordinal.toZFSet_injective
    exact hindex.symm.trans hotherIndex
  subst otherOrdinal
  exact hotherStageEq.trans hstageEq.symm



/-! ## Proper-class constructibility (not a local bound) -/







/-! ## A formula for one canonical bare pair -/









private theorem comp_canonicalBarePairStageRename_raw
    (fixed : Tuple ZFSet.{u} 13)
    (pair index stage : ZFSet.{u}) :
    (fun i => canonicalBarePairWitnessRawAssignment fixed pair index stage
      (canonicalBarePairStageRename i)) =
      bareStageAtRawAssignment fixed index stage := by
  funext i
  fin_cases i <;> rfl

private theorem canonicalBarePairWitnessRawAssignment_mem
    {U : ZFSet.{u}} (fixed : Tuple ZFSet.{u} 13)
    (pair index stage : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U) (hpair : pair ∈ U)
    (hindex : index ∈ U) (hstage : stage ∈ U) :
    ∀ i, canonicalBarePairWitnessRawAssignment fixed pair index stage i ∈ U := by
  intro i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · simpa only [canonicalBarePairWitnessRawAssignment,
      snoc_last] using hstage
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · simpa only [canonicalBarePairWitnessRawAssignment,
        snoc_castSucc, snoc_last] using hindex
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · simpa only [canonicalBarePairWitnessRawAssignment,
          canonicalBarePairRawAssignment, snoc_castSucc,
          snoc_last] using hpair
      · simpa only [canonicalBarePairWitnessRawAssignment,
          canonicalBarePairRawAssignment, snoc_castSucc] using hfixed i12

private theorem satisfiesIn_isOrdinal_iff_canonicalBare
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (x : ZFSet.{u}) (hx : x ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) OrdinalFormula.isOrdinal ![x] ↔
      x.IsOrdinal := by
  let xU : ZFCarrier U := ⟨x, hx⟩
  have hbridge := satisfies_subtype_iff_satisfiesIn
    (U : Set ZFSet.{u}) OrdinalFormula.isOrdinal ![xU]
  have hsemantic := OrdinalFormula.satisfies_isOrdinal hU xU
  have hraw : (fun i => (![xU] i).1) = ![x] := by
    funext i
    fin_cases i
    rfl
  rw [hraw] at hbridge
  exact hbridge.symm.trans hsemantic

private theorem satisfiesIn_ordinalAt_iff_canonicalBare
    {U : ZFSet.{u}} (hU : U.IsTransitive) {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ j, s j ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) (ordinalAt i) s ↔
      (s i).IsOrdinal := by
  rw [ordinalAt, satisfiesIn_rename]
  have hone : (fun _ : Fin 1 => s i) = ![s i] := by
    funext j
    fin_cases j
    rfl
  rw [hone, satisfiesIn_isOrdinal_iff_canonicalBare hU (s i) (hs i)]

/-- Exact raw semantics of `canonicalBarePairFormula`.  The stage conjunct
is intentionally left as `BareStageAtIn`; identifying it with `LStageZF`
requires a separate correctness hypothesis. -/
private theorem satisfiesIn_canonicalBarePairFormula_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13) (pair : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U) (hpair : pair ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) canonicalBarePairFormula
        (canonicalBarePairRawAssignment fixed pair) ↔
      ∃ index : ZFSet.{u}, index ∈ U ∧ index.IsOrdinal ∧
        ∃ stage : ZFSet.{u}, stage ∈ U ∧
          BareStageAtIn (U : Set ZFSet.{u}) fixed index stage ∧
          pair = ZFSet.pair index stage := by
  simp only [canonicalBarePairFormula, SatisfiesIn]
  apply exists_congr
  intro index
  apply and_congr_right
  intro hindex
  change index ∈ U at hindex
  constructor
  · rintro ⟨stage, hstage, hordinal, hstageAt, hpairEq⟩
    change stage ∈ U at hstage
    let witness := canonicalBarePairWitnessRawAssignment
      fixed pair index stage
    have hwitness : ∀ i, witness i ∈ U :=
      canonicalBarePairWitnessRawAssignment_mem fixed pair index stage
        hfixed hpair hindex hstage
    have hordinal' : index.IsOrdinal :=
      (satisfiesIn_ordinalAt_iff_canonicalBare hU
        (14 : Fin 16) witness hwitness).mp hordinal
    have hstageAt' : BareStageAtIn (U : Set ZFSet.{u})
        fixed index stage := by
      have hrenamed :
          SatisfiesIn (U : Set ZFSet.{u}) bareStageAtFormula
            (bareStageAtRawAssignment fixed index stage) := by
        rw [satisfiesIn_rename] at hstageAt
        change SatisfiesIn (U : Set ZFSet.{u}) bareStageAtFormula
          (fun i => witness (canonicalBarePairStageRename i)) at hstageAt
        rw [comp_canonicalBarePairStageRename_raw] at hstageAt
        exact hstageAt
      exact (satisfiesIn_bareStageAtFormula_iff hU fixed index stage
        hfixed hindex hstage).mp hrenamed
    have hpairEq' := (satisfiesIn_kuratowskiPairEqAt_iff hU
      (13 : Fin 16) (14 : Fin 16) (15 : Fin 16)
      witness hwitness).mp hpairEq
    refine ⟨hordinal', stage, hstage, hstageAt', ?_⟩
    have hpairCoordinate : witness (13 : Fin 16) = pair := rfl
    have hindexCoordinate : witness (14 : Fin 16) = index := rfl
    have hstageCoordinate : witness (15 : Fin 16) = stage := rfl
    simpa only [hpairCoordinate, hindexCoordinate,
      hstageCoordinate] using hpairEq'
  · rintro ⟨hordinal, stage, hstage, hstageAt, hpairEq⟩
    change stage ∈ U at hstage
    let witness := canonicalBarePairWitnessRawAssignment
      fixed pair index stage
    have hwitness : ∀ i, witness i ∈ U :=
      canonicalBarePairWitnessRawAssignment_mem fixed pair index stage
        hfixed hpair hindex hstage
    refine ⟨stage, hstage, ?_, ?_, ?_⟩
    · exact (satisfiesIn_ordinalAt_iff_canonicalBare hU
        (14 : Fin 16) witness hwitness).mpr hordinal
    · rw [satisfiesIn_rename]
      change SatisfiesIn (U : Set ZFSet.{u}) bareStageAtFormula
        (fun i => witness (canonicalBarePairStageRename i))
      rw [comp_canonicalBarePairStageRename_raw]
      exact (satisfiesIn_bareStageAtFormula_iff hU fixed index stage
        hfixed hindex hstage).mpr hstageAt
    · apply (satisfiesIn_kuratowskiPairEqAt_iff hU
        (13 : Fin 16) (14 : Fin 16) (15 : Fin 16)
        witness hwitness).mpr
      have hpairCoordinate : witness (13 : Fin 16) = pair := rfl
      have hindexCoordinate : witness (14 : Fin 16) = index := rfl
      have hstageCoordinate : witness (15 : Fin 16) = stage := rfl
      simpa only [hpairCoordinate, hindexCoordinate,
        hstageCoordinate] using hpairEq





/-- Coordinates of a Kuratowski pair belong to every transitive set which
contains the pair itself. -/
private theorem orderedPair_components_mem_of_transitive
    {U x y : ZFSet.{u}} (hU : U.IsTransitive)
    (hpair : ZFSet.pair x y ∈ U) : x ∈ U ∧ y ∈ U := by
  have hxSingleton : ({x} : ZFSet.{u}) ∈ U :=
    hU.mem_trans (by simp [ZFSet.pair]) hpair
  have hxyPair : ({x, y} : ZFSet.{u}) ∈ U :=
    hU.mem_trans (by simp [ZFSet.pair]) hpair
  exact ⟨hU.mem_trans (by simp) hxSingleton,
    hU.mem_trans (by simp) hxyPair⟩

/-- Under the displayed correctness contract, the canonical-pair formula
has exactly the expected external outputs whose ordinal codes lie in `U`. -/
private theorem satisfiesIn_canonicalBarePairFormula_iff_of_correct
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13) (pair : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U) (hpair : pair ∈ U)
    (hcorrect : CanonicalBareStagesCorrectIn U fixed) :
    SatisfiesIn (U : Set ZFSet.{u}) canonicalBarePairFormula
        (canonicalBarePairRawAssignment fixed pair) ↔
      ∃ ordinal : Ordinal.{u}, ordinal.toZFSet ∈ U ∧
        pair = canonicalBareHistoryPair ordinal := by
  rw [satisfiesIn_canonicalBarePairFormula_iff hU fixed pair
    hfixed hpair]
  constructor
  · rintro ⟨index, hindex, hordinal, stage, hstage,
      hstageAt, hpairEq⟩
    let ordinal : Ordinal.{u} := index.rank
    have hindexEq : index = ordinal.toZFSet :=
      hordinal.toZFSet_rank_eq.symm
    rw [hindexEq] at hindex hstageAt hpairEq
    have hstageEq : stage = LStageZF ordinal :=
      (hcorrect ordinal stage hindex hstage).mp hstageAt
    subst stage
    exact ⟨ordinal, hindex, by
      simpa only [canonicalBareHistoryPair] using hpairEq⟩
  · rintro ⟨ordinal, hindex, hpairEq⟩
    have hcanonicalPair : canonicalBareHistoryPair ordinal ∈ U := by
      simpa only [hpairEq] using hpair
    have hcomponents := orderedPair_components_mem_of_transitive hU
      (by simpa only [canonicalBareHistoryPair] using hcanonicalPair)
    refine ⟨ordinal.toZFSet, hindex, ZFSet.isOrdinal_toZFSet ordinal,
      LStageZF ordinal, hcomponents.2, ?_, ?_⟩
    · exact (hcorrect ordinal (LStageZF ordinal)
        hindex hcomponents.2).mpr rfl
    · simpa only [canonicalBareHistoryPair] using hpairEq

/-! ## Pointwise stage bounds -/

/-- A single canonical graph entry belongs to every nonzero limit level
strictly above its index. -/
private theorem canonicalBareHistoryPair_mem_LStageZF_of_lt_isSuccLimit
    {ordinal theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (hordinal : ordinal < theta) :
    canonicalBareHistoryPair ordinal ∈ LStageZF theta := by
  exact orderedPair_mem_LStageZF_of_isSuccLimit htheta
    (ordinal_toZFSet_mem_LStageZF_of_lt hordinal)
    (LStageZF_mem_LStageZF_of_lt_isSuccLimit htheta hordinal)

/-- Every entry of a bounded canonical history lies in a containing limit
level.  This is deliberately a subset statement; it does not claim that the
whole graph is itself an element of that level. -/
private theorem canonicalBareHistoryBelow_subset_LStageZF
    {bound theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (hbound : bound ≤ theta) :
    canonicalBareHistoryBelow bound ⊆ LStageZF theta := by
  intro entry hentry
  rcases mem_canonicalBareHistoryBelow_iff.mp hentry with
    ⟨ordinal, hordinal, rfl⟩
  exact canonicalBareHistoryPair_mem_LStageZF_of_lt_isSuccLimit
    htheta (hordinal.trans_le hbound)



/-! ## Ordinal bookkeeping for the intended local bound -/

/-- Below a limit, adjoining the finite-code headroom `omega` still stays
below (or reaches) that limit. -/
private theorem add_omega_le_of_lt_isSuccLimit
    {ordinal limit : Ordinal.{u}} (hlimit : Order.IsSuccLimit limit)
    (hordinal : ordinal < limit) :
    ordinal + Ordinal.omega0 ≤ limit := by
  apply (Ordinal.add_le_iff_of_isSuccLimit
    Ordinal.isSuccLimit_omega0).mpr
  intro finite hfinite
  rcases Ordinal.lt_omega0.mp hfinite with ⟨n, rfl⟩
  exact (hlimit.add_natCast_lt hordinal n).le

/-- A successor does not change the `alpha + omega` bookkeeping level. -/
private theorem succ_add_omega (ordinal : Ordinal.{u}) :
    Order.succ ordinal + Ordinal.omega0 =
      ordinal + Ordinal.omega0 := by
  rw [Order.succ_eq_add_one, add_assoc, Ordinal.one_add_omega0]

/-- The intended history-bound level is itself a nonzero limit. -/
private theorem isSuccLimit_add_omega (ordinal : Ordinal.{u}) :
    Order.IsSuccLimit (ordinal + Ordinal.omega0) :=
  Ordinal.isSuccLimit_add ordinal Ordinal.isSuccLimit_omega0

/-! ## Conditional local Separation at a limit -/

private theorem ordinal_lt_of_toZFSet_mem_stage
    {ordinal limit : Ordinal.{u}}
    (hordinal : ordinal.toZFSet ∈ LStageZF limit) : ordinal < limit := by
  have hrank := (ordinal_stage_invariants limit).1
    (ZFSet.isOrdinal_toZFSet ordinal) hordinal
  have heq : (ordinal.toZFSet : ZFSet.{u}).rank = ordinal := by
    apply Ordinal.toZFSet_injective
    exact (ZFSet.isOrdinal_toZFSet ordinal).toZFSet_rank_eq
  simpa only [heq] using hrank

/-- At a limit level, the conditional canonical-pair semantics is exactly
membership in the graph of all strictly earlier stage pairs. -/
private theorem satisfiesIn_canonicalBarePairFormula_stage_iff_of_correct
    {limit : Ordinal.{u}} (_hlimit : Order.IsSuccLimit limit)
    (hfixed : ∀ i : Fin 13,
      canonicalBareFixedParameters.{u} i ∈ LStageZF limit)
    (hcorrect : CanonicalBareStagesCorrectIn
      (LStageZF limit) canonicalBareFixedParameters)
    (pair : ZFSet.{u}) (hpair : pair ∈ LStageZF limit) :
    SatisfiesIn (LStageZF limit : Set ZFSet.{u})
        canonicalBarePairFormula
        (canonicalBarePairRawAssignment
          canonicalBareFixedParameters pair) ↔
      pair ∈ canonicalBareHistoryBelow limit := by
  rw [satisfiesIn_canonicalBarePairFormula_iff_of_correct
    (LStageZF_isTransitive limit) canonicalBareFixedParameters pair
    hfixed hpair hcorrect,
    mem_canonicalBareHistoryBelow_iff]
  constructor
  · rintro ⟨ordinal, hordinal, hpairEq⟩
    exact ⟨ordinal, ordinal_lt_of_toZFSet_mem_stage hordinal,
      hpairEq.symm⟩
  · rintro ⟨ordinal, hordinal, hpairEq⟩
    exact ⟨ordinal,
      ordinal_toZFSet_mem_LStageZF_of_lt hordinal, hpairEq.symm⟩

/-- Conditional Separation theorem for the earlier-pair graph.  Every
assumption is visible: the carrier is a genuine limit level, the fixed
parameters lie in it, and its raw bare-stage predicate is correct. -/
private theorem canonicalBareHistoryBelow_mem_DefZF_of_correct
    {limit : Ordinal.{u}} (hlimit : Order.IsSuccLimit limit)
    (hfixed : ∀ i : Fin 13,
      canonicalBareFixedParameters.{u} i ∈ LStageZF limit)
    (hcorrect : CanonicalBareStagesCorrectIn
      (LStageZF limit) canonicalBareFixedParameters) :
    canonicalBareHistoryBelow limit ∈ DefZF (LStageZF limit) := by
  rw [mem_DefZF_iff_exists_satisfies]
  let params : Tuple (ZFCarrier (LStageZF limit)) 13 :=
    fun i => ⟨canonicalBareFixedParameters i, hfixed i⟩
  refine ⟨canonicalBareHistoryBelow_subset_LStageZF hlimit
      (le_refl limit), 13, params, canonicalBarePairFormula, ?_⟩
  intro pair
  have hbridge := satisfies_subtype_iff_satisfiesIn
    (LStageZF limit : Set ZFSet.{u}) canonicalBarePairFormula
    (snoc params pair)
  have hraw :
      (fun i => (snoc params pair i).1) =
        canonicalBarePairRawAssignment
          canonicalBareFixedParameters pair.1 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rfl
    · simp only [snoc_castSucc, canonicalBarePairRawAssignment,
        params]
  have hsemantic :=
    satisfiesIn_canonicalBarePairFormula_stage_iff_of_correct
      hlimit hfixed hcorrect pair.1 pair.2
  calc
    pair.1 ∈ canonicalBareHistoryBelow limit ↔
        SatisfiesIn (LStageZF limit : Set ZFSet.{u})
          canonicalBarePairFormula
          (canonicalBarePairRawAssignment
            canonicalBareFixedParameters pair.1) := hsemantic.symm
    _ ↔ FOFormula.Satisfies (zfCarrierMem (LStageZF limit))
          canonicalBarePairFormula (snoc params pair) := by
      rw [← hraw]
      exact hbridge.symm

/-- Insertion preserves every nonzero limit level. -/
private theorem insert_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {element old : ZFSet.{u}}
    (helement : element ∈ LStageZF theta)
    (hold : old ∈ LStageZF theta) :
    insert element old ∈ LStageZF theta := by
  rw [ZFSet.insert_eq]
  exact union_mem_LStageZF_of_isSuccLimit htheta
    (singleton_mem_LStageZF_of_isSuccLimit htheta helement) hold

/-- The honest successor step for the intended invariant
`H_alpha ∈ L_(alpha + omega)`. -/
private theorem canonicalBareHistory_succ_mem_LStageZF_add_omega
    (ordinal : Ordinal.{u})
    (hhistory : canonicalBareHistory ordinal ∈
      LStageZF (ordinal + Ordinal.omega0)) :
    canonicalBareHistory (Order.succ ordinal) ∈
      LStageZF (Order.succ ordinal + Ordinal.omega0) := by
  rw [succ_add_omega ordinal, canonicalBareHistory_succ]
  have hlimit := isSuccLimit_add_omega ordinal
  have hordinal : ordinal < ordinal + Ordinal.omega0 :=
    lt_add_of_pos_right ordinal Ordinal.omega0_pos
  have hsuccessor : Order.succ ordinal <
      ordinal + Ordinal.omega0 := hlimit.succ_lt hordinal
  exact insert_mem_LStageZF_of_isSuccLimit hlimit
    (canonicalBareHistoryPair_mem_LStageZF_of_lt_isSuccLimit
      hlimit hsuccessor)
    hhistory

/-- The honest limit step above `omega`: conditional local correctness gives
the earlier graph by Separation, and finite closure then adds the top pair.
The conclusion is the exact invariant, not merely pointwise containment. -/
private theorem canonicalBareHistory_mem_LStageZF_add_omega_of_limit_of_correct
    {limit : Ordinal.{u}} (hlimit : Order.IsSuccLimit limit)
    (homega : Ordinal.omega0 < limit)
    (hcorrect : CanonicalBareStagesCorrectIn
      (LStageZF limit) canonicalBareFixedParameters) :
    canonicalBareHistory limit ∈
      LStageZF (limit + Ordinal.omega0) := by
  have hfixed : ∀ i : Fin 13,
      canonicalBareFixedParameters.{u} i ∈ LStageZF limit := by
    intro i
    exact stageHistoryFixedParameters_mem_LStageZF_of_omega_lt homega i
  have hbelowSucc : canonicalBareHistoryBelow limit ∈
      LStageZF (Order.succ limit) := by
    rw [LStageZF_succ]
    exact canonicalBareHistoryBelow_mem_DefZF_of_correct
      hlimit hfixed hcorrect
  have htargetLimit := isSuccLimit_add_omega limit
  have hlimitTarget : limit < limit + Ordinal.omega0 :=
    lt_add_of_pos_right limit Ordinal.omega0_pos
  have hsuccTarget : Order.succ limit < limit + Ordinal.omega0 :=
    htargetLimit.succ_lt hlimitTarget
  have hbelow : canonicalBareHistoryBelow limit ∈
      LStageZF (limit + Ordinal.omega0) :=
    LStageZF_mono hsuccTarget.le hbelowSucc
  have htop : canonicalBareHistoryPair limit ∈
      LStageZF (limit + Ordinal.omega0) :=
    canonicalBareHistoryPair_mem_LStageZF_of_lt_isSuccLimit
      htargetLimit hlimitTarget
  rw [canonicalBareHistory_eq_insert_top]
  exact insert_mem_LStageZF_of_isSuccLimit htargetLimit htop hbelow

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_CanonicalBareHistory

/- Source module: Solutions.Work_CUGCH_CanonicalBareHistorySemantics -/
section GCHSource_Work_CUGCH_CanonicalBareHistorySemantics
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Internal semantics of the canonical bare history

For an ordinal `alpha`, the set `canonicalBareHistory alpha` is the actual
graph

`{ <beta, L_beta> | beta <= alpha }`.

This file proves an assumption-transparent completeness statement.  If this
particular graph belongs to a transitive carrier `U`, the zero parameter is
the actual empty set, and the internal Goedel evaluator is correct on `U`,
then the graph is internally valid and witnesses the bare-stage formula at
`alpha`.  No reflection or elementarity hypothesis is used, and no theorem
below assumes `CanonicalBareStagesCorrectIn`.
-/

section

universe u

namespace Constructible.Model

noncomputable section

/-- A canonical graph pair belongs to `U` whenever its index is within the
bound and the whole canonical history belongs to the transitive set `U`. -/
private theorem canonicalBareHistoryPair_mem_of_history_mem
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    {bound ordinal : Ordinal.{u}} (hordinal : ordinal ≤ bound)
    (hhistory : canonicalBareHistory bound ∈ U) :
    canonicalBareHistoryPair ordinal ∈ U := by
  apply hU.mem_trans _ hhistory
  exact mem_canonicalBareHistory_iff.mpr
    ⟨ordinal, hordinal, rfl⟩

/-- Consequently both coordinates of every relevant canonical graph pair
belong to `U`. -/
private theorem canonicalBareHistory_components_mem
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    {bound ordinal : Ordinal.{u}} (hordinal : ordinal ≤ bound)
    (hhistory : canonicalBareHistory bound ∈ U) :
    ordinal.toZFSet ∈ U ∧ LStageZF ordinal ∈ U := by
  apply orderedPair_components_mem_of_transitive hU
  simpa only [canonicalBareHistoryPair] using
    (canonicalBareHistoryPair_mem_of_history_mem hU hordinal hhistory)

/-- The canonical graph contains its expected entry at every index through
the bound. -/
private theorem canonicalBareHistory_entry
    {bound ordinal : Ordinal.{u}} (hordinal : ordinal ≤ bound) :
    BareHistoryEntryIn (canonicalBareHistory bound)
      ordinal.toZFSet (LStageZF ordinal) := by
  exact pair_mem_canonicalBareHistory_iff.mpr
    ⟨ordinal, hordinal, rfl, rfl⟩

/-- Before invoking the internal evaluator, the canonical graph satisfies the
usual ambient zero/successor/limit recursion at every index through its
bound.  All witnesses required by the restricted predicate are obtained from
membership of the graph in the transitive carrier. -/
private theorem canonicalBareHistory_localStateAmbientIn
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    {bound ordinal : Ordinal.{u}} (hordinal : ordinal ≤ bound)
    (hhistory : canonicalBareHistory bound ∈ U) :
    BareHistoryLocalStateAmbientIn (U : Set ZFSet.{u}) fixed
      (canonicalBareHistory bound) ordinal.toZFSet
      (LStageZF ordinal) := by
  induction ordinal using Ordinal.limitRecOn with
  | zero =>
      exact Or.inl ⟨by rw [Ordinal.toZFSet_zero, hempty],
        by rw [LStageZF_zero, hempty]⟩
  | add_one alpha _ih =>
      rw [← Order.succ_eq_add_one] at hordinal ⊢
      have hcomponents := canonicalBareHistory_components_mem hU
        ((Order.le_succ alpha).trans hordinal) hhistory
      refine Or.inr (Or.inl
        ⟨alpha.toZFSet, hcomponents.1,
          LStageZF alpha, hcomponents.2, ?_, ?_, ?_⟩)
      · exact (ordinalToZFSet_successor_predecessor_iff
          alpha alpha.toZFSet).mpr rfl
      · exact canonicalBareHistory_entry
          ((Order.le_succ alpha).trans hordinal)
      · rw [LStageZF_succ,
          Godel.DefZF_eq_godelDef (LStageZF_isTransitive alpha)]
  | limit limit hl _ih =>
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · constructor
        · intro hzero
          have hcodes : limit.toZFSet = (0 : Ordinal.{u}).toZFSet := by
            calc
              limit.toZFSet = fixed (2 : Fin 13) := hzero
              _ = (∅ : ZFSet.{u}) := hempty
              _ = (0 : Ordinal.{u}).toZFSet := Ordinal.toZFSet_zero.symm
          exact hl.ne_bot (Ordinal.toZFSet_injective hcodes)
        · intro hpredecessor
          apply ordinalToZFSet_limit_no_predecessor hl
          rcases hpredecessor with
            ⟨predecessor, _hpredecessorU, hpredecessor⟩
          exact ⟨predecessor, hpredecessor⟩
      · intro z _hzU
        constructor
        · intro hz
          rcases (mem_LStageZF_limit_iff hl).mp hz with
            ⟨earlierOrdinal, hearlierOrdinal, hzEarlier⟩
          have hearlierLe : earlierOrdinal ≤ bound :=
            hearlierOrdinal.le.trans hordinal
          have hcomponents := canonicalBareHistory_components_mem hU
            hearlierLe hhistory
          exact ⟨earlierOrdinal.toZFSet, hcomponents.1,
            Ordinal.toZFSet_mem_toZFSet_iff.mpr hearlierOrdinal,
            LStageZF earlierOrdinal, hcomponents.2,
            canonicalBareHistory_entry hearlierLe, hzEarlier⟩
        · rintro ⟨earlierIndex, _hearlierIndexU, hearlierIndex,
            earlierStage, _hearlierStageU, hearlierEntry, hzEarlier⟩
          rcases pair_mem_canonicalBareHistory_iff.mp hearlierEntry with
            ⟨historyOrdinal, _hhistoryOrdinal,
              hearlierIndexEq, hearlierStageEq⟩
          subst earlierIndex
          subst earlierStage
          have hearlierOrdinal : historyOrdinal < limit :=
            Ordinal.toZFSet_mem_toZFSet_iff.mp hearlierIndex
          exact (mem_LStageZF_limit_iff hl).mpr
            ⟨historyOrdinal, hearlierOrdinal, hzEarlier⟩

/-- With the evaluator-correctness obligation supplied explicitly, the same
canonical graph satisfies the internally relativized local rule. -/
private theorem canonicalBareHistory_localStateIn
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : BareGodelDefOutputCorrectIn U fixed)
    {bound ordinal : Ordinal.{u}} (hordinal : ordinal ≤ bound)
    (hhistory : canonicalBareHistory bound ∈ U) :
    BareHistoryLocalStateIn (U : Set ZFSet.{u}) fixed
      (canonicalBareHistory bound) ordinal.toZFSet
      (LStageZF ordinal) := by
  have hstageU :=
    (canonicalBareHistory_components_mem hU hordinal hhistory).2
  apply (bareHistoryLocalStateIn_iff_ambient fixed
    (canonicalBareHistory bound) ordinal.toZFSet
    (LStageZF ordinal) hstageU hcorrect).mpr
  exact canonicalBareHistory_localStateAmbientIn hU fixed hempty
    hordinal hhistory

private theorem exists_ordinal_code_le_of_code_le
    {bound : Ordinal.{u}} {index : ZFSet.{u}}
    (hindex : index ∈ bound.toZFSet ∨ index = bound.toZFSet) :
    ∃ ordinal ≤ bound, index = ordinal.toZFSet := by
  rcases hindex with hindex | rfl
  · rcases Ordinal.mem_toZFSet_iff.mp hindex with
      ⟨ordinal, hordinal, hcode⟩
    exact ⟨ordinal, hordinal.le, hcode.symm⟩
  · exact ⟨bound, le_refl bound, rfl⟩

/-- If the canonical graph through `bound` is an element of a transitive
carrier, it is an internally total, functional, locally correct history
through `bound`.  The only non-bounded semantic input is the explicitly
displayed evaluator-correctness hypothesis. -/
private theorem canonicalBareHistory_validIn
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : BareGodelDefOutputCorrectIn U fixed)
    (bound : Ordinal.{u})
    (hhistory : canonicalBareHistory bound ∈ U) :
    BareValidStageHistoryIn (U : Set ZFSet.{u}) fixed
      (canonicalBareHistory bound) bound.toZFSet := by
  intro index _hindexU hindex
  rcases exists_ordinal_code_le_of_code_le hindex with
    ⟨ordinal, hordinal, rfl⟩
  have hcomponents := canonicalBareHistory_components_mem hU
    hordinal hhistory
  refine ⟨LStageZF ordinal, hcomponents.2,
    canonicalBareHistory_entry hordinal, ?_, ?_⟩
  · intro otherStage _hotherStageU hotherEntry
    exact canonicalBareHistory_functional
      (canonicalBareHistory_entry hordinal) hotherEntry
  · exact canonicalBareHistory_localStateIn hU fixed hempty hcorrect
      hordinal hhistory

/-- Predicate-level completeness: membership of the actual canonical history
in `U` supplies a witness for the actual constructible stage. -/
private theorem canonicalBareHistory_stageAtIn
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : BareGodelDefOutputCorrectIn U fixed)
    (ordinal : Ordinal.{u})
    (hhistory : canonicalBareHistory ordinal ∈ U) :
    BareStageAtIn (U : Set ZFSet.{u}) fixed ordinal.toZFSet
      (LStageZF ordinal) := by
  exact ⟨canonicalBareHistory ordinal, hhistory,
    canonicalBareHistory_validIn hU fixed hempty hcorrect ordinal hhistory,
    canonicalBareHistory_entry (le_refl ordinal)⟩

/-- Combining completeness with the independent soundness induction gives
the exact predicate semantics, conditional only on the displayed canonical
history bound and evaluator correctness. -/
private theorem bareStageAtIn_ordinal_iff_of_canonicalHistory_mem
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : BareGodelDefOutputCorrectIn U fixed)
    (ordinal : Ordinal.{u}) (stage : ZFSet.{u})
    (hindex : ordinal.toZFSet ∈ U) (hstage : stage ∈ U)
    (hhistory : canonicalBareHistory ordinal ∈ U) :
    BareStageAtIn (U : Set ZFSet.{u}) fixed ordinal.toZFSet stage ↔
      stage = LStageZF ordinal := by
  constructor
  · exact bareStageAtIn_ordinal_sound_of_transitive hU fixed hempty
      hcorrect ordinal hindex hstage
  · rintro rfl
    exact canonicalBareHistory_stageAtIn hU fixed hempty hcorrect
      ordinal hhistory





end

end Constructible.Model

end
end GCHSource_Work_CUGCH_CanonicalBareHistorySemantics

/- Source module: Solutions.Work_CUGCH_CanonicalBareHistoryOmegaBounds -/
section GCHSource_Work_CUGCH_CanonicalBareHistoryOmegaBounds
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Finite canonical-history bounds

The canonical history through a finite ordinal is hereditarily finite.  This
is the base input needed when the first infinite limit is treated separately:
the evaluator prefix contains `omega`, so that full prefix cannot be used as
parameters over `L_omega` itself.
-/

section

universe u

namespace Constructible.Model

noncomputable section

/-! ## Finite constructible levels -/







/-- The empty canonical history already belongs to `L_omega`. -/
private theorem canonicalBareHistory_zero_mem_LStageZF_omega :
    canonicalBareHistory (0 : Ordinal.{u}) ∈
      LStageZF (Ordinal.omega0 : Ordinal.{u}) := by
  rw [canonicalBareHistory_eq_insert_top]
  have hbelow :
      canonicalBareHistoryBelow (0 : Ordinal.{u}) = (∅ : ZFSet.{u}) := by
    apply ZFSet.ext
    intro entry
    constructor
    · intro hentry
      rcases mem_canonicalBareHistoryBelow_iff.mp hentry with
        ⟨ordinal, hordinal, _hentry⟩
      exact (not_lt_of_ge bot_le hordinal).elim
    · intro hentry
      exact (ZFSet.notMem_empty entry hentry).elim
  rw [hbelow]
  apply insert_mem_LStageZF_of_isSuccLimit Ordinal.isSuccLimit_omega0
  · exact canonicalBareHistoryPair_mem_LStageZF_of_lt_isSuccLimit
      Ordinal.isSuccLimit_omega0 (Ordinal.natCast_lt_omega0 0)
  · exact empty_mem_LStageZF_of_isSuccLimit Ordinal.isSuccLimit_omega0

/-- Every finite canonical history is an element of `L_omega`, not merely a
subset of that level. -/
private theorem canonicalBareHistory_natCast_mem_LStageZF_omega (n : Nat) :
    canonicalBareHistory (n : Ordinal.{u}) ∈
      LStageZF (Ordinal.omega0 : Ordinal.{u}) := by
  induction n with
  | zero => simpa using canonicalBareHistory_zero_mem_LStageZF_omega
  | succ n ih =>
      rw [Nat.cast_succ, ← Order.succ_eq_add_one,
        canonicalBareHistory_succ]
      apply insert_mem_LStageZF_of_isSuccLimit Ordinal.isSuccLimit_omega0
      · exact canonicalBareHistoryPair_mem_LStageZF_of_lt_isSuccLimit
          Ordinal.isSuccLimit_omega0
          (Ordinal.natCast_lt_omega0 (n + 1))
      · exact ih



end

end Constructible.Model

end
end GCHSource_Work_CUGCH_CanonicalBareHistoryOmegaBounds

/- Source module: Solutions.Work_CUGCH_CanonicalBareHistoryOmega -/
section GCHSource_Work_CUGCH_CanonicalBareHistoryOmega
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The canonical history at the first infinite limit

The full evaluator prefix contains the set `omega`, so it cannot be used as
a parameter over `L_omega`.  We instead work over `L_(omega + 1)` and
restrict the displayed stage index to an element of `omega`.

Crucially, this file does not assert full evaluator correctness in that
successor level.  It isolates the exact weaker fact required here: evaluator
correctness when the predecessor is one of the finite stages `L_n`.
-/

section

universe u

namespace Constructible.Model

noncomputable section

/-! ## The exact finite-input evaluator contract -/



private theorem empty_ne_insert_self_finite (predecessor : ZFSet.{u}) :
    (∅ : ZFSet.{u}) ≠ insert predecessor predecessor := by
  intro h
  have hmem : predecessor ∈ (∅ : ZFSet.{u}) := by
    rw [h]
    exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  exact ZFSet.notMem_empty predecessor hmem

/-! ## Soundness and completeness at finite indices -/

/-- Soundness of an internally recognized finite stage only needs the
finite-input evaluator contract. -/
private theorem bareStageAtIn_natCast_sound_of_transitive
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : FiniteBareGodelDefOutputCorrectIn U fixed)
    (n : Nat) :
    forall {stage : ZFSet.{u}},
      (n : Ordinal.{u}).toZFSet ∈ U -> stage ∈ U ->
      BareStageAtIn (U : Set ZFSet.{u}) fixed
          (n : Ordinal.{u}).toZFSet stage ->
        stage = LStageZF (n : Ordinal.{u}) := by
  induction n with
  | zero =>
      intro stage hindexU hstageU hstageAt
      rcases hstageAt with ⟨history, _hhistoryU, hvalid, hentry⟩
      have hlocal := hvalid.localState_of_entry hindexU hstageU hentry
      rcases hlocal with hbase | hsuccessor | hlimit
      · calc
          stage = fixed (2 : Fin 13) := hbase.2
          _ = (∅ : ZFSet.{u}) := hempty
          _ = LStageZF (0 : Ordinal.{u}) := LStageZF_zero.symm
      · rcases hsuccessor with
          ⟨predecessorIndex, _hpredecessorIndexU,
            _predecessorStage, _hpredecessorStageU,
            hpredecessor, _hentry, _houtput⟩
        have himpossible :
            (∅ : ZFSet.{u}) =
              insert predecessorIndex predecessorIndex := by
          simpa only [Nat.cast_zero, Ordinal.toZFSet_zero] using
            hpredecessor
        exact (empty_ne_insert_self_finite predecessorIndex
          himpossible).elim
      · have hzero :
            ((0 : Nat) : Ordinal.{u}).toZFSet =
              fixed (2 : Fin 13) := by
          rw [Nat.cast_zero, Ordinal.toZFSet_zero, hempty]
        exact (hlimit.1.1 hzero).elim
  | succ n ih =>
      rw [Nat.cast_succ, ← Order.succ_eq_add_one]
      intro stage hindexU hstageU hstageAt
      rcases hstageAt with ⟨history, hhistoryU, hvalid, hentry⟩
      have hlocal := hvalid.localState_of_entry hindexU hstageU hentry
      rcases hlocal with hbase | hsuccessor | hlimit
      · have hcodes :
            (Order.succ (n : Ordinal.{u})).toZFSet =
              (0 : Ordinal.{u}).toZFSet := by
          calc
            (Order.succ (n : Ordinal.{u})).toZFSet =
                fixed (2 : Fin 13) := hbase.1
            _ = (∅ : ZFSet.{u}) := hempty
            _ = (0 : Ordinal.{u}).toZFSet := Ordinal.toZFSet_zero.symm
        have hordinal : Order.succ (n : Ordinal.{u}) = 0 :=
          Ordinal.toZFSet_injective hcodes
        exact (Order.succ_ne_bot (n : Ordinal.{u}) hordinal).elim
      · rcases hsuccessor with
          ⟨predecessorIndex, hpredecessorIndexU,
            predecessorStage, hpredecessorStageU,
            hpredecessor, hpredecessorEntry, houtput⟩
        change predecessorIndex ∈ U at hpredecessorIndexU
        change predecessorStage ∈ U at hpredecessorStageU
        have hpredecessorIndex :
            predecessorIndex = (n : Ordinal.{u}).toZFSet :=
          (ordinalToZFSet_successor_predecessor_iff
            (n : Ordinal.{u}) predecessorIndex).mp hpredecessor
        subst predecessorIndex
        have hpredecessorAt :
            BareStageAtIn (U : Set ZFSet.{u}) fixed
              (n : Ordinal.{u}).toZFSet predecessorStage :=
          bareStageAtIn_of_validHistory hhistoryU rfl
            (Order.le_succ (n : Ordinal.{u})) hvalid hpredecessorEntry
        have hpredecessorStageEq :
            predecessorStage = LStageZF (n : Ordinal.{u}) :=
          ih hpredecessorIndexU hpredecessorStageU hpredecessorAt
        subst predecessorStage
        have hstageEq :
            stage = Godel.godelDef (LStageZF (n : Ordinal.{u})) :=
          (hcorrect n stage hpredecessorStageU hstageU).mp houtput
        calc
          stage = Godel.godelDef (LStageZF (n : Ordinal.{u})) := hstageEq
          _ = DefZF (LStageZF (n : Ordinal.{u})) :=
            (Godel.DefZF_eq_godelDef
              (LStageZF_isTransitive (n : Ordinal.{u}))).symm
          _ = LStageZF (Order.succ (n : Ordinal.{u})) :=
            (LStageZF_succ (n : Ordinal.{u})).symm
      · have hpredecessorMem :
            (n : Ordinal.{u}).toZFSet ∈
              (Order.succ (n : Ordinal.{u})).toZFSet :=
          Ordinal.toZFSet_mem_toZFSet_iff.mpr
            (Order.lt_succ (n : Ordinal.{u}))
        have hpredecessorU : (n : Ordinal.{u}).toZFSet ∈ U :=
          hU.mem_trans hpredecessorMem hindexU
        have hpredecessor :
            (Order.succ (n : Ordinal.{u})).toZFSet =
              insert (n : Ordinal.{u}).toZFSet
                (n : Ordinal.{u}).toZFSet :=
          (ordinalToZFSet_successor_predecessor_iff
            (n : Ordinal.{u}) (n : Ordinal.{u}).toZFSet).mpr rfl
        exact (hlimit.1.2
          ⟨(n : Ordinal.{u}).toZFSet, hpredecessorU,
            hpredecessor⟩).elim

/-- The canonical local rule at a finite index needs evaluator correctness
only for the immediately preceding finite stage. -/
private theorem canonicalBareHistory_localStateIn_natCast
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : FiniteBareGodelDefOutputCorrectIn U fixed)
    {bound : Ordinal.{u}} (n : Nat)
    (hindex : (n : Ordinal.{u}) ≤ bound)
    (hhistory : canonicalBareHistory bound ∈ U) :
    BareHistoryLocalStateIn (U : Set ZFSet.{u}) fixed
      (canonicalBareHistory bound) (n : Ordinal.{u}).toZFSet
      (LStageZF (n : Ordinal.{u})) := by
  cases n with
  | zero =>
      exact Or.inl ⟨by rw [Nat.cast_zero, Ordinal.toZFSet_zero, hempty],
        by rw [Nat.cast_zero, LStageZF_zero, hempty]⟩
  | succ n =>
      rw [Nat.cast_succ, ← Order.succ_eq_add_one] at hindex ⊢
      have hpredecessorLe : (n : Ordinal.{u}) ≤ bound :=
        (Order.le_succ (n : Ordinal.{u})).trans hindex
      have hpredecessorComponents :=
        canonicalBareHistory_components_mem hU hpredecessorLe hhistory
      have hstageComponents :=
        canonicalBareHistory_components_mem hU hindex hhistory
      refine Or.inr (Or.inl
        ⟨(n : Ordinal.{u}).toZFSet, hpredecessorComponents.1,
          LStageZF (n : Ordinal.{u}), hpredecessorComponents.2,
          ?_, ?_, ?_⟩)
      · exact (ordinalToZFSet_successor_predecessor_iff
          (n : Ordinal.{u}) (n : Ordinal.{u}).toZFSet).mpr rfl
      · exact canonicalBareHistory_entry hpredecessorLe
      · apply (hcorrect n (LStageZF (Order.succ (n : Ordinal.{u})))
          hpredecessorComponents.2 hstageComponents.2).mpr
        rw [LStageZF_succ,
          Godel.DefZF_eq_godelDef
            (LStageZF_isTransitive (n : Ordinal.{u}))]

private theorem exists_ordinal_code_le_natCast_of_code_le
    {bound : Nat} {index : ZFSet.{u}}
    (hindex : index ∈ (bound : Ordinal.{u}).toZFSet ∨
      index = (bound : Ordinal.{u}).toZFSet) :
    exists n : Nat, n ≤ bound ∧ index = (n : Ordinal.{u}).toZFSet := by
  have hexists : exists ordinal : Ordinal.{u},
      ordinal ≤ (bound : Ordinal.{u}) ∧ index = ordinal.toZFSet := by
    rcases hindex with hindex | rfl
    · rcases Ordinal.mem_toZFSet_iff.mp hindex with
        ⟨ordinal, hordinal, hcode⟩
      exact ⟨ordinal, hordinal.le, hcode.symm⟩
    · exact ⟨(bound : Ordinal.{u}), le_refl _, rfl⟩
  rcases hexists with ⟨ordinal, hordinal, hcode⟩
  rcases Ordinal.eq_natCast_of_le_natCast hordinal with ⟨n, hn⟩
  subst ordinal
  exact ⟨n, by exact_mod_cast hordinal, hcode⟩

/-- The actual finite canonical graph is internally valid under the exact
finite-input evaluator contract. -/
private theorem canonicalBareHistory_validIn_natCast
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : FiniteBareGodelDefOutputCorrectIn U fixed)
    (bound : Nat)
    (hhistory : canonicalBareHistory (bound : Ordinal.{u}) ∈ U) :
    BareValidStageHistoryIn (U : Set ZFSet.{u}) fixed
      (canonicalBareHistory (bound : Ordinal.{u}))
      (bound : Ordinal.{u}).toZFSet := by
  intro index _hindexU hindex
  rcases exists_ordinal_code_le_natCast_of_code_le hindex with
    ⟨n, hn, rfl⟩
  have hnOrdinal : (n : Ordinal.{u}) ≤ (bound : Ordinal.{u}) := by
    exact_mod_cast hn
  have hcomponents := canonicalBareHistory_components_mem hU
    hnOrdinal hhistory
  refine ⟨LStageZF (n : Ordinal.{u}), hcomponents.2,
    canonicalBareHistory_entry hnOrdinal, ?_, ?_⟩
  · intro otherStage _hotherStageU hotherEntry
    exact canonicalBareHistory_functional
      (canonicalBareHistory_entry hnOrdinal) hotherEntry
  · exact canonicalBareHistory_localStateIn_natCast hU fixed hempty
      hcorrect n hnOrdinal hhistory

/-- Predicate-level completeness at a finite index. -/
private theorem canonicalBareHistory_stageAtIn_natCast
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : FiniteBareGodelDefOutputCorrectIn U fixed)
    (n : Nat)
    (hhistory : canonicalBareHistory (n : Ordinal.{u}) ∈ U) :
    BareStageAtIn (U : Set ZFSet.{u}) fixed
      (n : Ordinal.{u}).toZFSet (LStageZF (n : Ordinal.{u})) := by
  exact ⟨canonicalBareHistory (n : Ordinal.{u}), hhistory,
    canonicalBareHistory_validIn_natCast hU fixed hempty hcorrect n
      hhistory,
    canonicalBareHistory_entry (le_refl (n : Ordinal.{u}))⟩

/-- Exact finite-index semantics, with no claim about nonfinite inputs. -/
private theorem bareStageAtIn_natCast_iff_of_canonicalHistory_mem
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : FiniteBareGodelDefOutputCorrectIn U fixed)
    (n : Nat) (stage : ZFSet.{u})
    (hindex : (n : Ordinal.{u}).toZFSet ∈ U)
    (hstage : stage ∈ U)
    (hhistory : canonicalBareHistory (n : Ordinal.{u}) ∈ U) :
    BareStageAtIn (U : Set ZFSet.{u}) fixed
        (n : Ordinal.{u}).toZFSet stage <->
      stage = LStageZF (n : Ordinal.{u}) := by
  constructor
  · exact bareStageAtIn_natCast_sound_of_transitive hU fixed hempty
      hcorrect n hindex hstage
  · rintro rfl
    exact canonicalBareHistory_stageAtIn_natCast hU fixed hempty
      hcorrect n hhistory

/-! ## A pair formula restricted to finite indices -/



private theorem comp_finiteCanonicalBarePairStageRename_raw
    (fixed : Tuple ZFSet.{u} 13)
    (pair index stage : ZFSet.{u}) :
    (fun i => canonicalBarePairWitnessRawAssignment fixed pair index stage
      (canonicalBarePairStageRename i)) =
      bareStageAtRawAssignment fixed index stage := by
  funext i
  fin_cases i <;> rfl

private theorem finiteCanonicalBarePairWitnessRawAssignment_mem
    {U : ZFSet.{u}} (fixed : Tuple ZFSet.{u} 13)
    (pair index stage : ZFSet.{u})
    (hfixed : forall i, fixed i ∈ U) (hpair : pair ∈ U)
    (hindex : index ∈ U) (hstage : stage ∈ U) :
    forall i,
      canonicalBarePairWitnessRawAssignment fixed pair index stage i ∈ U := by
  intro i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · simpa only [canonicalBarePairWitnessRawAssignment,
      snoc_last] using hstage
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · simpa only [canonicalBarePairWitnessRawAssignment,
        snoc_castSucc, snoc_last] using hindex
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · simpa only [canonicalBarePairWitnessRawAssignment,
          canonicalBarePairRawAssignment, snoc_castSucc,
          snoc_last] using hpair
      · simpa only [canonicalBarePairWitnessRawAssignment,
          canonicalBarePairRawAssignment, snoc_castSucc] using hfixed i12

/-- Exact raw semantics of the finite-index pair formula.  The occurrence of
`index ∈ fixed[12]` is visible in the conclusion; no assumption about that
parameter being `omega` is built into this syntactic theorem. -/
private theorem satisfiesIn_finiteCanonicalBarePairFormula_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13) (pair : ZFSet.{u})
    (hfixed : forall i, fixed i ∈ U) (hpair : pair ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) finiteCanonicalBarePairFormula
        (canonicalBarePairRawAssignment fixed pair) <->
      exists index : ZFSet.{u}, index ∈ U ∧
        index ∈ fixed (12 : Fin 13) ∧
        exists stage : ZFSet.{u}, stage ∈ U ∧
          BareStageAtIn (U : Set ZFSet.{u}) fixed index stage ∧
          pair = ZFSet.pair index stage := by
  simp only [finiteCanonicalBarePairFormula, SatisfiesIn]
  apply exists_congr
  intro index
  apply and_congr_right
  intro hindex
  change index ∈ U at hindex
  constructor
  · rintro ⟨stage, hstage, hindexOmega, hstageAt, hpairEq⟩
    change stage ∈ U at hstage
    let witness := canonicalBarePairWitnessRawAssignment
      fixed pair index stage
    have hwitness : forall i, witness i ∈ U :=
      finiteCanonicalBarePairWitnessRawAssignment_mem fixed pair index stage
        hfixed hpair hindex hstage
    have hstageAt' : BareStageAtIn (U : Set ZFSet.{u})
        fixed index stage := by
      have hrenamed :
          SatisfiesIn (U : Set ZFSet.{u}) bareStageAtFormula
            (bareStageAtRawAssignment fixed index stage) := by
        rw [satisfiesIn_rename] at hstageAt
        change SatisfiesIn (U : Set ZFSet.{u}) bareStageAtFormula
          (fun i => witness (canonicalBarePairStageRename i)) at hstageAt
        rw [comp_finiteCanonicalBarePairStageRename_raw] at hstageAt
        exact hstageAt
      exact (satisfiesIn_bareStageAtFormula_iff hU fixed index stage
        hfixed hindex hstage).mp hrenamed
    have hpairEq' := (satisfiesIn_kuratowskiPairEqAt_iff hU
      (13 : Fin 16) (14 : Fin 16) (15 : Fin 16)
      witness hwitness).mp hpairEq
    refine ⟨hindexOmega, stage, hstage, hstageAt', ?_⟩
    have hpairCoordinate : witness (13 : Fin 16) = pair := rfl
    have hindexCoordinate : witness (14 : Fin 16) = index := rfl
    have hstageCoordinate : witness (15 : Fin 16) = stage := rfl
    simpa only [hpairCoordinate, hindexCoordinate,
      hstageCoordinate] using hpairEq'
  · rintro ⟨hindexOmega, stage, hstage, hstageAt, hpairEq⟩
    change stage ∈ U at hstage
    let witness := canonicalBarePairWitnessRawAssignment
      fixed pair index stage
    have hwitness : forall i, witness i ∈ U :=
      finiteCanonicalBarePairWitnessRawAssignment_mem fixed pair index stage
        hfixed hpair hindex hstage
    refine ⟨stage, hstage, hindexOmega, ?_, ?_⟩
    · rw [satisfiesIn_rename]
      change SatisfiesIn (U : Set ZFSet.{u}) bareStageAtFormula
        (fun i => witness (canonicalBarePairStageRename i))
      rw [comp_finiteCanonicalBarePairStageRename_raw]
      exact (satisfiesIn_bareStageAtFormula_iff hU fixed index stage
        hfixed hindex hstage).mpr hstageAt
    · apply (satisfiesIn_kuratowskiPairEqAt_iff hU
        (13 : Fin 16) (14 : Fin 16) (15 : Fin 16)
        witness hwitness).mpr
      have hpairCoordinate : witness (13 : Fin 16) = pair := rfl
      have hindexCoordinate : witness (14 : Fin 16) = index := rfl
      have hstageCoordinate : witness (15 : Fin 16) = stage := rfl
      simpa only [hpairCoordinate, hindexCoordinate,
        hstageCoordinate] using hpairEq

/-! ## Separation of the graph below `omega` -/



/-- All evaluator parameters, including `omega`, belong to its successor
level. -/
private theorem stageHistoryFixedParametersRaw_mem_LStageZF_omega_succ :
    forall i : Fin 13,
      stageHistoryFixedParametersRaw.{u} i ∈
        LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})) := by
  intro i
  simpa only [stageHistoryFixedParametersRaw] using
    (stageHistoryFixedParameters_mem_LStageZF_of_omega_lt
      (Order.lt_succ (Ordinal.omega0 : Ordinal.{u})) i)

/-- A finite canonical history remains available one level above
`L_omega`. -/
private theorem canonicalBareHistory_natCast_mem_LStageZF_omega_succ (n : Nat) :
    canonicalBareHistory (n : Ordinal.{u}) ∈
      LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})) :=
  LStageZF_mono (Order.le_succ (Ordinal.omega0 : Ordinal.{u}))
    (canonicalBareHistory_natCast_mem_LStageZF_omega n)

/-- Under exactly the finite-input evaluator contract, the restricted pair
formula cuts out the graph of the stages strictly below `omega`. -/
private theorem satisfiesIn_finiteCanonicalBarePairFormula_omega_succ_iff
    (hcorrect : FiniteBareGodelDefOutputCorrectIn
      (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})))
      stageHistoryFixedParametersRaw)
    (pair : ZFSet.{u})
    (hpair : pair ∈
      LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u}))) :
    SatisfiesIn
        (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})) :
          Set ZFSet.{u})
        finiteCanonicalBarePairFormula
        (canonicalBarePairRawAssignment
          stageHistoryFixedParametersRaw pair) <->
      pair ∈ canonicalBareHistoryBelow Ordinal.omega0 := by
  rw [satisfiesIn_finiteCanonicalBarePairFormula_iff
    (LStageZF_isTransitive
      (Order.succ (Ordinal.omega0 : Ordinal.{u})))
    stageHistoryFixedParametersRaw pair
    stageHistoryFixedParametersRaw_mem_LStageZF_omega_succ hpair]
  constructor
  · rintro ⟨index, hindexU, hindexOmega, stage, hstageU,
      hstageAt, hpairEq⟩
    rw [stageHistoryFixedParametersRaw_last] at hindexOmega
    rcases Ordinal.mem_toZFSet_iff.mp hindexOmega with
      ⟨ordinal, hordinal, hindexCode⟩
    rcases Ordinal.lt_omega0.mp hordinal with ⟨n, hn⟩
    subst ordinal
    have hindexEq : index = (n : Ordinal.{u}).toZFSet :=
      hindexCode.symm
    subst index
    have hstageEq : stage = LStageZF (n : Ordinal.{u}) :=
      (bareStageAtIn_natCast_iff_of_canonicalHistory_mem
        (LStageZF_isTransitive
          (Order.succ (Ordinal.omega0 : Ordinal.{u})))
        stageHistoryFixedParametersRaw
        stageHistoryFixedParametersRaw_empty hcorrect n stage
        hindexU hstageU
        (canonicalBareHistory_natCast_mem_LStageZF_omega_succ n)).mp
          hstageAt
    subst stage
    apply mem_canonicalBareHistoryBelow_iff.mpr
    refine ⟨(n : Ordinal.{u}), Ordinal.natCast_lt_omega0 n, ?_⟩
    simpa only [canonicalBareHistoryPair] using hpairEq.symm
  · intro hpairBelow
    rcases mem_canonicalBareHistoryBelow_iff.mp hpairBelow with
      ⟨ordinal, hordinal, hpairEq⟩
    rcases Ordinal.lt_omega0.mp hordinal with ⟨n, hn⟩
    subst ordinal
    have hcanonicalPair : canonicalBareHistoryPair (n : Ordinal.{u}) ∈
        LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})) := by
      simpa only [hpairEq] using hpair
    have hcomponents := orderedPair_components_mem_of_transitive
      (LStageZF_isTransitive
        (Order.succ (Ordinal.omega0 : Ordinal.{u})))
      (by simpa only [canonicalBareHistoryPair] using hcanonicalPair)
    refine ⟨(n : Ordinal.{u}).toZFSet, hcomponents.1, ?_,
      LStageZF (n : Ordinal.{u}), hcomponents.2, ?_, ?_⟩
    · rw [stageHistoryFixedParametersRaw_last]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
        (Ordinal.natCast_lt_omega0 n)
    · exact canonicalBareHistory_stageAtIn_natCast
        (LStageZF_isTransitive
          (Order.succ (Ordinal.omega0 : Ordinal.{u})))
        stageHistoryFixedParametersRaw
        stageHistoryFixedParametersRaw_empty hcorrect n
        (canonicalBareHistory_natCast_mem_LStageZF_omega_succ n)
    · simpa only [canonicalBareHistoryPair] using hpairEq.symm

/-- Genuine internal Separation over `L_(omega+1)` constructs the whole
graph of finite stages. -/
private theorem canonicalBareHistoryBelow_omega_mem_DefZF_omega_succ
    (hcorrect : FiniteBareGodelDefOutputCorrectIn
      (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})))
      stageHistoryFixedParametersRaw) :
    canonicalBareHistoryBelow Ordinal.omega0 ∈
      DefZF (LStageZF (Order.succ
        (Ordinal.omega0 : Ordinal.{u}))) := by
  rw [mem_DefZF_iff_exists_satisfies]
  let params : Tuple
      (ZFCarrier (LStageZF
        (Order.succ (Ordinal.omega0 : Ordinal.{u})))) 13 :=
    fun i => ⟨stageHistoryFixedParametersRaw i,
      stageHistoryFixedParametersRaw_mem_LStageZF_omega_succ i⟩
  refine ⟨?_, 13, params, finiteCanonicalBarePairFormula, ?_⟩
  · intro pair hpair
    exact LStageZF_mono (Order.le_succ
      (Ordinal.omega0 : Ordinal.{u}))
      (canonicalBareHistoryBelow_subset_LStageZF
        Ordinal.isSuccLimit_omega0 (le_refl Ordinal.omega0) hpair)
  · intro pair
    have hbridge := satisfies_subtype_iff_satisfiesIn
      (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})) :
        Set ZFSet.{u}) finiteCanonicalBarePairFormula
      (snoc params pair)
    have hraw :
        (fun i => (snoc params pair i).1) =
          canonicalBarePairRawAssignment
            stageHistoryFixedParametersRaw pair.1 := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simp only [snoc_castSucc, canonicalBarePairRawAssignment,
          params]
    have hsemantic :=
      satisfiesIn_finiteCanonicalBarePairFormula_omega_succ_iff
        hcorrect pair.1 pair.2
    calc
      pair.1 ∈ canonicalBareHistoryBelow Ordinal.omega0 <->
          SatisfiesIn
            (LStageZF (Order.succ
              (Ordinal.omega0 : Ordinal.{u})) : Set ZFSet.{u})
            finiteCanonicalBarePairFormula
            (canonicalBarePairRawAssignment
              stageHistoryFixedParametersRaw pair.1) := hsemantic.symm
      _ <-> FOFormula.Satisfies
          (zfCarrierMem (LStageZF (Order.succ
            (Ordinal.omega0 : Ordinal.{u}))))
          finiteCanonicalBarePairFormula (snoc params pair) := by
        rw [← hraw]
        exact hbridge.symm

/-- The finite-stage graph is therefore present by `L_(omega+2)`. -/
private theorem canonicalBareHistoryBelow_omega_mem_LStageZF_omega_succ_succ
    (hcorrect : FiniteBareGodelDefOutputCorrectIn
      (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})))
      stageHistoryFixedParametersRaw) :
    canonicalBareHistoryBelow Ordinal.omega0 ∈
      LStageZF (Order.succ
        (Order.succ (Ordinal.omega0 : Ordinal.{u}))) := by
  rw [LStageZF_succ]
  exact canonicalBareHistoryBelow_omega_mem_DefZF_omega_succ hcorrect

/-- The honest `H_omega` bound, conditional only on finite-input evaluator
correctness in `L_(omega+1)`.  This is the exceptional base case for the
later uniform invariant `H_alpha ∈ L_(alpha + omega)`. -/
private theorem canonicalBareHistory_omega_mem_LStageZF_add_omega_of_finite_correct
    (hcorrect : FiniteBareGodelDefOutputCorrectIn
      (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})))
      stageHistoryFixedParametersRaw) :
    canonicalBareHistory (Ordinal.omega0 : Ordinal.{u}) ∈
      LStageZF ((Ordinal.omega0 : Ordinal.{u}) + Ordinal.omega0) := by
  have htargetLimit := isSuccLimit_add_omega
    (Ordinal.omega0 : Ordinal.{u})
  have homegaTarget : (Ordinal.omega0 : Ordinal.{u}) <
      (Ordinal.omega0 : Ordinal.{u}) + Ordinal.omega0 :=
    lt_add_of_pos_right Ordinal.omega0 Ordinal.omega0_pos
  have hsuccTarget : Order.succ (Ordinal.omega0 : Ordinal.{u}) <
      (Ordinal.omega0 : Ordinal.{u}) + Ordinal.omega0 :=
    htargetLimit.succ_lt homegaTarget
  have hsuccSuccTarget :
      Order.succ (Order.succ (Ordinal.omega0 : Ordinal.{u})) <
        (Ordinal.omega0 : Ordinal.{u}) + Ordinal.omega0 :=
    htargetLimit.succ_lt hsuccTarget
  have hbelow : canonicalBareHistoryBelow Ordinal.omega0 ∈
      LStageZF ((Ordinal.omega0 : Ordinal.{u}) + Ordinal.omega0) :=
    LStageZF_mono hsuccSuccTarget.le
      (canonicalBareHistoryBelow_omega_mem_LStageZF_omega_succ_succ
        hcorrect)
  have htop : canonicalBareHistoryPair Ordinal.omega0 ∈
      LStageZF ((Ordinal.omega0 : Ordinal.{u}) + Ordinal.omega0) :=
    canonicalBareHistoryPair_mem_LStageZF_of_lt_isSuccLimit
      htargetLimit homegaTarget
  rw [canonicalBareHistory_eq_insert_top]
  exact insert_mem_LStageZF_of_isSuccLimit htargetLimit htop hbelow

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_CanonicalBareHistoryOmega

/- Source module: Solutions.Work_CUGCH_CanonicalBareStageCorrectness -/
section GCHSource_Work_CUGCH_CanonicalBareStageCorrectness
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Exact local correctness from canonical-history bounds

This file packages the two independent parts of the bare-stage argument.
Soundness follows by induction over any internally valid history, whereas
completeness uses the actual graph

`{ <beta, L_beta> | beta <= alpha }`.

The only remaining inputs are stated literally: correctness of the internal
Goedel evaluator and membership of each required canonical graph in the
ambient transitive set.
-/

section

universe u

namespace Constructible.Model

noncomputable section

/-- Exact correctness of the bare-stage predicate follows once every
canonical history whose index is visible in `U` is itself an element of
`U`.  This is a packaging theorem, not a history-bound assertion. -/
private theorem canonicalBareStagesCorrectIn_of_histories_mem
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (hcorrect : BareGodelDefOutputCorrectIn U
      stageHistoryFixedParametersRaw)
    (hhistories : forall ordinal : Ordinal.{u},
      ordinal.toZFSet ∈ U -> canonicalBareHistory ordinal ∈ U) :
    CanonicalBareStagesCorrectIn U stageHistoryFixedParametersRaw := by
  intro ordinal stage hindex hstage
  exact bareStageAtIn_ordinal_iff_of_canonicalHistory_mem hU
    stageHistoryFixedParametersRaw stageHistoryFixedParametersRaw_empty
    hcorrect ordinal stage hindex hstage (hhistories ordinal hindex)

/-- Specialization of the packaging theorem to a constructible level. -/
private theorem canonicalBareStagesCorrectIn_LStageZF_of_histories_mem
    (theta : Ordinal.{u})
    (hcorrect : BareGodelDefOutputCorrectIn (LStageZF theta)
      stageHistoryFixedParametersRaw)
    (hhistories : forall ordinal : Ordinal.{u},
      ordinal.toZFSet ∈ LStageZF theta ->
        canonicalBareHistory ordinal ∈ LStageZF theta) :
    CanonicalBareStagesCorrectIn (LStageZF theta)
      stageHistoryFixedParametersRaw :=
  canonicalBareStagesCorrectIn_of_histories_mem
    (LStageZF_isTransitive theta) hcorrect hhistories

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_CanonicalBareStageCorrectness

/- Source module: Solutions.Work_CUGCH_CanonicalBareHistoryBounds -/
section GCHSource_Work_CUGCH_CanonicalBareHistoryBounds
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The global canonical-history bound from explicit local inputs

This file carries out the transfinite induction for the intended invariant

`canonicalBareHistory alpha ∈ LStageZF (alpha + omega)`.

Two inputs remain visible in the theorem statement: the bound at the first
infinite limit, and correctness of the internal Goedel evaluator at every
larger limit level.  In particular, this file does not assert either input
under a disguised name.
-/

section

universe u

namespace Constructible.Model

noncomputable section

private theorem ordinal_lt_of_toZFSet_mem_LStageZF_for_history_bound
    {theta ordinal : Ordinal.{u}}
    (hordinal : ordinal.toZFSet ∈ LStageZF theta) : ordinal < theta := by
  have hrank := (ordinal_stage_invariants theta).1
    (ZFSet.isOrdinal_toZFSet ordinal) hordinal
  have heq : (ordinal.toZFSet : ZFSet.{u}).rank = ordinal := by
    apply Ordinal.toZFSet_injective
    exact (ZFSet.isOrdinal_toZFSet ordinal).toZFSet_rank_eq
  simpa only [heq] using hrank

/-- The global canonical-history bound, conditional on exactly the two
inputs not supplied by the elementary finite and successor arguments:

* the history through `omega` belongs to `L_(omega + omega)`;
* at every limit `lambda > omega`, the internal Goedel evaluator over
  `L_lambda` has its intended ambient semantics.

At a larger limit, local stage correctness is derived only from history
bounds at strictly smaller ordinals.  Thus the proof is a genuine
transfinite induction rather than a circular use of the global conclusion. -/
private theorem canonicalBareHistory_global_bound_of_omega_and_limit_evaluator
    (homegaHistory : canonicalBareHistory (Ordinal.omega0 : Ordinal.{u}) ∈
      LStageZF (Ordinal.omega0 + Ordinal.omega0))
    (hevaluator : ∀ (limit : Ordinal.{u}),
      Order.IsSuccLimit limit → Ordinal.omega0 < limit →
        BareGodelDefOutputCorrectIn (LStageZF limit)
          stageHistoryFixedParametersRaw) :
    ∀ ordinal : Ordinal.{u}, canonicalBareHistory ordinal ∈
      LStageZF (ordinal + Ordinal.omega0) := by
  intro ordinal
  induction ordinal using Ordinal.limitRecOn with
  | zero =>
      simpa using
        canonicalBareHistory_zero_mem_LStageZF_omega
  | add_one ordinal ih =>
      rw [← Order.succ_eq_add_one]
      exact canonicalBareHistory_succ_mem_LStageZF_add_omega ordinal ih
  | limit limit hlimit ih =>
      by_cases hlimitOmega : limit = Ordinal.omega0
      · subst limit
        exact homegaHistory
      · have homegaLimit : Ordinal.omega0 < limit :=
          lt_of_le_of_ne (Ordinal.omega0_le_of_isSuccLimit hlimit)
            (Ne.symm hlimitOmega)
        have hstageCorrectRaw :
            CanonicalBareStagesCorrectIn (LStageZF limit)
              stageHistoryFixedParametersRaw := by
          apply canonicalBareStagesCorrectIn_LStageZF_of_histories_mem
            limit (hevaluator limit hlimit homegaLimit)
          intro earlier hearlierCode
          have hearlier : earlier < limit :=
            ordinal_lt_of_toZFSet_mem_LStageZF_for_history_bound
              hearlierCode
          exact LStageZF_mono
            (add_omega_le_of_lt_isSuccLimit hlimit hearlier)
            (ih earlier hearlier)
        have hstageCorrect :
            CanonicalBareStagesCorrectIn (LStageZF limit)
              canonicalBareFixedParameters := by
          have hfixedEq : canonicalBareFixedParameters =
              stageHistoryFixedParametersRaw := by
            rfl
          rw [hfixedEq]
          exact hstageCorrectRaw
        exact canonicalBareHistory_mem_LStageZF_add_omega_of_limit_of_correct
          hlimit homegaLimit hstageCorrect

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_CanonicalBareHistoryBounds

/- Source module: Solutions.Work_CUGCH_CanonicalBareHistoryGlobal -/
section GCHSource_Work_CUGCH_CanonicalBareHistoryGlobal
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# The global canonical-history invariant

This file assembles the exact transfinite induction for

`canonicalBareHistory alpha ∈ L_(alpha + omega)`.

The evaluator inputs are kept explicit.  The first is the finite-stage fact
needed only at the exceptional limit `omega`; the second is ordinary local
evaluator correctness at limit levels strictly above `omega`.
-/

section

universe u

namespace Constructible.Model

noncomputable section



/-- The honest global history bound from the two exact evaluator facts used
by its proof.  Neither premise is a disguised history-bound assumption. -/
private theorem canonicalBareHistory_mem_LStageZF_add_omega_of_evaluators_gchProof03
    (hfinite : FiniteBareGodelDefOutputCorrectIn
      (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})))
      stageHistoryFixedParametersRaw)
    (hlimitEvaluator : forall limit : Ordinal.{u},
      Order.IsSuccLimit limit -> Ordinal.omega0 < limit ->
        BareGodelDefOutputCorrectIn (LStageZF limit)
          stageHistoryFixedParametersRaw) :
    forall ordinal : Ordinal.{u},
      canonicalBareHistory ordinal ∈
        LStageZF (ordinal + Ordinal.omega0) := by
  apply canonicalBareHistory_global_bound_of_omega_and_limit_evaluator
  · exact
      canonicalBareHistory_omega_mem_LStageZF_add_omega_of_finite_correct
        hfinite
  · exact hlimitEvaluator







end

end Constructible.Model

end
end GCHSource_Work_CUGCH_CanonicalBareHistoryGlobal

universe u

theorem solution : Constructible.Model.FiniteBareGodelDefOutputCorrectIn.{u}
    (Constructible.LStageZF.{u}
      (@Order.succ.{u + 1} Ordinal.{u} (@PartialOrder.toPreorder.{u + 1} Ordinal.{u} Ordinal.partialOrder.{u})
        Ordinal.instSuccOrder.{u} Ordinal.omega0.{u}))
    Constructible.Model.stageHistoryFixedParametersRaw.{u} →
  (∀ (limit : Ordinal.{u}),
      @Order.IsSuccLimit.{u + 1} Ordinal.{u} (@PartialOrder.toPreorder.{u + 1} Ordinal.{u} Ordinal.partialOrder.{u})
          limit →
        @LT.lt.{u + 1} Ordinal.{u}
            (@Preorder.toLT.{u + 1} Ordinal.{u} (@PartialOrder.toPreorder.{u + 1} Ordinal.{u} Ordinal.partialOrder.{u}))
            Ordinal.omega0.{u} limit →
          Constructible.Model.BareGodelDefOutputCorrectIn.{u} (Constructible.LStageZF.{u} limit)
            Constructible.Model.stageHistoryFixedParametersRaw.{u}) →
    ∀ (ordinal : Ordinal.{u}),
      @Membership.mem.{u + 1, u + 1} ZFSet.{u} ZFSet.{u}
        (@SetLike.instMembership.{u + 1, u + 1} ZFSet.{u} ZFSet.{u} ZFSet.instSetLike.{u})
        (Constructible.LStageZF.{u}
          (@HAdd.hAdd.{u + 1, u + 1, u + 1} Ordinal.{u} Ordinal.{u} Ordinal.{u}
            (@instHAdd.{u + 1} Ordinal.{u} Ordinal.add.{u}) ordinal Ordinal.omega0.{u}))
        (Constructible.Model.canonicalBareHistory.{u} ordinal) :=
  @Constructible.Model.canonicalBareHistory_mem_LStageZF_add_omega_of_evaluators_gchProof03.{u}
