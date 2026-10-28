-- Prove2me | solution 1 for ContinuumHypothesis.Constructible.models_GCH
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T00:34:00.675077+00:00
-- url     : https://prove2.me/submissions/24adf454-427f-4c4d-8286-7488913bdb0e

import Definitions.Def_CH_ConstructibleGCH_HullIteration
import Definitions.Def_CH_ConstructibleGCH_Library27
import Theorems.Thm_Constructible_ContinuumFormula_CardinalControlledHull_element_mem_internalHartogsStage
import Theorems.Thm_Constructible_ContinuumFormula_hartogsStageBound_lCarrier
import Theorems.Thm_Constructible_ContinuumFormula_injects_textbookEElementaryHull_lCarrier
import Theorems.Thm_Constructible_MostowskiCollapse_CondensationHull_exists_internalizedCollapse

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

/- Source module: Solutions.Work_CUGCH_CondensationReflection -/
section GCHSource_Work_CUGCH_CondensationReflection
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Cofinal reflection levels for condensation

A condensation argument needs an ambient level at which the fixed internal
definition of the constructible hierarchy is correct.  This is separate from
the later requirement that a Skolem hull be elementary for *all* formulas.

The single formula below contains both the `V = L` core and, as a syntactic
subformula, the assertion that a stage exists at a supplied index.  Applying
the existing reflection construction to that formula gives arbitrarily high
limit levels at which both relevant subformulas are absolute to `L`.
-/

section

universe u

namespace Constructible

open Set

namespace Model

noncomputable section

local notation "LMem" => lCarrierMem























/-- At a condensation reflection level, the fixed `V = L` core has its
intended canonical assignment. -/
private theorem satisfiesIn_vEqualsLCore_of_condensationReflectionLevel
    {theta : Ordinal.{u}} (htheta : IsCondensationReflectionLevel theta) :
    SatisfiesIn (LStageZF theta : Set ZFSet.{u}) vEqualsLCoreFormula
      (fun i => (stageHistoryFixedParameters.{u} i).1) := by
  apply (satisfiesIn_stage_iff_L_of_closes vEqualsLCoreFormula theta
    htheta.2.2.1 (fun i => (stageHistoryFixedParameters.{u} i).1)
    htheta.2.1).mpr
  apply (satisfies_lCarrier_iff_satisfiesIn_L vEqualsLCoreFormula
    (stageHistoryFixedParameters.{u})).mp
  exact (satisfies_vEqualsLCoreFormula
    (stageHistoryFixedParameters.{u})).mpr rfl





end

end Model

end Constructible

end
end GCHSource_Work_CUGCH_CondensationReflection

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



/--
Tarski--Vaught for one formula and its finite subformula tree.  The explicit
inclusion hypothesis is used when a witness already lies in the smaller
carrier and must be viewed in the larger one.
-/
private theorem satisfiesIn_iff_of_closesWithin
    {small big : Set ZFSet.{u}} (hsubset : small ⊆ big)
    {n : Nat} (phi : FOFormula n) (hclose : ClosesWithin small big phi)
    (s : Tuple ZFSet.{u} n) (hs : forall i, s i ∈ small) :
    Model.SatisfiesIn small phi s <-> Model.SatisfiesIn big phi s := by
  induction phi with
  | mem i j => rfl
  | eq i j => rfl
  | neg phi ih =>
      exact not_congr (ih hclose s hs)
  | conj phi psi ihPhi ihPsi =>
      exact and_congr (ihPhi hclose.1 s hs) (ihPsi hclose.2 s hs)
  | ex phi ih =>
      constructor
      · rintro ⟨x, hxSmall, hphi⟩
        refine ⟨x, hsubset hxSmall, ?_⟩
        apply (ih hclose.1 (snoc s x) ?_).mp hphi
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hxSmall
        · simpa using hs j
      · intro hex
        rcases hclose.2 s hs hex with ⟨x, hxSmall, hphi⟩
        refine ⟨x, hxSmall, ?_⟩
        apply (ih hclose.1 (snoc s x) ?_).mpr hphi
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hxSmall
        · simpa using hs j



/-! ## The extensionality fragment -/







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





/-- Full witness closure implies absoluteness for every first-order formula. -/
private theorem satisfactionAbsolute_of_closesWithinAll
    {small big : Set ZFSet.{u}} (hsubset : small ⊆ big)
    (hclose : ClosesWithinAll small big) :
    SatisfactionAbsolute small big := by
  intro n phi s hs
  exact satisfiesIn_iff_of_closesWithin hsubset phi (hclose phi) s hs







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

/- Source module: Solutions.Work_CUGCH_Condensation -/
section GCHSource_Work_CUGCH_Condensation
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Condensation for constructible levels

This file assembles the order-theoretic condensation core with full
elementarity and the Mostowski collapse.  The only set-recursion input is the
explicit predicate `CollapseDefZFCommutes`: it records that collapse commutes
with one successor step of the constructible hierarchy.  The corresponding
theorem is proved separately from the definability of `DefZF` and is not
silently assumed here.
-/

section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section





namespace CondensationHull

variable {theta : Ordinal.{u}} {domain : ZFSet.{u}}

/--
The thirteen evaluator parameters are not an extra hull hypothesis. At a
condensation reflection level their canonical specification has a witness;
full elementarity pulls a witness into the hull, and uniqueness identifies
that witness with `stageHistoryFixedParameters`.
-/
private theorem fixedParameters_mem_of_elementary
    (hreflection : Model.IsCondensationReflectionLevel theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem :
      SatisfactionAbsolute (domain : Set ZFSet.{u})
        (LStageZF theta : Set ZFSet.{u})) :
    ∀ i : Fin 13,
      (Model.stageHistoryFixedParameters.{u} i).1 ∈ domain := by
  let fixed : Tuple ZFSet.{u} 13 :=
    fun i => (Model.stageHistoryFixedParameters.{u} i).1
  let closedBounded :
      FirstOrder.Language.setTheory.BoundedFormula Empty 0 :=
    (Model.toBoundedFormula
      Model.canonicalStageParametersFormula).exs
  let closed : FOFormula 0 :=
    Model.fromBoundedFormula closedBounded
  let emptyRaw : Tuple ZFSet.{u} 0 := fun i => Fin.elim0 i
  let fixedTheta : Tuple (Model.StageCarrier theta) 13 :=
    fun i => ⟨fixed i, hreflection.2.1 i⟩
  letI stageStructure :
      FirstOrder.Language.setTheory.Structure (Model.StageCarrier theta) :=
    FirstOrder.Language.setTheoryStructure
      (fun x y : Model.StageCarrier theta => x.1 ∈ y.1)
  have hcanonicalTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        Model.canonicalStageParametersFormula fixed :=
    (Model.satisfiesIn_vEqualsLCore_of_condensationReflectionLevel
      hreflection).1
  have hcanonicalThetaTyped :
      FOFormula.Satisfies
        (fun x y : Model.StageCarrier theta => x.1 ∈ y.1)
        Model.canonicalStageParametersFormula fixedTheta := by
    apply (Model.satisfies_stageCarrier_iff_satisfiesIn
      Model.canonicalStageParametersFormula fixedTheta).mpr
    simpa only [fixedTheta, fixed] using hcanonicalTheta
  have hboundedTheta :
      Model.realizes
        (fun x y : Model.StageCarrier theta => x.1 ∈ y.1)
        (Model.toBoundedFormula
          Model.canonicalStageParametersFormula) fixedTheta :=
    (Model.realizes_toBoundedFormula
      (fun x y : Model.StageCarrier theta => x.1 ∈ y.1)
      Model.canonicalStageParametersFormula fixedTheta).mpr
      hcanonicalThetaTyped
  let emptyTheta : Tuple (Model.StageCarrier theta) 0 :=
    fun i => Fin.elim0 i
  have hexBoundedTheta :
      Model.realizes
        (fun x y : Model.StageCarrier theta => x.1 ∈ y.1)
        closedBounded emptyTheta := by
    change
      ((Model.toBoundedFormula
        Model.canonicalStageParametersFormula).exs).Realize
          Empty.elim
    rw [FirstOrder.Language.BoundedFormula.realize_exs]
    exact ⟨fixedTheta, hboundedTheta⟩
  have hclosedThetaTyped :
      FOFormula.Satisfies
        (fun x y : Model.StageCarrier theta => x.1 ∈ y.1)
        closed emptyTheta := by
    exact (Model.realize_fromBoundedFormula
      (fun x y : Model.StageCarrier theta => x.1 ∈ y.1)
      closedBounded emptyTheta).mp hexBoundedTheta
  have hclosedTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        closed emptyRaw := by
    have hbridge := Model.satisfies_stageCarrier_iff_satisfiesIn
      closed emptyTheta
    apply hbridge.mp
    exact hclosedThetaTyped
  have hclosedDomain :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        closed emptyRaw :=
    (helem closed emptyRaw (fun i => Fin.elim0 i)).mpr
      hclosedTheta
  let DomainCarrier :=
    Model.ClassCarrier (domain : Set ZFSet.{u})
  letI domainStructure :
      FirstOrder.Language.setTheory.Structure DomainCarrier :=
    FirstOrder.Language.setTheoryStructure
      (fun x y : DomainCarrier => x.1 ∈ y.1)
  let emptyDomain : Tuple DomainCarrier 0 :=
    fun i => Fin.elim0 i
  have hclosedDomainTyped :
      FOFormula.Satisfies
        (fun x y : DomainCarrier => x.1 ∈ y.1)
        closed emptyDomain := by
    apply (Model.satisfies_subtype_iff_satisfiesIn
      (domain : Set ZFSet.{u}) closed emptyDomain).mpr
    rw [show (fun i => (emptyDomain i).1) = emptyRaw by
      exact Subsingleton.elim _ _]
    exact hclosedDomain
  have hexBoundedDomain :
      Model.realizes
        (fun x y : DomainCarrier => x.1 ∈ y.1)
        closedBounded emptyDomain := by
    exact (Model.realize_fromBoundedFormula
      (fun x y : DomainCarrier => x.1 ∈ y.1)
      closedBounded emptyDomain).mpr hclosedDomainTyped
  change
    ((Model.toBoundedFormula
      Model.canonicalStageParametersFormula).exs).Realize
        Empty.elim at hexBoundedDomain
  rw [FirstOrder.Language.BoundedFormula.realize_exs] at hexBoundedDomain
  rcases hexBoundedDomain with ⟨sDomain, hsDomainBounded⟩
  have hsDomainTyped :
      FOFormula.Satisfies
        (fun x y : DomainCarrier => x.1 ∈ y.1)
        Model.canonicalStageParametersFormula sDomain := by
    apply (Model.realizes_toBoundedFormula
      (fun x y : DomainCarrier => x.1 ∈ y.1)
      Model.canonicalStageParametersFormula sDomain).mp
    exact hsDomainBounded
  let sRaw : Tuple ZFSet.{u} 13 := fun i => (sDomain i).1
  have hsDomainRaw :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        Model.canonicalStageParametersFormula sRaw := by
    apply (Model.satisfies_subtype_iff_satisfiesIn
      (domain : Set ZFSet.{u})
      Model.canonicalStageParametersFormula sDomain).mp
    exact hsDomainTyped
  have hsThetaRaw :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        Model.canonicalStageParametersFormula sRaw :=
    (helem Model.canonicalStageParametersFormula sRaw
      (fun i => (sDomain i).2)).mp hsDomainRaw
  have hcloseCanonical :
      ClosesFrom Model.canonicalStageParametersFormula theta theta := by
    have hcloseCore := hreflection.2.2.1
    change
      ClosesFrom Model.canonicalStageParametersFormula theta theta ∧
        ClosesFrom
          (FOFormula.all Model.constructibleWithParametersFormula)
          theta theta at hcloseCore
    exact hcloseCore.1
  have hsLRaw :
      Model.SatisfiesIn (L : Set ZFSet.{u})
        Model.canonicalStageParametersFormula sRaw :=
    (satisfiesIn_stage_iff_L_of_closes
      Model.canonicalStageParametersFormula theta hcloseCanonical
      sRaw (fun i => hsubset (sDomain i).2)).mp hsThetaRaw
  let sL : Tuple Model.LCarrier.{u} 13 :=
    fun i =>
      ⟨sRaw i,
        mem_L_of_mem (hsubset (sDomain i).2)
          (LStageZF_mem_L theta)⟩
  have hsLTyped :
      FOFormula.Satisfies Model.lCarrierMem
        Model.canonicalStageParametersFormula sL := by
    apply (Model.satisfies_lCarrier_iff_satisfiesIn_L
      Model.canonicalStageParametersFormula sL).mpr
    simpa only [sL, sRaw] using hsLRaw
  have hsLEq :
      sL = Model.stageHistoryFixedParameters :=
    (Model.satisfies_canonicalStageParametersFormula sL).mp hsLTyped
  intro i
  have hvalue :
      (sDomain i).1 =
        (Model.stageHistoryFixedParameters.{u} i).1 := by
    exact congrArg (fun s : Tuple Model.LCarrier.{u} 13 => (s i).1) hsLEq
  rw [← hvalue]
  exact (sDomain i).2

/-- Package a genuinely elementary substructure at a condensation reflection
level. The fixed evaluator parameters are derived, not assumed. -/
private theorem of_elementary
    (hreflection : Model.IsCondensationReflectionLevel theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem :
      SatisfactionAbsolute (domain : Set ZFSet.{u})
        (LStageZF theta : Set ZFSet.{u})) :
    CondensationHull theta domain where
  reflection := hreflection
  subset_stage := hsubset
  satisfactionAbsolute := helem
  fixed_mem := fixedParameters_mem_of_elementary hreflection hsubset helem























/-! ## Bounded stage witnesses for the limit step -/































end CondensationHull

end

end MostowskiCollapse

end Constructible

end
end GCHSource_Work_CUGCH_Condensation

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

/-- Conditional identification of the internal Hartogs number with the
successor cardinal of `base`.

All graph operations except Cantor--Schroeder--Bernstein have already been
constructed inside `L`; consequently CSB is the only explicit hypothesis.
-/
private theorem internalHartogsLCarrier_isSuccessorCardinal_of
    (base : Constructible.Model.LCarrier.{u})
    (hbase : IsCardinal Constructible.Model.lCarrierMem base)
    (hantisymm : InternalInjectionAntisymm
      (A := Constructible.Model.LCarrier.{u})
      Constructible.Model.lCarrierMem) :
    IsSuccessorCardinal Constructible.Model.lCarrierMem base
      (internalHartogsLCarrier base) := by
  let hartogs := internalHartogsLCarrier base
  have hhartogs :
      IsHartogsNumber Constructible.Model.lCarrierMem base hartogs :=
    internalHartogsLCarrier_isHartogsNumber base
  refine ⟨hbase, internalHartogsLCarrier_isCardinal base,
    hhartogs.base_mem_lCarrier hbase, ?_⟩
  rintro ⟨intermediate, hintermediate, hbaseIntermediate,
    hintermediateHartogs⟩
  exact (hintermediate.not_injects_of_mem_lCarrier
      hbaseIntermediate hantisymm)
    (hhartogs.2.2 intermediate hintermediateHartogs)



/-! ## Unconditional specialization to `LCarrier` -/

/-- The internally constructed Cantor--Schroeder--Bernstein bijection
discharges the antisymmetry interface used above. -/
private theorem internalInjectionAntisymm_lCarrier :
    InternalInjectionAntisymm
      (A := Constructible.Model.LCarrier.{u})
      Constructible.Model.lCarrierMem := by
  intro x y hxy hyx
  exact injects_antisymm_lCarrier hxy hyx

/-- The internal Hartogs number of a cardinal is its successor cardinal. -/
private theorem internalHartogsLCarrier_isSuccessorCardinal
    (base : Constructible.Model.LCarrier.{u})
    (hbase : IsCardinal Constructible.Model.lCarrierMem base) :
    IsSuccessorCardinal Constructible.Model.lCarrierMem base
      (internalHartogsLCarrier base) :=
  internalHartogsLCarrier_isSuccessorCardinal_of
    base hbase internalInjectionAntisymm_lCarrier



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

private theorem isInductiveSet_lCarrier_iff_model
    (w : Constructible.Model.LCarrier.{u}) :
    IsInductiveSet LMem w ↔ Constructible.Model.IsInductiveSet w := by
  constructor
  · rintro ⟨⟨empty, hempty, hemptyMem⟩, hsuccessor⟩
    have hemptyEq : empty = emptyLCarrier := by
      apply lCarrier_extensionality
      intro z
      constructor
      · intro hz
        exact (hempty z hz).elim
      · intro hz
        exact (not_mem_emptyLCarrier z hz).elim
    constructor
    · simpa only [hemptyEq] using hemptyMem
    · intro x hx
      rcases hsuccessor x hx with ⟨successor, hsuccessorEq, hsuccessorMem⟩
      have hsuccessorCarrierEq : successor = successorLCarrier x := by
        apply lCarrier_extensionality
        intro z
        have hz := hsuccessorEq z
        change z.1 ∈ successor.1 ↔ z.1 ∈ x.1 ∨ z = x at hz
        change z.1 ∈ successor.1 ↔ z.1 ∈ (successorLCarrier x).1
        rw [hz, successorLCarrier_val,
          ZFSet.mem_insert_iff]
        simp only [Subtype.ext_iff, or_comm]
      simpa only [hsuccessorCarrierEq] using hsuccessorMem
  · rintro ⟨hempty, hsuccessor⟩
    constructor
    · refine ⟨emptyLCarrier, ?_, hempty⟩
      exact not_mem_emptyLCarrier
    · intro x hx
      refine ⟨successorLCarrier x, ?_, hsuccessor x hx⟩
      intro z
      change z.1 ∈ (successorLCarrier x).1 ↔ z.1 ∈ x.1 ∨ z = x
      rw [successorLCarrier_val, ZFSet.mem_insert_iff]
      simp only [Subtype.ext_iff, or_comm]

/-- The standard constructible `omega` is the least internally inductive set
in the relation-parametric semantics used by the GCH sentence. -/
private theorem omegaLCarrier_isOmega :
    IsOmega LMem (omegaLCarrier : Constructible.Model.LCarrier.{u}) := by
  constructor
  · exact (isInductiveSet_lCarrier_iff_model omegaLCarrier).2
      omegaLCarrier_isInductiveSet
  · intro w hw x hx
    exact omegaLCarrier_subset_of_isInductiveSet
      ((isInductiveSet_lCarrier_iff_model w).1 hw) x hx

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

/-- The internal powerset witness supplied by the powerset axiom, expressed
using the relation-parametric predicate occurring in `ModelsGCH`. -/
private theorem exists_powerSetOf_lCarrier
    (base : Constructible.Model.LCarrier.{u}) :
    ∃ power : Constructible.Model.LCarrier.{u},
      IsPowerSetOf LMem base power := by
  rcases Constructible.Model.exists_powerSetLCarrier base with
    ⟨power, hpower⟩
  refine ⟨power, ?_⟩
  intro x
  change x.1 ∈ power.1 ↔ IsSubsetOf LMem x base
  rw [hpower x]
  constructor
  · intro hsubset z hz
    exact hsubset hz
  · intro hsubset z hz
    exact hsubset ⟨z, Constructible.mem_L_of_mem hz x.2⟩ hz

/-- GCH in `LCarrier` follows once every internal infinite cardinal's
internal powerset is internally equinumerous with its Hartogs successor.

This is only a reduction: constructing that bijection is the genuine
condensation/small-stage part of the proof and remains visible as `hpower`.
-/
private theorem modelsGCH_lCarrier_of_powerSet_equinumerous_hartogs
    (hpower :
      ∀ (kappa power : Constructible.Model.LCarrier.{u}),
        IsCardinal LMem kappa →
        IsSubsetOf LMem omegaLCarrier kappa →
        IsPowerSetOf LMem kappa power →
        Equinumerous LMem power (internalHartogsLCarrier kappa)) :
    ModelsGCH (A := Constructible.Model.LCarrier.{u}) LMem := by
  refine ⟨omegaLCarrier, omegaLCarrier_isOmega,
    omegaLCarrier_isCardinal, ?_⟩
  intro kappa hkappa
  rcases exists_powerSetOf_lCarrier kappa with ⟨power, hpowerSet⟩
  refine ⟨internalHartogsLCarrier kappa, power,
    internalHartogsLCarrier_isSuccessorCardinal kappa hkappa.1,
    hpowerSet, ?_⟩
  exact hpower kappa power hkappa.1 hkappa.2 hpowerSet

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_GCHReduction

/- Source module: Solutions.Work_CUGCH_InternalCantor -/
section GCHSource_Work_CUGCH_InternalCantor
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Cantor's theorem inside the constructible universe

The diagonal subset is produced by Full Separation in `L`.  Consequently the
argument rules out an internally represented bijection between a set and its
internal powerset; it does not appeal to ambient cardinal arithmetic.
-/

section

universe u

namespace Constructible.ContinuumFormula









/-! ## The singleton injection into an internal powerset -/







/-- Every set internally injects into its internal powerset by singletons. -/
private theorem injects_powerSet_lCarrier
    {base power : Constructible.Model.LCarrier.{u}}
    (hpower : IsPowerSetOf Constructible.Model.lCarrierMem base power) :
    Injects Constructible.Model.lCarrierMem base power := by
  let container := unionLCarrier base power
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      singletonInjectionPredicate ![base, power] container with
    ⟨graph, hsupport, hrelation⟩
  have hvalue : ∀ x y : Constructible.Model.LCarrier.{u},
      GraphValue Constructible.Model.lCarrierMem graph x y ↔
        x.1 ∈ base.1 ∧ y.1 ∈ power.1 ∧
          IsSingletonOf Constructible.Model.lCarrierMem y x := by
    intro x y
    rw [graphValue_lCarrier_iff_graphRel, hrelation]
    constructor
    · rintro ⟨_hxContainer, _hyContainer, hformula⟩
      exact (satisfies_singletonInjectionPredicate base power x y).mp
        hformula
    · intro hformula
      refine ⟨?_, ?_, ?_⟩
      · exact (mem_unionLCarrier_iff base power x).mpr
          (Or.inl hformula.1)
      · exact (mem_unionLCarrier_iff base power y).mpr
          (Or.inr hformula.2.1)
      · exact (satisfies_singletonInjectionPredicate base power x y).mpr
          hformula
  refine ⟨graph, ?_, ?_, ?_⟩
  · intro pair hpair
    rcases hsupport pair hpair with
      ⟨x, y, _hxContainer, _hyContainer, hpairEq, hformula⟩
    have hsemantic :=
      (satisfies_singletonInjectionPredicate base power x y).mp hformula
    exact ⟨x, hsemantic.1, y, hsemantic.2.1,
      (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq⟩
  · intro x hx
    let singleton : Constructible.Model.LCarrier.{u} :=
      ⟨({x.1} : ZFSet.{u}), Constructible.singleton_mem_L x.2⟩
    have hsingleton :
        IsSingletonOf Constructible.Model.lCarrierMem singleton x := by
      constructor
      · change x.1 ∈ ({x.1} : ZFSet.{u})
        exact ZFSet.mem_singleton.mpr rfl
      · intro z hz
        apply Subtype.ext
        change z.1 ∈ ({x.1} : ZFSet.{u}) at hz
        exact ZFSet.mem_singleton.mp hz
    have hsingletonSubset :
        IsSubsetOf Constructible.Model.lCarrierMem singleton base := by
      intro z hz
      have hzx : z = x := hsingleton.2 z hz
      simpa only [hzx] using hx
    have hsingletonPower : singleton.1 ∈ power.1 :=
      (hpower singleton).mpr hsingletonSubset
    refine ⟨singleton, hsingletonPower,
      (hvalue x singleton).mpr ⟨hx, hsingletonPower, hsingleton⟩, ?_⟩
    intro y _hy hyValue
    have hySingleton := (hvalue x y).mp hyValue |>.2.2
    apply Constructible.Model.lCarrier_extensionality
    intro z
    constructor
    · intro hzy
      have hzx : z = x := hySingleton.2 z hzy
      subst z
      exact hsingleton.1
    · intro hzSingleton
      have hzx : z = x := hsingleton.2 z hzSingleton
      subst z
      exact hySingleton.1
  · intro y _hy x _hx hxy z _hz hzy
    have hySingletonX := (hvalue x y).mp hxy |>.2.2
    have hySingletonZ := (hvalue z y).mp hzy |>.2.2
    exact (hySingletonZ.2 x hySingletonX.1).symm

/--
Cantor's diagonal argument in `LCarrier`: an internal powerset is not
internally equinumerous with its base.
-/
private theorem not_equinumerous_powerSet_lCarrier
    {base power : Constructible.Model.LCarrier.{u}}
    (hpower : IsPowerSetOf Constructible.Model.lCarrierMem base power) :
    ¬Equinumerous Constructible.Model.lCarrierMem base power := by
  rintro ⟨graph, hgraph⟩
  rcases Constructible.Model.exists_separationLCarrier
      cantorDiagonalPredicate ![graph] base with ⟨diagonal, hdiagonal⟩
  have hdiagonalSubset :
      IsSubsetOf Constructible.Model.lCarrierMem diagonal base := by
    intro x hx
    exact (hdiagonal x).mp hx |>.1
  have hdiagonalPower : diagonal.1 ∈ power.1 :=
    (hpower diagonal).mpr hdiagonalSubset
  rcases hgraph.2.2 diagonal hdiagonalPower with
    ⟨x, hxBase, hxDiagonal, _hxUnique⟩
  have hmembership : x.1 ∈ diagonal.1 ↔ x.1 ∉ diagonal.1 := by
    constructor
    · intro hxMem
      rcases (hdiagonal x).mp hxMem with ⟨_hxBase, hpredicate⟩
      rcases (satisfies_cantorDiagonalPredicate graph x).mp
          hpredicate with ⟨image, hxImage, hxNotImage⟩
      rcases hgraph.2.1 x hxBase with
        ⟨value, hvaluePower, hxValue, hvalueUnique⟩
      have himageEq : image = value :=
        hvalueUnique image
          ((hgraph.1.graphValue_mem_lCarrier hxImage).2) hxImage
      have hdiagonalEq : diagonal = value :=
        hvalueUnique diagonal hdiagonalPower hxDiagonal
      have himageDiagonal : image = diagonal :=
        himageEq.trans hdiagonalEq.symm
      simpa only [himageDiagonal] using hxNotImage
    · intro hxNotMem
      apply (hdiagonal x).mpr
      refine ⟨hxBase, ?_⟩
      exact (satisfies_cantorDiagonalPredicate graph x).mpr
        ⟨diagonal, hxDiagonal, hxNotMem⟩
  by_cases hx : x.1 ∈ diagonal.1
  · exact (hmembership.mp hx) hx
  · exact hx (hmembership.mpr hx)



end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalCantor

/- Source module: Solutions.Work_CUGCH_CondensationGCHBridge -/
section GCHSource_Work_CUGCH_CondensationGCHBridge
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# The condensation-to-GCH bridge

This file isolates the exact use of Condensation in the usual proof of GCH
in `L`.  A cardinal-controlled elementary hull containing a subset `x` of an
internal cardinal `kappa` collapses to a level `L_beta`.  If the hull contains
every member of `kappa`, then the collapse fixes `x`; if the hull internally
injects into `kappa`, then `beta` is below the internal Hartogs successor of
`kappa`.  Consequently `x` belongs to that successor-indexed level.

The construction of the full all-formula Skolem hull and the cardinal bound
on the successor-indexed level are deliberately exposed as interfaces.  No
ambient `ZFSet.card` comparison is used as an internal graph witness.
-/

section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section





end

end MostowskiCollapse

namespace ContinuumFormula

open Constructible.Model
open Constructible.MostowskiCollapse

noncomputable section

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## Choosing the ambient reflection level -/



/-! ## Cardinal-controlled hulls -/



namespace CardinalControlledHull

variable {kappa x : LCarrier.{u}}

















end CardinalControlledHull



/-- Full controlled hulls put the entire internal powerset below the
Hartogs-indexed constructible stage. -/
private theorem powerSet_subset_internalHartogsStage
    {kappa power : LCarrier.{u}}
    (hkappa : IsCardinal LMem kappa)
    (hpower : IsPowerSetOf LMem kappa power)
    (hhulls : HasCardinalControlledHulls kappa) :
    ∀ x : LCarrier.{u}, x.1 ∈ power.1 →
      x.1 ∈ LStageZF (internalHartogsOrdinal kappa) := by
  intro x hxPower
  have hxSubset : IsSubsetOf LMem x kappa :=
    (hpower x).mp hxPower
  rcases hhulls x hxSubset with ⟨hull⟩
  exact hull.element_mem_internalHartogsStage hkappa hxSubset

/-- The preceding containment is represented by an actual constructible
identity graph. -/
private theorem powerSet_injects_internalHartogsStage
    {kappa power : LCarrier.{u}}
    (hkappa : IsCardinal LMem kappa)
    (hpower : IsPowerSetOf LMem kappa power)
    (hhulls : HasCardinalControlledHulls kappa) :
    Injects LMem power
      (stageLCarrier (internalHartogsOrdinal kappa)) := by
  apply injects_of_subset_lCarrier
  exact powerSet_subset_internalHartogsStage hkappa hpower hhulls

/-! ## The two remaining cardinal interfaces -/





/-- Condensation plus the stage bound gives the GCH upper injection. -/
private theorem powerSet_injects_internalHartogs
    {kappa power : LCarrier.{u}}
    (hkappa : IsCardinal LMem kappa)
    (hpower : IsPowerSetOf LMem kappa power)
    (hhulls : HasCardinalControlledHulls kappa)
    (hstage : HartogsStageBound kappa) :
    Injects LMem power (internalHartogsLCarrier kappa) :=
  (powerSet_injects_internalHartogsStage hkappa hpower hhulls).trans_lCarrier
    hstage

/-- Internal cardinal representatives and Cantor's theorem give the reverse
injection from `kappa^+` into the powerset. -/
private theorem internalHartogs_injects_powerSet_of_cardinalRepresentatives
    (hrepresentatives : HasInternalCardinalRepresentatives.{u})
    {kappa power : LCarrier.{u}}
    (hkappa : IsCardinal LMem kappa)
    (hpower : IsPowerSetOf LMem kappa power) :
    Injects LMem (internalHartogsLCarrier kappa) power := by
  rcases hrepresentatives power with
    ⟨cardinal, hcardinal, hpowerCardinal⟩
  rcases exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal kappa hkappa.1 with
    ⟨alpha, hkappaEq⟩
  rcases exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal
      cardinal hcardinal.1 with
    ⟨gamma, hcardinalEq⟩
  subst kappa
  subst cardinal
  have hkappaPower : Injects LMem (ordinalLCarrier alpha) power :=
    injects_powerSet_lCarrier hpower
  have hpowerGamma : Injects LMem power (ordinalLCarrier gamma) :=
    hpowerCardinal.injects
  have halphaGamma : alpha < gamma := by
    have hnotGammaAlpha : ¬ gamma < alpha := by
      intro hgammaAlpha
      have hforbidden : Injects LMem
          (ordinalLCarrier alpha) (ordinalLCarrier gamma) :=
        hkappaPower.trans_lCarrier hpowerGamma
      exact (hkappa.not_injects_of_mem_lCarrier
        ((ordinalLCarrier_mem_ordinalLCarrier_iff alpha gamma).mpr
          hgammaAlpha)
        internalInjectionAntisymm_lCarrier) hforbidden
    have halphaLeGamma : alpha ≤ gamma := le_of_not_gt hnotGammaAlpha
    exact lt_of_le_of_ne halphaLeGamma (by
      intro halphaEq
      subst gamma
      exact not_equinumerous_powerSet_lCarrier hpower
        hpowerCardinal.symm_lCarrier)
  let delta := internalHartogsOrdinal (ordinalLCarrier alpha)
  have hdeltaLeGamma : delta ≤ gamma := by
    by_contra hnot
    have hgammaDelta : gamma < delta := lt_of_not_ge hnot
    have hsuccessor := internalHartogsLCarrier_isSuccessorCardinal
      (ordinalLCarrier alpha) hkappa
    apply hsuccessor.2.2.2
    refine ⟨ordinalLCarrier gamma, hcardinal,
      (ordinalLCarrier_mem_ordinalLCarrier_iff gamma alpha).mpr
        halphaGamma, ?_⟩
    simpa only [internalHartogsLCarrier, delta] using
      (ordinalLCarrier_mem_ordinalLCarrier_iff delta gamma).mpr
        hgammaDelta
  have hhartogsGamma : Injects LMem
      (internalHartogsLCarrier (ordinalLCarrier alpha))
      (ordinalLCarrier gamma) := by
    apply injects_of_subset_lCarrier
    intro z hz
    apply (Ordinal.toZFSet_subset_toZFSet_iff.mpr hdeltaLeGamma)
    simpa only [delta, internalHartogsLCarrier,
      ordinalLCarrier_val] using hz
  exact hhartogsGamma.trans_lCarrier
    hpowerCardinal.symm_lCarrier.injects

/-- The exact condensation route to the powerset/Hartogs equinumerosity
required by `GCHReduction`. -/
private theorem powerSet_equinumerous_internalHartogs_of_condensation
    (hrepresentatives : HasInternalCardinalRepresentatives.{u})
    {kappa power : LCarrier.{u}}
    (hkappa : IsCardinal LMem kappa)
    (hpower : IsPowerSetOf LMem kappa power)
    (hhulls : HasCardinalControlledHulls kappa)
    (hstage : HartogsStageBound kappa) :
    Equinumerous LMem power (internalHartogsLCarrier kappa) := by
  exact injects_antisymm_lCarrier
    (powerSet_injects_internalHartogs hkappa hpower hhulls hstage)
    (internalHartogs_injects_powerSet_of_cardinalRepresentatives
      hrepresentatives hkappa hpower)

/-- Once the Skolem-hull and stage-cardinality interfaces are discharged for
all internal infinite cardinals, the existing reduction yields GCH in `L`. -/
private theorem modelsGCH_lCarrier_of_condensation_interfaces
    (hrepresentatives : HasInternalCardinalRepresentatives.{u})
    (hhulls : ∀ kappa : LCarrier.{u},
      IsCardinal LMem kappa →
      IsSubsetOf LMem omegaLCarrier kappa →
      HasCardinalControlledHulls kappa)
    (hstage : ∀ kappa : LCarrier.{u},
      IsCardinal LMem kappa →
      IsSubsetOf LMem omegaLCarrier kappa →
      HartogsStageBound kappa) :
    ModelsGCH (A := LCarrier.{u}) LMem := by
  apply modelsGCH_lCarrier_of_powerSet_equinumerous_hartogs
  intro kappa power hkappa hinfinite hpower
  exact powerSet_equinumerous_internalHartogs_of_condensation
    hrepresentatives hkappa hpower
      (hhulls kappa hkappa hinfinite)
      (hstage kappa hkappa hinfinite)

end

end ContinuumFormula

end Constructible

end
end GCHSource_Work_CUGCH_CondensationGCHBridge

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

/- Source module: Solutions.Work_CUGCH_TextbookESkolemClosure -/
section GCHSource_Work_CUGCH_TextbookESkolemClosure
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Full Tarski--Vaught closure through the textbook E enumeration

The textbook operation `E(U,n,m)` enumerates every positive-arity relation in
`Df(U,n)`.  `TextbookPositiveFormulaEnumeration` proves, without appealing to
an object-language truth predicate, that the relation of every formula with
at least one free coordinate occurs in this enumeration.

This file packages the corresponding full Tarski--Vaught criterion.  If a
subset of `U` contains witnesses for every relation `E(U,n+1,m)` and every
parameter tuple from the subset, then it is closed for every existential
subformula of every first-order formula.  Hence satisfaction is absolute for
all formulas, not merely for a finite fragment.

`ClosesUnderTextbookEWitnesses` is still an external semantic predicate.  No
claim is made here that a small subset satisfying it has already been
constructed inside `L`.  The remaining construction must internally
enumerate the pairs `(n,m)`, uniformly define the canonical witness step, and
collect its omega iteration by Replacement.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

section ZFC



/-- Closure under all textbook `E` witness relations supplies full recursive
Tarski--Vaught closure for every first-order formula. -/
private theorem closesWithinAll_of_closesUnderTextbookEWitnesses
    {small : Set ZFSet.{u}} {U : ZFSet.{u}}
    (hsubset : small ⊆ (U : Set ZFSet.{u}))
    (hclose : ClosesUnderTextbookEWitnesses small U) :
    ClosesWithinAll small (U : Set ZFSet.{u}) := by
  intro n formula
  induction formula with
  | mem i j => trivial
  | eq i j => trivial
  | neg formula ih => exact ih
  | conj formula psi ihFormula ihPsi =>
      exact ⟨ihFormula, ihPsi⟩
  | @ex m matrix ih =>
      refine ⟨ih, ?_⟩
      intro params hparams hexists
      rcases hexists with ⟨x, hxU, hxMatrix⟩
      let paramsU : Tuple (ZFCarrier U) m :=
        fun i => ⟨params i, hsubset (hparams i)⟩
      let xU : ZFCarrier U := ⟨x, hxU⟩
      have hxCarrier :
          FOFormula.Satisfies (zfCarrierMem U) matrix
            (snoc paramsU xU) := by
        apply (Model.satisfies_subtype_iff_satisfiesIn
          (U : Set ZFSet.{u}) matrix (snoc paramsU xU)).mpr
        simpa only [Model.subtypeVal_snoc, paramsU, xU] using hxMatrix
      rcases exists_textbookECode_for_positiveFormula U matrix with
        ⟨code, hcode⟩
      have hxRelation :
          textbookTupleGraph (snoc paramsU xU) ∈
            textbookEZF U (natCode (m + 1)) (natCode code) :=
        (hcode (snoc paramsU xU)).mpr hxCarrier
      rcases hclose code paramsU
          (fun i => by simpa only [paramsU] using hparams i)
          ⟨xU, hxRelation⟩ with
        ⟨w, hwSmall, hwRelation⟩
      refine ⟨w.1, hwSmall, ?_⟩
      have hwCarrier :
          FOFormula.Satisfies (zfCarrierMem U) matrix
            (snoc paramsU w) :=
        (hcode (snoc paramsU w)).mp hwRelation
      have hwRaw :=
        (Model.satisfies_subtype_iff_satisfiesIn
          (U : Set ZFSet.{u}) matrix (snoc paramsU w)).mp hwCarrier
      simpa only [Model.subtypeVal_snoc, paramsU] using hwRaw

/-- The same criterion stated as full satisfaction absoluteness. -/
private theorem satisfactionAbsolute_of_closesUnderTextbookEWitnesses
    {small : Set ZFSet.{u}} {U : ZFSet.{u}}
    (hsubset : small ⊆ (U : Set ZFSet.{u}))
    (hclose : ClosesUnderTextbookEWitnesses small U) :
    SatisfactionAbsolute small (U : Set ZFSet.{u}) :=
  satisfactionAbsolute_of_closesWithinAll hsubset
    (closesWithinAll_of_closesUnderTextbookEWitnesses hsubset hclose)

end ZFC

end Constructible

end
end GCHSource_Work_CUGCH_TextbookESkolemClosure

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

/- Source module: Solutions.Work_CUGCH_TextbookEUniformWitnessStep -/
section GCHSource_Work_CUGCH_TextbookEUniformWitnessStep
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# One simultaneous textbook E witness step

This file forms the actual internal request set

`(omega x (omega \ {0})) x { finite tuple graphs over seed }`

and applies Replacement to the total formula from
`TextbookEUniformWitnessFormula`.  Replacement produces both its genuine
range and its genuine Kuratowski function graph in `L`.  The resulting step
adjoins the range to the seed and simultaneously closes under every decoded
textbook E witness task.
-/

section

open Set

universe u

namespace Constructible.Model

open FiniteSequenceZF
open ContinuumFormula

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## The internal request domain -/











private theorem textbookEUniformTaskLCarrier_mem
    (code arity : Nat) :
    (textbookEUniformTaskLCarrier code arity).1 ∈
      textbookEWitnessTaskDomain.1 := by
  apply (mem_textbookEWitnessTaskDomain_iff
    (textbookEUniformTaskLCarrier code arity).1).mpr
  exact ⟨code, arity, rfl⟩

private theorem textbookEUniformRequestLCarrier_mem
    {seed prefixGraph : LCarrier.{u}} {code arity : Nat}
    (hprefixGraph :
      prefixGraph.1 ∈
        (ContinuumFormula.finiteTupleSpaceLCarrier seed arity).1) :
    (textbookEUniformRequestLCarrier code arity prefixGraph).1 ∈
      (textbookEUniformWitnessRequestDomain seed).1 := by
  apply (mem_textbookEUniformWitnessRequestDomain_iff seed
    (textbookEUniformRequestLCarrier code arity prefixGraph)).mpr
  refine ⟨textbookEUniformTaskLCarrier code arity, prefixGraph,
    textbookEUniformTaskLCarrier_mem code arity, ?_, rfl⟩
  apply (ContinuumFormula.mem_internalFiniteTupleSpaces_iff
    seed prefixGraph).mpr
  exact ⟨arity, hprefixGraph⟩

/-! ## Functionality of the total formula -/









/-! ## Replacement range and graph -/









private theorem seed_subset_textbookEUniformWitnessStep
    (seed U : LCarrier.{u}) :
    seed.1 ⊆ (textbookEUniformWitnessStep seed U).1 := by
  intro x hx
  let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx seed.2⟩
  exact (mem_unionLCarrier_iff seed
    (textbookEUniformWitnessReplacementData seed U).range xL).mpr
      (Or.inl hx)

private theorem textbookEUniformWitnessStep_subset
    {seed U : LCarrier.{u}} (hseed : seed.1 ⊆ U.1)
    (hempty : emptyLCarrier.1 ∈ U.1) :
    (textbookEUniformWitnessStep seed U).1 ⊆ U.1 := by
  intro x hx
  let xL : LCarrier.{u} :=
    ⟨x, mem_L_of_mem hx (textbookEUniformWitnessStep seed U).2⟩
  rcases (mem_unionLCarrier_iff seed
      (textbookEUniformWitnessReplacementData seed U).range xL).mp hx with
    hxSeed | hxRange
  · exact hseed hxSeed
  · rcases
      (textbookEUniformWitnessReplacementData seed U).mem_range_iff xL |>.mp
        hxRange with
      ⟨request, _hrequest, htotal⟩
    rcases (satisfies_textbookEUniformTotalFormula
      U seed (canonicalWitnessOrder U) request xL).mp htotal with
      hselected | ⟨hemptyEq, _hnone⟩
    · rcases
        (satisfies_textbookEUniformSelectedFormula
          U seed (canonicalWitnessOrder U) request xL).mp hselected with
        ⟨_task, _prefixGraph, _code, _positiveArity, _arity,
          _relation, _space, _hrequestEq, _htaskEq, _hsuccessor,
          _hrelation, _hspace, _hprefix, hxU, _hextension, _hminimal⟩
      exact hxU
    · have hxEq : xL.1 = emptyLCarrier.1 :=
        congrArg Subtype.val hemptyEq
      change x = emptyLCarrier.1 at hxEq
      rw [hxEq]
      exact hempty

/-! ## Simultaneous witness closure -/



private theorem textbookTupleGraph_change_codomain_uniform
    {seed U : ZFSet.{u}} {arity : Nat}
    (params : Tuple (ZFCarrier U) arity)
    (hparams : ∀ i, (params i).1 ∈ seed) :
    textbookTupleGraph (fun i => ⟨(params i).1, hparams i⟩) =
      textbookTupleGraph params := by
  apply ZFSet.ext
  intro q
  rw [mem_textbookTupleGraph_iff, mem_textbookTupleGraph_iff]

/--
The uniform Replacement step simultaneously supplies a witness for every
textbook E task and every seed-valued parameter tuple.
-/
private theorem textbookEUniformWitnessStep_closesAt
    (seed U : LCarrier.{u}) (arity code : Nat) :
    ClosesUnderTextbookEWitnessAtFrom seed.1
      (textbookEUniformWitnessStep seed U).1 U.1 arity code := by
  intro params hparams hexists
  let paramsSeed : Tuple (ZFCarrier seed.1) arity :=
    fun i => ⟨(params i).1, hparams i⟩
  have hprefixEq :
      textbookTupleGraph paramsSeed = textbookTupleGraph params :=
    textbookTupleGraph_change_codomain_uniform params hparams
  let prefixGraph : LCarrier.{u} :=
    ⟨textbookTupleGraph params,
      textbookTupleGraph_mem_L U.2 params⟩
  have hprefixSpace :
      prefixGraph.1 ∈
        (ContinuumFormula.finiteTupleSpaceLCarrier seed arity).1 := by
    change textbookTupleGraph params ∈ textbookTupleSpace seed.1 arity
    rw [← hprefixEq]
    exact textbookTupleGraph_mem_tupleSpace paramsSeed
  let relation : LCarrier.{u} :=
    textbookEZFLCarrier U (arity + 1) code
  let arityL : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier arity
  rcases hexists with ⟨x, hxRelation⟩
  let xL : LCarrier.{u} := ⟨x.1, mem_L_of_mem x.2 U.2⟩
  have hxExtension :
      insert (ZFSet.pair arityL.1 xL.1) prefixGraph.1 ∈ relation.1 := by
    change
      insert (ZFSet.pair (natCode arity) x.1)
          (textbookTupleGraph params) ∈
        textbookEZF U.1 (natCode (arity + 1)) (natCode code)
    simpa only [textbookTupleGraph_snoc, textbookTupleSnocGraph] using
      hxRelation
  have hxCandidate :
      xL.1 ∈
        (textbookEWitnessCandidates
          U relation prefixGraph arityL).1 :=
    (mem_textbookEWitnessCandidates_iff
      U relation prefixGraph arityL xL).mpr
        ⟨x.2, hxExtension⟩
  rcases existsUnique_textbookEWitnessMinimum
      U relation prefixGraph arityL ⟨xL, hxCandidate⟩ with
    ⟨y, hyMinimum, _hyUnique⟩
  have hyData := (mem_textbookEWitnessCandidates_iff
    U relation prefixGraph arityL y).mp hyMinimum.1
  have hySelected :
      FOFormula.Satisfies LMem textbookEUniformSelectedFormula
        ![U, seed, canonicalWitnessOrder U,
          textbookEUniformRequestLCarrier code arity prefixGraph, y] := by
    apply
      (satisfies_textbookEUniformSelectedFormula_decoded_iff
        U seed (canonicalWitnessOrder U)
        prefixGraph y arity code).mpr
    refine ⟨hprefixSpace, hyData.1, hyData.2, ?_⟩
    intro z hzU hzExtension
    apply hyMinimum.2 z
    exact (mem_textbookEWitnessCandidates_iff
      U relation prefixGraph arityL z).mpr
        ⟨hzU, hzExtension⟩
  have hrequest :
      (textbookEUniformRequestLCarrier code arity prefixGraph).1 ∈
        (textbookEUniformWitnessRequestDomain seed).1 :=
    textbookEUniformRequestLCarrier_mem hprefixSpace
  have hyRange :
      y.1 ∈
        (textbookEUniformWitnessReplacementData seed U).range.1 := by
    apply
      (textbookEUniformWitnessReplacementData seed U).mem_range_iff y |>.mpr
    refine
      ⟨textbookEUniformRequestLCarrier code arity prefixGraph,
        hrequest, ?_⟩
    apply (satisfies_textbookEUniformTotalFormula
      U seed (canonicalWitnessOrder U)
      (textbookEUniformRequestLCarrier code arity prefixGraph) y).mpr
    exact Or.inl hySelected
  have hyStep :
      y.1 ∈ (textbookEUniformWitnessStep seed U).1 := by
    exact (mem_unionLCarrier_iff seed
      (textbookEUniformWitnessReplacementData seed U).range y).mpr
        (Or.inr hyRange)
  let yU : ZFCarrier U.1 := ⟨y.1, hyData.1⟩
  refine ⟨yU, hyStep, ?_⟩
  change textbookTupleGraph (snoc params yU) ∈ relation.1
  rw [textbookTupleGraph_snoc]
  exact hyData.2



end

end Constructible.Model

end
end GCHSource_Work_CUGCH_TextbookEUniformWitnessStep

/- Source module: Solutions.Work_CUGCH_TextbookEUniformWitnessIteration -/
section GCHSource_Work_CUGCH_TextbookEUniformWitnessIteration
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The internal omega iteration of the uniform textbook E witness step

The simultaneous witness operation from
`TextbookEUniformWitnessStepFormula` is defined by one fixed first-order
formula.  This file applies the general finite-iteration formula to that
operation, uses Replacement over the genuine internal omega, and takes the
internal union of the resulting family.

The final closure proof is the standard finite-tuple maximum-stage argument:
each parameter occurs at a finite stage, all parameters occur together at
their maximum stage, and the next stage supplies the requested witness.
-/

section

open Set

universe u

namespace Constructible.Model

open FiniteSequenceZF
open ContinuumFormula

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Exact finite iteration -/











/-- Each finite stage is contained in its successor. -/
private theorem textbookEUniformWitnessStage_subset_succ
    (seed U : LCarrier.{u}) (n : Nat) :
    (textbookEUniformWitnessStage seed U n).1 ⊆
      (textbookEUniformWitnessStage seed U (n + 1)).1 := by
  exact seed_subset_textbookEUniformWitnessStep
    (textbookEUniformWitnessStage seed U n) U

/-- The finite-stage sequence is monotone. -/
private theorem textbookEUniformWitnessStage_mono
    (seed U : LCarrier.{u}) {m n : Nat} (hmn : m ≤ n) :
    (textbookEUniformWitnessStage seed U m).1 ⊆
      (textbookEUniformWitnessStage seed U n).1 := by
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n _ ih =>
      exact ih.trans
        (textbookEUniformWitnessStage_subset_succ seed U n)

/-- If `seed` is contained in `U` and the empty set belongs to `U`, every
finite stage remains contained in `U`. -/
private theorem textbookEUniformWitnessStage_subset
    (seed U : LCarrier.{u})
    (hseed : seed.1 ⊆ U.1)
    (hempty : emptyLCarrier.1 ∈ U.1)
    (n : Nat) :
    (textbookEUniformWitnessStage seed U n).1 ⊆ U.1 := by
  induction n with
  | zero => exact hseed
  | succ n ih =>
      exact textbookEUniformWitnessStep_subset ih hempty

/-! ## The internal omega family and its union -/









/-- Every finite stage is contained in the internally collected union. -/
private theorem textbookEUniformWitnessStage_subset_omegaUnion
    (seed U : LCarrier.{u}) (n : Nat) :
    (textbookEUniformWitnessStage seed U n).1 ⊆
      (textbookEUniformWitnessOmegaUnion seed U).1 := by
  simpa only [textbookEUniformWitnessOmegaUnion,
    textbookEUniformWitnessOmegaFamilySpec_value] using
    value_subset_parametricUniformOmegaUnion
      (textbookEUniformWitnessOmegaFamilySpec seed U) n

/-- The internally collected omega union contains the initial seed. -/
private theorem seed_subset_textbookEUniformWitnessOmegaUnion
    (seed U : LCarrier.{u}) :
    seed.1 ⊆ (textbookEUniformWitnessOmegaUnion seed U).1 := by
  simpa only [textbookEUniformWitnessStage_zero] using
    textbookEUniformWitnessStage_subset_omegaUnion seed U 0

/-- Under the natural ambient hypotheses, the omega union remains in `U`. -/
private theorem textbookEUniformWitnessOmegaUnion_subset
    (seed U : LCarrier.{u})
    (hseed : seed.1 ⊆ U.1)
    (hempty : emptyLCarrier.1 ∈ U.1) :
    (textbookEUniformWitnessOmegaUnion seed U).1 ⊆ U.1 := by
  intro z hz
  let zL : LCarrier.{u} :=
    ⟨z, mem_L_of_mem hz (textbookEUniformWitnessOmegaUnion seed U).2⟩
  rcases
      (mem_textbookEUniformWitnessOmegaUnion_iff seed U zL).mp hz with
    ⟨n, hzn⟩
  exact textbookEUniformWitnessStage_subset seed U hseed hempty n hzn

/-! ## The finite-tuple maximum-stage argument -/

/-- Every finite tuple from the omega union occurs together in one finite
stage. -/
private theorem exists_textbookEUniformWitnessStage_for_tuple
    (seed U : LCarrier.{u})
    {arity : Nat} (params : Tuple (ZFCarrier U.1) arity)
    (hparams : ∀ i,
      (params i).1 ∈ (textbookEUniformWitnessOmegaUnion seed U).1) :
    ∃ stage : Nat, ∀ i,
      (params i).1 ∈
        (textbookEUniformWitnessStage seed U stage).1 := by
  induction arity with
  | zero =>
      exact ⟨0, fun i => Fin.elim0 i⟩
  | succ arity ih =>
      let initial : Tuple (ZFCarrier U.1) arity :=
        fun i => params i.castSucc
      have hinitial : ∀ i,
          (initial i).1 ∈
            (textbookEUniformWitnessOmegaUnion seed U).1 :=
        fun i => hparams i.castSucc
      rcases ih initial hinitial with
        ⟨initialStage, hinitialStage⟩
      let lastL : LCarrier.{u} :=
        ⟨(params (Fin.last arity)).1,
          mem_L_of_mem (hparams (Fin.last arity))
            (textbookEUniformWitnessOmegaUnion seed U).2⟩
      rcases
          (mem_textbookEUniformWitnessOmegaUnion_iff
            seed U lastL).mp (hparams (Fin.last arity)) with
        ⟨lastStage, hlastStage⟩
      refine ⟨max initialStage lastStage, ?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact textbookEUniformWitnessStage_mono seed U
          (Nat.le_max_right initialStage lastStage) hlastStage
      · exact textbookEUniformWitnessStage_mono seed U
          (Nat.le_max_left initialStage lastStage) (hinitialStage j)

/--
The internally collected omega union is closed under every textbook `E`
witness task.  This is the full closure predicate, obtained only after the
finite iteration has been collected and unioned.
-/
private theorem textbookEUniformWitnessOmegaUnion_closes
    (seed U : LCarrier.{u}) :
    ClosesUnderTextbookEWitnesses
      (textbookEUniformWitnessOmegaUnion seed U).1 U.1 := by
  intro arity code params hparams hexists
  rcases exists_textbookEUniformWitnessStage_for_tuple
      seed U params hparams with
    ⟨stage, hstage⟩
  rcases textbookEUniformWitnessStep_closesAt
      (textbookEUniformWitnessStage seed U stage) U arity code
      params hstage hexists with
    ⟨witness, hwitnessNext, hwitnessRelation⟩
  refine ⟨witness, ?_, hwitnessRelation⟩
  let witnessL : LCarrier.{u} :=
    ⟨witness.1, mem_L_of_mem witness.2 U.2⟩
  apply
    (mem_textbookEUniformWitnessOmegaUnion_iff seed U witnessL).mpr
  exact ⟨stage + 1, hwitnessNext⟩

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_TextbookEUniformWitnessIteration

/- Source module: Solutions.Work_CUGCH_TextbookEElementaryHull -/
section GCHSource_Work_CUGCH_TextbookEElementaryHull
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# The full textbook E elementary hull

For constructible parameters `kappa` and `x`, choose a condensation reflection
level containing both.  Start with the textbook seed

`kappa union {x}`,

represented exactly by `adjoinLCarrier kappa x`, and iterate the simultaneous
textbook `E` witness operation through the internal natural numbers.
Replacement collects the finite stages, and their internal union is fully
elementary in the chosen constructible level.

The construction of the elementary hull is independent of its cardinal
bound.  The final assembly into `CardinalControlledHull` therefore keeps the
remaining smallness premise visible as an actual internal injection from this
specific hull into `kappa`.
-/

section

open Set

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model
open Constructible.MostowskiCollapse

noncomputable section

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## The chosen ambient level and the textbook seed -/



private theorem textbookEElementaryHullTheta_spec
    (kappa x : LCarrier.{u}) :
    IsCondensationReflectionLevel
        (textbookEElementaryHullTheta kappa x) ∧
      kappa.1 ∈ LStageZF (textbookEElementaryHullTheta kappa x) ∧
      x.1 ∈ LStageZF (textbookEElementaryHullTheta kappa x) :=
  Classical.choose_spec
    (exists_condensationReflectionLevel_containing_pair kappa x)





/-- Every member of the seed lies in the selected ambient level. -/
private theorem textbookEElementaryHullSeed_subset_ambient
    (kappa x : LCarrier.{u}) :
    (textbookEElementaryHullSeed kappa x).1 ⊆
      (textbookEElementaryHullAmbient kappa x).1 := by
  intro z hz
  let zL : LCarrier.{u} :=
    ⟨z, mem_L_of_mem hz (textbookEElementaryHullSeed kappa x).2⟩
  rcases (mem_adjoinLCarrier_iff kappa x zL).mp hz with
    hzx | hzkappa
  · have hzEq : z = x.1 := congrArg Subtype.val hzx
    simpa only [textbookEElementaryHullAmbient, stageLCarrier_val,
      hzEq] using (textbookEElementaryHullTheta_spec kappa x).2.2
  · change z ∈ LStageZF (textbookEElementaryHullTheta kappa x)
    exact
      (LStageZF_isTransitive
        (textbookEElementaryHullTheta kappa x)).mem_trans
          hzkappa
          (textbookEElementaryHullTheta_spec kappa x).2.1

/-- The empty set belongs to the selected nonzero limit level. -/
private theorem empty_mem_textbookEElementaryHullAmbient
    (kappa x : LCarrier.{u}) :
    emptyLCarrier.1 ∈ (textbookEElementaryHullAmbient kappa x).1 := by
  change (∅ : ZFSet.{u}) ∈
    LStageZF (textbookEElementaryHullTheta kappa x)
  exact empty_mem_LStageZF_of_isSuccLimit
    (textbookEElementaryHullTheta_spec kappa x).1.1

/-! ## The full elementary hull -/



/-- The full hull stays inside its selected constructible level. -/
private theorem textbookEElementaryHull_subset_ambient
    (kappa x : LCarrier.{u}) :
    (textbookEElementaryHull kappa x).1 ⊆
      LStageZF (textbookEElementaryHullTheta kappa x) := by
  simpa only [textbookEElementaryHull,
    textbookEElementaryHullAmbient, stageLCarrier_val] using
      textbookEUniformWitnessOmegaUnion_subset
        (textbookEElementaryHullSeed kappa x)
        (textbookEElementaryHullAmbient kappa x)
        (textbookEElementaryHullSeed_subset_ambient kappa x)
        (empty_mem_textbookEElementaryHullAmbient kappa x)

/-- Every member of `kappa` belongs to the full hull. -/
private theorem kappa_subset_textbookEElementaryHull
    (kappa x : LCarrier.{u}) :
    kappa.1 ⊆ (textbookEElementaryHull kappa x).1 := by
  intro z hz
  let zL : LCarrier.{u} := ⟨z, mem_L_of_mem hz kappa.2⟩
  apply seed_subset_textbookEUniformWitnessOmegaUnion
    (textbookEElementaryHullSeed kappa x)
    (textbookEElementaryHullAmbient kappa x)
  exact (mem_adjoinLCarrier_iff kappa x zL).mpr (Or.inr hz)

/-- The distinguished subset parameter itself belongs to the full hull. -/
private theorem x_mem_textbookEElementaryHull
    (kappa x : LCarrier.{u}) :
    x.1 ∈ (textbookEElementaryHull kappa x).1 := by
  apply seed_subset_textbookEUniformWitnessOmegaUnion
    (textbookEElementaryHullSeed kappa x)
    (textbookEElementaryHullAmbient kappa x)
  exact (mem_adjoinLCarrier_iff kappa x x).mpr (Or.inl rfl)

/-- The concrete omega union is closed under every textbook E witness task. -/
private theorem textbookEElementaryHull_closesUnderTextbookEWitnesses
    (kappa x : LCarrier.{u}) :
    ClosesUnderTextbookEWitnesses
      (textbookEElementaryHull kappa x).1
      (LStageZF (textbookEElementaryHullTheta kappa x)) := by
  intro arity code params hparams hexists
  exact
    textbookEUniformWitnessOmegaUnion_closes
      (textbookEElementaryHullSeed kappa x)
      (textbookEElementaryHullAmbient kappa x)
      (n := arity) code params hparams hexists

/--
The internally constructed omega union is a fully elementary substructure of
the selected constructible level.
-/
private theorem textbookEElementaryHull_satisfactionAbsolute
    (kappa x : LCarrier.{u}) :
    SatisfactionAbsolute
      ((textbookEElementaryHull kappa x).1 : Set ZFSet.{u})
      (LStageZF (textbookEElementaryHullTheta kappa x) :
        Set ZFSet.{u}) := by
  exact satisfactionAbsolute_of_closesUnderTextbookEWitnesses
    (textbookEElementaryHull_subset_ambient kappa x)
    (textbookEElementaryHull_closesUnderTextbookEWitnesses kappa x)

/-! ## Condensation and the explicit cardinal-smallness interface -/

/-- Package the concrete elementary omega union as a condensation hull. -/
private theorem textbookEElementaryCondensationHull
    (kappa x : LCarrier.{u}) :
    CondensationHull
      (textbookEElementaryHullTheta kappa x)
      (textbookEElementaryHull kappa x).1 :=
  CondensationHull.of_elementary
    (textbookEElementaryHullTheta_spec kappa x).1
    (textbookEElementaryHull_subset_ambient kappa x)
    (textbookEElementaryHull_satisfactionAbsolute kappa x)

/--
If the concrete elementary hull has a genuine internal injection into
`kappa`, it supplies a `CardinalControlledHull`.  No cardinal smallness is
inferred from an external set cardinality.
-/
private theorem nonempty_cardinalControlledHull_of_textbookEElementaryHull_injects
    (kappa x : LCarrier.{u})
    (hsmall :
      Injects LMem (textbookEElementaryHull kappa x) kappa) :
    Nonempty (CardinalControlledHull kappa x) := by
  rcases
      (textbookEElementaryCondensationHull kappa x)
        |>.exists_internalizedCollapse with
    ⟨collapseData, _⟩
  exact ⟨{
    theta := textbookEElementaryHullTheta kappa x
    domain := textbookEElementaryHull kappa x
    hull := textbookEElementaryCondensationHull kappa x
    collapseData := collapseData
    bound_subset := kappa_subset_textbookEElementaryHull kappa x
    element_mem := x_mem_textbookEElementaryHull kappa x
    small := hsmall
  }⟩

/--
Exact all-subsets interface for the remaining cardinal estimate.  For an
infinite internal cardinal, the intended caller supplies `hkappa` and
`omega ⊆ kappa` separately when applying the later GCH bridge; this theorem
uses precisely the still-missing injection for each `x ⊆ kappa`.
-/
private theorem hasCardinalControlledHulls_of_textbookEElementaryHull_injects
    (kappa : LCarrier.{u})
    (hsmall : ∀ x : LCarrier.{u},
      IsSubsetOf LMem x kappa →
        Injects LMem (textbookEElementaryHull kappa x) kappa) :
    HasCardinalControlledHulls kappa := by
  intro x hx
  exact
    nonempty_cardinalControlledHull_of_textbookEElementaryHull_injects
      kappa x (hsmall x hx)

end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_TextbookEElementaryHull

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

















/-- The standard Skolem-hull construction discharges the full
`HasCardinalControlledHulls` interface. -/
private theorem hasCardinalControlledHulls_lCarrier
    (kappa : LCarrier.{u})
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem omegaLCarrier kappa) :
    HasCardinalControlledHulls kappa := by
  apply hasCardinalControlledHulls_of_textbookEElementaryHull_injects
  intro x _hx
  exact injects_textbookEElementaryHull_lCarrier
    kappa x hcardinal homega

end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_TextbookEUniformWitnessCardinality

/- Source module: Solutions.Work_CUGCH_CondensationGCHApplication -/
section GCHSource_Work_CUGCH_CondensationGCHApplication
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# GCH in the constructible universe

This file first records the condensation bridge with its two substantive
interfaces explicit.  It then discharges both interfaces by the textbook
`E`-Skolem-hull construction and the internal Hartogs-stage induction.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

/-- The Condensation reduction yields GCH in `L` once its two genuinely open
interfaces are constructed.  Internal cardinal representatives require no
additional hypothesis. -/
private theorem modelsGCH_lCarrier_of_hulls_and_hartogsStageBound
    (hhulls : forall kappa : LCarrier.{u},
      IsCardinal LMem kappa ->
      IsSubsetOf LMem omegaLCarrier kappa ->
      HasCardinalControlledHulls kappa)
    (hstage : forall kappa : LCarrier.{u},
      IsCardinal LMem kappa ->
      IsSubsetOf LMem omegaLCarrier kappa ->
      HartogsStageBound kappa) :
    ModelsGCH (A := LCarrier.{u}) LMem := by
  exact modelsGCH_lCarrier_of_condensation_interfaces
    hasInternalCardinalRepresentatives_lCarrier hhulls hstage

/-- The constructible membership structure satisfies GCH.

The controlled-hull input is the full textbook `E` Skolem hull, and the
stage-cardinality input is the internal transfinite induction below the
Hartogs successor. -/
private theorem modelsGCH_lCarrier :
    ModelsGCH (A := LCarrier.{u}) LMem :=
  modelsGCH_lCarrier_of_hulls_and_hartogsStageBound
    (fun kappa hcardinal homega =>
      hasCardinalControlledHulls_lCarrier
        kappa hcardinal homega)
    (fun kappa hcardinal homega =>
      hartogsStageBound_lCarrier
        kappa hcardinal homega)

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_CondensationGCHApplication

/- Source module: Solutions.Work_CUGCH_SentenceBridge -/
section GCHSource_Work_CUGCH_SentenceBridge
set_option autoImplicit false


/-!
Semantic bridge for the Prove2Me GCH sentence.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

The constructible hierarchy equivalence reuses our checked adaptation of
Zike Liu's Lean 4 constructible-universe formalization, Apache-2.0,
commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
-/

namespace ContinuumHypothesis.Constructible.GCHBridge
open FirstOrder FirstOrder.Language
noncomputable section
open Classical
set_option Elab.async false
set_option maxHeartbeats 1000000








private theorem transport_gch (h : M ⊨ gchSentence) : Carrier ⊨ gchSentence :=
  (StrongHomClass.realize_sentence carrierIso gchSentence).mpr h


















private theorem named_all {A : Type*} [setLang.Structure A]
    (v : ℕ → A) (i : ℕ) (φ : SFormula) :
    Formula.Realize (SFormula.all i φ) v ↔
      ∀ z : A, Formula.Realize φ (Function.update v i z) := by
  rw [SFormula.all, Formula.realize_iAlls]
  simp only [Formula.realize_relabel]
  have heq (u : Unit → A) :
      (Sum.elim v u) ∘ (fun j => if j = i then Sum.inr () else Sum.inl j) =
        Function.update v i (u ()) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  simp only [heq]
  constructor
  · intro h z; exact h (fun _ => z)
  · intro h u; exact h (u ())

private theorem named_ex {A : Type*} [setLang.Structure A]
    (v : ℕ → A) (i : ℕ) (φ : SFormula) :
    Formula.Realize (SFormula.ex i φ) v ↔
      ∃ z : A, Formula.Realize φ (Function.update v i z) := by
  rw [SFormula.ex, Formula.realize_iExs]
  simp only [Formula.realize_relabel]
  have heq (u : Unit → A) :
      (Sum.elim v u) ∘ (fun j => if j = i then Sum.inr () else Sum.inl j) =
        Function.update v i (u ()) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  simp only [heq]
  constructor
  · rintro ⟨u, hu⟩; exact ⟨u (), hu⟩
  · rintro ⟨z, hz⟩; exact ⟨fun _ => z, hz⟩







private theorem realizes_subset (v : ℕ → M) (x y : ℕ)
    (hx : Fresh 1000 x) (hy : Fresh 1000 y) :
    Formula.Realize (SFormula.subset x y) v ↔ SubsetOf (v x) (v y) := by
  simp (disch := (simp only [Fresh] at *; omega)) only
    [SFormula.subset, named_all, Formula.realize_imp, named_mem,
      Function.update_self, Function.update_of_ne, SubsetOf]

private theorem realizes_empty (v : ℕ → M) (x : ℕ) (hx : Fresh 1001 x) :
    Formula.Realize (SFormula.isEmpty x) v ↔ EmptySet (v x) := by
  simp (disch := (simp only [Fresh] at *; omega)) only
    [SFormula.isEmpty, named_all, Formula.realize_not, named_mem,
      Function.update_self, Function.update_of_ne, EmptySet]

private theorem realizes_succ (v : ℕ → M) (s z : ℕ)
    (hs : Fresh 1002 s) (hz : Fresh 1002 z) :
    Formula.Realize (SFormula.isSucc s z) v ↔ SuccessorOf (v s) (v z) := by
  simp (disch := (simp only [Fresh] at *; omega)) only
    [SFormula.isSucc, named_all, Formula.realize_iff, Formula.realize_sup,
      named_mem, named_eq, Function.update_self, Function.update_of_ne, SuccessorOf]

private theorem realizes_inductive (v : ℕ → M) (w : ℕ) (hw : Fresh 1005 w) :
    Formula.Realize (SFormula.isInductive w) v ↔ InductiveSet (v w) := by
  simp (disch := (simp only [Fresh] at *; omega)) only
    [SFormula.isInductive, Formula.realize_inf, Formula.realize_imp,
      named_all, named_ex, realizes_empty, realizes_succ, named_mem,
      Function.update_self, Function.update_of_ne, InductiveSet]

private theorem realizes_omega (v : ℕ → M) (w : ℕ) (hw : Fresh 1006 w) :
    Formula.Realize (SFormula.isOmega w) v ↔ Omega (v w) := by
  simp (disch := (simp only [Fresh] at *; omega)) only
    [SFormula.isOmega, Formula.realize_inf, Formula.realize_imp,
      named_all, realizes_inductive, realizes_subset,
      Function.update_self, Function.update_of_ne, Omega]

private theorem realizes_powerSet (v : ℕ → M) (p x : ℕ)
    (hp : Fresh 1007 p) (hx : Fresh 1007 x) :
    Formula.Realize (SFormula.isPowerset p x) v ↔ PowerSetOf (v p) (v x) := by
  simp (disch := (simp only [Fresh] at *; omega)) only
    [SFormula.isPowerset, Formula.realize_iff, named_all, named_mem,
      realizes_subset, Function.update_self, Function.update_of_ne, PowerSetOf]

private theorem realizes_singleton (v : ℕ → M) (s x : ℕ)
    (hs : Fresh 1008 s) (hx : Fresh 1008 x) :
    Formula.Realize (SFormula.isSingleton s x) v ↔ SingletonOf (v s) (v x) := by
  simp (disch := (simp only [Fresh] at *; omega)) only
    [SFormula.isSingleton, Formula.realize_iff, named_all, named_mem, named_eq,
      Function.update_self, Function.update_of_ne, SingletonOf]

private theorem realizes_doubleton (v : ℕ → M) (s x y : ℕ)
    (hs : Fresh 1009 s) (hx : Fresh 1009 x) (hy : Fresh 1009 y) :
    Formula.Realize (SFormula.isDoubleton s x y) v ↔ DoubletonOf (v s) (v x) (v y) := by
  simp (disch := (simp only [Fresh] at *; omega)) only
    [SFormula.isDoubleton, Formula.realize_iff, Formula.realize_sup,
      named_all, named_mem, named_eq,
      Function.update_self, Function.update_of_ne, DoubletonOf]

private theorem realizes_pair (v : ℕ → M) (p x y : ℕ)
    (hp : Fresh 1010 p) (hx : Fresh 1010 x) (hy : Fresh 1010 y) :
    Formula.Realize (SFormula.isPair p x y) v ↔ PairOf (v p) (v x) (v y) := by
  simp (disch := (simp only [Fresh] at *; omega)) only
    [SFormula.isPair, Formula.realize_iff, Formula.realize_sup,
      named_all, named_mem, realizes_singleton, realizes_doubleton,
      Function.update_self, Function.update_of_ne, PairOf]

private theorem realizes_pairIn (v : ℕ → M) (f x y : ℕ)
    (hf : Fresh 1011 f) (hx : Fresh 1011 x) (hy : Fresh 1011 y) :
    Formula.Realize (SFormula.pairIn f x y) v ↔ PairIn (v f) (v x) (v y) := by
  simp (disch := (simp only [Fresh] at *; omega)) only
    [SFormula.pairIn, Formula.realize_inf, named_ex, named_mem, realizes_pair,
      Function.update_self, Function.update_of_ne, PairIn]

private theorem realizes_injection (v : ℕ → M) (f x y : ℕ)
    (hf : Fresh 1015 f) (hx : Fresh 1015 x) (hy : Fresh 1015 y) :
    Formula.Realize (SFormula.isInjection f x y) v ↔ Injection (v f) (v x) (v y) := by
  simp (disch := (simp only [Fresh] at *; omega)) only
    [SFormula.isInjection, Formula.realize_inf, Formula.realize_imp,
      named_all, named_ex, named_mem, named_eq, realizes_pairIn,
      Function.update_self, Function.update_of_ne, Injection, and_assoc]

private theorem realizes_injects (v : ℕ → M) (x y : ℕ)
    (hx : Fresh 1016 x) (hy : Fresh 1016 y) :
    Formula.Realize (SFormula.injects x y) v ↔ Injects (v x) (v y) := by
  simp (disch := (simp only [Fresh] at *; omega)) only
    [SFormula.injects, named_ex, realizes_injection,
      Function.update_self, Function.update_of_ne, Injects]

private theorem realizes_bijection (v : ℕ → M) (f x y : ℕ)
    (hf : Fresh 1018 f) (hx : Fresh 1018 x) (hy : Fresh 1018 y) :
    Formula.Realize (SFormula.isBijection f x y) v ↔ Bijection (v f) (v x) (v y) := by
  simp (disch := (simp only [Fresh] at *; omega)) only
    [SFormula.isBijection, Formula.realize_inf, Formula.realize_imp,
      named_all, named_ex, named_mem, realizes_injection, realizes_pairIn,
      Function.update_self, Function.update_of_ne, Bijection]

private theorem realizes_equinum (v : ℕ → M) (x y : ℕ)
    (hx : Fresh 1019 x) (hy : Fresh 1019 y) :
    Formula.Realize (SFormula.equinum x y) v ↔ Equinumerous (v x) (v y) := by
  simp (disch := (simp only [Fresh] at *; omega)) only
    [SFormula.equinum, named_ex, realizes_bijection,
      Function.update_self, Function.update_of_ne, Equinumerous]

private theorem realizes_finite (v : ℕ → M) (s : ℕ) (hs : Fresh 1021 s) :
    Formula.Realize (SFormula.isFiniteSet s) v ↔ FiniteSet (v s) := by
  simp (disch := (simp only [Fresh] at *; omega)) only
    [SFormula.isFiniteSet, Formula.realize_inf, named_ex,
      named_mem, realizes_omega, realizes_equinum,
      Function.update_self, Function.update_of_ne, FiniteSet]

private theorem realizes_gch (v : ℕ → M) :
    Formula.Realize SFormula.gch v ↔ GapGCH := by
  simp (disch := (simp only [Fresh] at * <;> omega)) only
    [SFormula.gch, Formula.realize_not, Formula.realize_imp,
      Formula.realize_inf, Formula.realize_sup, named_all,
      realizes_finite, realizes_powerSet, realizes_injects, realizes_equinum,
      Function.update_self, Function.update_of_ne, GapGCH]
  simp [-Subtype.forall, -Subtype.exists, Function.update_apply]

private theorem sentence_of_gapGCH (h : GapGCH) : M ⊨ gchSentence := by
  change Formula.Realize (SFormula.close SFormula.gch) (default : Empty → M)
  rw [SFormula.close, Formula.realize_iAlls]
  intro v
  apply Formula.realize_relabel.mpr
  exact (realizes_gch _).mpr h

end
end ContinuumHypothesis.Constructible.GCHBridge


end GCHSource_Work_CUGCH_SentenceBridge

/- Source module: Solutions.Work_CUGCH_InternalBridge -/
section GCHSource_Work_CUGCH_InternalBridge
set_option autoImplicit false




/-!
Internal semantic comparison for the two GCH formulations.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

The existing constructible-model interfaces and formalization are by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
-/

namespace ContinuumHypothesis.Constructible.GCHBridge
open _root_.Constructible
open _root_.Constructible.Model
open _root_.Constructible.ContinuumFormula
noncomputable section
open Classical
set_option Elab.async false
set_option maxHeartbeats 1000000

private theorem singleton_native_iff (s x : M) :
    SingletonOf s x ↔ _root_.Constructible.ContinuumFormula.IsSingletonOf E s x := by
  constructor
  · intro h
    exact ⟨(h x).mpr rfl, fun z hz => (h z).mp hz⟩
  · intro h z
    constructor
    · exact h.2 z
    · rintro rfl
      exact h.1

private theorem doubleton_native_iff (s x y : M) :
    DoubletonOf s x y ↔
      _root_.Constructible.ContinuumFormula.IsUnorderedPairOf E s x y := by
  constructor
  · intro h
    exact ⟨(h x).mpr (Or.inl rfl), (h y).mpr (Or.inr rfl),
      fun z hz => (h z).mp hz⟩
  · intro h z
    constructor
    · exact h.2.2 z
    · rintro (rfl | rfl)
      · exact h.1
      · exact h.2.1

private theorem pair_native_iff (p x y : M) :
    PairOf p x y ↔
      _root_.Constructible.ContinuumFormula.IsKuratowskiPairOf E p x y := by
  constructor
  · intro h
    have hs : SingletonOf (pairLCarrier x x) x := by
      intro z
      exact (mem_pairLCarrier_iff x x z).trans
        ⟨fun h => h.elim id id, fun h => Or.inl h⟩
    have hd : DoubletonOf (pairLCarrier x y) x y := by
      intro z
      exact mem_pairLCarrier_iff x y z
    refine ⟨⟨pairLCarrier x x, (h _).mpr (Or.inl hs),
      (singleton_native_iff _ _).mp hs⟩,
      ⟨pairLCarrier x y, (h _).mpr (Or.inr hd),
        (doubleton_native_iff _ _ _).mp hd⟩, ?_⟩
    intro z hz
    rcases (h z).mp hz with hsingle | hdouble
    · exact Or.inl ((singleton_native_iff _ _).mp hsingle)
    · exact Or.inr ((doubleton_native_iff _ _ _).mp hdouble)
  · rintro ⟨⟨s, hs, hsSpec⟩, ⟨d, hd, hdSpec⟩, hsupport⟩
    have hsRaw := (singleton_native_iff s x).mpr hsSpec
    have hdRaw := (doubleton_native_iff d x y).mpr hdSpec
    intro z
    constructor
    · intro hz
      rcases hsupport z hz with hsingle | hdouble
      · exact Or.inl ((singleton_native_iff _ _).mpr hsingle)
      · exact Or.inr ((doubleton_native_iff _ _ _).mpr hdouble)
    · rintro (hz | hz)
      · have heq : z = s := lCarrier_extensionality fun w =>
          (hz w).trans (hsRaw w).symm
        simpa only [heq] using hs
      · have heq : z = d := lCarrier_extensionality fun w =>
          (hz w).trans (hdRaw w).symm
        simpa only [heq] using hd

private theorem pairIn_native_iff (f x y : M) :
    PairIn f x y ↔ _root_.Constructible.ContinuumFormula.GraphValue E f x y := by
  constructor
  · rintro ⟨p, hp, hpf⟩
    exact ⟨p, hpf, (pair_native_iff p x y).mp hp⟩
  · rintro ⟨p, hpf, hp⟩
    exact ⟨p, (pair_native_iff p x y).mpr hp, hpf⟩

private theorem omega_native_iff (w : M) :
    _root_.Constructible.ContinuumFormula.IsOmega E w ↔ Omega w := Iff.rfl

private theorem powerSet_native_iff (p x : M) :
    _root_.Constructible.ContinuumFormula.IsPowerSetOf E x p ↔ PowerSetOf p x := Iff.rfl





private theorem injection_of_native {f x y : M} (h : NativeInjection f x y) :
    Injection f x y := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rcases h.2.1 a ha with ⟨b, hb, hab, _⟩
    exact ⟨b, hb, (pairIn_native_iff f a b).mpr hab⟩
  · intro a b c habc
    rcases habc with ⟨ha, hab, hac⟩
    have hbG := (pairIn_native_iff f a b).mp hab
    have hcG := (pairIn_native_iff f a c).mp hac
    have hb := (h.1.graphValue_mem_lCarrier hbG).2
    have hc := (h.1.graphValue_mem_lCarrier hcG).2
    rcases h.2.1 a ha with ⟨w, _hw, _haw, hunique⟩
    exact (hunique b hb hbG).trans (hunique c hc hcG).symm
  · intro a a' b hab
    rcases hab with ⟨ha, ha', hab, ha'b⟩
    have habG := (pairIn_native_iff f a b).mp hab
    have ha'bG := (pairIn_native_iff f a' b).mp ha'b
    have hb := (h.1.graphValue_mem_lCarrier habG).2
    exact (h.2.2 b hb a ha habG a' ha' ha'bG).symm

private theorem equinumerous_of_native {x y : M} (h : NativeEquinumerous x y) :
    Equinumerous x y := by
  rcases h with ⟨f, hf⟩
  refine ⟨f, injection_of_native hf.toIsInjection, ?_⟩
  intro b hb
  rcases hf.2.2 b hb with ⟨a, ha, hab, _⟩
  exact ⟨a, ha, (pairIn_native_iff f a b).mpr hab⟩



private theorem satisfies_normalizeInjection (f a b x y : M) :
    FOFormula.Satisfies E normalizeInjectionFormula
      (snoc (snoc ![f, a, b] x) y) ↔
        E x a ∧ E y b ∧ GraphValue E f x y := by
  have heq : snoc (snoc ![f, a, b] x) y = ![f, a, b, x, y] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  simp only [normalizeInjectionFormula, FOFormula.Satisfies, satisfies_graphValueAt]
  rfl

private theorem exists_normalizedGraph (f a b : M) :
    ∃ g : M, IsGraphBetween E g a b ∧
      ∀ x y : M, GraphValue E g x y ↔
        E x a ∧ E y b ∧ GraphValue E f x y := by
  let container := _root_.Constructible.ContinuumFormula.unionLCarrier a b
  rcases exists_definableRelationGraph_with_support normalizeInjectionFormula
      ![f, a, b] container with ⟨g, hsupport, hrelation⟩
  have hvalue (x y : M) : GraphValue E g x y ↔
      E x a ∧ E y b ∧ GraphValue E f x y := by
    rw [graphValue_lCarrier_iff_graphRel, hrelation,
      satisfies_normalizeInjection]
    constructor
    · rintro ⟨_, _, h⟩
      exact h
    · rintro ⟨hx, hy, hxy⟩
      exact ⟨(_root_.Constructible.ContinuumFormula.mem_unionLCarrier_iff a b x).mpr (Or.inl hx),
        (_root_.Constructible.ContinuumFormula.mem_unionLCarrier_iff a b y).mpr (Or.inr hy), hx, hy, hxy⟩
  refine ⟨g, ?_, hvalue⟩
  intro p hp
  rcases hsupport p hp with ⟨x, y, _hx, _hy, hpair, hformula⟩
  rcases (satisfies_normalizeInjection f a b x y).mp hformula with ⟨hx, hy, _⟩
  exact ⟨x, hx, y, hy, (isKuratowskiPairOf_lCarrier_iff p x y).mpr hpair⟩

private theorem injects_native_of_platform {a b : M} (h : Injects a b) :
    NativeInjects a b := by
  rcases h with ⟨f, hf⟩
  rcases exists_normalizedGraph f a b with ⟨g, hbetween, hvalue⟩
  refine ⟨g, hbetween, ?_, ?_⟩
  · intro x hx
    rcases hf.1 x hx with ⟨y, hy, hxy⟩
    have hxyN := (pairIn_native_iff f x y).mp hxy
    refine ⟨y, hy, (hvalue x y).mpr ⟨hx, hy, hxyN⟩, ?_⟩
    intro z hz hxz
    have hxzOld := (pairIn_native_iff f x z).mpr ((hvalue x z).mp hxz).2.2
    exact (hf.2.1 x y z ⟨hx, hxy, hxzOld⟩).symm
  · intro y _hy x hx hxy z hz hzy
    have hxyOld := (pairIn_native_iff f x y).mpr ((hvalue x y).mp hxy).2.2
    have hzyOld := (pairIn_native_iff f z y).mpr ((hvalue z y).mp hzy).2.2
    exact hf.2.2 z x y ⟨hz, hx, hzyOld, hxyOld⟩



end
end ContinuumHypothesis.Constructible.GCHBridge


end GCHSource_Work_CUGCH_InternalBridge

/- Source module: Solutions.Work_CUGCH_PowerBridge -/
section GCHSource_Work_CUGCH_PowerBridge
set_option autoImplicit false



/-!
Transport of internal powersets along internally represented injections.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
Uses the constructible separation and graph interfaces of Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
-/

namespace ContinuumHypothesis.Constructible.GCHBridge
open _root_.Constructible
open _root_.Constructible.Model
open _root_.Constructible.ContinuumFormula
noncomputable section
open Classical
set_option Elab.async false
set_option maxHeartbeats 1000000





private theorem satisfies_imageMemberAt {n : Nat} (f u z : Fin n) (s : Tuple M n) :
    FOFormula.Satisfies E (imageMemberAt f u z) s ↔
      ∃ x : M, E x (s u) ∧ GraphValue E (s f) x (s z) := by
  simp only [imageMemberAt, FOFormula.satisfies_boundedEx,
    satisfies_graphValueAt, snoc_castSucc, snoc_last]



private theorem satisfies_imageAt {n : Nat} (f u v : Fin n) (s : Tuple M n) :
    FOFormula.Satisfies E (imageAt f u v) s ↔
      ImageOf (s f) (s u) (s v) := by
  simp only [imageAt, FOFormula.satisfies_all, FOFormula.satisfies_biimp,
    FOFormula.Satisfies, satisfies_imageMemberAt, snoc_last, snoc_castSucc, ImageOf]



private theorem satisfies_imageMemberFormula (f u z : M) :
    FOFormula.Satisfies E imageMemberFormula (snoc ![f, u] z) ↔
      ∃ x : M, E x u ∧ GraphValue E f x z := by
  rw [imageMemberFormula, satisfies_imageMemberAt]
  rfl

private theorem exists_internalImage {f a b u : M}
    (hf : NativeInjection f a b) (hu : IsSubsetOf E u a) :
    ∃ v : M, IsSubsetOf E v b ∧ ImageOf f u v := by
  rcases exists_separationLCarrier imageMemberFormula ![f, u] b with ⟨v, hv⟩
  have hspec (z : M) : E z v ↔ ∃ x : M, E x u ∧ GraphValue E f x z := by
    have hv' : E z v ↔ E z b ∧
        FOFormula.Satisfies E imageMemberFormula (snoc ![f, u] z) := hv z
    rw [hv', satisfies_imageMemberFormula]
    constructor
    · exact And.right
    · intro h
      rcases h with ⟨x, hx, hxz⟩
      exact ⟨(hf.1.graphValue_mem_lCarrier hxz).2, x, hx, hxz⟩
  refine ⟨v, ?_, hspec⟩
  intro z hz
  rcases (hspec z).mp hz with ⟨x, _hx, hxz⟩
  exact (hf.1.graphValue_mem_lCarrier hxz).2

private theorem imageOf_unique {f u v w : M}
    (hv : ImageOf f u v) (hw : ImageOf f u w) : v = w :=
  lCarrier_extensionality fun z => (hv z).trans (hw z).symm

private theorem imageOf_injective {f a b u v w : M}
    (hf : NativeInjection f a b)
    (hu : IsSubsetOf E u a) (hv : IsSubsetOf E v a)
    (huw : ImageOf f u w) (hvw : ImageOf f v w) : u = v := by
  have hsub {r s : M} (hr : IsSubsetOf E r a)
      (hrw : ImageOf f r w) (hsw : ImageOf f s w) : IsSubsetOf E r s := by
    intro x hx
    rcases hf.2.1 x (hr x hx) with ⟨y, hy, hxy, _⟩
    have hyw : E y w := (hrw y).mpr ⟨x, hx, hxy⟩
    rcases (hsw y).mp hyw with ⟨z, hz, hzy⟩
    have hza := (hf.1.graphValue_mem_lCarrier hzy).1
    have hzx : z = x := hf.2.2 y hy x (hr x hx) hxy z hza hzy
    exact hzx ▸ hz
  exact lCarrier_extensionality fun x =>
    ⟨fun hx => hsub hu huw hvw x hx, fun hx => hsub hv hvw huw x hx⟩



private theorem satisfies_powerImageGraphFormula (f pa pb u v : M) :
    FOFormula.Satisfies E powerImageGraphFormula
        (snoc (snoc ![f, pa, pb] u) v) ↔
      E u pa ∧ E v pb ∧ ImageOf f u v := by
  have heq : snoc (snoc ![f, pa, pb] u) v = ![f, pa, pb, u, v] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  simp only [powerImageGraphFormula, FOFormula.Satisfies, satisfies_imageAt]
  rfl

private theorem exists_powerImageGraph (f pa pb : M) :
    ∃ g : M, IsGraphBetween E g pa pb ∧
      ∀ u v : M, GraphValue E g u v ↔ E u pa ∧ E v pb ∧ ImageOf f u v := by
  let container := _root_.Constructible.ContinuumFormula.unionLCarrier pa pb
  rcases exists_definableRelationGraph_with_support powerImageGraphFormula
      ![f, pa, pb] container with ⟨g, hsupport, hrelation⟩
  have hvalue (u v : M) : GraphValue E g u v ↔
      E u pa ∧ E v pb ∧ ImageOf f u v := by
    rw [graphValue_lCarrier_iff_graphRel, hrelation, satisfies_powerImageGraphFormula]
    constructor
    · rintro ⟨_, _, h⟩
      exact h
    · rintro ⟨hu, hv, himage⟩
      exact ⟨(_root_.Constructible.ContinuumFormula.mem_unionLCarrier_iff pa pb u).mpr (Or.inl hu),
        (_root_.Constructible.ContinuumFormula.mem_unionLCarrier_iff pa pb v).mpr (Or.inr hv), hu, hv, himage⟩
  refine ⟨g, ?_, hvalue⟩
  intro p hp
  rcases hsupport p hp with ⟨u, v, _, _, hpair, hformula⟩
  rcases (satisfies_powerImageGraphFormula f pa pb u v).mp hformula with ⟨hu, hv, _⟩
  exact ⟨u, hu, v, hv, (isKuratowskiPairOf_lCarrier_iff p u v).mpr hpair⟩

private theorem powerSet_injects_of_injects {a b pa pb : M}
    (hab : NativeInjects a b) (hpa : IsPowerSetOf E a pa)
    (hpb : IsPowerSetOf E b pb) : NativeInjects pa pb := by
  rcases hab with ⟨f, hf⟩
  rcases exists_powerImageGraph f pa pb with ⟨g, hbetween, hvalue⟩
  refine ⟨g, hbetween, ?_, ?_⟩
  · intro u hu
    have hua : IsSubsetOf E u a := (hpa u).mp hu
    rcases exists_internalImage hf hua with ⟨v, hvb, huv⟩
    have hv : E v pb := (hpb v).mpr hvb
    refine ⟨v, hv, (hvalue u v).mpr ⟨hu, hv, huv⟩, ?_⟩
    intro w _hw huw
    exact imageOf_unique ((hvalue u w).mp huw).2.2 huv
  · intro v _hv u hu huv w hw hwv
    exact imageOf_injective hf ((hpa w).mp hw) ((hpa u).mp hu)
      ((hvalue w v).mp hwv).2.2 ((hvalue u v).mp huv).2.2

private theorem powerSet_equinumerous_of_equinumerous {a b pa pb : M}
    (hab : NativeEquinumerous a b) (hpa : IsPowerSetOf E a pa)
    (hpb : IsPowerSetOf E b pb) : NativeEquinumerous pa pb := by
  apply injects_antisymm_lCarrier
  · exact powerSet_injects_of_injects hab.injects hpa hpb
  · exact powerSet_injects_of_injects hab.symm_lCarrier.injects hpb hpa

end
end ContinuumHypothesis.Constructible.GCHBridge


end GCHSource_Work_CUGCH_PowerBridge

/- Source module: Solutions.Work_CUGCH_GapBridge -/
section GCHSource_Work_CUGCH_GapBridge
set_option autoImplicit false




/-!
Successor-cardinal GCH implies the gap formulation for arbitrary infinite sets.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
The internal cardinal and graph infrastructure is by Zike Liu, Apache-2.0,
commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
-/

namespace ContinuumHypothesis.Constructible.GCHBridge
open _root_.Constructible
open _root_.Constructible.Model
open _root_.Constructible.ContinuumFormula
noncomputable section
open Classical
set_option Elab.async false
set_option maxHeartbeats 1000000

private theorem ordinal_trichotomy {a b : M}
    (ha : IsVonNeumannOrdinal E a) (hb : IsVonNeumannOrdinal E b) :
    E a b ∨ a = b ∨ E b a := by
  rcases exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal a ha with ⟨alpha, rfl⟩
  rcases exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal b hb with ⟨beta, rfl⟩
  rcases lt_trichotomy alpha beta with h | h | h
  · exact Or.inl ((ordinalLCarrier_mem_ordinalLCarrier_iff beta alpha).mpr h)
  · exact Or.inr (Or.inl (congrArg ordinalLCarrier h))
  · exact Or.inr (Or.inr ((ordinalLCarrier_mem_ordinalLCarrier_iff alpha beta).mpr h))

private theorem cardinal_compare_of_injects {a b : M}
    (ha : IsCardinal E a) (hb : IsCardinal E b) (hab : NativeInjects a b) :
    a = b ∨ E a b := by
  rcases ordinal_trichotomy ha.1 hb.1 with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact False.elim ((ha.not_injects_of_mem_lCarrier h
      internalInjectionAntisymm_lCarrier) hab)

private theorem omega_subset_of_infinite_representative {s kappa omega : M}
    (hs : ¬FiniteSet s) (hkappa : IsCardinal E kappa)
    (hsKappa : NativeEquinumerous s kappa)
    (homega : IsOmega E omega) (homegaCard : IsCardinal E omega) :
    IsSubsetOf E omega kappa := by
  rcases ordinal_trichotomy homegaCard.1 hkappa.1 with h | h | h
  · exact fun z hz => hkappa.1.1 omega h z hz
  · subst kappa
    exact fun _ hz => hz
  · exact False.elim (hs ⟨omega, (omega_native_iff omega).mp homega,
      kappa, h, equinumerous_of_native hsKappa.symm_lCarrier⟩)

private theorem gapGCH_of_native
    (hrepresentatives : ∀ a : M, ∃ cardinal : M,
      IsCardinal E cardinal ∧ NativeEquinumerous a cardinal)
    (hgch : ModelsGCH (A := M) E) : GapGCH := by
  rcases hgch with ⟨omega, homega, homegaCard, hcardinalGCH⟩
  intro s hs p hp t ht
  rcases hrepresentatives s with ⟨kappa, hkappa, hsKappa⟩
  rcases hrepresentatives t with ⟨lambda, hlambda, htLambda⟩
  have homegaKappa := omega_subset_of_infinite_representative
    hs hkappa hsKappa homega homegaCard
  rcases hcardinalGCH kappa ⟨hkappa, homegaKappa⟩ with
    ⟨next, q, hnext, hq, hqNext⟩
  have hpNative : IsPowerSetOf E s p := (powerSet_native_iff p s).mpr hp
  have hpQ : NativeEquinumerous p q :=
    powerSet_equinumerous_of_equinumerous hsKappa hpNative hq
  have hpNext : NativeEquinumerous p next := hpQ.trans_lCarrier hqNext
  have hsT : NativeInjects s t := injects_native_of_platform ht.1
  have htP : NativeInjects t p := injects_native_of_platform ht.2
  have hkappaLambda : NativeInjects kappa lambda :=
    hsKappa.symm_lCarrier.injects.trans_lCarrier
      (hsT.trans_lCarrier htLambda.injects)
  have hlambdaNext : NativeInjects lambda next :=
    htLambda.symm_lCarrier.injects.trans_lCarrier
      (htP.trans_lCarrier hpNext.injects)
  rcases cardinal_compare_of_injects hkappa hlambda hkappaLambda with h | hkl
  · have htS : NativeEquinumerous t s := by
      rw [← h] at htLambda
      exact htLambda.trans_lCarrier hsKappa.symm_lCarrier
    exact Or.inl (equinumerous_of_native htS)
  · rcases cardinal_compare_of_injects hlambda hnext.2.1 hlambdaNext with h | hln
    · have htP' : NativeEquinumerous t p := by
        rw [h] at htLambda
        exact htLambda.trans_lCarrier hpNext.symm_lCarrier
      exact Or.inr (equinumerous_of_native htP')
    · exact False.elim (hnext.2.2.2 ⟨lambda, hlambda, hkl, hln⟩)

end
end ContinuumHypothesis.Constructible.GCHBridge


end GCHSource_Work_CUGCH_GapBridge

/- Source module: Solutions.Work_CUGCH_Final -/
section GCHSource_Work_CUGCH_Final
set_option autoImplicit false



/-!
GCH for the platform's unchanged constructible carrier and sentence.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
The constructible-universe proof reused here is by Zike Liu (Apache-2.0),
commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Mathematical references:
Andrew Marks, Set Theory, Lemma 21.3 and Corollary 21.4; Kurt Gödel (1938, 1940).
-/

open FirstOrder FirstOrder.Language
open ContinuumHypothesis ContinuumHypothesis.Constructible
open ContinuumHypothesis.Constructible.GCHBridge

private theorem gchFinalProof14 : Carrier ⊨ gchSentence := by
  apply transport_gch
  apply sentence_of_gapGCH
  exact gapGCH_of_native
    _root_.Constructible.ContinuumFormula.hasInternalCardinalRepresentatives_lCarrier
    _root_.Constructible.ContinuumFormula.modelsGCH_lCarrier




end GCHSource_Work_CUGCH_Final


theorem solution : @FirstOrder.Language.Sentence.Realize.{0, 0, 1} ContinuumHypothesis.setLang ContinuumHypothesis.Constructible.Carrier
  ContinuumHypothesis.Constructible.carrierStructure ContinuumHypothesis.gchSentence :=
  @gchFinalProof14
