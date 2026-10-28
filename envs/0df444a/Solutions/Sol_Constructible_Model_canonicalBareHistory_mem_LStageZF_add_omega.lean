-- Prove2me | solution 1 for Constructible.Model.canonicalBareHistory_mem_LStageZF_add_omega
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-25T23:49:31.501875+00:00
-- url     : https://prove2.me/submissions/0d664002-1283-4fe9-a7d2-649f840c58ad

import Definitions.Def_CH_ConstructibleGCH_Library04
import Theorems.Thm_Constructible_Godel_RudimentaryTerm_bareGodelDefOutputCorrectIn_LStageZF_of_omega_lt
import Theorems.Thm_Constructible_Model_canonicalBareHistory_mem_LStageZF_add_omega_of_evaluators

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

/-- Pairing raises an explicit stage bound by one successor. -/
private theorem pair_mem_LStageZF_succ {alpha : Ordinal.{u}}
    {x y : ZFSet.{u}} (hx : x ∈ LStageZF alpha)
    (hy : y ∈ LStageZF alpha) :
    ({x, y} : ZFSet.{u}) ∈ LStageZF (Order.succ alpha) := by
  rw [LStageZF_succ]
  exact pair_mem_DefZF hx hy



/-- A Kuratowski ordered pair raises an explicit stage bound by two
successors. -/
private theorem orderedPair_mem_LStageZF_succ_succ {alpha : Ordinal.{u}}
    {x y : ZFSet.{u}} (hx : x ∈ LStageZF alpha)
    (hy : y ∈ LStageZF alpha) :
    ZFSet.pair x y ∈
      LStageZF (Order.succ (Order.succ alpha)) := by
  change ({{x}, {x, y}} : ZFSet.{u}) ∈
    LStageZF (Order.succ (Order.succ alpha))
  apply pair_mem_LStageZF_succ
  · simpa using pair_mem_LStageZF_succ hx hx
  · exact pair_mem_LStageZF_succ hx hy

/-- A right-associated Kuratowski triple raises an explicit stage bound by
four successors. -/
private theorem triple_mem_LStageZF_four_succ {alpha : Ordinal.{u}}
    {x y z : ZFSet.{u}} (hx : x ∈ LStageZF alpha)
    (hy : y ∈ LStageZF alpha) (hz : z ∈ LStageZF alpha) :
    Godel.triple x y z ∈
      LStageZF
        (Order.succ (Order.succ (Order.succ (Order.succ alpha)))) := by
  change ZFSet.pair x (ZFSet.pair y z) ∈
    LStageZF
      (Order.succ (Order.succ (Order.succ (Order.succ alpha))))
  apply orderedPair_mem_LStageZF_succ_succ
  · exact LStageZF_mono
      ((Order.le_succ alpha).trans (Order.le_succ (Order.succ alpha))) hx
  · exact orderedPair_mem_LStageZF_succ_succ hy hz

/-- If a Kuratowski pair belongs to a transitive level, both coordinates
belong to that level. -/
private theorem orderedPair_components_mem_LStageZF {alpha : Ordinal.{u}}
    {x y : ZFSet.{u}} (hpair : ZFSet.pair x y ∈ LStageZF alpha) :
    x ∈ LStageZF alpha ∧ y ∈ LStageZF alpha := by
  have htrans := LStageZF_isTransitive alpha
  have hxSingleton : ({x} : ZFSet.{u}) ∈ LStageZF alpha :=
    htrans.mem_trans (by simp [ZFSet.pair]) hpair
  have hxyPair : ({x, y} : ZFSet.{u}) ∈ LStageZF alpha :=
    htrans.mem_trans (by simp [ZFSet.pair]) hpair
  exact
    ⟨htrans.mem_trans (by simp) hxSingleton,
      htrans.mem_trans (by simp) hxyPair⟩

/-- A fiber of a relation whose relation and selected coordinate lie in one
level belongs to the next level. -/
private theorem Godel.fiber_mem_LStageZF_succ {alpha : Ordinal.{u}}
    {relation index : ZFSet.{u}}
    (hrelation : relation ∈ LStageZF alpha)
    (hindex : index ∈ LStageZF alpha) :
    Godel.fiber relation index ∈ LStageZF (Order.succ alpha) := by
  rw [LStageZF_succ]
  apply (Godel.fiberDelta0Section hrelation hindex).mem_DefZF
    (LStageZF_isTransitive alpha)
  intro value hvalue
  exact (orderedPair_components_mem_LStageZF
    ((LStageZF_isTransitive alpha).mem_trans
      (Godel.mem_fiber_iff.mp hvalue) hrelation)).1

/-! ## Local closure under the rudimentary basis -/

/-- Every Jensen--Devlin primitive operation preserves an arbitrary nonzero
limit level.  The proof keeps an explicit common input stage and uses at most
five further successor stages; no appeal to closure of the proper class `L`
occurs. -/
private theorem Godel.op_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (i : Fin 9) {x y : ZFSet.{u}}
    (hx : x ∈ LStageZF theta) (hy : y ∈ LStageZF theta) :
    Godel.op i x y ∈ LStageZF theta := by
  rcases (mem_LStageZF_limit_iff htheta).mp hx with
    ⟨alpha, halpha, hxAlpha⟩
  rcases (mem_LStageZF_limit_iff htheta).mp hy with
    ⟨beta, hbeta, hyBeta⟩
  let gamma0 := max alpha beta
  let gamma1 := Order.succ gamma0
  let gamma2 := Order.succ gamma1
  let gamma3 := Order.succ gamma2
  let gamma4 := Order.succ gamma3
  let gamma5 := Order.succ gamma4
  have hgamma0 : gamma0 < theta := max_lt halpha hbeta
  have hgamma1 : gamma1 < theta := htheta.succ_lt hgamma0
  have hgamma2 : gamma2 < theta := htheta.succ_lt hgamma1
  have hgamma3 : gamma3 < theta := htheta.succ_lt hgamma2
  have hgamma4 : gamma4 < theta := htheta.succ_lt hgamma3
  have hgamma5 : gamma5 < theta := htheta.succ_lt hgamma4
  have hx0 : x ∈ LStageZF gamma0 :=
    LStageZF_mono (le_max_left alpha beta) hxAlpha
  have hy0 : y ∈ LStageZF gamma0 :=
    LStageZF_mono (le_max_right alpha beta) hyBeta
  have lift0 : ∀ {z : ZFSet.{u}}, z ∈ LStageZF gamma0 →
      z ∈ LStageZF gamma4 := by
    intro z hz
    exact LStageZF_subset_succ gamma3
      (LStageZF_subset_succ gamma2
        (LStageZF_subset_succ gamma1
          (LStageZF_subset_succ gamma0 hz)))
  have lift1 : ∀ {z : ZFSet.{u}}, z ∈ LStageZF gamma1 →
      z ∈ LStageZF gamma4 := by
    intro z hz
    exact LStageZF_subset_succ gamma3
      (LStageZF_subset_succ gamma2
        (LStageZF_subset_succ gamma1 hz))
  have lift2 : ∀ {z : ZFSet.{u}}, z ∈ LStageZF gamma2 →
      z ∈ LStageZF gamma4 := by
    intro z hz
    exact LStageZF_subset_succ gamma3
      (LStageZF_subset_succ gamma2 hz)
  have htrans0 := LStageZF_isTransitive gamma0
  have hsub : Godel.op i x y ⊆ LStageZF gamma4 := by
    intro q hq
    fin_cases i
    · rcases Godel.mem_F0_iff.mp hq with rfl | rfl
      · exact lift0 hx0
      · exact lift0 hy0
    · exact lift0 (htrans0.mem_trans (Godel.mem_F1_iff.mp hq).1 hx0)
    · rcases Godel.mem_F2_iff.mp hq with ⟨a, ha, b, hb, rfl⟩
      apply lift2
      exact orderedPair_mem_LStageZF_succ_succ
        (htrans0.mem_trans ha hx0) (htrans0.mem_trans hb hy0)
    · rcases Godel.mem_F3_iff.mp hq with
        ⟨a, z, b, hz, hab, rfl⟩
      have hab0 : ZFSet.pair a b ∈ LStageZF gamma0 :=
        htrans0.mem_trans hab hy0
      have hcomponents := orderedPair_components_mem_LStageZF hab0
      exact triple_mem_LStageZF_four_succ hcomponents.1
        (htrans0.mem_trans hz hx0) hcomponents.2
    · rcases Godel.mem_F4_iff.mp hq with
        ⟨a, b, z, hz, hab, rfl⟩
      have hab0 : ZFSet.pair a b ∈ LStageZF gamma0 :=
        htrans0.mem_trans hab hy0
      have hcomponents := orderedPair_components_mem_LStageZF hab0
      exact triple_mem_LStageZF_four_succ hcomponents.1
        hcomponents.2 (htrans0.mem_trans hz hx0)
    · rcases (Godel.mem_F5_iff (x := x) (y := y) (z := q)).mp hq with
        ⟨member, hmember, hqMember⟩
      exact lift0
        (htrans0.mem_trans hqMember
          (htrans0.mem_trans hmember hx0))
    · rcases (Godel.mem_F6_iff (x := x) (y := y) (z := q)).mp hq with
        ⟨left, hpair⟩
      exact lift0
        (orderedPair_components_mem_LStageZF
          (htrans0.mem_trans hpair hx0)).2
    · rcases (Godel.mem_F7_iff (x := x) (y := y) (q := q)).mp hq with
        ⟨a, ha, b, hb, rfl, _hab⟩
      apply lift2
      exact orderedPair_mem_LStageZF_succ_succ
        (htrans0.mem_trans ha hx0) (htrans0.mem_trans hb hx0)
    · rcases Godel.mem_F8_iff.mp hq with ⟨z, hz, rfl⟩
      apply lift1
      exact Godel.fiber_mem_LStageZF_succ hx0
        (htrans0.mem_trans hz hy0)
  have hx4 : x ∈ LStageZF gamma4 := lift0 hx0
  have hy4 : y ∈ LStageZF gamma4 := lift0 hy0
  have hop5 : Godel.op i x y ∈ LStageZF gamma5 := by
    change Godel.op i x y ∈ LStageZF (Order.succ gamma4)
    rw [LStageZF_succ]
    exact Godel.op_mem_DefZF_of_subset
      (LStageZF_isTransitive gamma4) hx4 hy4 hsub
  exact LStageZF_mono hgamma5.le hop5





















/-- The earlier constructible level itself belongs to a later limit level. -/
private theorem LStageZF_mem_LStageZF_of_lt_isSuccLimit
    {alpha theta : Ordinal.{u}} (_htheta : Order.IsSuccLimit theta)
    (halpha : alpha < theta) :
    LStageZF alpha ∈ LStageZF theta :=
  LStageZF_mem_of_lt halpha

/-! ## Local bounds for finite sequence and program codes -/













namespace Godel.RudimentaryTerm













/-! ## Local bounds for successful stack executions -/

/-- One successful local machine step preserves the property that every
stack entry belongs to the prescribed nonzero limit level. -/
private theorem runStackToken_entries_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {U : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF theta)
    (hstep : runStackToken (rudimentaryGenerator U) token input =
      some output) :
    ∀ x ∈ output, x ∈ LStageZF theta := by
  cases token with
  | inl generator =>
      simp only [runStackToken, Option.some.injEq] at hstep
      subst output
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact rudimentaryGenerator_mem_LStageZF_of_isSuccLimit
          htheta hU generator
      · exact hinput x hx
  | inr operation =>
      cases input with
      | nil => simp [runStackToken] at hstep
      | cons right tail =>
          cases tail with
          | nil => simp [runStackToken] at hstep
          | cons left rest =>
              simp only [runStackToken, Option.some.injEq] at hstep
              subst output
              intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact Godel.op_mem_LStageZF_of_isSuccLimit
                  htheta operation
                  (hinput left (by simp)) (hinput right (by simp))
              · exact hinput x (by simp [hx])

/-- Every state in a successful finite trace remains entrywise inside the
prescribed nonzero limit level. -/
private theorem ExecutionTrace.entries_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {U : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    {program : List (StackToken (Option (Constructible.ZFCarrier U)))}
    {states : List (List ZFSet.{u})}
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    {input : List ZFSet.{u}} (hhead : states.head? = some input)
    (hinput : ∀ x ∈ input, x ∈ LStageZF theta) :
    ∀ stack ∈ states, ∀ x ∈ stack, x ∈ LStageZF theta := by
  induction htrace generalizing input with
  | nil stack =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst input
      simpa using hinput
  | @cons token program input next tailStates hstep htail ih =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst input
      have hnext : ∀ x ∈ next, x ∈ LStageZF theta :=
        runStackToken_entries_mem_LStageZF_of_isSuccLimit
          htheta hU token _ _ hinput hstep
      intro stack hstack
      simp only [List.mem_cons] at hstack
      rcases hstack with rfl | hstack
      · exact hinput
      · exact ih rfl hnext stack
          (by simpa only [List.mem_cons] using hstack)





end Godel.RudimentaryTerm

namespace Model











end Model

end ZFC

end Constructible

end
end GCHSource_Work_CUGCH_BareStageHistoryBounds

/- Source module: Solutions.Work_CUGCH_BareGodelDefAbsolute -/
section GCHSource_Work_CUGCH_BareGodelDefAbsolute
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Local correctness of the Goedel-definability evaluator

This file proves that the first-order formula used at a successor step of a
bare stage history has its intended ambient meaning when interpreted in a
constructible limit level above `omega`.

The proof deliberately separates soundness from completeness.  Soundness
only projects a restricted finite evaluation certificate to the ambient
universe.  Completeness constructs the canonical program and execution-trace
codes and checks, using the local bounds from `BareStageHistoryBounds`, that
every unbounded witness belongs to the prescribed level.
-/

section

open Set

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF
open Constructible.FiniteSequenceZF







private theorem carrierVal_eq {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (Carrier a) n) :
    Delta0Formula.val s = (fun i => (s i).1) := by
  rfl

private theorem carrierVal_snoc4 {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (Carrier a) n) (w x y z : Carrier a) :
    Delta0Formula.val (snoc (snoc (snoc (snoc s w) x) y) z) =
      snoc (snoc (snoc (snoc (fun i => (s i).1) w.1) x.1) y.1) z.1 := by
  rw [Delta0Formula.val_snoc, Delta0Formula.val_snoc,
    Delta0Formula.val_snoc, Delta0Formula.val_snoc, carrierVal_eq]

private theorem carrierVal_snoc5 {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (Carrier a) n) (v w x y z : Carrier a) :
    Delta0Formula.val
        (snoc (snoc (snoc (snoc (snoc s v) w) x) y) z) =
      snoc (snoc (snoc (snoc (snoc (fun i => (s i).1) v.1)
        w.1) x.1) y.1) z.1 := by
  rw [Delta0Formula.val_snoc, Delta0Formula.val_snoc,
    Delta0Formula.val_snoc, Delta0Formula.val_snoc,
    Delta0Formula.val_snoc, carrierVal_eq]











private theorem sequenceValidity_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (omega sequence : Carrier a)
    (hvalid : FOFormula.Satisfies (zfCarrierMem a)
      sequenceValidityFormula ![omega, sequence]) :
    FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
      ![omega.1, sequence.1] := by
  rw [satisfies_sequenceValidityFormula_carrier ha] at hvalid
  rw [satisfies_sequenceValidityFormula]
  rcases hvalid with
    ⟨length, graph, hsequence, hlength, hfunctional⟩
  refine ⟨length.1, graph.1, hsequence, hlength, ?_⟩
  intro index hindex
  let indexA : Carrier a :=
    ⟨index, ha.mem_trans hindex length.2⟩
  rcases hfunctional indexA hindex with
    ⟨value, hvalue, hunique⟩
  refine ⟨value.1, hvalue, ?_⟩
  intro other hother
  have hpairA : ZFSet.pair other index ∈ a :=
    ha.mem_trans hother graph.2
  have hsingletonA : ({other} : ZFSet.{u}) ∈ a :=
    ha.mem_trans (by simp [ZFSet.pair]) hpairA
  have hotherA : other ∈ a :=
    ha.mem_trans (by simp) hsingletonA
  let otherA : Carrier a := ⟨other, hotherA⟩
  exact hunique otherA hother

private theorem sequenceValidityAssignment_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 2)
    (hvalid : FOFormula.Satisfies (zfCarrierMem a)
      sequenceValidityFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
      (fun i => (s i).1) := by
  have hstandard : FOFormula.Satisfies (zfCarrierMem a)
      sequenceValidityFormula ![s 0, s 1] := by
    apply (satisfies_congr_assignment (zfCarrierMem a)
      sequenceValidityFormula s ![s 0, s 1] ?_).mp hvalid
    intro i
    fin_cases i <;> rfl
  have hambient := sequenceValidity_carrier_to_ambient ha
    (s 0) (s 1) hstandard
  apply (satisfies_congr_assignment Delta0Formula.ZFMem
    sequenceValidityFormula ![(s 0).1, (s 1).1]
      (fun i => (s i).1) ?_).mp hambient
  intro i
  fin_cases i <;> rfl

private theorem hasLength_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 2)
    (hlength : FOFormula.Satisfies (zfCarrierMem a)
      hasLengthFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
      (fun i => (s i).1) := by
  simp only [hasLengthFormula, FOFormula.Satisfies] at hlength ⊢
  rcases hlength with ⟨graph, hgraph⟩
  refine ⟨graph.1, ?_⟩
  have hraw := (Delta0Formula.satisfies_toFO_absolute ha
    _ (snoc s graph)).mp hgraph
  change FOFormula.Satisfies (fun x y : ZFSet.{u} => x ∈ y)
    (Delta0Formula.kuratowskiPairEqAt 0 1 2).toFO
    (Delta0Formula.val (snoc s graph)) at hraw
  change FOFormula.Satisfies (fun x y : ZFSet.{u} => x ∈ y)
    (Delta0Formula.kuratowskiPairEqAt 0 1 2).toFO
    (snoc (fun i => (s i).1) graph.1)
  rw [Delta0Formula.val_snoc] at hraw
  have hval : Delta0Formula.val s = (fun i => (s i).1) := rfl
  rw [hval] at hraw
  exact hraw

private theorem variableStackStep_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 16)
    (hstep : FOFormula.Satisfies (zfCarrierMem a)
      variableStackStepFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem variableStackStepFormula
      (fun i => (s i).1) := by
  simp only [variableStackStepFormula, FOFormula.Satisfies,
    FOFormula.satisfies_disj] at hstep ⊢
  rcases hstep with ⟨generator, htoken, hgenerator, houtput⟩
  refine ⟨generator.1, ?_, ?_, ?_⟩
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha
      _ (snoc s generator)).mp htoken
    rw [Delta0Formula.val_snoc] at hraw
    exact hraw
  · rcases hgenerator with hgenerator | hgenerator
    · exact Or.inl (congrArg Subtype.val hgenerator)
    · exact Or.inr hgenerator
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha
      _ (snoc s generator)).mp houtput
    rw [Delta0Formula.val_snoc] at hraw
    exact hraw

set_option maxHeartbeats 1200000 in
private theorem operationStackStep_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive) (operation : Fin 9)
    (s : Tuple (Carrier a) 16)
    (hstep : FOFormula.Satisfies (zfCarrierMem a)
      (operationStackStepFormula operation) s) :
    FOFormula.Satisfies Delta0Formula.ZFMem
      (operationStackStepFormula operation) (fun i => (s i).1) := by
  simp only [operationStackStepFormula, operationStackStepBody,
    FOFormula.Satisfies, FOFormula.satisfies_rename] at hstep ⊢
  rcases hstep with
    ⟨right, left, rest, result, inner,
      htoken, hinput, hinner, houtput, hop⟩
  refine ⟨right.1, left.1, rest.1, result.1, inner.1,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _
      (snoc (snoc (snoc (snoc (snoc s right) left) rest)
        result) inner)).mp htoken
    rw [carrierVal_snoc5] at hraw
    exact hraw
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _
      (snoc (snoc (snoc (snoc (snoc s right) left) rest)
        result) inner)).mp hinput
    rw [carrierVal_snoc5] at hraw
    exact hraw
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _
      (snoc (snoc (snoc (snoc (snoc s right) left) rest)
        result) inner)).mp hinner
    rw [carrierVal_snoc5] at hraw
    exact hraw
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _
      (snoc (snoc (snoc (snoc (snoc s right) left) rest)
        result) inner)).mp houtput
    rw [carrierVal_snoc5] at hraw
    exact hraw
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _ _).mp hop
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      (opGraphFormula operation).toFO _ _ ?_).mp hraw
    intro j
    exact congrFun (carrierVal_snoc5 s right left rest result inner)
      (stackStepOpGraphRename j)

private theorem stackStep_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 16)
    (hstep : FOFormula.Satisfies (zfCarrierMem a)
      stackStepFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
      (fun i => (s i).1) := by
  simp only [stackStepFormula, anyOperationStackStepFormula,
    FOFormula.satisfies_disj] at hstep ⊢
  rcases hstep with hvariable | hoperation
  · exact Or.inl (variableStackStep_carrier_to_ambient ha s hvariable)
  · right
    rcases hoperation with h | h | h | h | h | h | h | h | h
    · exact Or.inl (operationStackStep_carrier_to_ambient ha 0 s h)
    · exact Or.inr (Or.inl
        (operationStackStep_carrier_to_ambient ha 1 s h))
    · exact Or.inr (Or.inr (Or.inl
        (operationStackStep_carrier_to_ambient ha 2 s h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (operationStackStep_carrier_to_ambient ha 3 s h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (operationStackStep_carrier_to_ambient ha 4 s h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (operationStackStep_carrier_to_ambient ha 5 s h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (operationStackStep_carrier_to_ambient ha 6 s h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl
          (operationStackStep_carrier_to_ambient ha 7 s h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr
          (operationStackStep_carrier_to_ambient ha 8 s h))))))))

set_option maxHeartbeats 1200000 in
private theorem traceStep_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 16)
    (hstep : FOFormula.Satisfies (zfCarrierMem a)
      traceStepFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem traceStepFormula
      (fun i => (s i).1) := by
  simp only [traceStepFormula, traceStepBody, FOFormula.Satisfies,
    FOFormula.satisfies_rename] at hstep ⊢
  rcases hstep with
    ⟨token, input, succ, output,
      htoken, hinput, hsucc, houtput, hstack⟩
  refine ⟨token.1, input.1, succ.1, output.1,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _ _).mp htoken
    change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula _ at hraw
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      valueAtFormula _ _ ?_).mp hraw
    intro i
    exact congrFun (carrierVal_snoc4 s token input succ output)
      (traceStepProgramValueRename i)
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _ _).mp hinput
    change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula _ at hraw
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      valueAtFormula _ _ ?_).mp hraw
    intro i
    exact congrFun (carrierVal_snoc4 s token input succ output)
      (traceStepInputValueRename i)
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _ _).mp hsucc
    change FOFormula.Satisfies Delta0Formula.ZFMem
      (Delta0Formula.successorFOAt (18 : Fin 20) (15 : Fin 20)) _ at hraw
    rw [carrierVal_snoc4] at hraw
    exact hraw
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _ _).mp houtput
    change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula _ at hraw
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      valueAtFormula _ _ ?_).mp hraw
    intro i
    exact congrFun (carrierVal_snoc4 s token input succ output)
      (traceStepOutputValueRename i)
  · have hraw := stackStep_carrier_to_ambient ha _ hstack
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      stackStepFormula _ _ ?_).mp hraw
    intro i
    exact congrFun (carrierVal_snoc4 s token input succ output)
      (traceStepStackStepRename i)

private theorem stackProgramEvalCore_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 20)
    (hcore : FOFormula.Satisfies (zfCarrierMem a)
      stackProgramEvalCore s) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalCore
      (fun i => (s i).1) := by
  rw [stackProgramEvalCore] at hcore ⊢
  rcases hcore with
    ⟨hprogramLength, htraceLength, hsuccessor,
      hinitial, hfinal, hfinalStack, hsteps⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [FOFormula.satisfies_rename] at hprogramLength ⊢
    exact hasLength_carrier_to_ambient ha _ hprogramLength
  · rw [FOFormula.satisfies_rename] at htraceLength ⊢
    exact hasLength_carrier_to_ambient ha _ htraceLength
  · exact (Delta0Formula.satisfies_toFO_absolute ha _ s).mp hsuccessor
  · rw [FOFormula.satisfies_rename] at hinitial ⊢
    exact (Delta0Formula.satisfies_toFO_absolute ha _ _).mp hinitial
  · rw [FOFormula.satisfies_rename] at hfinal ⊢
    exact (Delta0Formula.satisfies_toFO_absolute ha _ _).mp hfinal
  · exact (Delta0Formula.satisfies_toFO_absolute ha _ s).mp hfinalStack
  · rw [FOFormula.satisfies_boundedAll] at hsteps ⊢
    intro index hindex
    let indexA : Carrier a :=
      ⟨index, ha.mem_trans hindex (s 17).2⟩
    have hrestricted := hsteps indexA hindex
    rw [FOFormula.satisfies_rename] at hrestricted ⊢
    have hambient := traceStep_carrier_to_ambient ha _ hrestricted
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      traceStepFormula _ _ ?_).mp hambient
    intro i
    simp only [carrierVal_snoc_apply, indexA]

private theorem stackProgramEval_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 16)
    (heval : FOFormula.Satisfies (zfCarrierMem a)
      stackProgramEvalFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
      (fun i => (s i).1) := by
  rw [stackProgramEvalFormula] at heval ⊢
  rcases heval with
    ⟨hprogramValid, trace, htraceValid,
      programLength, traceLength, finalStack, hcore⟩
  refine ⟨?_, trace.1, ?_, programLength.1, traceLength.1,
    finalStack.1, ?_⟩
  · rw [FOFormula.satisfies_rename] at hprogramValid ⊢
    exact sequenceValidityAssignment_carrier_to_ambient
      ha _ hprogramValid
  · rw [FOFormula.satisfies_rename] at htraceValid ⊢
    let traceValidityAssignment : Tuple (Carrier a) 2 :=
      fun i => snoc s trace (evalTraceValidityRename i)
    have htraceRestricted :
        FOFormula.Satisfies (zfCarrierMem a) sequenceValidityFormula
          traceValidityAssignment := htraceValid
    have htraceAmbient := sequenceValidityAssignment_carrier_to_ambient
      ha traceValidityAssignment htraceRestricted
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      sequenceValidityFormula _ _ ?_).mp htraceAmbient
    intro i
    simp only [traceValidityAssignment, carrierVal_snoc_apply]
  · let coreAssignment : Tuple (Carrier a) 20 :=
      snoc (snoc (snoc (snoc s trace) programLength)
        traceLength) finalStack
    have hcoreRestricted :
        FOFormula.Satisfies (zfCarrierMem a) stackProgramEvalCore
          coreAssignment := hcore
    have hambient := stackProgramEvalCore_carrier_to_ambient
      ha coreAssignment hcoreRestricted
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      stackProgramEvalCore _ _ ?_).mp hambient
    intro i
    simp only [coreAssignment, carrierVal_snoc_apply]

/-! ## Canonical witnesses inside a limit stage -/







private theorem satisfies_variableStackStepFormula_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
        variableStackStepFormula
        (stackStepStageAssignment hdelta hsub U hU token input output
          hinput houtput) ↔
      ∃ generator : Carrier A,
        stackTokenZFCode U token = triple varTag generator.1 ∅ ∧
          (generator.1 = U ∨ generator.1 ∈ U) ∧
          listCode output = ZFSet.pair generator.1 (listCode input) := by
  simp only [variableStackStepFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_absolute hA,
    Delta0Formula.satisfies_tripleEqAt,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    FOFormula.satisfies_disj, snoc_last, snoc_castSucc,
    Delta0Formula.val_snoc, Delta0Formula.val_apply,
    stackStepStageAssignment_val_apply, stackStepLiftOne,
    stackStepTokenIndex, stackStepVarTagIndex,
    stackStepEmptyIndex, stackStepUniverseIndex,
    stackStepOutputIndex, stackStepInputIndex,
    Subtype.ext_iff]
  rfl

private theorem comp_stackStepOpGraphRename_carrier
    {A : ZFSet.{u}}
    (s : Tuple (Carrier A) 16)
    (right left rest result inner : Carrier A) :
    (fun i =>
      (snoc (snoc (snoc (snoc (snoc s right) left) rest)
        result) inner (stackStepOpGraphRename i)).1) =
      ![result.1, left.1, right.1] := by
  funext i
  fin_cases i <;> rfl

private theorem satisfies_operationStackStepFormula_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (operation : Fin 9)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
        (operationStackStepFormula operation)
        (stackStepStageAssignment hdelta hsub U hU token input output
          hinput houtput) ↔
      ∃ right left rest result : Carrier A,
        stackTokenZFCode U token =
            triple appTag (operationCode operation) ∅ ∧
          listCode input = ZFSet.pair right.1 (ZFSet.pair left.1 rest.1) ∧
          listCode output = ZFSet.pair result.1 rest.1 ∧
          ZFSet.pair left.1 rest.1 ∈ A ∧
          result.1 = op operation left.1 right.1 := by
  simp only [operationStackStepFormula, operationStackStepBody,
    FOFormula.Satisfies, Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_absolute hA,
    Delta0Formula.satisfies_tripleEqAt,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    FOFormula.satisfies_rename, snoc_castSucc,
    Delta0Formula.val_snoc, Delta0Formula.val_apply,
    stackStepStageAssignment_val_apply,
    stackStepLiftFive, stackStepAssignment_operation,
    stackStepAssignment_appTag, stackStepAssignment_empty,
    stackStepAssignment_token, stackStepAssignment_input,
    stackStepAssignment_output, stackStepWitness_right,
    stackStepWitness_left, stackStepWitness_rest,
    stackStepWitness_result, stackStepWitness_inner]
  constructor
  · rintro ⟨right, left, rest, result, inner,
      htoken, hinputCode, hinner, houtputCode, hop⟩
    have hcomp :
        Delta0Formula.val (fun i =>
          snoc (snoc (snoc (snoc (snoc
            (stackStepStageAssignment hdelta hsub U hU token input output
              hinput houtput) right) left) rest) result) inner
            (stackStepOpGraphRename i)) =
          ![result.1, left.1, right.1] := by
      funext j
      exact congrFun (comp_stackStepOpGraphRename_carrier
        (stackStepStageAssignment hdelta hsub U hU token input output
          hinput houtput) right left rest result inner) j
    have hopRaw :
        Delta0Formula.Satisfies Delta0Formula.ZFMem
          (opGraphFormula operation) ![result.1, left.1, right.1] := by
      rw [hcomp] at hop
      exact hop
    have hop' : result.1 = op operation left.1 right.1 :=
      (satisfies_opGraphFormula operation result.1 left.1 right.1).mp hopRaw
    have hinnerMem : ZFSet.pair left.1 rest.1 ∈ A := by
      rw [← hinner]
      exact inner.2
    exact ⟨right, left, rest, result, htoken,
      hinputCode.trans (congrArg (ZFSet.pair right.1) hinner),
      houtputCode, hinnerMem, hop'⟩
  · rintro ⟨right, left, rest, result,
      htoken, hinputCode, houtputCode, hinnerMem, hop⟩
    have hopRaw :
        Delta0Formula.Satisfies Delta0Formula.ZFMem
          (opGraphFormula operation) ![result.1, left.1, right.1] :=
      (satisfies_opGraphFormula operation result.1 left.1 right.1).mpr hop
    let inner : Carrier A :=
      ⟨ZFSet.pair left.1 rest.1, hinnerMem⟩
    have hcomp :
        Delta0Formula.val (fun i =>
          snoc (snoc (snoc (snoc (snoc
            (stackStepStageAssignment hdelta hsub U hU token input output
              hinput houtput) right) left) rest) result) inner
            (stackStepOpGraphRename i)) =
          ![result.1, left.1, right.1] := by
      funext j
      exact congrFun (comp_stackStepOpGraphRename_carrier
        (stackStepStageAssignment hdelta hsub U hU token input output
          hinput houtput) right left rest result inner) j
    refine ⟨right, left, rest, result, inner,
      htoken, hinputCode, rfl, houtputCode, ?_⟩
    rw [hcomp]
    exact hopRaw

private theorem satisfies_stackStepFormula_stageCarrier_of_run
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta)
    (hrun : runStackToken (rudimentaryGenerator U) token input =
      some output) :
    FOFormula.Satisfies (zfCarrierMem A)
      stackStepFormula
      (stackStepStageAssignment hdelta hsub U hU token input output
        hinput houtput) := by
  simp only [stackStepFormula, FOFormula.satisfies_disj]
  cases token with
  | inl generator =>
      left
      rw [satisfies_variableStackStepFormula_stageCarrier
        hA hdelta hsub]
      cases generator with
      | none =>
          have houtputEq : output = U :: input :=
            (Option.some.inj hrun).symm
          refine ⟨⟨U, hsub hU⟩, rfl, Or.inl rfl, ?_⟩
          simp only [houtputEq, listCode_cons]
      | some generator =>
          have hgenerator : generator.1 ∈ LStageZF delta :=
            (LStageZF_isTransitive delta).mem_trans generator.2 hU
          have houtputEq : output = generator.1 :: input :=
            (Option.some.inj hrun).symm
          refine ⟨⟨generator.1, hsub hgenerator⟩, rfl,
            Or.inr generator.2, ?_⟩
          simp only [houtputEq, listCode_cons]
  | inr operation =>
      right
      simp only [anyOperationStackStepFormula,
        FOFormula.satisfies_disj]
      have hop : FOFormula.Satisfies (zfCarrierMem A)
          (operationStackStepFormula operation)
          (stackStepStageAssignment hdelta hsub U hU (Sum.inr operation)
            input output hinput houtput) := by
        rw [satisfies_operationStackStepFormula_stageCarrier
          hA hdelta hsub]
        cases input with
        | nil => cases hrun
        | cons right tail =>
            cases tail with
            | nil => cases hrun
            | cons left rest =>
                have hright := hinput right (by simp)
                have hleft := hinput left (by simp)
                have hrestEntries : ∀ x ∈ rest, x ∈ LStageZF delta := by
                  intro x hx
                  exact hinput x (by simp [hx])
                have hrest :=
                  listCode_mem_LStageZF_of_isSuccLimit hdelta hrestEntries
                have hresult := op_mem_LStageZF_of_isSuccLimit
                  hdelta operation hleft hright
                have hinner := orderedPair_mem_LStageZF_of_isSuccLimit
                  hdelta hleft hrest
                have houtputEq :
                    output = op operation left right :: rest :=
                  (Option.some.inj hrun).symm
                refine ⟨⟨right, hsub hright⟩, ⟨left, hsub hleft⟩,
                  ⟨listCode rest, hsub hrest⟩,
                  ⟨op operation left right, hsub hresult⟩,
                  rfl, rfl, ?_, hsub hinner, rfl⟩
                simp only [houtputEq, listCode_cons]
      fin_cases operation
      · exact Or.inl hop
      · exact Or.inr (Or.inl hop)
      · exact Or.inr (Or.inr (Or.inl hop))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hop)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hop))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hop)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl hop))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl hop)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr hop)))))))

private theorem satisfies_valueAtFormula_stageCarrier_iff
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (xs : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ LStageZF delta)
    (k : Nat) (value : Carrier A) :
    FOFormula.Satisfies (zfCarrierMem A) valueAtFormula
        ![⟨IndexedSequenceZF.sequenceCode xs,
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hxs)⟩,
          ⟨natCode k, hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩,
          value] ↔
      ∃ hk : k < xs.length, value.1 = xs.get ⟨k, hk⟩ := by
  rw [valueAtFormula,
    Delta0Formula.satisfies_toFO_absolute hA]
  have hval :
      Delta0Formula.val
        ![⟨IndexedSequenceZF.sequenceCode xs,
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hxs)⟩,
          ⟨natCode k, hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩,
          value] = ![IndexedSequenceZF.sequenceCode xs,
            natCode k, value.1] := by
    funext i
    fin_cases i <;> rfl
  rw [hval]
  exact satisfies_valueAt_sequenceCode_iff xs k value.1

private theorem satisfies_hasLengthFormula_stageCarrier_iff
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (xs : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ LStageZF delta)
    (length : Carrier A) :
    FOFormula.Satisfies (zfCarrierMem A) hasLengthFormula
        ![⟨IndexedSequenceZF.sequenceCode xs,
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hxs)⟩,
          length] ↔
      length.1 = natCode xs.length := by
  simp only [hasLengthFormula, FOFormula.Satisfies]
  constructor
  · rintro ⟨graph, hpair⟩
    have hpairRaw := (satisfies_kuratowskiPairEqAt_carrier
      hA
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) _).mp hpair
    exact (ZFSet.pair_inj.mp hpairRaw).1.symm
  · intro hlength
    let graph : Carrier A :=
      ⟨IndexedSequenceZF.graph xs,
        hsub (graphFrom_mem_LStageZF_of_isSuccLimit hdelta hxs 0)⟩
    refine ⟨graph, ?_⟩
    apply (satisfies_kuratowskiPairEqAt_carrier
      hA
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) _).mpr
    change IndexedSequenceZF.sequenceCode xs =
      ZFSet.pair length.1 (IndexedSequenceZF.graph xs)
    rw [hlength]
    rfl

private theorem satisfies_sequenceValidity_sequenceCode_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (xs : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      sequenceValidityFormula
      ![⟨Ordinal.omega0.toZFSet, homegaA⟩,
        ⟨IndexedSequenceZF.sequenceCode xs,
          hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hxs)⟩] := by
  rw [satisfies_sequenceValidityFormula_carrier
    hA]
  let length : Carrier A :=
    ⟨natCode xs.length,
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta xs.length)⟩
  let graph : Carrier A :=
    ⟨IndexedSequenceZF.graph xs,
      hsub (graphFrom_mem_LStageZF_of_isSuccLimit hdelta hxs 0)⟩
  refine ⟨length, graph, rfl, ?_, ?_⟩
  · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 xs.length)
  · intro index hindex
    rcases (mem_natCode_iff index.1 xs.length).mp hindex with
      ⟨k, hk, hindexEq⟩
    have hvalue : xs.get ⟨k, hk⟩ ∈ LStageZF delta :=
      hxs _ (List.get_mem xs ⟨k, hk⟩)
    let value : Carrier A :=
      ⟨xs.get ⟨k, hk⟩, hsub hvalue⟩
    refine ⟨value, ?_, ?_⟩
    · apply (mem_graph_iff xs _).mpr
      exact ⟨⟨k, hk⟩, by simp only [hindexEq, value]⟩
    · intro other hother
      rcases (mem_graph_iff xs _).mp hother with ⟨j, hpair⟩
      have hparts := ZFSet.pair_inj.mp hpair
      have hkj : k = j.1 := natCode_injective
        (hindexEq.symm.trans hparts.2)
      simpa only [value, hkj] using hparts.1

private theorem satisfies_successorFOAt_carrier
    {a : ZFSet.{u}} (ha : a.IsTransitive) {n : Nat}
    (successor predecessor : Fin n) (s : Tuple (Carrier a) n) :
    FOFormula.Satisfies (zfCarrierMem a)
        (Delta0Formula.successorFOAt successor predecessor) s ↔
      (s successor).1 = insert (s predecessor).1 (s predecessor).1 := by
  rw [Delta0Formula.successorFOAt,
    Delta0Formula.satisfies_toFO_absolute ha,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_successorAt]
  simp only [Delta0Formula.val_apply]





private theorem stackStepPrefixStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta) :
    (fun i => (stackStepPrefixStageAssignment hdelta hsub U hU i).1) =
      stackStepPrefixAssignment U := by
  funext i
  fin_cases i <;> rfl



private theorem traceStepExecutionStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) (k : Nat) :
    (fun i => (traceStepExecutionStageAssignment hdelta hsub U hU program
      states hstateCodes k i).1) =
      traceStepAssignment U (stackProgramZFCode U program)
        (IndexedSequenceZF.sequenceCode (encodedStackStates states))
        (natCode k) := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · rfl
      · simpa only [traceStepExecutionStageAssignment,
          traceStepAssignment, stackStepAssignment, snoc_castSucc] using
          congrFun (stackStepPrefixStageAssignment_val hdelta hsub U hU) i12

private theorem comp_traceStepProgramValueRename_execution_stage
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) (k : Nat)
    (token input succ output : Carrier A) :
    (fun i => snoc (snoc (snoc (snoc
      (traceStepExecutionStageAssignment hdelta hsub U hU program states
        hstateCodes k) token) input) succ) output
        (traceStepProgramValueRename i)) =
      ![⟨stackProgramZFCode U program,
          hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit
            hdelta hU program)⟩,
        ⟨natCode k,
          hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩, token] := by
  funext i
  fin_cases i <;> rfl

private theorem comp_traceStepInputValueRename_execution_stage
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) (k : Nat)
    (token input succ output : Carrier A) :
    (fun i => snoc (snoc (snoc (snoc
      (traceStepExecutionStageAssignment hdelta hsub U hU program states
        hstateCodes k) token) input) succ) output
        (traceStepInputValueRename i)) =
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
        ⟨natCode k,
          hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩, input] := by
  funext i
  fin_cases i <;> rfl

private theorem comp_traceStepOutputValueRename_execution_stage
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) (k : Nat)
    (token input succ output : Carrier A) :
    (fun i => snoc (snoc (snoc (snoc
      (traceStepExecutionStageAssignment hdelta hsub U hU program states
        hstateCodes k) token) input) succ) output
        (traceStepOutputValueRename i)) =
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
        succ, output] := by
  funext i
  fin_cases i <;> rfl

private theorem comp_traceStepStackStepRename_execution_stage
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) (k : Nat)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta)
    (succ : Carrier A) :
    (fun i => snoc (snoc (snoc (snoc
      (traceStepExecutionStageAssignment hdelta hsub U hU program states
        hstateCodes k)
      ⟨stackTokenZFCode U token,
        hsub (stackTokenZFCode_mem_LStageZF_of_isSuccLimit hdelta hU token)⟩)
      ⟨listCode input,
        hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta hinput)⟩) succ)
      ⟨listCode output,
        hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta houtput)⟩
      (traceStepStackStepRename i)) =
      stackStepStageAssignment hdelta hsub U hU token input output
        hinput houtput := by
  funext i
  apply Subtype.ext
  have hextendedVal :
      (fun j => (snoc (snoc (snoc (snoc
        (traceStepExecutionStageAssignment hdelta hsub U hU program states
          hstateCodes k)
        ⟨stackTokenZFCode U token,
          hsub (stackTokenZFCode_mem_LStageZF_of_isSuccLimit hdelta hU token)⟩)
        ⟨listCode input,
          hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta hinput)⟩) succ)
        ⟨listCode output,
          hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta houtput)⟩ j).1) =
        snoc (snoc (snoc (snoc
          (traceStepAssignment U (stackProgramZFCode U program)
            (IndexedSequenceZF.sequenceCode (encodedStackStates states))
            (natCode k))
          (stackTokenZFCode U token)) (listCode input)) succ.1)
          (listCode output) := by
    rw [Model.subtypeVal_snoc, Model.subtypeVal_snoc,
      Model.subtypeVal_snoc, Model.subtypeVal_snoc,
      traceStepExecutionStageAssignment_val]
  have hraw := congrFun
    (comp_traceStepStackStepRename U (stackProgramZFCode U program)
      (IndexedSequenceZF.sequenceCode (encodedStackStates states))
      (natCode k) (stackTokenZFCode U token) (listCode input)
      succ.1 (listCode output)) i
  rw [congrFun hextendedVal (traceStepStackStepRename i),
    congrFun (stackStepStageAssignment_val hdelta hsub U hU token input
      output hinput houtput) i]
  exact hraw

private theorem satisfies_traceStepFormula_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    (hstates : ∀ stack ∈ states,
      ∀ x ∈ stack, x ∈ LStageZF delta)
    (k : Nat) (hk : k < program.length) :
    FOFormula.Satisfies (zfCarrierMem A) traceStepFormula
      (traceStepExecutionStageAssignment hdelta hsub U hU program states
        (encodedStackStates_entries_mem_LStageZF hdelta hstates) k) := by
  have hlength := htrace.length
  have hi : k < states.length := by omega
  have ho : k + 1 < states.length := by omega
  let token := program.get ⟨k, hk⟩
  let input := states.get ⟨k, hi⟩
  let output := states.get ⟨k + 1, ho⟩
  have hinput : ∀ x ∈ input, x ∈ LStageZF delta :=
    hstates input (List.get_mem states ⟨k, hi⟩)
  have houtput : ∀ x ∈ output, x ∈ LStageZF delta :=
    hstates output (List.get_mem states ⟨k + 1, ho⟩)
  let tokenStage : Carrier A :=
    ⟨stackTokenZFCode U token,
      hsub (stackTokenZFCode_mem_LStageZF_of_isSuccLimit hdelta hU token)⟩
  let inputStage : Carrier A :=
    ⟨listCode input,
      hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta hinput)⟩
  let succStage : Carrier A :=
    ⟨natCode (k + 1),
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta (k + 1))⟩
  let outputStage : Carrier A :=
    ⟨listCode output,
      hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta houtput)⟩
  rw [traceStepFormula]
  refine ⟨tokenStage, inputStage, succStage, outputStage, ?_⟩
  rw [traceStepBody]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [FOFormula.satisfies_rename,
      comp_traceStepProgramValueRename_execution_stage]
    apply (satisfies_valueAtFormula_stageCarrier_iff hA hdelta hsub
      (encodedStackProgram U program) (by
        intro code hcode
        rcases List.mem_map.mp hcode with ⟨item, _hitem, rfl⟩
        exact stackTokenZFCode_mem_LStageZF_of_isSuccLimit
          hdelta hU item) k tokenStage).mpr
    refine ⟨by simpa only [encodedStackProgram, List.length_map] using hk, ?_⟩
    simp only [encodedStackProgram, tokenStage, token,
      List.get_eq_getElem, List.getElem_map]
  · rw [FOFormula.satisfies_rename,
      comp_traceStepInputValueRename_execution_stage]
    apply (satisfies_valueAtFormula_stageCarrier_iff hA hdelta hsub
      (encodedStackStates states)
      (encodedStackStates_entries_mem_LStageZF hdelta hstates)
      k inputStage).mpr
    refine ⟨by simpa only [encodedStackStates, List.length_map] using hi, ?_⟩
    simp only [encodedStackStates, inputStage, input,
      List.get_eq_getElem, List.getElem_map]
  · apply (satisfies_successorFOAt_carrier
      hA (18 : Fin 20) (15 : Fin 20) _).mpr
    exact natCode_succ_eq_insert k
  · rw [FOFormula.satisfies_rename,
      comp_traceStepOutputValueRename_execution_stage]
    apply (satisfies_valueAtFormula_stageCarrier_iff hA hdelta hsub
      (encodedStackStates states)
      (encodedStackStates_entries_mem_LStageZF hdelta hstates)
      (k + 1) outputStage).mpr
    refine ⟨by simpa only [encodedStackStates, List.length_map] using ho, ?_⟩
    simp only [encodedStackStates, outputStage, output,
      List.get_eq_getElem, List.getElem_map]
  · rw [FOFormula.satisfies_rename,
      comp_traceStepStackStepRename_execution_stage
        (hinput := hinput) (houtput := houtput)]
    apply satisfies_stackStepFormula_stageCarrier_of_run
      hA hdelta hsub U hU token input output hinput houtput
    rcases htrace.indexed with ⟨_hlength, hsteps⟩
    simpa only [token, input, output] using hsteps ⟨k, hk⟩



private theorem stackProgramEvalCoreExecutionStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    (fun i => (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA
      U hU program result hresult states hstateCodes i).1) =
      snoc (snoc (snoc (snoc
        (stackProgramEvalAssignment U (stackProgramZFCode U program)
          result)
        (IndexedSequenceZF.sequenceCode (encodedStackStates states)))
        (natCode program.length)) (natCode states.length))
        (listCode [result]) := by
  funext i
  refine Fin.lastCases ?_ (fun i19 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i18 => ?_) i19
    · rfl
    · refine Fin.lastCases ?_ (fun i17 => ?_) i18
      · rfl
      · refine Fin.lastCases ?_ (fun i16 => ?_) i17
        · rfl
        · refine Fin.lastCases ?_ (fun i15 => ?_) i16
          · rfl
          · refine Fin.lastCases ?_ (fun i14 => ?_) i15
            · rfl
            · refine Fin.lastCases ?_ (fun i13 => ?_) i14
              · rfl
              · simpa only [stackProgramEvalCoreExecutionStageAssignment,
                  stackProgramEvalAssignment, stackStepAssignment,
                  snoc_castSucc] using congrFun
                    (stackStepPrefixStageAssignment_val hdelta hsub U hU) i13













private theorem satisfies_evalTraceSteps_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    (hstates : ∀ stack ∈ states,
      ∀ x ∈ stack, x ∈ LStageZF delta)
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      (FOFormula.boundedAll (17 : Fin 20)
        (FOFormula.rename evalTraceStepRename traceStepFormula))
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
        result hresult states hstateCodes) := by
  rw [FOFormula.satisfies_boundedAll]
  intro index hindex
  change index.1 ∈ natCode program.length at hindex
  rcases (mem_natCode_iff index.1 program.length).mp hindex with
    ⟨k, hk, hindexValue⟩
  have hindexEq : index =
      (⟨natCode k,
        hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩ :
        Carrier A) := Subtype.ext hindexValue
  subst index
  rw [FOFormula.satisfies_rename]
  have hlocal := satisfies_traceStepFormula_execution_stageCarrier
    hA hdelta hsub U hU program states htrace hstates k hk
  apply (satisfies_congr_assignment (zfCarrierMem A)
    traceStepFormula _ _ ?_).mpr hlocal
  intro i
  apply Subtype.ext
  have hextendedVal :
      (fun j => (snoc
        (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
          result hresult states hstateCodes)
        (⟨natCode k,
          hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩ :
          Carrier A) j).1) =
        snoc (snoc (snoc (snoc (snoc
          (stackProgramEvalAssignment U (stackProgramZFCode U program)
            result)
          (IndexedSequenceZF.sequenceCode (encodedStackStates states)))
          (natCode program.length)) (natCode states.length))
          (listCode [result])) (natCode k) := by
    rw [Model.subtypeVal_snoc,
      stackProgramEvalCoreExecutionStageAssignment_val]
  have hraw := congrFun
    (comp_evalTraceStepRename U (stackProgramZFCode U program)
      result (IndexedSequenceZF.sequenceCode (encodedStackStates states))
      (natCode program.length) (natCode states.length)
      (listCode [result]) (natCode k)) i
  rw [congrFun hextendedVal (evalTraceStepRename i),
    congrFun (traceStepExecutionStageAssignment_val hdelta hsub U hU program
      states (encodedStackStates_entries_mem_LStageZF hdelta hstates) k) i]
  exact hraw

private theorem satisfies_evalProgramLength_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      (FOFormula.rename evalProgramLengthRename hasLengthFormula)
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
        result hresult states hstateCodes) := by
  have hprogramCodes : ∀ code ∈ encodedStackProgram U program,
      code ∈ LStageZF delta := by
    intro code hcode
    rcases List.mem_map.mp hcode with ⟨token, _htoken, rfl⟩
    exact stackTokenZFCode_mem_LStageZF_of_isSuccLimit hdelta hU token
  let programLength : Carrier A :=
    ⟨natCode program.length,
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta program.length)⟩
  rw [FOFormula.satisfies_rename]
  have hcomp :
      (fun i => stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes
          (evalProgramLengthRename i)) =
        ![⟨stackProgramZFCode U program,
            hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit
              hdelta hU program)⟩, programLength] := by
    funext i
    fin_cases i <;> rfl
  rw [hcomp]
  apply (satisfies_hasLengthFormula_stageCarrier_iff hA hdelta hsub
    (encodedStackProgram U program) hprogramCodes programLength).mpr
  simp only [programLength, encodedStackProgram, List.length_map]

private theorem satisfies_evalTraceLength_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      (FOFormula.rename evalTraceLengthRename hasLengthFormula)
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
        result hresult states hstateCodes) := by
  let traceLength : Carrier A :=
    ⟨natCode states.length,
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta states.length)⟩
  rw [FOFormula.satisfies_rename]
  have hcomp :
      (fun i => stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes
          (evalTraceLengthRename i)) =
        ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
          traceLength] := by
    funext i
    fin_cases i <;> rfl
  rw [hcomp]
  apply (satisfies_hasLengthFormula_stageCarrier_iff hA hdelta hsub
    (encodedStackStates states) hstateCodes traceLength).mpr
  simp only [traceLength, encodedStackStates, List.length_map]

private theorem satisfies_evalSuccessor_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta)
    (hlength : states.length = program.length + 1) :
    FOFormula.Satisfies (zfCarrierMem A)
      (Delta0Formula.successorFOAt (18 : Fin 20) (17 : Fin 20))
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes) := by
  apply (satisfies_successorFOAt_carrier
    hA (18 : Fin 20) (17 : Fin 20) _).mpr
  change natCode states.length =
    insert (natCode program.length) (natCode program.length)
  rw [hlength]
  exact natCode_succ_eq_insert program.length



private theorem comp_evalInitialValueRename_execution_stageCarrier
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    (fun i => stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA
      U hU program result hresult states hstateCodes
        (evalInitialValueRename i)) =
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
        (⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩ :
          Carrier A),
        (⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩ :
          Carrier A)] := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun x => ?_) j) i
  · exact stackProgramEvalCoreExecutionStageAssignment_trace
      hdelta hsub homegaA U hU program result hresult states hstateCodes
  · exact stackProgramEvalCoreExecutionStageAssignment_empty
      hdelta hsub homegaA U hU program result hresult states hstateCodes
  · fin_cases x
    exact stackProgramEvalCoreExecutionStageAssignment_empty
      hdelta hsub homegaA U hU program result hresult states hstateCodes

private theorem satisfies_valueAt_zero_encodedStackStates_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta)
    (hstatesNonempty : 0 < states.length)
    (hhead : states.head? = some []) :
    FOFormula.Satisfies (zfCarrierMem A) valueAtFormula
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
        (⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩ :
          Carrier A),
        (⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩ :
          Carrier A)] := by
  rcases exists_encodedStackStates_zero_eq states hstatesNonempty hhead with
    ⟨hzero, hrawHead⟩
  let emptyStage : Carrier A :=
    ⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩
  let zeroStage : Carrier A :=
    ⟨natCode 0, hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta 0)⟩
  have hvalue :
      FOFormula.Satisfies (zfCarrierMem A) valueAtFormula
        ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
          zeroStage, emptyStage] := by
    exact (satisfies_valueAtFormula_stageCarrier_iff hA hdelta hsub
      (encodedStackStates states) hstateCodes 0 emptyStage).mpr
        ⟨hzero, hrawHead⟩
  apply (satisfies_congr_assignment (zfCarrierMem A)
    valueAtFormula _ _ ?_).mpr hvalue
  intro i
  fin_cases i
  · rfl
  · apply Subtype.ext
    change (∅ : ZFSet.{u}) = natCode 0
    simp [natCode]
  · rfl

private theorem satisfies_evalInitial_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta)
    (hlength : states.length = program.length + 1)
    (hhead : states.head? = some []) :
    FOFormula.Satisfies (zfCarrierMem A)
      (FOFormula.rename evalInitialValueRename valueAtFormula)
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes) := by
  have hvalue := satisfies_valueAt_zero_encodedStackStates_stageCarrier
    hA hdelta hsub states hstateCodes (by omega) hhead
  rw [FOFormula.satisfies_rename]
  apply (satisfies_congr_assignment (zfCarrierMem A)
    valueAtFormula _ _ ?_).mpr hvalue
  intro i
  exact congrFun
    (comp_evalInitialValueRename_execution_stageCarrier hdelta hsub homegaA
      U hU program result hresult states hstateCodes) i

private theorem satisfies_evalFinal_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta)
    (hlength : states.length = program.length + 1)
    (hlast : states.getLast? = some [result]) :
    FOFormula.Satisfies (zfCarrierMem A)
      (FOFormula.rename evalFinalValueRename valueAtFormula)
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes) := by
  have hrawLast :
      (encodedStackStates states).getLast? = some (listCode [result]) := by
    simp only [encodedStackStates, List.getLast?_map, hlast,
      Option.map_some]
  have hrawLength :
      (encodedStackStates states).length = program.length + 1 := by
    simpa only [encodedStackStates, List.length_map] using hlength
  have hprogramLength : program.length < (encodedStackStates states).length :=
    by omega
  have hrawLastGet :
      listCode [result] = (encodedStackStates states).get
        ⟨program.length, hprogramLength⟩ := by
    have hgetLast :
        (encodedStackStates states).getLast? =
          some ((encodedStackStates states).get
            ⟨program.length, hprogramLength⟩) := by
      rw [List.getLast?_eq_getElem?]
      have hindex :
          (encodedStackStates states).length - 1 = program.length := by
        omega
      rw [hindex, List.getElem?_eq_getElem hprogramLength]
      rfl
    rw [hgetLast] at hrawLast
    exact (Option.some.inj hrawLast).symm
  let finalStack : Carrier A :=
    ⟨listCode [result],
      hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta (by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hresult))⟩
  rw [FOFormula.satisfies_rename]
  have hcomp :
      (fun i => stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA
        U hU program result hresult states hstateCodes
          (evalFinalValueRename i)) =
        ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
          ⟨natCode program.length,
            hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta program.length)⟩,
          finalStack] := by
    funext i
    fin_cases i
    · exact stackProgramEvalCoreExecutionStageAssignment_trace
        hdelta hsub homegaA U hU program result hresult states hstateCodes
    · exact stackProgramEvalCoreExecutionStageAssignment_programLength
        hdelta hsub homegaA U hU program result hresult states hstateCodes
    · apply Subtype.ext
      exact stackProgramEvalCoreExecutionStageAssignment_finalStack
        hdelta hsub homegaA U hU program result hresult states hstateCodes
  rw [hcomp]
  apply (satisfies_valueAtFormula_stageCarrier_iff hA hdelta hsub
    (encodedStackStates states) hstateCodes program.length finalStack).mpr
  exact ⟨hprogramLength, hrawLastGet⟩

private theorem satisfies_evalFinalStack_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      (Delta0Formula.kuratowskiPairEqAt
        (19 : Fin 20) (15 : Fin 20) (3 : Fin 20)).toFO
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes) := by
  apply (satisfies_kuratowskiPairEqAt_carrier
    hA
    (19 : Fin 20) (15 : Fin 20) (3 : Fin 20) _).mpr
  rw [stackProgramEvalCoreExecutionStageAssignment_finalStack,
    stackProgramEvalCoreExecutionStageAssignment_result]
  have hempty := congrArg Subtype.val
    (stackProgramEvalCoreExecutionStageAssignment_empty hdelta hsub homegaA
      U hU program result hresult states hstateCodes)
  rw [hempty]
  rfl

private theorem satisfies_stackProgramEvalCore_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    (hhead : states.head? = some [])
    (hlast : states.getLast? = some [result])
    (hstates : ∀ stack ∈ states,
      ∀ x ∈ stack, x ∈ LStageZF delta)
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      stackProgramEvalCore
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes) := by
  rw [stackProgramEvalCore]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact satisfies_evalProgramLength_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
  · exact satisfies_evalTraceLength_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
  · exact satisfies_evalSuccessor_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
        htrace.length
  · exact satisfies_evalInitial_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
        htrace.length hhead
  · exact satisfies_evalFinal_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
        htrace.length hlast
  · exact satisfies_evalFinalStack_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
  · exact satisfies_evalTraceSteps_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states htrace hstates
        hstateCodes







private theorem satisfies_stackProgramEvalFormula_stageCarrier_of_run
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (hrun : runStackProgram (rudimentaryGenerator U) program [] =
      some [result]) :
    FOFormula.Satisfies (zfCarrierMem A)
      stackProgramEvalFormula
      (stackProgramEvalStageAssignment hdelta hsub homegaA U hU program
        result (hsub hresult)) := by
  rcases exists_executionTrace_of_run
      (rudimentaryGenerator U) program [] [result] hrun with
    ⟨states, htrace, hhead, hlast⟩
  have hstates : ∀ stack ∈ states,
      ∀ x ∈ stack, x ∈ LStageZF delta :=
    htrace.entries_mem_LStageZF_of_isSuccLimit hdelta hU hhead (by simp)
  have hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta :=
    encodedStackStates_entries_mem_LStageZF hdelta hstates
  have hprogramCodes : ∀ code ∈ encodedStackProgram U program,
      code ∈ LStageZF delta := by
    intro code hcode
    rcases List.mem_map.mp hcode with ⟨token, _htoken, rfl⟩
    exact stackTokenZFCode_mem_LStageZF_of_isSuccLimit hdelta hU token
  let omegaStage : Carrier A :=
    ⟨Ordinal.omega0.toZFSet, homegaA⟩
  let programStage : Carrier A :=
    ⟨stackProgramZFCode U program,
      hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit hdelta hU program)⟩
  let traceStage : Carrier A :=
    ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
      hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩
  let programLengthStage : Carrier A :=
    ⟨natCode program.length,
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta program.length)⟩
  let traceLengthStage : Carrier A :=
    ⟨natCode states.length,
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta states.length)⟩
  let finalStackStage : Carrier A :=
    ⟨listCode [result],
      hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta (by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hresult))⟩
  let baseAssignment :=
    stackProgramEvalStageAssignment hdelta hsub homegaA U hU program
      result (hsub hresult)
  let traceContext : Tuple (Carrier A) 17 :=
    snoc baseAssignment traceStage
  rw [stackProgramEvalFormula]
  refine ⟨?_, traceStage, ?_, programLengthStage,
    traceLengthStage, finalStackStage, ?_⟩
  · rw [FOFormula.satisfies_rename]
    have hcomp :
        (fun i => baseAssignment (evalProgramValidityRename i)) =
          ![omegaStage, programStage] := by
      funext i
      fin_cases i <;> rfl
    rw [hcomp]
    simpa only [programStage, stackProgramZFCode,
      encodedStackProgram] using
      (satisfies_sequenceValidity_sequenceCode_stageCarrier
        hA hdelta hsub homegaA
          (encodedStackProgram U program) hprogramCodes)
  · rw [FOFormula.satisfies_rename]
    have hcomp :
        (fun i => traceContext (evalTraceValidityRename i)) =
          ![omegaStage, traceStage] := by
      funext i
      fin_cases i <;> rfl
    rw [hcomp]
    exact satisfies_sequenceValidity_sequenceCode_stageCarrier
      hA hdelta hsub homegaA (encodedStackStates states) hstateCodes
  · exact satisfies_stackProgramEvalCore_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states htrace hhead hlast
        hstates hstateCodes





/-! ## The output formula over a limit stage -/



private theorem godelDefOutputStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A) :
    (fun i => (godelDefOutputStageAssignment hdelta hsub homegaA
      U nextU hU hnextU i).1) =
      Model.bareGodelDefOutputRawAssignment
        Model.stageHistoryFixedParametersRaw U nextU := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun i13 => ?_) i14
    · rfl
    · fin_cases i13 <;> rfl



private theorem stackProgramEvalCodeStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U code result : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hcode : code ∈ A)
    (hresult : result ∈ A) :
    (fun i => (stackProgramEvalCodeStageAssignment hdelta hsub homegaA U code
      result hU hcode hresult i).1) =
      stackProgramEvalAssignment U code result := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · rfl
      · simpa only [stackProgramEvalCodeStageAssignment,
          stackProgramEvalAssignment, snoc_castSucc] using
          congrFun (stackStepPrefixStageAssignment_val hdelta hsub U hU) i12

private theorem comp_godelDefEvalRename_stage
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU result code : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A)
    (hresult : result ∈ A) (hcode : code ∈ A) :
    (fun i => snoc (snoc
      (godelDefOutputStageAssignment hdelta hsub homegaA U nextU hU hnextU)
      ⟨result, hresult⟩) ⟨code, hcode⟩ (godelDefEvalRename i)) =
      stackProgramEvalCodeStageAssignment hdelta hsub homegaA U code result
        hU hcode hresult := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · simp only [godelDefEvalRename, Fin.lastCases_castSucc,
        godelDefOutputStageAssignment,
        stackProgramEvalCodeStageAssignment, snoc_castSucc]

private theorem satisfies_godelDefSubset_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU result : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A)
    (hresult : result ∈ A) :
    FOFormula.Satisfies (zfCarrierMem A)
      (Delta0Formula.subsetAt (15 : Fin 16) (0 : Fin 16)).toFO
      (snoc (godelDefOutputStageAssignment hdelta hsub homegaA
        U nextU hU hnextU) ⟨result, hresult⟩) ↔ result ⊆ U := by
  rw [Delta0Formula.satisfies_toFO_absolute
      hA,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_subsetAt]
  change result ⊆ U ↔ result ⊆ U
  rfl

private theorem satisfies_godelDefOutputFormula_components_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A) :
    FOFormula.Satisfies (zfCarrierMem A)
      godelDefOutputFormula
      (godelDefOutputStageAssignment hdelta hsub homegaA
        U nextU hU hnextU) ↔
      ∀ result : Carrier A,
        result.1 ∈ nextU ↔ result.1 ⊆ U ∧
          ∃ code : Carrier A,
            FOFormula.Satisfies (zfCarrierMem A)
              stackProgramEvalFormula
              (stackProgramEvalCodeStageAssignment hdelta hsub homegaA
                U code.1 result.1 hU code.2 result.2) := by
  simp only [godelDefOutputFormula, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp]
  apply forall_congr'
  intro result
  change
    (result.1 ∈ nextU ↔
      FOFormula.Satisfies (zfCarrierMem A)
          (Delta0Formula.subsetAt (15 : Fin 16) (0 : Fin 16)).toFO
          (snoc (godelDefOutputStageAssignment hdelta hsub homegaA
            U nextU hU hnextU) result) ∧
        ∃ code : Carrier A,
          FOFormula.Satisfies (zfCarrierMem A)
            (FOFormula.rename godelDefEvalRename stackProgramEvalFormula)
            (snoc (snoc (godelDefOutputStageAssignment hdelta hsub homegaA
              U nextU hU hnextU) result) code)) ↔ _
  rw [satisfies_godelDefSubset_stageCarrier hA]
  simp only [FOFormula.satisfies_rename,
    comp_godelDefEvalRename_stage]

private theorem rudimentaryClosureTerm_eval_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {U : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    (term : RudimentaryClosureTerm U) :
    term.eval ∈ LStageZF theta := by
  induction term with
  | var generator =>
      cases generator with
      | none => exact hU
      | some x =>
          exact (LStageZF_isTransitive theta).mem_trans x.2 hU
  | app i left right hleft hright =>
      exact op_mem_LStageZF_of_isSuccLimit htheta i hleft hright

private theorem godelDef_element_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {U result : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    (hresult : result ∈ godelDef U) : result ∈ LStageZF theta := by
  rcases mem_godelDef_iff_exists_rudimentaryTerm.mp hresult with
    ⟨_hsubset, term, hterm⟩
  rw [← hterm]
  exact rudimentaryClosureTerm_eval_mem_LStageZF_of_isSuccLimit
    htheta hU term

private theorem satisfies_godelDefOutputFormula_stageCarrier_iff
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A) :
    FOFormula.Satisfies (zfCarrierMem A)
      godelDefOutputFormula
      (godelDefOutputStageAssignment hdelta hsub homegaA
        U nextU hU hnextU) ↔ nextU = godelDef U := by
  rw [satisfies_godelDefOutputFormula_components_stageCarrier hA]
  constructor
  · intro h
    apply ZFSet.ext
    intro result
    constructor
    · intro hnext
      have hresultA : result ∈ A := hA.mem_trans hnext hnextU
      let resultStage : Carrier A := ⟨result, hresultA⟩
      rcases (h resultStage).mp hnext with ⟨hsubset, code, heval⟩
      have hambient := stackProgramEval_carrier_to_ambient
        hA _ heval
      rw [stackProgramEvalCodeStageAssignment_val] at hambient
      rcases (satisfies_stackProgramEvalFormula_iff_exists_run
        U code.1 result).mp hambient with
        ⟨program, _hrep, hrun⟩
      exact mem_godelDef_iff.mpr
        ⟨hsubset, mem_rudimentaryClosure_of_runStackProgram
          U program result hrun⟩
    · intro hgodel
      have hresultDelta : result ∈ LStageZF delta :=
        godelDef_element_mem_LStageZF_of_isSuccLimit hdelta hU hgodel
      let resultStage : Carrier A := ⟨result, hsub hresultDelta⟩
      apply (h resultStage).mpr
      have hparts := mem_godelDef_iff.mp hgodel
      rcases mem_rudimentaryClosure_iff_exists_term.mp hparts.2 with
        ⟨term, hterm⟩
      let program := stackProgram term
      have hrun : runStackProgram (rudimentaryGenerator U) program [] =
          some [result] := by
        simp only [program, run_stackProgram, hterm]
      let code : Carrier A :=
        ⟨stackProgramZFCode U program,
          hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit
            hdelta hU program)⟩
      refine ⟨hparts.1, code, ?_⟩
      have heval := satisfies_stackProgramEvalFormula_stageCarrier_of_run
        hA hdelta hsub homegaA U hU program result hresultDelta hrun
      change FOFormula.Satisfies (zfCarrierMem A)
        stackProgramEvalFormula
        (stackProgramEvalCodeStageAssignment hdelta hsub homegaA
          U code.1 result hU code.2 (hsub hresultDelta))
      simpa only [code, program, stackProgramEvalStageAssignment,
        stackProgramEvalCodeStageAssignment] using heval
  · intro hnext result
    rw [hnext, mem_godelDef_iff]
    constructor
    · rintro ⟨hsubset, hclosure⟩
      have hresultDelta : result.1 ∈ LStageZF delta :=
        godelDef_element_mem_LStageZF_of_isSuccLimit hdelta hU
          (mem_godelDef_iff.mpr ⟨hsubset, hclosure⟩)
      rcases mem_rudimentaryClosure_iff_exists_term.mp hclosure with
        ⟨term, hterm⟩
      let program := stackProgram term
      have hrun : runStackProgram (rudimentaryGenerator U) program [] =
          some [result.1] := by
        simp only [program, run_stackProgram, hterm]
      let code : Carrier A :=
        ⟨stackProgramZFCode U program,
          hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit
            hdelta hU program)⟩
      refine ⟨hsubset, code, ?_⟩
      have heval := satisfies_stackProgramEvalFormula_stageCarrier_of_run
        hA hdelta hsub homegaA U hU program result.1 hresultDelta hrun
      change FOFormula.Satisfies (zfCarrierMem A)
        stackProgramEvalFormula
        (stackProgramEvalCodeStageAssignment hdelta hsub homegaA
          U code.1 result.1 hU code.2 result.2)
      simpa only [code, program, stackProgramEvalStageAssignment,
        stackProgramEvalCodeStageAssignment] using heval
    · rintro ⟨hsubset, code, heval⟩
      have hambient := stackProgramEval_carrier_to_ambient
        hA _ heval
      rw [stackProgramEvalCodeStageAssignment_val] at hambient
      rcases (satisfies_stackProgramEvalFormula_iff_exists_run
        U code.1 result.1).mp hambient with
        ⟨program, _hrep, hrun⟩
      exact ⟨hsubset,
        mem_rudimentaryClosure_of_runStackProgram
          U program result.1 hrun⟩

/-- Pointwise correctness of the internal Goedel-definability output formula
in a transitive carrier containing a nonzero limit level with all canonical
finite witnesses.  Only the predecessor `U` is required to lie in that
sublevel; the candidate output may be any element of the ambient carrier. -/
private theorem bareGodelDefOutputIn_of_isSuccLimit_substage_iff
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A) :
    Model.BareGodelDefOutputIn (A : Set ZFSet.{u})
        Model.stageHistoryFixedParametersRaw U nextU ↔
      nextU = godelDef U := by
  let s := godelDefOutputStageAssignment
    hdelta hsub homegaA U nextU hU hnextU
  have hbridge := Model.satisfies_subtype_iff_satisfiesIn
    (A : Set ZFSet.{u}) godelDefOutputFormula s
  have hval := godelDefOutputStageAssignment_val
    hdelta hsub homegaA U nextU hU hnextU
  rw [hval] at hbridge
  exact hbridge.symm.trans
    (satisfies_godelDefOutputFormula_stageCarrier_iff
      hA hdelta hsub homegaA U nextU hU hnextU)



end
end «RudimentaryTerm»
end «Godel»
end «Constructible»
end
end GCHSource_Work_CUGCH_BareGodelDefAbsolute

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

/-- Every finite constructible level is itself an element of `L_omega`.
This is genuine internal membership, not only inclusion in `L_omega`. -/
private theorem LStageZF_natCast_mem_LStageZF_omega (n : Nat) :
    LStageZF (n : Ordinal.{u}) ∈
      LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
  LStageZF_mem_LStageZF_of_lt_isSuccLimit
    Ordinal.isSuccLimit_omega0 (Ordinal.natCast_lt_omega0 n)











end

end Constructible.Model

end
end GCHSource_Work_CUGCH_CanonicalBareHistoryOmegaBounds

/- Source module: Solutions.Work_CUGCH_BareGodelDefFinite -/
section GCHSource_Work_CUGCH_BareGodelDefFinite
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The Goedel evaluator on finite constructible predecessors

This file isolates the exceptional carrier used at the first infinite
history stage.  The evaluator is interpreted in `L_(omega+1)`, because its
fixed prefix contains the set `omega`; its actual predecessor, output,
program, and trace data are bounded already by `L_omega`.

No claim is made here about arbitrary predecessor inputs in `L_(omega+1)`.
-/

section

universe u

namespace Constructible.Model

noncomputable section

/-- The witness-producing substage `L_omega` is contained in the semantic
carrier `L_(omega+1)`. -/
private theorem LStageZF_omega_subset_omega_succ :
    (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u}) ⊆
      LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})) :=
  LStageZF_mono (Order.le_succ (Ordinal.omega0 : Ordinal.{u}))

/-- The one fixed parameter absent from `L_omega` itself is available in
the successor carrier in which the finite evaluator is interpreted. -/
private theorem omega_toZFSet_mem_LStageZF_omega_succ :
    (Ordinal.omega0 : Ordinal.{u}).toZFSet ∈
      LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})) :=
  ordinal_toZFSet_mem_LStageZF_of_lt
    (Order.lt_succ (Ordinal.omega0 : Ordinal.{u}))

/-- A finite predecessor is available in the witness-producing substage. -/
private theorem finiteGodelPredecessor_mem_LStageZF_omega (n : Nat) :
    LStageZF (n : Ordinal.{u}) ∈
      LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
  LStageZF_natCast_mem_LStageZF_omega n





/-- Exact pointwise correctness of the Goedel-output formula for an actual
finite constructible predecessor.  The candidate output ranges over all of
`L_(omega+1)`, while the predecessor is explicitly fixed to `L_n`. -/
private theorem bareGodelDefOutputIn_omega_succ_natCast_iff
    (n : Nat) (stage : ZFSet.{u})
    (hstage : stage ∈
      LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u}))) :
    BareGodelDefOutputIn
        (LStageZF (Order.succ
          (Ordinal.omega0 : Ordinal.{u})) : Set ZFSet.{u})
        stageHistoryFixedParametersRaw
        (LStageZF (n : Ordinal.{u})) stage ↔
      stage = Godel.godelDef (LStageZF (n : Ordinal.{u})) := by
  exact
    Godel.RudimentaryTerm.bareGodelDefOutputIn_of_isSuccLimit_substage_iff
        (LStageZF_isTransitive
          (Order.succ (Ordinal.omega0 : Ordinal.{u})))
        Ordinal.isSuccLimit_omega0
        LStageZF_omega_subset_omega_succ
        omega_toZFSet_mem_LStageZF_omega_succ
        (LStageZF (n : Ordinal.{u})) stage
        (finiteGodelPredecessor_mem_LStageZF_omega n) hstage

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_BareGodelDefFinite

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

/-- The exact finite-input evaluator contract needed at the first infinite
history stage.  The predecessor is an actual finite level `L_n`; no claim is
made about arbitrary predecessor inputs in `L_(omega+1)`. -/
private theorem finiteBareGodelDefOutputCorrectIn_omega_succ :
    FiniteBareGodelDefOutputCorrectIn
      (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})))
      stageHistoryFixedParametersRaw := by
  intro n stage _hpredecessor hstage
  exact bareGodelDefOutputIn_omega_succ_natCast_iff n stage hstage



/-- Once the exact finite-input fact at `L_(omega+1)` is supplied, the
global history bound is unconditional at all larger limit levels: evaluator
correctness there is the proved limit-level absoluteness theorem. -/
private theorem canonicalBareHistory_mem_LStageZF_add_omega_of_finite_correct
    (hfinite : FiniteBareGodelDefOutputCorrectIn
      (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})))
      stageHistoryFixedParametersRaw) :
    forall ordinal : Ordinal.{u},
      canonicalBareHistory ordinal ∈
        LStageZF (ordinal + Ordinal.omega0) := by
  apply canonicalBareHistory_mem_LStageZF_add_omega_of_evaluators hfinite
  intro limit hlimit homega
  exact
    Godel.RudimentaryTerm.bareGodelDefOutputCorrectIn_LStageZF_of_omega_lt
      hlimit homega



/-- Unconditional global canonical-history bound. -/
private theorem canonicalBareHistory_mem_LStageZF_add_omega_gchProof04
    (ordinal : Ordinal.{u}) :
    canonicalBareHistory ordinal ∈
      LStageZF (ordinal + Ordinal.omega0) :=
  canonicalBareHistory_mem_LStageZF_add_omega_of_finite_correct
    finiteBareGodelDefOutputCorrectIn_omega_succ ordinal

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_CanonicalBareHistoryGlobal

universe u

theorem solution : ∀ (ordinal : Ordinal.{u}),
  @Membership.mem.{u + 1, u + 1} ZFSet.{u} ZFSet.{u}
    (@SetLike.instMembership.{u + 1, u + 1} ZFSet.{u} ZFSet.{u} ZFSet.instSetLike.{u})
    (Constructible.LStageZF.{u}
      (@HAdd.hAdd.{u + 1, u + 1, u + 1} Ordinal.{u} Ordinal.{u} Ordinal.{u}
        (@instHAdd.{u + 1} Ordinal.{u} Ordinal.add.{u}) ordinal Ordinal.omega0.{u}))
    (Constructible.Model.canonicalBareHistory.{u} ordinal) :=
  @Constructible.Model.canonicalBareHistory_mem_LStageZF_add_omega_gchProof04.{u}
