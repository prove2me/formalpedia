-- Prove2me | solution 1 for Constructible.ContinuumFormula.CardinalControlledHull.element_mem_internalHartogsStage
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-25T23:57:31.137671+00:00
-- url     : https://prove2.me/submissions/346c7f66-9861-43f3-b083-599fca4fe2be

import Definitions.Def_CH_ConstructibleGCH_Library05
import Theorems.Thm_Constructible_ContinuumFormula_CardinalControlledHull_collapsedHeight_lt_internalHartogsOrdinal
import Theorems.Thm_Constructible_Godel_RudimentaryTerm_bareGodelDefOutputCorrectIn_LStageZF_of_omega_lt
import Theorems.Thm_Constructible_Model_canonicalBareHistory_mem_LStageZF_add_omega
import Theorems.Thm_Constructible_MostowskiCollapse_StageCondensationInterfaces_range_eq_LStageZF_ordinalHeight

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





















private theorem DefZF_subset_powerset (a : ZFSet.{u}) : DefZF a ⊆ a.powerset := by
  intro z hz
  exact ZFSet.mem_powerset.mpr ((mem_DefZF_iff.mp hz).1)





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



/-! ## Pointwise stage bounds -/







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





/-! ## Conditional local Separation at a limit -/













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



/-- Exact formula semantics under the same transparent assumptions. -/
private theorem satisfiesIn_bareStageAtFormula_ordinal_iff_of_canonicalHistory_mem
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13) (hfixed : ∀ i, fixed i ∈ U)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : BareGodelDefOutputCorrectIn U fixed)
    (ordinal : Ordinal.{u}) (stage : ZFSet.{u})
    (hindex : ordinal.toZFSet ∈ U) (hstage : stage ∈ U)
    (hhistory : canonicalBareHistory ordinal ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) bareStageAtFormula
        (bareStageAtRawAssignment fixed ordinal.toZFSet stage) ↔
      stage = LStageZF ordinal := by
  rw [satisfiesIn_bareStageAtFormula_iff hU fixed
      ordinal.toZFSet stage hfixed hindex hstage,
    bareStageAtIn_ordinal_iff_of_canonicalHistory_mem hU fixed hempty
      hcorrect ordinal stage hindex hstage hhistory]

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_CanonicalBareHistorySemantics

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



































/-- Collapsing an already transitive membership structure fixes each of its
elements. -/
private theorem collapse_eq_self_of_mem {domain : ZFSet.{u}}
    (htransitive : domain.IsTransitive) :
    ∀ x : ZFSet.{u}, x ∈ domain → collapse domain x = x := by
  intro x
  refine ZFSet.inductionOn
    (p := fun x => x ∈ domain → collapse domain x = x) x ?_
  intro x ih hxdomain
  apply ZFSet.ext
  intro z
  rw [mem_collapse_iff]
  constructor
  · rintro ⟨y, hyx, hydomain, hvalue⟩
    have hyz : y = z := (ih y hyx hydomain).symm.trans hvalue
    simpa only [hyz] using hyx
  · intro hzx
    have hzdomain : z ∈ domain :=
      htransitive.mem_trans hzx hxdomain
    exact ⟨z, hzx, hzdomain, ih z hzx hzdomain⟩

end

end Constructible.MostowskiCollapse

end
end GCHSource_Work_CUGCH_MostowskiCollapse

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

















/-! ## Ordinal reflection through full elementarity -/























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







/-! ## Constructible stages at limit indices -/















end

end Constructible.MostowskiCollapse

end
end GCHSource_Work_CUGCH_MostowskiCollapseOrdinals

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





/-- The bounded ordinal formula has its ambient meaning in every transitive
set. -/
private theorem satisfiesIn_isOrdinal_iff {U : ZFSet.{u}} (hU : U.IsTransitive)
    (x : ZFSet.{u}) (hx : x ∈ U) :
    Model.SatisfiesIn (U : Set ZFSet.{u})
        OrdinalFormula.isOrdinal ![x] ↔ x.IsOrdinal := by
  let xU : ZFCarrier U := ⟨x, hx⟩
  have hbridge := Model.satisfies_subtype_iff_satisfiesIn
    (U : Set ZFSet.{u}) OrdinalFormula.isOrdinal ![xU]
  have hsemantic := OrdinalFormula.satisfies_isOrdinal hU xU
  have hraw : (fun i => (![xU] i).1) = ![x] := by
    funext i
    fin_cases i
    rfl
  rw [hraw] at hbridge
  exact hbridge.symm.trans hsemantic

/-- Coordinate form of `satisfiesIn_isOrdinal_iff`. -/
private theorem satisfiesIn_ordinalAt_iff {U : ZFSet.{u}} (hU : U.IsTransitive)
    {n : Nat} (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : forall j, s j ∈ U) :
    Model.SatisfiesIn (U : Set ZFSet.{u}) (Model.ordinalAt i) s ↔
      (s i).IsOrdinal := by
  rw [Model.ordinalAt,
    Model.satisfiesIn_rename (U : Set ZFSet.{u})]
  have hone : (fun _ : Fin 1 => s i) = ![s i] := by
    funext j
    fin_cases j
    rfl
  rw [hone, satisfiesIn_isOrdinal_iff hU (s i) (hs i)]



















/-! ## Bounded stage witnesses for the limit step -/































end CondensationHull

end

end MostowskiCollapse

end Constructible

end
end GCHSource_Work_CUGCH_Condensation

/- Source module: Solutions.Work_CUGCH_CondensationFixedParameters -/
section GCHSource_Work_CUGCH_CondensationFixedParameters
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# Canonical parameters in elementary substructures of constructible levels

The thirteen constants used by the internal stage recursion are not extra
parameters in the Condensation Lemma.  They are uniquely characterized by a
parameter-free first-order assertion: there are thirteen objects satisfying
`canonicalStageParametersFormula`.

This file first checks the exact semantics of the open matrix over every
limit level `L_theta` above `omega`.  It then existentially closes all thirteen
variables, transfers that closed sentence by full elementarity, and uses the
same semantic characterization to identify the witnesses in the elementary
substructure with the canonical constants.
-/

section

open Set

universe u

namespace Constructible

namespace Model

noncomputable section

private theorem satisfiesIn_all_iff_CondensationFixedParameters_gch
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s <->
      forall x : ZFSet.{u}, x ∈ M ->
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

/-- In a transitive carrier, the formula `emptySetAt i` says exactly that
coordinate `i` is the ambient empty set. -/
private theorem satisfiesIn_emptySetAt_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive) {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : forall j, s j ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) (emptySetAt i) s <->
      s i = (∅ : ZFSet.{u}) := by
  rw [emptySetAt, satisfiesIn_all_iff_CondensationFixedParameters_gch]
  simp only [SatisfiesIn, snoc_last, snoc_castSucc]
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact (h z (hU.mem_trans hz (hs i)) hz).elim
    · intro hz
      exact (ZFSet.notMem_empty z hz).elim
  · intro h z _hzU hz
    rw [h] at hz
    exact (ZFSet.notMem_empty z hz).elim

/-- The bounded successor formula is absolute to a transitive carrier. -/
private theorem satisfiesIn_successorSetAt_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive) {n : Nat}
    (successor index : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : forall j, s j ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u})
        (successorSetAt successor index) s <->
      s successor = insert (s index) (s index) := by
  let sU : Tuple (ZFCarrier U) n := fun j => ⟨s j, hs j⟩
  have hbridge := satisfies_subtype_iff_satisfiesIn
    (U : Set ZFSet.{u}) (successorSetAt successor index) sU
  have hvalues : (fun j => (sU j).1) = s := by
    funext j
    rfl
  rw [hvalues] at hbridge
  change
    (FOFormula.Satisfies (zfCarrierMem U)
        (successorSetAt successor index) sU <->
      SatisfiesIn (U : Set ZFSet.{u})
        (successorSetAt successor index) s) at hbridge
  have habsolute := Delta0Formula.satisfies_toFO_absolute hU
    (Delta0Formula.successorAt successor index) sU
  change
    (FOFormula.Satisfies (zfCarrierMem U)
        (successorSetAt successor index) sU <->
      FOFormula.Satisfies (fun x y : ZFSet.{u} => x ∈ y)
        (successorSetAt successor index) (fun j => (sU j).1))
      at habsolute
  rw [hvalues] at habsolute
  have hambient :
      FOFormula.Satisfies (fun x y : ZFSet.{u} => x ∈ y)
          (successorSetAt successor index) s <->
        s successor = insert (s index) (s index) := by
    simpa only [successorSetAt, Delta0Formula.ZFMem] using
      (Delta0Formula.satisfies_successorFOAt_ambient
        successor index s)
  exact hbridge.symm.trans (habsolute.trans hambient)



/-- Over a transitive carrier containing the empty set and closed under von
Neumann successor, `inductiveSetAt` has its ordinary set-theoretic meaning. -/
private theorem satisfiesIn_inductiveSetAt_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (hemptyU : (∅ : ZFSet.{u}) ∈ U)
    (hsuccU : forall x : ZFSet.{u}, x ∈ U -> insert x x ∈ U)
    {n : Nat} (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : forall j, s j ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) (inductiveSetAt i) s <->
      IsInductiveSetIn U (s i) := by
  simp only [inductiveSetAt, SatisfiesIn, satisfiesIn_all_iff_CondensationFixedParameters_gch,
    satisfiesIn_imp_iff, snoc_last, snoc_castSucc, IsInductiveSetIn]
  constructor
  · rintro ⟨⟨e, heU, heEmpty, heMem⟩, hsucc⟩
    have he : e = (∅ : ZFSet.{u}) := by
      simpa only [snoc_last] using
        (satisfiesIn_emptySetAt_iff hU (Fin.last n) (snoc s e) (by
        intro j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · simpa using heU
        · simpa using hs k)).mp heEmpty
    constructor
    · simpa only [he] using heMem
    · intro x hxU hxw
      rcases hsucc x hxU hxw with ⟨next, hnextU, hnext, hnextMem⟩
      have hnextEq : next = insert x x := by
        simpa only [snoc_last, snoc_castSucc] using
          (satisfiesIn_successorSetAt_iff hU
          (Fin.last (n + 1)) (Fin.last n).castSucc
          (snoc (snoc s x) next) (by
            intro j
            refine Fin.lastCases ?_ (fun j' => ?_) j
            · simpa using hnextU
            · refine Fin.lastCases ?_ (fun k => ?_) j'
              · simpa using hxU
              · simpa using hs k)).mp hnext
      simpa only [hnextEq] using hnextMem
  · rintro ⟨hempty, hsucc⟩
    constructor
    · refine ⟨∅, hemptyU, ?_, hempty⟩
      apply (satisfiesIn_emptySetAt_iff hU (Fin.last n)
        (snoc s (∅ : ZFSet.{u})) (by
          intro j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hemptyU
          · simpa using hs k)).mpr
      simp only [snoc_last]
    · intro x hxU hxw
      refine ⟨insert x x, hsuccU x hxU, ?_, hsucc x hxU hxw⟩
      apply (satisfiesIn_successorSetAt_iff hU
        (Fin.last (n + 1)) (Fin.last n).castSucc
        (snoc (snoc s x) (insert x x)) (by
          intro j
          refine Fin.lastCases ?_ (fun j' => ?_) j
          · simpa using hsuccU x hxU
          · refine Fin.lastCases ?_ (fun k => ?_) j'
            · simpa using hxU
            · simpa using hs k)).mpr
      simp only [snoc_last, snoc_castSucc]

/-- The standard `omega` is internally inductive in every transitive carrier
that contains it and is closed under von Neumann successor. -/
private theorem omega_isInductiveSetIn (U : ZFSet.{u}) :
    IsInductiveSetIn U Ordinal.omega0.toZFSet := by
  constructor
  · rw [Ordinal.mem_toZFSet_iff]
    exact ⟨0, Ordinal.omega0_pos, Ordinal.toZFSet_zero⟩
  · intro x _hxU hxOmega
    rcases Ordinal.mem_toZFSet_iff.mp hxOmega with ⟨alpha, halpha, rfl⟩
    rw [← Ordinal.toZFSet_add_one]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (by
        rw [← Order.succ_eq_add_one]
        exact Ordinal.isSuccLimit_omega0.succ_lt halpha)

/-- Every standard natural-number ordinal belongs to an internally inductive
set. -/
private theorem natOrdinal_mem_of_isInductiveSetIn
    {U w : ZFSet.{u}} (hw : IsInductiveSetIn U w)
    (hnU : forall n : Nat, (n : Ordinal.{u}).toZFSet ∈ U)
    (n : Nat) :
    (n : Ordinal.{u}).toZFSet ∈ w := by
  induction n with
  | zero =>
      simpa only [Nat.cast_zero, Ordinal.toZFSet_zero] using hw.1
  | succ n ih =>
      have hnext := hw.2 (n : Ordinal.{u}).toZFSet (hnU n) ih
      simpa only [Nat.cast_add, Nat.cast_one, ← Ordinal.toZFSet_add_one]
        using hnext

/-- In `L_theta` for `omega < theta`, the least-inductive-set formula denotes
the actual von Neumann `omega`, not merely an internally nonstandard object. -/
private theorem satisfiesIn_omegaSetAt_iff
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (homega : Ordinal.omega0 < theta) {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : forall j, s j ∈ LStageZF theta) :
    SatisfiesIn (LStageZF theta : Set ZFSet.{u}) (omegaSetAt i) s <->
      s i = Ordinal.omega0.toZFSet := by
  let U : ZFSet.{u} := LStageZF theta
  have htrans : U.IsTransitive := LStageZF_isTransitive theta
  have hemptyU : (∅ : ZFSet.{u}) ∈ U :=
    empty_mem_LStageZF_of_isSuccLimit htheta
  have hsuccU : forall x : ZFSet.{u}, x ∈ U -> insert x x ∈ U :=
    fun x hx => MostowskiCollapse.insert_self_mem_LStageZF_of_isSuccLimit
      htheta hx
  have homegaU : Ordinal.omega0.toZFSet ∈ U :=
    ordinal_toZFSet_mem_LStageZF_of_lt homega
  have hnU : forall k : Nat, (k : Ordinal.{u}).toZFSet ∈ U := by
    intro k
    exact ordinal_toZFSet_mem_LStageZF_of_lt
      ((Ordinal.natCast_lt_omega0 k).trans homega)
  rw [omegaSetAt]
  simp only [SatisfiesIn, satisfiesIn_all_iff_CondensationFixedParameters_gch,
    satisfiesIn_imp_iff, Model.satisfiesIn_boundedAll_iff,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hInd, hminimal⟩
    have hIndRaw : IsInductiveSetIn U (s i) :=
      (satisfiesIn_inductiveSetAt_iff htrans hemptyU hsuccU i s hs).mp hInd
    have hOmegaFormula :
        SatisfiesIn (U : Set ZFSet.{u})
          (inductiveSetAt (Fin.last n))
          (snoc s Ordinal.omega0.toZFSet) :=
      (satisfiesIn_inductiveSetAt_iff htrans hemptyU hsuccU
        (Fin.last n) (snoc s Ordinal.omega0.toZFSet) (by
          intro j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa [U] using homegaU
          · simpa [U] using hs k)).mpr (by
            simpa only [snoc_last] using omega_isInductiveSetIn U)
    have hsubsetOmega := hminimal Ordinal.omega0.toZFSet homegaU hOmegaFormula
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact hsubsetOmega z (htrans.mem_trans hz (hs i)) hz
    · intro hz
      rcases Ordinal.mem_toZFSet_iff.mp hz with ⟨alpha, halpha, rfl⟩
      rcases Ordinal.lt_omega0.mp halpha with ⟨k, rfl⟩
      exact natOrdinal_mem_of_isInductiveSetIn hIndRaw hnU k
  · intro hsi
    constructor
    · apply (satisfiesIn_inductiveSetAt_iff htrans hemptyU hsuccU i s hs).mpr
      simpa only [hsi] using omega_isInductiveSetIn U
    · intro w hwU hwFormula z hzU hzOmega
      have hwInd : IsInductiveSetIn U w := by
        simpa only [snoc_last] using
          (satisfiesIn_inductiveSetAt_iff htrans hemptyU hsuccU
          (Fin.last n) (snoc s w) (by
            intro j
            refine Fin.lastCases ?_ (fun k => ?_) j
            · simpa [U] using hwU
            · simpa [U] using hs k)).mp hwFormula
      rw [hsi] at hzOmega
      rcases Ordinal.mem_toZFSet_iff.mp hzOmega with ⟨alpha, halpha, rfl⟩
      rcases Ordinal.lt_omega0.mp halpha with ⟨k, rfl⟩
      exact natOrdinal_mem_of_isInductiveSetIn hwInd hnU k

/-- Exact `L_theta` semantics of the canonical thirteen-parameter matrix.
The quantifier hypotheses are explicit: all free coordinates must be elements
of the stage in which the formula is evaluated. -/
private theorem satisfiesIn_canonicalStageParametersFormula_iff
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (homega : Ordinal.omega0 < theta)
    (s : Tuple ZFSet.{u} 13)
    (hs : forall i, s i ∈ LStageZF theta) :
    SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        canonicalStageParametersFormula s <->
      s = stageHistoryFixedParametersRaw := by
  simp only [canonicalStageParametersFormula, SatisfiesIn]
  rw [satisfiesIn_emptySetAt_iff (LStageZF_isTransitive theta)
      (0 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (1 : Fin 13) (0 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (4 : Fin 13) (3 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (5 : Fin 13) (4 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (6 : Fin 13) (5 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (7 : Fin 13) (6 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (8 : Fin 13) (7 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (9 : Fin 13) (8 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (10 : Fin 13) (9 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (11 : Fin 13) (10 : Fin 13) s hs]
  rw [satisfiesIn_omegaSetAt_iff htheta homega (12 : Fin 13) s hs]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10, h11, h12⟩
    let sL : Tuple LCarrier.{u} 13 :=
      fun i => ⟨s i, mem_L_of_mem (hs i) (LStageZF_mem_L theta)⟩
    have hsLFormula :
        FOFormula.Satisfies lCarrierMem
          canonicalStageParametersFormula sL := by
      simp only [canonicalStageParametersFormula, FOFormula.Satisfies,
        satisfies_emptySetAt, satisfies_successorSetAt,
        satisfies_omegaSetAt]
      simpa only [sL, Subtype.ext_iff, successorLCarrier_val,
        emptyLCarrier, omegaLCarrier] using
        ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
          h10, h11, h12⟩
    have hsLEq : sL = stageHistoryFixedParameters :=
      (satisfies_canonicalStageParametersFormula sL).mp hsLFormula
    funext i
    have hi := congrArg (fun t : Tuple LCarrier.{u} 13 => (t i).1) hsLEq
    simpa only [sL, stageHistoryFixedParametersRaw] using hi
  · intro hsEq
    rw [hsEq]
    have hfixedFormula :
        FOFormula.Satisfies lCarrierMem
          canonicalStageParametersFormula
          (stageHistoryFixedParameters : Tuple LCarrier.{u} 13) :=
      (satisfies_canonicalStageParametersFormula
        stageHistoryFixedParameters).mpr rfl
    simp only [canonicalStageParametersFormula, FOFormula.Satisfies,
      satisfies_emptySetAt, satisfies_successorSetAt,
      satisfies_omegaSetAt] at hfixedFormula
    simpa only [stageHistoryFixedParametersRaw, Subtype.ext_iff,
      successorLCarrier_val, emptyLCarrier, omegaLCarrier] using
      hfixedFormula

/-!
The next definition is the actual sentence used for the Tarski--Vaught
transfer.  It has arity zero: none of the thirteen constants occurs as a free
parameter.  The conversion through Mathlib syntax is only a hygienic way of
binding the complete tuple with `exs`.
-/



/-- Full elementarity pulls every canonical evaluator constant into the
smaller domain.  No reflection-level hypothesis and no canonical constant as
a free formula parameter is used. -/
private theorem stageHistoryFixedParameters_mem_of_elementary_limit
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (htheta : Order.IsSuccLimit theta)
    (homega : Ordinal.omega0 < theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u})) :
    forall i : Fin 13,
      (stageHistoryFixedParameters.{u} i).1 ∈ domain := by
  let fixed : Tuple ZFSet.{u} 13 := stageHistoryFixedParametersRaw
  have hfixedTheta : forall i, fixed i ∈ LStageZF theta := by
    intro i
    exact stageHistoryFixedParameters_mem_LStageZF_of_omega_lt homega i
  let FixedTheta : Tuple (StageCarrier theta) 13 :=
    fun i => ⟨fixed i, hfixedTheta i⟩
  letI stageStructure :
      FirstOrder.Language.setTheory.Structure (StageCarrier theta) :=
    FirstOrder.Language.setTheoryStructure
      (fun x y : StageCarrier theta => x.1 ∈ y.1)
  have hcanonicalTheta :
      SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        canonicalStageParametersFormula fixed :=
    (satisfiesIn_canonicalStageParametersFormula_iff
      htheta homega fixed hfixedTheta).mpr rfl
  have hcanonicalThetaTyped :
      FOFormula.Satisfies
        (fun x y : StageCarrier theta => x.1 ∈ y.1)
        canonicalStageParametersFormula FixedTheta := by
    apply (satisfies_stageCarrier_iff_satisfiesIn
      canonicalStageParametersFormula FixedTheta).mpr
    simpa only [FixedTheta, fixed] using hcanonicalTheta
  have hboundedTheta :
      realizes
        (fun x y : StageCarrier theta => x.1 ∈ y.1)
        (toBoundedFormula canonicalStageParametersFormula) FixedTheta :=
    (realizes_toBoundedFormula
      (fun x y : StageCarrier theta => x.1 ∈ y.1)
      canonicalStageParametersFormula FixedTheta).mpr
      hcanonicalThetaTyped
  let emptyTheta : Tuple (StageCarrier theta) 0 := fun i => Fin.elim0 i
  have hexBoundedTheta :
      realizes
        (fun x y : StageCarrier theta => x.1 ∈ y.1)
        ((toBoundedFormula canonicalStageParametersFormula).exs)
        emptyTheta := by
    change ((toBoundedFormula canonicalStageParametersFormula).exs).Realize
      Empty.elim
    rw [FirstOrder.Language.BoundedFormula.realize_exs]
    exact ⟨FixedTheta, hboundedTheta⟩
  have hclosedThetaTyped :
      FOFormula.Satisfies
        (fun x y : StageCarrier theta => x.1 ∈ y.1)
        canonicalStageParametersExistFormula emptyTheta := by
    exact (realize_fromBoundedFormula
      (fun x y : StageCarrier theta => x.1 ∈ y.1)
      ((toBoundedFormula canonicalStageParametersFormula).exs)
      emptyTheta).mp hexBoundedTheta
  let emptyRaw : Tuple ZFSet.{u} 0 := fun i => Fin.elim0 i
  have hclosedTheta :
      SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        canonicalStageParametersExistFormula emptyRaw := by
    apply (satisfies_stageCarrier_iff_satisfiesIn
      canonicalStageParametersExistFormula emptyTheta).mp
    simpa only [emptyTheta, emptyRaw] using hclosedThetaTyped
  have hclosedDomain :
      SatisfiesIn (domain : Set ZFSet.{u})
        canonicalStageParametersExistFormula emptyRaw :=
    (helem canonicalStageParametersExistFormula emptyRaw
      (fun i => Fin.elim0 i)).mpr hclosedTheta
  let DomainCarrier := ClassCarrier (domain : Set ZFSet.{u})
  letI domainStructure :
      FirstOrder.Language.setTheory.Structure DomainCarrier :=
    FirstOrder.Language.setTheoryStructure
      (fun x y : DomainCarrier => x.1 ∈ y.1)
  let emptyDomain : Tuple DomainCarrier 0 := fun i => Fin.elim0 i
  have hclosedDomainTyped :
      FOFormula.Satisfies
        (fun x y : DomainCarrier => x.1 ∈ y.1)
        canonicalStageParametersExistFormula emptyDomain := by
    apply (satisfies_subtype_iff_satisfiesIn
      (domain : Set ZFSet.{u}) canonicalStageParametersExistFormula
      emptyDomain).mpr
    rw [show (fun i => (emptyDomain i).1) = emptyRaw by
      exact Subsingleton.elim _ _]
    exact hclosedDomain
  have hexBoundedDomain :
      realizes
        (fun x y : DomainCarrier => x.1 ∈ y.1)
        ((toBoundedFormula canonicalStageParametersFormula).exs)
        emptyDomain := by
    exact (realize_fromBoundedFormula
      (fun x y : DomainCarrier => x.1 ∈ y.1)
      ((toBoundedFormula canonicalStageParametersFormula).exs)
      emptyDomain).mpr hclosedDomainTyped
  change ((toBoundedFormula canonicalStageParametersFormula).exs).Realize
    Empty.elim at hexBoundedDomain
  rw [FirstOrder.Language.BoundedFormula.realize_exs] at hexBoundedDomain
  rcases hexBoundedDomain with ⟨sDomain, hsDomainBounded⟩
  have hsDomainTyped :
      FOFormula.Satisfies
        (fun x y : DomainCarrier => x.1 ∈ y.1)
        canonicalStageParametersFormula sDomain := by
    exact (realizes_toBoundedFormula
      (fun x y : DomainCarrier => x.1 ∈ y.1)
      canonicalStageParametersFormula sDomain).mp hsDomainBounded
  let sRaw : Tuple ZFSet.{u} 13 := fun i => (sDomain i).1
  have hsDomainRaw :
      SatisfiesIn (domain : Set ZFSet.{u})
        canonicalStageParametersFormula sRaw := by
    exact (satisfies_subtype_iff_satisfiesIn
      (domain : Set ZFSet.{u}) canonicalStageParametersFormula
      sDomain).mp hsDomainTyped
  have hsThetaRaw :
      SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        canonicalStageParametersFormula sRaw :=
    (helem canonicalStageParametersFormula sRaw
      (fun i => (sDomain i).2)).mp hsDomainRaw
  have hsEq : sRaw = stageHistoryFixedParametersRaw :=
    (satisfiesIn_canonicalStageParametersFormula_iff
      htheta homega sRaw (fun i => hsubset (sDomain i).2)).mp hsThetaRaw
  intro i
  have hvalue :
      (sDomain i).1 = (stageHistoryFixedParameters.{u} i).1 := by
    exact congrArg (fun t : Tuple ZFSet.{u} 13 => t i) hsEq
  rw [← hvalue]
  exact (sDomain i).2

end

end Model

end Constructible

end
end GCHSource_Work_CUGCH_CondensationFixedParameters

/- Source module: Solutions.Work_CUGCH_CondensationBareStage -/
section GCHSource_Work_CUGCH_CondensationBareStage
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# Condensation from a locally correct relation-free stage predicate

The central hypothesis in this file is deliberately an exact semantic
contract, not a renamed reflection hypothesis.  `BareStageCorrectAt theta`
says that, for every ordinal code and candidate stage which belong to
`L_theta`, the relation-free first-order stage formula holds in `L_theta` if
and only if the candidate is the externally constructed `L_alpha`.

From that biconditional and full elementarity, this file derives the three
stage interfaces used by the usual Mostowski-collapse proof.  The remaining
task for arbitrary limit levels above `omega` is therefore stated without
ambiguity: prove `BareStageCorrectAt theta` from the ordinary limit
hypothesis.  No theorem in this file silently assumes that implication.
-/

section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section

namespace BareStageCondensation





/-- An ordinal code in `L_theta` has index strictly below `theta`. -/
private theorem ordinal_lt_of_toZFSet_mem_LStageZF
    {theta alpha : Ordinal.{u}}
    (halpha : alpha.toZFSet ∈ LStageZF theta) : alpha < theta := by
  have hrank := (ordinal_stage_invariants theta).1
    (ZFSet.isOrdinal_toZFSet alpha) halpha
  have heq : (alpha.toZFSet : ZFSet.{u}).rank = alpha := by
    apply Ordinal.toZFSet_injective
    exact (ZFSet.isOrdinal_toZFSet alpha).toZFSet_rank_eq
  simpa only [heq] using hrank

/-- Every correctly indexed actual stage is itself available in the ambient
level. -/
private theorem actualStage_mem_of_index_mem
    {theta alpha : Ordinal.{u}}
    (halpha : alpha.toZFSet ∈ LStageZF theta) :
    LStageZF alpha ∈ LStageZF theta :=
  LStageZF_mem_of_lt (ordinal_lt_of_toZFSet_mem_LStageZF halpha)







private theorem bareConstructibleStageRename_assignment
    (x index stage : ZFSet.{u}) :
    (fun i => bareConstructibleWitnessAssignment x index stage
      (Model.constructibleInternalStageRename i)) =
      bareStageAssignment index stage := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · have hrename :
        Model.constructibleInternalStageRename i13.castSucc.castSucc =
          i13.castSucc.castSucc.castSucc := by
        simp only [Model.constructibleInternalStageRename,
          Fin.lastCases_castSucc]
        apply Fin.ext
        rfl
      rw [hrename]
      simp [bareConstructibleWitnessAssignment,
        bareConstructibleParameters, bareStageAssignment]

/-- Full elementarity and exact local correctness put every internally
indexed constructible level into the elementary domain. -/
private theorem stage_mem
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u}))
    (hfixed : ∀ i : Fin 13,
      (Model.stageHistoryFixedParameters.{u} i).1 ∈ domain)
    (hcorrect : BareStageCorrectAt theta)
    (alpha : Ordinal.{u}) (halpha : alpha.toZFSet ∈ domain) :
    LStageZF alpha ∈ domain := by
  let params : Tuple ZFSet.{u} 14 :=
    snoc (fun i => (Model.stageHistoryFixedParameters.{u} i).1)
      alpha.toZFSet
  have hparamsDomain : ∀ i, params i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact halpha
    · simpa [params] using hfixed j
  have halphaTheta : alpha.toZFSet ∈ LStageZF theta := hsubset halpha
  have hstageTheta : LStageZF alpha ∈ LStageZF theta :=
    actualStage_mem_of_index_mem halphaTheta
  have hstageSatTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        Model.bareStageAtFormula
        (bareStageAssignment alpha.toZFSet (LStageZF alpha)) :=
    (hcorrect alpha (LStageZF alpha) halphaTheta hstageTheta).mpr rfl
  have hexTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (.ex Model.bareStageAtFormula) params := by
    refine ⟨LStageZF alpha, hstageTheta, ?_⟩
    simpa [params, bareStageAssignment] using hstageSatTheta
  have hexDomain :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        (.ex Model.bareStageAtFormula) params :=
    (helem (.ex Model.bareStageAtFormula) params hparamsDomain).mpr hexTheta
  rcases hexDomain with ⟨stage, hstageDomain, hstageSatDomain⟩
  change stage ∈ domain at hstageDomain
  have hfullDomain : ∀ i, snoc params stage i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hstageDomain
    · simpa using hparamsDomain j
  have hstageSatTheta' :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        Model.bareStageAtFormula (snoc params stage) :=
    (helem Model.bareStageAtFormula (snoc params stage)
      hfullDomain).mp hstageSatDomain
  have hstageEq : stage = LStageZF alpha :=
    (hcorrect alpha stage halphaTheta (hsubset hstageDomain)).mp
      (by simpa [params, bareStageAssignment] using hstageSatTheta')
  simpa only [← hstageEq] using hstageDomain

/-- Exact local correctness reflects a stage containing each domain member,
with the ordinal index itself in the domain. -/
private theorem internallyStageCovered
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (htheta : Order.IsSuccLimit theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u}))
    (hfixed : ∀ i : Fin 13,
      (Model.stageHistoryFixedParameters.{u} i).1 ∈ domain)
    (hcorrect : BareStageCorrectAt theta) :
    InternallyStageCovered domain := by
  intro x hxDomain
  have hxTheta : x ∈ LStageZF theta := hsubset hxDomain
  rcases (mem_LStageZF_limit_iff htheta).mp hxTheta with
    ⟨alpha, halphaTheta, hxAlpha⟩
  have hindexTheta : alpha.toZFSet ∈ LStageZF theta :=
    ordinal_toZFSet_mem_LStageZF_of_lt halphaTheta
  have hstageTheta : LStageZF alpha ∈ LStageZF theta :=
    LStageZF_mem_of_lt halphaTheta
  let params := bareConstructibleParameters x
  let full := bareConstructibleWitnessAssignment
    x alpha.toZFSet (LStageZF alpha)
  have hfullTheta : ∀ i, full i ∈ LStageZF theta := by
    intro i
    refine Fin.lastCases ?_ (fun i15 => ?_) i
    · exact hstageTheta
    · refine Fin.lastCases ?_ (fun i14 => ?_) i15
      · exact hindexTheta
      · refine Fin.lastCases ?_ (fun i13 => ?_) i14
        · exact hxTheta
        · simpa [full, bareConstructibleWitnessAssignment,
            bareConstructibleParameters] using hsubset (hfixed i13)
  have hordinalTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (Model.ordinalAt (14 : Fin 16)) full :=
    (CondensationHull.satisfiesIn_ordinalAt_iff
      (LStageZF_isTransitive theta) (14 : Fin 16) full hfullTheta).mpr
      (ZFSet.isOrdinal_toZFSet alpha)
  have hstageThetaSat :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (FOFormula.rename Model.constructibleInternalStageRename
          Model.bareStageAtFormula) full := by
    rw [Model.satisfiesIn_rename,
      bareConstructibleStageRename_assignment]
    exact (hcorrect alpha (LStageZF alpha)
      hindexTheta hstageTheta).mpr rfl
  have hformulaTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        bareConstructibleFormula params := by
    exact ⟨alpha.toZFSet, hindexTheta, LStageZF alpha, hstageTheta,
      hordinalTheta, hstageThetaSat, hxAlpha⟩
  have hparamsDomain : ∀ i, params i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hxDomain
    · simpa [params, bareConstructibleParameters] using hfixed j
  have hformulaDomain :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        bareConstructibleFormula params :=
    (helem bareConstructibleFormula params hparamsDomain).mpr hformulaTheta
  rcases hformulaDomain with
    ⟨index, hindexDomain, stage, hstageDomain,
      hindexFormula, hstageFormula, hxStage⟩
  change index ∈ domain at hindexDomain
  change stage ∈ domain at hstageDomain
  change x ∈ stage at hxStage
  let full' := bareConstructibleWitnessAssignment x index stage
  have hfull'Domain : ∀ i, full' i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun i15 => ?_) i
    · exact hstageDomain
    · refine Fin.lastCases ?_ (fun i14 => ?_) i15
      · exact hindexDomain
      · refine Fin.lastCases ?_ (fun i13 => ?_) i14
        · exact hxDomain
        · simpa [full', bareConstructibleWitnessAssignment,
            bareConstructibleParameters] using hfixed i13
  have hindexThetaFormula :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (Model.ordinalAt (14 : Fin 16)) full' :=
    (helem (Model.ordinalAt (14 : Fin 16)) full' hfull'Domain).mp
      (by simpa [full', params,
          bareConstructibleWitnessAssignment] using hindexFormula)
  have hindexOrdinal : index.IsOrdinal :=
    (CondensationHull.satisfiesIn_ordinalAt_iff
      (LStageZF_isTransitive theta) (14 : Fin 16) full'
      (fun i => hsubset (hfull'Domain i))).mp hindexThetaFormula
  let alpha' : Ordinal.{u} := index.rank
  have hindexEq : index = alpha'.toZFSet :=
    hindexOrdinal.toZFSet_rank_eq.symm
  have hstageDirectDomain :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        Model.bareStageAtFormula (bareStageAssignment index stage) := by
    have hrenamed :=
      (Model.satisfiesIn_rename (domain : Set ZFSet.{u})
        Model.bareStageAtFormula Model.constructibleInternalStageRename
        full').mp (by simpa [full', params,
          bareConstructibleWitnessAssignment] using hstageFormula)
    rw [bareConstructibleStageRename_assignment] at hrenamed
    exact hrenamed
  have hstageParamsDomain : ∀ i,
      bareStageAssignment index stage i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun i14 => ?_) i
    · exact hstageDomain
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · exact hindexDomain
      · simpa [bareStageAssignment] using hfixed i13
  have hstageThetaFormula :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        Model.bareStageAtFormula (bareStageAssignment index stage) :=
    (helem Model.bareStageAtFormula (bareStageAssignment index stage)
      hstageParamsDomain).mp hstageDirectDomain
  have hstageEq : stage = LStageZF alpha' :=
    (hcorrect alpha' stage
      (hsubset (by simpa only [← hindexEq] using hindexDomain))
      (hsubset hstageDomain)).mp
      (by simpa only [← hindexEq] using hstageThetaFormula)
  refine ⟨alpha', ?_, ?_⟩
  · simpa only [← hindexEq] using hindexDomain
  · simpa only [← hstageEq] using hxStage

/-! ## Bounded earlier-stage witnesses -/







private theorem bareBoundedStageRename_assignment
    (x bound index stage : ZFSet.{u}) :
    (fun i => bareBoundedStageWitnessAssignment x bound index stage
      (bareBoundedStageRename i)) =
      bareStageAssignment index stage := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · have hrename :
        bareBoundedStageRename i13.castSucc.castSucc =
          i13.castSucc.castSucc.castSucc.castSucc := by
        simp only [bareBoundedStageRename, Fin.lastCases_castSucc]
        apply Fin.ext
        rfl
      rw [hrename]
      simp [bareBoundedStageWitnessAssignment,
        bareBoundedStageParameters, bareStageAssignment]



/-- Exact stage correctness supplies the bounded witness needed at a limit
index in the elementary domain. -/
private theorem smallerStageWitnesses
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u}))
    (hfixed : ∀ i : Fin 13,
      (Model.stageHistoryFixedParameters.{u} i).1 ∈ domain)
    (hcorrect : BareStageCorrectAt theta)
    (limit : Ordinal.{u}) (hlimit : Order.IsSuccLimit limit)
    (hlimitDomain : limit.toZFSet ∈ domain) :
    HasSmallerInternalLStageWitnesses domain limit := by
  intro x hxDomain hxLimit
  rcases (mem_LStageZF_limit_iff hlimit).mp hxLimit with
    ⟨delta, hdeltaLimit, hxDelta⟩
  have hlimitTheta : limit.toZFSet ∈ LStageZF theta :=
    hsubset hlimitDomain
  have hlimitLtTheta : limit < theta :=
    ordinal_lt_of_toZFSet_mem_LStageZF hlimitTheta
  have hdeltaTheta : delta.toZFSet ∈ LStageZF theta :=
    ordinal_toZFSet_mem_LStageZF_of_lt
      (hdeltaLimit.trans hlimitLtTheta)
  have hstageTheta : LStageZF delta ∈ LStageZF theta :=
    LStageZF_mem_of_lt (hdeltaLimit.trans hlimitLtTheta)
  let params := bareBoundedStageParameters x limit.toZFSet
  let full := bareBoundedStageWitnessAssignment
    x limit.toZFSet delta.toZFSet (LStageZF delta)
  have hfullTheta : ∀ i, full i ∈ LStageZF theta := by
    intro i
    refine Fin.lastCases ?_ (fun i16 => ?_) i
    · exact hstageTheta
    · refine Fin.lastCases ?_ (fun i15 => ?_) i16
      · exact hdeltaTheta
      · refine Fin.lastCases ?_ (fun i14 => ?_) i15
        · exact hlimitTheta
        · refine Fin.lastCases ?_ (fun i13 => ?_) i14
          · exact hsubset hxDomain
          · simpa [full, bareBoundedStageWitnessAssignment,
              bareBoundedStageParameters] using hsubset (hfixed i13)
  have hordinalTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (Model.ordinalAt (15 : Fin 17)) full :=
    (CondensationHull.satisfiesIn_ordinalAt_iff
      (LStageZF_isTransitive theta) (15 : Fin 17) full hfullTheta).mpr
      (ZFSet.isOrdinal_toZFSet delta)
  have hstageThetaSat :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (FOFormula.rename bareBoundedStageRename
          Model.bareStageAtFormula) full := by
    rw [Model.satisfiesIn_rename, bareBoundedStageRename_assignment]
    exact (hcorrect delta (LStageZF delta)
      hdeltaTheta hstageTheta).mpr rfl
  have hformulaTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        bareBoundedStageContainsFormula params := by
    exact ⟨delta.toZFSet, hdeltaTheta, LStageZF delta, hstageTheta,
      Ordinal.toZFSet_mem_toZFSet_iff.mpr hdeltaLimit,
      hordinalTheta, hstageThetaSat, hxDelta⟩
  have hparamsDomain : ∀ i, params i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun i14 => ?_) i
    · exact hlimitDomain
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · exact hxDomain
      · simpa [params, bareBoundedStageParameters] using hfixed i13
  have hformulaDomain :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        bareBoundedStageContainsFormula params :=
    (helem bareBoundedStageContainsFormula params hparamsDomain).mpr
      hformulaTheta
  rcases hformulaDomain with
    ⟨index, hindexDomain, stage, hstageDomain,
      hindexBound, hindexFormula, hstageFormula, hxStage⟩
  change index ∈ domain at hindexDomain
  change stage ∈ domain at hstageDomain
  change index ∈ limit.toZFSet at hindexBound
  change x ∈ stage at hxStage
  let full' := bareBoundedStageWitnessAssignment
    x limit.toZFSet index stage
  have hfull'Domain : ∀ i, full' i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun i16 => ?_) i
    · exact hstageDomain
    · refine Fin.lastCases ?_ (fun i15 => ?_) i16
      · exact hindexDomain
      · refine Fin.lastCases ?_ (fun i14 => ?_) i15
        · exact hlimitDomain
        · refine Fin.lastCases ?_ (fun i13 => ?_) i14
          · exact hxDomain
          · simpa [full', bareBoundedStageWitnessAssignment,
              bareBoundedStageParameters] using hfixed i13
  have hindexThetaFormula :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (Model.ordinalAt (15 : Fin 17)) full' :=
    (helem (Model.ordinalAt (15 : Fin 17)) full' hfull'Domain).mp
      (by simpa [full', params,
          bareBoundedStageWitnessAssignment] using hindexFormula)
  have hindexOrdinal : index.IsOrdinal :=
    (CondensationHull.satisfiesIn_ordinalAt_iff
      (LStageZF_isTransitive theta) (15 : Fin 17) full'
      (fun i => hsubset (hfull'Domain i))).mp hindexThetaFormula
  let delta' : Ordinal.{u} := index.rank
  have hindexEq : index = delta'.toZFSet :=
    hindexOrdinal.toZFSet_rank_eq.symm
  have hstageDirectDomain :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        Model.bareStageAtFormula (bareStageAssignment index stage) := by
    have hrenamed :=
      (Model.satisfiesIn_rename (domain : Set ZFSet.{u})
        Model.bareStageAtFormula bareBoundedStageRename full').mp
        (by simpa [full', params,
            bareBoundedStageWitnessAssignment] using hstageFormula)
    rw [bareBoundedStageRename_assignment] at hrenamed
    exact hrenamed
  have hstageParamsDomain : ∀ i,
      bareStageAssignment index stage i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun i14 => ?_) i
    · exact hstageDomain
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · exact hindexDomain
      · simpa [bareStageAssignment] using hfixed i13
  have hstageThetaFormula :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        Model.bareStageAtFormula (bareStageAssignment index stage) :=
    (helem Model.bareStageAtFormula (bareStageAssignment index stage)
      hstageParamsDomain).mp hstageDirectDomain
  have hstageEq : stage = LStageZF delta' :=
    (hcorrect delta' stage
      (hsubset (by simpa only [← hindexEq] using hindexDomain))
      (hsubset hstageDomain)).mp
      (by simpa only [← hindexEq] using hstageThetaFormula)
  refine ⟨delta', ?_, ?_, ?_⟩
  · exact Ordinal.toZFSet_mem_toZFSet_iff.mp
      (by simpa only [← hindexEq] using hindexBound)
  · simpa only [← hindexEq] using hindexDomain
  · simpa only [← hstageEq] using hxStage

/-- Above `omega`, exact local correctness of the bare stage predicate turns
ordinary full elementarity into every explicit interface required by the
collapse assembly. -/
private theorem stageInterfaces_of_fixedParameters
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (htheta : Order.IsSuccLimit theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u}))
    (hfixedDomain : ∀ i : Fin 13,
      (Model.stageHistoryFixedParameters.{u} i).1 ∈ domain)
    (hcorrect : BareStageCorrectAt theta) :
    StageCondensationInterfaces theta domain := by
  exact
    { isLimit := htheta
      subset_stage := hsubset
      satisfactionAbsolute := helem
      empty_mem := by
        have hempty := hfixedDomain (2 : Fin 13)
        rw [Model.stageHistoryFixedParameters_empty] at hempty
        exact hempty
      stage_mem := stage_mem hsubset helem hfixedDomain hcorrect
      internallyStageCovered :=
        internallyStageCovered htheta hsubset helem hfixedDomain hcorrect
      smallerStageWitnesses := by
        intro limit hlimit hlimitDomain
        exact smallerStageWitnesses hsubset helem hfixedDomain hcorrect
          limit hlimit hlimitDomain }

/-- Above `omega`, the canonical fixed parameters follow from ordinary full
elementarity.  Consequently exact local correctness of the bare stage
formula is the only remaining premise needed by the transparent assembly. -/
private theorem stageInterfaces_of_bareStageCorrect
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (htheta : Order.IsSuccLimit theta)
    (homega : Ordinal.omega0 < theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u}))
    (hcorrect : BareStageCorrectAt theta) :
    StageCondensationInterfaces theta domain :=
  stageInterfaces_of_fixedParameters htheta hsubset helem
    (Model.stageHistoryFixedParameters_mem_of_elementary_limit
      htheta homega hsubset helem)
    hcorrect



end BareStageCondensation

end

end MostowskiCollapse

end Constructible

end
end GCHSource_Work_CUGCH_CondensationBareStage

/- Source module: Solutions.Work_CUGCH_BareStageCorrect -/
section GCHSource_Work_CUGCH_BareStageCorrect
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# From canonical history bounds to exact bare-stage correctness

This file connects the two independent parts of the relation-free stage
argument to the existing, standard `BareStageCorrectAt` contract.

The hypotheses remain explicit:

* the canonical evaluator parameters belong to `L_theta`;
* the internally evaluated successor output is the ambient `godelDef`;
* for every `alpha < theta`, the actual canonical history through `alpha`
  belongs to `L_theta`.

The conclusion is not a weakened replacement: it is exactly
`BareStageCorrectAt theta`, the biconditional used by the Condensation
assembly.
-/

section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section

namespace BareStageCondensation

private theorem bareStageAssignment_eq_raw
    (index stage : ZFSet.{u}) :
    bareStageAssignment index stage =
      Model.bareStageAtRawAssignment
        Model.stageHistoryFixedParametersRaw index stage := by
  rfl

/-- Exact final bridge with the local history bound stated directly at the
ambient level `L_theta`. -/
private theorem bareStageCorrectAt_of_canonicalHistory_mem
    (theta : Ordinal.{u})
    (hfixed : ∀ i : Fin 13,
      Model.stageHistoryFixedParametersRaw.{u} i ∈ LStageZF theta)
    (hevaluator : Model.BareGodelDefOutputCorrectIn
      (LStageZF theta) Model.stageHistoryFixedParametersRaw)
    (hhistory : ∀ alpha : Ordinal.{u}, alpha < theta →
      Model.canonicalBareHistory alpha ∈ LStageZF theta) :
    BareStageCorrectAt theta := by
  intro alpha stage hindex hstage
  have halpha : alpha < theta :=
    ordinal_lt_of_toZFSet_mem_LStageZF hindex
  have hsemantic :=
    Model.satisfiesIn_bareStageAtFormula_ordinal_iff_of_canonicalHistory_mem
      (LStageZF_isTransitive theta)
      Model.stageHistoryFixedParametersRaw hfixed
      Model.stageHistoryFixedParametersRaw_empty hevaluator
      alpha stage hindex hstage (hhistory alpha halpha)
  simpa only [bareStageAssignment_eq_raw] using hsemantic

/-- The usual invariant `H_alpha ∈ L_(alpha + omega)` supplies the direct
history premise at every nonzero limit `theta`. -/
private theorem bareStageCorrectAt_of_add_omega_history_bound
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (hfixed : ∀ i : Fin 13,
      Model.stageHistoryFixedParametersRaw.{u} i ∈ LStageZF theta)
    (hevaluator : Model.BareGodelDefOutputCorrectIn
      (LStageZF theta) Model.stageHistoryFixedParametersRaw)
    (hhistoryBound : ∀ alpha : Ordinal.{u},
      Model.canonicalBareHistory alpha ∈
        LStageZF (alpha + Ordinal.omega0)) :
    BareStageCorrectAt theta := by
  apply bareStageCorrectAt_of_canonicalHistory_mem theta
    hfixed hevaluator
  intro alpha halpha
  exact LStageZF_mono
    (Model.add_omega_le_of_lt_isSuccLimit htheta halpha)
    (hhistoryBound alpha)

/-- Above `omega`, canonical fixed-parameter membership is automatic.  Thus
evaluator correctness and the honest canonical-history bound are precisely
the two remaining mathematical inputs to exact local stage correctness. -/
private theorem bareStageCorrectAt_of_evaluator_and_history_bounds
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (homega : Ordinal.omega0 < theta)
    (hevaluator : Model.BareGodelDefOutputCorrectIn
      (LStageZF theta) Model.stageHistoryFixedParametersRaw)
  (hhistoryBound : ∀ alpha : Ordinal.{u},
      Model.canonicalBareHistory alpha ∈
        LStageZF (alpha + Ordinal.omega0)) :
    BareStageCorrectAt theta := by
  apply bareStageCorrectAt_of_add_omega_history_bound htheta
    (hevaluator := hevaluator)
  · intro i
    simpa only [Model.stageHistoryFixedParametersRaw] using
      (Model.stageHistoryFixedParameters_mem_LStageZF_of_omega_lt
        homega i)
  · exact hhistoryBound



end BareStageCondensation

end

end MostowskiCollapse

end Constructible

end
end GCHSource_Work_CUGCH_BareStageCorrect

/- Source module: Solutions.Work_CUGCH_CondensationOmega -/
section GCHSource_Work_CUGCH_CondensationOmega
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Condensation at the first limit level

This file proves the `theta = omega` case of the standard Condensation
Lemma.  The proof does not use the fixed evaluator parameters from the
reflection-level argument: the standard omega level does not contain its own
omega.  Instead it uses the ordinary fact that `L_omega` consists of
hereditarily finite sets and is therefore pointwise generated from the empty
set by finite insertion.
-/

section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section

namespace OmegaCondensation



/-- The internal powerset of an externally finite `ZFSet` has only finitely
many members externally. -/
private theorem externallyFinite_powerset {a : ZFSet.{u}}
    (ha : ExternallyFinite a) : ExternallyFinite a.powerset := by
  classical
  let code : ZFSet.{u} -> Finset ZFSet.{u} :=
    fun z => ha.toFinset.filter fun x => x ∈ z
  have himage :
      code '' (a.powerset : Set ZFSet.{u}) ⊆
        (↑(ha.toFinset.powerset) : Set (Finset ZFSet.{u})) := by
    rintro t ⟨z, _hz, rfl⟩
    change code z ∈ ha.toFinset.powerset
    rw [Finset.mem_powerset]
    intro x hx
    exact (Finset.mem_filter.mp (by simpa only [code] using hx)).1
  apply Set.Finite.of_finite_image
    ((Finset.finite_toSet ha.toFinset.powerset).subset himage)
  intro x hx y hy hxy
  have hxsub : x ⊆ a := ZFSet.mem_powerset.mp hx
  have hysub : y ⊆ a := ZFSet.mem_powerset.mp hy
  apply ZFSet.ext
  intro z
  have hzx : z ∈ code x ↔ z ∈ x := by
    constructor
    · exact fun hz => (Finset.mem_filter.mp
        (by simpa only [code] using hz)).2
    · intro hz
      simpa only [code] using (Finset.mem_filter.mpr
        ⟨ha.mem_toFinset.mpr (hxsub hz), hz⟩)
  have hzy : z ∈ code y ↔ z ∈ y := by
    constructor
    · exact fun hz => (Finset.mem_filter.mp
        (by simpa only [code] using hz)).2
    · intro hz
      simpa only [code] using (Finset.mem_filter.mpr
        ⟨ha.mem_toFinset.mpr (hysub hz), hz⟩)
  rw [← hzx, hxy, hzy]

/-- `DefZF a` is externally finite whenever `a` is externally finite. -/
private theorem externallyFinite_defZF {a : ZFSet.{u}}
    (ha : ExternallyFinite a) : ExternallyFinite (DefZF a) := by
  exact (externallyFinite_powerset ha).subset (DefZF_subset_powerset a)

/-- Every finite-indexed constructible level has finitely many members. -/
private theorem externallyFinite_LStageZF_nat (n : Nat) :
    ExternallyFinite (LStageZF (n : Ordinal.{u})) := by
  induction n with
  | zero =>
      rw [Nat.cast_zero, LStageZF_zero, ExternallyFinite]
      have hcoe : ((∅ : ZFSet.{u}) : Set ZFSet.{u}) = ∅ := by
        ext x
        simp
      rw [hcoe]
      exact Set.finite_empty
  | succ n ih =>
      rw [Nat.cast_succ, ← Order.succ_eq_add_one, LStageZF_succ]
      exact externallyFinite_defZF ih

/-- Every member of `L_omega` is externally finite.  Together with
transitivity of `L_omega`, this is precisely the hereditary-finiteness fact
needed below. -/
private theorem externallyFinite_of_mem_LStageZF_omega
    {x : ZFSet.{u}} (hx : x ∈ LStageZF (Ordinal.omega0 : Ordinal.{u})) :
    ExternallyFinite x := by
  rcases (mem_LStageZF_limit_iff Ordinal.isSuccLimit_omega0).mp hx with
    ⟨alpha, halpha, hxalpha⟩
  rcases Ordinal.lt_omega0.mp halpha with ⟨n, rfl⟩
  exact (externallyFinite_LStageZF_nat n).subset
    ((LStageZF_isTransitive (n : Ordinal.{u})).subset_of_mem hxalpha)

/-! ## Exact first-order definitions of the finite constructors -/









/-- Tarski--Vaught in the special form used below: an object uniquely
first-order definable in `big` from parameters in `small` belongs to `small`.
No definability or uniqueness is hidden in the name; both are explicit
hypotheses. -/
private theorem uniqueDefinable_mem_of_satisfactionAbsolute
    {small big : Set ZFSet.{u}} (hsubset : small ⊆ big)
    (helem : SatisfactionAbsolute small big)
    {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple ZFSet.{u} n)
    (hparams : ∀ i, params i ∈ small)
    (out : ZFSet.{u}) (hout : out ∈ big)
    (hsat : Model.SatisfiesIn big phi (snoc params out))
    (hunique : ∀ y : ZFSet.{u}, y ∈ big →
      Model.SatisfiesIn big phi (snoc params y) → y = out) :
    out ∈ small := by
  have hexBig : Model.SatisfiesIn big (.ex phi) params :=
    ⟨out, hout, hsat⟩
  have hexSmall : Model.SatisfiesIn small (.ex phi) params :=
    (helem (.ex phi) params hparams).mpr hexBig
  rcases hexSmall with ⟨y, hySmall, hySmallSat⟩
  have hsnoc : ∀ i, snoc params y i ∈ small := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hySmall
    · simpa using hparams j
  have hyBigSat : Model.SatisfiesIn big phi (snoc params y) :=
    (helem phi (snoc params y) hsnoc).mp hySmallSat
  have hyo : y = out := hunique y (hsubset hySmall) hyBigSat
  simpa only [← hyo] using hySmall

/-! ## Closure of `L_omega` and of an elementary substructure -/

/-- Inserting one member into a set already in a transitive carrier produces
a definable subset of that carrier. -/
private theorem insert_mem_DefZF_of_mem {A a b : ZFSet.{u}}
    (htrans : A.IsTransitive) (ha : a ∈ A) (hb : b ∈ A) :
    insert a b ∈ DefZF A := by
  rw [mem_DefZF_iff_exists_satisfies]
  let sa : ZFCarrier A := ⟨a, ha⟩
  let sb : ZFCarrier A := ⟨b, hb⟩
  let params : Tuple (ZFCarrier A) 2 := ![sa, sb]
  let phi : FOFormula 3 :=
    FOFormula.disj
      (.eq (Fin.last 2) (Fin.castSucc (0 : Fin 2)))
      (.mem (Fin.last 2) (Fin.castSucc (1 : Fin 2)))
  refine ⟨?_, 2, params, phi, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.mp hz with rfl | hz
    · exact ha
    · exact htrans.mem_trans hz hb
  · intro z
    rw [ZFSet.mem_insert_iff, FOFormula.satisfies_disj]
    change
      (z.1 = a ∨ z.1 ∈ b) ↔
        (snoc params z (Fin.last 2) =
            snoc params z (Fin.castSucc (0 : Fin 2)) ∨
          (snoc params z (Fin.last 2)).1 ∈
            (snoc params z (Fin.castSucc (1 : Fin 2))).1)
    simp only [snoc_last, snoc_castSucc]
    simp only [params, sa, sb, Matrix.cons_val_zero,
      Matrix.cons_val_one, Subtype.ext_iff]

/-- The empty set is a member of `L_omega`. -/
private theorem empty_mem_LStageZF_omega :
    (∅ : ZFSet.{u}) ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}) := by
  apply (mem_LStageZF_limit_iff Ordinal.isSuccLimit_omega0).mpr
  refine ⟨((1 : Nat) : Ordinal.{u}),
    Ordinal.natCast_lt_omega0 1, ?_⟩
  rw [show ((1 : Nat) : Ordinal.{u}) = Order.succ 0 by simp,
    LStageZF_succ, LStageZF_zero, DefZF_empty]
  simp

/-- `L_omega` is closed under adjoining one element to a set. -/
private theorem insert_mem_LStageZF_omega {a b : ZFSet.{u}}
    (ha : a ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}))
    (hb : b ∈ LStageZF (Ordinal.omega0 : Ordinal.{u})) :
    insert a b ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}) := by
  rcases (mem_LStageZF_limit_iff Ordinal.isSuccLimit_omega0).mp ha with
    ⟨alpha, halpha, haalpha⟩
  rcases (mem_LStageZF_limit_iff Ordinal.isSuccLimit_omega0).mp hb with
    ⟨beta, hbeta, hbbeta⟩
  let delta : Ordinal.{u} := max alpha beta
  have hdelta : delta < Ordinal.omega0 :=
    max_lt halpha hbeta
  have haDelta : a ∈ LStageZF delta :=
    LStageZF_mono (le_max_left alpha beta) haalpha
  have hbDelta : b ∈ LStageZF delta :=
    LStageZF_mono (le_max_right alpha beta) hbbeta
  apply (mem_LStageZF_limit_iff Ordinal.isSuccLimit_omega0).mpr
  refine ⟨Order.succ delta,
    Ordinal.isSuccLimit_omega0.succ_lt hdelta, ?_⟩
  rw [LStageZF_succ]
  exact insert_mem_DefZF_of_mem
    (LStageZF_isTransitive delta) haDelta hbDelta

/-- Full elementarity in `L_omega` puts the actual empty set in the smaller
structure.  Uniqueness is checked in the transitive ambient level. -/
private theorem empty_mem_of_elementary_omega {domain : ZFSet.{u}}
    (hsubset : domain ⊆ LStageZF (Ordinal.omega0 : Ordinal.{u}))
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u})) :
    (∅ : ZFSet.{u}) ∈ domain := by
  let noParams : Tuple ZFSet.{u} 0 := fun i => Fin.elim0 i
  apply uniqueDefinable_mem_of_satisfactionAbsolute
    hsubset helem emptyBody noParams
    (fun i => Fin.elim0 i) (∅ : ZFSet.{u})
    empty_mem_LStageZF_omega
  · have hraw :
        Model.SatisfiesIn
          (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u})
          emptyBody ![(∅ : ZFSet.{u})] :=
      (satisfiesIn_emptyBody_iff _ _).mpr
        (fun z _hz => ZFSet.notMem_empty z)
    have hassign :
        snoc noParams (∅ : ZFSet.{u}) = ![(∅ : ZFSet.{u})] := by
      funext i
      fin_cases i
      rfl
    rw [hassign]
    exact hraw
  · intro y hy hySat
    have hySat' :
        Model.SatisfiesIn
          (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u})
          emptyBody ![y] := by
      have hassign : snoc noParams y = ![y] := by
        funext i
        fin_cases i
        rfl
      rw [← hassign]
      exact hySat
    have hnone := (satisfiesIn_emptyBody_iff _ y).mp hySat'
    apply (ZFSet.eq_empty y).mpr
    intro z hz
    have hzOmega :
        z ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
      (LStageZF_isTransitive
        (Ordinal.omega0 : Ordinal.{u})).mem_trans hz hy
    exact hnone z hzOmega hz

/-- Full elementarity in `L_omega` is closed under the actual finite
insertion operation. -/
private theorem insert_mem_of_elementary_omega {domain : ZFSet.{u}}
    (hsubset : domain ⊆ LStageZF (Ordinal.omega0 : Ordinal.{u}))
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u}))
    {a b : ZFSet.{u}} (ha : a ∈ domain) (hb : b ∈ domain) :
    insert a b ∈ domain := by
  let params : Tuple ZFSet.{u} 2 := ![a, b]
  have haOmega := hsubset ha
  have hbOmega := hsubset hb
  have houtOmega :
      insert a b ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
    insert_mem_LStageZF_omega haOmega hbOmega
  refine uniqueDefinable_mem_of_satisfactionAbsolute
    hsubset helem insertBody params ?_ (insert a b) houtOmega ?_ ?_
  · intro i
    fin_cases i
    · change a ∈ domain
      exact ha
    · change b ∈ domain
      exact hb
  · have hraw :
        Model.SatisfiesIn
          (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u})
          insertBody ![a, b, insert a b] :=
      (satisfiesIn_insertBody_iff _ _ _ _).mpr
        (fun z _hz => ZFSet.mem_insert_iff)
    have hassign :
        snoc params (insert a b) = ![a, b, insert a b] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    exact hraw
  · intro y hyOmega hySat
    have hySat' :
        Model.SatisfiesIn
          (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u})
          insertBody ![a, b, y] := by
      have hassign : snoc params y = ![a, b, y] := by
        funext i
        fin_cases i <;> rfl
      rw [← hassign]
      exact hySat
    have hcharacterization :=
      (satisfiesIn_insertBody_iff _ a b y).mp hySat'
    apply ZFSet.ext
    intro z
    constructor
    · intro hzy
      have hzOmega :
          z ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
        (LStageZF_isTransitive
          (Ordinal.omega0 : Ordinal.{u})).mem_trans hzy hyOmega
      exact ZFSet.mem_insert_iff.mpr
        ((hcharacterization z hzOmega).mp hzy)
    · intro hzInsert
      have hzOmega :
          z ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
        (LStageZF_isTransitive
          (Ordinal.omega0 : Ordinal.{u})).mem_trans hzInsert houtOmega
      exact (hcharacterization z hzOmega).mpr
        (ZFSet.mem_insert_iff.mp hzInsert)

/-- A set with finitely many members belongs to a carrier containing the
empty set and closed under insertion, provided each of its members belongs to
that carrier. -/
private theorem mem_of_externallyFinite_of_insert_closed
    {domain x : ZFSet.{u}} (hempty : (∅ : ZFSet.{u}) ∈ domain)
    (hinsert : ∀ {a b : ZFSet.{u}}, a ∈ domain → b ∈ domain →
      insert a b ∈ domain)
    (hfinite : ExternallyFinite x) (hmembers : x ⊆ domain) :
    x ∈ domain := by
  classical
  have build : ∀ s : Finset ZFSet.{u},
      (∀ z : ZFSet.{u}, z ∈ s → z ∈ domain) →
        ∃ y : ZFSet.{u}, y ∈ domain ∧
          ∀ z : ZFSet.{u}, (z ∈ y ↔ z ∈ s) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _hmembers
        refine ⟨∅, hempty, ?_⟩
        intro z
        simp
    | @insert a s ha ih =>
        intro hsMembers
        have haDomain : a ∈ domain :=
          hsMembers a (Finset.mem_insert_self a s)
        have hsDomain : ∀ z : ZFSet.{u}, z ∈ s → z ∈ domain := by
          intro z hz
          exact hsMembers z (Finset.mem_insert_of_mem hz)
        rcases ih hsDomain with ⟨old, holdDomain, hold⟩
        refine ⟨insert a old, hinsert haDomain holdDomain, ?_⟩
        intro z
        rw [ZFSet.mem_insert_iff, Finset.mem_insert, hold z]
  have hfinsetMembers :
      ∀ z : ZFSet.{u}, z ∈ hfinite.toFinset → z ∈ domain := by
    intro z hz
    exact hmembers (hfinite.mem_toFinset.mp hz)
  rcases build hfinite.toFinset hfinsetMembers with
    ⟨y, hyDomain, hyMembers⟩
  have hxy : x = y := by
    apply ZFSet.ext
    intro z
    rw [hyMembers z]
    exact hfinite.mem_toFinset.symm
  simpa only [hxy] using hyDomain

/-- Every fully elementary substructure of `L_omega` contains all of
`L_omega`.  The proof is well-founded membership induction, using hereditary
finiteness and the two exact finite constructors above. -/
private theorem LStageZF_omega_subset_of_elementary {domain : ZFSet.{u}}
    (hsubset : domain ⊆ LStageZF (Ordinal.omega0 : Ordinal.{u}))
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u})) :
    LStageZF (Ordinal.omega0 : Ordinal.{u}) ⊆ domain := by
  have hempty : (∅ : ZFSet.{u}) ∈ domain :=
    empty_mem_of_elementary_omega hsubset helem
  have hinsert : ∀ {a b : ZFSet.{u}}, a ∈ domain → b ∈ domain →
      insert a b ∈ domain :=
    fun ha hb => insert_mem_of_elementary_omega hsubset helem ha hb
  intro x hxOmega
  refine ZFSet.inductionOn
    (p := fun x : ZFSet.{u} =>
      x ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}) → x ∈ domain)
    x ?_ hxOmega
  intro x ih hx
  apply mem_of_externallyFinite_of_insert_closed hempty hinsert
    (externallyFinite_of_mem_LStageZF_omega hx)
  intro y hy
  have hyOmega :
      y ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
    (LStageZF_isTransitive
      (Ordinal.omega0 : Ordinal.{u})).mem_trans hy hx
  exact ih y hy hyOmega

/-- A fully elementary substructure of `L_omega` whose carrier is an actual
`ZFSet` is exactly `L_omega`. -/
private theorem domain_eq_LStageZF_omega_of_elementary {domain : ZFSet.{u}}
    (hsubset : domain ⊆ LStageZF (Ordinal.omega0 : Ordinal.{u}))
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u})) :
    domain = LStageZF (Ordinal.omega0 : Ordinal.{u}) := by
  apply ZFSet.ext
  intro x
  constructor
  · exact fun hx => hsubset hx
  · exact fun hx =>
      LStageZF_omega_subset_of_elementary hsubset helem hx

end OmegaCondensation

/-- The standard Condensation conclusion at `theta = omega`: the Mostowski
collapse of every set-sized fully elementary substructure of `L_omega` is
`L_omega` itself. -/
private theorem condensation_of_elementary_omega {domain : ZFSet.{u}}
    (hsubset : domain ⊆ LStageZF (Ordinal.omega0 : Ordinal.{u}))
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u})) :
    range domain = LStageZF (Ordinal.omega0 : Ordinal.{u}) := by
  have hdomain :
      domain = LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
    OmegaCondensation.domain_eq_LStageZF_omega_of_elementary
      hsubset helem
  have htrans : domain.IsTransitive := by
    rw [hdomain]
    exact LStageZF_isTransitive (Ordinal.omega0 : Ordinal.{u})
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    rcases mem_range_iff.mp hz with ⟨x, hx, hcollapse⟩
    have hfixed := collapse_eq_self_of_mem htrans x hx
    have hxz : x = z := hfixed.symm.trans hcollapse
    rw [← hdomain, ← hxz]
    exact hx
  · intro hz
    have hzDomain : z ∈ domain := by
      rw [hdomain]
      exact hz
    exact mem_range_iff.mpr
      ⟨z, hzDomain, collapse_eq_self_of_mem htrans z hzDomain⟩

end

end MostowskiCollapse

end Constructible

end
end GCHSource_Work_CUGCH_CondensationOmega

/- Source module: Solutions.Work_CUGCH_StandardCondensation -/
section GCHSource_Work_CUGCH_StandardCondensation
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# The standard Condensation Lemma for constructible limit levels

For every nonzero limit ordinal `theta`, the Mostowski collapse of a
set-sized fully elementary membership substructure of `L_theta` is exactly
the constructible level indexed by the ordinal height of the collapse.

The proof separates the exceptional first limit `theta = omega`, where
`L_omega` is hereditarily finite, from the case `omega < theta`.  In the
second case, local correctness of the relation-free stage predicate follows
from the proved Goedel-evaluator absoluteness theorem and the unconditional
canonical-history bound.
-/

section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section

/-- The ordinal height of the first infinite constructible level is exactly
`omega`. -/
private theorem ordinalHeight_LStageZF_omega0 :
    ordinalHeight (LStageZF (Ordinal.omega0 : Ordinal.{u})) =
      Ordinal.omega0 := by
  apply le_antisymm
  · unfold ordinalHeight
    apply Ordinal.iSup_le
    intro x
    split_ifs with hx
    · exact Order.succ_le_iff.mpr
        ((ordinal_stage_invariants
          (Ordinal.omega0 : Ordinal.{u})).1 hx x.2)
    · exact bot_le
  · rw [Ordinal.omega0_le]
    intro n
    exact (lt_ordinalHeight_of_mem
      (ordinal_toZFSet_mem_LStageZF_of_lt
        (Ordinal.natCast_lt_omega0 n))).le

/--
The standard Condensation Lemma at an arbitrary nonzero limit level.

`SatisfactionAbsolute domain (LStageZF theta)` is full first-order
elementarity for membership, with all free parameters in `domain`.  The
conclusion identifies the collapse with the precise level determined by its
ordinal height; no reflection-level or evaluator hypothesis is exposed.
-/
private theorem condensation_of_elementary_isSuccLimit
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (htheta : Order.IsSuccLimit theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u})) :
    range domain = LStageZF (ordinalHeight (range domain)) := by
  by_cases hthetaOmega : theta = Ordinal.omega0
  · subst theta
    have hrange :
        range domain =
          LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
      condensation_of_elementary_omega hsubset helem
    rw [hrange, ordinalHeight_LStageZF_omega0]
  · have homega : Ordinal.omega0 < theta :=
      lt_of_le_of_ne (Ordinal.omega0_le_of_isSuccLimit htheta)
        (Ne.symm hthetaOmega)
    have hcorrect : BareStageCondensation.BareStageCorrectAt theta :=
      BareStageCondensation.bareStageCorrectAt_of_evaluator_and_history_bounds
        htheta homega
        (Godel.RudimentaryTerm.bareGodelDefOutputCorrectIn_LStageZF_of_omega_lt
          htheta homega)
        Model.canonicalBareHistory_mem_LStageZF_add_omega
    exact
      (BareStageCondensation.stageInterfaces_of_bareStageCorrect
        htheta homega hsubset helem hcorrect).range_eq_LStageZF_ordinalHeight



end

end MostowskiCollapse

end Constructible

end
end GCHSource_Work_CUGCH_StandardCondensation

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

/-- Collapse fixes every member of a transitive set included in its domain.
The collapse domain itself need not be transitive. -/
private theorem collapse_eq_self_of_mem_of_transitive_subset
    {domain bound : ZFSet.{u}}
    (hboundTransitive : bound.IsTransitive)
    (hboundDomain : bound ⊆ domain) :
    ∀ x : ZFSet.{u}, x ∈ bound → collapse domain x = x := by
  intro x
  refine ZFSet.inductionOn
    (p := fun x => x ∈ bound → collapse domain x = x) x ?_
  intro x ih hxBound
  apply ZFSet.ext
  intro z
  rw [mem_collapse_iff]
  constructor
  · rintro ⟨y, hyx, _hyDomain, hyz⟩
    have hyBound : y ∈ bound :=
      hboundTransitive.mem_trans hyx hxBound
    have hyFixed : collapse domain y = y := ih y hyx hyBound
    have hyEq : y = z := hyFixed.symm.trans hyz
    simpa only [hyEq] using hyx
  · intro hzx
    have hzBound : z ∈ bound :=
      hboundTransitive.mem_trans hzx hxBound
    exact ⟨z, hzx, hboundDomain hzBound, ih z hzx hzBound⟩

/-- If every member of `x` lies in a transitive part of the collapse domain,
then collapse fixes `x` as well.  Membership of `x` in the domain is not
needed for this pointwise statement. -/
private theorem collapse_eq_self_of_subset_of_transitive_subset
    {domain bound x : ZFSet.{u}}
    (hboundTransitive : bound.IsTransitive)
    (hboundDomain : bound ⊆ domain)
    (hxBound : x ⊆ bound) :
    collapse domain x = x := by
  apply ZFSet.ext
  intro z
  rw [mem_collapse_iff]
  constructor
  · rintro ⟨y, hyx, _hyDomain, hyz⟩
    have hyBound : y ∈ bound := hxBound hyx
    have hyFixed := collapse_eq_self_of_mem_of_transitive_subset
      hboundTransitive hboundDomain y hyBound
    have hyEq : y = z := hyFixed.symm.trans hyz
    simpa only [hyEq] using hyx
  · intro hzx
    have hzBound : z ∈ bound := hxBound hzx
    exact ⟨z, hzx, hboundDomain hzBound,
      collapse_eq_self_of_mem_of_transitive_subset
        hboundTransitive hboundDomain z hzBound⟩

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



/-- The standard Condensation Lemma identifies the external collapse range
with the level indexed by its ordinal height.  The reflection-level data in
`h.hull` supplies the ordinary nonzero-limit and full-elementarity premises;
it is not an additional premise of this theorem. -/
private theorem range_eq_LStageZF_collapsedHeight
    (h : CardinalControlledHull kappa x) :
    range h.domain.1 = LStageZF h.collapsedHeight :=
  condensation_of_elementary_isSuccLimit
    h.hull.reflection.1 h.hull.subset_stage
      h.hull.satisfactionAbsolute









/-- A subset of `kappa` contained in the hull is fixed by collapse and hence
belongs to the collapsed level. -/
private theorem element_mem_collapsedStage
    (h : CardinalControlledHull kappa x)
    (hkappa : IsCardinal LMem kappa)
    (hx : IsSubsetOf LMem x kappa) :
    x.1 ∈ LStageZF h.collapsedHeight := by
  have hkappaOrdinal : kappa.1.IsOrdinal :=
    (isVonNeumannOrdinal_lCarrier_iff kappa).mp hkappa.1
  have hxRaw : x.1 ⊆ kappa.1 := by
    intro z hz
    let zL : LCarrier.{u} := ⟨z, mem_L_of_mem hz x.2⟩
    exact hx zL hz
  have hfixed : collapse h.domain.1 x.1 = x.1 :=
    collapse_eq_self_of_subset_of_transitive_subset
      hkappaOrdinal.isTransitive h.bound_subset hxRaw
  change x.1 ∈ LStageZF h.collapsedHeight
  rw [← h.range_eq_LStageZF_collapsedHeight]
  exact mem_range_iff.mpr ⟨x.1, h.element_mem, hfixed⟩

/-- The subset captured by the hull already occurs before the Hartogs-indexed
constructible level. -/
private theorem element_mem_internalHartogsStage_gchProof06
    (h : CardinalControlledHull kappa x)
    (hkappa : IsCardinal LMem kappa)
    (hx : IsSubsetOf LMem x kappa) :
    x.1 ∈ LStageZF (internalHartogsOrdinal kappa) := by
  exact LStageZF_mono
    h.collapsedHeight_lt_internalHartogsOrdinal.le
    (h.element_mem_collapsedStage hkappa hx)

end CardinalControlledHull







/-! ## The two remaining cardinal interfaces -/













end

end ContinuumFormula

end Constructible

end
end GCHSource_Work_CUGCH_CondensationGCHBridge

universe u

theorem solution : ∀ {kappa x : Constructible.Model.LCarrier.{u}} (h : Constructible.ContinuumFormula.CardinalControlledHull.{u} kappa x),
  @Constructible.ContinuumFormula.IsCardinal.{u + 1} Constructible.Model.LCarrier.{u}
      Constructible.Model.lCarrierMem.{u} kappa →
    @Constructible.ContinuumFormula.IsSubsetOf.{u + 1} Constructible.Model.LCarrier.{u}
        Constructible.Model.lCarrierMem.{u} x kappa →
      @Membership.mem.{u + 1, u + 1} ZFSet.{u} ZFSet.{u}
        (@SetLike.instMembership.{u + 1, u + 1} ZFSet.{u} ZFSet.{u} ZFSet.instSetLike.{u})
        (Constructible.LStageZF.{u} (Constructible.ContinuumFormula.internalHartogsOrdinal.{u} kappa))
        (@Subtype.val.{u + 2} ZFSet.{u}
          (fun x =>
            @Membership.mem.{u + 1, u + 1} ZFSet.{u} (Set.{u + 1} ZFSet.{u}) (@Set.instMembership.{u + 1} ZFSet.{u})
              Constructible.L.{u} x)
          x) :=
  @Constructible.ContinuumFormula.CardinalControlledHull.element_mem_internalHartogsStage_gchProof06.{u}
