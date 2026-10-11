-- Prove2me | solution 1 for CLRS.Chapter4Publication.MatrixRecursive.correctness_and_running_time
-- status  : ACCEPTED   (prove)
-- author  : @Chutong
-- created : 2026-10-11T06:34:32.337981+00:00
-- url     : https://prove2.me/submissions/d02db2e1-4eb6-4419-b04a-4842770de59d

import Definitions.Def_CLRS_Chapter4_Algo2Lean
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixMultiply
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixMultiplyGenerated
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixMultiplyPoints
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixRecursive
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixRecursiveGenerated
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixStrassen
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixStrassenGenerated
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixStrassenPoints
import Definitions.Def_CLRS_Chapter4_Algo2LeanLib_CallCost
import Definitions.Def_CLRS_Chapter4_Algo2LeanLib_MatrixHeap
import Definitions.Def_CLRS_Chapter4_Publication_MatrixContracts
import Std

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section
namespace CLRS

-- Copyright 2026 Lunjia Hu and contributors.
-- SPDX-License-Identifier: Apache-2.0

/-

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/

namespace Algo2LeanCore

universe u v w





variable {Heap : Type u} {Frame : Type v} {Result : Type w}















namespace Valid

variable {State : Type u} {step nextProperty : State → State → Prop}

theorem nonempty {initial : State} {states : List State} {final : State} (h : Valid step initial states final) : states ≠ [] := by
  cases h <;> simp









/-- Concatenation keeps the shared endpoint once. -/
theorem append {a : State} {xs : List State} {b : State} {ys : List State} {c : State} (first : Valid step a xs b) (second : Valid step b ys c) :
    Valid step a (xs.dropLast ++ ys) c := by
  induction first with
  | single => simpa using second
  | @cons before after rest final transition tail ih =>
    have split : (before :: rest).dropLast = before :: rest.dropLast := by
      cases rest with
      | nil => exact (tail.nonempty rfl).elim
      | cons head rest => simp
    simpa [split] using Valid.cons transition (ih second)

/-- Deterministic completed runs agree, regardless of their transcript witnesses. -/
theorem eq_of_terminal {a : State} {xs : List State} {b : State} {ys : List State} {c : State} (deterministic : Deterministic step)
    (first : Valid step a xs b) (second : Valid step a ys c)
    (atFirst : Terminal step b) (atSecond : Terminal step c) : b = c := by
  induction first generalizing ys c with
  | single =>
    cases second with
    | single => rfl
    | cons transition => exact False.elim (atFirst _ transition)
  | cons transition _ inductionHypothesis =>
    cases second with
    | single => exact False.elim (atSecond _ transition)
    | cons other tail =>
      cases deterministic transition other
      exact inductionHypothesis tail atFirst atSecond

end Valid



namespace Reaches

variable {State : Type u} {step : State → State → Prop}

theorem refl (state : State) : Reaches step state state := ⟨[state], .single _⟩

theorem single {a : State} {b : State} (transition : step a b) : Reaches step a b :=
  ⟨[a, b], .cons transition (.single _)⟩

theorem trans {a : State} {b : State} {c : State} (first : Reaches step a b) (second : Reaches step b c) : Reaches step a c := by
  obtain ⟨xs, first⟩ := first
  obtain ⟨ys, second⟩ := second
  exact ⟨xs.dropLast ++ ys, first.append second⟩

/-- Extend an execution segment by one local transition at its beginning. -/
theorem prepend {a : State} {b : State} {c : State} (transition : step a b) (rest : Reaches step b c) : Reaches step a c :=
  (single transition).trans rest

/-- Turn a constructed result into a theorem about every completed execution. -/
theorem eq_of_terminal {a : State} {b : State} {c : State} (deterministic : Deterministic step)
    (first : Reaches step a b) (second : Reaches step a c)
    (atFirst : Terminal step b) (atSecond : Terminal step c) : b = c := by
  obtain ⟨_, first⟩ := first
  obtain ⟨_, second⟩ := second
  exact Valid.eq_of_terminal (step := step) deterministic first second atFirst atSecond



end Reaches



theorem Summary.root {step : Algo2LeanCore.Config Heap Frame Result → Algo2LeanCore.Config Heap Frame Result → Prop} {heap : Heap} {frame : Frame} {heap' : Heap} {result : Result} (summary : Summary step heap frame heap' result) :
    Reaches step (start heap frame) (.done heap' result) := by
  simpa [start, resumeConfig] using summary []

end Algo2LeanCore

/- Integer sequences are mathematical objects, addressed by stable identities. -/
namespace Algo2LeanGenerated



















































































































































































































































namespace SequenceType

variable {α : Type} (type : SequenceType α)



































end SequenceType

end Algo2LeanGenerated

end CLRS
end

section
namespace CLRS

namespace «MatrixRecursiveLibrary»

open _root_.CLRS.Algo2LeanGenerated

-- Generated by Algo2Lean 0.1.1 https://github.com/lunjiah/algo2lean
-- Generated direct transitions; outputs are completed valid transcripts.
namespace Algo2LeanGenerated



 -- temporary

 -- temporary











end Algo2LeanGenerated

open Algo2LeanGenerated






-- Complete this function from the supplied local state, under any caller stack.

-- Object inputs carry their heap, preserving shared references and cycles.




-- Output and clock increments from one completed execution.











-- Complete this function from the supplied local state, under any caller stack.

-- Object inputs carry their heap, preserving shared references and cycles.




-- Output and clock increments from one completed execution.


theorem matrix_recursive.Returns.withCost {input output}
    (run : _root_.CLRS.MatrixRecursiveLibrary.matrix_recursive.Returns input output) : ∃ costs, _root_.CLRS.MatrixRecursiveLibrary.matrix_recursive.ReturnsWithCost input output costs := by
  exact ⟨Heap.cost (_root_.CLRS.MatrixRecursiveLibrary.matrix_recursive.load input).1 output.1, run, rfl⟩

theorem matrix_recursive.Call.run {before input after output}
    (call : _root_.CLRS.MatrixRecursiveLibrary.matrix_recursive.Call before input after output) :
    _root_.CLRS.MatrixRecursiveLibrary.matrix_recursive.Run before input after output :=
  ⟨call.1, call.2.root⟩


end «MatrixRecursiveLibrary»

end CLRS
end

section
namespace CLRS

/-! Heap views shared by the array-of-arrays matrix examples. Input rows may
alias. Preservation concerns every allocated input object, not just the two
outer array references. Counter changes are stated separately by each program. -/

namespace Algo2LeanCore.MatrixHeap

open Algo2LeanGenerated













theorem Extends.trans {a b c : Heap} (first : Extends a b) (second : Extends b c) :
    Extends a c := by
  refine ⟨Nat.le_trans first.nextRef second.nextRef,
    Nat.le_trans first.nextCollection second.nextCollection, ?_, ?_,
    second.nextObject.trans first.nextObject, second.objects.trans first.objects⟩
  · intro r valid
    exact (second.store r (Nat.lt_of_lt_of_le valid first.nextRef)).trans (first.store r valid)
  · intro r valid
    exact (second.collections r (Nat.lt_of_lt_of_le valid first.nextCollection)).trans
      (first.collections r valid)

theorem Extends.valid {before after : Heap} (extension : Extends before after)
    {matrix : CollectionRef} (valid : rows.valid before matrix) : rows.valid after matrix := by
  refine ⟨Nat.lt_of_lt_of_le valid.1 extension.nextCollection, ?_⟩
  change (after.collections matrix).map _ = _
  rw [extension.collections matrix valid.1]
  exact valid.2

theorem Extends.get {before after : Heap} (extension : Extends before after)
    {matrix : CollectionRef} (valid : rows.valid before matrix) (i : Int) :
    rows.get after matrix i = rows.get before matrix i := by
  simp only [SequenceType.get, valid, extension.valid valid, if_pos]
  unfold Heap.readElement
  rw [extension.collections matrix valid.1]





















/-- Writing a row allocated after the old heap preserves that old heap. -/
theorem Extends.write {before after : Heap} (extension : Extends before after)
    (row : SeqRef) (fresh : before.nextRef ≤ row) (i value : Int) :
    Extends before (after.write row i value) := by
  refine ⟨extension.nextRef, extension.nextCollection, ?_, extension.collections,
    extension.nextObject, extension.objects⟩
  intro r valid
  have different : r ≠ row := by omega
  funext j
  simp [Heap.write, different, extension.store r valid]

/-- Installing a row in a newly allocated outer array preserves old matrices. -/
theorem Extends.set {before after : Heap} (extension : Extends before after)
    (matrix : CollectionRef) (fresh : before.nextCollection ≤ matrix) (i : Int) (row : SeqRef) :
    Extends before (rows.set after matrix i row) := by
  refine ⟨extension.nextRef, extension.nextCollection, extension.store, ?_,
    extension.nextObject, extension.objects⟩
  intro r valid
  have different : r ≠ matrix := by omega
  simp [SequenceType.set, Heap.writeElement, different, extension.collections r valid]





















end Algo2LeanCore.MatrixHeap

end CLRS
end

section
namespace CLRS

open MatrixRecursiveLibrary MatrixRecursiveLibrary.Algo2LeanGenerated

open Algo2LeanCore Algo2LeanGenerated
namespace MatrixRecursiveAnalysis

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000



@[simp] theorem get_tick (heap : Heap) (m : CollectionRef) (i : Int) (clock : String) :
    seq_Seq_Int.get (heap.tick clock) m i = seq_Seq_Int.get heap m i := rfl



@[simp] theorem hasRows_tick (heap : Heap) (m : CollectionRef) (rows : Int → SeqRef) (clock : String) :
    HasRows (heap.tick clock) m rows ↔ HasRows heap m rows := Iff.rfl



@[simp] theorem blockEffect_nextRef (depth : Nat) (heap : Heap)
    (a b c : Int → SeqRef) (stride row col inner : Int) :
    (blockEffect a b c stride depth heap row col inner).nextRef = heap.nextRef := by
  induction depth generalizing heap row col inner with
  | zero => rfl
  | succ depth ih => simp only [blockEffect, ih, Heap.tick_nextRef]

@[simp] theorem blockEffect_nextCollection (depth : Nat) (heap : Heap)
    (a b c : Int → SeqRef) (stride row col inner : Int) :
    (blockEffect a b c stride depth heap row col inner).nextCollection = heap.nextCollection := by
  induction depth generalizing heap row col inner with
  | zero => rfl
  | succ depth ih => simp only [blockEffect, ih]; rfl

@[simp] theorem blockEffect_collections (depth : Nat) (heap : Heap)
    (a b c : Int → SeqRef) (stride row col inner : Int) :
    (blockEffect a b c stride depth heap row col inner).collections = heap.collections := by
  induction depth generalizing heap row col inner with
  | zero => rfl
  | succ depth ih => simp only [blockEffect, ih]; rfl

@[simp] theorem hasRows_effect (depth : Nat) (heap : Heap)
    (a b c rows : Int → SeqRef) (stride row col inner : Int) (m : CollectionRef) :
    HasRows (blockEffect a b c stride depth heap row col inner) m rows ↔ HasRows heap m rows := by
  simp only [HasRows, SequenceType.get, SequenceType.valid, Heap.validSequence,
    Heap.sequenceType, Heap.readElement, blockEffect_collections, blockEffect_nextCollection,
    blockEffect_nextRef]

/-- Finite terminating execution of all eight calls, for every power-of-two size. -/
theorem block_summary (depth : Nat) (heap : Heap) (a b c : CollectionRef)
    (ar br cr : Int → SeqRef)
    (stride row col inner : Int)
    (ha : HasRows heap a ar) (hb : HasRows heap b br) (hc : HasRows heap c cr) :
    matrix_block.Call heap (a, b, c, stride, row, col, inner, (2 ^ depth : Nat))
      (blockEffect ar br cr stride depth heap row col inner) 0 := by
  induction depth generalizing heap row col inner with
  | zero =>
    refine ⟨⟨ha.1, hb.1, hc.1⟩, ?_⟩
    intro stack
    apply Reaches.prepend (Step.matrix_block_pc82 ..)
    apply Reaches.prepend (Step.matrix_block_pc81 ..)
    apply Reaches.prepend (Step.matrix_block_pc80_true _ _ _ (by simp))
    apply Reaches.prepend (Step.matrix_block_pc79 ..)
    apply Reaches.prepend (Step.matrix_block_pc78 _ _ _ (by simpa [hc.2 row |>.1, ha.2 row |>.1, hb.2 inner |>.1] using And.intro (And.intro (hc.2 row |>.2) (And.intro (ha.2 row |>.2) (hb.2 inner |>.2))) (hc.2 row |>.2)))
    apply Reaches.prepend (Step.matrix_block_pc77 ..)
    simpa only [blockEffect, get_tick, hc.2 row |>.1, ha.2 row |>.1, hb.2 inner |>.1,
      Option.getD_some, Heap.read_tick] using Reaches.single (Step.matrix_block_pc76 _ _ _)
  | succ depth ih =>
    have positive : 0 < (2 ^ depth : Nat) := Nat.pow_pos (by decide)
    have half_eq : Int.fdiv ((2 ^ (depth + 1) : Nat) : Int) 2 = ((2 ^ depth : Nat) : Int) := by
      simp [Nat.pow_succ, Int.fdiv_eq_ediv, Int.mul_ediv_cancel]
    refine ⟨⟨ha.1, hb.1, hc.1⟩, ?_⟩
    intro stack
    apply Reaches.prepend (Step.matrix_block_pc82 ..)
    apply Reaches.prepend (Step.matrix_block_pc81 ..)
    apply Reaches.prepend (Step.matrix_block_pc80_false _ _ _ (by
      simp only [decide_eq_false_iff_not, Nat.pow_succ, Int.natCast_mul]
      omega))
    apply Reaches.prepend (Step.matrix_block_pc75 _ _ _ (by decide))
    simp only [half_eq]
    apply Reaches.prepend (Step.matrix_block_pc74 ..)
    apply Reaches.prepend (Step.matrix_block_pc73 ..)
    apply Reaches.prepend (Step.matrix_block_pc72 ..)
    apply Reaches.prepend (Step.matrix_block_pc71 ..)
    apply Reaches.prepend (Step.matrix_block_pc70 ..)
    apply Reaches.prepend (Step.matrix_block_pc69 ..)
    apply Reaches.prepend (Step.matrix_block_pc68 ..)
    apply Reaches.prepend (Step.matrix_block_pc67 ..)
    apply Reaches.prepend (Step.matrix_block_pc66 ..)
    apply Reaches.trans ((ih _ _ _ _ (by simpa using ha) (by simpa using hb) (by simpa using hc)).2 _)
    apply Reaches.prepend (Step.matrix_block_pc65 ..)
    apply Reaches.prepend (Step.matrix_block_pc64 ..)
    apply Reaches.prepend (Step.matrix_block_pc63 ..)
    apply Reaches.prepend (Step.matrix_block_pc62 ..)
    apply Reaches.prepend (Step.matrix_block_pc61 ..)
    apply Reaches.prepend (Step.matrix_block_pc60 ..)
    apply Reaches.prepend (Step.matrix_block_pc59 ..)
    apply Reaches.prepend (Step.matrix_block_pc58 ..)
    apply Reaches.prepend (Step.matrix_block_pc57 ..)
    apply Reaches.trans ((ih _ _ _ _ (by simpa using ha) (by simpa using hb) (by simpa using hc)).2 _)
    apply Reaches.prepend (Step.matrix_block_pc56 ..)
    apply Reaches.prepend (Step.matrix_block_pc55 ..)
    apply Reaches.prepend (Step.matrix_block_pc54 ..)
    apply Reaches.prepend (Step.matrix_block_pc53 ..)
    apply Reaches.prepend (Step.matrix_block_pc52 ..)
    apply Reaches.prepend (Step.matrix_block_pc51 ..)
    apply Reaches.prepend (Step.matrix_block_pc50 ..)
    apply Reaches.prepend (Step.matrix_block_pc49 ..)
    apply Reaches.prepend (Step.matrix_block_pc48 ..)
    apply Reaches.trans ((ih _ _ _ _ (by simpa using ha) (by simpa using hb) (by simpa using hc)).2 _)
    apply Reaches.prepend (Step.matrix_block_pc47 ..)
    apply Reaches.prepend (Step.matrix_block_pc46 ..)
    apply Reaches.prepend (Step.matrix_block_pc45 ..)
    apply Reaches.prepend (Step.matrix_block_pc44 ..)
    apply Reaches.prepend (Step.matrix_block_pc43 ..)
    apply Reaches.prepend (Step.matrix_block_pc42 ..)
    apply Reaches.prepend (Step.matrix_block_pc41 ..)
    apply Reaches.prepend (Step.matrix_block_pc40 ..)
    apply Reaches.prepend (Step.matrix_block_pc39 ..)
    apply Reaches.trans ((ih _ _ _ _ (by simpa using ha) (by simpa using hb) (by simpa using hc)).2 _)
    apply Reaches.prepend (Step.matrix_block_pc38 ..)
    apply Reaches.prepend (Step.matrix_block_pc37 ..)
    apply Reaches.prepend (Step.matrix_block_pc36 ..)
    apply Reaches.prepend (Step.matrix_block_pc35 ..)
    apply Reaches.prepend (Step.matrix_block_pc34 ..)
    apply Reaches.prepend (Step.matrix_block_pc33 ..)
    apply Reaches.prepend (Step.matrix_block_pc32 ..)
    apply Reaches.prepend (Step.matrix_block_pc31 ..)
    apply Reaches.prepend (Step.matrix_block_pc30 ..)
    apply Reaches.trans ((ih _ _ _ _ (by simpa using ha) (by simpa using hb) (by simpa using hc)).2 _)
    apply Reaches.prepend (Step.matrix_block_pc29 ..)
    apply Reaches.prepend (Step.matrix_block_pc28 ..)
    apply Reaches.prepend (Step.matrix_block_pc27 ..)
    apply Reaches.prepend (Step.matrix_block_pc26 ..)
    apply Reaches.prepend (Step.matrix_block_pc25 ..)
    apply Reaches.prepend (Step.matrix_block_pc24 ..)
    apply Reaches.prepend (Step.matrix_block_pc23 ..)
    apply Reaches.prepend (Step.matrix_block_pc22 ..)
    apply Reaches.prepend (Step.matrix_block_pc21 ..)
    apply Reaches.trans ((ih _ _ _ _ (by simpa using ha) (by simpa using hb) (by simpa using hc)).2 _)
    apply Reaches.prepend (Step.matrix_block_pc20 ..)
    apply Reaches.prepend (Step.matrix_block_pc19 ..)
    apply Reaches.prepend (Step.matrix_block_pc18 ..)
    apply Reaches.prepend (Step.matrix_block_pc17 ..)
    apply Reaches.prepend (Step.matrix_block_pc16 ..)
    apply Reaches.prepend (Step.matrix_block_pc15 ..)
    apply Reaches.prepend (Step.matrix_block_pc14 ..)
    apply Reaches.prepend (Step.matrix_block_pc13 ..)
    apply Reaches.prepend (Step.matrix_block_pc12 ..)
    apply Reaches.trans ((ih _ _ _ _ (by simpa using ha) (by simpa using hb) (by simpa using hc)).2 _)
    apply Reaches.prepend (Step.matrix_block_pc11 ..)
    apply Reaches.prepend (Step.matrix_block_pc10 ..)
    apply Reaches.prepend (Step.matrix_block_pc9 ..)
    apply Reaches.prepend (Step.matrix_block_pc8 ..)
    apply Reaches.prepend (Step.matrix_block_pc7 ..)
    apply Reaches.prepend (Step.matrix_block_pc6 ..)
    apply Reaches.prepend (Step.matrix_block_pc5 ..)
    apply Reaches.prepend (Step.matrix_block_pc4 ..)
    apply Reaches.prepend (Step.matrix_block_pc3 ..)
    apply Reaches.trans ((ih _ _ _ _ (by simpa using ha) (by simpa using hb) (by simpa using hc)).2 _)
    apply Reaches.prepend (Step.matrix_block_pc2 ..)
    exact Reaches.single (Step.matrix_block_pc1 ..)



/-- Recursive multiplication never changes any other allocated input object. -/
@[simp] theorem blockEffect_read_other (depth : Nat) (heap : Heap)
    (a b c : Int → SeqRef) (other : SeqRef) (stride row col inner index : Int) (hne : ∀ r, other ≠ c r) :
    (blockEffect a b c stride depth heap row col inner).read other index = heap.read other index := by
  induction depth generalizing heap row col inner with
  | zero => simp [blockEffect, hne]
  | succ depth ih => simp only [blockEffect, ih, Heap.read_tick]



/-- Exactly one scalar multiplication at each of the eight-way recursion leaves. -/
@[simp] theorem blockEffect_clocks (depth : Nat) (heap : Heap)
    (a b c : Int → SeqRef) (stride row col inner : Int) (name : String) :
    (blockEffect a b c stride depth heap row col inner).clocks name =
      heap.clocks name + if name = "multiplications" then 8 ^ depth else
        if name = "calls" then callCount depth else 0 := by
  induction depth generalizing heap row col inner with
  | zero =>
    by_cases hname : name = "multiplications" <;> by_cases hcalls : name = "calls" <;>
      simp_all [blockEffect, Heap.tick, callCount]
  | succ depth ih =>
    simp only [blockEffect, ih]
    by_cases hname : name = "multiplications"
    · subst name
      simp [Nat.pow_succ, Heap.tick]
      omega
    · by_cases hcalls : name = "calls"
      · subst name
        simp [Heap.tick, callCount]
        omega
      · simp [hname, hcalls, Heap.tick]

/-- The cubic scalar count, stated without an asymptotic approximation. -/
theorem multiplications_cubic (depth : Nat) : 8 ^ depth = (2 ^ depth) ^ 3 := by
  have h := Nat.pow_mul 2 3 depth
  simpa [← Nat.pow_mul, Nat.mul_comm] using h.symm






/-- The eight block contributions sum to the full block contribution. -/
theorem contribution_split (a b : Int → Seq) (stride qr qc : Int) (depth : Nat) (r c k : Int) :
    let h : Int := (2 ^ depth : Nat)
    contribution a b stride qr qc depth r c k +
    contribution a b stride qr qc depth r c (k+h) +
    contribution a b stride qr qc depth r (c+h) k +
    contribution a b stride qr qc depth r (c+h) (k+h) +
    contribution a b stride qr qc depth (r+h) c k +
    contribution a b stride qr qc depth (r+h) c (k+h) +
    contribution a b stride qr qc depth (r+h) (c+h) k +
    contribution a b stride qr qc depth (r+h) (c+h) (k+h) =
    contribution a b stride qr qc (depth + 1) r c k := by
  have positive : 0 < (2 ^ depth : Nat) := Nat.pow_pos (by decide)
  simp only [contribution, Nat.pow_succ, Int.natCast_mul, innerProduct]
  split <;> split <;> split <;> split <;> split <;> simp_all <;> omega



@[simp] theorem blockEffect_store_other (depth : Nat) (heap : Heap)
    (a b c : Int → SeqRef) (other : SeqRef) (stride row col inner : Int) (hne : ∀ r, other ≠ c r) :
    (blockEffect a b c stride depth heap row col inner).store other = heap.store other := by
  funext index
  exact blockEffect_read_other depth heap a b c other stride row col inner index hne

/-- Every individual output cell equals its old value plus the block's dot product.
    The statement permits aliasing between the two inputs, but neither aliases c. -/
theorem blockEffect_correct (depth : Nat) (heap : Heap) (a b c : Int → SeqRef)
    (stride row col inner qr qc : Int) (ha : ∀ i j, a i ≠ c j) (hb : ∀ i j, b i ≠ c j)
    (distinct : ∀ i j, 0 ≤ j → j < stride → (c i = c j ↔ i = j))
    (row_nonnegative : 0 ≤ row) (row_bound : row + (2 ^ depth : Nat) ≤ stride) :
    (blockEffect a b c stride depth heap row col inner).read (c qr) qc =
      heap.read (c qr) qc +
        contribution (fun i => heap.store (a i)) (fun i => heap.store (b i)) stride qr qc depth row col inner := by
  induction depth generalizing heap row col inner with
  | zero =>
    have row_bound' : row < stride := by
      simp only [Nat.pow_zero, Int.natCast_one] at row_bound
      omega
    have same := distinct qr row row_nonnegative row_bound'
    simp only [blockEffect, Heap.read, Heap.write, Heap.tick]
    simp only [contribution, innerProduct, Nat.pow_zero, Int.natCast_one]
    by_cases hr : qr = row <;> by_cases hc : qc = col
    · subst qr; subst qc
      simp [show row < row + 1 by omega, show col < col + 1 by omega]
    · subst qr
      simp [hc, show ¬(col ≤ qc ∧ qc < col + 1) by omega]
    · have refs : c qr ≠ c row := fun eq => hr (same.mp eq)
      simp [refs, show ¬(row ≤ qr ∧ qr < row + 1 ∧ col ≤ qc ∧ qc < col + 1) by omega]
    · have refs : c qr ≠ c row := fun eq => hr (same.mp eq)
      simp [refs, show ¬(row ≤ qr ∧ qr < row + 1 ∧ col ≤ qc ∧ qc < col + 1) by omega]
  | succ depth ih =>
    have positive : 0 < (2 ^ depth : Nat) := Nat.pow_pos (by decide)
    have doubled : ((2 ^ (depth + 1) : Nat) : Int) = (2 ^ depth : Nat) + (2 ^ depth : Nat) := by
      simp [Nat.pow_succ, Int.natCast_mul]; omega
    rw [doubled] at row_bound
    simp only [blockEffect]
    simp (disch := first | exact ha _ | exact hb _ | omega) only [ih, blockEffect_store_other, Heap.tick_store, Heap.read_tick]
    have combined := contribution_split (fun i => heap.store (a i)) (fun i => heap.store (b i)) stride qr qc depth row col inner
    dsimp only at combined
    omega





theorem finiteSum_append (n m : Nat) (f : Nat → Int) :
    finiteSum (n + m) f = finiteSum n f + finiteSum m (fun i => f (n+i)) := by
  induction m with
  | zero => simp [finiteSum]
  | succ m ih =>
    change finiteSum (n+m) f + f (n+m) = finiteSum n f +
      (finiteSum m (fun i => f (n+i)) + f (n+m))
    rw [ih]; omega

/-- The recursive specification is the usual finite dot product. -/
theorem innerProduct_eq_sum (a b : Int → Seq) (stride qr qc : Int) (depth : Nat) (first : Int) :
    innerProduct a b stride qr qc depth first = finiteSum (2 ^ depth)
      (fun i => a qr (first + i) * b (first + i) qc) := by
  induction depth generalizing first with
  | zero => simp [innerProduct, finiteSum]
  | succ depth ih =>
    have twice : 2 ^ (depth+1) = 2 ^ depth + 2 ^ depth := by
      simp [Nat.pow_succ, Nat.mul_two]
    rw [innerProduct, ih, ih, twice, finiteSum_append]
    simp only [Int.natCast_add, Int.add_assoc]


open Algo2LeanCore.MatrixHeap



@[simp] theorem initializeRows_nextRef (heap : Heap) (c : CollectionRef) (first : Int) (count : Nat) :
    (initializeRows heap c first count).nextRef = heap.nextRef + count := by
  induction count generalizing heap first with
  | zero => simp [initializeRows]
  | succ count ih => simp only [initializeRows, ih, SequenceType.set, Heap.writeElement, Heap.allocate]; omega



@[simp] theorem initializeRows_valid (heap : Heap) (c m : CollectionRef) (first : Int) (count : Nat) :
    seq_Seq_Int.valid (initializeRows heap c first count) m ↔ seq_Seq_Int.valid heap m := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih => simp only [initializeRows, ih, SequenceType.valid_set]; rfl

 theorem initializeRows_store_old (heap : Heap) (c : CollectionRef) (first : Int) (count : Nat)
    (r : SeqRef) (valid : r < heap.nextRef) :
    (initializeRows heap c first count).store r = heap.store r := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    rw [initializeRows, ih]
    · simp [SequenceType.set, Heap.writeElement, Heap.allocate, Nat.ne_of_lt valid]
    · simpa [SequenceType.set, Heap.writeElement] using Nat.lt_succ_of_lt valid

 theorem initializeRows_store_new (heap : Heap) (c : CollectionRef) (first : Int) (count : Nat)
    (r : SeqRef) (lower : heap.nextRef ≤ r) (upper : r < heap.nextRef + count) :
    (initializeRows heap c first count).store r = fun _ => 0 := by
  induction count generalizing heap first with
  | zero => exact False.elim ((Nat.not_lt_of_ge lower) (by simpa using upper))
  | succ count ih =>
    rw [initializeRows]
    by_cases equal : r = heap.nextRef
    · rw [initializeRows_store_old]
      · simp [equal, SequenceType.set, Heap.writeElement, Heap.allocate]
      · simp [equal, SequenceType.set, Heap.writeElement]
    · exact ih _ _ (Nat.lt_of_le_of_ne lower (Ne.symm equal)) (by simpa [SequenceType.set, Heap.writeElement, Nat.add_assoc, Nat.add_comm count 1] using upper)

 theorem initializeRows_get_outside (heap : Heap) (c : CollectionRef) (first i : Int) (count : Nat)
    (outside : i < first ∨ first + count ≤ i) :
    seq_Seq_Int.get (initializeRows heap c first count) c i = seq_Seq_Int.get heap c i := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    rw [initializeRows, ih _ _ (by omega), SequenceType.get_set_other_index _ _ _ _ _ _ (by omega)]
    rfl

 theorem initializeRows_get_inside (heap : Heap) (c : CollectionRef) (first i : Int) (count : Nat)
    (valid : seq_Seq_Int.valid heap c) (lower : first ≤ i) (upper : i < first + count) :
    seq_Seq_Int.get (initializeRows heap c first count) c i = some (heap.nextRef + (i - first).toNat) := by
  induction count generalizing heap first with
  | zero => omega
  | succ count ih =>
    rw [initializeRows]
    by_cases equal : i = first
    · subst i
      rw [initializeRows_get_outside _ _ _ _ _ (Or.inl (by omega)), SequenceType.get_set_same _ _ _ _ _ (show seq_Seq_Int.valid (heap.allocate (fun _ => 0)) c from valid)]
      simp
    · rw [ih _ _ (by apply (seq_Seq_Int.valid_set _ _ _ _ _).mpr; exact valid)
        (by omega) (by omega)]
      congr 1
      simp only [SequenceType.set, Heap.writeElement, Heap.allocate]
      omega

/-- The allocation loop terminates after exactly the remaining number of rows. -/
private theorem initializeRows_execution (count : Nat) (heap : Heap) (state : State_matrix_recursive)
    (stack : Stack) (valid : seq_Seq_Int.valid heap state.v3)
    (size : state.v2 = state.v4 + count) :
    ∃ finalState : State_matrix_recursive,
      Reaches Step (.active heap (.fn_matrix_recursive 13 state) stack)
        (.active (initializeRows heap state.v3 state.v4 count) (.fn_matrix_recursive 11 finalState) stack) ∧
      finalState.v0 = state.v0 ∧ finalState.v1 = state.v1 ∧ finalState.v2 = state.v2 ∧
      finalState.v3 = state.v3 := by
  induction count generalizing heap state with
  | zero =>
    refine ⟨{ state with t15 := decide (state.v4 < state.v2) }, ?_, rfl, rfl, rfl, rfl⟩
    apply Reaches.prepend (Step.matrix_recursive_pc13 ..)
    exact Reaches.single (Step.matrix_recursive_pc12_false _ _ _ (by change decide (state.v4 < state.v2) = false; simp only [decide_eq_false_iff_not]; omega))
  | succ count ih =>
    have tail := ih (seq_Seq_Int.set (heap.allocate (fun _ => 0)) state.v3 state.v4 heap.nextRef)
      { state with v4 := state.v4 + 1, t15 := true, t19 := 0, t16 := heap.nextRef, t18 := state.v3, t17 := state.v4 }
      (by apply (seq_Seq_Int.valid_set _ _ _ _ _).mpr; exact valid) (by dsimp only; omega)
    obtain ⟨finalState, execution, a, b, n, c⟩ := tail
    refine ⟨finalState, ?_, a, b, n, c⟩
    apply Reaches.prepend (Step.matrix_recursive_pc13 ..)
    apply Reaches.prepend (Step.matrix_recursive_pc12_true _ _ _ (by simp only [decide_eq_true_eq]; omega))
    apply Reaches.prepend (Step.matrix_recursive_pc19 ..)
    apply Reaches.prepend (Step.matrix_recursive_pc18 ..)
    apply Reaches.prepend (Step.matrix_recursive_pc17 ..)
    apply Reaches.prepend (Step.matrix_recursive_pc16 ..)
    apply Reaches.prepend (Step.matrix_recursive_pc15 _ _ _ valid)
    apply Reaches.prepend (Step.matrix_recursive_pc14 ..)
    simpa only [initializeRows, show decide (state.v4 < state.v2) = true by simp only [decide_eq_true_eq]; omega] using execution

theorem initializeRows_extends (before heap : Heap) (c : CollectionRef) (first : Int) (count : Nat)
    (extension : Extends before heap) (fresh : before.nextCollection ≤ c) :
    Extends before (initializeRows heap c first count) := by
  induction count generalizing heap first with
  | zero => exact extension
  | succ count ih =>
    exact ih _ _ ((extension.trans (extends_allocate heap _)).set c fresh first heap.nextRef)

@[simp] theorem initializeRows_clocks (heap : Heap) (c : CollectionRef) (first : Int) (count : Nat) :
    (initializeRows heap c first count).clocks = heap.clocks := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih => simp only [initializeRows, ih]; rfl





@[simp] theorem zeroHeap_clocks (heap : Heap) (n : Nat) : (zeroHeap heap n).clocks = heap.clocks := by
  simp only [zeroHeap, initializeRows_clocks]; rfl

theorem zeroHeap_extends (heap : Heap) (n : Nat) : Extends heap (zeroHeap heap n) := by
  apply initializeRows_extends
  · exact (extends_allocate heap _).trans (extends_const _ _)
  · exact Nat.le_refl _

theorem zeroHeap_rows (heap : Heap) (n : Nat) :
    HasRows (zeroHeap heap n) heap.nextCollection (outputRows heap n) := by
  refine ⟨?_, ?_⟩
  · simp only [zeroHeap, initializeRows_valid]
    exact seq_Seq_Int.valid_const _ _
  · intro i
    by_cases inside : 0 ≤ i ∧ i < n
    · constructor
      · rw [zeroHeap, initializeRows_get_inside (seq_Seq_Int.const (heap.allocate (fun _ => 0)) heap.nextRef).1 heap.nextCollection 0 i n (show seq_Seq_Int.valid _ heap.nextCollection from seq_Seq_Int.valid_const (heap.allocate (fun _ => 0)) heap.nextRef) inside.1 (by omega)]
        simp [outputRows, inside, SequenceType.const, SequenceType.create, Heap.createSequence, Heap.allocate]
      · simp only [outputRows, if_pos inside, zeroHeap, initializeRows_nextRef]
        change heap.nextRef + 1 + i.toNat < heap.nextRef + 1 + n
        omega
    · constructor
      · rw [zeroHeap, initializeRows_get_outside _ _ _ _ _ (by omega)]
        simp only [outputRows, if_neg inside]
        exact seq_Seq_Int.get_const (heap.allocate (fun _ => 0)) heap.nextRef i
      · simp only [outputRows, if_neg inside, zeroHeap, initializeRows_nextRef]
        change heap.nextRef < heap.nextRef + 1 + n
        omega

theorem zeroHeap_zero (heap : Heap) (n : Nat) (i : Int) :
    (zeroHeap heap n).store (outputRows heap n i) = fun _ => 0 := by
  by_cases inside : 0 ≤ i ∧ i < n
  · apply initializeRows_store_new
    · simp only [outputRows, if_pos inside]
      change heap.nextRef + 1 ≤ heap.nextRef + 1 + i.toNat
      omega
    · simp only [outputRows, if_pos inside]
      change heap.nextRef + 1 + i.toNat < heap.nextRef + 1 + n
      omega
  · simp only [zeroHeap, outputRows, if_neg inside]
    rw [initializeRows_store_old]
    · simp [SequenceType.const, SequenceType.create, Heap.createSequence, Heap.allocate]
    · change heap.nextRef < heap.nextRef + 1
      omega

theorem outputRows_distinct (heap : Heap) (n : Nat) (i j : Int) (low : 0 ≤ j) (high : j < n) :
    outputRows heap n i = outputRows heap n j ↔ i = j := by
  by_cases inside : 0 ≤ i ∧ i < n
  · simp only [outputRows, if_pos inside, if_pos (show 0 ≤ j ∧ j < (n : Int) from ⟨low, high⟩)]
    change (heap.nextRef + 1 + i.toNat = heap.nextRef + 1 + j.toNat ↔ i = j)
    omega
  · simp only [outputRows, if_neg inside, if_pos (show 0 ≤ j ∧ j < (n : Int) from ⟨low, high⟩)]
    change (heap.nextRef = heap.nextRef + 1 + j.toNat ↔ i = j)
    omega

theorem outputRows_fresh (heap : Heap) (n : Nat) (i : Int) : heap.nextRef ≤ outputRows heap n i := by
  unfold outputRows
  split <;> omega



theorem stored_hasRows (heap : Heap) (matrix : CollectionRef) (values : Values)
    (stored : Stored heap matrix values) : HasRows heap matrix (inputRows heap matrix) := by
  refine ⟨stored.1, fun i => ?_⟩
  obtain ⟨row, read, valid, _⟩ := stored.2 i
  change seq_Seq_Int.get heap matrix i = some ((seq_Seq_Int.get heap matrix i).getD 0) ∧ _
  change seq_Seq_Int.get heap matrix i = some row at read
  simp [inputRows, read, valid]

theorem hasRows_mono (before after : Heap) (matrix : CollectionRef) (rs : Int → SeqRef)
    (view : HasRows before matrix rs) (extension : Extends before after) : HasRows after matrix rs := by
  refine ⟨extension.valid view.1, fun i => ?_⟩
  exact ⟨(extension.get view.1 i).trans (view.2 i).1, Nat.lt_of_lt_of_le (view.2 i).2 extension.nextRef⟩

theorem blockEffect_extends (depth : Nat) (before heap : Heap) (a b c : Int → SeqRef)
    (stride row col inner : Int) (extension : Extends before heap)
    (fresh : ∀ i, before.nextRef ≤ c i) :
    Extends before (blockEffect a b c stride depth heap row col inner) := by
  induction depth generalizing heap row col inner with
  | zero =>
    exact ((extension.trans (extends_tick heap "calls" 1)).trans
      (extends_tick (heap.tick "calls") "multiplications" 1)).write (c row) (fresh row) _ _
  | succ depth ih =>
    simp only [blockEffect]
    repeat apply ih
    exact extension.trans (extends_tick heap "calls" 1)



/-- Complete the multiplication once the independent output rows exist. -/
private theorem recursive_finish (depth : Nat) (heap : Heap) (state : State_matrix_recursive)
    (ar br cr : Int → SeqRef) (stack : Stack)
    (ha : HasRows heap state.v0 ar) (hb : HasRows heap state.v1 br) (hc : HasRows heap state.v3 cr)
    (size : state.v2 = (2 ^ depth : Nat)) :
    Reaches Step (.active heap (.fn_matrix_recursive 11 state) stack)
      (resumeConfig (blockEffect ar br cr (2 ^ depth : Nat) depth heap 0 0 0)
        (.fn_matrix_recursive state.v3) stack) := by
  apply Reaches.prepend (Step.matrix_recursive_pc11 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc10 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc9 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc8 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc7 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc6 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc5 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc4 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc3 ..)
  simp only [size]
  apply Reaches.trans ((block_summary depth heap state.v0 state.v1 state.v3 ar br cr
    (2 ^ depth : Nat) 0 0 0 ha hb hc).2 _)
  apply Reaches.prepend (Step.matrix_recursive_pc2 ..)
  exact Reaches.single (Step.matrix_recursive_pc1 _ _ _ ((hasRows_effect _ _ _ _ _ _ _ _ _ _ _).mpr hc).1)



private theorem recursive_start (heap : Heap) (a b : CollectionRef) (n : Int) (stack : Stack) :
    Reaches Step (.active heap (.fn_matrix_recursive 24 { v0 := a, v1 := b, v2 := n }) stack)
      (.active (seq_Seq_Int.const (heap.allocate (fun _ => 0)) heap.nextRef).1
        (.fn_matrix_recursive 13 (initializationState heap a b n)) stack) := by
  apply Reaches.prepend (Step.matrix_recursive_pc24 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc23 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc22 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc21 ..)
  apply Reaches.prepend (Step.matrix_recursive_pc20 ..)
  exact Reaches.refl _

/-- The public function allocates independent output rows and finishes all calls.
    Input matrices and arbitrary sharing among their rows are permitted. -/
theorem recursive_summary (depth : Nat) (heap : Heap) (a b : CollectionRef) (av bv : Values)
    (ha : Stored heap a av) (hb : Stored heap b bv) :
    matrix_recursive.Call heap (a, b, (2 ^ depth : Nat))
      (resultHeap heap a b depth) heap.nextCollection := by
  have ext := zeroHeap_extends heap (2 ^ depth)
  have ar := hasRows_mono _ _ _ _ (stored_hasRows _ _ _ ha) ext
  have br := hasRows_mono _ _ _ _ (stored_hasRows _ _ _ hb) ext
  have cr := zeroHeap_rows heap (2 ^ depth)
  refine ⟨⟨ha.1, hb.1⟩, ?_⟩
  intro stack
  let state := initializationState heap a b (2 ^ depth : Nat)
  obtain ⟨finalState, allocationRun, h0, h1, h2, h3⟩ := initializeRows_execution (2 ^ depth)
    (seq_Seq_Int.const (heap.allocate (fun _ => 0)) heap.nextRef).1 state stack
    (show seq_Seq_Int.valid (seq_Seq_Int.const (heap.allocate (fun _ => 0)) heap.nextRef).1 state.v3 from
      by simpa only [state, initializationState, SequenceType.const, SequenceType.create,
        Heap.createSequence, Heap.allocate] using seq_Seq_Int.valid_const (heap.allocate (fun _ => 0)) heap.nextRef)
    (by simp [state, initializationState])
  dsimp only [state, initializationState] at h0 h1 h2 h3
  have completed := recursive_finish depth (zeroHeap heap (2 ^ depth)) finalState
    (inputRows heap a) (inputRows heap b) (outputRows heap (2 ^ depth)) stack
    (by simpa only [h0] using ar) (by simpa only [h1] using br) (by simpa only [h3] using cr) h2
  apply Reaches.trans (recursive_start heap a b (2 ^ depth : Nat) stack)
  apply Reaches.trans allocationRun
  simpa only [h3, resultHeap, state, initializationState, zeroHeap] using completed



theorem result_heap_correct (heap : Heap) (a b : CollectionRef) (av bv : Values) (depth : Nat)
    (ha : Stored heap a av) (hb : Stored heap b bv) :
    Stored (resultHeap heap a b depth) heap.nextCollection (matrixProduct av bv (2 ^ depth)) := by
  have old := zeroHeap_extends heap (2 ^ depth)
  have inputA := stored_hasRows heap a av ha
  have inputB := stored_hasRows heap b bv hb
  have sepA : ∀ i j, inputRows heap a i ≠ outputRows heap (2 ^ depth) j := by
    intro i j
    have lower := outputRows_fresh heap (2 ^ depth) j
    have upper := (inputA.2 i).2
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le upper lower)
  have sepB : ∀ i j, inputRows heap b i ≠ outputRows heap (2 ^ depth) j := by
    intro i j
    have lower := outputRows_fresh heap (2 ^ depth) j
    have upper := (inputB.2 i).2
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le upper lower)
  have inputsA : (fun i => (zeroHeap heap (2 ^ depth)).store (inputRows heap a i)) = av := by
    funext i j
    rw [old.store _ (inputA.2 i).2]
    exact ha.read i j
  have inputsB : (fun i => (zeroHeap heap (2 ^ depth)).store (inputRows heap b i)) = bv := by
    funext i j
    rw [old.store _ (inputB.2 i).2]
    exact hb.read i j
  have view := (hasRows_effect depth (zeroHeap heap (2 ^ depth)) (inputRows heap a) (inputRows heap b)
    (outputRows heap (2 ^ depth)) (outputRows heap (2 ^ depth)) (2 ^ depth : Nat) 0 0 0 heap.nextCollection).mpr
      (zeroHeap_rows heap (2 ^ depth))
  refine ⟨view.1, fun row => ⟨outputRows heap (2 ^ depth) row, (view.2 row).1, (view.2 row).2, ?_⟩⟩
  funext col
  have correct := blockEffect_correct depth (zeroHeap heap (2 ^ depth)) (inputRows heap a) (inputRows heap b)
    (outputRows heap (2 ^ depth)) (2 ^ depth : Nat) 0 0 0 row col sepA sepB
    (outputRows_distinct heap (2 ^ depth)) (by omega) (by simp)
  rw [inputsA, inputsB] at correct
  simpa only [resultHeap, Heap.read, zeroHeap_zero, contribution, Int.zero_add,
    matrixProduct, innerProduct_eq_sum] using correct

/-- All preexisting rows, outer arrays and objects are unchanged. -/
theorem result_heap_preserves (heap : Heap) (a b : CollectionRef) (depth : Nat) :
    Extends heap (resultHeap heap a b depth) :=
  blockEffect_extends depth heap _ _ _ _ _ _ _ _ (zeroHeap_extends heap (2 ^ depth))
    (outputRows_fresh heap (2 ^ depth))



/-- Termination, full matrix correctness, preservation, and exact costs. -/
theorem output_with_cost (heap : Heap) (a b : CollectionRef) (av bv : Values) (depth : Nat)
    (ha : Stored heap a av) (hb : Stored heap b bv) :
    matrix_recursive.ReturnsWithCost (heap, a, b, (2 ^ depth : Nat))
      (resultHeap heap a b depth, heap.nextCollection) (costs depth) := by
  refine ⟨(recursive_summary depth heap a b av bv ha hb).run, ?_⟩
  funext clock
  simp [Heap.cost, resultHeap, costs, matrix_recursive.load]

/-- Closed form for recursive-call overhead, avoiding truncated division. -/
theorem callCount_exact (depth : Nat) : 7 * callCount depth + 1 = 8 ^ (depth + 1) := by
  induction depth with
  | zero => decide
  | succ depth ih => simp only [callCount, Nat.pow_succ] at *; omega

/-- Both scalar work and recursive-call overhead are cubic in matrix dimension. -/
theorem runtime_bounds (depth : Nat) :
    costs depth "multiplications" = (2 ^ depth) ^ 3 ∧
    8 ^ depth ≤ costs depth "calls" ∧ costs depth "calls" ≤ 2 * 8 ^ depth := by
  have exactCalls := callCount_exact depth
  have positive : 0 < (8 ^ depth : Nat) := Nat.pow_pos (by decide)
  simp only [Nat.pow_succ] at exactCalls
  change 8 ^ depth = (2 ^ depth) ^ 3 ∧ 8 ^ depth ≤ callCount depth ∧ callCount depth ≤ 2 * 8 ^ depth
  exact ⟨multiplications_cubic depth, by omega, by omega⟩

theorem transitions_deterministic : Deterministic Step := by
  intro before left right first second
  cases first <;> cases second <;> simp_all


-- Main result: Running time
/-- For n = 2^depth, every execution charges n³ scalar multiplications and between
    n³ and 2n³ recursive calls: at most 3n³ total units, hence Θ(n³) counted work.
    This theorem fixes the output heap and exact clocks; `runtime_bounds` bounds
    those clocks. Array allocations, loop bookkeeping, and integer bit complexity
    are excluded. -/
theorem output_with_cost_iff (heap finalHeap : Heap) (a b result : CollectionRef)
    (av bv : Values) (depth : Nat) (charged : Clocks)
    (ha : Stored heap a av) (hb : Stored heap b bv) :
    matrix_recursive.ReturnsWithCost (heap, a, b, (2 ^ depth : Nat)) (finalHeap, result) charged ↔
      finalHeap = resultHeap heap a b depth ∧ result = heap.nextCollection ∧ charged = costs depth := by
  have canonical := output_with_cost heap a b av bv depth ha hb
  constructor
  · intro completed
    have same := Reaches.eq_of_terminal (step := Step) transitions_deterministic
      completed.1.2 canonical.1.2
      (by intro next impossible; cases impossible)
      (by intro next impossible; cases impossible)
    have heaps : finalHeap = resultHeap heap a b depth := by cases same; rfl
    have refs : result = heap.nextCollection := by cases same; rfl
    refine ⟨heaps, refs, ?_⟩
    exact completed.2.symm.trans (heaps ▸ canonical.2)
  · rintro ⟨rfl, rfl, rfl⟩
    exact canonical

-- Main result: Correctness




/-- Completed outputs have fresh, valid, pairwise distinct rows in the finite
    square. Shared input rows impose no separation requirement on the inputs. -/
theorem every_execution_fresh_rows (heap finalHeap : Heap) (a b result : CollectionRef)
    (av bv : Values) (depth : Nat) (ha : Stored heap a av) (hb : Stored heap b bv)
    (run : matrix_recursive.Returns (heap, a, b, (2 ^ depth : Nat)) (finalHeap, result)) :
    result = heap.nextCollection ∧
    (∀ i : Int, 0 ≤ i → i < (2 ^ depth : Nat) →
      seq_Seq_Int.get finalHeap result i = some (heap.nextRef + 1 + i.toNat) ∧
      heap.nextRef < heap.nextRef + 1 + i.toNat ∧ heap.nextRef + 1 + i.toNat < finalHeap.nextRef) ∧
    (∀ i j : Int, 0 ≤ i → i < (2 ^ depth : Nat) → 0 ≤ j → j < (2 ^ depth : Nat) →
      (seq_Seq_Int.get finalHeap result i = seq_Seq_Int.get finalHeap result j ↔ i = j)) := by
  obtain ⟨charged, completed⟩ := run.withCost
  obtain ⟨rfl, rfl, _⟩ := (output_with_cost_iff heap finalHeap a b result av bv depth charged ha hb).mp completed
  have view : HasRows (resultHeap heap a b depth) heap.nextCollection (outputRows heap (2 ^ depth)) :=
    (hasRows_effect _ _ _ _ _ _ _ _ _ _ _).mpr (zeroHeap_rows heap (2 ^ depth))
  refine ⟨rfl, ?_, ?_⟩
  · intro i nonneg bound
    have found := view.2 i
    simp only [outputRows, if_pos (show 0 ≤ i ∧ i < ((2 ^ depth : Nat) : Int) from ⟨nonneg, bound⟩)] at found
    exact ⟨found.1, by omega, found.2⟩
  · intro i j ni bi nj bj
    rw [(view.2 i).1, (view.2 j).1]
    simpa only [Option.some.injEq] using outputRows_distinct heap (2 ^ depth) i j nj bj

end MatrixRecursiveAnalysis

end CLRS
end

section
namespace CLRS

/-!
Clock contracts describe increments from the caller's actual initial heap.
Weighted and amortized bounds compose on the same finite call witness used
for correctness; no counter is reset and no second execution is selected.
-/

namespace Algo2LeanGenerated

















theorem Heap.Increments.cost {before after : Heap} {costs : Clocks}
    (effect : before.Increments after costs) : Heap.cost before after = costs := by
  funext name
  simp [Heap.cost, effect name]

















namespace CallCost

universe u
variable {State : Type u}











end CallCost
end Algo2LeanGenerated

end CLRS
end

section
namespace CLRS

/-!
Publication-facing total-correctness contracts for the three CLRS Chapter 4
matrix programs. Every result uses the actual generated `Call` relation and the
same final heap for its mathematical answer, preservation, allocation, and cost.
The positive runtime constant is chosen before all dimensions and input heaps.

Inputs are genuine arrays of integer row arrays. `Stored` requires allocated
outer and row references at every integer index; the rows may share references.
The returned finite rows are fresh and pairwise distinct. Outside the finite
square the returned values are zero. Work counts the explicitly named source
ticks, excluding uncharged allocation/bookkeeping and integer bit complexity.
-/

open Algo2LeanCore Algo2LeanGenerated Algo2LeanCore.MatrixHeap

namespace Chapter4Publication







private theorem finiteSum_eq_dot (a b : Values) (row column : Int) (n : Nat) :
    MatrixRecursiveAnalysis.finiteSum n (fun inner => a row inner * b inner column) =
      Chapter4Math.dot n (fun inner => a row inner) (fun inner => b inner column) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [MatrixRecursiveAnalysis.finiteSum, Chapter4Math.dot, ih]

private theorem recursive_product (n : Nat) (a b : Values) :
    MatrixRecursiveAnalysis.matrixProduct a b n = product n a b := by
  funext row column
  simp only [MatrixRecursiveAnalysis.matrixProduct, product]
  split
  · exact finiteSum_eq_dot a b row column n
  · rfl



namespace MatrixMultiply



-- Main result: Correctness and running time


end MatrixMultiply

namespace MatrixRecursive



-- Main result: Correctness and running time


end MatrixRecursive

namespace Strassen





-- Main result: Correctness and running time


end Strassen
end Chapter4Publication

end CLRS
end

namespace CLRS
end CLRS
open CLRS
open Algo2LeanCore Algo2LeanGenerated Algo2LeanCore.MatrixHeap
namespace CLRS.Chapter4Publication
end CLRS.Chapter4Publication
open CLRS.Chapter4Publication
namespace CLRS.Chapter4Publication.MatrixRecursive
end CLRS.Chapter4Publication.MatrixRecursive
open CLRS.Chapter4Publication CLRS.Chapter4Publication.MatrixRecursive

theorem solution :
    ∃ C : Nat, 0 < C ∧
      ∀ (heap : Heap) (a b : CollectionRef) (av bv : Values) (depth : Nat),
        Stored heap a av → Stored heap b bv →
        ∃ after result,
          MatrixRecursiveLibrary.matrix_recursive.Call heap (a, b, ((2^depth : Nat) : Int)) after result ∧
          Stored after result (product (2^depth) av bv) ∧ Extends heap after ∧
          heap.nextCollection ≤ result ∧ result < after.nextCollection ∧
          FreshRows heap after result (2^depth) ∧
          heap.Increments after (MatrixRecursiveAnalysis.costs depth) ∧
          ((2^depth : Nat)^3) ≤ runtime (heap.cost after) ∧
          runtime (heap.cost after) ≤ C*((2^depth : Nat)^3) := by
  refine ⟨3, by decide, ?_⟩
  intro heap a b av bv depth sa sb
  let after := MatrixRecursiveAnalysis.resultHeap heap a b depth
  have call := MatrixRecursiveAnalysis.recursive_summary depth heap a b av bv sa sb
  have stored := MatrixRecursiveAnalysis.result_heap_correct heap a b av bv depth sa sb
  have frame := MatrixRecursiveAnalysis.result_heap_preserves heap a b depth
  have fresh := MatrixRecursiveAnalysis.every_execution_fresh_rows
    heap after a b heap.nextCollection av bv depth sa sb call.run
  have increments : heap.Increments after (MatrixRecursiveAnalysis.costs depth) := by
    intro clock
    simp [after, MatrixRecursiveAnalysis.resultHeap, MatrixRecursiveAnalysis.costs]
  refine ⟨after, heap.nextCollection, call, ?_, frame, Nat.le_refl _, stored.1.1, ?_, increments, ?_⟩
  · simpa only [recursive_product] using stored
  · constructor
    · intro i hi
      obtain ⟨read, lower, upper⟩ := fresh.2.1 (i : Int) (by omega) (by omega)
      exact ⟨heap.nextRef + 1 + i, read, Nat.le_of_lt lower, upper⟩
    · intro i j hi hj equal
      have same := (fresh.2.2 (i : Int) (j : Int) (by omega) (by omega) (by omega) (by omega)).mp equal
      exact_mod_cast same
  · rw [increments.cost]
    have bounds := MatrixRecursiveAnalysis.runtime_bounds depth
    have powers := MatrixRecursiveAnalysis.multiplications_cubic depth
    unfold runtime
    omega
