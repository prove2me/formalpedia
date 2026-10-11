-- Prove2me | solution 1 for CLRS.Chapter4Publication.MatrixMultiply.correctness_and_running_time
-- status  : ACCEPTED   (prove)
-- author  : @Chutong
-- created : 2026-10-11T06:34:31.476094+00:00
-- url     : https://prove2.me/submissions/98fe52de-f746-42e3-8f07-2b192ec4a36e

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





/-- Reuse a local preservation theorem without constructing a transcript. -/
theorem invariant {initial : State} {states : List State} {final : State} (h : Valid step initial states final) (property : State → Prop)
    (atStart : property initial)
    (preserve : ∀ a b, step a b → property a → property b) : property final := by
  induction h with
  | single => exact atStart
  | cons transition _ ih => exact ih (preserve _ _ transition atStart)



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

theorem invariant {a : State} {b : State} (run : Reaches step a b) (property : State → Prop)
    (atStart : property a)
    (preserve : ∀ before after, step before after → property before → property after) : property b := by
  obtain ⟨_, transcript⟩ := run
  exact transcript.invariant property atStart preserve

end Reaches



theorem Summary.root {step : Algo2LeanCore.Config Heap Frame Result → Algo2LeanCore.Config Heap Frame Result → Prop} {heap : Heap} {frame : Frame} {heap' : Heap} {result : Result} (summary : Summary step heap frame heap' result) :
    Reaches step (start heap frame) (.done heap' result) := by
  simpa [start, resumeConfig] using summary []

end Algo2LeanCore

/- Integer sequences are mathematical objects, addressed by stable identities. -/
namespace Algo2LeanGenerated





























































/-- Combine adjacent increments of one counter. -/
theorem Heap.tick_add (h : Heap) (name : String) (a b : Nat) :
    (h.tick name a).tick name b = h.tick name (a + b) := by
  simp only [tick]
  congr 1
  funext clock
  by_cases same : clock = name <;> simp [same, Nat.add_assoc]





















































































































































































namespace SequenceType

variable {α : Type} (type : SequenceType α)



































end SequenceType

end Algo2LeanGenerated

end CLRS
end

section
namespace CLRS

namespace «MatrixMultiplyLibrary»

open _root_.CLRS.Algo2LeanGenerated

-- Generated by Algo2Lean 0.1.1 https://github.com/lunjiah/algo2lean
-- Generated direct transitions; outputs are completed valid transcripts.
namespace Algo2LeanGenerated



 -- temporary

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











-- Complete this function from the supplied local state, under any caller stack.

-- Object inputs carry their heap, preserving shared references and cycles.




-- Output and clock increments from one completed execution.




theorem matrix_multiply.Call.run {before input after output}
    (call : _root_.CLRS.MatrixMultiplyLibrary.matrix_multiply.Call before input after output) :
    _root_.CLRS.MatrixMultiplyLibrary.matrix_multiply.Run before input after output :=
  ⟨call.1, call.2.root⟩


end «MatrixMultiplyLibrary»

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

theorem Stored.mono {before after : Heap} {matrix : CollectionRef} {values : Values}
    (stored : Stored before matrix values) (extension : Extends before after) :
    Stored after matrix values := by
  refine ⟨extension.valid stored.1, ?_⟩
  intro i
  obtain ⟨row, read, valid, contents⟩ := stored.2 i
  exact ⟨row, (extension.get stored.1 i).trans read,
    Nat.lt_of_lt_of_le valid extension.nextRef, (extension.store row valid).trans contents⟩



















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

theorem stored_const (h : Heap) (row : SeqRef) (values : Seq) (valid : row < h.nextRef)
    (contents : h.store row = values) :
    Stored (rows.const h row).1 (rows.const h row).2 (fun _ => values) := by
  refine ⟨rows.valid_const h row, ?_⟩
  intro i
  exact ⟨row, rows.get_const h row i, valid, contents⟩

/-- Replace one row reference, leaving every other row value unchanged. -/
theorem Stored.set {h : Heap} {matrix : CollectionRef} {values : Values}
    (stored : Stored h matrix values) (i : Int) (row : SeqRef) (newValues : Seq)
    (valid : row < h.nextRef) (contents : h.store row = newValues) :
    Stored (rows.set h matrix i row) matrix
      (fun j => if j = i then newValues else values j) := by
  refine ⟨(rows.valid_set h matrix matrix i row).mpr stored.1, ?_⟩
  intro j
  by_cases same : j = i
  · subst j
    refine ⟨row, rows.get_set_same h matrix i row stored.1, valid, ?_⟩
    simpa [SequenceType.set, Heap.writeElement] using contents
  · obtain ⟨old, read, allocated, oldValues⟩ := stored.2 j
    refine ⟨old, ?_, allocated, ?_⟩
    · simpa only [rows.get_set_other_index h matrix j i row same] using read
    · simpa [same, SequenceType.set, Heap.writeElement] using oldValues

















end Algo2LeanCore.MatrixHeap

end CLRS
end

section
namespace CLRS

open MatrixMultiplyLibrary MatrixMultiplyLibrary.Algo2LeanGenerated

/-!
CLRS 4.1 on genuine arrays of row arrays. The inputs may share rows, including
with each other. A fresh row is allocated for every output row. The proof
constructs terminating executions and proves preservation of all pre-existing
objects, the mathematical matrix product, and exactly n³ scalar multiply-adds.
-/
open Algo2LeanCore Algo2LeanGenerated
open Algo2LeanCore.MatrixHeap

namespace MatrixMultiplyAnalysis









@[simp] theorem fill_nextRef (h : Heap) (r : SeqRef) (values : Seq) (first : Int) (count : Nat) :
    (fill h r values first count).nextRef = h.nextRef := by
  induction count generalizing h first with
  | zero => rfl
  | succ count ih => simp [fill, ih]

@[simp] theorem fill_clocks (h : Heap) (r : SeqRef) (values : Seq) (first : Int) (count : Nat) :
    (fill h r values first count).clocks = h.clocks := by
  induction count generalizing h first with
  | zero => rfl
  | succ count ih => simp [fill, ih]

@[simp] theorem fill_collections (h : Heap) (r : SeqRef) (values : Seq) (first : Int) (count : Nat) :
    (fill h r values first count).collections = h.collections := by
  induction count generalizing h first with
  | zero => rfl
  | succ count ih => simp [fill, ih]

@[simp] theorem fill_nextCollection (h : Heap) (r : SeqRef) (values : Seq) (first : Int) (count : Nat) :
    (fill h r values first count).nextCollection = h.nextCollection := by
  induction count generalizing h first with
  | zero => rfl
  | succ count ih => simpa [fill, Heap.write] using ih (h.write r first (values first)) (first + 1)



theorem fill_outside (h : Heap) (r : SeqRef) (values : Seq) (first i : Int) (count : Nat)
    (outside : i < first ∨ first + (count : Int) ≤ i) :
    (fill h r values first count).store r i = h.store r i := by
  induction count generalizing h first with
  | zero => rfl
  | succ count ih =>
    rw [fill, ih]
    · have ne : i ≠ first := by omega
      simp [Heap.write, ne]
    · omega

theorem fill_inside (h : Heap) (r : SeqRef) (values : Seq) (first i : Int) (count : Nat)
    (inside : first ≤ i ∧ i < first + (count : Int)) :
    (fill h r values first count).store r i = values i := by
  induction count generalizing h first with
  | zero => omega
  | succ count ih =>
    rw [fill]
    by_cases eq : i = first
    · subst i
      rw [fill_outside _ _ _ _ _ _ (Or.inl (by omega))]
      simp [Heap.write]
    · apply ih
      omega

@[simp] theorem write_tick (h : Heap) (r : SeqRef) (index value : Int) (amount : Nat) :
    (h.tick "multiply_add" amount).write r index value =
      (h.write r index value).tick "multiply_add" amount := rfl

@[simp] theorem fill_tick (h : Heap) (r : SeqRef) (values : Seq) (first : Int)
    (count amount : Nat) :
    fill (h.tick "multiply_add" amount) r values first count =
      (fill h r values first count).tick "multiply_add" amount := by
  induction count generalizing h first with
  | zero => rfl
  | succ count ih => exact ih (h.write r first (values first)) (first + 1)

/-- Finish a dot-product loop; nested inputs can share any of their row arrays. -/
theorem dot_loop (count : Nat) (state : Configuration)
    (a b : CollectionRef) (av bv : Values) (n row column first total : Int)
    (location : matrix_dot.At.dot_loop state)
    (ra : matrix_dot.Local.a state = some a)
    (rb : matrix_dot.Local.b state = some b)
    (rn : matrix_dot.Local.n state = some n)
    (rr : matrix_dot.Local.row state = some row)
    (rc : matrix_dot.Local.column state = some column)
    (rk : matrix_dot.Local.k state = some first)
    (rt : matrix_dot.Local.total state = some total)
    (bound : n = first + (count : Int))
    (va : Stored state.heap a av) (vb : Stored state.heap b bv) :
    matrix_dot.CallFrom state (state.heap.tick "multiply_add" count)
      (total + dotFrom av bv row column first count) := by
  cases state with
  | done => cases location
  | active h frame originalStack =>
    cases frame with
    | invalid => cases location
    | fn_matrix_multiply => cases location
    | fn_matrix_row => cases location
    | fn_matrix_dot pc s =>
      have atLoop : pc = 4 := by unfold matrix_dot.At.dot_loop at location; split at location <;> simp_all
      subst pc
      simp [matrix_dot.Local.a, matrix_dot.Local.b, matrix_dot.Local.n, matrix_dot.Local.row,
        matrix_dot.Local.column, matrix_dot.Local.k, matrix_dot.Local.total] at ra rb rn rr rc rk rt
      dsimp only [Config.heap] at va vb ⊢
      induction count generalizing h s first total with
      | zero =>
        intro stack
        apply Reaches.prepend (Step.matrix_dot_pc4 ..)
        apply Reaches.prepend (Step.matrix_dot_pc3_false _ _ _ (by simp; omega))
        apply Reaches.prepend (Step.matrix_dot_pc2 ..)
        simpa [dotFrom, rt] using Reaches.single (Step.matrix_dot_pc1 h _ stack)
      | succ count ih =>
        obtain ⟨ar, ag, arvalid, arvalues⟩ := va.2 row
        obtain ⟨br, bg, brvalid, brvalues⟩ := vb.2 first
        have next := ih (h := h.tick "multiply_add")
          (s := { s with v5 := first + 1, v6 := total + av row first * bv first column, t8 := decide (s.v5 < s.v2) }) (first := first + 1)
          (total := total + av row first * bv first column)
          (bound := by omega) (location := True.intro) (va := va) (vb := vb)
          (ra := ra) (rb := rb) (rn := rn) (rr := rr) (rc := rc) (rk := rfl) (rt := rfl)
        intro stack
        apply Reaches.prepend (Step.matrix_dot_pc4 ..)
        apply Reaches.prepend (Step.matrix_dot_pc3_true _ _ _ (by simp; omega))
        apply Reaches.prepend (Step.matrix_dot_pc7 ..)
        apply Reaches.prepend (Step.matrix_dot_pc6 _ _ _ (by
          simp [ra, rb, rr, rk, show seq_Seq_Int = rows from rfl, ag, bg, arvalid, brvalid]))
        apply Reaches.prepend (Step.matrix_dot_pc5 ..)
        simpa [dotFrom, ra, rb, rn, rr, rc, rk, rt, Heap.read, Heap.tick_add,
          Nat.add_comm 1, Int.add_assoc, show seq_Seq_Int = rows from rfl, ag, bg,
          arvalues, brvalues] using next stack

/-- One dot product costs exactly n scalar multiply-adds. -/
theorem dot_summary (h : Heap) (a b : CollectionRef) (av bv : Values)
    (n : Nat) (row column : Int) (va : Stored h a av) (vb : Stored h b bv) :
    matrix_dot.Call h (a, b, n, row, column) (h.tick "multiply_add" n)
      (entry av bv n row column) := by
  refine ⟨⟨va.1, vb.1⟩, ?_⟩
  intro stack
  apply Reaches.prepend (Step.matrix_dot_pc9 ..)
  apply Reaches.prepend (Step.matrix_dot_pc8 ..)
  have run := dot_loop n (.active h (.fn_matrix_dot 4
    { v0 := a, v1 := b, v2 := n, v3 := row, v4 := column }) stack)
    a b av bv n row column 0 0 True.intro rfl rfl rfl rfl rfl rfl rfl (by omega) va vb
  simpa [Config.heap, entry] using run stack

theorem fill_extends {before after : Heap} (extension : Extends before after)
    (r : SeqRef) (fresh : before.nextRef ≤ r) (values : Seq) (first : Int) (count : Nat) :
    Extends before (fill after r values first count) := by
  induction count generalizing after first with
  | zero => exact extension
  | succ count ih => exact ih (extension.write r fresh first (values first)) (first + 1)

/-- Complete one output row while preserving the original nested inputs. -/
theorem columns_loop (count : Nat) (state : Configuration) (original : Heap)
    (a b : CollectionRef) (av bv : Values) (result : SeqRef) (n : Nat) (row first : Int)
    (location : matrix_row.At.columns_loop state)
    (ra : matrix_row.Local.a state = some a)
    (rb : matrix_row.Local.b state = some b)
    (rn : matrix_row.Local.n state = some (n : Int))
    (rr : matrix_row.Local.row state = some row)
    (ro : matrix_row.Local.result state = some result)
    (ri : matrix_row.Local.column state = some first)
    (bound : first + (count : Int) = n)
    (va : Stored original a av) (vb : Stored original b bv)
    (extension : Extends original state.heap) (fresh : original.nextRef ≤ result)
    (valid : result < state.heap.nextRef) :
    matrix_row.CallFrom state
      ((fill state.heap result (entry av bv n row) first count).tick
        "multiply_add" (count * n)) result := by
  cases state with
  | done => cases location
  | active h frame originalStack =>
    cases frame with
    | invalid => cases location
    | fn_matrix_dot => cases location
    | fn_matrix_multiply => cases location
    | fn_matrix_row pc s =>
      have atLoop : pc = 4 := by unfold matrix_row.At.columns_loop at location; split at location <;> simp_all
      subst pc
      simp [matrix_row.Local.a, matrix_row.Local.b, matrix_row.Local.n,
        matrix_row.Local.row, matrix_row.Local.result, matrix_row.Local.column] at ra rb rn rr ro ri
      dsimp only [Config.heap] at extension valid ⊢
      induction count generalizing h s first with
      | zero =>
        intro stack
        apply Reaches.prepend (Step.matrix_row_pc4 ..)
        apply Reaches.prepend (Step.matrix_row_pc3_false _ _ _ (by simp [rn, ri]; omega))
        apply Reaches.prepend (Step.matrix_row_pc2 ..)
        simpa [fill, ro] using Reaches.single (Step.matrix_row_pc1 h _ stack (by simpa [ro] using valid))
      | succ count ih =>
        let value := entry av bv n row first
        let updated := (h.tick "multiply_add" n).write result first value
        have extended : Extends original updated :=
          (extension.trans (extends_tick h "multiply_add" n)).write result fresh first value
        have next := ih (h := updated)
          (s := { s with v5 := first + 1, v6 := value, t8 := decide (s.v5 < s.v2), t9 := value, t10 := a, t11 := b, t12 := n, t13 := row, t14 := first })
          (first := first + 1) (bound := by omega) (location := True.intro)
          (extension := extended) (valid := valid)
          (ra := ra) (rb := rb) (rn := rn) (rr := rr) (ro := ro) (ri := rfl)
        intro stack
        apply Reaches.prepend (Step.matrix_row_pc4 ..)
        apply Reaches.prepend (Step.matrix_row_pc3_true _ _ _ (by simp [ri, rn]; omega))
        apply Reaches.prepend (Step.matrix_row_pc13 ..)
        apply Reaches.prepend (Step.matrix_row_pc12 ..)
        apply Reaches.prepend (Step.matrix_row_pc11 ..)
        apply Reaches.prepend (Step.matrix_row_pc10 ..)
        apply Reaches.prepend (Step.matrix_row_pc9 ..)
        apply Reaches.prepend (Step.matrix_row_pc8 ..)
        simp only [rn]
        apply Reaches.trans ((dot_summary h s.v0 s.v1 av bv n s.v3 s.v5
          (by simpa [ra] using va.mono extension) (by simpa [rb] using vb.mono extension)).2 _)
        apply Reaches.prepend (Step.matrix_row_pc7 ..)
        apply Reaches.prepend (Step.matrix_row_pc6 _ _ _ (by simpa [ro] using valid))
        apply Reaches.prepend (Step.matrix_row_pc5 ..)
        simpa [value, updated, ra, rb, rn, rr, ro, ri,
          fill, fill_tick, Heap.tick_add, Nat.succ_mul, Nat.add_comm] using next stack





theorem row_summary (h : Heap) (a b : CollectionRef) (av bv : Values)
    (n : Nat) (row : Int) (va : Stored h a av) (vb : Stored h b bv) :
    matrix_row.Call h (a, b, n, row) (rowHeap h av bv n row) h.nextRef := by
  refine ⟨⟨va.1, vb.1⟩, ?_⟩
  intro stack
  apply Reaches.prepend (Step.matrix_row_pc17 ..)
  apply Reaches.prepend (Step.matrix_row_pc16 ..)
  apply Reaches.prepend (Step.matrix_row_pc15 ..)
  apply Reaches.prepend (Step.matrix_row_pc14 ..)
  have run := columns_loop n (.active (h.allocate (fun _ => 0))
    (.fn_matrix_row 4 { v0 := a, v1 := b, v2 := n, v3 := row, v4 := h.nextRef, t15 := h.nextRef }) stack)
    h a b av bv h.nextRef n row 0 True.intro rfl rfl rfl rfl rfl rfl (by omega)
    va vb (extends_allocate h _) (Nat.le_refl _) (by simp [Config.heap])
  simpa [Config.heap, rowHeap] using run stack

theorem rowHeap_extends (h : Heap) (av bv : Values) (n : Nat) (row : Int) :
    Extends h (rowHeap h av bv n row) :=
  (fill_extends (extends_allocate h _) h.nextRef (Nat.le_refl _) _ 0 n).trans
    (extends_tick _ "multiply_add" (n * n))

@[simp] theorem rowHeap_nextRef (h : Heap) (av bv : Values) (n : Nat) (row : Int) :
    (rowHeap h av bv n row).nextRef = h.nextRef + 1 := by simp [rowHeap]

@[simp] theorem rowHeap_nextCollection (h : Heap) (av bv : Values) (n : Nat) (row : Int) :
    (rowHeap h av bv n row).nextCollection = h.nextCollection := by
  simp [rowHeap, Heap.tick, Heap.allocate]



@[simp] theorem rowHeap_clocks (h : Heap) (av bv : Values) (n : Nat) (row : Int) :
    (rowHeap h av bv n row).clocks = (h.tick "multiply_add" (n * n)).clocks := by
  simp [rowHeap, Heap.tick]

theorem rowHeap_result (h : Heap) (av bv : Values) (n : Nat) (row : Int) :
    (rowHeap h av bv n row).store h.nextRef = rowValues av bv n row := by
  funext column
  simp only [rowHeap, Heap.tick_store, rowValues]
  split
  next inside => exact fill_inside _ _ _ _ _ _ (by simpa using inside)
  next outside =>
    rw [fill_outside _ _ _ _ _ _ (by omega)]
    simp [Heap.allocate]



theorem partialProduct_zero (av bv : Values) (n : Nat) :
    partialProduct av bv n 0 = fun _ _ => 0 := by
  funext row column
  simp [partialProduct, show ¬ (0 ≤ row ∧ row < 0) by omega]

theorem partialProduct_done (av bv : Values) (n : Nat) :
    partialProduct av bv n n = product av bv n := by
  funext row column
  by_cases vr : 0 ≤ row ∧ row < (n : Int) <;>
    by_cases vc : 0 ≤ column ∧ column < (n : Int) <;>
    simp [partialProduct, rowValues, product, vr, vc]

theorem partialProduct_step (av bv : Values) (n : Nat) (first : Int) (nonnegative : 0 ≤ first) :
    (fun row => if row = first then rowValues av bv n first else partialProduct av bv n first row) =
      partialProduct av bv n (first + 1) := by
  funext row column
  by_cases same : row = first
  · subst row
    simp [partialProduct, nonnegative, show first < first + 1 by omega]
  · have equivalent : (0 ≤ row ∧ row < first + 1) ↔ (0 ≤ row ∧ row < first) := by omega
    simp [same, partialProduct, equivalent]



/-- Finish the outer loop, allocating a new independent row on each iteration. -/
theorem rows_loop (count : Nat) (state : Configuration) (original : Heap)
    (a b result : CollectionRef) (av bv : Values) (n : Nat) (first : Int)
    (location : matrix_multiply.At.rows_loop state)
    (ra : matrix_multiply.Local.a state = some a)
    (rb : matrix_multiply.Local.b state = some b)
    (rn : matrix_multiply.Local.n state = some (n : Int))
    (rr : matrix_multiply.Local.result state = some result)
    (ri : matrix_multiply.Local.row state = some first)
    (bound : first + (count : Int) = n) (nonnegative : 0 ≤ first)
    (va : Stored original a av) (vb : Stored original b bv)
    (extension : Extends original state.heap) (fresh : original.nextCollection ≤ result)
    (current : Stored state.heap result (partialProduct av bv n first))
    (base : Nat) (allocated : state.heap.nextRef = base + first.toNat)
    (references : RowReferences state.heap result base first.toNat) :
    ∃ after, matrix_multiply.CallFrom state after result ∧ Extends original after ∧
      Stored after result (product av bv n) ∧
      after.clocks = (state.heap.tick "multiply_add" (count * (n * n))).clocks ∧
      after.nextRef = base + n ∧ RowReferences after result base n := by
  cases state with
  | done => cases location
  | active h frame originalStack =>
    cases frame with
    | invalid => cases location
    | fn_matrix_dot => cases location
    | fn_matrix_row => cases location
    | fn_matrix_multiply pc s =>
      have atLoop : pc = 4 := by unfold matrix_multiply.At.rows_loop at location; split at location <;> simp_all
      subst pc
      simp [matrix_multiply.Local.a, matrix_multiply.Local.b, matrix_multiply.Local.n,
        matrix_multiply.Local.result, matrix_multiply.Local.row] at ra rb rn rr ri
      dsimp only [Config.heap] at extension current allocated references ⊢
      induction count generalizing h s first with
      | zero =>
        have firstEq : first = n := by omega
        refine ⟨h, ?_, extension, ?_, by simp, ?_, ?_⟩
        · intro stack
          apply Reaches.prepend (Step.matrix_multiply_pc4 ..)
          apply Reaches.prepend (Step.matrix_multiply_pc3_false _ _ _ (by simp [rn, ri]; omega))
          apply Reaches.prepend (Step.matrix_multiply_pc2 ..)
          simpa [rr] using Reaches.single (Step.matrix_multiply_pc1 h _ stack
            (by simpa [rr, show seq_Seq_Int = rows from rfl] using current.1))
        · simpa only [firstEq, partialProduct_done] using current
        · simpa [firstEq] using allocated
        · simpa [firstEq] using references
      | succ count ih =>
        let completed := rowHeap h av bv n first
        let updated := rows.set completed result first h.nextRef
        have rowExtension := rowHeap_extends h av bv n first
        have extended : Extends original updated :=
          (extension.trans rowExtension).set result fresh first h.nextRef
        have nextStored : Stored updated result (partialProduct av bv n (first + 1)) := by
          have installed := (current.mono rowExtension).set first h.nextRef
            (rowValues av bv n first) (by simp) (rowHeap_result h av bv n first)
          simpa only [partialProduct_step av bv n first nonnegative] using installed
        have nextAllocated : updated.nextRef = base + (first + 1).toNat := by
          have nextIndex : (first + 1).toNat = first.toNat + 1 := by omega
          simp [updated, completed, SequenceType.set, nextIndex, allocated, Nat.add_assoc]
        have nextReferences : RowReferences updated result base (first + 1).toNat := by
          intro i validIndex
          by_cases currentRow : (i : Int) = first
          · have eq : i = first.toNat := by omega
            change rows.get (rows.set completed result first h.nextRef) result (i : Int) = some (base + i)
            rw [currentRow, rows.get_set_same _ _ _ _ (rowExtension.valid current.1), allocated, eq]
          · have earlier : i < first.toNat := by omega
            rw [show rows.get updated result i = rows.get completed result i from
              rows.get_set_other_index _ _ _ _ _ currentRow]
            exact (rowExtension.get current.1 i).trans (references i earlier)
        obtain ⟨after, next, preserved, finalValues, clocks, finalAllocated, finalReferences⟩ := ih (h := updated)
          (s := { s with v4 := first + 1, t6 := decide (s.v4 < s.v2), t7 := h.nextRef, t8 := first, t9 := result, t10 := a, t11 := b, t12 := n, t13 := first })
          (first := first + 1) (bound := by omega) (nonnegative := by omega)
          (location := True.intro) (extension := extended) (current := nextStored)
          (allocated := nextAllocated) (references := nextReferences)
          (ra := ra) (rb := rb) (rn := rn) (rr := rr) (ri := rfl)
        refine ⟨after, ?_, preserved, finalValues, ?_, finalAllocated, finalReferences⟩
        · intro stack
          apply Reaches.prepend (Step.matrix_multiply_pc4 ..)
          apply Reaches.prepend (Step.matrix_multiply_pc3_true _ _ _ (by simp [ri, rn]; omega))
          apply Reaches.prepend (Step.matrix_multiply_pc13 ..)
          apply Reaches.prepend (Step.matrix_multiply_pc12 ..)
          apply Reaches.prepend (Step.matrix_multiply_pc11 ..)
          apply Reaches.prepend (Step.matrix_multiply_pc10 ..)
          apply Reaches.prepend (Step.matrix_multiply_pc9 ..)
          simp only [rn]
          apply Reaches.trans ((row_summary h s.v0 s.v1 av bv n s.v4
            (by simpa [ra] using va.mono extension) (by simpa [rb] using vb.mono extension)).2 _)
          apply Reaches.prepend (Step.matrix_multiply_pc8 ..)
          apply Reaches.prepend (Step.matrix_multiply_pc7 ..)
          apply Reaches.prepend (Step.matrix_multiply_pc6 _ _ _ (by
            simpa [rr, ri, show seq_Seq_Int = rows from rfl] using rowExtension.valid current.1))
          apply Reaches.prepend (Step.matrix_multiply_pc5 ..)
          simpa [updated, completed, ra, rb, rn, rr, ri, show seq_Seq_Int = rows from rfl] using next stack
        · rw [clocks]
          funext clock
          by_cases same : clock = "multiply_add" <;>
            simp [updated, completed, SequenceType.set, Heap.tick, Nat.succ_mul, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm, same]



/-- Total correctness, input preservation, and exact cost for every natural
    dimension, including zero. Inputs and their rows may alias arbitrarily. -/
theorem summary (h : Heap) (a b : CollectionRef) (av bv : Values) (n : Nat)
    (va : Stored h a av) (vb : Stored h b bv) :
    ∃ after, matrix_multiply.Call h (a, b, n) after h.nextCollection ∧
      Extends h after ∧ Stored after h.nextCollection (product av bv n) ∧
      Heap.cost h after = costs n ∧ after.nextRef = h.nextRef + 1 + n ∧
      RowReferences after h.nextCollection (h.nextRef + 1) n := by
  let zero := h.allocate (fun _ => 0)
  let initial := (rows.const zero h.nextRef).1
  have extension : Extends h initial :=
    (extends_allocate h _).trans (extends_const zero h.nextRef)
  have initialValues : Stored initial h.nextCollection (partialProduct av bv n 0) := by
    have stored := stored_const zero h.nextRef (fun _ => 0)
      (by simp [zero]) (by funext i; simp [zero, Heap.allocate])
    simpa [initial, zero, SequenceType.const, SequenceType.create, Heap.createSequence,
      partialProduct_zero] using stored
  obtain ⟨after, finish, preserved, values, clocks, allocated, references⟩ := rows_loop n
    (.active initial (.fn_matrix_multiply 4
      { v0 := a, v1 := b, v2 := n, v3 := h.nextCollection, t14 := h.nextCollection, t15 := h.nextRef }) [])
    h a b h.nextCollection av bv n 0 True.intro rfl rfl rfl rfl rfl (by omega) (by omega)
    va vb extension (Nat.le_refl _) initialValues (h.nextRef + 1) rfl (by intro i impossible; omega)
  refine ⟨after, ⟨⟨va.1, vb.1⟩, ?_⟩, preserved, values, ?_, allocated, references⟩
  · intro stack
    apply Reaches.prepend (Step.matrix_multiply_pc18 ..)
    apply Reaches.prepend (Step.matrix_multiply_pc17 ..)
    apply Reaches.prepend (Step.matrix_multiply_pc16 ..)
    apply Reaches.prepend (Step.matrix_multiply_pc15 ..)
    apply Reaches.prepend (Step.matrix_multiply_pc14 ..)
    exact finish stack
  · funext clock
    by_cases same : clock = "multiply_add" <;>
      simp [same, Heap.cost, clocks, costs, Clocks.single, Config.heap, initial, zero,
      SequenceType.const, SequenceType.create, Heap.createSequence, Heap.allocateSequence,
      Heap.tick, Nat.pow_succ, Nat.mul_assoc]

theorem transitions_deterministic : Deterministic Step := by
  intro before left right first second
  cases first <;> cases second <;> simp_all

/-- Any completed execution has the values, preservation, and cost of the
    terminating execution constructed above. -/
theorem execution_correct (h after : Heap) (a b result : CollectionRef)
    (av bv : Values) (n : Nat) (va : Stored h a av) (vb : Stored h b bv)
    (run : matrix_multiply.Run h (a, b, n) after result) :
    result = h.nextCollection ∧ Extends h after ∧ Stored after result (product av bv n) ∧
      Heap.cost h after = costs n ∧ after.nextRef = h.nextRef + 1 + n ∧
      RowReferences after result (h.nextRef + 1) n := by
  obtain ⟨final, call, extension, values, cost, allocated, references⟩ := summary h a b av bv n va vb
  have same := Reaches.eq_of_terminal (step := Step) transitions_deterministic
    run.2 call.2.root (by intro next impossible; cases impossible) (by intro next impossible; cases impossible)
  cases same
  exact ⟨rfl, extension, values, cost, allocated, references⟩





-- Main result: Correctness






-- Main result: Running time


/-- Every finite output row has a fresh identity, and different row indices
    have different identities. Thus later writes to one row cannot alias another. -/
theorem every_execution_fresh_rows (h after : Heap) (a b result : CollectionRef)
    (av bv : Values) (n : Nat) (va : Stored h a av) (vb : Stored h b bv)
    (run : matrix_multiply.Run h (a, b, n) after result) :
    (∀ i : Nat, i < n → rows.get after result i = some (h.nextRef + 1 + i) ∧
      h.nextRef < h.nextRef + 1 + i ∧ h.nextRef + 1 + i < after.nextRef) ∧
    (∀ i j : Nat, i < n → j < n → i ≠ j →
      rows.get after result i ≠ rows.get after result j) := by
  have correct := execution_correct h after a b result av bv n va vb run
  have allocated := correct.2.2.2.2.1
  have references := correct.2.2.2.2.2
  constructor
  · intro i valid
    exact ⟨references i valid, by omega, by omega⟩
  · intro i j vi vj different
    rw [references i vi, references j vj]
    intro same
    have equal : h.nextRef + 1 + i = h.nextRef + 1 + j := Option.some.inj same
    omega

end MatrixMultiplyAnalysis

end CLRS
end

section
namespace CLRS

open MatrixStrassenLibrary MatrixStrassenLibrary.Algo2LeanGenerated

/-! Generated by scripts/build_chapter4_analysis.py.
Edit the corresponding source modules in proofs/chapter4, then rebuild.
This bundle is checked against the actual generated algorithm and can
be loaded directly into the editor's Lean analysis pane. -/

/-! Source: proofs/chapter4/MatrixMath.lean -/

section

/-!
Finite integer-matrix algebra and arithmetic-operation recurrences for CLRS 4.

These are mathematical lemmas. An application to an Algo2Lean source program
must additionally prove that the generated execution relation implements these
operations and charges these recurrences; this file alone makes no such claim.
Matrices are unbounded mathematical functions; `mul n` reads the first n inner
coordinates. In applications n is the finite matrix dimension.
-/
namespace Chapter4Math













end Chapter4Math

namespace Chapter4Math

/-- Split a dot product at an arbitrary finite inner coordinate. -/
theorem dot_append (n m : Nat) (a b : Vector) :
    dot (n + m) a b = dot n a b +
      dot m (fun k => a (n + k)) (fun k => b (n + k)) := by
  induction m with
  | zero => simp [dot]
  | succ m ih =>
    change dot (n + m) a b + a (n + m) * b (n + m) =
      dot n a b + (dot m (fun k => a (n + k)) (fun k => b (n + k)) +
        a (n + m) * b (n + m))
    rw [ih]
    omega





































end Chapter4Math

namespace Chapter4Math































end Chapter4Math

namespace Chapter4Math





end Chapter4Math

end

/-! Source: proofs/chapter4/StrassenValue.lean -/

section

open Chapter4Math
namespace StrassenValues



































end StrassenValues

end

/-! Source: proofs/chapter4/StrassenLinear.lean -/

section

open Algo2LeanCore Algo2LeanGenerated

namespace MatrixStrassenAnalysis

/- The source loops first receive reusable heap summaries. Matrix algebra and
   the recursive correctness argument then use these summaries as interfaces. -/

































end MatrixStrassenAnalysis

end

/-! Source: proofs/chapter4/StrassenHelpers.lean -/

section

open Algo2LeanCore Algo2LeanGenerated Algo2LeanCore.MatrixHeap
namespace MatrixStrassenHelpers

open MatrixStrassenAnalysis




































































end MatrixStrassenHelpers

end

/-! Source: proofs/chapter4/StrassenQuadrant.lean -/

section

/-! A square-block copy composes the verified row copier, preserving arbitrary
shared input rows while allocating the result row by row. -/
open Algo2LeanCore Algo2LeanGenerated Algo2LeanCore.MatrixHeap
namespace MatrixStrassenHelpers











end MatrixStrassenHelpers

end

/-! Source: proofs/chapter4/StrassenComposition.lean -/

section

/-! Composition of the recursive branch using only source-level call summaries.
Each field records one real source call in evaluation order, including nested
arguments. This lemma by itself assumes no mathematical correctness contract. -/

open Algo2LeanCore Algo2LeanGenerated

namespace MatrixStrassenComposition













end MatrixStrassenComposition

end

/-! Source: proofs/chapter4/StrassenExecution.lean -/

section

open Algo2LeanCore Algo2LeanGenerated MatrixStrassenAnalysis MatrixStrassenHelpers
open Algo2LeanCore.MatrixHeap
open MatrixStrassenComposition

namespace MatrixStrassenExecution

















end MatrixStrassenExecution

end

/-! Source: proofs/chapter4/StrassenDeterminism.lean -/

section

open Algo2LeanCore Algo2LeanGenerated
namespace MatrixStrassenDeterminism

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000









end MatrixStrassenDeterminism

end

/-! Source: proofs/chapter4/StrassenTheorems.lean -/

section

open Algo2LeanCore Algo2LeanGenerated
open Algo2LeanCore.MatrixHeap
open MatrixStrassenExecution
open StrassenValues (strassenValue  )

namespace MatrixStrassenVerified







-- Main result: Correctness












-- Main result: Running time


end MatrixStrassenVerified

end

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



















theorem Heap.ClocksMonotone.increments {before after : Heap}
    (monotone : before.ClocksMonotone after) :
    before.Increments after (Heap.cost before after) := by
  intro name
  have ordered := monotone name
  simp only [Heap.cost]
  omega















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



private theorem dotFrom_eq_dot (a b : Values) (row column first : Int) (n : Nat) :
    MatrixMultiplyAnalysis.dotFrom a b row column first n =
      Chapter4Math.dot n (fun inner => a row (first + inner))
        (fun inner => b (first + inner) column) := by
  induction n generalizing first with
  | zero => rfl
  | succ n ih =>
    rw [MatrixMultiplyAnalysis.dotFrom, ih]
    rw [show n + 1 = 1 + n by omega, Chapter4Math.dot_append]
    simp [Chapter4Math.dot, Int.natCast_add, Int.add_assoc]

private theorem multiply_product (n : Nat) (a b : Values) :
    MatrixMultiplyAnalysis.product a b n = product n a b := by
  funext row column
  simp only [MatrixMultiplyAnalysis.product, MatrixMultiplyAnalysis.entry, product]
  split
  · simpa using dotFrom_eq_dot a b row column 0 n
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
namespace CLRS.Chapter4Publication.MatrixMultiply
end CLRS.Chapter4Publication.MatrixMultiply
open CLRS.Chapter4Publication CLRS.Chapter4Publication.MatrixMultiply

theorem solution :
    ∃ C : Nat, 0 < C ∧
      ∀ (heap : Heap) (a b : CollectionRef) (av bv : Values) (n : Nat),
        Stored heap a av → Stored heap b bv →
        ∃ after result,
          MatrixMultiplyLibrary.matrix_multiply.Call heap (a, b, (n : Int)) after result ∧
          Stored after result (product n av bv) ∧ Extends heap after ∧
          heap.nextCollection ≤ result ∧ result < after.nextCollection ∧
          FreshRows heap after result n ∧
          heap.Increments after (MatrixMultiplyAnalysis.costs n) ∧
          n^3 ≤ runtime (heap.cost after) ∧ runtime (heap.cost after) ≤ C*n^3 := by
  refine ⟨1, by decide, ?_⟩
  intro heap a b av bv n sa sb
  obtain ⟨after, call, frame, stored, cost, allocated, references⟩ :=
    MatrixMultiplyAnalysis.summary heap a b av bv n sa sb
  have fresh := MatrixMultiplyAnalysis.every_execution_fresh_rows
    heap after a b heap.nextCollection av bv n sa sb call.run
  have monotone : heap.ClocksMonotone after := by
    intro clock
    have resumed : ∀ (h : Heap) (r : MatrixMultiplyLibrary.Algo2LeanGenerated.Result)
        (s : MatrixMultiplyLibrary.Algo2LeanGenerated.Stack),
        (resumeConfig h r s).heap = h := by
      intro h r s
      cases s <;> rfl
    have one : ∀ {before next : MatrixMultiplyLibrary.Algo2LeanGenerated.Configuration},
        MatrixMultiplyLibrary.Algo2LeanGenerated.Step before next →
          before.heap.clocks clock ≤ next.heap.clocks clock := by
      intro before next step
      cases step
      all_goals try simp only [resumed]
      all_goals simp only [Config.heap, Heap.write_clocks, Heap.allocate_clocks,
        SequenceType.set, SequenceType.const, SequenceType.create, Heap.createSequence,
        Heap.writeElement, Heap.allocateSequence]
      all_goals try exact Nat.le_refl _
      all_goals exact Heap.clocks_le_tick _ _ _ _
    have ordered := call.run.2.invariant
      (fun state => heap.clocks clock ≤ state.heap.clocks clock) (Nat.le_refl _)
      (fun _ _ move previous => Nat.le_trans previous (one move))
    exact ordered
  refine ⟨after, heap.nextCollection, call, ?_, frame, Nat.le_refl _, stored.1.1, ?_, ?_, ?_⟩
  · simpa only [multiply_product] using stored
  · constructor
    · intro i hi
      exact ⟨heap.nextRef + 1 + i, (fresh.1 i hi).1,
        Nat.le_of_lt (fresh.1 i hi).2.1, (fresh.1 i hi).2.2⟩
    · intro i j hi hj equal
      by_cases different : i = j
      · exact different
      · exact False.elim (fresh.2 i j hi hj different equal)
  · simpa only [cost] using monotone.increments
  · simp [cost, runtime, MatrixMultiplyAnalysis.costs, Clocks.single]
