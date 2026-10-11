-- Prove2me | solution 1 for CLRS.Chapter4Publication.Strassen.correctness_and_running_time
-- status  : ACCEPTED   (prove)
-- author  : @Chutong
-- created : 2026-10-11T06:34:33.345305+00:00
-- url     : https://prove2.me/submissions/29f53d92-0b1a-46e9-a780-baeff4a19ad3

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





end Reaches





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















theorem FreshRows.before_mono {before middle after : Heap} {matrix : CollectionRef} {n : Nat}
    (fresh : FreshRows middle after matrix n) (bound : before.nextRef ≤ middle.nextRef) :
    FreshRows before after matrix n := by
  refine ⟨?_, fresh.2⟩
  intro i valid
  obtain ⟨row, read, lower, upper⟩ := fresh.1 i valid
  exact ⟨row, read, Nat.le_trans bound lower, upper⟩

end Algo2LeanCore.MatrixHeap

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



theorem dot_add_left (n : Nat) (a b c : Vector) :
    dot n (fun i => a i + b i) c = dot n a c + dot n b c := by
  induction n with
  | zero => simp [dot]
  | succ n ih => simp only [dot, ih, Int.add_mul]; omega

theorem dot_sub_left (n : Nat) (a b c : Vector) :
    dot n (fun i => a i - b i) c = dot n a c - dot n b c := by
  induction n with
  | zero => simp [dot]
  | succ n ih => simp only [dot, ih, Int.sub_mul]; omega

theorem dot_add_right (n : Nat) (a b c : Vector) :
    dot n a (fun i => b i + c i) = dot n a b + dot n a c := by
  induction n with
  | zero => simp [dot]
  | succ n ih => simp only [dot, ih, Int.mul_add]; omega

theorem dot_sub_right (n : Nat) (a b c : Vector) :
    dot n a (fun i => b i - c i) = dot n a b - dot n a c := by
  induction n with
  | zero => simp [dot]
  | succ n ih => simp only [dot, ih, Int.mul_sub]; omega



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











theorem mul_add_left (n : Nat) (a b c : Matrix) :
    mul n (add a b) c = add (mul n a c) (mul n b c) := by
  funext i j
  exact dot_add_left n (a i) (b i) (fun k => c k j)

theorem mul_sub_left (n : Nat) (a b c : Matrix) :
    mul n (sub a b) c = sub (mul n a c) (mul n b c) := by
  funext i j
  exact dot_sub_left n (a i) (b i) (fun k => c k j)

theorem mul_add_right (n : Nat) (a b c : Matrix) :
    mul n a (add b c) = add (mul n a b) (mul n a c) := by
  funext i j
  exact dot_add_right n (a i) (fun k => b k j) (fun k => c k j)

theorem mul_sub_right (n : Nat) (a b c : Matrix) :
    mul n a (sub b c) = sub (mul n a b) (mul n a c) := by
  funext i j
  exact dot_sub_right n (a i) (fun k => b k j) (fun k => c k j)









/-- Seven products reproduce all four quadrants of the usual eight products.
This identity uses distributivity only and does not assume commutative blocks. -/
theorem strassen_eq_blockMul (n : Nat) (a b : Blocks) :
    strassen n a b = blockMul n a b := by
  simp only [strassen, blockMul, mul_add_left, mul_add_right, mul_sub_left, mul_sub_right]
  congr 1 <;> funext i j <;> simp only [add, sub] <;> omega

/-- Splitting the inner product commutes with taking any output block. -/
theorem block_mul (n row col : Nat) (a b : Matrix) :
    block (mul (n + n) a b) row col =
      add (mul n (block a row 0) (block b 0 col))
          (mul n (block a row n) (block b n col)) := by
  funext i j
  change dot (n + n) (a (row + i)) (fun k => b k (col + j)) =
    dot n (fun k => a (row + i) (0 + k)) (fun k => b (0 + k) (col + j)) +
    dot n (fun k => a (row + i) (n + k)) (fun k => b (n + k) (col + j))
  simpa only [Nat.zero_add] using
    dot_append n n (fun k => a (row + i) k) (fun k => b k (col + j))

/-- Ordinary finite matrix multiplication obeys the block multiplication rule. -/
theorem quadrants_mul (n : Nat) (a b : Matrix) :
    quadrants n (mul (n + n) a b) = blockMul n (quadrants n a) (quadrants n b) := by
  simp only [quadrants, blockMul, block_mul]

/-- The Strassen formulas agree with every entry of all four product blocks. -/
theorem strassen_quadrants (n : Nat) (a b : Matrix) :
    strassen n (quadrants n a) (quadrants n b) = quadrants n (mul (n + n) a b) := by
  rw [strassen_eq_blockMul, quadrants_mul]



end Chapter4Math

namespace Chapter4Math



theorem strassenOverhead_exact (k : Nat) :
    3 * strassenOverhead k + 4^k = 7^k := by
  induction k with
  | zero => decide
  | succ k ih => simp only [strassenOverhead, Nat.pow_succ]; omega















theorem calls7_exact (k : Nat) : 6 * calls 7 k + 1 = 7^(k+1) := by
  induction k with
  | zero => decide
  | succ k ih => simp only [calls, Nat.pow_succ] at *; omega



theorem calls7_bound (k : Nat) : calls 7 k ≤ 2 * 7^k := by
  have equation := calls7_exact k
  simp only [Nat.pow_succ] at equation
  omega







end Chapter4Math

namespace Chapter4Math





end Chapter4Math

end

/-! Source: proofs/chapter4/StrassenValue.lean -/

section

open Chapter4Math
namespace StrassenValues












/-- Linear combinations preserve the matrix representation. -/
theorem linear_rep (n : Nat) (sign : Int) (a b : Seq) (A B : Matrix)
    (ra : Rep n a A) (rb : Rep n b B) :
    Rep n (linearValues n sign a b) (fun i j => A i j + sign * B i j) := by
  intro i j hi hj
  simp only [linearValues]
  rw [if_pos (by omega), ra i j hi hj, rb i j hi hj]

theorem add_rep {n : Nat} {a b : Seq} {A B : Matrix}
    (ra : Rep n a A) (rb : Rep n b B) :
    Rep n (linearValues n 1 a b) (add A B) := by
  simpa [Rep, Chapter4Math.add] using linear_rep n 1 a b A B ra rb

theorem sub_rep {n : Nat} {a b : Seq} {A B : Matrix}
    (ra : Rep n a A) (rb : Rep n b B) :
    Rep n (linearValues n (-1) a b) (sub A B) := by
  simpa [Rep, Chapter4Math.sub, Int.sub_eq_add_neg] using linear_rep n (-1) a b A B ra rb

/-- Taking a quadrant preserves every entry of its mathematical block. -/
theorem quadrant_rep (n h row col : Nat) (a : Seq) (A : Matrix)
    (positive : 0 < h) (rbound : row+h ≤ n) (cbound : col+h ≤ n) (ra : Rep n a A) :
    Rep h (quadrantValues n h row col a) (block A row col) := by
  intro i j hi hj
  have hr : row+i < n := by omega
  have hc : col+j < n := by omega
  simp only [quadrantValues]
  rw [if_pos (by omega)]
  simpa [block, Int.natCast_add] using ra (row+i) (col+j) hr hc




/-- Joining representations of the four mathematical quadrants recovers M. -/
theorem join_rep (h : Nat) (a b c d : Seq) (M : Matrix) (positive : 0 < h)
    (ra : Rep h a (block M 0 0)) (rb : Rep h b (block M 0 h))
    (rc : Rep h c (block M h 0)) (rd : Rep h d (block M h h)) :
    Rep (h+h) (joinValues h a b c d) M := by
  intro i j hi hj
  simp only [joinValues]
  rw [if_pos (by omega)]
  by_cases rowLow : i < h
  · rw [if_pos (show (i:Int) < h by omega)]
    by_cases colLow : j < h
    · rw [if_pos (show (j:Int) < h by omega)]
      simpa [block, Int.natCast_add, Int.natCast_mul] using ra i j rowLow colLow
    · rw [if_neg (show ¬(j:Int) < h by omega)]
      have hle : h ≤ j := by omega
      simpa [block, Nat.add_sub_of_le hle, Int.natCast_add, Int.natCast_mul,
        Int.natCast_sub hle] using rb i (j-h) rowLow (by omega)
  · rw [if_neg (show ¬(i:Int) < h by omega)]
    have hleI : h ≤ i := by omega
    by_cases colLow : j < h
    · rw [if_pos (show (j:Int) < h by omega)]
      simpa [block, Nat.add_sub_of_le hleI, Int.natCast_add, Int.natCast_mul,
        Int.natCast_sub hleI] using rc (i-h) j (by omega) colLow
    · rw [if_neg (show ¬(j:Int) < h by omega)]
      have hleJ : h ≤ j := by omega
      simpa [block, Nat.add_sub_of_le hleI, Nat.add_sub_of_le hleJ,
        Int.natCast_add, Int.natCast_mul, Int.natCast_sub hleI, Int.natCast_sub hleJ]
        using rd (i-h) (j-h) (by omega) (by omega)



/-- The recursive seven-product program has the ordinary matrix product value
    for every finite power-of-two dimension and arbitrary integer entries. -/
theorem strassen_correct (depth : Nat) (a b : Seq) (A B : Matrix)
    (ra : Rep (2^depth) a A) (rb : Rep (2^depth) b B) :
    Rep (2^depth) (strassenValue depth a b) (mul (2^depth) A B) := by
  induction depth generalizing a b A B with
  | zero =>
    intro i j hi hj
    have izero : i = 0 := by have : i < 1 := hi; omega
    have jzero : j = 0 := by have : j < 1 := hj; omega
    subst i; subst j
    have aa := ra 0 0 (by decide) (by decide)
    have bb := rb 0 0 (by decide) (by decide)
    change a 0 0 = A 0 0 at aa
    change b 0 0 = B 0 0 at bb
    simp [strassenValue, mul, dot, aa, bb]
  | succ depth ih =>
    let h : Nat := 2^depth
    have positive : 0 < h := Nat.pow_pos (by decide)
    have width : 2^(depth+1) = h+h := by simp [h, Nat.pow_succ, Nat.mul_two]
    have widthInt : ((h+h:Nat):Int) = 2*(h:Int) := by omega
    rw [width] at ra rb ⊢
    have qa11 := quadrant_rep (h+h) h 0 0 a A positive (by omega) (by omega) ra
    have qa12 := quadrant_rep (h+h) h 0 h a A positive (by omega) (by omega) ra
    have qa21 := quadrant_rep (h+h) h h 0 a A positive (by omega) (by omega) ra
    have qa22 := quadrant_rep (h+h) h h h a A positive (by omega) (by omega) ra
    have qb11 := quadrant_rep (h+h) h 0 0 b B positive (by omega) (by omega) rb
    have qb12 := quadrant_rep (h+h) h 0 h b B positive (by omega) (by omega) rb
    have qb21 := quadrant_rep (h+h) h h 0 b B positive (by omega) (by omega) rb
    have qb22 := quadrant_rep (h+h) h h h b B positive (by omega) (by omega) rb
    rw [widthInt] at qa11 qa12 qa21 qa22 qb11 qb12 qb21 qb22
    have p1 := ih _ _ _ _ qa11 (sub_rep qb12 qb22)
    have p2 := ih _ _ _ _ (add_rep qa11 qa12) qb22
    have p3 := ih _ _ _ _ (add_rep qa21 qa22) qb11
    have p4 := ih _ _ _ _ qa22 (sub_rep qb21 qb11)
    have p5 := ih _ _ _ _ (add_rep qa11 qa22) (add_rep qb11 qb22)
    have p6 := ih _ _ _ _ (sub_rep qa12 qa22) (add_rep qb21 qb22)
    have p7 := ih _ _ _ _ (sub_rep qa11 qa21) (add_rep qb11 qb12)
    have c11 := add_rep (sub_rep (add_rep p5 p4) p2) p6
    have c12 := add_rep p1 p2
    have c21 := add_rep p3 p4
    have c22 := sub_rep (sub_rep (add_rep p5 p1) p3) p7
    change Rep h _ (strassen h (quadrants h A) (quadrants h B)).nw at c11
    change Rep h _ (strassen h (quadrants h A) (quadrants h B)).ne at c12
    change Rep h _ (strassen h (quadrants h A) (quadrants h B)).sw at c21
    change Rep h _ (strassen h (quadrants h A) (quadrants h B)).se at c22
    rw [strassen_quadrants] at c11 c12 c21 c22
    have joined := join_rep h _ _ _ _ (mul (h+h) A B) positive c11 c12 c21 c22
    exact joined

/-- Directly usable entrywise correctness, with the standard finite dot product. -/
theorem strassen_entry (depth : Nat) (a b : Seq) (i j : Nat)
    (hi : i < 2^depth) (hj : j < 2^depth) :
    strassenValue depth a b (i:Int) (j:Int) =
      dot (2^depth) (fun k => a (i:Int) (k:Int))
        (fun k => b (k:Int) (j:Int)) := by
  exact strassen_correct depth a b
    (fun r c => a (r:Int) (c:Int))
    (fun r c => b (r:Int) (c:Int))
    (by intro r c hr hc; rfl) (by intro r c hr hc; rfl) i j hi hj



/-- All entries outside the finite result square are zero. -/
theorem strassen_outside (depth : Nat) (a b : Seq) (row col : Int)
    (outside : row < 0 ∨ ((2^depth:Nat):Int) ≤ row ∨ col < 0 ∨ ((2^depth:Nat):Int) ≤ col) :
    strassenValue depth a b row col = 0 := by
  cases depth with
  | zero =>
    have nonzero : ¬(row = 0 ∧ col = 0) := by simp only [Nat.pow_zero] at outside; omega
    simp [strassenValue, nonzero]
  | succ depth =>
    change joinValues _ _ _ _ _ row col = 0
    have size : ((2^(depth+1):Nat):Int) = 2*((2^depth:Nat):Int) := by
      simp [Nat.pow_succ, Int.natCast_mul, Int.mul_comm]
    rw [size] at outside
    simp only [joinValues]
    rw [if_neg (by omega)]

end StrassenValues

end

/-! Source: proofs/chapter4/StrassenLinear.lean -/

section

open Algo2LeanCore Algo2LeanGenerated

namespace MatrixStrassenAnalysis

/- The source loops first receive reusable heap summaries. Matrix algebra and
   the recursive correctness argument then use these summaries as interfaces. -/





@[simp] theorem linearRun_nextRef (count : Nat) (heap : Heap)
    (a b c : SeqRef) (sign index : Int) :
    (linearRun count heap a b c sign index).nextRef = heap.nextRef := by
  induction count generalizing heap index with
  | zero => rfl
  | succ count ih => simp [linearRun, ih, linearStep, Heap.write]



theorem linear_exit (state : Configuration) (heap : Heap) (a b c : SeqRef)
    (bound sign index : Int) (located : AtLinear state heap a b c bound sign index)
    (allocated : c < heap.nextRef) (finished : bound ≤ index) :
    matrix_linear_row.CallFrom state heap c := by
  obtain ⟨named, sameHeap, sameA, sameB, sameC, sameBound, sameSign, sameIndex⟩ := located
  unfold matrix_linear_row.At.loop at named
  split at named <;> try contradiction
  rename_i currentHeap locals originalStack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [matrix_linear_row.Local.a, matrix_linear_row.Local.b, matrix_linear_row.Local.c,
    matrix_linear_row.Local.count, matrix_linear_row.Local.sign, matrix_linear_row.Local.i]
    at sameA sameB sameC sameBound sameSign sameIndex
  intro caller
  apply Reaches.prepend (Step.matrix_linear_row_pc4 _ _ _)
  apply Reaches.prepend (Step.matrix_linear_row_pc3_false _ _ _
    (by simp [sameIndex, sameBound]; omega))
  apply Reaches.prepend (Step.matrix_linear_row_pc2 _ _ _)
  simpa [sameC] using Reaches.single
    (Step.matrix_linear_row_pc1 heap _ caller (by simpa [sameC] using allocated))

theorem linear_step (state : Configuration) (heap finalHeap : Heap) (a b c : SeqRef)
    (bound sign index : Int) (located : AtLinear state heap a b c bound sign index)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef) (validC : c < heap.nextRef)
    (unfinished : index < bound)
    (continuation : ∀ next, AtLinear next (linearStep heap a b c sign index)
      a b c bound sign (index + 1) → matrix_linear_row.CallFrom next finalHeap c) :
    matrix_linear_row.CallFrom state finalHeap c := by
  obtain ⟨named, sameHeap, sameA, sameB, sameC, sameBound, sameSign, sameIndex⟩ := located
  unfold matrix_linear_row.At.loop at named
  split at named <;> try contradiction
  rename_i currentHeap locals originalStack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [matrix_linear_row.Local.a, matrix_linear_row.Local.b, matrix_linear_row.Local.c,
    matrix_linear_row.Local.count, matrix_linear_row.Local.sign, matrix_linear_row.Local.i]
    at sameA sameB sameC sameBound sameSign sameIndex
  have resume : ∀ next : State_matrix_linear_row,
      next.v0 = a → next.v1 = b → next.v4 = c → next.v2 = bound →
      next.v3 = sign → next.v5 = index + 1 →
      Summary Step (linearStep heap a b c sign index) (.fn_matrix_linear_row 4 next)
        finalHeap (.fn_matrix_linear_row c) := by
    intro next aEq bEq cEq boundEq signEq indexEq
    exact continuation (.active (linearStep heap a b c sign index) (.fn_matrix_linear_row 4 next) [])
      (by simp [AtLinear, matrix_linear_row.At.loop, Config.heap, matrix_linear_row.Local.a,
        matrix_linear_row.Local.b, matrix_linear_row.Local.c, matrix_linear_row.Local.count,
        matrix_linear_row.Local.sign, matrix_linear_row.Local.i, aEq, bEq, cEq, boundEq, signEq, indexEq])
  intro caller
  apply Reaches.prepend (Step.matrix_linear_row_pc4 _ _ _)
  apply Reaches.prepend (Step.matrix_linear_row_pc3_true _ _ _
    (by simp [sameIndex, sameBound, unfinished]))
  apply Reaches.prepend (Step.matrix_linear_row_pc7 _ _ _
    (by simp [sameA, sameB, sameC, validA, validB, validC]))
  apply Reaches.prepend (Step.matrix_linear_row_pc6 _ _ _)
  apply Reaches.prepend (Step.matrix_linear_row_pc5 _ _ _)
  simp only [sameA, sameB, sameC, sameSign, sameIndex]
  apply resume _ _ _ _ _ _ _ caller <;> simp [sameBound]

theorem linear_remaining (count : Nat) (heap : Heap) (a b c : SeqRef) (sign index : Int)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef) (validC : c < heap.nextRef) :
    ∀ state, AtLinear state heap a b c (index + (count : Int)) sign index →
      matrix_linear_row.CallFrom state (linearRun count heap a b c sign index) c := by
  induction count generalizing heap index with
  | zero =>
    intro state located
    exact linear_exit state heap a b c _ sign index located validC (by simp)
  | succ count ih =>
    intro state located
    apply linear_step state heap _ a b c _ sign index located validA validB validC (by omega)
    intro next nextLocated
    have equalBound : index + ((count + 1 : Nat) : Int) = index + 1 + (count : Int) := by omega
    rw [equalBound] at nextLocated
    exact ih (linearStep heap a b c sign index) (index + 1) validA validB validC next nextLocated

theorem linear_summary (heap : Heap) (a b : SeqRef) (count : Nat) (sign : Int)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef) :
    matrix_linear_row.Call heap (a, b, (count : Int), sign)
      (linearRun count (heap.allocate (fun _ => 0)) a b heap.nextRef sign 0) heap.nextRef := by
  refine ⟨⟨validA, validB⟩, ?_⟩
  intro caller
  apply Reaches.prepend (Step.matrix_linear_row_pc11 _ _ _)
  apply Reaches.prepend (Step.matrix_linear_row_pc10 _ _ _)
  apply Reaches.prepend (Step.matrix_linear_row_pc9 _ _ _)
  apply Reaches.prepend (Step.matrix_linear_row_pc8 _ _ _)
  have remaining := linear_remaining count (heap.allocate (fun _ => 0)) a b heap.nextRef sign 0
    (Nat.lt_trans validA (Nat.lt_succ_self _)) (Nat.lt_trans validB (Nat.lt_succ_self _)) (Nat.lt_succ_self _)
  exact remaining (.active (heap.allocate (fun _ => 0)) (.fn_matrix_linear_row 4
      { v0 := a, v1 := b, v2 := count, v3 := sign, v4 := heap.nextRef, t8 := heap.nextRef }) [])
    (by simp [AtLinear, matrix_linear_row.At.loop, Config.heap, matrix_linear_row.Local.a,
      matrix_linear_row.Local.b, matrix_linear_row.Local.c, matrix_linear_row.Local.count,
      matrix_linear_row.Local.sign, matrix_linear_row.Local.i]) caller

@[simp] theorem linearRun_old (count : Nat) (heap : Heap) (a b c other : SeqRef)
    (sign first index : Int) (different : other ≠ c) :
    (linearRun count heap a b c sign first).read other index = heap.read other index := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    simp only [linearRun]
    rw [ih]
    simp [linearStep, Heap.read, Heap.write, different]

theorem linearRun_value (count : Nat) (heap : Heap) (a b c : SeqRef)
    (sign first index : Int) (separateA : a ≠ c) (separateB : b ≠ c) :
    (linearRun count heap a b c sign first).read c index =
      if first ≤ index ∧ index < first + (count : Int)
      then heap.read a index + sign * heap.read b index else heap.read c index := by
  induction count generalizing heap first with
  | zero =>
    simp only [linearRun, Int.natCast_zero, Int.add_zero]
    rw [if_neg (by omega)]
  | succ count ih =>
    simp only [linearRun]
    rw [ih]
    simp only [linearStep, Heap.read, Heap.write, Heap.tick,
      separateA, separateB, false_and, ↓reduceIte, true_and]
    grind

theorem linearRun_clocks (count : Nat) (heap : Heap) (a b c : SeqRef)
    (sign first : Int) (name : String) :
    (linearRun count heap a b c sign first).clocks name =
      heap.clocks name + if name = "linear_cells" then count else 0 := by
  induction count generalizing heap first with
  | zero => simp [linearRun]
  | succ count ih =>
    simp only [linearRun, ih, linearStep, Heap.tick, Heap.write]
    by_cases same : name = "linear_cells" <;> simp [same, Nat.add_assoc, Nat.add_comm 1 count]











end MatrixStrassenAnalysis

end

/-! Source: proofs/chapter4/StrassenHelpers.lean -/

section

open Algo2LeanCore Algo2LeanGenerated Algo2LeanCore.MatrixHeap
namespace MatrixStrassenHelpers

open MatrixStrassenAnalysis

private theorem linearRun_data (count : Nat) (heap : Heap) (a b c : SeqRef) (sign first : Int) :
    (linearRun count heap a b c sign first).nextCollection = heap.nextCollection ∧
    (linearRun count heap a b c sign first).collections = heap.collections ∧
    (linearRun count heap a b c sign first).nextObject = heap.nextObject ∧
    (linearRun count heap a b c sign first).objects = heap.objects := by
  induction count generalizing heap first with
  | zero => exact ⟨rfl,rfl,rfl,rfl⟩
  | succ count ih => exact ih (linearStep heap a b c sign first) (first+1)

/-- One row combination allocates independent output storage and preserves all
    previously allocated rows, collections, and objects. -/
theorem linear_row_contract (heap : Heap) (a b : SeqRef) (count : Nat) (sign : Int)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef) :
    ∃ after result, matrix_linear_row.Call heap (a,b,(count:Int),sign) after result ∧
      Extends heap after ∧ result < after.nextRef ∧ heap.nextRef ≤ result ∧
      after.store result = (fun index => if 0 ≤ index ∧ index < (count:Int)
        then heap.read a index + sign * heap.read b index else 0) ∧
      (∀ name, after.clocks name = heap.clocks name + Clocks.single "linear_cells" count name) := by
  let final := linearRun count (heap.allocate (fun _ => 0)) a b heap.nextRef sign 0
  have data := linearRun_data count (heap.allocate (fun _ => 0)) a b heap.nextRef sign 0
  refine ⟨final, heap.nextRef, linear_summary heap a b count sign validA validB, ?_, by simp [final],
    Nat.le_refl _, ?_, ?_⟩
  · refine ⟨by simp [final], by rw [data.1]; exact Nat.le_refl _, ?_, ?_, data.2.2.1, data.2.2.2⟩
    · intro old valid
      funext index
      rw [show final.store old index = final.read old index from rfl,
        linearRun_old count _ a b heap.nextRef old sign 0 index (Nat.ne_of_lt valid)]
      exact Heap.read_allocate_old heap _ old index valid
    · intro old _; exact congrFun data.2.1 old
  · funext index
    rw [show final.store heap.nextRef index = final.read heap.nextRef index from rfl,
      linearRun_value count _ a b heap.nextRef sign 0 index (Nat.ne_of_lt validA) (Nat.ne_of_lt validB)]
    simp [validA, validB]
  · intro name
    simpa only [Heap.allocate_clocks, Clocks.single] using
      linearRun_clocks count (heap.allocate (fun _ => 0)) a b heap.nextRef sign 0 name




private theorem copyLoop (count : Nat) (heap : Heap) (s : State_matrix_quadrant_row)
    (bound : s.v1 = s.v4 + (count:Int)) (validA : s.v0 < heap.nextRef)
    (validC : s.v3 < heap.nextRef) :
    Summary Step heap (.fn_matrix_quadrant_row 4 s)
      (copyRun count heap s.v0 s.v3 s.v2 s.v4) (.fn_matrix_quadrant_row s.v3) := by
  induction count generalizing heap s with
  | zero =>
    intro stack
    apply Reaches.prepend (Step.matrix_quadrant_row_pc4 ..)
    apply Reaches.prepend (Step.matrix_quadrant_row_pc3_false _ _ _ (by simp; omega))
    apply Reaches.prepend (Step.matrix_quadrant_row_pc2 ..)
    exact Reaches.single (Step.matrix_quadrant_row_pc1 _ _ _ validC)
  | succ count ih =>
    intro stack
    apply Reaches.prepend (Step.matrix_quadrant_row_pc4 ..)
    apply Reaches.prepend (Step.matrix_quadrant_row_pc3_true _ _ _ (by simp; omega))
    apply Reaches.prepend (Step.matrix_quadrant_row_pc7 _ _ _ (by exact ⟨validA,validC⟩))
    apply Reaches.prepend (Step.matrix_quadrant_row_pc6 ..)
    apply Reaches.prepend (Step.matrix_quadrant_row_pc5 ..)
    exact ih (copyStep heap s.v0 s.v3 s.v2 s.v4)
      {s with v4 := s.v4+1, t6 := decide (s.v4 < s.v1)} (by dsimp; omega) validA validC stack

private theorem copyRun_data (count : Nat) (heap : Heap) (a c : SeqRef) (col first : Int) :
    (copyRun count heap a c col first).nextRef = heap.nextRef ∧
    (copyRun count heap a c col first).nextCollection = heap.nextCollection ∧
    (copyRun count heap a c col first).collections = heap.collections ∧
    (copyRun count heap a c col first).nextObject = heap.nextObject ∧
    (copyRun count heap a c col first).objects = heap.objects := by
  induction count generalizing heap first with
  | zero => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | succ count ih => exact ih (copyStep heap a c col first) (first+1)

private theorem copyRun_old (count : Nat) (heap : Heap) (a c other : SeqRef)
    (col first index : Int) (different : other ≠ c) :
    (copyRun count heap a c col first).read other index = heap.read other index := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    simp only [copyRun]
    rw [ih]
    simp [copyStep, Heap.read, Heap.write, different]

private theorem copyRun_value (count : Nat) (heap : Heap) (a c : SeqRef)
    (col first index : Int) (separate : a ≠ c) :
    (copyRun count heap a c col first).read c index =
      if first ≤ index ∧ index < first+(count:Int)
      then heap.read a (col+index) else heap.read c index := by
  induction count generalizing heap first with
  | zero => simp only [copyRun, Int.natCast_zero, Int.add_zero]; rw [if_neg (by omega)]
  | succ count ih =>
    simp only [copyRun]
    rw [ih]
    simp only [copyStep, Heap.read, Heap.write, Heap.tick,
      separate, false_and, ↓reduceIte, true_and]
    grind

private theorem copyRun_clocks (count : Nat) (heap : Heap) (a c : SeqRef)
    (col first : Int) (name : String) :
    (copyRun count heap a c col first).clocks name =
      heap.clocks name + Clocks.single "copied_cells" count name := by
  induction count generalizing heap first with
  | zero => simp [copyRun, Clocks.single]
  | succ count ih =>
    simp only [copyRun, ih, copyStep, Heap.tick, Heap.write, Clocks.single]
    by_cases same : name = "copied_cells" <;> simp [same, Nat.add_assoc, Nat.add_comm 1 count]

/-- Copying a finite row segment returns fresh storage, preserves every previous
    row and outer array, and charges exactly the number of copied entries. -/
theorem quadrant_row_contract (heap : Heap) (a : SeqRef) (count : Nat) (column : Int)
    (validA : a < heap.nextRef) :
    ∃ after result, matrix_quadrant_row.Call heap (a,(count:Int),column) after result ∧
      Extends heap after ∧ result < after.nextRef ∧ heap.nextRef ≤ result ∧
      after.store result = (fun index => if 0 ≤ index ∧ index < (count:Int)
        then heap.read a (column+index) else 0) ∧
      (∀ name, after.clocks name = heap.clocks name + Clocks.single "copied_cells" count name) := by
  let final := copyRun count (heap.allocate (fun _ => 0)) a heap.nextRef column 0
  have data := copyRun_data count (heap.allocate (fun _ => 0)) a heap.nextRef column 0
  refine ⟨final, heap.nextRef, ?_, ?_, ?_, Nat.le_refl _, ?_, ?_⟩
  · refine ⟨validA, ?_⟩
    intro stack
    apply Reaches.prepend (Step.matrix_quadrant_row_pc11 ..)
    apply Reaches.prepend (Step.matrix_quadrant_row_pc10 ..)
    apply Reaches.prepend (Step.matrix_quadrant_row_pc9 ..)
    apply Reaches.prepend (Step.matrix_quadrant_row_pc8 ..)
    apply copyLoop count _ _ (by simp) (by simpa using Nat.lt_trans validA (Nat.lt_succ_self _))
      (Nat.lt_succ_self _) stack
  · refine ⟨by simp [final, data.1], by rw [data.2.1]; exact Nat.le_refl _, ?_, ?_, data.2.2.2.1, data.2.2.2.2⟩
    · intro old valid
      funext index
      rw [show final.store old index = final.read old index from rfl,
        copyRun_old count _ a heap.nextRef old column 0 index (Nat.ne_of_lt valid)]
      exact Heap.read_allocate_old heap _ old index valid
    · intro old _; exact congrFun data.2.2.1 old
  · simp [final, data.1]
  · funext index
    rw [show final.store heap.nextRef index = final.read heap.nextRef index from rfl,
      copyRun_value count _ a heap.nextRef column 0 index (Nat.ne_of_lt validA)]
    simp [validA]
  · exact copyRun_clocks count _ a heap.nextRef column 0





private theorem joinLoop (count : Nat) (heap : Heap) (s : State_matrix_join_row)
    (bound : s.v2 = s.v4 + (count:Int)) (validA : s.v0 < heap.nextRef)
    (validB : s.v1 < heap.nextRef) (validC : s.v3 < heap.nextRef)
    (separateB : s.v1 ≠ s.v3) :
    Summary Step heap (.fn_matrix_join_row 4 s)
      (joinRun count heap s.v0 s.v1 s.v3 s.v2 s.v4) (.fn_matrix_join_row s.v3) := by
  induction count generalizing heap s with
  | zero =>
    intro stack
    apply Reaches.prepend (Step.matrix_join_row_pc4 ..)
    apply Reaches.prepend (Step.matrix_join_row_pc3_false _ _ _ (by simp; omega))
    apply Reaches.prepend (Step.matrix_join_row_pc2 ..)
    exact Reaches.single (Step.matrix_join_row_pc1 _ _ _ validC)
  | succ count ih =>
    intro stack
    apply Reaches.prepend (Step.matrix_join_row_pc4 ..)
    apply Reaches.prepend (Step.matrix_join_row_pc3_true _ _ _ (by simp; omega))
    apply Reaches.prepend (Step.matrix_join_row_pc8 _ _ _ (by exact ⟨validA,validC⟩))
    apply Reaches.prepend (Step.matrix_join_row_pc7 _ _ _ (by exact ⟨validB,validC⟩))
    apply Reaches.prepend (Step.matrix_join_row_pc6 ..)
    apply Reaches.prepend (Step.matrix_join_row_pc5 ..)
    have readB : (heap.write s.v3 s.v4 (heap.read s.v0 s.v4)).read s.v1 s.v4 = heap.read s.v1 s.v4 := by
      simp [Heap.read, Heap.write, separateB]
    simp only [readB]
    exact ih (joinStep heap s.v0 s.v1 s.v3 s.v2 s.v4)
      {s with v4 := s.v4+1, t6 := decide (s.v4 < s.v2)} (by dsimp; omega) validA validB validC separateB stack

private theorem joinRun_data (count : Nat) (heap : Heap) (a b c : SeqRef) (h first : Int) :
    (joinRun count heap a b c h first).nextRef = heap.nextRef ∧
    (joinRun count heap a b c h first).nextCollection = heap.nextCollection ∧
    (joinRun count heap a b c h first).collections = heap.collections ∧
    (joinRun count heap a b c h first).nextObject = heap.nextObject ∧
    (joinRun count heap a b c h first).objects = heap.objects := by
  induction count generalizing heap first with
  | zero => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | succ count ih => exact ih (joinStep heap a b c h first) (first+1)

private theorem joinRun_old (count : Nat) (heap : Heap) (a b c other : SeqRef)
    (h first index : Int) (different : other ≠ c) :
    (joinRun count heap a b c h first).read other index = heap.read other index := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    simp only [joinRun]
    rw [ih]
    simp [joinStep, Heap.read, Heap.write, different]

private theorem joinRun_value (count : Nat) (heap : Heap) (a b c : SeqRef)
    (h first index : Int) (nonneg : 0 ≤ first) (bound : first+(count:Int) ≤ h)
    (separateA : a ≠ c) (separateB : b ≠ c) :
    (joinRun count heap a b c h first).read c index =
      if first ≤ index ∧ index < first+(count:Int) then heap.read a index
      else if first+h ≤ index ∧ index < first+h+(count:Int)
      then heap.read b (index-h) else heap.read c index := by
  induction count generalizing heap first with
  | zero => simp only [joinRun, Int.natCast_zero, Int.add_zero]; rw [if_neg (by omega), if_neg (by omega)]
  | succ count ih =>
    simp only [joinRun]
    rw [ih _ (first+1) (by omega) (by omega)]
    simp only [joinStep, Heap.read, Heap.write, Heap.tick,
      separateA, separateB, false_and, ↓reduceIte, true_and]
    grind

private theorem joinRun_clocks (count : Nat) (heap : Heap) (a b c : SeqRef)
    (h first : Int) (name : String) :
    (joinRun count heap a b c h first).clocks name =
      heap.clocks name + Clocks.single "copied_cells" (2*count) name := by
  induction count generalizing heap first with
  | zero => simp [joinRun, Clocks.single]
  | succ count ih =>
    simp only [joinRun, ih, joinStep, Heap.tick, Heap.write, Clocks.single]
    by_cases same : name = "copied_cells" <;> simp [same] <;> omega

/-- Joining two row segments copies their entries into one fresh row. -/
theorem join_row_contract (heap : Heap) (a b : SeqRef) (count : Nat)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef) :
    ∃ after result, matrix_join_row.Call heap (a,b,(count:Int)) after result ∧
      Extends heap after ∧ result < after.nextRef ∧ heap.nextRef ≤ result ∧
      after.store result = (fun index => if 0 ≤ index ∧ index < 2*(count:Int)
        then if index < (count:Int) then heap.read a index else heap.read b (index-count) else 0) ∧
      (∀ name, after.clocks name = heap.clocks name + Clocks.single "copied_cells" (2*count) name) := by
  let final := joinRun count (heap.allocate (fun _ => 0)) a b heap.nextRef count 0
  have data := joinRun_data count (heap.allocate (fun _ => 0)) a b heap.nextRef count 0
  refine ⟨final, heap.nextRef, ?_, ?_, ?_, Nat.le_refl _, ?_, ?_⟩
  · refine ⟨⟨validA,validB⟩, ?_⟩
    intro stack
    apply Reaches.prepend (Step.matrix_join_row_pc12 ..)
    apply Reaches.prepend (Step.matrix_join_row_pc11 ..)
    apply Reaches.prepend (Step.matrix_join_row_pc10 ..)
    apply Reaches.prepend (Step.matrix_join_row_pc9 ..)
    apply joinLoop count _ _ (by simp) (by simpa using Nat.lt_trans validA (Nat.lt_succ_self _))
      (by simpa using Nat.lt_trans validB (Nat.lt_succ_self _)) (Nat.lt_succ_self _) (Nat.ne_of_lt validB) stack
  · refine ⟨by simp [final, data.1], by rw [data.2.1]; exact Nat.le_refl _, ?_, ?_, data.2.2.2.1, data.2.2.2.2⟩
    · intro old valid
      funext index
      rw [show final.store old index = final.read old index from rfl,
        joinRun_old count _ a b heap.nextRef old count 0 index (Nat.ne_of_lt valid)]
      exact Heap.read_allocate_old heap _ old index valid
    · intro old _; exact congrFun data.2.2.1 old
  · simp [final, data.1]
  · funext index
    rw [show final.store heap.nextRef index = final.read heap.nextRef index from rfl,
      joinRun_value count _ a b heap.nextRef count 0 index (by omega) (by omega) (Nat.ne_of_lt validA) (Nat.ne_of_lt validB)]
    simp only [Heap.read_allocate_old _ _ _ _ validA, Heap.read_allocate_old _ _ _ _ validB,
      Heap.read_allocate_new, Int.zero_add]
    split <;> split <;> (try split) <;> simp_all <;> omega
  · exact joinRun_clocks count _ a b heap.nextRef count 0




private theorem prefix_next (values : Values) (i : Nat) :
    (fun j => if j = (i:Int) then values i else rowPrefix values i j) = rowPrefix values (i+1) := by
  funext j k
  by_cases same : j = (i:Int)
  · subst j
    simp only
    change values i k = if 0 ≤ (i:Int) ∧ (i:Int) < ((i+1:Nat):Int) then values i k else 0
    rw [if_pos (by omega)]
  · simp only [if_neg same]
    have eqRange : (0 ≤ j ∧ j < (i:Int)) ↔ (0 ≤ j ∧ j < ((i+1:Nat):Int)) := by omega
    simp only [rowPrefix, eqRange]

private theorem prefix_zero (values : Values) : rowPrefix values 0 = fun _ _ => 0 := by
  funext i j
  simp only [rowPrefix, Int.natCast_zero]
  rw [if_neg (by omega)]

private theorem linearMatrixLoop (remaining : Nat) (base heap : Heap) (s : State_matrix_linear)
    (n i : Nat) (av bv : Values) (bound : s.v2 = (n:Int)) (index : s.v5 = (i:Int))
    (finish : i+remaining = n) (sa : Stored base s.v0 av) (sb : Stored base s.v1 bv)
    (frame : Extends base heap) (fresh : base.nextCollection ≤ s.v4)
    (stored : Stored heap s.v4 (rowPrefix (fun r c =>
      if 0 ≤ c ∧ c < (n:Int) then av r c + s.v3*bv r c else 0) i)) :
    ∃ after, Summary Step heap (.fn_matrix_linear 4 s) after (.fn_matrix_linear s.v4) ∧
      Extends base after ∧ Stored after s.v4 (StrassenValues.linearValues n s.v3 av bv) ∧
      (∀ name, after.clocks name = heap.clocks name + Clocks.single "linear_cells" (remaining*n) name) := by
  induction remaining generalizing heap s i with
  | zero =>
    have ieq : i = n := by omega
    subst i
    refine ⟨heap, ?_, frame, ?_, ?_⟩
    · intro stack
      apply Reaches.prepend (Step.matrix_linear_pc4 ..)
      apply Reaches.prepend (Step.matrix_linear_pc3_false _ _ _ (by simp [bound,index]))
      apply Reaches.prepend (Step.matrix_linear_pc2 ..)
      exact Reaches.single (Step.matrix_linear_pc1 _ _ _ stored.1)
    · have eqValues : rowPrefix (fun r c => if 0 ≤ c ∧ c < (n:Int)
          then av r c + s.v3*bv r c else 0) n = StrassenValues.linearValues n s.v3 av bv := by
        funext r c
        simp only [rowPrefix, StrassenValues.linearValues]
        grind
      rw [eqValues] at stored
      exact stored
    · intro name; simp [Clocks.single]
  | succ remaining ih =>
    have ai := sa.mono frame
    have bi := sb.mono frame
    obtain ⟨one,row,rowRun,rowFrame,rowValid,rowFresh,rowValue,rowClocks⟩ :=
      linear_row_contract heap ((rows.get heap s.v0 s.v5).getD 0)
        ((rows.get heap s.v1 s.v5).getD 0) n s.v3 (ai.row_valid s.v5) (bi.row_valid s.v5)
    let nextHeap := rows.set one s.v4 s.v5 row
    let next : State_matrix_linear := { s with v5 := s.v5+1, t7 := decide (s.v5<s.v2), t8 := row, t9 := s.v5, t10 := s.v4, t11 := (rows.get heap s.v0 s.v5).getD 0, t12 := (rows.get heap s.v1 s.v5).getD 0, t13 := s.v2, t14 := s.v3 }
    have nextFrame : Extends base nextHeap := (frame.trans rowFrame).set s.v4 fresh s.v5 row
    have nextStored : Stored nextHeap next.v4 (rowPrefix (fun r c =>
        if 0 ≤ c ∧ c < (n:Int) then av r c + next.v3*bv r c else 0) (i+1)) := by
      have st := (stored.mono rowFrame).set s.v5 row _ rowValid rowValue
      have rowEq : (fun c => if 0 ≤ c ∧ c < (n:Int) then
          heap.read ((rows.get heap s.v0 s.v5).getD 0) c +
            s.v3 * heap.read ((rows.get heap s.v1 s.v5).getD 0) c else 0) =
          (fun c => if 0 ≤ c ∧ c < (n:Int) then av (i:Int) c + s.v3*bv (i:Int) c else 0) := by
        funext c; rw [ai.read,bi.read,index]
      rw [rowEq,index, prefix_next (fun r c => if 0 ≤ c ∧ c < (n:Int) then av r c + s.v3*bv r c else 0) i] at st
      simpa only [nextHeap,next,index] using st
    obtain ⟨after,completed,afterFrame,afterStored,afterClocks⟩ :=
      ih nextHeap next (i+1) bound (by dsimp [next]; omega) (by omega) sa sb nextFrame fresh nextStored
    refine ⟨after, ?_, afterFrame, afterStored, ?_⟩
    · intro stack
      apply Reaches.prepend (Step.matrix_linear_pc4 ..)
      apply Reaches.prepend (Step.matrix_linear_pc3_true _ _ _ (by simp [bound,index]; omega))
      apply Reaches.prepend (Step.matrix_linear_pc13 _ _ _ (by exact ai.row s.v5))
      apply Reaches.prepend (Step.matrix_linear_pc12 _ _ _ (by exact bi.row s.v5))
      apply Reaches.prepend (Step.matrix_linear_pc11 ..)
      apply Reaches.prepend (Step.matrix_linear_pc10 ..)
      apply Reaches.prepend (Step.matrix_linear_pc9 ..)
      simp only [bound]
      apply Reaches.trans (rowRun.2 _)
      apply Reaches.prepend (Step.matrix_linear_pc8 ..)
      apply Reaches.prepend (Step.matrix_linear_pc7 ..)
      apply Reaches.prepend (Step.matrix_linear_pc6 _ _ _ (by exact rowFrame.valid stored.1))
      apply Reaches.prepend (Step.matrix_linear_pc5 ..)
      simpa only [next,nextHeap,bound,show seq_Seq_Int = rows from rfl] using completed stack
    · intro name
      rw [afterClocks]
      change one.clocks name + _ = _
      rw [rowClocks]
      by_cases same : name = "linear_cells" <;> simp [Clocks.single,same, Nat.add_mul] <;> omega

/-- A matrix linear combination fills fresh independent rows and preserves
    every preexisting heap object. -/
theorem linear_contract (heap : Heap) (a b : CollectionRef) (av bv : Values) (n : Nat) (sign : Int)
    (sa : Stored heap a av) (sb : Stored heap b bv) :
    ∃ after result, matrix_linear.Call heap (a,b,(n:Int),sign) after result ∧
      Extends heap after ∧ Stored after result (StrassenValues.linearValues n sign av bv) ∧
      (∀ name, after.clocks name = heap.clocks name + Clocks.single "linear_cells" (n*n) name) := by
  let initialized := (rows.const (heap.allocate (fun _ => 0)) heap.nextRef).1
  have frame : Extends heap initialized := (extends_allocate heap _).trans (extends_const _ _)
  have stored : Stored initialized heap.nextCollection (fun _ _ => 0) :=
    stored_const (heap.allocate (fun _ => 0)) heap.nextRef _ (Nat.lt_succ_self _) (by simp [Heap.allocate])
  let state : State_matrix_linear := { v0 := a, v1 := b, v2 := n, v3 := sign, v4 := heap.nextCollection, t15 := heap.nextCollection, t16 := heap.nextRef }
  obtain ⟨after,completed,afterFrame,afterStored,afterClocks⟩ :=
    linearMatrixLoop n heap initialized state n 0 av bv rfl rfl (by omega) sa sb frame (Nat.le_refl _)
      (by simpa only [state,prefix_zero] using stored)
  refine ⟨after,heap.nextCollection,⟨⟨sa.1,sb.1⟩,?_⟩,afterFrame,afterStored,afterClocks⟩
  intro stack
  apply Reaches.prepend (Step.matrix_linear_pc18 ..)
  apply Reaches.prepend (Step.matrix_linear_pc17 ..)
  apply Reaches.prepend (Step.matrix_linear_pc16 ..)
  apply Reaches.prepend (Step.matrix_linear_pc15 ..)
  apply Reaches.prepend (Step.matrix_linear_pc14 ..)
  exact completed stack




private theorem paired_zero (values : Values) (n : Nat) : pairedPrefix values n 0 = fun _ _ => 0 := by
  funext i j
  simp only [pairedPrefix, Int.natCast_zero, Int.add_zero]
  rw [if_neg (by omega)]

private theorem paired_next (values : Values) (n i : Nat) (unfinished : i < n) :
    (fun j => if j = (i:Int)+(n:Int) then values ((i:Int)+n)
      else if j = (i:Int) then values i else pairedPrefix values n i j) = pairedPrefix values n (i+1) := by
  funext j k
  by_cases bottom : j = (i:Int)+(n:Int)
  · subst j
    simp only
    change values _ _ = if _ then values _ _ else 0
    rw [if_pos (by omega)]
  · simp only [if_neg bottom]
    by_cases top : j = (i:Int)
    · subst j
      simp only
      change values _ _ = if _ then values _ _ else 0
      rw [if_pos (by omega)]
    · simp only [if_neg top]
      have eqRange : ((0 ≤ j ∧ j < (i:Int)) ∨ ((n:Int) ≤ j ∧ j < (n:Int)+(i:Int))) ↔
          ((0 ≤ j ∧ j < ((i+1:Nat):Int)) ∨ ((n:Int) ≤ j ∧ j < (n:Int)+((i+1:Nat):Int))) := by omega
      simp only [pairedPrefix, eqRange]



private theorem freshOn_install (before heap after : Heap) (matrix : CollectionRef)
    (domain : Nat → Prop) (ownership : FreshOn before heap matrix domain)
    (valid : rows.valid heap matrix) (extension : Extends heap after)
    (bound : before.nextRef ≤ heap.nextRef) (index row : Nat)
    (fresh : heap.nextRef ≤ row) (allocated : row < after.nextRef) :
    FreshOn before (rows.set after matrix index row) matrix (fun i => i = index ∨ domain i) := by
  have installed : rows.get (rows.set after matrix index row) matrix index = some row :=
    rows.get_set_same after matrix index row (extension.valid valid)
  have unchanged : ∀ i : Nat, i ≠ index →
      rows.get (rows.set after matrix index row) matrix i = rows.get heap matrix i := by
    intro i different
    rw [rows.get_set_other_index _ _ _ _ _ (by omega)]
    exact extension.get valid i
  constructor
  · intro i inside
    rcases inside with same | old
    · subst i
      exact ⟨row, installed, Nat.le_trans bound fresh, allocated⟩
    · by_cases same : i = index
      · subst i
        exact ⟨row, installed, Nat.le_trans bound fresh, allocated⟩
      · obtain ⟨oldRow, read, lower, upper⟩ := ownership.1 i old
        exact ⟨oldRow, (unchanged i same).trans read, lower,
          Nat.lt_of_lt_of_le upper extension.nextRef⟩
  · intro i j di dj equal
    by_cases sameI : i = index
    · subst i
      by_cases sameJ : j = index
      · exact sameJ.symm
      · have oldJ : domain j := dj.resolve_left sameJ
        obtain ⟨oldRow, read, lower, upper⟩ := ownership.1 j oldJ
        rw [installed, unchanged j sameJ, read] at equal
        have rowEq := Option.some.inj equal
        exact False.elim ((Nat.not_lt_of_ge fresh) (by simpa only [rowEq] using upper))
    · by_cases sameJ : j = index
      · subst j
        have oldI : domain i := di.resolve_left sameI
        obtain ⟨oldRow, read, lower, upper⟩ := ownership.1 i oldI
        rw [installed, unchanged i sameI, read] at equal
        have rowEq := Option.some.inj equal
        exact False.elim ((Nat.not_lt_of_ge fresh) (by simpa only [rowEq] using upper))
      · rw [unchanged i sameI, unchanged j sameJ] at equal
        exact ownership.2 i j (di.resolve_left sameI) (dj.resolve_left sameJ) equal



private theorem pairedDomain_step (n i : Nat) :
    (fun j => j = i + n ∨ j = i ∨ pairedDomain n i j) = pairedDomain n (i + 1) := by
  funext j
  apply propext
  simp only [pairedDomain]
  omega

private theorem joinMatrixLoop (remaining : Nat) (base heap : Heap) (s : State_matrix_join)
    (n i : Nat) (av bv cv dv : Values) (bound : s.v4 = (n:Int)) (index : s.v6 = (i:Int))
    (finish : i+remaining = n) (sa : Stored base s.v0 av) (sb : Stored base s.v1 bv)
    (sc : Stored base s.v2 cv) (sd : Stored base s.v3 dv)
    (frame : Extends base heap) (fresh : base.nextCollection ≤ s.v5)
    (stored : Stored heap s.v5 (pairedPrefix (StrassenValues.joinValues n av bv cv dv) n i))
    (ownership : FreshOn base heap s.v5 (pairedDomain n i)) :
    ∃ after, Summary Step heap (.fn_matrix_join 4 s) after (.fn_matrix_join s.v5) ∧
      Extends base after ∧ Stored after s.v5 (StrassenValues.joinValues n av bv cv dv) ∧
      (∀ name, after.clocks name = heap.clocks name + Clocks.single "copied_cells" (4*(remaining*n)) name) ∧
      FreshRows base after s.v5 (2*n) := by
  induction remaining generalizing heap s i with
  | zero =>
    have ieq : i = n := by omega
    subst i
    refine ⟨heap, ?_, frame, ?_, ?_, ?_⟩
    · intro stack
      apply Reaches.prepend (Step.matrix_join_pc4 ..)
      apply Reaches.prepend (Step.matrix_join_pc3_false _ _ _ (by simp [bound,index]))
      apply Reaches.prepend (Step.matrix_join_pc2 ..)
      exact Reaches.single (Step.matrix_join_pc1 _ _ _ stored.1)
    · have eqValues : pairedPrefix (StrassenValues.joinValues n av bv cv dv) n n =
          StrassenValues.joinValues n av bv cv dv := by
        funext r c
        simp only [pairedPrefix,StrassenValues.joinValues]
        grind
      rw [eqValues] at stored
      exact stored
    · intro name; simp [Clocks.single]
    · have domainEq : pairedDomain n n = (fun j => j < 2*n) := by
        funext j
        apply propext
        unfold pairedDomain
        omega
      change FreshOn base heap s.v5 (fun j => j < 2*n)
      simpa only [domainEq] using ownership
  | succ remaining ih =>
    have unfinished : i < n := by omega
    have ai := sa.mono frame
    have bi := sb.mono frame
    obtain ⟨one,topRow,topRun,topFrame,topValid,topFresh,topValue,topClocks⟩ :=
      join_row_contract heap ((rows.get heap s.v0 s.v6).getD 0)
        ((rows.get heap s.v1 s.v6).getD 0) n (ai.row_valid s.v6) (bi.row_valid s.v6)
    let middle := rows.set one s.v5 s.v6 topRow
    have middleFrame : Extends base middle := (frame.trans topFrame).set s.v5 fresh s.v6 topRow
    have topEq : (fun c => if 0 ≤ c ∧ c < 2*(n:Int) then
        if c < (n:Int) then heap.read ((rows.get heap s.v0 s.v6).getD 0) c
        else heap.read ((rows.get heap s.v1 s.v6).getD 0) (c-n) else 0) =
        StrassenValues.joinValues n av bv cv dv i := by
      funext c
      rw [ai.read,bi.read,index]
      simp only [StrassenValues.joinValues]
      have irange : 0 ≤ (i:Int) ∧ (i:Int) < 2*n := by omega
      have ilow : (i:Int) < n := by omega
      simp only [irange.1,irange.2,ilow,true_and,if_pos]
    have topStored := (stored.mono topFrame).set s.v6 topRow _ topValid topValue
    rw [topEq] at topStored
    have topOwned : FreshOn base middle s.v5 (fun j => j = i ∨ pairedDomain n i j) := by
      simpa only [middle, index] using freshOn_install base heap one s.v5
        (pairedDomain n i) ownership stored.1 topFrame frame.nextRef i topRow topFresh topValid
    have ci := sc.mono middleFrame
    have di := sd.mono middleFrame
    obtain ⟨two,bottomRow,bottomRun,bottomFrame,bottomValid,bottomFresh,bottomValue,bottomClocks⟩ :=
      join_row_contract middle ((rows.get middle s.v2 s.v6).getD 0)
        ((rows.get middle s.v3 s.v6).getD 0) n (ci.row_valid s.v6) (di.row_valid s.v6)
    let nextHeap := rows.set two s.v5 (s.v6+s.v4) bottomRow
    let next : State_matrix_join := { s with v6 := s.v6+1, t8 := decide (s.v6<s.v4), t9 := bottomRow, t10 := s.v6+s.v4, t11 := s.v5, t12 := (rows.get middle s.v2 s.v6).getD 0, t13 := (rows.get middle s.v3 s.v6).getD 0, t14 := s.v4, t15 := topRow, t16 := s.v6, t17 := s.v5, t18 := (rows.get heap s.v0 s.v6).getD 0, t19 := (rows.get heap s.v1 s.v6).getD 0, t20 := s.v4 }
    have nextFrame : Extends base nextHeap := (middleFrame.trans bottomFrame).set s.v5 fresh _ bottomRow
    have bottomEq : (fun c => if 0 ≤ c ∧ c < 2*(n:Int) then
        if c < (n:Int) then middle.read ((rows.get middle s.v2 s.v6).getD 0) c
        else middle.read ((rows.get middle s.v3 s.v6).getD 0) (c-n) else 0) =
        StrassenValues.joinValues n av bv cv dv ((i:Int)+n) := by
      funext c
      rw [ci.read,di.read,index]
      simp only [StrassenValues.joinValues]
      have irange : 0 ≤ (i:Int)+n ∧ (i:Int)+n < 2*n := by omega
      have ilow : ¬(i:Int)+n < n := by omega
      have cancel : (i:Int)+n-n = i := by omega
      simp only [irange.1,irange.2,ilow,true_and,if_false,cancel]
    have nextStored : Stored nextHeap next.v5 (pairedPrefix (StrassenValues.joinValues n av bv cv dv) n (i+1)) := by
      have st := (topStored.mono bottomFrame).set (s.v6+s.v4) bottomRow _ bottomValid bottomValue
      rw [bottomEq,index,bound,paired_next _ n i unfinished] at st
      simpa only [nextHeap,next,index,bound] using st
    have nextOwned : FreshOn base nextHeap next.v5 (pairedDomain n (i+1)) := by
      have installed := freshOn_install base middle two s.v5
        (fun j => j = i ∨ pairedDomain n i j) topOwned topStored.1 bottomFrame
        middleFrame.nextRef (i+n) bottomRow bottomFresh bottomValid
      rw [pairedDomain_step] at installed
      simpa only [nextHeap, next, index, bound, Int.natCast_add] using installed
    obtain ⟨after,completed,afterFrame,afterStored,afterClocks,afterOwned⟩ :=
      ih nextHeap next (i+1) bound (by dsimp [next]; omega) (by omega) sa sb sc sd nextFrame fresh nextStored nextOwned
    refine ⟨after, ?_, afterFrame, afterStored, ?_, afterOwned⟩
    · intro stack
      apply Reaches.prepend (Step.matrix_join_pc4 ..)
      apply Reaches.prepend (Step.matrix_join_pc3_true _ _ _ (by simp [bound,index]; omega))
      apply Reaches.prepend (Step.matrix_join_pc19 _ _ _ (by exact ai.row s.v6))
      apply Reaches.prepend (Step.matrix_join_pc18 _ _ _ (by exact bi.row s.v6))
      apply Reaches.prepend (Step.matrix_join_pc17 ..)
      apply Reaches.prepend (Step.matrix_join_pc16 ..)
      simp only [bound]
      apply Reaches.trans (topRun.2 _)
      apply Reaches.prepend (Step.matrix_join_pc15 ..)
      apply Reaches.prepend (Step.matrix_join_pc14 ..)
      apply Reaches.prepend (Step.matrix_join_pc13 _ _ _ (by exact topFrame.valid stored.1))
      apply Reaches.prepend (Step.matrix_join_pc12 _ _ _ (by exact ci.row s.v6))
      apply Reaches.prepend (Step.matrix_join_pc11 _ _ _ (by exact di.row s.v6))
      apply Reaches.prepend (Step.matrix_join_pc10 ..)
      apply Reaches.prepend (Step.matrix_join_pc9 ..)
      apply Reaches.trans (bottomRun.2 _)
      apply Reaches.prepend (Step.matrix_join_pc8 ..)
      apply Reaches.prepend (Step.matrix_join_pc7 ..)
      apply Reaches.prepend (Step.matrix_join_pc6 _ _ _ (by exact bottomFrame.valid topStored.1))
      apply Reaches.prepend (Step.matrix_join_pc5 ..)
      simpa only [next,nextHeap,middle,bound,show seq_Seq_Int = rows from rfl] using completed stack
    · intro name
      rw [afterClocks]
      change two.clocks name + _ = _
      rw [bottomClocks]
      change one.clocks name + _ + _ = _
      rw [topClocks]
      by_cases same : name = "copied_cells" <;> simp [Clocks.single,same,Nat.add_mul] <;> omega

/-- Join four nested blocks into a fresh matrix; every finite row comes from
    an independent row allocation. Input rows may alias freely. -/
theorem join_contract_rows (heap : Heap) (a b c d : CollectionRef) (av bv cv dv : Values) (h : Nat)
    (sa : Stored heap a av) (sb : Stored heap b bv) (sc : Stored heap c cv) (sd : Stored heap d dv)
    (_positive : 0 < h) :
    ∃ after result, matrix_join.Call heap (a,b,c,d,(h:Int)) after result ∧
      Extends heap after ∧ Stored after result (StrassenValues.joinValues h av bv cv dv) ∧
      (∀ name, after.clocks name = heap.clocks name + Clocks.single "copied_cells" (4*(h*h)) name) ∧
      heap.nextCollection ≤ result ∧ FreshRows heap after result (2*h) := by
  let initialized := (rows.const (heap.allocate (fun _ => 0)) heap.nextRef).1
  have frame : Extends heap initialized := (extends_allocate heap _).trans (extends_const _ _)
  have stored : Stored initialized heap.nextCollection (fun _ _ => 0) :=
    stored_const (heap.allocate (fun _ => 0)) heap.nextRef _ (Nat.lt_succ_self _) (by simp [Heap.allocate])
  let state : State_matrix_join := { v0 := a, v1 := b, v2 := c, v3 := d, v4 := h, v5 := heap.nextCollection, t21 := heap.nextCollection, t22 := heap.nextRef }
  obtain ⟨after,completed,afterFrame,afterStored,afterClocks,afterOwned⟩ :=
    joinMatrixLoop h heap initialized state h 0 av bv cv dv rfl rfl (by omega) sa sb sc sd frame (Nat.le_refl _)
      (by simpa only [state,paired_zero] using stored)
      (by
        constructor
        · intro j impossible
          simp only [pairedDomain, Nat.add_zero] at impossible
          omega
        · intro j k impossible
          simp only [pairedDomain, Nat.add_zero] at impossible
          omega)
  refine ⟨after,heap.nextCollection,⟨⟨sa.1,sb.1,sc.1,sd.1⟩,?_⟩,afterFrame,afterStored,afterClocks,Nat.le_refl _,afterOwned⟩
  intro stack
  apply Reaches.prepend (Step.matrix_join_pc24 ..)
  apply Reaches.prepend (Step.matrix_join_pc23 ..)
  apply Reaches.prepend (Step.matrix_join_pc22 ..)
  apply Reaches.prepend (Step.matrix_join_pc21 ..)
  apply Reaches.prepend (Step.matrix_join_pc20 ..)
  exact completed stack



end MatrixStrassenHelpers

end

/-! Source: proofs/chapter4/StrassenQuadrant.lean -/

section

/-! A square-block copy composes the verified row copier, preserving arbitrary
shared input rows while allocating the result row by row. -/
open Algo2LeanCore Algo2LeanGenerated Algo2LeanCore.MatrixHeap
namespace MatrixStrassenHelpers



private theorem quadrant_prefix_next (values : Values) (i : Nat) :
    (fun j => if j = (i : Int) then values i else quadrantPrefix values i j) =
      quadrantPrefix values (i + 1) := by
  funext j k
  by_cases same : j = (i : Int)
  · subst j
    simp only
    change values i k = if 0 ≤ (i : Int) ∧ (i : Int) < ((i + 1 : Nat) : Int) then values i k else 0
    rw [if_pos (by omega)]
  · simp only [if_neg same]
    have eqRange : (0 ≤ j ∧ j < (i : Int)) ↔ (0 ≤ j ∧ j < ((i + 1 : Nat) : Int)) := by omega
    simp only [quadrantPrefix, eqRange]

private theorem quadrant_prefix_zero (values : Values) :
    quadrantPrefix values 0 = fun _ _ => 0 := by
  funext i j
  simp only [quadrantPrefix, Int.natCast_zero]
  rw [if_neg (by omega)]

private theorem quadrantMatrixLoop (remaining : Nat) (base heap : Heap) (s : State_matrix_quadrant)
    (h i : Nat) (av : Values) (bound : s.v2 = (h : Int)) (index : s.v6 = (i : Int))
    (finish : i + remaining = h) (sa : Stored base s.v0 av)
    (frame : Extends base heap) (fresh : base.nextCollection ≤ s.v5)
    (stored : Stored heap s.v5 (quadrantPrefix (fun r c =>
      if 0 ≤ c ∧ c < (h : Int) then av (s.v3 + r) (s.v4 + c) else 0) i)) :
    ∃ after, Summary Step heap (.fn_matrix_quadrant 4 s) after (.fn_matrix_quadrant s.v5) ∧
      Extends base after ∧ Stored after s.v5 (StrassenValues.quadrantValues s.v1 h s.v3 s.v4 av) ∧
      (∀ name, after.clocks name = heap.clocks name + Clocks.single "copied_cells" (remaining * h) name) := by
  induction remaining generalizing heap s i with
  | zero =>
    have ieq : i = h := by omega
    subst i
    refine ⟨heap, ?_, frame, ?_, ?_⟩
    · intro stack
      apply Reaches.prepend (Step.matrix_quadrant_pc4 ..)
      apply Reaches.prepend (Step.matrix_quadrant_pc3_false _ _ _ (by simp [bound, index]))
      apply Reaches.prepend (Step.matrix_quadrant_pc2 ..)
      exact Reaches.single (Step.matrix_quadrant_pc1 _ _ _ stored.1)
    · have eqValues : quadrantPrefix (fun r c => if 0 ≤ c ∧ c < (h : Int)
          then av (s.v3 + r) (s.v4 + c) else 0) h =
          StrassenValues.quadrantValues s.v1 h s.v3 s.v4 av := by
        funext r c
        simp only [quadrantPrefix, StrassenValues.quadrantValues]
        grind
      rw [eqValues] at stored
      exact stored
    · intro name; simp [Clocks.single]
  | succ remaining ih =>
    have ai := sa.mono frame
    obtain ⟨one, row, rowRun, rowFrame, rowValid, rowFresh, rowValue, rowClocks⟩ :=
      quadrant_row_contract heap ((rows.get heap s.v0 (s.v3 + s.v6)).getD 0) h s.v4
        (ai.row_valid (s.v3 + s.v6))
    let nextHeap := rows.set one s.v5 s.v6 row
    let next : State_matrix_quadrant := { s with v6 := s.v6 + 1, t8 := decide (s.v6 < s.v2), t9 := row, t10 := s.v6, t11 := s.v5, t12 := (rows.get heap s.v0 (s.v3 + s.v6)).getD 0, t13 := s.v2, t14 := s.v4 }
    have nextFrame : Extends base nextHeap := (frame.trans rowFrame).set s.v5 fresh s.v6 row
    have nextStored : Stored nextHeap next.v5 (quadrantPrefix (fun r c =>
        if 0 ≤ c ∧ c < (h : Int) then av (next.v3 + r) (next.v4 + c) else 0) (i + 1)) := by
      have st := (stored.mono rowFrame).set s.v6 row _ rowValid rowValue
      have rowEq : (fun c => if 0 ≤ c ∧ c < (h : Int) then
          heap.read ((rows.get heap s.v0 (s.v3 + s.v6)).getD 0) (s.v4 + c) else 0) =
          (fun c => if 0 ≤ c ∧ c < (h : Int) then av (s.v3 + (i : Int)) (s.v4 + c) else 0) := by
        funext c; rw [ai.read, index]
      rw [rowEq, index, quadrant_prefix_next
        (fun r c => if 0 ≤ c ∧ c < (h : Int) then av (s.v3 + r) (s.v4 + c) else 0) i] at st
      simpa only [nextHeap, next, index] using st
    obtain ⟨after, completed, afterFrame, afterStored, afterClocks⟩ :=
      ih nextHeap next (i + 1) bound (by dsimp [next]; omega) (by omega) sa nextFrame fresh nextStored
    refine ⟨after, ?_, afterFrame, afterStored, ?_⟩
    · intro stack
      apply Reaches.prepend (Step.matrix_quadrant_pc4 ..)
      apply Reaches.prepend (Step.matrix_quadrant_pc3_true _ _ _ (by simp [bound, index]; omega))
      apply Reaches.prepend (Step.matrix_quadrant_pc12 _ _ _ (by exact ai.row (s.v3 + s.v6)))
      apply Reaches.prepend (Step.matrix_quadrant_pc11 ..)
      apply Reaches.prepend (Step.matrix_quadrant_pc10 ..)
      apply Reaches.prepend (Step.matrix_quadrant_pc9 ..)
      simp only [bound]
      apply Reaches.trans (rowRun.2 _)
      apply Reaches.prepend (Step.matrix_quadrant_pc8 ..)
      apply Reaches.prepend (Step.matrix_quadrant_pc7 ..)
      apply Reaches.prepend (Step.matrix_quadrant_pc6 _ _ _ (by exact rowFrame.valid stored.1))
      apply Reaches.prepend (Step.matrix_quadrant_pc5 ..)
      simpa only [next, nextHeap, bound, show seq_Seq_Int = rows from rfl] using completed stack
    · intro name
      rw [afterClocks]
      change one.clocks name + _ = _
      rw [rowClocks]
      by_cases same : name = "copied_cells" <;> simp [Clocks.single, same, Nat.add_mul] <;> omega

/-- Copy a square block into a fresh nested matrix, preserving all input objects
    and charging exactly one copy for each of its h² entries. -/
theorem quadrant_contract (heap : Heap) (a : CollectionRef) (av : Values)
    (n row col : Int) (h : Nat) (sa : Stored heap a av) (_positive : 0 < h) :
    ∃ after result, matrix_quadrant.Call heap (a, n, (h : Int), row, col) after result ∧
      Extends heap after ∧ Stored after result (StrassenValues.quadrantValues n h row col av) ∧
      (∀ name, after.clocks name = heap.clocks name + Clocks.single "copied_cells" (h * h) name) := by
  let initialized := (rows.const (heap.allocate (fun _ => 0)) heap.nextRef).1
  have frame : Extends heap initialized := (extends_allocate heap _).trans (extends_const _ _)
  have stored : Stored initialized heap.nextCollection (fun _ _ => 0) :=
    stored_const (heap.allocate (fun _ => 0)) heap.nextRef _ (Nat.lt_succ_self _) (by simp [Heap.allocate])
  let state : State_matrix_quadrant := { v0 := a, v1 := n, v2 := h, v3 := row, v4 := col, v5 := heap.nextCollection, t15 := heap.nextCollection, t16 := heap.nextRef }
  obtain ⟨after, completed, afterFrame, afterStored, afterClocks⟩ :=
    quadrantMatrixLoop h heap initialized state h 0 av rfl rfl (by omega) sa frame (Nat.le_refl _)
      (by simpa only [state, quadrant_prefix_zero] using stored)
  refine ⟨after, heap.nextCollection, ⟨sa.1, ?_⟩, afterFrame, afterStored, afterClocks⟩
  intro stack
  apply Reaches.prepend (Step.matrix_quadrant_pc17 ..)
  apply Reaches.prepend (Step.matrix_quadrant_pc16 ..)
  apply Reaches.prepend (Step.matrix_quadrant_pc15 ..)
  apply Reaches.prepend (Step.matrix_quadrant_pc14 ..)
  apply Reaches.prepend (Step.matrix_quadrant_pc13 ..)
  exact completed stack

end MatrixStrassenHelpers

end

/-! Source: proofs/chapter4/StrassenComposition.lean -/

section

/-! Composition of the recursive branch using only source-level call summaries.
Each field records one real source call in evaluation order, including nested
arguments. This lemma by itself assumes no mathematical correctness contract. -/

open Algo2LeanCore Algo2LeanGenerated

namespace MatrixStrassenComposition











set_option maxHeartbeats 1600000 in
/-- Composing the branch calls produces a summary of the actual generated
    program. The initial call tick is included, while each supplied summary
    accounts for its own heap effects and operation counts. -/
theorem recursive_summary (heap : Heap) (a b : CollectionRef) (n half : Int)
    (validA : seq_Seq_Int.valid heap a) (validB : seq_Seq_Int.valid heap b)
    (recursive : 1 < n) (halfEq : Int.fdiv n 2 = half)
    (plan : BranchRun (heap.tick "calls") a b n half) :
    strassen.Call heap (a, b, n) plan.finalHeap plan.result := by
  refine ⟨⟨validA, validB⟩, ?_⟩
  intro stack
  apply Reaches.prepend (Step.strassen_pc195 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc194 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc193_false _ _ _ (by simp; omega))
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc192 _ _ _ (by decide))
  dsimp only
  simp only [halfEq]
  apply Reaches.prepend (Step.strassen_pc191 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc190 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc189 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc188 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc187 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc186 ..)
  dsimp only
  apply Reaches.trans (plan.a11_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc185 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc184 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc183 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc182 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc181 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc180 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc179 ..)
  dsimp only
  apply Reaches.trans (plan.a12_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc178 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc177 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc176 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc175 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc174 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc173 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc172 ..)
  dsimp only
  apply Reaches.trans (plan.a21_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc171 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc170 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc169 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc168 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc167 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc166 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc165 ..)
  dsimp only
  apply Reaches.trans (plan.a22_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc164 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc163 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc162 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc161 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc160 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc159 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc158 ..)
  dsimp only
  apply Reaches.trans (plan.b11_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc157 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc156 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc155 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc154 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc153 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc152 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc151 ..)
  dsimp only
  apply Reaches.trans (plan.b12_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc150 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc149 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc148 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc147 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc146 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc145 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc144 ..)
  dsimp only
  apply Reaches.trans (plan.b21_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc143 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc142 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc141 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc140 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc139 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc138 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc137 ..)
  dsimp only
  apply Reaches.trans (plan.b22_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc136 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc135 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc134 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc133 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc132 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc131 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc130 ..)
  dsimp only
  apply Reaches.trans (plan.linear1_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc129 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc128 ..)
  dsimp only
  apply Reaches.trans (plan.p1_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc127 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc126 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc125 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc124 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc123 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc122 ..)
  dsimp only
  apply Reaches.trans (plan.linear2_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc121 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc120 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc119 ..)
  dsimp only
  apply Reaches.trans (plan.p2_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc118 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc117 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc116 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc115 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc114 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc113 ..)
  dsimp only
  apply Reaches.trans (plan.linear3_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc112 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc111 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc110 ..)
  dsimp only
  apply Reaches.trans (plan.p3_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc109 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc108 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc107 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc106 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc105 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc104 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc103 ..)
  dsimp only
  apply Reaches.trans (plan.linear4_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc102 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc101 ..)
  dsimp only
  apply Reaches.trans (plan.p4_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc100 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc99 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc98 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc97 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc96 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc95 ..)
  dsimp only
  apply Reaches.trans (plan.linear5_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc94 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc93 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc92 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc91 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc90 ..)
  dsimp only
  apply Reaches.trans (plan.linear6_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc89 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc88 ..)
  dsimp only
  apply Reaches.trans (plan.p5_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc87 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc86 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc85 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc84 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc83 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc82 ..)
  dsimp only
  apply Reaches.trans (plan.linear7_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc81 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc80 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc79 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc78 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc77 ..)
  dsimp only
  apply Reaches.trans (plan.linear8_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc76 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc75 ..)
  dsimp only
  apply Reaches.trans (plan.p6_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc74 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc73 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc72 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc71 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc70 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc69 ..)
  dsimp only
  apply Reaches.trans (plan.linear9_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc68 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc67 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc66 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc65 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc64 ..)
  dsimp only
  apply Reaches.trans (plan.linear10_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc63 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc62 ..)
  dsimp only
  apply Reaches.trans (plan.p7_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc61 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc60 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc59 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc58 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc57 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc56 ..)
  dsimp only
  apply Reaches.trans (plan.linear11_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc55 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc54 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc53 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc52 ..)
  dsimp only
  apply Reaches.trans (plan.linear12_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc51 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc50 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc49 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc48 ..)
  dsimp only
  apply Reaches.trans (plan.c11_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc47 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc46 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc45 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc44 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc43 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc42 ..)
  dsimp only
  apply Reaches.trans (plan.c12_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc41 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc40 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc39 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc38 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc37 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc36 ..)
  dsimp only
  apply Reaches.trans (plan.c21_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc35 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc34 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc33 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc32 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc31 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc30 ..)
  dsimp only
  apply Reaches.trans (plan.linear16_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc29 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc28 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc27 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc26 ..)
  dsimp only
  apply Reaches.trans (plan.linear17_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc25 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc24 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc23 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc22 ..)
  dsimp only
  apply Reaches.trans (plan.c22_run.2 _)
  try dsimp only
  apply Reaches.prepend (Step.strassen_pc21 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc20 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc19 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc18 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc17 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc16 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc15 ..)
  dsimp only
  apply Reaches.trans (plan.joined_run.2 _)
  try dsimp only
  exact Reaches.single (Step.strassen_pc14 _ _ _ plan.result_valid)

end MatrixStrassenComposition

end

/-! Source: proofs/chapter4/StrassenExecution.lean -/

section

open Algo2LeanCore Algo2LeanGenerated MatrixStrassenAnalysis MatrixStrassenHelpers
open Algo2LeanCore.MatrixHeap
open MatrixStrassenComposition

namespace MatrixStrassenExecution



@[simp] theorem square_half (depth : Nat) : (2^depth)*(2^depth) = (4:Nat)^depth := by
  rw [← Nat.mul_pow]

/-- This is the actual call tree and per-node instrumentation of the source. -/
theorem costs_step (depth : Nat) (name : String) :
    costs (depth+1) name = (if name = "calls" then 1 else 0) + 7*costs depth name +
      (if name = "linear_cells" then 18*((2^depth)*(2^depth)) else 0) +
      (if name = "copied_cells" then 12*((2^depth)*(2^depth)) else 0) := by
  by_cases calls : name = "calls" <;> by_cases products : name = "products" <;>
    by_cases linear : name = "linear_cells" <;> by_cases copied : name = "copied_cells" <;>
    simp_all [costs, Chapter4Math.calls, Chapter4Math.strassenOverhead, Nat.pow_succ] <;> omega

theorem tick_preserves (heap : Heap) : Extends heap (heap.tick "calls") := extends_tick heap "calls" 1

private theorem leaf_contract_rows (heap : Heap) (a b : CollectionRef) (av bv : Values)
    (sa : Stored heap a av) (sb : Stored heap b bv) :
    ∃ after result, strassen.Call heap (a,b,1) after result ∧
      Extends heap after ∧ Stored after result (StrassenValues.strassenValue 0 av bv) ∧
      (∀ name, after.clocks name = heap.clocks name + costs 0 name) ∧ heap.nextCollection ≤ result ∧ FreshRows heap after result 1 := by
  let zero := (heap.tick "calls").allocate (fun _ => 0)
  let outer := (rows.const zero heap.nextRef).1
  let allocated := outer.allocate (fun _ => 0)
  let installed := rows.set allocated heap.nextCollection 0 (heap.nextRef+1)
  let final := (installed.write (heap.nextRef+1) 0 (av 0 0*bv 0 0)).tick "products"
  have frameZero : Extends heap zero := (extends_tick heap "calls" 1).trans (extends_allocate _ _)
  have frameOuter : Extends heap outer := frameZero.trans (extends_const _ _)
  have frameAllocated : Extends heap allocated := frameOuter.trans (extends_allocate _ _)
  have frameInstalled : Extends heap installed := frameAllocated.set heap.nextCollection (Nat.le_refl _) 0 _
  have ai := sa.mono frameInstalled
  have bi := sb.mono frameInstalled
  have initialStored : Stored outer heap.nextCollection (fun _ _ => 0) :=
    stored_const zero heap.nextRef _ (Nat.lt_succ_self _) (by simp [zero,Heap.allocate])
  have allocatedStored := initialStored.mono (extends_allocate outer (fun _ => 0))
  have installedStored : Stored installed heap.nextCollection (fun _ _ => 0) := by
    have st := allocatedStored.set 0 (heap.nextRef+1) (fun _ => 0)
      (by simp [allocated,outer,zero,SequenceType.const,SequenceType.create,Heap.createSequence])
      (by simp [allocated,outer,zero,SequenceType.const,SequenceType.create,Heap.createSequence,Heap.allocate])
    simpa only [ite_self] using st
  have outputRow : rows.get installed heap.nextCollection 0 = some (heap.nextRef+1) :=
    rows.get_set_same allocated heap.nextCollection 0 _ allocatedStored.1
  refine ⟨final,heap.nextCollection,?_,?_,?_,?_,Nat.le_refl _,?_⟩
  · refine ⟨⟨sa.1,sb.1⟩,?_⟩
    intro stack
    apply Reaches.prepend (Step.strassen_pc195 ..)
    apply Reaches.prepend (Step.strassen_pc194 ..)
    apply Reaches.prepend (Step.strassen_pc193_true _ _ _ (by simp))
    apply Reaches.prepend (Step.strassen_pc13 ..)
    apply Reaches.prepend (Step.strassen_pc12 ..)
    apply Reaches.prepend (Step.strassen_pc11 ..)
    apply Reaches.prepend (Step.strassen_pc10 ..)
    apply Reaches.prepend (Step.strassen_pc9 ..)
    apply Reaches.prepend (Step.strassen_pc8 ..)
    apply Reaches.prepend (Step.strassen_pc7 ..)
    apply Reaches.prepend (Step.strassen_pc6 ..)
    apply Reaches.prepend (Step.strassen_pc5 _ _ _ (by exact allocatedStored.1))
    apply Reaches.prepend (Step.strassen_pc4 _ _ _ (by
      repeat' apply And.intro
      all_goals first | exact ai.row 0 | exact ai.row_valid 0 | exact bi.row 0 | exact bi.row_valid 0 | exact installedStored.row 0 | exact installedStored.row_valid 0))
    dsimp only
    change Reaches Step (.active (installed.write ((rows.get installed heap.nextCollection 0).getD 0) 0
      (installed.read ((rows.get installed a 0).getD 0) 0 * installed.read ((rows.get installed b 0).getD 0) 0)) _ _) _
    rw [outputRow,ai.read,bi.read]
    dsimp only [Option.getD]
    apply Reaches.prepend (Step.strassen_pc3 ..)
    apply Reaches.prepend (Step.strassen_pc2 ..)
    exact Reaches.single (Step.strassen_pc1 _ _ _ installedStored.1)
  · exact (frameInstalled.write (heap.nextRef+1) (by omega) 0 _).trans (extends_tick _ "products" 1)
  · refine ⟨installedStored.1,?_⟩
    intro i
    by_cases same : i = 0
    · subst i
      refine ⟨heap.nextRef+1,?_,?_,?_⟩
      · simpa only [final,rows_get_tick,rows_get_write] using outputRow
      · change heap.nextRef + 1 < heap.nextRef + 1 + 1
        omega
      · funext j
        simp [final,installed,allocated,outer,zero,SequenceType.set,SequenceType.const,SequenceType.create,Heap.createSequence,Heap.writeElement,Heap.write,Heap.allocate,StrassenValues.strassenValue]
    · refine ⟨heap.nextRef,?_,?_,?_⟩
      · change rows.get installed heap.nextCollection i = some heap.nextRef
        rw [rows.get_set_other_index allocated heap.nextCollection i 0 _ same]
        change rows.get outer heap.nextCollection i = some heap.nextRef
        exact rows.get_const zero heap.nextRef i
      · change heap.nextRef < heap.nextRef + 1 + 1
        exact Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)
      · funext j
        simp [final,installed,allocated,outer,zero,SequenceType.set,SequenceType.const,SequenceType.create,Heap.createSequence,Heap.writeElement,Heap.write,Heap.allocate,StrassenValues.strassenValue,same]
  · intro name
    by_cases calls : name = "calls" <;> by_cases products : name = "products" <;>
      simp_all [final,installed,allocated,outer,zero,SequenceType.set,SequenceType.const,SequenceType.create,Heap.createSequence,Heap.writeElement,Heap.write,Heap.tick,costs,Chapter4Math.calls,Chapter4Math.strassenOverhead]
  · constructor
    · intro i valid
      have izero : i = 0 := by omega
      subst i
      refine ⟨heap.nextRef+1,?_,by omega,?_⟩
      · simpa only [Int.natCast_zero,final,rows_get_tick,rows_get_write] using outputRow
      · change heap.nextRef+1 < heap.nextRef+1+1
        exact Nat.lt_succ_self _
    · intro i j hi hj _
      omega

/-- Every source invocation terminates on a power-of-two dimension, returns the
    mathematically specified Strassen value, preserves all earlier arrays, and
    charges these exact counters in the same execution. Its result reference
    is fresh relative to every sequence allocated before the invocation. -/
theorem strassen_summary_rows (depth : Nat) (heap : Heap) (a b : CollectionRef) (av bv : Values)
    (sa : Stored heap a av) (sb : Stored heap b bv) :
    ∃ after result, strassen.Call heap (a,b,((2^depth:Nat):Int)) after result ∧
      Extends heap after ∧ Stored after result (StrassenValues.strassenValue depth av bv) ∧
      (∀ name, after.clocks name = heap.clocks name + costs depth name) ∧ heap.nextCollection ≤ result ∧ FreshRows heap after result (2^depth) := by
  induction depth generalizing heap a b av bv with
  | zero => simpa only [Nat.pow_zero,Int.natCast_one] using leaf_contract_rows heap a b av bv sa sb
  | succ depth ih =>
    let h : Nat := 2^depth
    let n : Int := 2*h
    have positive : 0 < h := Nat.pow_pos (by decide)
    have startA := sa.mono (tick_preserves heap)
    have startB := sb.mono (tick_preserves heap)
    let a11Values : Values := StrassenValues.quadrantValues n h 0 0 av
    obtain ⟨a11Heap, a11Ref, a11Run, a11Frame, a11Stored, a11Clocks⟩ :=
      quadrant_contract (heap.tick "calls") a av n 0 0 h startA positive
    change Stored a11Heap a11Ref a11Values at a11Stored
    let a12Values : Values := StrassenValues.quadrantValues n h 0 h av
    obtain ⟨a12Heap, a12Ref, a12Run, a12Frame, a12Stored, a12Clocks⟩ :=
      quadrant_contract a11Heap a av n 0 h h (startA.mono a11Frame) positive
    change Stored a12Heap a12Ref a12Values at a12Stored
    let a21Values : Values := StrassenValues.quadrantValues n h h 0 av
    obtain ⟨a21Heap, a21Ref, a21Run, a21Frame, a21Stored, a21Clocks⟩ :=
      quadrant_contract a12Heap a av n h 0 h (startA.mono (a11Frame.trans a12Frame)) positive
    change Stored a21Heap a21Ref a21Values at a21Stored
    let a22Values : Values := StrassenValues.quadrantValues n h h h av
    obtain ⟨a22Heap, a22Ref, a22Run, a22Frame, a22Stored, a22Clocks⟩ :=
      quadrant_contract a21Heap a av n h h h (startA.mono (a11Frame.trans (a12Frame.trans a21Frame))) positive
    change Stored a22Heap a22Ref a22Values at a22Stored
    let b11Values : Values := StrassenValues.quadrantValues n h 0 0 bv
    obtain ⟨b11Heap, b11Ref, b11Run, b11Frame, b11Stored, b11Clocks⟩ :=
      quadrant_contract a22Heap b bv n 0 0 h (startB.mono (a11Frame.trans (a12Frame.trans (a21Frame.trans a22Frame)))) positive
    change Stored b11Heap b11Ref b11Values at b11Stored
    let b12Values : Values := StrassenValues.quadrantValues n h 0 h bv
    obtain ⟨b12Heap, b12Ref, b12Run, b12Frame, b12Stored, b12Clocks⟩ :=
      quadrant_contract b11Heap b bv n 0 h h (startB.mono (a11Frame.trans (a12Frame.trans (a21Frame.trans (a22Frame.trans b11Frame))))) positive
    change Stored b12Heap b12Ref b12Values at b12Stored
    let b21Values : Values := StrassenValues.quadrantValues n h h 0 bv
    obtain ⟨b21Heap, b21Ref, b21Run, b21Frame, b21Stored, b21Clocks⟩ :=
      quadrant_contract b12Heap b bv n h 0 h (startB.mono (a11Frame.trans (a12Frame.trans (a21Frame.trans (a22Frame.trans (b11Frame.trans b12Frame)))))) positive
    change Stored b21Heap b21Ref b21Values at b21Stored
    let b22Values : Values := StrassenValues.quadrantValues n h h h bv
    obtain ⟨b22Heap, b22Ref, b22Run, b22Frame, b22Stored, b22Clocks⟩ :=
      quadrant_contract b21Heap b bv n h h h (startB.mono (a11Frame.trans (a12Frame.trans (a21Frame.trans (a22Frame.trans (b11Frame.trans (b12Frame.trans b21Frame))))))) positive
    change Stored b22Heap b22Ref b22Values at b22Stored
    let linear1Values : Values := StrassenValues.linearValues h (-1) b12Values b22Values
    obtain ⟨linear1Heap, linear1Ref, linear1Run, linear1Frame, linear1Stored, linear1Clocks⟩ :=
      linear_contract b22Heap b12Ref b22Ref b12Values b22Values h (-1) (b12Stored.mono (b21Frame.trans b22Frame)) b22Stored
    change Stored linear1Heap linear1Ref linear1Values at linear1Stored
    let p1Values : Values := StrassenValues.strassenValue depth a11Values linear1Values
    obtain ⟨p1Heap, p1Ref, p1Run, p1Frame, p1Stored, p1Clocks, _⟩ :=
      ih linear1Heap a11Ref linear1Ref a11Values linear1Values (a11Stored.mono (a12Frame.trans (a21Frame.trans (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans linear1Frame)))))))) linear1Stored
    change Stored p1Heap p1Ref p1Values at p1Stored
    let linear2Values : Values := StrassenValues.linearValues h (1) a11Values a12Values
    obtain ⟨linear2Heap, linear2Ref, linear2Run, linear2Frame, linear2Stored, linear2Clocks⟩ :=
      linear_contract p1Heap a11Ref a12Ref a11Values a12Values h (1) (a11Stored.mono (a12Frame.trans (a21Frame.trans (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans p1Frame))))))))) (a12Stored.mono (a21Frame.trans (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans p1Frame))))))))
    change Stored linear2Heap linear2Ref linear2Values at linear2Stored
    let p2Values : Values := StrassenValues.strassenValue depth linear2Values b22Values
    obtain ⟨p2Heap, p2Ref, p2Run, p2Frame, p2Stored, p2Clocks, _⟩ :=
      ih linear2Heap linear2Ref b22Ref linear2Values b22Values linear2Stored (b22Stored.mono (linear1Frame.trans (p1Frame.trans linear2Frame)))
    change Stored p2Heap p2Ref p2Values at p2Stored
    let linear3Values : Values := StrassenValues.linearValues h (1) a21Values a22Values
    obtain ⟨linear3Heap, linear3Ref, linear3Run, linear3Frame, linear3Stored, linear3Clocks⟩ :=
      linear_contract p2Heap a21Ref a22Ref a21Values a22Values h (1) (a21Stored.mono (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans p2Frame))))))))) (a22Stored.mono (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans p2Frame))))))))
    change Stored linear3Heap linear3Ref linear3Values at linear3Stored
    let p3Values : Values := StrassenValues.strassenValue depth linear3Values b11Values
    obtain ⟨p3Heap, p3Ref, p3Run, p3Frame, p3Stored, p3Clocks, _⟩ :=
      ih linear3Heap linear3Ref b11Ref linear3Values b11Values linear3Stored (b11Stored.mono (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans linear3Frame))))))))
    change Stored p3Heap p3Ref p3Values at p3Stored
    let linear4Values : Values := StrassenValues.linearValues h (-1) b21Values b11Values
    obtain ⟨linear4Heap, linear4Ref, linear4Run, linear4Frame, linear4Stored, linear4Clocks⟩ :=
      linear_contract p3Heap b21Ref b11Ref b21Values b11Values h (-1) (b21Stored.mono (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans p3Frame))))))) (b11Stored.mono (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans p3Frame)))))))))
    change Stored linear4Heap linear4Ref linear4Values at linear4Stored
    let p4Values : Values := StrassenValues.strassenValue depth a22Values linear4Values
    obtain ⟨p4Heap, p4Ref, p4Run, p4Frame, p4Stored, p4Clocks, _⟩ :=
      ih linear4Heap a22Ref linear4Ref a22Values linear4Values (a22Stored.mono (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans linear4Frame))))))))))) linear4Stored
    change Stored p4Heap p4Ref p4Values at p4Stored
    let linear5Values : Values := StrassenValues.linearValues h (1) a11Values a22Values
    obtain ⟨linear5Heap, linear5Ref, linear5Run, linear5Frame, linear5Stored, linear5Clocks⟩ :=
      linear_contract p4Heap a11Ref a22Ref a11Values a22Values h (1) (a11Stored.mono (a12Frame.trans (a21Frame.trans (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans p4Frame))))))))))))))) (a22Stored.mono (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans p4Frame))))))))))))
    change Stored linear5Heap linear5Ref linear5Values at linear5Stored
    let linear6Values : Values := StrassenValues.linearValues h (1) b11Values b22Values
    obtain ⟨linear6Heap, linear6Ref, linear6Run, linear6Frame, linear6Stored, linear6Clocks⟩ :=
      linear_contract linear5Heap b11Ref b22Ref b11Values b22Values h (1) (b11Stored.mono (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans linear5Frame)))))))))))) (b22Stored.mono (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans linear5Frame)))))))))
    change Stored linear6Heap linear6Ref linear6Values at linear6Stored
    let p5Values : Values := StrassenValues.strassenValue depth linear5Values linear6Values
    obtain ⟨p5Heap, p5Ref, p5Run, p5Frame, p5Stored, p5Clocks, _⟩ :=
      ih linear6Heap linear5Ref linear6Ref linear5Values linear6Values (linear5Stored.mono linear6Frame) linear6Stored
    change Stored p5Heap p5Ref p5Values at p5Stored
    let linear7Values : Values := StrassenValues.linearValues h (-1) a12Values a22Values
    obtain ⟨linear7Heap, linear7Ref, linear7Run, linear7Frame, linear7Stored, linear7Clocks⟩ :=
      linear_contract p5Heap a12Ref a22Ref a12Values a22Values h (-1) (a12Stored.mono (a21Frame.trans (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans p5Frame))))))))))))))))) (a22Stored.mono (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans p5Frame)))))))))))))))
    change Stored linear7Heap linear7Ref linear7Values at linear7Stored
    let linear8Values : Values := StrassenValues.linearValues h (1) b21Values b22Values
    obtain ⟨linear8Heap, linear8Ref, linear8Run, linear8Frame, linear8Stored, linear8Clocks⟩ :=
      linear_contract linear7Heap b21Ref b22Ref b21Values b22Values h (1) (b21Stored.mono (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans linear7Frame))))))))))))) (b22Stored.mono (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans linear7Frame))))))))))))
    change Stored linear8Heap linear8Ref linear8Values at linear8Stored
    let p6Values : Values := StrassenValues.strassenValue depth linear7Values linear8Values
    obtain ⟨p6Heap, p6Ref, p6Run, p6Frame, p6Stored, p6Clocks, _⟩ :=
      ih linear8Heap linear7Ref linear8Ref linear7Values linear8Values (linear7Stored.mono linear8Frame) linear8Stored
    change Stored p6Heap p6Ref p6Values at p6Stored
    let linear9Values : Values := StrassenValues.linearValues h (-1) a11Values a21Values
    obtain ⟨linear9Heap, linear9Ref, linear9Run, linear9Frame, linear9Stored, linear9Clocks⟩ :=
      linear_contract p6Heap a11Ref a21Ref a11Values a21Values h (-1) (a11Stored.mono (a12Frame.trans (a21Frame.trans (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans p6Frame))))))))))))))))))))) (a21Stored.mono (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans p6Frame)))))))))))))))))))
    change Stored linear9Heap linear9Ref linear9Values at linear9Stored
    let linear10Values : Values := StrassenValues.linearValues h (1) b11Values b12Values
    obtain ⟨linear10Heap, linear10Ref, linear10Run, linear10Frame, linear10Stored, linear10Clocks⟩ :=
      linear_contract linear9Heap b11Ref b12Ref b11Values b12Values h (1) (b11Stored.mono (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans linear9Frame)))))))))))))))))) (b12Stored.mono (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans linear9Frame)))))))))))))))))
    change Stored linear10Heap linear10Ref linear10Values at linear10Stored
    let p7Values : Values := StrassenValues.strassenValue depth linear9Values linear10Values
    obtain ⟨p7Heap, p7Ref, p7Run, p7Frame, p7Stored, p7Clocks, _⟩ :=
      ih linear10Heap linear9Ref linear10Ref linear9Values linear10Values (linear9Stored.mono linear10Frame) linear10Stored
    change Stored p7Heap p7Ref p7Values at p7Stored
    let linear11Values : Values := StrassenValues.linearValues h (1) p5Values p4Values
    obtain ⟨linear11Heap, linear11Ref, linear11Run, linear11Frame, linear11Stored, linear11Clocks⟩ :=
      linear_contract p7Heap p5Ref p4Ref p5Values p4Values h (1) (p5Stored.mono (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans p7Frame)))))) (p4Stored.mono (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans p7Frame)))))))))
    change Stored linear11Heap linear11Ref linear11Values at linear11Stored
    let linear12Values : Values := StrassenValues.linearValues h (-1) linear11Values p2Values
    obtain ⟨linear12Heap, linear12Ref, linear12Run, linear12Frame, linear12Stored, linear12Clocks⟩ :=
      linear_contract linear11Heap linear11Ref p2Ref linear11Values p2Values h (-1) linear11Stored (p2Stored.mono (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans linear11Frame))))))))))))))
    change Stored linear12Heap linear12Ref linear12Values at linear12Stored
    let c11Values : Values := StrassenValues.linearValues h (1) linear12Values p6Values
    obtain ⟨c11Heap, c11Ref, c11Run, c11Frame, c11Stored, c11Clocks⟩ :=
      linear_contract linear12Heap linear12Ref p6Ref linear12Values p6Values h (1) linear12Stored (p6Stored.mono (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans linear12Frame)))))
    change Stored c11Heap c11Ref c11Values at c11Stored
    let c12Values : Values := StrassenValues.linearValues h (1) p1Values p2Values
    obtain ⟨c12Heap, c12Ref, c12Run, c12Frame, c12Stored, c12Clocks⟩ :=
      linear_contract c11Heap p1Ref p2Ref p1Values p2Values h (1) (p1Stored.mono (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans (linear12Frame.trans c11Frame)))))))))))))))))) (p2Stored.mono (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans (linear12Frame.trans c11Frame))))))))))))))))
    change Stored c12Heap c12Ref c12Values at c12Stored
    let c21Values : Values := StrassenValues.linearValues h (1) p3Values p4Values
    obtain ⟨c21Heap, c21Ref, c21Run, c21Frame, c21Stored, c21Clocks⟩ :=
      linear_contract c12Heap p3Ref p4Ref p3Values p4Values h (1) (p3Stored.mono (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans (linear12Frame.trans (c11Frame.trans c12Frame))))))))))))))) (p4Stored.mono (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans (linear12Frame.trans (c11Frame.trans c12Frame)))))))))))))
    change Stored c21Heap c21Ref c21Values at c21Stored
    let linear16Values : Values := StrassenValues.linearValues h (1) p5Values p1Values
    obtain ⟨linear16Heap, linear16Ref, linear16Run, linear16Frame, linear16Stored, linear16Clocks⟩ :=
      linear_contract c21Heap p5Ref p1Ref p5Values p1Values h (1) (p5Stored.mono (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans (linear12Frame.trans (c11Frame.trans (c12Frame.trans c21Frame))))))))))) (p1Stored.mono (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans (linear12Frame.trans (c11Frame.trans (c12Frame.trans c21Frame))))))))))))))))))))
    change Stored linear16Heap linear16Ref linear16Values at linear16Stored
    let linear17Values : Values := StrassenValues.linearValues h (-1) linear16Values p3Values
    obtain ⟨linear17Heap, linear17Ref, linear17Run, linear17Frame, linear17Stored, linear17Clocks⟩ :=
      linear_contract linear16Heap linear16Ref p3Ref linear16Values p3Values h (-1) linear16Stored (p3Stored.mono (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans (linear12Frame.trans (c11Frame.trans (c12Frame.trans (c21Frame.trans linear16Frame)))))))))))))))))
    change Stored linear17Heap linear17Ref linear17Values at linear17Stored
    let c22Values : Values := StrassenValues.linearValues h (-1) linear17Values p7Values
    obtain ⟨c22Heap, c22Ref, c22Run, c22Frame, c22Stored, c22Clocks⟩ :=
      linear_contract linear17Heap linear17Ref p7Ref linear17Values p7Values h (-1) linear17Stored (p7Stored.mono (linear11Frame.trans (linear12Frame.trans (c11Frame.trans (c12Frame.trans (c21Frame.trans (linear16Frame.trans linear17Frame)))))))
    change Stored c22Heap c22Ref c22Values at c22Stored
    let joinedValues : Values := StrassenValues.joinValues h c11Values c12Values c21Values c22Values
    obtain ⟨joinedHeap, joinedRef, joinedRun, joinedFrame, joinedStored, joinedClocks, joinedFresh, joinedRows⟩ :=
      join_contract_rows c22Heap c11Ref c12Ref c21Ref c22Ref c11Values c12Values c21Values c22Values h (c11Stored.mono (c12Frame.trans (c21Frame.trans (linear16Frame.trans (linear17Frame.trans c22Frame))))) (c12Stored.mono (c21Frame.trans (linear16Frame.trans (linear17Frame.trans c22Frame)))) (c21Stored.mono (linear16Frame.trans (linear17Frame.trans c22Frame))) c22Stored positive
    change Stored joinedHeap joinedRef joinedValues at joinedStored
    let plan : BranchRun (heap.tick "calls") a b n h := {
      a11 := ⟨a11Heap, a11Ref⟩
      a12 := ⟨a12Heap, a12Ref⟩
      a21 := ⟨a21Heap, a21Ref⟩
      a22 := ⟨a22Heap, a22Ref⟩
      b11 := ⟨b11Heap, b11Ref⟩
      b12 := ⟨b12Heap, b12Ref⟩
      b21 := ⟨b21Heap, b21Ref⟩
      b22 := ⟨b22Heap, b22Ref⟩
      linear1 := ⟨linear1Heap, linear1Ref⟩
      p1 := ⟨p1Heap, p1Ref⟩
      linear2 := ⟨linear2Heap, linear2Ref⟩
      p2 := ⟨p2Heap, p2Ref⟩
      linear3 := ⟨linear3Heap, linear3Ref⟩
      p3 := ⟨p3Heap, p3Ref⟩
      linear4 := ⟨linear4Heap, linear4Ref⟩
      p4 := ⟨p4Heap, p4Ref⟩
      linear5 := ⟨linear5Heap, linear5Ref⟩
      linear6 := ⟨linear6Heap, linear6Ref⟩
      p5 := ⟨p5Heap, p5Ref⟩
      linear7 := ⟨linear7Heap, linear7Ref⟩
      linear8 := ⟨linear8Heap, linear8Ref⟩
      p6 := ⟨p6Heap, p6Ref⟩
      linear9 := ⟨linear9Heap, linear9Ref⟩
      linear10 := ⟨linear10Heap, linear10Ref⟩
      p7 := ⟨p7Heap, p7Ref⟩
      linear11 := ⟨linear11Heap, linear11Ref⟩
      linear12 := ⟨linear12Heap, linear12Ref⟩
      c11 := ⟨c11Heap, c11Ref⟩
      c12 := ⟨c12Heap, c12Ref⟩
      c21 := ⟨c21Heap, c21Ref⟩
      linear16 := ⟨linear16Heap, linear16Ref⟩
      linear17 := ⟨linear17Heap, linear17Ref⟩
      c22 := ⟨c22Heap, c22Ref⟩
      joined := ⟨joinedHeap, joinedRef⟩
      a11_run := a11Run
      a12_run := a12Run
      a21_run := a21Run
      a22_run := a22Run
      b11_run := b11Run
      b12_run := b12Run
      b21_run := b21Run
      b22_run := b22Run
      linear1_run := by simpa only [Int.natCast_mul] using linear1Run
      p1_run := p1Run
      linear2_run := by simpa only [Int.natCast_mul] using linear2Run
      p2_run := p2Run
      linear3_run := by simpa only [Int.natCast_mul] using linear3Run
      p3_run := p3Run
      linear4_run := by simpa only [Int.natCast_mul] using linear4Run
      p4_run := p4Run
      linear5_run := by simpa only [Int.natCast_mul] using linear5Run
      linear6_run := by simpa only [Int.natCast_mul] using linear6Run
      p5_run := p5Run
      linear7_run := by simpa only [Int.natCast_mul] using linear7Run
      linear8_run := by simpa only [Int.natCast_mul] using linear8Run
      p6_run := p6Run
      linear9_run := by simpa only [Int.natCast_mul] using linear9Run
      linear10_run := by simpa only [Int.natCast_mul] using linear10Run
      p7_run := p7Run
      linear11_run := by simpa only [Int.natCast_mul] using linear11Run
      linear12_run := by simpa only [Int.natCast_mul] using linear12Run
      c11_run := by simpa only [Int.natCast_mul] using c11Run
      c12_run := by simpa only [Int.natCast_mul] using c12Run
      c21_run := by simpa only [Int.natCast_mul] using c21Run
      linear16_run := by simpa only [Int.natCast_mul] using linear16Run
      linear17_run := by simpa only [Int.natCast_mul] using linear17Run
      c22_run := by simpa only [Int.natCast_mul] using c22Run
      joined_run := joinedRun
      result_valid := joinedStored.1 }
    have width : ((2^(depth+1):Nat):Int) = n := by
      simp [n, h, Nat.pow_succ, Int.natCast_mul, Int.mul_comm]
    have recursive : 1 < n := by dsimp [n]; omega
    have half : Int.fdiv n 2 = (h:Int) := by
      simp [n, Int.fdiv_eq_ediv]
    have priorFrame : Extends heap c22Heap := (tick_preserves heap).trans (a11Frame.trans (a12Frame.trans (a21Frame.trans (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans (linear12Frame.trans (c11Frame.trans (c12Frame.trans (c21Frame.trans (linear16Frame.trans (linear17Frame.trans (c22Frame)))))))))))))))))))))))))))))))))
    refine ⟨joinedHeap, joinedRef, ?_, priorFrame.trans joinedFrame, ?_, ?_,
      Nat.le_trans priorFrame.nextCollection joinedFresh, ?_⟩
    · rw [width]
      exact recursive_summary heap a b n h sa.1 sb.1 recursive half plan
    · exact joinedStored
    · intro name
      rw [joinedClocks name, c22Clocks name, linear17Clocks name, linear16Clocks name, c21Clocks name, c12Clocks name, c11Clocks name, linear12Clocks name, linear11Clocks name, p7Clocks name, linear10Clocks name, linear9Clocks name, p6Clocks name, linear8Clocks name, linear7Clocks name, p5Clocks name, linear6Clocks name, linear5Clocks name, p4Clocks name, linear4Clocks name, p3Clocks name, linear3Clocks name, p2Clocks name, linear2Clocks name, p1Clocks name, linear1Clocks name, b22Clocks name, b21Clocks name, b12Clocks name, b11Clocks name, a22Clocks name, a21Clocks name, a12Clocks name, a11Clocks name]
      rw [costs_step]
      simp only [Clocks.single, Heap.tick]
      by_cases calls : name = "calls" <;> by_cases linear : name = "linear_cells" <;>
        by_cases copied : name = "copied_cells" <;> simp [calls, linear, copied, h] <;> omega
    · have sameSize : 2^ (depth+1) = 2*h := by simp [h,Nat.pow_succ,Nat.mul_comm]
      rw [sameSize]
      exact joinedRows.before_mono priorFrame.nextRef





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
open StrassenValues (strassenValue strassen_entry strassen_outside)

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











private theorem strassen_product (depth : Nat) (a b : Values) :
    StrassenValues.strassenValue depth a b = product (2^depth) a b := by
  funext row column
  unfold product
  split
  next inside =>
    have ri : ((row.toNat : Nat) : Int) = row := by omega
    have ci : ((column.toNat : Nat) : Int) = column := by omega
    have result := StrassenValues.strassen_entry depth a b row.toNat column.toNat
      (by omega) (by omega)
    simpa only [ri, ci] using result
  next outside =>
    exact StrassenValues.strassen_outside depth a b row column (by omega)

namespace MatrixMultiply



-- Main result: Correctness and running time


end MatrixMultiply

namespace MatrixRecursive



-- Main result: Correctness and running time


end MatrixRecursive

namespace Strassen



private theorem work_bounds (depth : Nat) :
    7^depth ≤ runtime (MatrixStrassenExecution.costs depth) ∧
    runtime (MatrixStrassenExecution.costs depth) ≤ 13*7^depth := by
  have overhead := Chapter4Math.strassenOverhead_exact depth
  have small : 3 * Chapter4Math.strassenOverhead depth ≤ 7^depth :=
    Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq overhead)
  have scaled := Nat.mul_le_mul_left 10 small
  have calls := Chapter4Math.calls7_bound depth
  simp only [runtime, MatrixStrassenExecution.costs]
  simp
  omega

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
namespace CLRS.Chapter4Publication.Strassen
end CLRS.Chapter4Publication.Strassen
open CLRS.Chapter4Publication CLRS.Chapter4Publication.Strassen

theorem solution :
    ∃ C : Nat, 0 < C ∧
      ∀ (heap : Heap) (a b : CollectionRef) (av bv : Values) (depth : Nat),
        Stored heap a av → Stored heap b bv →
        ∃ after result,
          MatrixStrassenLibrary.strassen.Call heap (a, b, ((2^depth : Nat) : Int)) after result ∧
          Stored after result (product (2^depth) av bv) ∧ Extends heap after ∧
          heap.nextCollection ≤ result ∧ result < after.nextCollection ∧
          FreshRows heap after result (2^depth) ∧
          heap.Increments after (MatrixStrassenExecution.costs depth) ∧
          7^depth ≤ runtime (heap.cost after) ∧ runtime (heap.cost after) ≤ C*7^depth := by
  refine ⟨13, by decide, ?_⟩
  intro heap a b av bv depth sa sb
  obtain ⟨after, result, call, frame, stored, increments, fresh, freshRows⟩ :=
    MatrixStrassenExecution.strassen_summary_rows depth heap a b av bv sa sb
  have charged : heap.Increments after (MatrixStrassenExecution.costs depth) := increments
  refine ⟨after, result, call, ?_, frame, fresh, stored.1.1, freshRows, charged, ?_⟩
  · simpa only [strassen_product] using stored
  · rw [charged.cost]
    exact work_bounds depth
