-- Prove2me | solution 1 for CountingMatroid.Analysis.LeastHalvingsCost.leastHalvings_otherSteps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T11:55:57.651994+00:00
-- url     : https://prove2.me/submissions/9c71abf0-f74a-423d-b421-ed5a78c79331

/-
Required support modules adapted from meelgroup/arlib, commit 6262f60ad7556be62e94e87f6b5811cf299e7d94. Copyright and authorship notices are preserved in each file. Module import paths use CountingMatroidSupport; original declaration namespaces are retained for proof compatibility. Arlib is not a Lake package dependency.

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
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

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
import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
section
/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/


/-!
# The cost of a primitive operation

This module is the single place in the library where "an addition costs one" is
written down.  Everything in `Arlib.Computation` reduces to it.

The design has two halves, and keeping them apart is what makes an algorithm
readable.

* A **`Cost`** is a vector of operation counts — `Op → ℕ` — not a number.  A
  program's cost is therefore recorded in units of *what it did*, with no cost
  model in sight, which is why `Arlib.Computation.Machine`'s primitives take no
  cost-model argument and an algorithm mentions none.
* A **`CostModel`** turns that vector into a number, once, at the end, by
  `Cost.steps`.  This is the "resource currency" arrangement of [HL21]: the
  program accumulates abstract currencies and the exchange rate is applied last.

Every entry of a `CostModel` is at least one (`CostModel.one_le`).  Without that
field `fun _ => 0` would be a legal cost model under which every program is free,
and the area would ship a generator of the zero-cost non-algorithm it exists to
exclude.

## Main definitions

* `Op` — the primitive operations of the machine.
* `Cost` — a vector of operation counts.
* `CostModel` — a charge for each operation, everywhere at least one.
* `CostModel.unitCost` — the unit-cost RAM; every operation costs one.
* `Cost.steps` — the scalar cost of a `Cost` under a model.
-/

namespace Arlib.Computation



namespace Op









end Op





namespace CostVec

variable {κ : Type} [DecidableEq κ]





@[simp] theorem one_apply_self (o : κ) : one o o = 1 := by simp [one]

@[simp] theorem one_apply_of_ne {o o' : κ} (h : o' ≠ o) : one o o' = 0 := by
  simp [one, h]

@[simp] theorem many_apply_self (o : κ) (n : ℕ) : many o n o = n := by simp [many]

@[simp] theorem many_apply_of_ne {o o' : κ} (n : ℕ) (h : o' ≠ o) : many o n o' = 0 := by
  simp [many, h]















end CostVec





namespace Rate

variable {κ : Type}







end Rate

namespace CostModel





end CostModel

namespace CostVec

variable {κ : Type} [Fintype κ] [DecidableEq κ]
























end CostVec

end Arlib.Computation

end

section


/-!
# Resource bounds for the charged rational median

The insertion scan preserves sorted values and has polynomial charged cost
when its input rational encodings have a common bound.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations

/-- INTERNAL: The word-operation fold in `otherSteps` distributes over
two charged cost vectors. -/
theorem foldl_word_add (l : List Arlib.Computation.Op)
    (f g : Arlib.Computation.Op → ℕ) :
    ∀ a b, l.foldl (fun z x => z + (f x + g x)) (a + b) =
      l.foldl (fun z x => z + f x) a + l.foldl (fun z x => z + g x) b := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      intro a b
      simpa [List.foldl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (a + f x) (b + g x)

/-- INTERNAL: Nonoracle charges add when charged computations are sequenced. -/
theorem otherSteps_bind {α β : Type}
    (p : Arlib.Computation.Charged Op Cell α)
    (f : α → Arlib.Computation.Charged Op Cell β) :
    otherSteps (p >>= f) = otherSteps p + otherSteps (f p.val) := by
  simp only [otherSteps, Arlib.Computation.Charged.cost_bind, Pi.add_apply]
  have h := foldl_word_add Arlib.Computation.Op.all
    (fun x => p.cost (Op.word x)) (fun x => (f p.val).cost (Op.word x)) 0 0
  simp only [Nat.zero_add] at h
  rw [h]
  omega



/-- INTERNAL: A charged rational comparison costs at most the sum of the
operand encoding lengths. -/
theorem ratLess_otherSteps_le (a b : ℚ) :
    otherSteps (ratLess a b) ≤ binaryRatLength a + binaryRatLength b := by
  simp only [otherSteps, ratLess, Arlib.Computation.Charged.cost_opMany]
  simp [Arlib.Computation.Op.all, Arlib.Computation.CostVec.many,
    binaryRatLength, binaryNatLength]
  change a.num.natAbs.log2 + a.den.log2 + 3 +
    (b.num.natAbs.log2 + b.den.log2 + 3) ≤ _
  omega











end CountingMatroid.Analysis.ResourceBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · proved · extracted and closed the median length, sign, and charge invariants used by the estimator.
-/

end

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.LeastHalvingsCost

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations
open CountingMatroid.Analysis.ResourceBound

/-- INTERNAL: The exact encoding length of a halving accumulator.
TEXLINE: main.tex:1348-1351 -/
private theorem halfPower_binaryRatLength (i : ℕ) :
    binaryRatLength ((1 / 2 : ℚ) ^ i) = i + 4 := by
  have hn : (1 / 2 : ℚ).num = 1 := by norm_num
  have hd : (1 / 2 : ℚ).den = 2 := by norm_num
  unfold binaryRatLength binaryNatLength
  rw [Rat.num_pow, Rat.den_pow, hn, hd, Nat.log2_two_pow]
  norm_num
  have h : (1 : ℕ).log2 = 0 := by decide
  rw [h]
  omega



end CountingMatroid.Analysis.LeastHalvingsCost

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r12 · proved · bounded each halving step and summed the charged fold using
  the power-of-one-half accumulator invariant.
* r11 · partial · proved the exact rational encoding length of a halving
  accumulator; the charged fold bound still needs the state invariant and sum.
-/

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.LeastHalvingsCost

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations
open CountingMatroid.Analysis.ResourceBound

/-- INTERNAL: The capped halving search has polynomial charged work in its
input rational encoding and denominator cap. The loop's rational accumulator
is a power of one half, so its encoding grows by at most one bit per round.
TEXLINE: main.tex:1348-1351 -/
theorem solution (q : ℚ) :
    otherSteps (CountingMatroid.Program.leastHalvings q) ≤
      100 * (q.den.log2 + 8) *
        (binaryRatLength q + q.den.log2 + 16) ^ 2 + 1 := by
  have hdiv (p : ℚ) : otherSteps (ratDiv p 2) ≤ (binaryRatLength p + 4) ^ 2 := by
    simp only [otherSteps, ratDiv, Arlib.Computation.Charged.cost_opMany]
    simp [Arlib.Computation.Op.all, Arlib.Computation.CostVec.many,
      binaryRatLength, binaryNatLength]
    change (p.num.natAbs.log2 + p.den.log2 + 3 + 4) ^ 2 ≤ _
    exact Nat.pow_le_pow_left (by omega) 2
  let N := q.den.log2 + 8
  let K := binaryRatLength q + q.den.log2 + 16
  let step : (ℕ × ℚ) → ℕ → Arlib.Computation.Charged Op Cell (Option (ℕ × ℚ)) :=
    fun acc _ => do
      let needsStep ← ratLess q acc.2
      if needsStep then
        let b ← successor acc.1
        let power ← ratDiv acc.2 2
        pure (some (b, power))
      else pure none
  have hstep_val (acc : ℕ × ℚ) (i : ℕ) :
      (step acc i).val =
        if q < acc.2 then some (acc.1 + 1, acc.2 / 2) else none := by
    by_cases h : q < acc.2 <;>
      simp [step, ratLess, h, successor, ratDiv]
  have hstep_cost (b i : ℕ) (hb : b ≤ N) :
      otherSteps (step (b, (1 / 2 : ℚ) ^ b) i) ≤ 3 * K ^ 2 := by
    have hless := ratLess_otherSteps_le q ((1 / 2 : ℚ) ^ b)
    have hd := hdiv ((1 / 2 : ℚ) ^ b)
    rw [halfPower_binaryRatLength] at hless hd
    have hK : 1 ≤ K := by dsimp [K]; omega
    have hlen : binaryRatLength q + (b + 4) ≤ K := by
      dsimp [N, K] at hb ⊢
      omega
    have hdivlen : b + 8 ≤ K := by
      dsimp [N, K] at hb ⊢
      omega
    have hdivcost : otherSteps (ratDiv ((1 / 2 : ℚ) ^ b) 2) ≤ K ^ 2 :=
      hd.trans (Nat.pow_le_pow_left hdivlen 2)
    have hlesscost : otherSteps (ratLess q ((1 / 2 : ℚ) ^ b)) ≤ K :=
      hless.trans hlen
    by_cases h : q < (1 / 2 : ℚ) ^ b
    · have heq : otherSteps (step (b, (1 / 2 : ℚ) ^ b) i) =
          otherSteps (ratLess q ((1 / 2 : ℚ) ^ b)) + 1 +
            otherSteps (ratDiv ((1 / 2 : ℚ) ^ b) 2) := by
        simp only [step, otherSteps_bind, ratLess, h]
        simp [otherSteps, successor, ratDiv, Arlib.Computation.Op.all,
          Arlib.Computation.CostVec.many]
        omega
      rw [heq]
      nlinarith
    · have heq : otherSteps (step (b, (1 / 2 : ℚ) ^ b) i) =
          otherSteps (ratLess q ((1 / 2 : ℚ) ^ b)) := by
        simp only [step, otherSteps_bind, ratLess, h]
        simp [otherSteps, Arlib.Computation.Op.all]
      rw [heq]
      nlinarith
  have hfoldcost {β ι : Type}
      (f : β → ι → Arlib.Computation.Charged Op Cell (Option β))
      (i : ι) (l : List ι) (b : β) :
      otherSteps (Arlib.Computation.Charged.foldlWhile f (i :: l) b) =
        otherSteps (f b i) +
          match (f b i).val with
          | none => 0
          | some b' => otherSteps (Arlib.Computation.Charged.foldlWhile f l b') := by
    cases h : (f b i).val with
    | none =>
        have hv := h
        simp only [Arlib.Computation.Charged.val] at hv
        simp only [Arlib.Computation.Charged.foldlWhile, hv, otherSteps,
          Arlib.Computation.Charged.cost]
        omega
    | some b' =>
        have hv := h
        simp only [Arlib.Computation.Charged.val] at hv
        simp only [Arlib.Computation.Charged.foldlWhile, hv, otherSteps,
          Arlib.Computation.Charged.cost, Pi.add_apply]
        have hadd := foldl_word_add Arlib.Computation.Op.all
          (fun x => (f b i).cost (Op.word x))
          (fun x => (Arlib.Computation.Charged.foldlWhile f l b').cost (Op.word x)) 0 0
        simp only [Nat.zero_add] at hadd
        simp only [Arlib.Computation.Charged.cost] at hadd
        rw [hadd]
        omega
  have hloop : ∀ (l : List ℕ) (b : ℕ), b + l.length ≤ N →
      otherSteps (Arlib.Computation.Charged.foldlWhile
        (fun acc i => step acc i) l (b, (1 / 2 : ℚ) ^ b)) ≤
        l.length * (3 * K ^ 2) := by
    intro l
    induction l with
    | nil =>
        intro b hb
        simp [otherSteps, Arlib.Computation.Charged.foldlWhile,
          Arlib.Computation.Charged.cost, Arlib.Computation.Op.all]
    | cons i l ih =>
        intro b hb
        have hfirst := hstep_cost b i (by simp [N] at hb ⊢; omega)
        by_cases h : q < (1 / 2 : ℚ) ^ b
        · have hs : (step (b, (1 / 2 : ℚ) ^ b) i).val =
              some (b + 1, (1 / 2 : ℚ) ^ (b + 1)) := by
            rw [hstep_val (b, (1 / 2 : ℚ) ^ b) i, if_pos h]
            rw [pow_succ]
            simp [div_eq_mul_inv]
          have htail := ih (b + 1) (by simp only [List.length_cons] at hb; omega)
          rw [hfoldcost, hs]
          simp only [List.length_cons]
          rw [show (l.length + 1) * (3 * K ^ 2) =
            3 * K ^ 2 + l.length * (3 * K ^ 2) by ring]
          omega
        · have hs : (step (b, (1 / 2 : ℚ) ^ b) i).val = none := by
            rw [hstep_val (b, (1 / 2 : ℚ) ^ b) i, if_neg h]
          rw [hfoldcost, hs]
          simp only [List.length_cons]
          rw [show (l.length + 1) * (3 * K ^ 2) =
            3 * K ^ 2 + l.length * (3 * K ^ 2) by ring]
          omega
  have hrun := hloop (List.range N) 0 (by simp [N])
  have hcap : otherSteps (binaryLoopBound q.den) = 1 := by
    simp [binaryLoopBound, otherSteps, Arlib.Computation.Op.all]
  have hpure (n : ℕ) :
      otherSteps (pure n : Arlib.Computation.Charged Op Cell ℕ) = 0 := by
    simp [otherSteps, Arlib.Computation.Op.all]
  unfold CountingMatroid.Program.leastHalvings
  simp only [otherSteps_bind, Arlib.Computation.Charged.repeatWhile]
  rw [hcap]
  simp only [hpure, Nat.add_zero]
  simp only [binaryLoopBound, Arlib.Computation.Charged.val_op]
  change 1 + otherSteps (Arlib.Computation.Charged.foldlWhile
    (fun acc i => step acc i) (List.range N) (0, (1 : ℚ))) ≤
      100 * N * K ^ 2 + 1
  have hrun' : otherSteps (Arlib.Computation.Charged.foldlWhile
      (fun acc i => step acc i) (List.range N) (0, (1 : ℚ))) ≤
      N * (3 * K ^ 2) := by
    simpa only [List.length_range, pow_zero] using hrun
  have hpoly : N * (3 * K ^ 2) ≤ 100 * N * K ^ 2 := by
    calc
      N * (3 * K ^ 2) = 3 * (N * K ^ 2) := by ring
      _ ≤ 100 * (N * K ^ 2) := Nat.mul_le_mul_right _ (by decide)
      _ = 100 * N * K ^ 2 := by ring
  omega
