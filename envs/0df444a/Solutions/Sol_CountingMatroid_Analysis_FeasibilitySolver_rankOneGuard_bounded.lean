-- Prove2me | solution 1 for CountingMatroid.Analysis.FeasibilitySolver.rankOneGuard_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:08:50.232566+00:00
-- url     : https://prove2.me/submissions/b87a3094-90af-4e36-a1a7-3a6198a1e041

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
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_ExchangePathCertificate
import Definitions.Def_CountingMatroid_Analysis_ExchangeWalkReversal
import Definitions.Def_CountingMatroid_Analysis_FeasibilitySolver
import Definitions.Def_CountingMatroid_Analysis_IntersectionSearch
import Definitions.Def_CountingMatroid_Analysis_RankOneFeasibility
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Subroutines
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_RankOneFeasibility_singletonScan_costs

namespace CountingMatroid.Analysis.IntersectionSearchCost
end CountingMatroid.Analysis.IntersectionSearchCost
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.IntersectionAugmentation
end CountingMatroid.Analysis.IntersectionAugmentation
namespace CountingMatroid.Analysis.FoundPathAugmentation
end CountingMatroid.Analysis.FoundPathAugmentation
namespace CountingMatroid.Analysis.ShortestExchangeAugmentation
end CountingMatroid.Analysis.ShortestExchangeAugmentation
namespace CountingMatroid.Analysis.ShortestSourceWalkIndependence
end CountingMatroid.Analysis.ShortestSourceWalkIndependence
namespace CountingMatroid.Analysis.ExchangeWalkCardinality
end CountingMatroid.Analysis.ExchangeWalkCardinality
namespace CountingMatroid.Analysis.FindPathCertificate
end CountingMatroid.Analysis.FindPathCertificate
namespace CountingMatroid.Analysis.FrozenPathTable
end CountingMatroid.Analysis.FrozenPathTable
namespace CountingMatroid.Analysis.NoPathSeparator
end CountingMatroid.Analysis.NoPathSeparator
namespace CountingMatroid.Analysis.ExchangeClosedBasis
end CountingMatroid.Analysis.ExchangeClosedBasis
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


set_option autoImplicit false

/-!
The common-base predicate is connected to the paper's feasibility pretest.
Ranks zero and one are implemented and verified using the charged interface;
the rank-one implementation is the first augmentation from the empty set.
An explicit capped exchange-graph implementation handles arbitrary rank.
Its uniform cost certificate is proved. The parent now reduces correctness to
the augmentation-progress obligation in a separate child file, which remains
open. The parent proof has no open tactic goals but depends on that obligation.
-/

namespace CountingMatroid.Analysis.FeasibilitySolver

open CountingMatroid.Model.Subroutines
open CountingMatroid.Model
open scoped Classical

















/-- INTERNAL: The rank-one guard adds no oracle calls beyond the selected
scan or fallback implementation. -/
theorem rankOneGuard_oracleCalls (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) :
    oracleCalls ((rankOneGuard solver).run n r o₁ o₂) =
      if r = 1 then oracleCalls (RankOneFeasibility.singletonScan o₁ o₂)
      else oracleCalls (solver.run n r o₁ o₂) := by
  by_cases hr : r = 1 <;>
    simp [rankOneGuard, Operations.natEqual, oracleCalls, hr]

/-- INTERNAL: The rank-one guard adds one charged comparison to either branch. -/
theorem rankOneGuard_otherSteps (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) :
    otherSteps ((rankOneGuard solver).run n r o₁ o₂) =
      1 + if r = 1 then otherSteps (RankOneFeasibility.singletonScan o₁ o₂)
      else otherSteps (solver.run n r o₁ o₂) := by
  by_cases hr : r = 1 <;>
    simp [rankOneGuard, Operations.natEqual, otherSteps, hr,
      Arlib.Computation.Op.all, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]







end CountingMatroid.Analysis.FeasibilitySolver

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r17 · partial · proved the complementary-basis cardinality separator used by augmentation_progress; isolated the remaining no-path obligations as basis certificates for the computed reachable set. The single-child handoff was also mechanically rejected; all new files remain owned locally.

* r16 · partial · proved the explicit solver's unconditional polynomial resource certificate after the two-child handoff was mechanically rejected. Only augmentation_progress remains open; parent cardinality induction and contract assembly elaborate against that obligation.

* r15 · decomposed · constructed a charged capped exchange-graph/BFS implementation and reduced the parent to its independent augmentation-progress and uniform-cost certificates. Proved exact query/table specifications and the parent cardinality induction; the two child certificates remain open pending live handoff.

* r14 · partial · implemented and verified the first augmentation from the empty set as a charged singleton scan; proved exact correctness and unconditional costs, and wired its rank-one guard and polynomial bounds into the parent. The remaining witness requires correctness only for 1 < r; no new open helper or transferred proof debt.
* r13 · partial · implemented the charged rank-zero guard; proved its value, zero additional oracle cost, and one-comparison overhead. The parent now handles rank zero and absorbs the guard cost into its polynomial coefficient. The positive-rank intersection implementation and its uniform bounds remain open; no new unproved declarations.
* r12 · open · library-first search again found no deterministic two-oracle intersection solver with polynomial charged bounds; checked augmentation and direct-sum independence statements. Preserved the existing bridge and target, and proposed the explicitly cited Schrijver dependency for Prior review; no new proof debt introduced.
* r11 · open · searched pinned Mathlib and Arlib for common independent sets, intersection algorithms, augmenting paths, and submodular minimization; no matching solver was found. Checked the single-matroid augmentation signatures and the unconditional cost quantifiers; the existing charged implementation dependency remains unresolved.
* r10 · recovery · isolated the missing charged augmenting-path implementation and its two cost proofs; a mathematical decider or a prior theorem alone cannot instantiate this contract without charged code.
* r9 · open · searched pinned Mathlib and Arlib for a two-oracle intersection algorithm or submodular minimization route; only single-matroid augmentation is present. The remaining goal is the cited solver's charged implementation and both uniform polynomial bounds.
* r8 · open · rechecked the entire pinned Mathlib and Arlib sources by matroid-intersection, common-independent-set, and augmenting-path statements; no executable two-oracle solver or cost certificate matches `FeasibilityContract`. The Schrijver citation remains the missing borrowed dependency.
* r7 · open · searched the pinned Mathlib matroid sources and all Arlib Lean sources by matroid-intersection and augmentation statement shape; no two-oracle implementation or polynomial charged certificate exists. The cited Schrijver theorem supplies an external algorithmic result, but the custom charged realization remains a local obligation.
* r6 · open · rechecked the contract shape and pinned Matroid/Computation sources; Mathlib has single-matroid augmentation but no executable matroid-intersection pretest or polynomial charged cost certificate. The Schrijver result remains a Prior proposal.
* r5 · open · searched pinned Mathlib and Arlib for matroid-intersection code; none supplies a charged polynomial pretest, while exhaustive candidate enumeration has exponential oracle cost.
* r4 · decomposed · proved the common-base/size-r-independent bridge and narrowed the remaining executable solver obligation to the predicate in Schrijver's cited pretest.
* r3 · open · recovery identified the irreducible boundary as executable charged code plus correctness and two uniform cost bounds; no smaller cited library theorem supplies it.
* r2 · open · checked the contract, its project uses, and pinned Matroid/Computation sources; no executable polynomial matroid-intersection result supplies this contract.
* r1 · open · library search found no charged matroid-intersection implementation; the cited polynomial pretest still needs code and a cost proof.
-/

end
set_option autoImplicit false

/-!
The common-base predicate is connected to the paper's feasibility pretest.
Ranks zero and one are implemented and verified using the charged interface;
the rank-one implementation is the first augmentation from the empty set.
An explicit capped exchange-graph implementation handles arbitrary rank.
Its uniform cost certificate is proved. The parent now reduces correctness to
the augmentation-progress obligation in a separate child file, which remains
open. The parent proof has no open tactic goals but depends on that obligation.
-/

namespace CountingMatroid.Analysis.FeasibilitySolver
end CountingMatroid.Analysis.FeasibilitySolver
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FeasibilitySolver

open CountingMatroid.Model.Subroutines
open CountingMatroid.Model
open scoped Classical

/-- INTERNAL: Absorb the singleton scan and its guard into uniform polynomial
coefficients. The bound holds for arbitrary oracle functions, so the guard
introduces no promise-dependent resource assumption. -/
theorem solution (solver : FeasibilityImplementation)
    (callConstant callDegree bitConstant bitDegree : ℕ)
    (hbounded : FeasibilityBounded solver callConstant callDegree bitConstant bitDegree) :
    FeasibilityBounded (rankOneGuard solver)
      (callConstant + 2) (callDegree + 3) (bitConstant + 5) (bitDegree + 3) := by
  intro n r o₁ o₂
  rw [rankOneGuard_oracleCalls, rankOneGuard_otherSteps]
  have hsize : 1 ≤ n + r + 1 := by omega
  have hcallPow : (n + r + 1) ^ callDegree ≤ (n + r + 1) ^ (callDegree + 3) :=
    pow_le_pow_right₀ hsize (by omega)
  have hbitPow : (n + r + 1) ^ bitDegree ≤ (n + r + 1) ^ (bitDegree + 3) :=
    pow_le_pow_right₀ hsize (by omega)
  have hcallCube : (n + r + 1) ^ 3 ≤ (n + r + 1) ^ (callDegree + 3) :=
    pow_le_pow_right₀ hsize (by omega)
  have hbitCube : (n + r + 1) ^ 3 ≤ (n + r + 1) ^ (bitDegree + 3) :=
    pow_le_pow_right₀ hsize (by omega)
  have hlinear : n ≤ (n + r + 1) ^ 3 := by
    calc
      n ≤ n + r + 1 := by omega
      _ ≤ (n + r + 1) ^ 3 := by
        simpa only [pow_one] using
          (pow_le_pow_right₀ hsize (by decide : 1 ≤ 3))
  have hwork : n * (n * (n + 1) + 3) ≤ 4 * (n + r + 1) ^ 3 := by
    have hproduct : n * (n * (n + 1)) ≤
        (n + r + 1) * ((n + r + 1) * (n + r + 1)) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
    nlinarith
  have hunit : 1 ≤ (n + r + 1) ^ (bitDegree + 3) := one_le_pow₀ hsize
  obtain ⟨hc, hb⟩ := hbounded n r o₁ o₂
  have hc' := hc.trans (Nat.mul_le_mul_left callConstant hcallPow)
  have hb' := hb.trans (Nat.mul_le_mul_left bitConstant hbitPow)
  by_cases hr : r = 1
  · simp only [if_pos hr]
    rw [(RankOneFeasibility.singletonScan_costs o₁ o₂).1,
      (RankOneFeasibility.singletonScan_costs o₁ o₂).2]
    constructor <;> nlinarith
  · simp only [if_neg hr]
    constructor <;> nlinarith
