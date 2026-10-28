-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedRunResourceEnvelope.boundedRun_resource_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:40:40.072257+00:00
-- url     : https://prove2.me/submissions/ca03ed6b-1491-41b2-9e9e-63d8d39dfa3b

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
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
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
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunOracleCalls_boundedRun_oracleCalls_envelope
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunOtherSteps_boundedRun_otherSteps_envelope
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_boundedRun_value_nonneg
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_boundedRun_zero_phases_otherSteps
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_finishPhase_ratio_length_le
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_observePhase_counts_le
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_observePhase_height_le
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_observePhase_numerator_nonneg
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_binaryRatLength_mul_le

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
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

















@[simp] theorem many_zero (o : κ) : many o 0 = 0 := by funext o'; simp [many]









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

namespace CountingMatroid.Analysis.RationalHeight
open CountingMatroid.Model





/-- INTERNAL: Two component lengths bound the rational encoding length. -/
theorem binaryRatLength_le_height (q : ℚ) :
    binaryRatLength q ≤ 2 * rationalHeight q + 2 := by
  unfold rationalHeight binaryRatLength binaryNatLength
  omega




end CountingMatroid.Analysis.RationalHeight

end

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.RationalHeight





/-- INTERNAL: A charged finite loop preserves a counter bound that grows by one
per iteration. -/
theorem chargedFold_count_growth {ι β : Type} (P : β → ℕ → Prop)
    (f : β → ι → Arlib.Computation.Charged Op Cell β)
    (hf : ∀ b i k, P b k → P (f b i).val (k + 1))
    (l : List ι) (b : β) (k : ℕ) (hb : P b k) :
    P (Arlib.Computation.Charged.foldl f l b).val (k + l.length) := by
  induction l generalizing b k with
  | nil => simpa using hb
  | cons i xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (f b i).val (k + 1) (hf b i k hb)



















end CountingMatroid.Analysis.BoundedRunResourceEnvelope

end

section


/-!
Polynomial output encoding length is proved for every schedule and execution,
using additive observation heights and a phase-product invariant. Nonnegativity
and the zero-phase costs are also proved here. The complete resource envelope
uses separate oracle-call and nonoracle-work obligations; those dependencies
must be closed before the envelope has a complete proof.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The charged natural-power fold computes exponentiation. -/
private theorem natPower_fold_value (base : ℕ) (l : List ℕ) (acc : ℕ) :
    (Arlib.Computation.Charged.foldl (fun acc _ => natMul acc base) l acc).val =
      acc * base ^ l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons _ xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons, ih]
      simp [natMul, pow_succ]
      ring

/-- INTERNAL: The charged natural power loop computes exponentiation. -/
theorem natPower_value (base exponent : ℕ) :
    (CountingMatroid.Program.natPower base exponent).val = base ^ exponent := by
  unfold CountingMatroid.Program.natPower Arlib.Computation.Charged.repeatFor
  simpa using natPower_fold_value base (List.range exponent) 1











/-- INTERNAL: With no annealing phases the run returns the initial scale.
TEXLINE: main.tex:1430-1440 -/
theorem boundedRun_zero_phases_value (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (hL : s.L = 0) :
    (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0).val.1 = (2 ^ n : ℚ) := by
  simp [CountingMatroid.Program.boundedRun, hL, natPower_value,
    ratMul, ratOfNat,
    Arlib.Computation.Charged.repeatFor]

/-- INTERNAL: An integer-power loop spends no independence-oracle calls. -/
private theorem natPower_oracle_cost_zero (base : ℕ) (l : List ℕ) (acc : ℕ)
    (op : Op) (hop : op ≠ Op.word .mul) :
    (Arlib.Computation.Charged.foldl (fun acc _ => natMul acc base) l acc).cost op = 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons _ xs ih =>
      rw [Arlib.Computation.Charged.cost_foldl_cons]
      change (natMul acc base).cost op +
        (Arlib.Computation.Charged.foldl (fun acc _ => natMul acc base) xs
          (natMul acc base).val).cost op = 0
      rw [ih]
      simp [natMul, Arlib.Computation.CostVec.one, hop]

/-- INTERNAL: The zero-phase run makes no independence-oracle calls.
TEXLINE: main.tex:1430-1440 -/
theorem boundedRun_zero_phases_oracleCalls (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (hL : s.L = 0) :
    oracleCalls (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0) = 0 := by
  simp [CountingMatroid.Program.boundedRun, hL,
    CountingMatroid.Program.natPower, Arlib.Computation.Charged.repeatFor,
    oracleCalls, initialWeights, allocateLearnedWeights, ratOfNat, ratMul, natMul,
    Arlib.Computation.CostVec.many]
  constructor
  · exact natPower_oracle_cost_zero 2 (List.range n) 1 Op.oracleFirst (by decide)
  · exact natPower_oracle_cost_zero 2 (List.range n) 1 Op.oracleSecond (by decide)





/-- INTERNAL: The exact initial scale has linear binary length. -/
private theorem binaryRatLength_two_pow (n : ℕ) :
    binaryRatLength (2 ^ n : ℚ) = n + 4 := by
  simp [binaryRatLength, binaryNatLength, Nat.log2_two_pow]
  have h : Nat.log2 1 = 0 := by decide
  simp [h]
  omega




open CountingMatroid.Analysis.RationalHeight





end CountingMatroid.Analysis.BoundedRunResourceEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r16 · handoff blocked · the child-ready shell command was rejected because it used rm -f to remove the old response; no handoff was submitted and BoundedRunOtherSteps remains owned here.
* r16 · partial recovery · proved the all-phase output-length conjunct via rational height and phase-product induction; isolated nonoracle work in BoundedRunOtherSteps for live handoff.
* r15 · decomposed · separated the state-independent oracle charge into BoundedRunOracleCalls; output size and nonoracle charge still need a reachable-state invariant.
* r14 · partial recovery · proved observation type-count and phase-power charge bounds; the positive-phase rational-size and abort-path invariant remains open.
* r13 · partial recovery · proved phase-power binary length and a quadratic charge bound for rational multiplication; the reachable phase-state and abort-path cost invariant is still missing.
* r12 · open · verified that rational multiplication has unbounded charge on arbitrary input (`otherSteps (ratMul (2 ^ K : ℚ) 1) ≥ K`); a reachable-state invariant must also bound observation counts by the loop length.
* r11 · open · direct simplification exposed the entire positive-phase fold; the generic charged loop bound requires a price for arbitrary cursors, while rational-operation costs are unbounded without a reachable-state length invariant.
* r10 · open · audited arbitrary schedule fields and expanded the positive-phase goal; Arlib's fold cost bound needs a state-length invariant for the stored multiplier tables and phase accumulators, which is still absent.
* r9 · partial recovery · proved nonnegativity of every successful observation accumulator, completed phase ratio, and bounded-run output; the three positive-phase quantitative bounds still need a joint phase-state invariant.
* r8 · partial recovery · proved the zero-phase oracle and quadratic work bounds and integrated the entire zero-phase case into the envelope; the positive-phase joint invariant remains open.
* r7 · partial recovery · proved the charged natural-power value and isolated the zero-phase output; the positive-phase state-and-cost invariant remains open.
* r6 · open · isolated the capped-run phase invariant from schedule construction and amplification.
-/

end
/-!
Polynomial output encoding length is proved for every schedule and execution,
using additive observation heights and a phase-product invariant. Nonnegativity
and the zero-phase costs are also proved here. The complete resource envelope
uses separate oracle-call and nonoracle-work obligations; those dependencies
must be closed before the envelope has a complete proof.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines






























open CountingMatroid.Analysis.RationalHeight

/-- INTERNAL: The capped run has a resource bound expressed only in the
schedule fields that its code reads. This separates the phase-state invariant
from the arithmetic used to construct the schedule and amplify the answer.
TEXLINE: main.tex:1350-1440 -/
theorem solution :
    ∃ (C degree : ℕ), ∀ (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
      (tape : ℕ → Bool) (s : AnnealingSchedule),
      0 ≤ s.ρ →
      let size := n + s.L + s.τ + s.restartCap + s.observations +
        s.drawTrials + binaryRatLength s.ρ + 1
      let run := CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0
      0 ≤ run.val.1 ∧
      binaryRatLength run.val.1 ≤ C * size ^ degree ∧
      oracleCalls run ≤ C * size ^ degree ∧
      otherSteps run ≤ C * size ^ degree := by
  refine ⟨100, 100, ?_⟩
  intro n r o₁ o₂ tape s hρ
  dsimp only
  by_cases hL : s.L = 0
  · let size := n + s.L + s.τ + s.restartCap + s.observations +
      s.drawTrials + binaryRatLength s.ρ + 1
    have hsize : n + 1 ≤ size := by dsimp [size]; omega
    have hquad : 100 * (n + 1) ^ 2 ≤ 100 * size ^ 100 := by
      have hpow : (n + 1) ^ 2 ≤ size ^ 2 := Nat.pow_le_pow_left hsize 2
      have hstep : size ^ 2 ≤ size ^ 100 := Nat.pow_le_pow_right (by omega) (by omega)
      exact Nat.mul_le_mul_left 100 (hpow.trans hstep)
    rw [boundedRun_zero_phases_value n r o₁ o₂ tape s hL]
    constructor
    · positivity
    constructor
    · rw [binaryRatLength_two_pow]
      calc
        n + 4 ≤ 100 * (n + 1) ^ 2 := by nlinarith only
        _ ≤ 100 * size ^ 100 := hquad
    constructor
    · rw [boundedRun_zero_phases_oracleCalls n r o₁ o₂ tape s hL]
      exact Nat.zero_le _
    · exact (boundedRun_zero_phases_otherSteps n r o₁ o₂ tape s hL).trans hquad
  · -- The value bound is independent of stored multiplier sizes. Charges on
    -- unsuccessful paths are handled by the separate nonoracle-work obligation.
    refine ⟨boundedRun_value_nonneg n r o₁ o₂ tape s hρ, ?_, ?_, ?_⟩
    · let K := 2 * (1 + s.observations *
          (binaryRatLength 1 + n * binaryRatLength s.ρ + 1)) + 2 +
          3 * (s.observations + 4)
      have hout : binaryRatLength
          (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0).val.1 ≤
          (n + 4) + (4 + s.L * K) := by
        let P : Option (CountingMatroid.Program.AnnealingCursor n) → ℕ → Prop :=
          fun acc k => ∀ current, acc = some current → binaryRatLength current.product ≤ 4 + k * K
        let f : ℕ → Option (CountingMatroid.Program.AnnealingCursor n) →
            Arlib.Computation.Charged Op Cell
              (Option (CountingMatroid.Program.AnnealingCursor n)) :=
          fun j acc =>
            match acc with
            | none => pure none
            | some current => do
                let q ← CountingMatroid.Program.ratPower s.ρ j
                let started ← CountingMatroid.Program.restartPhase r o₁ o₂ tape s
                  current.tables j current.bitCursor
                match started with
                | none => pure none
                | some started =>
                    let observed ← CountingMatroid.Program.observePhase r o₁ o₂ tape s q
                      current.currentWeights started
                    match observed with
                    | none => pure none
                    | some observed =>
                        let finished ← CountingMatroid.Program.finishPhase s j
                          current.currentWeights observed
                        match finished with
                        | none => pure none
                        | some (ratio, nextWeights) =>
                            let product ← ratMul current.product ratio
                            let next ← successor j
                            let update ← lessThan next s.L
                            if update then
                              let tables ← learnedWeightWrite current.tables next s.L nextWeights
                              pure (some ⟨tables, nextWeights, product, observed.bitCursor⟩)
                            else pure (some ⟨current.tables, nextWeights, product,
                              observed.bitCursor⟩)
        have hstep : ∀ acc j k, P acc k → P (f j acc).val (k + 1) := by
          intro acc j k hacc next hnext
          cases acc with
          | none => simp [f] at hnext
          | some current =>
              dsimp [f] at hnext
              cases hstarted : (CountingMatroid.Program.restartPhase r o₁ o₂ tape s
                current.tables j current.bitCursor).val with
              | none => simp [hstarted] at hnext
              | some started =>
                  simp only [hstarted, Arlib.Computation.Charged.val_bind] at hnext
                  cases hobserved : (CountingMatroid.Program.observePhase r o₁ o₂ tape s
                    (CountingMatroid.Program.ratPower s.ρ j).val current.currentWeights
                    started).val with
                  | none => simp [hobserved] at hnext
                  | some observed =>
                      simp only [hobserved, Arlib.Computation.Charged.val_bind] at hnext
                      cases hfinished : (CountingMatroid.Program.finishPhase s j
                        current.currentWeights observed).val with
                      | none => simp [hfinished] at hnext
                      | some result =>
                          rcases result with ⟨ratio, nextWeights⟩
                          simp only [hfinished, Arlib.Computation.Charged.val_bind,
                            ratMul, Arlib.Computation.Charged.val_opMany] at hnext
                          have hobs := observePhase_height_le r o₁ o₂ tape s
                            (CountingMatroid.Program.ratPower s.ρ j).val
                            current.currentWeights started observed hobserved
                          have hcounts := observePhase_counts_le r o₁ o₂ tape s
                            (CountingMatroid.Program.ratPower s.ρ j).val
                            current.currentWeights started observed hobserved
                          have hratio := finishPhase_ratio_length_le s j current.currentWeights
                            observed (hcounts .transversal) ratio nextWeights hfinished
                          have hl := binaryRatLength_le_height observed.numeratorSum
                          have hr : binaryRatLength ratio ≤ K := by dsimp [K]; omega
                          have hm := ScheduleOtherStepsEnvelope.binaryRatLength_mul_le
                            current.product ratio
                          have hc := hacc current rfl
                          split at hnext
                          · simp only [Arlib.Computation.Charged.val_bind,
                              Arlib.Computation.Charged.val_pure,
                              learnedWeightWrite, Arlib.Computation.Charged.val_opMany] at hnext
                            cases Option.some.inj hnext
                            dsimp at *
                            nlinarith
                          · simp only [Arlib.Computation.Charged.val_pure] at hnext
                            cases Option.some.inj hnext
                            dsimp at *
                            nlinarith
        unfold CountingMatroid.Program.boundedRun
        simp only [Arlib.Computation.Charged.val_bind]
        unfold Arlib.Computation.Charged.repeatFor
        have hinit : P (some ⟨(allocateLearnedWeights n s.L (initialWeights n).val).val,
            (initialWeights n).val, 1, 0⟩) 0 := by
          intro current hc
          cases Option.some.inj hc
          norm_num [binaryRatLength, binaryNatLength, Nat.log2_eq_log_two]
        have hphases := chargedFold_count_growth P (fun acc j => f j acc) hstep
          (List.range s.L) _ 0 hinit
        split
        · norm_num [binaryRatLength, binaryNatLength, Nat.log2_eq_log_two]
          omega
        · simp only [Arlib.Computation.Charged.val_bind, natPower_value,
            ratOfNat, ratMul, Arlib.Computation.Charged.val_opMany]
          rename_i result hresult
          have hp := hphases result hresult
          simp only [List.length_range, Nat.zero_add] at hp
          have hm := ScheduleOtherStepsEnvelope.binaryRatLength_mul_le (2 ^ n : ℚ) result.product
          rw [binaryRatLength_two_pow] at hm
          simpa using hm.trans (Nat.add_le_add_left hp _)
      let size := n + s.L + s.τ + s.restartCap + s.observations +
        s.drawTrials + binaryRatLength s.ρ + 1
      have hn : n ≤ size := by dsimp [size]; omega
      have hLsize : s.L ≤ size := by dsimp [size]; omega
      have hN : s.observations ≤ size := by dsimp [size]; omega
      have hR : binaryRatLength s.ρ ≤ size := by dsimp [size]; omega
      have hs : 1 ≤ size := by dsimp [size]; omega
      have hcube : size ≤ size ^ 3 := by
        simpa using Nat.pow_le_pow_right hs (show 1 ≤ 3 by decide)
      have hK : K ≤ 31 * size ^ 3 := by
        have h1 : binaryRatLength (1 : ℚ) = 4 := by decide
        dsimp [K]
        rw [h1]
        calc
          2 * (1 + s.observations * (4 + n * binaryRatLength s.ρ + 1)) + 2 +
              3 * (s.observations + 4) ≤
              2 * (1 + size * (4 + size * size + 1)) + 2 + 3 * (size + 4) := by
                gcongr
          _ ≤ 31 * size ^ 3 := by nlinarith
      have hfour : size ≤ size ^ 4 := by
        simpa using Nat.pow_le_pow_right hs (show 1 ≤ 4 by decide)
      calc
        binaryRatLength (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0).val.1 ≤
            (n + 4) + (4 + s.L * K) := hout
        _ ≤ (size + 4) + (4 + size * (31 * size ^ 3)) := by gcongr
        _ ≤ 100 * size ^ 4 := by nlinarith only [hfour, hs]
        _ ≤ 100 * size ^ 100 := Nat.mul_le_mul_left 100
          (Nat.pow_le_pow_right hs (by decide))
    · exact BoundedRunOracleCalls.boundedRun_oracleCalls_envelope
        n r o₁ o₂ tape s
    · exact BoundedRunOtherSteps.boundedRun_otherSteps_envelope
        n r o₁ o₂ tape s hρ
