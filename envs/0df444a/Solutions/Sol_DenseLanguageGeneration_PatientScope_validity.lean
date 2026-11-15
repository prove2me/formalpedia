-- Prove2me | solution 1 for DenseLanguageGeneration.PatientScope.validity
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:25:12.291606+00:00
-- url     : https://prove2.me/submissions/c6c48d05-71de-4ba7-adbb-aaf3b4b560d7

import Definitions.Def_DenseLanguageGeneration_PatientScope_criticalChain
import Definitions.Def_DenseLanguageGeneration_PatientScope_density
import Mathlib.Algebra.Order.Archimedean.IndicatorCard
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.LiminfLimsup

/- Proofs for STOC submission 335. Includes GenLimitLib at commit
c828be22ac30d37a8767ed74ec49c66e0afd54f4, https://github.com/pengzhang91/generation-in-the-limit-lib
Adapted to Lean 4.33.1 and combined for single-file verification.
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

-- GenLimit.Core.Basic
section
set_option autoImplicit true

/-!
# Language generation in the limit: basic definitions

This file fixes a countable universe `ℕ` and an indexed family of languages.
The family is indexed, rather than represented as a set of sets, because the
Kleinberg--Mullainathan algorithm depends on the enumeration order and permits
repeated languages.
-/

namespace GenLimit

/- AUDIT NOTE: These original definitions fix the universe as `ℕ`, following
the enumeration used in Section 5. The paper-facing transport to an arbitrary
countable universe is provided in
`GenLimit.Paper01_LanguageGeneration.Transport`. -/
/-- A language over the countable universe `ℕ`. -/
abbrev Language := Set ℕ

/-- An indexed family of languages. Repeated languages are permitted. -/
abbrev LanguageFamily := ℕ → Language

/-- A stream is an exact presentation of `L` when its range is exactly `L`. -/
def Presents (stream : ℕ → ℕ) (L : Language) : Prop :=
  Set.range stream = L

/-- The set of observations strictly before time `t`. -/
def sample (stream : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range t).image stream

/-- Candidate `i` is consistent with all observations strictly before `t`. -/
def Consistent (C : LanguageFamily) (stream : ℕ → ℕ) (t i : ℕ) : Prop :=
  ↑(sample stream t) ⊆ C i

/-- A Boolean membership oracle, uniform in the language index and element. -/
structure MembershipOracle (C : LanguageFamily) where
  query : ℕ → ℕ → Bool
  query_spec : query i u = true ↔ u ∈ C i

theorem mem_sample_iff {stream : ℕ → ℕ} {t u : ℕ} :
    u ∈ sample stream t ↔ ∃ s < t, stream s = u := by
  simp [sample]

/-- Samples depend only on the corresponding finite stream prefix. -/
theorem sample_eq_of_eq_on_prefix
    {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    sample stream₁ t = sample stream₂ t := by
  ext x
  simp only [mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

theorem sample_mono {stream : ℕ → ℕ} {s t : ℕ} (hst : s ≤ t) :
    sample stream s ⊆ sample stream t := by
  intro u hu
  rw [mem_sample_iff] at hu ⊢
  obtain ⟨r, hrs, hru⟩ := hu
  exact ⟨r, lt_of_lt_of_le hrs hst, hru⟩

theorem value_mem_sample {stream : ℕ → ℕ} {s t : ℕ} (hst : s < t) :
    stream s ∈ sample stream t := by
  rw [mem_sample_iff]
  exact ⟨s, hst, rfl⟩

theorem mem_language_of_mem_sample_of_presents
    {stream : ℕ → ℕ} {L : Language} (hP : Presents stream L)
    {t u : ℕ} (hu : u ∈ sample stream t) : u ∈ L := by
  rw [← hP]
  rw [mem_sample_iff] at hu
  obtain ⟨s, -, rfl⟩ := hu
  exact ⟨s, rfl⟩

/-- Any candidate containing the presented target is consistent at every
time. -/
theorem consistent_of_target_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {z i t : ℕ}
    (hP : Presents stream (C z)) (hsub : C z ⊆ C i) :
    Consistent C stream t i := by
  intro u hu
  exact hsub (mem_language_of_mem_sample_of_presents hP hu)

theorem eventually_mem_sample_of_presents
    {stream : ℕ → ℕ} {L : Language} (hP : Presents stream L)
    {u : ℕ} (hu : u ∈ L) : ∃ T, ∀ t, T ≤ t → u ∈ sample stream t := by
  rw [← hP] at hu
  obtain ⟨s, rfl⟩ := hu
  refine ⟨s + 1, ?_⟩
  intro t ht
  rw [mem_sample_iff]
  exact ⟨s, lt_of_lt_of_le (Nat.lt_succ_self s) ht, rfl⟩

theorem presents_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {z t : ℕ}
    (hP : Presents stream (C z)) : Consistent C stream t z := by
  exact consistent_of_target_subset hP Set.Subset.rfl

theorem eventually_not_consistent_of_not_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {z i : ℕ}
    (hP : Presents stream (C z)) (hbad : ¬ C z ⊆ C i) :
    ∃ T, ∀ t, T ≤ t → ¬ Consistent C stream t i := by
  obtain ⟨u, huz, hui⟩ := Set.not_subset.mp hbad
  obtain ⟨T, hT⟩ := eventually_mem_sample_of_presents hP huz
  refine ⟨T, ?_⟩
  intro t ht hcon
  exact hui (hcon (hT t ht))

end GenLimit

end

-- GenLimit.Core.TargetStability
section
set_option autoImplicit true

/-!
# Eventual stability of consistency under a target presentation

If `stream` presents `C z`, then a candidate which contains `C z` is
consistent at every time.  Conversely, every fixed candidate which does not
contain `C z` is eventually falsified by the stream.  This file makes the
second statement uniform over an arbitrary finite scope.

The resulting equivalence says that, after one finite threshold, consistency
inside the scope is a static property.  In particular, a candidate in the
scope which is consistent after that threshold remains consistent forever.
-/

namespace GenLimit

/-- For one fixed candidate, consistency eventually agrees with containment
of the presented target. -/
theorem candidate_eventually_consistent_iff_target_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {z i : ℕ}
    (hP : Presents stream (C z)) :
    ∃ T, ∀ t, T ≤ t →
      (Consistent C stream t i ↔ C z ⊆ C i) := by
  classical
  by_cases hsub : C z ⊆ C i
  · refine ⟨0, ?_⟩
    intro t _
    exact ⟨fun _ => hsub, fun _ => consistent_of_target_subset hP hsub⟩
  · obtain ⟨T, hT⟩ := eventually_not_consistent_of_not_subset hP hsub
    refine ⟨T, ?_⟩
    intro t ht
    constructor
    · intro hcon
      exact False.elim ((hT t ht) hcon)
    · intro hsub'
      exact False.elim (hsub hsub')

/-- Uniform finite-scope stabilization.  The scope `s` contains the indices
`i < s`; after one threshold, each such candidate is consistent exactly when
it contains the presented target. -/
theorem finite_scope_eventually_consistent_iff_target_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) (s : ℕ) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i < s →
      (Consistent C stream t i ↔ C z ⊆ C i) := by
  induction s with
  | zero =>
      exact ⟨0, by omega⟩
  | succ s ih =>
      obtain ⟨Ts, hTs⟩ := ih
      obtain ⟨Ti, hTi⟩ :=
        candidate_eventually_consistent_iff_target_subset
          (C := C) (stream := stream) (z := z) (i := s) hP
      refine ⟨max Ts Ti, ?_⟩
      intro t ht i his
      have hTs_t : Ts ≤ t := le_trans (Nat.le_max_left Ts Ti) ht
      have hTi_t : Ti ≤ t := le_trans (Nat.le_max_right Ts Ti) ht
      rcases Nat.lt_succ_iff_lt_or_eq.mp his with his' | rfl
      · exact hTs t hTs_t i his'
      · exact hTi t hTi_t

/-- The stabilization statement requested for all candidates no later than
the target index. -/
theorem target_prefix_eventually_consistent_iff_target_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i ≤ z →
      (Consistent C stream t i ↔ C z ⊆ C i) := by
  obtain ⟨T, hT⟩ :=
    finite_scope_eventually_consistent_iff_target_subset hP (z + 1)
  refine ⟨T, ?_⟩
  intro t ht i hiz
  exact hT t ht i (Nat.lt_succ_of_le hiz)

/-- Once finite-scope consistency has stabilized, any candidate which is
consistent at one time stays consistent at every later time. -/
theorem finite_scope_eventually_consistency_persistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) (s : ℕ) :
    ∃ T, ∀ t, T ≤ t → ∀ u, t ≤ u → ∀ i, i < s →
      Consistent C stream t i → Consistent C stream u i := by
  obtain ⟨T, hT⟩ :=
    finite_scope_eventually_consistent_iff_target_subset hP s
  refine ⟨T, ?_⟩
  intro t ht u _ i his hcon
  have hsub : C z ⊆ C i := (hT t ht i his).1 hcon
  exact consistent_of_target_subset hP hsub

/-- After one finite threshold, any consistent candidate of index at most
`z` remains consistent at all later times. -/
theorem target_prefix_eventually_consistency_persistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) :
    ∃ T, ∀ t, T ≤ t → ∀ u, t ≤ u → ∀ i, i ≤ z →
      Consistent C stream t i → Consistent C stream u i := by
  obtain ⟨T, hT⟩ :=
    finite_scope_eventually_consistency_persistent hP (z + 1)
  refine ⟨T, ?_⟩
  intro t ht u htu i hiz hcon
  exact hT t ht u htu i (Nat.lt_succ_of_le hiz) hcon

end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Critical
section
set_option autoImplicit true

/-!
# Recursive criticality for the patient-scope algorithm

This file records Definition 3.2 of arXiv:2608.01320v2.  Its
recursive notion of criticality compares a language only with earlier
*critical* languages.  Its eventual target theorem is derived directly from
the shared finite-scope stability of consistency.  Comparisons with KM
criticality live in the explicit cross-development bridge module.

Indices are zero-based.  Thus a scope of size `s` contains precisely the
indices in `Finset.range s`.
-/

namespace GenLimit

/-- Definition 3.2: recursive criticality in increasing index order. -/
def RecursiveCritical (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ → Prop
  | 0 => Consistent C stream t 0
  | n + 1 =>
      Consistent C stream t (n + 1) ∧
        ∀ j, j ≤ n → RecursiveCritical C stream t j → C (n + 1) ⊆ C j

theorem recursiveCritical_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ}
    (h : RecursiveCritical C stream t n) : Consistent C stream t n := by
  cases n with
  | zero => simpa [RecursiveCritical] using h
  | succ n =>
      have h' : Consistent C stream t (n + 1) ∧
          ∀ j, j ≤ n → RecursiveCritical C stream t j → C (n + 1) ⊆ C j := by
        simpa [RecursiveCritical] using h
      exact h'.1

/-- The critical languages form a descending inclusion chain (Remark 3.3). -/
theorem recursiveCritical_subset_of_le
    {C : LanguageFamily} {stream : ℕ → ℕ} {t i j : ℕ}
    (hij : i ≤ j)
    (hi : RecursiveCritical C stream t i)
    (hj : RecursiveCritical C stream t j) : C j ⊆ C i := by
  rcases eq_or_lt_of_le hij with rfl | hij
  · exact Set.Subset.rfl
  · cases j with
    | zero => omega
    | succ j =>
        have hj' : Consistent C stream t (j + 1) ∧
            ∀ k, k ≤ j → RecursiveCritical C stream t k → C (j + 1) ⊆ C k := by
          simpa [RecursiveCritical] using hj
        exact hj'.2 i (Nat.le_of_lt_succ hij) hi

/-- Lemma 3.4.  Once consistency in the target prefix has stabilized, every
earlier recursively critical language is consistent and hence contains the
target. -/
theorem target_eventually_recursiveCritical
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) :
    ∃ T, ∀ t, T ≤ t → RecursiveCritical C stream t z := by
  obtain ⟨T, hT⟩ :=
    target_prefix_eventually_consistent_iff_target_subset hP
  refine ⟨T, ?_⟩
  intro t ht
  cases z with
  | zero =>
      simpa only [RecursiveCritical] using presents_consistent (t := t) hP
  | succ n =>
      rw [RecursiveCritical]
      refine ⟨presents_consistent hP, ?_⟩
      intro j hj hjcrit
      have hjz : j ≤ n + 1 := Nat.le_trans hj (Nat.le_succ n)
      exact (hT t ht j hjz).1 (recursiveCritical_consistent hjcrit)

/-- `f` is the highest-indexed critical language in the first `s` entries. -/
def IsFocus
    (C : LanguageFamily) (stream : ℕ → ℕ) (t s f : ℕ) : Prop :=
  f < s ∧ RecursiveCritical C stream t f ∧
    ∀ j, j < s → RecursiveCritical C stream t j → j ≤ f

/-- A focus exists whenever a critical language lies inside the scope. -/
theorem exists_focus_of_critical_in_scope
    {C : LanguageFamily} {stream : ℕ → ℕ} {t s z : ℕ}
    (hzs : z < s) (hz : RecursiveCritical C stream t z) :
    ∃ f, IsFocus C stream t s f := by
  classical
  let candidates := (Finset.range s).filter (RecursiveCritical C stream t)
  have hne : candidates.Nonempty := by
    refine ⟨z, ?_⟩
    simp [candidates, hzs, hz]
  refine ⟨candidates.max' hne, ?_⟩
  have hmem := candidates.max'_mem hne
  have hparts : candidates.max' hne < s ∧
      RecursiveCritical C stream t (candidates.max' hne) := by
    simpa [candidates] using hmem
  refine ⟨hparts.1, hparts.2, ?_⟩
  intro j hjs hj
  apply Finset.le_max' candidates j
  simp [candidates, hjs, hj]

/-- If a recursively critical index `z` lies inside the scope, the focus
language is contained in `C z`.  In the validity proof, `z` is instantiated
with the target index.  This is the set-theoretic step used in Lemma 3.12. -/
theorem focus_subset_target
    {C : LanguageFamily} {stream : ℕ → ℕ} {t s f z : ℕ}
    (hf : IsFocus C stream t s f)
    (hzs : z < s) (hz : RecursiveCritical C stream t z) :
    C f ⊆ C z := by
  have hzf : z ≤ f := hf.2.2 z hzs hz
  exact recursiveCritical_subset_of_le hzf hz hf.2.1

end GenLimit

end

-- GenLimit.Core.OracleFamily
section
set_option autoImplicit true

/-!
# Indexed language families with a membership oracle

This shared record is used by both formalized papers.  The finite-query KM
machine uses all four fields to realize its tests.  The semantic KM generator
and the semantic patient-scope machine use only the indexed languages and
their infinitude, but keeping the common record lets the generators be
compared on exactly the same family.
-/

namespace GenLimit

/-- An indexed infinite language family equipped with a uniform Boolean
membership oracle. -/
structure OracleFamily where
  language : LanguageFamily
  infinite' : ∀ i, (language i).Infinite
  query : ℕ → ℕ → Bool
  query_spec : ∀ i u, query i u = true ↔ u ∈ language i

namespace OracleFamily

variable (O : OracleFamily)

/-- A language index is consistent with a fixed finite positive sample when
the uniform membership oracle accepts every point in that sample. -/
def ConsistentOnFinset (S : Finset ℕ) (i : ℕ) : Prop :=
  ∀ x ∈ S, O.query i x = true

instance consistentOnFinsetDecidable (S : Finset ℕ) (i : ℕ) :
    Decidable (O.ConsistentOnFinset S i) := by
  unfold ConsistentOnFinset
  infer_instance

/-- Oracle consistency on a finite sample is exactly set containment. -/
theorem consistentOnFinset_iff {S : Finset ℕ} {i : ℕ} :
    O.ConsistentOnFinset S i ↔ (↑S : Set ℕ) ⊆ O.language i := by
  constructor
  · intro h x hx
    exact (O.query_spec i x).mp (h x hx)
  · intro h x hx
    exact (O.query_spec i x).mpr (h hx)

end OracleFamily

end GenLimit

end

-- GenLimit.Support.LeastCandidate
section
set_option autoImplicit true

/-!
# Extremal candidates with a fallback

Paper-independent selection from a finite candidate set.  The fallback makes
the selector total; whenever a candidate exists, the selector is exactly the
least candidate and inherits the usual membership and minimality facts.

The module also supplies the least index naming the same object as a given
entry of an indexed family.  This is the shared duplicate-name convention
used by identification and generation reductions.
-/

namespace GenLimit.Support

/-- Select the least member of `candidates`, or `fallback` when the candidate
set is empty. -/
def leastCandidateWithFallback [LinearOrder α]
    (candidates : Finset α) (fallback : α) : α :=
  if h : candidates.Nonempty then candidates.min' h else fallback

theorem leastCandidateWithFallback_eq_min'
    [LinearOrder α] {candidates : Finset α} {fallback : α}
    (hne : candidates.Nonempty) :
    leastCandidateWithFallback candidates fallback = candidates.min' hne := by
  simp [leastCandidateWithFallback, hne]

theorem leastCandidateWithFallback_mem
    [LinearOrder α] {candidates : Finset α} {fallback : α}
    (hne : candidates.Nonempty) :
    leastCandidateWithFallback candidates fallback ∈ candidates := by
  rw [leastCandidateWithFallback_eq_min' hne]
  exact Finset.min'_mem _ _

theorem leastCandidateWithFallback_le
    [LinearOrder α] {candidates : Finset α} {fallback i : α}
    (hi : i ∈ candidates) :
    leastCandidateWithFallback candidates fallback ≤ i := by
  have hne : candidates.Nonempty := ⟨i, hi⟩
  rw [leastCandidateWithFallback_eq_min' hne]
  exact Finset.min'_le _ _ hi

/-! ## Greatest candidates -/

/-- Select the greatest member of `candidates`, or `fallback` when the
candidate set is empty. -/
def greatestCandidateWithFallback [LinearOrder α]
    (candidates : Finset α) (fallback : α) : α :=
  if h : candidates.Nonempty then candidates.max' h else fallback

theorem greatestCandidateWithFallback_eq_max'
    [LinearOrder α] {candidates : Finset α} {fallback : α}
    (hne : candidates.Nonempty) :
    greatestCandidateWithFallback candidates fallback = candidates.max' hne := by
  simp [greatestCandidateWithFallback, hne]

theorem greatestCandidateWithFallback_mem
    [LinearOrder α] {candidates : Finset α} {fallback : α}
    (hne : candidates.Nonempty) :
    greatestCandidateWithFallback candidates fallback ∈ candidates := by
  rw [greatestCandidateWithFallback_eq_max' hne]
  exact Finset.max'_mem _ _

theorem le_greatestCandidateWithFallback
    [LinearOrder α] {candidates : Finset α} {fallback i : α}
    (hi : i ∈ candidates) :
    i ≤ greatestCandidateWithFallback candidates fallback := by
  have hne : candidates.Nonempty := ⟨i, hi⟩
  rw [greatestCandidateWithFallback_eq_max' hne]
  exact Finset.le_max' _ _ hi

/-! ## Least equivalent family indices -/

/-- The least index whose family entry is equal to the entry at `z`.
Repeated names are allowed, and no decidable equality on the entries is
required. -/
noncomputable def leastEquivalentIndex
    {β : Type*} (family : ℕ → β) (z : ℕ) : ℕ := by
  classical
  exact Nat.find
    (show ∃ i, family i = family z from ⟨z, rfl⟩)

theorem leastEquivalentIndex_spec
    {β : Type*} (family : ℕ → β) (z : ℕ) :
    family (leastEquivalentIndex family z) = family z := by
  classical
  exact Nat.find_spec
    (show ∃ i, family i = family z from ⟨z, rfl⟩)

theorem leastEquivalentIndex_minimal
    {β : Type*} (family : ℕ → β) (z i : ℕ)
    (hi : family i = family z) :
    leastEquivalentIndex family z ≤ i := by
  classical
  exact Nat.find_min'
    (show ∃ j, family j = family z from ⟨z, rfl⟩) hi

theorem leastEquivalentIndex_le_self
    {β : Type*} (family : ℕ → β) (z : ℕ) :
    leastEquivalentIndex family z ≤ z :=
  leastEquivalentIndex_minimal family z z rfl

theorem leastEquivalentIndex_ne_of_lt
    {β : Type*} (family : ℕ → β) (z : ℕ) {i : ℕ}
    (hi : i < leastEquivalentIndex family z) :
    family i ≠ family z := by
  intro heq
  exact (Nat.not_lt_of_ge
    (leastEquivalentIndex_minimal family z i heq)) hi

end GenLimit.Support

end

-- GenLimit.Paper39_DenseGeneration.Patient.Machine
section
set_option autoImplicit true

/-!
# A semantic patient-scope machine

This file gives a precise state machine for the patient-scope algorithm from
Section 3.2 of the patient-scope manuscript.  It is deliberately semantic:
criticality uses exact inclusion between languages, and the definitions below
use classical choice.  In particular, this is not the finite-membership-query
machine from `GenLimit.Paper01_LanguageGeneration.FiniteQuery.Machine`.

Time is zero-based.  A state at time `t` records the situation after the first
`t` adversary announcements and generator outputs.  A scope `s` is an
exclusive upper bound, so it contains the indices in `Finset.range s`.

The `age` field counts completed rounds with the current focus.  Consequently,
scope expansion is tested by `2 ^ tau ≤ age` before the next output.  This is
the literal meaning of waiting until the focus has been unchanged throughout
the previous `2 ^ tau` rounds.
-/

namespace GenLimit
namespace PatientMachine

/-- The reason for the most recent focus update. -/
inductive MoveKind where
  | initial
  | stay
  | expand
  | backtrack
deriving DecidableEq, Repr

/-- State after a finite number of complete adversary/generator rounds. -/
structure State where
  /-- Exclusive upper bound on language indices in scope. -/
  scope : ℕ
  /-- Number of focus changes, initialized to one as in the paper. -/
  tau : ℕ
  /-- Number of completed consecutive rounds with the current focus. -/
  age : ℕ
  /-- Index of the current focus language. -/
  focus : ℕ
  /-- All values previously output by the generator. -/
  used : Finset ℕ
  /-- Output of the most recently completed round. -/
  lastOutput : Option ℕ
  /-- Branch taken in the most recently completed round. -/
  move : MoveKind

/-- The initial state, before either party has announced a value. -/
def initialState : State where
  scope := 1
  tau := 1
  age := 0
  focus := 0
  used := ∅
  lastOutput := none
  move := .initial

/-- Indices that are consistent after `t` observations and lie in scope. -/
noncomputable def consistentIndices
    (C : LanguageFamily) (stream : ℕ → ℕ) (t scope : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range scope).filter (Consistent C stream t)

/-- Critical indices after `t` observations and inside the given scope. -/
noncomputable def criticalIndices
    (C : LanguageFamily) (stream : ℕ → ℕ) (t scope : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range scope).filter (RecursiveCritical C stream t)

/-- Old critical indices that remain critical after the current observation. -/
noncomputable def survivingCriticalIndices
    (C : LanguageFamily) (stream : ℕ → ℕ) (t scope : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range scope).filter fun i =>
    RecursiveCritical C stream t i ∧ RecursiveCritical C stream (t + 1) i

@[simp] theorem mem_consistentIndices
    {C : LanguageFamily} {stream : ℕ → ℕ} {t scope i : ℕ} :
    i ∈ consistentIndices C stream t scope ↔
      i < scope ∧ Consistent C stream t i := by
  classical
  simp [consistentIndices]

@[simp] theorem mem_criticalIndices
    {C : LanguageFamily} {stream : ℕ → ℕ} {t scope i : ℕ} :
    i ∈ criticalIndices C stream t scope ↔
      i < scope ∧ RecursiveCritical C stream t i := by
  classical
  simp [criticalIndices]

@[simp] theorem mem_survivingCriticalIndices
    {C : LanguageFamily} {stream : ℕ → ℕ} {t scope i : ℕ} :
    i ∈ survivingCriticalIndices C stream t scope ↔
      i < scope ∧ RecursiveCritical C stream t i ∧
        RecursiveCritical C stream (t + 1) i := by
  classical
  simp [survivingCriticalIndices]

/-- Highest critical index in scope, with an explicit fallback for histories
outside the paper's model. -/
noncomputable def highestCritical
    (C : LanguageFamily) (stream : ℕ → ℕ) (t scope fallback : ℕ) : ℕ := by
  classical
  let candidates := criticalIndices C stream t scope
  exact GenLimit.Support.greatestCandidateWithFallback candidates fallback

/-- Highest old critical index that is still critical, again totalized by an
explicit fallback. -/
noncomputable def highestSurvivor
    (C : LanguageFamily) (stream : ℕ → ℕ) (t scope fallback : ℕ) : ℕ := by
  classical
  let candidates := survivingCriticalIndices C stream t scope
  exact GenLimit.Support.greatestCandidateWithFallback candidates fallback

/-- Lowest consistent index in a nonempty finite scope. -/
noncomputable def lowestConsistentInScope
    (C : LanguageFamily) (stream : ℕ → ℕ) (t scope fallback : ℕ) : ℕ := by
  classical
  let candidates := consistentIndices C stream t scope
  exact GenLimit.Support.leastCandidateWithFallback candidates fallback

/-- Lowest globally consistent language.  The fallback makes the definition
total on streams that have no consistent language in the family. -/
noncomputable def lowestConsistent
    (C : LanguageFamily) (stream : ℕ → ℕ) (t fallback : ℕ) : ℕ := by
  classical
  exact if h : ∃ i, Consistent C stream t i then Nat.find h else fallback

theorem highestCritical_isFocus
    {C : LanguageFamily} {stream : ℕ → ℕ} {t scope fallback : ℕ}
    (hne : (criticalIndices C stream t scope).Nonempty) :
    IsFocus C stream t scope
      (highestCritical C stream t scope fallback) := by
  classical
  let candidates := criticalIndices C stream t scope
  have hne' : candidates.Nonempty := hne
  have hmem :
      GenLimit.Support.greatestCandidateWithFallback candidates fallback ∈ candidates :=
    GenLimit.Support.greatestCandidateWithFallback_mem hne'
  have hparts :
      GenLimit.Support.greatestCandidateWithFallback candidates fallback < scope ∧
      RecursiveCritical C stream t
        (GenLimit.Support.greatestCandidateWithFallback candidates fallback) := by
    simpa [candidates] using hmem
  have hmax : ∀ j, j < scope → RecursiveCritical C stream t j →
      j ≤ GenLimit.Support.greatestCandidateWithFallback candidates fallback := by
    intro j hjs hj
    exact GenLimit.Support.le_greatestCandidateWithFallback
      (by simp [candidates, hjs, hj])
  simpa [highestCritical, candidates] using
    (show IsFocus C stream t scope
        (GenLimit.Support.greatestCandidateWithFallback candidates fallback) from
      ⟨hparts.1, hparts.2, hmax⟩)

theorem highestSurvivor_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {t scope fallback : ℕ}
    (hne : (survivingCriticalIndices C stream t scope).Nonempty) :
    let i := highestSurvivor C stream t scope fallback
    i < scope ∧ RecursiveCritical C stream t i ∧
      RecursiveCritical C stream (t + 1) i ∧
      ∀ j, j < scope → RecursiveCritical C stream t j →
        RecursiveCritical C stream (t + 1) j → j ≤ i := by
  classical
  let candidates := survivingCriticalIndices C stream t scope
  have hne' : candidates.Nonempty := hne
  have hmem :
      GenLimit.Support.greatestCandidateWithFallback candidates fallback ∈ candidates :=
    GenLimit.Support.greatestCandidateWithFallback_mem hne'
  have hparts :
      GenLimit.Support.greatestCandidateWithFallback candidates fallback < scope ∧
      RecursiveCritical C stream t
        (GenLimit.Support.greatestCandidateWithFallback candidates fallback) ∧
      RecursiveCritical C stream (t + 1)
        (GenLimit.Support.greatestCandidateWithFallback candidates fallback) := by
    simpa [candidates] using hmem
  have hmax : ∀ j, j < scope → RecursiveCritical C stream t j →
      RecursiveCritical C stream (t + 1) j →
      j ≤ GenLimit.Support.greatestCandidateWithFallback candidates fallback := by
    intro j hjs hjold hjnew
    exact GenLimit.Support.le_greatestCandidateWithFallback
      (by simp [candidates, hjs, hjold, hjnew])
  simpa [highestSurvivor, candidates] using
    (show
      GenLimit.Support.greatestCandidateWithFallback candidates fallback < scope ∧
        RecursiveCritical C stream t
          (GenLimit.Support.greatestCandidateWithFallback candidates fallback) ∧
        RecursiveCritical C stream (t + 1)
          (GenLimit.Support.greatestCandidateWithFallback candidates fallback) ∧
        ∀ j, j < scope → RecursiveCritical C stream t j →
          RecursiveCritical C stream (t + 1) j →
          j ≤ GenLimit.Support.greatestCandidateWithFallback candidates fallback from
      ⟨hparts.1, hparts.2.1, hparts.2.2, hmax⟩)

theorem lowestConsistentInScope_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {t scope fallback : ℕ}
    (hne : (consistentIndices C stream t scope).Nonempty) :
    let i := lowestConsistentInScope C stream t scope fallback
    i < scope ∧ Consistent C stream t i ∧
      ∀ j, j < i → ¬ Consistent C stream t j := by
  classical
  let candidates := consistentIndices C stream t scope
  have hne' : candidates.Nonempty := hne
  have hmem :
      GenLimit.Support.leastCandidateWithFallback candidates fallback ∈ candidates :=
    GenLimit.Support.leastCandidateWithFallback_mem hne'
  have hparts :
      GenLimit.Support.leastCandidateWithFallback candidates fallback < scope ∧
      Consistent C stream t
        (GenLimit.Support.leastCandidateWithFallback candidates fallback) := by
    simpa [candidates] using hmem
  have hmin : ∀ j,
      j < GenLimit.Support.leastCandidateWithFallback candidates fallback →
      ¬ Consistent C stream t j := by
    intro j hj hcon
    have hjs : j < scope := lt_trans hj hparts.1
    have hjmem : j ∈ candidates := by simp [candidates, hjs, hcon]
    exact (Nat.not_lt_of_ge
      (GenLimit.Support.leastCandidateWithFallback_le hjmem)) hj
  simpa [lowestConsistentInScope, candidates] using
    (show
      GenLimit.Support.leastCandidateWithFallback candidates fallback < scope ∧
        Consistent C stream t
          (GenLimit.Support.leastCandidateWithFallback candidates fallback) ∧
        ∀ j, j < GenLimit.Support.leastCandidateWithFallback candidates fallback →
          ¬ Consistent C stream t j from
      ⟨hparts.1, hparts.2, hmin⟩)

theorem lowestConsistent_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {t fallback : ℕ}
    (hne : ∃ i, Consistent C stream t i) :
    Consistent C stream t (lowestConsistent C stream t fallback) ∧
      ∀ j, j < lowestConsistent C stream t fallback →
        ¬ Consistent C stream t j := by
  classical
  have hspec := Nat.find_spec hne
  have hmin : ∀ j, j < Nat.find hne → ¬ Consistent C stream t j :=
    fun j hj => Nat.find_min hne hj
  have heq : lowestConsistent C stream t fallback = Nat.find hne := by
    simp only [lowestConsistent]
    rw [dif_pos hne]
  rw [heq]
  exact ⟨hspec, hmin⟩

/-- A consistent index with no earlier consistent predecessor is
recursively critical. -/
theorem recursiveCritical_of_consistent_of_minimal
    {C : LanguageFamily} {stream : ℕ → ℕ} {t i : ℕ}
    (hcon : Consistent C stream t i)
    (hmin : ∀ j, j < i → ¬ Consistent C stream t j) :
    RecursiveCritical C stream t i := by
  cases i with
  | zero => simpa only [RecursiveCritical] using hcon
  | succ n =>
      rw [RecursiveCritical]
      refine ⟨hcon, ?_⟩
      intro j hj hjcrit
      exact False.elim
        (hmin j (Nat.lt_succ_of_le hj) (recursiveCritical_consistent hjcrit))

/-- The focus/scope part of a transition, before producing the output. -/
structure Decision where
  scope : ℕ
  tau : ℕ
  focus : ℕ
  move : MoveKind

/-- Backtracking after round `t`'s adversary announcement falsifies the old
focus.  Criticality before the announcement is evaluated at `t`; criticality
after it is evaluated at `t + 1`.

If the old scope still contains a consistent language, the machine keeps the
highest old critical language that remains critical.  When none survives, it
uses the lowest consistent language in that scope.  If the old scope has no
consistent language, it expands to the globally lowest consistent index. -/
noncomputable def backtrackDecision
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) : Decision := by
  classical
  let consistent := consistentIndices C stream (t + 1) old.scope
  if hcon : consistent.Nonempty then
    let survivors := survivingCriticalIndices C stream t old.scope
    let i := if survivors.Nonempty then
      highestSurvivor C stream t old.scope old.focus
    else
      lowestConsistentInScope C stream (t + 1) old.scope old.focus
    exact ⟨i + 1, old.tau + 1, i, .backtrack⟩
  else
    let i := lowestConsistent C stream (t + 1) old.focus
    if hall : ∃ j, Consistent C stream (t + 1) j then
      exact ⟨i + 1, old.tau + 1, i, .backtrack⟩
    else
      -- Off-model case: preserve a positive scope and the old focus.
      exact ⟨max old.scope 1, old.tau + 1, old.focus, .backtrack⟩

/-- Stable-focus update.  Once `2 ^ tau` complete rounds have elapsed under
the current focus, the exclusive scope grows by one. -/
noncomputable def stableDecision
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) : Decision := by
  classical
  if hwait : 2 ^ old.tau ≤ old.age then
    let newScope := old.scope + 1
    let newFocus := highestCritical C stream (t + 1) newScope old.focus
    let newTau := if newFocus = old.focus then old.tau else old.tau + 1
    exact ⟨newScope, newTau, newFocus, .expand⟩
  else
    exact ⟨old.scope, old.tau, old.focus, .stay⟩

/-- Focus update after receiving the adversary value in round `t`. -/
noncomputable def decide
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) : Decision := by
  classical
  exact if Consistent C stream (t + 1) old.focus then
    stableDecision C stream t old
  else
    backtrackDecision C stream t old

/-- A value is available for output when it is in the focus and has been
announced by neither party. -/
def Available
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ)
    (used : Finset ℕ) (focus x : ℕ) : Prop :=
  x ∈ C focus ∧ x ∉ sample stream t ∧ x ∉ used

theorem available_exists
    (C : LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    (stream : ℕ → ℕ) (t : ℕ) (used : Finset ℕ) (focus : ℕ) :
    ∃ x, Available C stream t used focus x := by
  classical
  obtain ⟨x, hx, hfresh⟩ :=
    (hInfinite focus).exists_notMem_finset (sample stream t ∪ used)
  simp only [Finset.mem_union, not_or] at hfresh
  exact ⟨x, hx, hfresh.1, hfresh.2⟩

/-- Smallest value in the focus not previously announced by either party. -/
noncomputable def leastAvailable
    (C : LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    (stream : ℕ → ℕ) (t : ℕ) (used : Finset ℕ) (focus : ℕ) : ℕ := by
  classical
  exact Nat.find (available_exists C hInfinite stream t used focus)

theorem leastAvailable_spec
    (C : LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    (stream : ℕ → ℕ) (t : ℕ) (used : Finset ℕ) (focus : ℕ) :
    Available C stream t used focus
      (leastAvailable C hInfinite stream t used focus) := by
  classical
  exact Nat.find_spec (available_exists C hInfinite stream t used focus)

theorem leastAvailable_minimal
    (C : LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    (stream : ℕ → ℕ) (t : ℕ) (used : Finset ℕ) (focus x : ℕ)
    (hx : Available C stream t used focus x) :
    leastAvailable C hInfinite stream t used focus ≤ x := by
  classical
  exact Nat.find_min' (available_exists C hInfinite stream t used focus) hx

/-- Execute round `t`: receive `stream t`, update the focus, and announce the
smallest fresh value in the resulting focus. -/
noncomputable def processRound
    (O : OracleFamily)
    (stream : ℕ → ℕ) (t : ℕ) (old : State) : State := by
  classical
  let d := decide O.language stream t old
  let x := leastAvailable O.language O.infinite' stream (t + 1) old.used d.focus
  exact
    { scope := d.scope
      tau := d.tau
      age := if d.focus = old.focus then old.age + 1 else 1
      focus := d.focus
      used := insert x old.used
      lastOutput := some x
      move := d.move }

/-- State after the first `t` complete rounds. -/
noncomputable def run
    (O : OracleFamily)
    (stream : ℕ → ℕ) : ℕ → State
  | 0 => initialState
  | t + 1 => processRound O stream t (run O stream t)

/-- The generator's round-`t` announcement. -/
noncomputable def output
    (O : OracleFamily)
    (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  (run O stream (t + 1)).lastOutput.getD 0

@[simp] theorem run_zero
    (O : OracleFamily)
    (stream : ℕ → ℕ) :
    run O stream 0 = initialState := rfl

@[simp] theorem run_succ
    (O : OracleFamily)
    (stream : ℕ → ℕ) (t : ℕ) :
    run O stream (t + 1) =
      processRound O stream t (run O stream t) := rfl

@[simp] theorem processRound_lastOutput
    (O : OracleFamily)
    (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (processRound O stream t old).lastOutput =
      some (leastAvailable O.language O.infinite' stream (t + 1) old.used
        (decide O.language stream t old).focus) := by
  simp [processRound]

@[simp] theorem output_eq_leastAvailable
    (O : OracleFamily)
    (stream : ℕ → ℕ) (t : ℕ) :
    output O stream t =
      leastAvailable O.language O.infinite' stream (t + 1)
        (run O stream t).used
        (decide O.language stream t (run O stream t)).focus := by
  simp [output]

/-- Every output belongs to the focus selected in its round, is absent from
the adversary sample through that round, and was not output earlier. -/
theorem output_available
    (O : OracleFamily)
    (stream : ℕ → ℕ) (t : ℕ) :
    Available O.language stream (t + 1) (run O stream t).used
      (decide O.language stream t (run O stream t)).focus
      (output O stream t) := by
  rw [output_eq_leastAvailable]
  exact leastAvailable_spec O.language O.infinite' stream (t + 1)
    (run O stream t).used
    (decide O.language stream t (run O stream t)).focus

end PatientMachine
end GenLimit

end

-- MissionCritical
section
set_option autoImplicit true

/-! The finite-list public mission and GenLimitLib use the same recursive
critical chain after shifting positive labels to zero-based naturals. -/
namespace DenseLanguageGeneration.PatientScope
open ActiveLanguageGeneration.Hierarchy
open scoped Classical
noncomputable section

def encode (x : ℕ) : ℕ+ := Equiv.pnatEquivNat.symm x

def oracle (L : Family) : GenLimit.OracleFamily where
  language i := encode ⁻¹' (L i).val
  infinite' i := by
    have h : encode ⁻¹' (L i).val = Equiv.pnatEquivNat '' (L i).val := by
      ext j
      constructor
      · intro hj; exact ⟨encode j,hj,Equiv.pnatEquivNat.apply_symm_apply _⟩
      · rintro ⟨x,hx,rfl⟩
        change Equiv.pnatEquivNat.symm (Equiv.pnatEquivNat x) ∈ (L i).val
        simpa using hx
    rw [h]
    exact (L i).property.image Equiv.pnatEquivNat.injective.injOn
  query i x := decide (encode x ∈ (L i).val)
  query_spec _ _ := by simp

theorem consistent_transport (L : Family) (a : ℕ → ℕ) (t j : ℕ) :
    Consistent L (history (encode ∘ a) t) j ↔
      GenLimit.Consistent (oracle L).language a t j := by
  constructor
  · intro h x hx
    obtain ⟨s,hs,rfl⟩ := GenLimit.mem_sample_iff.mp hx
    apply h
    exact List.mem_map.mpr ⟨s, List.mem_range.mpr hs,rfl⟩
  · intro h x hx
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
    exact h (GenLimit.mem_sample_iff.mpr ⟨s,List.mem_range.mp hs,rfl⟩)

private theorem inclusion_transport (L : Family) (i j : ℕ) :
    (L i).val ⊆ (L j).val ↔ (oracle L).language i ⊆ (oracle L).language j := by
  constructor
  · intro h x hx; exact h hx
  · intro h x hx
    have h' : x.natPred ∈ (oracle L).language i := by
      change Equiv.pnatEquivNat.symm (Equiv.pnatEquivNat x) ∈ (L i).val
      simpa using hx
    simpa [oracle, encode] using h h'

private theorem critical_eqn (C : GenLimit.LanguageFamily) (a : ℕ → ℕ) (t j : ℕ) :
    GenLimit.RecursiveCritical C a t j ↔ GenLimit.Consistent C a t j ∧
      ∀ k < j, GenLimit.RecursiveCritical C a t k → C j ⊆ C k := by
  cases j with
  | zero => simp [GenLimit.RecursiveCritical]
  | succ j => simp only [GenLimit.RecursiveCritical, Nat.lt_succ_iff]

theorem indices_transport (L : Family) (a : ℕ → ℕ) (t s : ℕ) :
    criticalIndices L (history (encode ∘ a) t) s =
    GenLimit.PatientMachine.criticalIndices (oracle L).language a t s := by
  classical
  induction s with
  | zero => simp [criticalIndices,GenLimit.PatientMachine.criticalIndices]
  | succ s ih =>
    rw [criticalIndices, ih]
    have hcond :
        (Consistent L (history (encode ∘ a) t) s ∧
        ∀ k ∈ GenLimit.PatientMachine.criticalIndices (oracle L).language a t s,
          (L s).val ⊆ (L k).val) ↔ GenLimit.RecursiveCritical (oracle L).language a t s := by
      rw [critical_eqn, consistent_transport]
      simp only [GenLimit.PatientMachine.mem_criticalIndices, and_imp, inclusion_transport]
    split
    · rename_i hc
      have hcrit := hcond.mp hc
      ext j
      simp only [Finset.mem_insert, GenLimit.PatientMachine.mem_criticalIndices]
      constructor
      · rintro (rfl | ⟨hlt,hc⟩)
        · exact ⟨by omega,hcrit⟩
        · exact ⟨by omega,hc⟩
      · rintro ⟨hlt,hc⟩
        by_cases h : j = s
        · exact Or.inl h
        · exact Or.inr ⟨by omega,hc⟩
    · rename_i hc
      ext j
      simp only [GenLimit.PatientMachine.mem_criticalIndices]
      constructor
      · rintro ⟨hlt, h⟩; exact ⟨by omega,h⟩
      · rintro ⟨hlt,h⟩
        have hne : j ≠ s := by rintro rfl; exact hc (hcond.mpr h)
        exact ⟨by omega,h⟩

theorem critical_transport (L : Family) (a : ℕ → ℕ) (t j : ℕ) :
    Critical L (history (encode ∘ a) t) j ↔ GenLimit.RecursiveCritical (oracle L).language a t j := by
  rw [Critical,indices_transport,GenLimit.PatientMachine.mem_criticalIndices]
  simp

/-- Lemma 3.4 with the public mission's exact binders and criticality predicate. -/
theorem eventually_critical (L : Family) (i : ℕ) (a : ℕ → ℕ+)
    (ha : IsEnumeration (L i) a) :
    ∃ T : ℕ, ∀ t ≥ T, Critical L (history a t) i := by
  let b : ℕ → ℕ := Equiv.pnatEquivNat ∘ a
  have he : encode ∘ b = a := by
    funext n; exact Equiv.pnatEquivNat.symm_apply_apply (a n)
  have hp : GenLimit.Presents b ((oracle L).language i) := by
    ext x
    constructor
    · rintro ⟨n,rfl⟩
      have hx : a n ∈ (L i).val := by rw [← ha.2]; exact ⟨n,rfl⟩
      change Equiv.pnatEquivNat.symm (Equiv.pnatEquivNat (a n)) ∈ (L i).val
      simpa using hx
    · intro hx
      change encode x ∈ (L i).val at hx
      rw [← ha.2] at hx
      obtain ⟨n,hn⟩ := hx
      refine ⟨n,?_⟩
      change Equiv.pnatEquivNat (a n) = x
      rw [hn]
      exact Equiv.pnatEquivNat.apply_symm_apply x
  obtain ⟨T,hT⟩ := GenLimit.target_eventually_recursiveCritical hp
  exact ⟨T, fun t ht => he ▸ (critical_transport L b t i).2 (hT t ht)⟩

end
end DenseLanguageGeneration.PatientScope

end

-- GenLimit.Paper39_DenseGeneration.Patient.MachineInvariant
section
set_option autoImplicit true

/-!
# Invariants of the semantic patient-scope machine

This file proves that the state machine in
`GenLimit.Paper39_DenseGeneration.Patient.Machine` follows
the paper's mathematical model whenever the adversary stream presents one of
the candidate languages.  The statements separate local transition facts
from the global run invariant so later validity and charging arguments can use
the branch information directly.
-/

namespace GenLimit
namespace PatientMachine

/-- If the old focus survives one more observation, criticality of every
language in the old scope is unchanged.  The old focus being maximal is the
key hypothesis: every old critical language contains it and therefore also
survives. -/
theorem critical_iff_next_of_focus_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {t scope focus : ℕ}
    (hfocus : IsFocus C stream t scope focus)
    (hsurvives : Consistent C stream (t + 1) focus) :
    ∀ i, i < scope →
      (RecursiveCritical C stream t i ↔
        RecursiveCritical C stream (t + 1) i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hiscope
      constructor
      · intro hiold
        have hifocus : i ≤ focus := hfocus.2.2 i hiscope hiold
        have hsub : C focus ⊆ C i :=
          recursiveCritical_subset_of_le hifocus hiold hfocus.2.1
        have hinewCon : Consistent C stream (t + 1) i :=
          fun x hx => hsub (hsurvives hx)
        cases i with
        | zero => simpa [RecursiveCritical] using hinewCon
        | succ i =>
            rw [RecursiveCritical]
            refine ⟨hinewCon, ?_⟩
            intro j hji hjnew
            have hjlt : j < i + 1 := Nat.lt_succ_of_le hji
            have hjscope : j < scope := lt_trans hjlt hiscope
            have hjold : RecursiveCritical C stream t j :=
              (ih j hjlt hjscope).2 hjnew
            have hiold' : Consistent C stream t (i + 1) ∧
                ∀ k, k ≤ i → RecursiveCritical C stream t k →
                  C (i + 1) ⊆ C k := by
              simpa [RecursiveCritical] using hiold
            exact hiold'.2 j hji hjold
      · intro hinew
        have hinewCon := recursiveCritical_consistent hinew
        have hioldCon : Consistent C stream t i := by
          intro x hx
          exact hinewCon (sample_mono (Nat.le_succ t) hx)
        cases i with
        | zero => simpa [RecursiveCritical] using hioldCon
        | succ i =>
            rw [RecursiveCritical]
            refine ⟨hioldCon, ?_⟩
            intro j hji hjold
            have hjlt : j < i + 1 := Nat.lt_succ_of_le hji
            have hjscope : j < scope := lt_trans hjlt hiscope
            have hjnew : RecursiveCritical C stream (t + 1) j :=
              (ih j hjlt hjscope).1 hjold
            have hinew' : Consistent C stream (t + 1) (i + 1) ∧
                ∀ k, k ≤ i → RecursiveCritical C stream (t + 1) k →
                  C (i + 1) ⊆ C k := by
              simpa [RecursiveCritical] using hinew
            exact hinew'.2 j hji hjnew

/-- A surviving focus remains the focus when the scope is fixed. -/
theorem focus_next_of_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {t scope focus : ℕ}
    (hfocus : IsFocus C stream t scope focus)
    (hsurvives : Consistent C stream (t + 1) focus) :
    IsFocus C stream (t + 1) scope focus := by
  refine ⟨hfocus.1, ?_, ?_⟩
  · exact (critical_iff_next_of_focus_consistent hfocus hsurvives
      focus hfocus.1).1 hfocus.2.1
  · intro j hjs hj
    exact hfocus.2.2 j hjs
      ((critical_iff_next_of_focus_consistent hfocus hsurvives j hjs).2 hj)

/-- At time zero, index zero is the unique index in scope and is critical. -/
theorem initial_focus_isFocus
    (C : LanguageFamily) (stream : ℕ → ℕ) :
    IsFocus C stream 0 initialState.scope initialState.focus := by
  simp [initialState, IsFocus, RecursiveCritical, Consistent, sample]

@[simp] theorem stableDecision_scope
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (stableDecision C stream t old).scope =
      if 2 ^ old.tau ≤ old.age then old.scope + 1 else old.scope := by
  classical
  by_cases h : 2 ^ old.tau ≤ old.age <;> simp [stableDecision, h]

@[simp] theorem stableDecision_move
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (stableDecision C stream t old).move =
      if 2 ^ old.tau ≤ old.age then .expand else .stay := by
  classical
  by_cases h : 2 ^ old.tau ≤ old.age <;> simp [stableDecision, h]

theorem stableDecision_of_not_wait
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hwait : ¬ 2 ^ old.tau ≤ old.age) :
    stableDecision C stream t old =
      ⟨old.scope, old.tau, old.focus, .stay⟩ := by
  classical
  simp [stableDecision, hwait]

theorem stableDecision_isFocus
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hfocus : IsFocus C stream t old.scope old.focus)
    (hsurvives : Consistent C stream (t + 1) old.focus) :
    IsFocus C stream (t + 1)
      (stableDecision C stream t old).scope
      (stableDecision C stream t old).focus := by
  classical
  have hfixed := focus_next_of_consistent hfocus hsurvives
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · let newScope := old.scope + 1
    have hlt : old.focus < newScope :=
      lt_of_lt_of_le hfocus.1 (Nat.le_succ old.scope)
    have hne :
        (criticalIndices C stream (t + 1) newScope).Nonempty := by
      exact ⟨old.focus, mem_criticalIndices.mpr ⟨hlt, hfixed.2.1⟩⟩
    have hnewFocus := highestCritical_isFocus
      (fallback := old.focus) hne
    simpa [stableDecision, hwait, newScope] using hnewFocus
  · simpa [stableDecision, hwait] using hfixed

/-- In an expansion round the selected focus is never below the old focus. -/
theorem stableDecision_focus_le
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hfocus : IsFocus C stream t old.scope old.focus)
    (hsurvives : Consistent C stream (t + 1) old.focus) :
    old.focus ≤ (stableDecision C stream t old).focus := by
  classical
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · have hnew := stableDecision_isFocus hfocus hsurvives
    have holdNew : RecursiveCritical C stream (t + 1) old.focus :=
      (focus_next_of_consistent hfocus hsurvives).2.1
    have hlt : old.focus < (stableDecision C stream t old).scope := by
      simpa [stableDecision, hwait] using
        (lt_of_lt_of_le hfocus.1 (Nat.le_succ old.scope))
    exact hnew.2.2 old.focus hlt holdNew
  · simp [stableDecision, hwait]

/-- A stable-branch focus change can only move to the newly admitted index.
It therefore certifies that the exponential waiting condition was met. -/
theorem stableDecision_changed
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hfocus : IsFocus C stream t old.scope old.focus)
    (hsurvives : Consistent C stream (t + 1) old.focus)
    (hchanged : (stableDecision C stream t old).focus ≠ old.focus) :
    2 ^ old.tau ≤ old.age ∧
      (stableDecision C stream t old).focus = old.scope := by
  classical
  have hwait : 2 ^ old.tau ≤ old.age := by
    by_contra hnot
    exact hchanged (by simp [stableDecision, hnot])
  have hnew := stableDecision_isFocus hfocus hsurvives
  have hle : (stableDecision C stream t old).focus ≤ old.scope := by
    have hlt : (stableDecision C stream t old).focus < old.scope + 1 := by
      simpa [stableDecision, hwait] using hnew.1
    exact Nat.le_of_lt_succ hlt
  have hnotlt : ¬ (stableDecision C stream t old).focus < old.scope := by
    intro hlt
    have hfixed := focus_next_of_consistent hfocus hsurvives
    have hcrit := hnew.2.1
    have hbelow : (stableDecision C stream t old).focus ≤ old.focus :=
      hfixed.2.2 _ hlt hcrit
    have habove := stableDecision_focus_le hfocus hsurvives
    exact hchanged (Nat.le_antisymm hbelow habove)
  exact ⟨hwait, Nat.le_antisymm hle (Nat.le_of_not_gt hnotlt)⟩

/-- Backtracking always increments `tau` and records its branch. -/
@[simp] theorem backtrackDecision_tau
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (backtrackDecision C stream t old).tau = old.tau + 1 := by
  classical
  by_cases hcon : (consistentIndices C stream (t + 1) old.scope).Nonempty
  · simp [backtrackDecision, hcon]
  · by_cases hall : ∃ j, Consistent C stream (t + 1) j <;>
      simp [backtrackDecision, hcon, hall]

@[simp] theorem backtrackDecision_move
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (backtrackDecision C stream t old).move = .backtrack := by
  classical
  by_cases hcon : (consistentIndices C stream (t + 1) old.scope).Nonempty
  · simp [backtrackDecision, hcon]
  · by_cases hall : ∃ j, Consistent C stream (t + 1) j <;>
      simp [backtrackDecision, hcon, hall]

/-- Backtracking returns a genuine focus whenever some language in the whole
family remains consistent. -/
theorem backtrackDecision_isFocus
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hexists : ∃ i, Consistent C stream (t + 1) i) :
    IsFocus C stream (t + 1)
      (backtrackDecision C stream t old).scope
      (backtrackDecision C stream t old).focus := by
  classical
  let consistent := consistentIndices C stream (t + 1) old.scope
  by_cases hcon : consistent.Nonempty
  · let survivors := survivingCriticalIndices C stream t old.scope
    by_cases hsurv : survivors.Nonempty
    · let i := highestSurvivor C stream t old.scope old.focus
      have hi := highestSurvivor_spec (fallback := old.focus) hsurv
      have hifocus : IsFocus C stream (t + 1) (i + 1) i := by
        refine ⟨Nat.lt_succ_self i, hi.2.2.1, ?_⟩
        intro j hj _
        exact Nat.le_of_lt_succ hj
      simpa [backtrackDecision, consistent, hcon, survivors, hsurv, i]
        using hifocus
    · let i := lowestConsistentInScope C stream (t + 1)
        old.scope old.focus
      have hi := lowestConsistentInScope_spec
        (fallback := old.focus) hcon
      have hicrit : RecursiveCritical C stream (t + 1) i :=
        recursiveCritical_of_consistent_of_minimal hi.2.1 hi.2.2
      have hifocus : IsFocus C stream (t + 1) (i + 1) i := by
        exact ⟨Nat.lt_succ_self i, hicrit,
          fun j hj _ => Nat.le_of_lt_succ hj⟩
      simpa [backtrackDecision, consistent, hcon, survivors, hsurv, i]
        using hifocus
  · let i := lowestConsistent C stream (t + 1) old.focus
    have hi := lowestConsistent_spec (fallback := old.focus) hexists
    have hicrit : RecursiveCritical C stream (t + 1) i :=
      recursiveCritical_of_consistent_of_minimal hi.1 hi.2
    have hifocus : IsFocus C stream (t + 1) (i + 1) i := by
      exact ⟨Nat.lt_succ_self i, hicrit,
        fun j hj _ => Nat.le_of_lt_succ hj⟩
    simpa [backtrackDecision, consistent, hcon, hexists, i]
      using hifocus

theorem backtrackDecision_of_survivor
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hcon : (consistentIndices C stream (t + 1) old.scope).Nonempty)
    (hsurv : (survivingCriticalIndices C stream t old.scope).Nonempty) :
    backtrackDecision C stream t old =
      let i := highestSurvivor C stream t old.scope old.focus
      ⟨i + 1, old.tau + 1, i, .backtrack⟩ := by
  classical
  simp [backtrackDecision, hcon, hsurv]

theorem backtrackDecision_of_no_survivor
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hcon : (consistentIndices C stream (t + 1) old.scope).Nonempty)
    (hsurv : ¬ (survivingCriticalIndices C stream t old.scope).Nonempty) :
    backtrackDecision C stream t old =
      let i := lowestConsistentInScope C stream (t + 1)
        old.scope old.focus
      ⟨i + 1, old.tau + 1, i, .backtrack⟩ := by
  classical
  simp [backtrackDecision, hcon, hsurv]

theorem backtrackDecision_of_empty_scope
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hcon : ¬ (consistentIndices C stream (t + 1) old.scope).Nonempty)
    (hexists : ∃ i, Consistent C stream (t + 1) i) :
    backtrackDecision C stream t old =
      let i := lowestConsistent C stream (t + 1) old.focus
      ⟨i + 1, old.tau + 1, i, .backtrack⟩ := by
  classical
  simp [backtrackDecision, hcon, hexists]

/-- With a surviving old critical language, backtracking lands strictly below
the falsified old focus. -/
theorem backtrackDecision_focus_lt_of_survivor
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hfocus : IsFocus C stream t old.scope old.focus)
    (hfalsified : ¬ Consistent C stream (t + 1) old.focus)
    (hcon : (consistentIndices C stream (t + 1) old.scope).Nonempty)
    (hsurv : (survivingCriticalIndices C stream t old.scope).Nonempty) :
    (backtrackDecision C stream t old).focus < old.focus := by
  classical
  let i := highestSurvivor C stream t old.scope old.focus
  have hi := highestSurvivor_spec (fallback := old.focus) hsurv
  have hile : i ≤ old.focus := hfocus.2.2 i hi.1 hi.2.1
  have hine : i ≠ old.focus := by
    intro hieq
    apply hfalsified
    rw [← hieq]
    exact recursiveCritical_consistent hi.2.2.1
  have hilt : i < old.focus := lt_of_le_of_ne hile hine
  simpa [backtrackDecision_of_survivor hcon hsurv, i] using hilt

/-- If no consistent language remains in the old scope, the selected global
minimum lies weakly beyond that scope. -/
theorem backtrackDecision_scope_le_focus_of_empty
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hcon : ¬ (consistentIndices C stream (t + 1) old.scope).Nonempty)
    (hexists : ∃ i, Consistent C stream (t + 1) i) :
    old.scope ≤ (backtrackDecision C stream t old).focus := by
  classical
  let i := lowestConsistent C stream (t + 1) old.focus
  have hi := (lowestConsistent_spec (fallback := old.focus) hexists).1
  have hnotlt : ¬ i < old.scope := by
    intro hlt
    apply hcon
    exact ⟨i, mem_consistentIndices.mpr ⟨hlt, hi⟩⟩
  have hiscope : old.scope ≤ i := Nat.le_of_not_gt hnotlt
  simpa [backtrackDecision_of_empty_scope hcon hexists, i] using hiscope

@[simp] theorem stableDecision_tau
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (stableDecision C stream t old).tau =
      if (stableDecision C stream t old).focus = old.focus then
        old.tau else old.tau + 1 := by
  classical
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · simp [stableDecision, hwait]
  · simp [stableDecision, hwait]

theorem stableDecision_tau_mono
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    old.tau ≤ (stableDecision C stream t old).tau := by
  classical
  rw [stableDecision_tau]
  split <;> omega

/-- The complete focus decision is well-formed under the abstract on-model
condition that at least one language remains consistent. -/
theorem decide_isFocus
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hfocus : IsFocus C stream t old.scope old.focus)
    (hexists : ∃ i, Consistent C stream (t + 1) i) :
    IsFocus C stream (t + 1)
      (decide C stream t old).scope
      (decide C stream t old).focus := by
  classical
  by_cases hcon : Consistent C stream (t + 1) old.focus
  · simpa [decide, hcon] using stableDecision_isFocus hfocus hcon
  · simpa [decide, hcon] using backtrackDecision_isFocus hexists

theorem decide_tau_mono
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    old.tau ≤ (decide C stream t old).tau := by
  classical
  by_cases hcon : Consistent C stream (t + 1) old.focus
  · simpa [decide, hcon] using stableDecision_tau_mono C stream t old
  · simp [decide, hcon]

/-- On model, `tau` stays fixed exactly when the focus stays fixed; otherwise
it increases by one. -/
theorem decide_tau_eq_focus_test
    {C : LanguageFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hfocus : IsFocus C stream t old.scope old.focus)
    (hexists : ∃ i, Consistent C stream (t + 1) i) :
    (decide C stream t old).tau =
      if (decide C stream t old).focus = old.focus then
        old.tau else old.tau + 1 := by
  classical
  by_cases hcon : Consistent C stream (t + 1) old.focus
  · simp [decide, hcon, stableDecision_tau]
  · have hnewFocus := decide_isFocus hfocus hexists
    have hnewCon := recursiveCritical_consistent hnewFocus.2.1
    have hne : (decide C stream t old).focus ≠ old.focus := by
      intro heq
      exact hcon (heq ▸ hnewCon)
    have hneBack : (backtrackDecision C stream t old).focus ≠ old.focus := by
      simpa [decide, hcon] using hne
    simp [decide, hcon, hneBack]

@[simp] theorem processRound_scope
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (processRound O stream t old).scope =
      (decide O.language stream t old).scope := by
  simp [processRound]

@[simp] theorem processRound_tau
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (processRound O stream t old).tau =
      (decide O.language stream t old).tau := by
  simp [processRound]

@[simp] theorem processRound_focus
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (processRound O stream t old).focus =
      (decide O.language stream t old).focus := by
  simp [processRound]

@[simp] theorem processRound_age
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (processRound O stream t old).age =
      if (decide O.language stream t old).focus = old.focus then
        old.age + 1 else 1 := by
  simp [processRound]

@[simp] theorem processRound_move
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (processRound O stream t old).move =
      (decide O.language stream t old).move := by
  simp [processRound]

@[simp] theorem processRound_used
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (processRound O stream t old).used =
      insert
        (leastAvailable O.language O.infinite' stream (t + 1) old.used
          (decide O.language stream t old).focus)
        old.used := by
  simp [processRound]

@[simp] theorem run_succ_scope
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (run O stream (t + 1)).scope =
      (decide O.language stream t (run O stream t)).scope := by
  simp

@[simp] theorem run_succ_tau
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (run O stream (t + 1)).tau =
      (decide O.language stream t (run O stream t)).tau := by
  simp

@[simp] theorem run_succ_focus
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (run O stream (t + 1)).focus =
      (decide O.language stream t (run O stream t)).focus := by
  simp

@[simp] theorem run_succ_age
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (run O stream (t + 1)).age =
      if (run O stream (t + 1)).focus = (run O stream t).focus then
        (run O stream t).age + 1 else 1 := by
  simp

@[simp] theorem run_succ_move
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (run O stream (t + 1)).move =
      (decide O.language stream t (run O stream t)).move := by
  simp

/-- The semantic machine is on-model when at least one candidate language is
consistent after every finite observation prefix.  Exact presentation of a
family member is one sufficient condition, but partial enumeration supplies
the same invariant without presenting any member of the family exactly. -/
def OnModel (O : OracleFamily) (stream : ℕ → ℕ) : Prop :=
  ∀ t, ∃ i, Consistent O.language stream t i

/-- The semantic machine's focus is well-formed whenever the run is
on-model. -/
theorem run_focus_isFocus_of_onModel
    (O : OracleFamily) {stream : ℕ → ℕ}
    (hOn : OnModel O stream) :
    ∀ t, IsFocus O.language stream t
      (run O stream t).scope (run O stream t).focus := by
  intro t
  induction t with
  | zero => simpa using initial_focus_isFocus O.language stream
  | succ t ih =>
      have hexists : ∃ i, Consistent O.language stream (t + 1) i :=
        hOn (t + 1)
      have hnext := decide_isFocus ih hexists
      simpa using hnext

/-- An exact presentation of a family member is an on-model run. -/
theorem onModel_of_presents
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) : OnModel O stream := by
  intro t
  exact ⟨z, presents_consistent hP⟩

/-- The semantic machine's focus is well-formed at every time along a target
presentation. -/
theorem run_focus_isFocus
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    ∀ t, IsFocus O.language stream t
      (run O stream t).scope (run O stream t).focus :=
  run_focus_isFocus_of_onModel O (onModel_of_presents O hP)

theorem run_scope_pos
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) (t : ℕ) :
    0 < (run O stream t).scope := by
  have hf := run_focus_isFocus O hP t
  exact lt_of_le_of_lt (Nat.zero_le _) hf.1

theorem run_tau_step_mono
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (run O stream t).tau ≤ (run O stream (t + 1)).tau := by
  simpa using decide_tau_mono O.language stream t (run O stream t)

theorem run_tau_pos
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    0 < (run O stream t).tau := by
  induction t with
  | zero => simp [initialState]
  | succ t ih => exact lt_of_lt_of_le ih (run_tau_step_mono O stream t)

theorem run_age_pos_succ
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    0 < (run O stream (t + 1)).age := by
  rw [run_succ_age]
  split <;> omega

theorem run_tau_eq_focus_test
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) (t : ℕ) :
    (run O stream (t + 1)).tau =
      if (run O stream (t + 1)).focus = (run O stream t).focus then
        (run O stream t).tau else (run O stream t).tau + 1 := by
  have hfocus := run_focus_isFocus O hP t
  have hexists : ∃ i, Consistent O.language stream (t + 1) i :=
    ⟨z, presents_consistent hP⟩
  have htau := decide_tau_eq_focus_test hfocus hexists
  simpa using htau

theorem run_tau_succ_eq_iff_focus_eq
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) (t : ℕ) :
    (run O stream (t + 1)).tau = (run O stream t).tau ↔
      (run O stream (t + 1)).focus = (run O stream t).focus := by
  rw [run_tau_eq_focus_test O hP t]
  split <;> rename_i h
  · simpa using h
  · omega

theorem run_tau_succ_eq_add_one_iff_focus_ne
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) (t : ℕ) :
    (run O stream (t + 1)).tau = (run O stream t).tau + 1 ↔
      (run O stream (t + 1)).focus ≠ (run O stream t).focus := by
  rw [run_tau_eq_focus_test O hP t]
  split
  · omega
  · simp_all

/-- The finite set of outputs in rounds strictly before `t`. -/
noncomputable def outputsBefore
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range t).image (output O stream)

theorem run_used_eq_outputsBefore
    (O : OracleFamily) (stream : ℕ → ℕ) :
    ∀ t, (run O stream t).used = outputsBefore O stream t := by
  intro t
  induction t with
  | zero => simp [outputsBefore, initialState]
  | succ t ih =>
      simp [outputsBefore, Finset.range_add_one, processRound, ih,
        output_eq_leastAvailable]

theorem output_mem_run_used
    (O : OracleFamily) (stream : ℕ → ℕ) {s t : ℕ} (hst : s < t) :
    output O stream s ∈ (run O stream t).used := by
  rw [run_used_eq_outputsBefore]
  exact Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr hst, rfl⟩

theorem output_not_mem_sample
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    output O stream t ∉ sample stream (t + 1) :=
  (output_available O stream t).2.1

theorem output_not_mem_prior_used
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    output O stream t ∉ (run O stream t).used :=
  (output_available O stream t).2.2

theorem output_mem_round_focus
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    output O stream t ∈ O.language (run O stream (t + 1)).focus := by
  simpa using (output_available O stream t).1

/-- Generator announcements are pairwise distinct. -/
theorem output_ne_of_lt
    (O : OracleFamily) (stream : ℕ → ℕ) {s t : ℕ} (hst : s < t) :
    output O stream s ≠ output O stream t := by
  intro heq
  have hmem := output_mem_run_used O stream hst
  rw [heq] at hmem
  exact output_not_mem_prior_used O stream t hmem

/-- The round-`t` generator output differs from every adversary announcement
through round `t`. -/
theorem stream_ne_output
    (O : OracleFamily) (stream : ℕ → ℕ) (t s : ℕ) (hst : s ≤ t) :
    stream s ≠ output O stream t := by
  intro heq
  have hmem : stream s ∈ sample stream (t + 1) :=
    value_mem_sample (Nat.lt_succ_of_le hst)
  rw [heq] at hmem
  exact output_not_mem_sample O stream t hmem

end PatientMachine
end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Patient.History
section
set_option autoImplicit true

/-!
# Recurrence and history facts for the patient-scope machine

This module derives facts that depend only on the recurrence in
`PatientMachine.processRound`.  They are kept separate from the semantic
focus/scope invariants used to prove eventual validity.

Because `PatientMachine` is total on arbitrary streams, its off-model
backtracking fallback can increment `tau` while retaining the old focus when
no consistent language exists.  Thus the unrestricted converse “unchanged
focus implies unchanged `tau`” is false.  Below it is stated under the natural
condition that the old focus remains consistent; a presentation-dependent
version can instead discharge the off-model branch using existence of the
true consistent language.
-/

namespace GenLimit
namespace PatientMachine

/-- A stable-focus decision either preserves `tau` or increments it once. -/
theorem stableDecision_tau_cases
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    let d := stableDecision C stream t old
    d.tau = old.tau ∨ d.tau = old.tau + 1 := by
  classical
  simp only [stableDecision]
  split
  · dsimp
    split <;> simp
  · simp

/-- A focus change made by the stable branch increments `tau` exactly once. -/
theorem stableDecision_tau_eq_succ_of_focus_ne
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hfocus : (stableDecision C stream t old).focus ≠ old.focus) :
    (stableDecision C stream t old).tau = old.tau + 1 := by
  classical
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · by_cases heq :
        highestCritical C stream (t + 1) (old.scope + 1) old.focus =
          old.focus
    · simp [stableDecision, hwait, heq] at hfocus
    · simp [stableDecision, hwait, heq]
  · simp [stableDecision, hwait] at hfocus

/-- If the stable branch retains the focus, it retains `tau`. -/
theorem stableDecision_tau_eq_of_focus_eq
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hfocus : (stableDecision C stream t old).focus = old.focus) :
    (stableDecision C stream t old).tau = old.tau := by
  classical
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · have heq :
        highestCritical C stream (t + 1) (old.scope + 1) old.focus =
          old.focus := by
      simpa [stableDecision, hwait] using hfocus
    simp [stableDecision, hwait, heq]
  · simp [stableDecision, hwait]

/-- If at least one language is consistent, the focus selected by
backtracking is consistent.  This excludes only the explicitly totalized
off-model fallback. -/
theorem backtrackDecision_focus_consistent_of_exists
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hall : ∃ i, Consistent C stream (t + 1) i) :
    Consistent C stream (t + 1)
      (backtrackDecision C stream t old).focus := by
  classical
  by_cases hcon : (consistentIndices C stream (t + 1) old.scope).Nonempty
  · by_cases hsurv :
        (survivingCriticalIndices C stream t old.scope).Nonempty
    · have hspec := highestSurvivor_spec
          (C := C) (stream := stream) (t := t) (scope := old.scope)
          (fallback := old.focus) hsurv
      have hcrit : RecursiveCritical C stream (t + 1)
          (highestSurvivor C stream t old.scope old.focus) := hspec.2.2.1
      have hfocus :
          (backtrackDecision C stream t old).focus =
            highestSurvivor C stream t old.scope old.focus := by
        simp [backtrackDecision, hcon, hsurv, highestSurvivor]
      rw [hfocus]
      exact recursiveCritical_consistent hcrit
    · have hspec := lowestConsistentInScope_spec
          (C := C) (stream := stream) (t := t + 1)
          (scope := old.scope) (fallback := old.focus) hcon
      have hfocus :
          (backtrackDecision C stream t old).focus =
            lowestConsistentInScope C stream (t + 1) old.scope old.focus := by
        simp [backtrackDecision, hcon, hsurv, lowestConsistentInScope]
      rw [hfocus]
      exact hspec.2.1
  · have hspec := lowestConsistent_spec
        (C := C) (stream := stream) (t := t + 1)
        (fallback := old.focus) hall
    have hfocus :
        (backtrackDecision C stream t old).focus =
          lowestConsistent C stream (t + 1) old.focus := by
      simp [backtrackDecision, hcon, hall]
    rw [hfocus]
    exact hspec.1

/-- Every decision either preserves `tau` or increments it once. -/
theorem decide_tau_cases
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    let d := decide C stream t old
    d.tau = old.tau ∨ d.tau = old.tau + 1 := by
  classical
  simp only [decide]
  split
  · exact stableDecision_tau_cases C stream t old
  · exact Or.inr (backtrackDecision_tau C stream t old)

/-- Any decision which changes focus increments `tau` exactly once. -/
theorem decide_tau_eq_succ_of_focus_ne
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hfocus : (decide C stream t old).focus ≠ old.focus) :
    (decide C stream t old).tau = old.tau + 1 := by
  classical
  by_cases hcon : Consistent C stream (t + 1) old.focus
  · have hfocus' :
        (stableDecision C stream t old).focus ≠ old.focus := by
      simpa [decide, hcon] using hfocus
    simpa [decide, hcon] using
      stableDecision_tau_eq_succ_of_focus_ne C stream t old hfocus'
  · simp [decide, hcon]

/-- When the old focus remains consistent, an unchanged focus implies an
unchanged `tau`; this excludes the backtracking fallback. -/
theorem decide_tau_eq_of_focus_eq_of_consistent
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hcon : Consistent C stream (t + 1) old.focus)
    (hfocus : (decide C stream t old).focus = old.focus) :
    (decide C stream t old).tau = old.tau := by
  classical
  rw [decide, if_pos hcon] at hfocus ⊢
  exact stableDecision_tau_eq_of_focus_eq C stream t old hfocus

/-- In any on-model round with at least one consistent language, retaining
the focus is equivalent, as far as the recurrence is concerned, to retaining
`tau`. -/
theorem decide_tau_eq_of_focus_eq_of_exists_consistent
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hall : ∃ i, Consistent C stream (t + 1) i)
    (hfocus : (decide C stream t old).focus = old.focus) :
    (decide C stream t old).tau = old.tau := by
  classical
  by_cases hcon : Consistent C stream (t + 1) old.focus
  · exact decide_tau_eq_of_focus_eq_of_consistent
      C stream t old hcon hfocus
  · have hbackFocus :
        (backtrackDecision C stream t old).focus = old.focus := by
      simpa [decide, hcon] using hfocus
    have hbackCon :=
      backtrackDecision_focus_consistent_of_exists C stream t old hall
    rw [hbackFocus] at hbackCon
    exact False.elim (hcon hbackCon)

/-- A completed round either preserves `tau` or increments it once. -/
theorem processRound_tau_cases
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (processRound O stream t old).tau = old.tau ∨
      (processRound O stream t old).tau = old.tau + 1 := by
  simpa only [processRound] using
    decide_tau_cases O.language stream t old

/-- `tau` never decreases in one completed round. -/
theorem processRound_tau_mono
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    old.tau ≤ (processRound O stream t old).tau := by
  rcases processRound_tau_cases O stream t old with h | h
  · omega
  · omega

/-- A round which changes focus increments `tau` exactly once. -/
theorem processRound_tau_eq_succ_of_focus_ne
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hfocus : (processRound O stream t old).focus ≠ old.focus) :
    (processRound O stream t old).tau = old.tau + 1 := by
  apply decide_tau_eq_succ_of_focus_ne O.language stream t old
  simpa only [processRound] using hfocus

/-- On the consistent-focus branch, a round which retains the focus also
retains `tau`. -/
theorem processRound_tau_eq_of_focus_eq_of_consistent
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hcon : Consistent O.language stream (t + 1) old.focus)
    (hfocus : (processRound O stream t old).focus = old.focus) :
    (processRound O stream t old).tau = old.tau := by
  apply decide_tau_eq_of_focus_eq_of_consistent
    O.language stream t old hcon
  simpa only [processRound] using hfocus

/-- In an on-model round with a consistent candidate somewhere in the
family, an unchanged focus implies unchanged `tau`. -/
theorem processRound_tau_eq_of_focus_eq_of_exists_consistent
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State)
    (hall : ∃ i, Consistent O.language stream (t + 1) i)
    (hfocus : (processRound O stream t old).focus = old.focus) :
    (processRound O stream t old).tau = old.tau := by
  apply decide_tau_eq_of_focus_eq_of_exists_consistent
    O.language stream t old hall
  simpa only [processRound] using hfocus

/-- `tau` is globally monotone along the run. -/
theorem run_tau_mono
    (O : OracleFamily) (stream : ℕ → ℕ) {s t : ℕ} (hst : s ≤ t) :
    (run O stream s).tau ≤ (run O stream t).tau := by
  induction t generalizing s with
  | zero =>
      have hs : s = 0 := Nat.eq_zero_of_le_zero hst
      subst s
      exact Nat.le_refl _
  | succ t ih =>
      rcases eq_or_lt_of_le hst with hEq | hlt
      · subst s
        exact Nat.le_refl _
      · exact le_trans (ih (Nat.le_of_lt_succ hlt))
          (run_tau_step_mono O stream t)

/-- A focus change between consecutive run states increments `tau` exactly
once. -/
theorem run_succ_tau_eq_succ_of_focus_ne
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ)
    (hfocus : (run O stream (t + 1)).focus ≠
      (run O stream t).focus) :
    (run O stream (t + 1)).tau = (run O stream t).tau + 1 := by
  rw [run_succ] at hfocus ⊢
  exact processRound_tau_eq_succ_of_focus_ne
    O stream t (run O stream t) hfocus

/-- Along a genuine presentation, an unchanged focus between consecutive run
states implies unchanged `tau`. -/
theorem run_succ_tau_eq_of_focus_eq
    (O : OracleFamily) (stream : ℕ → ℕ) {z t : ℕ}
    (hP : Presents stream (O.language z))
    (hfocus : (run O stream (t + 1)).focus =
      (run O stream t).focus) :
    (run O stream (t + 1)).tau = (run O stream t).tau := by
  rw [run_succ] at hfocus ⊢
  apply processRound_tau_eq_of_focus_eq_of_exists_consistent
    O stream t (run O stream t) ⟨z, presents_consistent hP⟩ hfocus

/-- The recorded age never exceeds the number of completed rounds. -/
theorem run_age_le_time
    (O : OracleFamily) (stream : ℕ → ℕ) :
    ∀ t, (run O stream t).age ≤ t := by
  intro t
  induction t with
  | zero => simp [initialState]
  | succ t ih =>
      classical
      rw [run_succ]
      simp [processRound]
      split <;> omega

/-- Looking back fewer than `age` completed rounds reaches a post-state with
the same focus.  The indices `t - k`, for `k < age`, are exactly the last
`age` completed-round post-states, including the current state at `k = 0`. -/
theorem run_focus_eq_of_lt_age
    (O : OracleFamily) (stream : ℕ → ℕ) :
    ∀ t k, k < (run O stream t).age →
      (run O stream (t - k)).focus = (run O stream t).focus := by
  intro t
  induction t with
  | zero =>
      intro k hk
      simp [initialState] at hk
  | succ t ih =>
      intro k hk
      classical
      by_cases hk0 : k = 0
      · subst k
        simp
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        by_cases hsame :
            (decide O.language stream t (run O stream t)).focus =
              (run O stream t).focus
        ·
          simp [run_succ, processRound, hsame] at hk
          have hj : j < (run O stream t).age := by omega
          have hprev := ih j hj
          simpa [run_succ, processRound, hsame] using hprev
        · have hage : (run O stream (t + 1)).age = 1 := by
            simp [run_succ, processRound, hsame]
          omega

/-- The used set recurrence inserts precisely the output of the new round. -/
theorem run_succ_used
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (run O stream (t + 1)).used =
      insert (output O stream t) (run O stream t).used := by
  classical
  rw [run_succ]
  simp [processRound, output_eq_leastAvailable]

/-- Membership in `used` is equivalent to occurrence as an earlier output. -/
theorem mem_run_used_iff
    (O : OracleFamily) (stream : ℕ → ℕ) {t x : ℕ} :
    x ∈ (run O stream t).used ↔
      ∃ r, r < t ∧ output O stream r = x := by
  classical
  rw [run_used_eq_outputsBefore]
  simp [outputsBefore]

/-- Generator outputs never repeat. -/
theorem output_injective
    (O : OracleFamily) (stream : ℕ → ℕ) :
    Function.Injective (output O stream) := by
  intro r t hrt
  rcases lt_trichotomy r t with hlt | heq | hgt
  · have hmem : output O stream r ∈ (run O stream t).used :=
      mem_run_used_iff O stream |>.2 ⟨r, hlt, rfl⟩
    have hfresh := output_not_mem_prior_used O stream t
    exact False.elim (hfresh (hrt ▸ hmem))
  · exact heq
  · have hmem : output O stream t ∈ (run O stream r).used :=
      mem_run_used_iff O stream |>.2 ⟨t, hgt, rfl⟩
    have hfresh := output_not_mem_prior_used O stream r
    exact False.elim (hfresh (hrt.symm ▸ hmem))

end PatientMachine
end GenLimit

end

-- GenLimit.Core.GenericGeneration
section
set_option autoImplicit true

/-!
# A generic countable-universe interface

The original core fixes the universe to `ℕ`, as in the finite-query
Kleinberg--Mullainathan construction. Many later papers state their results
over an arbitrary countable example space. This file supplies that generic
paper-facing layer without changing the existing API.

A finite history of length `t` is represented by `Fin t → α`. Thus a
`Generator α` is literally a function on finite sequences, while
`output G stream t` exposes only the prefix strictly before time `t`.
-/

namespace GenLimit.Generic

/-- A language over an arbitrary example type. -/
abbrev Language (α : Type*) := Set α

/-- A possibly uncountable class of languages. -/
abbrev LanguageClass (α : Type*) := Set (Language α)

/-- An enumerated countable family of languages.  Unlike `LanguageClass`,
this representation preserves the paper's index order and repetitions. -/
abbrev LanguageFamily (α : Type*) := ℕ → Language α

/-- An infinite stream of examples. -/
abbrev Stream (α : Type*) := ℕ → α

/-- A causal operator whose output at time `t` depends on exactly the finite
history strictly before `t`.  Element generators, set generators,
identifiers, detectors, and randomized generators are specializations of
this common interface. -/
abbrev FiniteHistoryOperator (Input Output : Type*) :=
  ∀ t : ℕ, (Fin t → Input) → Output

/-- A generator is a map from each finite sequence to one new example. -/
abbrev Generator (α : Type*) := FiniteHistoryOperator α α

/-- Run a finite-history operator on the prefix of a stream. -/
def historyOutput
    (op : FiniteHistoryOperator α β) (stream : Stream α) (t : ℕ) : β :=
  op t (fun i => stream i)

/-- Exact presentation: repetitions are allowed, and every target element
must eventually occur. -/
def Presents (stream : Stream α) (L : Language α) : Prop :=
  Set.range stream = L

/-- Every element ever shown by the stream belongs to `L`. -/
def StreamIn (stream : Stream α) (L : Language α) : Prop :=
  Set.range stream ⊆ L

/-- The distinct values in a finite sequence. -/
noncomputable def sequenceSample {t : ℕ} (xs : Fin t → α) : Finset α := by
  classical
  exact Finset.univ.image xs

/-- The distinct observations strictly before time `t`. -/
noncomputable def sample (stream : Stream α) (t : ℕ) : Finset α := by
  classical
  exact (Finset.range t).image stream

/-- The stream that follows a finite history and then repeats a fallback
value forever. -/
def historyThenFallback (history : List α) (fallback : α) : Stream α :=
  fun n => if h : n < history.length then history.get ⟨n, h⟩ else fallback

/-- A finite history followed by a fallback stays in a language when both
the history and fallback do. -/
theorem streamIn_historyThenFallback
    {history : List α} {fallback : α} {L : Language α}
    (hhistory : ∀ x ∈ history, x ∈ L)
    (hfallback : fallback ∈ L) :
    StreamIn (historyThenFallback history fallback) L := by
  rintro _ ⟨n, rfl⟩
  by_cases hn : n < history.length
  · rw [historyThenFallback, dif_pos hn]
    exact hhistory _ (List.get_mem history ⟨n, hn⟩)
  · rw [historyThenFallback, dif_neg hn]
    exact hfallback

/-- Run `G` on the prefix of `stream` strictly before time `t`. -/
def output (G : Generator α) (stream : Stream α) (t : ℕ) : α :=
  G t (fun i => stream i)

theorem mem_sequenceSample_iff {t : ℕ} {xs : Fin t → α} {x : α} :
    x ∈ sequenceSample xs ↔ ∃ i : Fin t, xs i = x := by
  classical
  simp [sequenceSample]

/-- Passing a list through its canonical `Fin`-indexed input recovers its
underlying finite set of values. -/
theorem sequenceSample_list_get [DecidableEq α] (xs : List α) :
    sequenceSample xs.get = xs.toFinset := by
  classical
  ext x
  rw [mem_sequenceSample_iff, List.mem_toFinset, List.mem_iff_get]

/-- An injective finite history has as many distinct observations as
positions. -/
theorem sequenceSample_card_of_injective
    {t : ℕ} (xs : Fin t → α) (hxs : Function.Injective xs) :
    (sequenceSample xs).card = t := by
  classical
  rw [sequenceSample, Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    exact hxs hij

/-- Pointwise membership of a finite history implies membership of every
element in its underlying sample. -/
theorem sequenceSample_subset_of_pointwise
    {t : ℕ} {xs : Fin t → α} {S : Set α}
    (hxs : ∀ k, xs k ∈ S) :
    (↑(sequenceSample xs) : Set α) ⊆ S := by
  intro x hx
  have hx' : x ∈ sequenceSample xs := hx
  rw [mem_sequenceSample_iff] at hx'
  obtain ⟨k, rfl⟩ := hx'
  exact hxs k

/-- Enumerating a finset through its canonical equivalence with `Fin`
recovers exactly that finset as the distinct sample. -/
theorem sequenceSample_equivFin_symm (S : Finset α) :
    sequenceSample (fun i : Fin S.card => (S.equivFin.symm i).1) = S := by
  classical
  ext x
  rw [mem_sequenceSample_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact (S.equivFin.symm i).2
  · intro hx
    let z : S := ⟨x, hx⟩
    refine ⟨S.equivFin z, ?_⟩
    change (S.equivFin.symm (S.equivFin z)).1 = x
    simp [z]

/-- The value map of a finset's canonical `Fin` enumeration is injective. -/
theorem equivFin_symm_value_injective (S : Finset α) :
    Function.Injective (fun i : Fin S.card => (S.equivFin.symm i).1) := by
  intro i j hij
  apply S.equivFin.symm.injective
  apply Subtype.ext
  exact hij

theorem mem_sample_iff {stream : Stream α} {t : ℕ} {x : α} :
    x ∈ sample stream t ↔ ∃ s < t, stream s = x := by
  classical
  simp [sample]

/-- An injective stream has exactly `t` distinct observations before round
`t`. -/
theorem sample_card_of_injective
    (stream : Stream α) (hstream : Function.Injective stream) (t : ℕ) :
    (sample stream t).card = t := by
  classical
  rw [sample, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    exact hstream hab

/-- Samples depend only on the corresponding finite stream prefix. -/
theorem sample_eq_of_eq_on_prefix
    {stream₁ stream₂ : Stream α} {t : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    sample stream₁ t = sample stream₂ t := by
  classical
  ext x
  simp only [mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

/-- Sampling a finite-history stream at the end of the history recovers
exactly the history's distinct values. -/
theorem sample_historyThenFallback_length [DecidableEq α]
    (history : List α) (fallback : α) :
    sample (historyThenFallback history fallback) history.length =
      history.toFinset := by
  classical
  ext x
  simp only [mem_sample_iff, List.mem_toFinset]
  constructor
  · rintro ⟨n, hn, hnx⟩
    apply List.mem_iff_get.mpr
    refine ⟨⟨n, hn⟩, ?_⟩
    simpa [historyThenFallback, hn] using hnx
  · intro hx
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
    refine ⟨i, i.isLt, ?_⟩
    simpa [historyThenFallback, i.isLt] using hi

theorem sequenceSample_prefix (stream : Stream α) (t : ℕ) :
    sequenceSample (fun i : Fin t => stream i) = sample stream t := by
  classical
  ext x
  simp only [mem_sequenceSample_iff, mem_sample_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, i.isLt, hi⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem sample_mono {stream : Stream α} {s t : ℕ} (hst : s ≤ t) :
    sample stream s ⊆ sample stream t := by
  intro x hx
  rw [mem_sample_iff] at hx ⊢
  obtain ⟨i, his, rfl⟩ := hx
  exact ⟨i, lt_of_lt_of_le his hst, rfl⟩

theorem value_mem_sample {stream : Stream α} {s t : ℕ} (hst : s < t) :
    stream s ∈ sample stream t := by
  rw [mem_sample_iff]
  exact ⟨s, hst, rfl⟩

theorem sample_card_step (stream : Stream α) (t : ℕ) :
    (sample stream (t + 1)).card ≤ (sample stream t).card + 1 := by
  classical
  have hsub : sample stream (t + 1) ⊆ insert (stream t) (sample stream t) := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_sample_iff.mp hx
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hst
    · exact Finset.mem_insert_of_mem (mem_sample_iff.mpr ⟨s, hs, hxs⟩)
    · subst s
      subst x
      exact @Finset.mem_insert_self α (Classical.decEq α) (stream t) (sample stream t)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)

/-- If a finite prefix contains at least `k` distinct observations, some
earlier prefix contains exactly `k`. -/
theorem exists_sample_card_eq_of_le
    {stream : Stream α} {t k : ℕ}
    (hk : k ≤ (sample stream t).card) :
    ∃ r ≤ t, (sample stream r).card = k := by
  classical
  let hex : ∃ r, k ≤ (sample stream r).card := ⟨t, hk⟩
  let r := Nat.find hex
  have hrLower : k ≤ (sample stream r).card := Nat.find_spec hex
  have hrt : r ≤ t := Nat.find_min' hex hk
  by_cases hr0 : r = 0
  · have hk0 : k = 0 := by
      rw [hr0] at hrLower
      simpa [sample] using hrLower
    exact ⟨0, by simp, by simp [sample, hk0]⟩
  · obtain ⟨s, hrs⟩ := Nat.exists_eq_succ_of_ne_zero hr0
    have hprevNot : ¬ k ≤ (sample stream s).card :=
      Nat.find_min hex (by
        change s < r
        rw [hrs]
        exact Nat.lt_succ_self s)
    have hprev : (sample stream s).card < k :=
      Nat.lt_of_not_ge hprevNot
    have hupper : (sample stream (s + 1)).card ≤ k :=
      (sample_card_step stream s).trans (Nat.succ_le_iff.mpr hprev)
    rw [hrs] at hrLower hrt
    exact ⟨s + 1, hrt, Nat.le_antisymm hupper hrLower⟩

/-- If every reached size can be crossed exactly, a property that holds
eventually after reaching exact size `d` also holds after reaching any larger
exact size. -/
theorem eventualAtExactSize_mono
    {size : ℕ → ℕ} {good : ℕ → Prop} {d n : ℕ}
    (hcross : ∀ {t k}, k ≤ size t → ∃ r ≤ t, size r = k)
    (hdn : d ≤ n)
    (hgood : ∀ t, size t = d → ∀ s, t ≤ s → good s) :
    ∀ t, size t = n → ∀ s, t ≤ s → good s := by
  intro t ht s hts
  have hdAtT : d ≤ size t := by
    rw [ht]
    exact hdn
  obtain ⟨r, hrt, hr⟩ := hcross hdAtT
  exact hgood r hr s (hrt.trans hts)

theorem sample_card_le (stream : Stream α) (t : ℕ) :
    (sample stream t).card ≤ t := by
  classical
  simpa [sample] using
    (Finset.card_image_le (s := Finset.range t) (f := stream))

theorem mem_language_of_mem_sample_of_presents
    {stream : Stream α} {L : Language α} (hP : Presents stream L)
    {t : ℕ} {x : α} (hx : x ∈ sample stream t) : x ∈ L := by
  rw [← hP]
  obtain ⟨s, -, rfl⟩ := mem_sample_iff.mp hx
  exact ⟨s, rfl⟩

theorem streamIn_of_presents
    {stream : Stream α} {L : Language α} (hP : Presents stream L) :
    StreamIn stream L := by
  intro x hx
  rw [← hP]
  exact hx

theorem eventually_mem_sample_of_presents
    {stream : Stream α} {L : Language α} (hP : Presents stream L)
    {x : α} (hx : x ∈ L) :
    ∃ T, ∀ t, T ≤ t → x ∈ sample stream t := by
  rw [← hP] at hx
  obtain ⟨s, rfl⟩ := hx
  refine ⟨s + 1, ?_⟩
  intro t ht
  exact value_mem_sample (lt_of_lt_of_le (Nat.lt_succ_self s) ht)

theorem finset_eventually_subset_sample
    {stream : Stream α} {L : Language α} (hP : Presents stream L)
    (S : Finset α) (hS : ↑S ⊆ L) :
    ∃ T, S ⊆ sample stream T := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert x S hxS ih =>
      have hxL : x ∈ L := hS (by simp)
      have hSL : (↑S : Set α) ⊆ L := by
        intro y hy
        exact hS (by simp [hy])
      obtain ⟨Tx, hTx⟩ := eventually_mem_sample_of_presents hP hxL
      obtain ⟨TS, hTS⟩ := ih hSL
      refine ⟨max Tx TS, ?_⟩
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact hTx _ (Nat.le_max_left _ _)
      · exact sample_mono (Nat.le_max_right _ _) (hTS hy)

theorem exists_sample_card_ge_of_presents_infinite
    {stream : Stream α} {L : Language α}
    (hP : Presents stream L) (hL : L.Infinite) (d : ℕ) :
    ∃ t, d ≤ (sample stream t).card := by
  classical
  obtain ⟨S, hSL, hcard⟩ := hL.exists_subset_card_eq d
  obtain ⟨T, hST⟩ := finset_eventually_subset_sample hP S hSL
  refine ⟨T, ?_⟩
  rw [← hcard]
  exact Finset.card_le_card hST

/-- An exact presentation of an infinite language passes through every finite
number of distinct observations. -/
theorem exists_sample_card_eq_of_presents_infinite
    {stream : Stream α} {L : Language α}
    (hP : Presents stream L) (hL : L.Infinite) (d : ℕ) :
    ∃ t, (sample stream t).card = d := by
  classical
  let hex : ∃ t, d ≤ (sample stream t).card :=
    exists_sample_card_ge_of_presents_infinite hP hL d
  have ht : d ≤ (sample stream (Nat.find hex)).card := Nat.find_spec hex
  by_cases ht0 : Nat.find hex = 0
  · rw [ht0] at ht
    have hd0 : d = 0 := by simpa [sample] using ht
    exact ⟨0, by simp [sample, hd0]⟩
  · obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero ht0
    have hprevNot : ¬d ≤ (sample stream s).card :=
      Nat.find_min hex (by rw [hs]; exact Nat.lt_succ_self s)
    have hprev : (sample stream s).card < d := Nat.lt_of_not_ge hprevNot
    have hupper : (sample stream (s + 1)).card ≤ d :=
      le_trans (sample_card_step stream s) (Nat.succ_le_iff.mpr hprev)
    rw [hs] at ht
    exact ⟨s + 1, Nat.le_antisymm hupper ht⟩

/-- The generated value is a fresh member of `L` at time `t`. -/
def CorrectAt
    (G : Generator α) (L : Language α) (stream : Stream α) (t : ℕ) : Prop :=
  output G stream t ∈ L ∧ output G stream t ∉ sample stream t

end GenLimit.Generic

end

-- GenLimit.Core.PartialPresentation
section
set_option autoImplicit true

/-!
# Partial presentations

The partial-enumeration model presents an infinite set `E` contained in the
true language, but `E` need not itself occur in the indexed family. This
module gives that paper-independent observation model a shared name and records
presentation-relative consistency facts without assuming that the presented
set has a family index.
-/

namespace GenLimit.Generic

/-- An infinite partial presentation of `K` is a stream with infinite range
whose observations all belong to `K`. Repetitions are allowed. -/
def InfinitePartialPresentation
    (stream : Stream α) (K : Language α) : Prop :=
  (Set.range stream).Infinite ∧ StreamIn stream K

/-- The range-based definition is equivalent to naming the infinite set
presented by the stream. This is the formulation used by Papers 15 and 39. -/
theorem infinitePartialPresentation_iff_exists_presented_subset
    (stream : Stream α) (K : Language α) :
    InfinitePartialPresentation stream K ↔
      ∃ E : Language α,
        Presents stream E ∧ E.Infinite ∧ E ⊆ K := by
  constructor
  · rintro ⟨hrange, hsub⟩
    exact ⟨Set.range stream, rfl, hrange, hsub⟩
  · rintro ⟨E, hP, hE, hsub⟩
    rw [← hP] at hE hsub
    exact ⟨hE, hsub⟩

end GenLimit.Generic

namespace GenLimit

/-- The `ℕ`-universe specialization used by the indexed-family Core API. -/
abbrev InfinitePartialPresentation
    (stream : ℕ → ℕ) (K : Language) : Prop :=
  Generic.InfinitePartialPresentation stream K

/-- The named-presented-set formulation of an infinite partial presentation
for the `ℕ`-universe API. -/
theorem infinitePartialPresentation_iff_exists_presented_subset
    (stream : ℕ → ℕ) (K : Language) :
    InfinitePartialPresentation stream K ↔
      ∃ E : Language, Presents stream E ∧ E.Infinite ∧ E ⊆ K := by
  exact Generic.infinitePartialPresentation_iff_exists_presented_subset
    stream K

/-- A candidate containing the presented set is consistent at every time. -/
theorem consistent_of_presented_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {E : Language} {i t : ℕ}
    (hP : Presents stream E) (hsub : E ⊆ C i) :
    Consistent C stream t i := by
  intro u hu
  exact hsub (mem_language_of_mem_sample_of_presents hP hu)

/-- A fixed candidate not containing the presented set is eventually
inconsistent. -/
theorem eventually_not_consistent_of_not_presented_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {E : Language} {i : ℕ}
    (hP : Presents stream E) (hbad : ¬ E ⊆ C i) :
    ∃ T, ∀ t, T ≤ t → ¬ Consistent C stream t i := by
  obtain ⟨u, huE, hui⟩ := Set.not_subset.mp hbad
  obtain ⟨T, hT⟩ := eventually_mem_sample_of_presents hP huE
  refine ⟨T, ?_⟩
  intro t ht hcon
  exact hui (hcon (hT t ht))

/-- For one fixed candidate, consistency eventually agrees with containment
of the presented set. -/
theorem candidate_eventually_consistent_iff_presented_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {E : Language} {i : ℕ}
    (hP : Presents stream E) :
    ∃ T, ∀ t, T ≤ t → (Consistent C stream t i ↔ E ⊆ C i) := by
  classical
  by_cases hsub : E ⊆ C i
  · exact ⟨0, fun _ _ =>
      ⟨fun _ => hsub, fun _ => consistent_of_presented_subset hP hsub⟩⟩
  · obtain ⟨T, hT⟩ :=
      eventually_not_consistent_of_not_presented_subset hP hsub
    refine ⟨T, ?_⟩
    intro t ht
    exact ⟨fun hcon => False.elim ((hT t ht) hcon),
      fun hsub' => False.elim (hsub hsub')⟩

/-- Uniform stabilization of consistency on a finite index prefix. -/
theorem finite_scope_eventually_consistent_iff_presented_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {E : Language}
    (hP : Presents stream E) (s : ℕ) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i < s →
      (Consistent C stream t i ↔ E ⊆ C i) := by
  induction s with
  | zero => exact ⟨0, by omega⟩
  | succ s ih =>
      obtain ⟨Ts, hTs⟩ := ih
      obtain ⟨Ti, hTi⟩ :=
        candidate_eventually_consistent_iff_presented_subset
          (C := C) (stream := stream) (E := E) (i := s) hP
      refine ⟨max Ts Ti, ?_⟩
      intro t ht i his
      rcases Nat.lt_succ_iff_lt_or_eq.mp his with his' | rfl
      · exact hTs t (le_trans (Nat.le_max_left _ _) ht) i his'
      · exact hTi t (le_trans (Nat.le_max_right _ _) ht)

end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Dynamics
section
set_option autoImplicit true

/-!
# Fixed-scope dynamics of recursive criticality

This module records the local invariants used by the patient-scope state
machine.  Consistency can only be lost as the sample grows.  Nevertheless, if
the current focus remains consistent, then every old critical language in the
same fixed scope remains consistent: the focus is contained in all earlier
critical languages.  The recursive definition of `RecursiveCritical` then
implies that every critical status, and hence the focus, is unchanged in that
scope.

The main results are stated for arbitrary times `t ≤ u`; the one-step version
`fixed_scope_one_step` specializes them to the arrival of one new sample.
-/

namespace GenLimit

/-- Consistency is antitone in time: a candidate consistent with a later
sample was consistent with every earlier sample. -/
theorem consistent_of_time_le
    {C : LanguageFamily} {stream : ℕ → ℕ} {t u i : ℕ}
    (htu : t ≤ u) (h : Consistent C stream u i) :
    Consistent C stream t i := by
  intro x hx
  exact h (sample_mono htu hx)

/-- If a later-indexed old critical language remains consistent, then every
earlier old critical language remains consistent as well.  This is the local
descending-chain argument behind the patient-scope focus invariant.

No ordering assumption on `t` and `u` is needed: the conclusion follows just
from the static inclusion `C f ⊆ C i` and consistency of `f` at `u`. -/
theorem old_critical_consistent_of_later_critical_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {t u i f : ℕ}
    (hif : i ≤ f)
    (hi : RecursiveCritical C stream t i)
    (hf : RecursiveCritical C stream t f)
    (hstay : Consistent C stream u f) :
    Consistent C stream u i := by
  intro x hx
  exact recursiveCritical_subset_of_le hif hi hf (hstay hx)

/-- If every old critical language in a finite scope remains consistent at a
later time, recursive criticality is unchanged throughout that scope.

This lemma isolates the induction on Definition 3.2.  The patient-scope
application below derives `hkeep` from consistency of the old focus. -/
theorem recursiveCritical_iff_of_old_critical_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {t u s : ℕ}
    (htu : t ≤ u)
    (hkeep : ∀ i, i < s → RecursiveCritical C stream t i →
      Consistent C stream u i) :
    ∀ i, i < s →
      (RecursiveCritical C stream u i ↔ RecursiveCritical C stream t i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro his
      cases i with
      | zero =>
          simp only [RecursiveCritical]
          constructor
          · exact consistent_of_time_le htu
          · intro hzero
            exact hkeep 0 his (by simpa only [RecursiveCritical] using hzero)
      | succ n =>
          rw [RecursiveCritical, RecursiveCritical]
          constructor
          · intro hnew
            refine ⟨consistent_of_time_le htu hnew.1, ?_⟩
            intro j hj hjold
            have hji : j < n + 1 := Nat.lt_succ_of_le hj
            have hjs : j < s := lt_trans hji his
            have hjnew : RecursiveCritical C stream u j :=
              (ih j hji hjs).2 hjold
            exact hnew.2 j hj hjnew
          · intro hold
            have hold' : RecursiveCritical C stream t (n + 1) := by
              simpa only [RecursiveCritical] using hold
            refine ⟨hkeep (n + 1) his hold', ?_⟩
            intro j hj hjnew
            have hji : j < n + 1 := Nat.lt_succ_of_le hj
            have hjs : j < s := lt_trans hji his
            have hjold : RecursiveCritical C stream t j :=
              (ih j hji hjs).1 hjnew
            exact hold.2 j hj hjold

/-- If the old focus remains consistent, all old critical languages in its
fixed scope remain consistent. -/
theorem old_critical_in_scope_consistent_of_focus_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {t u s f i : ℕ}
    (hf : IsFocus C stream t s f)
    (hi : i < s)
    (hicrit : RecursiveCritical C stream t i)
    (hstay : Consistent C stream u f) :
    Consistent C stream u i := by
  have hif : i ≤ f := hf.2.2 i hi hicrit
  exact old_critical_consistent_of_later_critical_consistent
    hif hicrit hf.2.1 hstay

/-- Stability of every critical status in a fixed scope when its old focus
remains consistent.  This version permits any later time `u`, not only the
next round. -/
theorem recursiveCritical_iff_of_focus_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {t u s f : ℕ}
    (htu : t ≤ u)
    (hf : IsFocus C stream t s f)
    (hstay : Consistent C stream u f) :
    ∀ i, i < s →
      (RecursiveCritical C stream u i ↔ RecursiveCritical C stream t i) := by
  apply recursiveCritical_iff_of_old_critical_consistent htu
  intro i hi hicrit
  exact old_critical_in_scope_consistent_of_focus_consistent
    hf hi hicrit hstay

/-- With a fixed scope, a focus which remains consistent is still the focus at
every later time. -/
theorem isFocus_of_consistent_at_later_time
    {C : LanguageFamily} {stream : ℕ → ℕ} {t u s f : ℕ}
    (htu : t ≤ u)
    (hf : IsFocus C stream t s f)
    (hstay : Consistent C stream u f) :
    IsFocus C stream u s f := by
  have hstable := recursiveCritical_iff_of_focus_consistent htu hf hstay
  refine ⟨hf.1, (hstable f hf.1).2 hf.2.1, ?_⟩
  intro j hjs hjcrit
  exact hf.2.2 j hjs ((hstable j hjs).1 hjcrit)

/-- A fixed finite scope has at most one highest-indexed critical language. -/
theorem isFocus_unique
    {C : LanguageFamily} {stream : ℕ → ℕ} {t s f g : ℕ}
    (hf : IsFocus C stream t s f)
    (hg : IsFocus C stream t s g) : f = g := by
  apply Nat.le_antisymm
  · exact hg.2.2 f hf.1 hf.2.1
  · exact hf.2.2 g hg.1 hg.2.1

/-- One-step fixed-scope invariant.  If the announcement arriving between
times `t` and `t + 1` does not falsify the old focus, then every critical
status in the scope and the focus itself are unchanged. -/
theorem fixed_scope_one_step
    {C : LanguageFamily} {stream : ℕ → ℕ} {t s f : ℕ}
    (hf : IsFocus C stream t s f)
    (hstay : Consistent C stream (t + 1) f) :
    (∀ i, i < s →
        (RecursiveCritical C stream (t + 1) i ↔
          RecursiveCritical C stream t i)) ∧
      IsFocus C stream (t + 1) s f := by
  have htu : t ≤ t + 1 := by omega
  exact ⟨recursiveCritical_iff_of_focus_consistent htu hf hstay,
    isFocus_of_consistent_at_later_time htu hf hstay⟩

/-- An old critical language remains critical at a later time exactly when
it remains consistent. This is the persistence step in arXiv v2 Remark 3.3. -/
theorem recursiveCritical_persists_iff_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {t u i : ℕ}
    (htu : t ≤ u) (hi : RecursiveCritical C stream t i) :
    RecursiveCritical C stream u i ↔ Consistent C stream u i := by
  refine ⟨recursiveCritical_consistent, fun hcon => ?_⟩
  have hf : IsFocus C stream t (i + 1) i :=
    ⟨Nat.lt_succ_self i, hi, fun j hj _ => Nat.le_of_lt_succ hj⟩
  exact (isFocus_of_consistent_at_later_time htu hf hcon).2.1

/-- ArXiv v2 Remark 3.3: the old critical languages that disappear form a
suffix of the old critical chain. The statement also holds across many rounds. -/
theorem lost_recursiveCritical_suffix
    {C : LanguageFamily} {stream : ℕ → ℕ} {t u i j : ℕ}
    (htu : t ≤ u) (hij : i ≤ j)
    (hi : RecursiveCritical C stream t i)
    (hj : RecursiveCritical C stream t j)
    (hlost : ¬ RecursiveCritical C stream u i) :
    ¬ RecursiveCritical C stream u j := by
  intro hjnew
  apply hlost
  apply (recursiveCritical_persists_iff_consistent htu hi).2
  exact old_critical_consistent_of_later_critical_consistent
    hij hi hj (recursiveCritical_consistent hjnew)

/-- ArXiv v2 Remark 3.3: every newly critical index is above every surviving
old critical index. -/
theorem new_recursiveCritical_above_survivor
    {C : LanguageFamily} {stream : ℕ → ℕ} {t u i j : ℕ}
    (htu : t ≤ u)
    (hinew : RecursiveCritical C stream u i)
    (hiold : ¬ RecursiveCritical C stream t i)
    (hjold : RecursiveCritical C stream t j)
    (hjnew : RecursiveCritical C stream u j) : j < i := by
  by_contra hnot
  have hij : i ≤ j := Nat.le_of_not_gt hnot
  have hf : IsFocus C stream t (j + 1) j :=
    ⟨Nat.lt_succ_self j, hjold, fun k hk _ => Nat.le_of_lt_succ hk⟩
  exact hiold ((recursiveCritical_iff_of_focus_consistent htu hf
    (recursiveCritical_consistent hjnew) i (Nat.lt_succ_of_le hij)).1 hinew)

end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Patient.Validity
section
set_option autoImplicit true

/-!
# Validity of the semantic patient-scope machine

This file proves Lemma 3.12 for the semantic machine.  The proof has two
parts.  First, after consistency stabilizes on the finite target prefix, a
scope not yet containing the target must eventually increase.  Second, once
the target is critical and lies in scope, every later transition keeps it in
scope.  The selected focus is then contained in the target, so every output is
a fresh target element.
-/

namespace GenLimit
namespace PatientMachine

/-- `processRound` preserves the focus well-formedness supplied by `decide`. -/
theorem processRound_isFocus
    {O : OracleFamily} {stream : ℕ → ℕ} {t : ℕ} {old : State}
    (hfocus : IsFocus O.language stream t old.scope old.focus)
    (hexists : ∃ i, Consistent O.language stream (t + 1) i) :
    IsFocus O.language stream (t + 1)
      (processRound O stream t old).scope
      (processRound O stream t old).focus := by
  simpa only [processRound] using decide_isFocus hfocus hexists

/-- Compatibility name for the post-round focus membership fact.  New code
uses `output_mem_round_focus`; this alias preserves audited downstream source
anchors. -/
theorem output_mem_run_succ_focus
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    output O stream t ∈ O.language (run O stream (t + 1)).focus :=
  output_mem_round_focus O stream t

/-- If the target is critical both before and after a transition and is in
the old scope, the new scope still contains it. -/
theorem processRound_preserves_target_in_scope
    {O : OracleFamily} {stream : ℕ → ℕ} {t z : ℕ} {old : State}
    (hzscope : z < old.scope)
    (hzold : RecursiveCritical O.language stream t z)
    (hznew : RecursiveCritical O.language stream (t + 1) z) :
    z < (processRound O stream t old).scope := by
  classical
  by_cases hcon : Consistent O.language stream (t + 1) old.focus
  · simp only [processRound]
    rw [decide, if_pos hcon]
    rw [stableDecision_scope]
    split <;> omega
  · have hscopeCon :
        (consistentIndices O.language stream (t + 1) old.scope).Nonempty :=
      ⟨z, mem_consistentIndices.mpr
        ⟨hzscope, recursiveCritical_consistent hznew⟩⟩
    have hsurv :
        (survivingCriticalIndices O.language stream t old.scope).Nonempty :=
      ⟨z, mem_survivingCriticalIndices.mpr
        ⟨hzscope, hzold, hznew⟩⟩
    let i := highestSurvivor O.language stream t old.scope old.focus
    have hi := highestSurvivor_spec
      (C := O.language) (stream := stream) (t := t)
      (scope := old.scope) (fallback := old.focus) hsurv
    have hzi : z ≤ i := hi.2.2.2 z hzscope hzold hznew
    simp only [processRound]
    rw [decide, if_neg hcon]
    rw [backtrackDecision_of_survivor hscopeCon hsurv]
    simpa [i] using Nat.lt_succ_of_le hzi

/-- Once the target is eventually critical and has entered the scope, it
remains in scope forever. -/
theorem target_in_scope_persistent
    (O : OracleFamily) (stream : ℕ → ℕ) {z T t : ℕ}
    (hcrit : ∀ u, T ≤ u → RecursiveCritical O.language stream u z)
    (hTt : T ≤ t) (hzscope : z < (run O stream t).scope) :
    ∀ u, t ≤ u → z < (run O stream u).scope := by
  intro u htu
  induction u, htu using Nat.le_induction with
  | base => exact hzscope
  | succ u htu ih =>
      rw [run_succ]
      apply processRound_preserves_target_in_scope
        ih
      · exact hcrit u (le_trans hTt htu)
      · exact hcrit (u + 1) (by omega)

/-- Once consistency has stabilized on indices through `w`, a scope not yet
containing `w` must later increase.  The presented set need not itself be one
of the indexed languages; `hOn` supplies the weaker on-model invariant needed
to keep the machine focus well-formed. -/
theorem exists_later_scope_increase_below_witness
    (O : OracleFamily) (stream : ℕ → ℕ) {E : Language} {w T t : ℕ}
    (hP : Presents stream E)
    (hOn : OnModel O stream)
    (hstable : ∀ u, T ≤ u → ∀ i, i ≤ w →
      (Consistent O.language stream u i ↔ E ⊆ O.language i))
    (hTt : T ≤ t)
    (hscope : (run O stream t).scope ≤ w) :
    ∃ u, t < u ∧
      (run O stream t).scope < (run O stream u).scope := by
  generalize hn :
      2 ^ (run O stream t).tau - (run O stream t).age = n
  induction n using Nat.strong_induction_on generalizing t with
  | h n ih =>
      let old := run O stream t
      have hfocus := run_focus_isFocus_of_onModel O hOn t
      have hfocusLe : old.focus ≤ w :=
        le_trans (Nat.le_of_lt hfocus.1) hscope
      have hfocusCon : Consistent O.language stream t old.focus :=
        recursiveCritical_consistent hfocus.2.1
      have hESub : E ⊆ O.language old.focus :=
        (hstable t hTt old.focus hfocusLe).1 hfocusCon
      have hnextCon : Consistent O.language stream (t + 1) old.focus :=
        consistent_of_presented_subset hP hESub
      by_cases hwait : 2 ^ old.tau ≤ old.age
      · refine ⟨t + 1, Nat.lt_succ_self t, ?_⟩
        simp [run_succ, processRound, decide, hnextCon,
          stableDecision, hwait, old]
      · have hnextScope :
            (run O stream (t + 1)).scope = old.scope := by
          simp [run_succ, processRound, decide, hnextCon,
            stableDecision, hwait, old]
        have hnextTau : (run O stream (t + 1)).tau = old.tau := by
          simp [run_succ, processRound, decide, hnextCon,
            stableDecision, hwait, old]
        have hnextAge : (run O stream (t + 1)).age = old.age + 1 := by
          simp [run_succ, processRound, decide, hnextCon,
            stableDecision, hwait, old]
        have hageLt : old.age < 2 ^ old.tau := Nat.lt_of_not_ge hwait
        have hmeasureCore :
            2 ^ old.tau - (old.age + 1) <
              2 ^ old.tau - old.age := by
          omega
        have hmeasureLt :
            2 ^ (run O stream (t + 1)).tau -
                (run O stream (t + 1)).age < n := by
          calc
            2 ^ (run O stream (t + 1)).tau -
                (run O stream (t + 1)).age =
                2 ^ old.tau - (old.age + 1) := by
                  rw [hnextTau, hnextAge]
            _ < 2 ^ old.tau - old.age := hmeasureCore
            _ = n := by simpa [old] using hn
        have hscopeNext : (run O stream (t + 1)).scope ≤ w := by
          rw [hnextScope]
          simpa [old] using hscope
        obtain ⟨u, htu, huScope⟩ := ih _ hmeasureLt
          (t := t + 1) (by omega) hscopeNext
          rfl
        refine ⟨u, lt_trans (Nat.lt_succ_self t) htu, ?_⟩
        have : old.scope < (run O stream u).scope := by
          rw [← hnextScope]
          exact huScope
        simpa [old] using this

/-- Exact-presentation specialization of
`exists_later_scope_increase_below_witness`. -/
theorem exists_later_scope_increase_below_target
    (O : OracleFamily) (stream : ℕ → ℕ) {z T t : ℕ}
    (hP : Presents stream (O.language z))
    (hstable : ∀ u, T ≤ u → ∀ i, i ≤ z →
      (Consistent O.language stream u i ↔ O.language z ⊆ O.language i))
    (hTt : T ≤ t)
    (hscope : (run O stream t).scope ≤ z) :
    ∃ u, t < u ∧
      (run O stream t).scope < (run O stream u).scope :=
  exists_later_scope_increase_below_witness O stream hP
    (onModel_of_presents O hP) hstable hTt hscope

/-- An eventually permanent critical witness eventually enters the patient
scope and remains there. -/
theorem critical_witness_eventually_in_scope
    (O : OracleFamily) (stream : ℕ → ℕ) {E : Language} {w Tc : ℕ}
    (hP : Presents stream E)
    (hOn : OnModel O stream)
    (hcrit : ∀ t, Tc ≤ t → RecursiveCritical O.language stream t w) :
    ∃ T, ∀ t, T ≤ t → w < (run O stream t).scope := by
  obtain ⟨Ts, hstable⟩ :=
    finite_scope_eventually_consistent_iff_presented_subset
      (C := O.language) hP (w + 1)
  let T0 := max Ts Tc
  have hTs : Ts ≤ T0 := Nat.le_max_left _ _
  have hTc : Tc ≤ T0 := Nat.le_max_right _ _
  have hreachFrom : ∀ t, T0 ≤ t →
      ∃ u, t ≤ u ∧ w < (run O stream u).scope := by
    intro t hT0t
    generalize hn : w + 1 - (run O stream t).scope = n
    induction n using Nat.strong_induction_on generalizing t with
    | h n ih =>
        by_cases hwscope : w < (run O stream t).scope
        · exact ⟨t, Nat.le_refl _, hwscope⟩
        · have hscope : (run O stream t).scope ≤ w :=
            Nat.le_of_not_gt hwscope
          obtain ⟨u, htu, hinc⟩ :=
            exists_later_scope_increase_below_witness O stream hP hOn
              (fun v hv i hi => hstable v (le_trans hTs hv) i
                (Nat.lt_succ_of_le hi))
              hT0t hscope
          by_cases huw : w < (run O stream u).scope
          · exact ⟨u, Nat.le_of_lt htu, huw⟩
          · have huscope : (run O stream u).scope ≤ w :=
              Nat.le_of_not_gt huw
            have hmeasureLt :
                w + 1 - (run O stream u).scope < n := by
              rw [← hn]
              omega
            obtain ⟨v, huv, hvscope⟩ := ih _ hmeasureLt
              (t := u) (le_trans hT0t (Nat.le_of_lt htu)) rfl
            exact ⟨v, le_trans (Nat.le_of_lt htu) huv, hvscope⟩
  have hreach : ∃ u, T0 ≤ u ∧ w < (run O stream u).scope :=
    hreachFrom T0 (Nat.le_refl _)
  obtain ⟨u, hT0u, huscope⟩ := hreach
  refine ⟨u, ?_⟩
  intro t hut
  exact target_in_scope_persistent O stream
    (fun v hv => hcrit v (le_trans hTc (le_trans hT0u hv)))
    (Nat.le_refl u) huscope t hut

/-- The patient scope eventually contains an exactly presented target and
never loses it. -/
theorem target_eventually_in_scope
    (O : OracleFamily) (stream : ℕ → ℕ) {z : ℕ}
    (hP : Presents stream (O.language z)) :
    ∃ T, ∀ t, T ≤ t → z < (run O stream t).scope := by
  obtain ⟨Tc, hcrit⟩ := target_eventually_recursiveCritical hP
  exact critical_witness_eventually_in_scope O stream hP
    (onModel_of_presents O hP) hcrit

/-- Lemma 3.12: the semantic patient-scope generator eventually outputs fresh
elements of the presented target language.  Freshness and injectivity are
available separately as `output_not_mem_sample` and `output_injective`. -/
theorem patient_validity
    (O : OracleFamily) (stream : ℕ → ℕ) {z : ℕ}
    (hP : Presents stream (O.language z)) :
    ∃ T, ∀ t, T ≤ t → output O stream t ∈ O.language z := by
  obtain ⟨Ts, hscope⟩ := target_eventually_in_scope O stream hP
  obtain ⟨Tc, hcrit⟩ := target_eventually_recursiveCritical hP
  refine ⟨max Ts Tc, ?_⟩
  intro t ht
  have hTs : Ts ≤ t + 1 := by omega
  have hTc : Tc ≤ t + 1 := by omega
  have hfocus := run_focus_isFocus O hP (t + 1)
  have hsub : O.language (run O stream (t + 1)).focus ⊆ O.language z :=
    focus_subset_target hfocus (hscope (t + 1) hTs) (hcrit (t + 1) hTc)
  exact hsub (output_mem_round_focus O stream t)

end PatientMachine
end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Patient.Output
section
set_option autoImplicit true

/-!
# Output facts for the semantic patient-scope machine

The round-`t` output is the least value available in the focus stored in the
post-round state `run (t + 1)`.  These indexing lemmas isolate that fact for
the predecessor comparison in Fact 3.13.
-/

namespace GenLimit
namespace PatientMachine

theorem output_available_post_focus
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    Available O.language stream (t + 1) (run O stream t).used
      (run O stream (t + 1)).focus (output O stream t) := by
  simpa using output_available O stream t

theorem output_minimal_post_focus
    (O : OracleFamily) (stream : ℕ → ℕ) (t x : ℕ)
    (hx : Available O.language stream (t + 1) (run O stream t).used
      (run O stream (t + 1)).focus x) :
    output O stream t ≤ x := by
  rw [output_eq_leastAvailable]
  rw [run_succ_focus] at hx
  exact leastAvailable_minimal O.language O.infinite' stream (t + 1)
    (run O stream t).used
    (decide O.language stream t (run O stream t)).focus x hx

/-- The previous-round form used by Fact 3.13. -/
theorem previous_output_le
    (O : OracleFamily) (stream : ℕ → ℕ) {t x : ℕ}
    (ht : 0 < t)
    (hx : Available O.language stream t (run O stream (t - 1)).used
      (run O stream t).focus x) :
    output O stream (t - 1) ≤ x := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  simpa using output_minimal_post_focus O stream s x hx

end PatientMachine
end GenLimit

end

-- GenLimit.Support.TurnTaking.Announcements
section
set_option autoImplicit true

/-!
# Turn-taking announcements and fresh plays

In each round the adversary speaks before the generator.  These definitions
record which party first announces a value and the freshness properties used
by turn-taking generation arguments.  They allow arbitrary repetitions unless
`FreshPlay` is assumed explicitly.

The API is shared by the P30 and P39 developments; neither paper owns these
basic notions.
-/

namespace GenLimit

/-- Values announced by the adversary before any earlier generator output. -/
def AdversaryFirst (adversary generator : ℕ → ℕ) : Set ℕ :=
  {x | ∃ t, adversary t = x ∧ ∀ s, s < t → generator s ≠ x}

/-- Values announced by the generator before any adversary announcement up to
and including the same round. -/
def GeneratorFirst (adversary generator : ℕ → ℕ) : Set ℕ :=
  {x | ∃ t, generator t = x ∧ ∀ s, s ≤ t → adversary s ≠ x}

/-- First time at which a stream announces `x`, defaulting to `0` when `x`
does not occur.  Clients normally use this only after establishing range
membership. -/
noncomputable def firstAnnouncementTime
    (announcer : ℕ → ℕ) (x : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, announcer t = x then Nat.find h else 0

theorem firstAnnouncementTime_spec
    {announcer : ℕ → ℕ} {x : ℕ} (hx : x ∈ Set.range announcer) :
    announcer (firstAnnouncementTime announcer x) = x := by
  classical
  simp only [firstAnnouncementTime]
  split
  · exact Nat.find_spec ‹∃ t, announcer t = x›
  · exact False.elim (‹¬ ∃ t, announcer t = x› hx)

theorem firstAnnouncementTime_min
    {announcer : ℕ → ℕ} {x t : ℕ} (hx : x ∈ Set.range announcer)
    (ht : announcer t = x) :
    firstAnnouncementTime announcer x ≤ t := by
  classical
  simp only [firstAnnouncementTime]
  split
  · exact Nat.find_min' ‹∃ q, announcer q = x› ht
  · exact False.elim (‹¬ ∃ q, announcer q = x› hx)

theorem firstAnnouncementTime_not_mem_sample
    {announcer : ℕ → ℕ} {x : ℕ} (hx : x ∈ Set.range announcer) :
    x ∉ sample announcer (firstAnnouncementTime announcer x) := by
  intro hmem
  rw [mem_sample_iff] at hmem
  obtain ⟨s, hs, hseq⟩ := hmem
  exact (Nat.not_lt_of_ge (firstAnnouncementTime_min hx hseq)) hs

/-- Pair a value with the generator output immediately before its first
announcement by the other stream. -/
noncomputable def predecessorPartner
    (announcer generator : ℕ → ℕ) (x : ℕ) : ℕ :=
  generator (firstAnnouncementTime announcer x - 1)

/-- Predecessor pairing is injective on any range subset whose first
announcement times are positive.  Positivity removes the ambiguity of
truncated subtraction at time zero. -/
theorem predecessorPartner_injOn
    {announcer generator : ℕ → ℕ} {S : Set ℕ}
    (hgenerator : Function.Injective generator)
    (hrange : S ⊆ Set.range announcer)
    (hpositive : ∀ x, x ∈ S → 0 < firstAnnouncementTime announcer x) :
    Set.InjOn (predecessorPartner announcer generator) S := by
  intro x hx y hy hxy
  have hpred :
      firstAnnouncementTime announcer x - 1 =
        firstAnnouncementTime announcer y - 1 := by
    apply hgenerator
    exact hxy
  have htime :
      firstAnnouncementTime announcer x =
        firstAnnouncementTime announcer y := by
    have hxpos := hpositive x hx
    have hypos := hpositive y hy
    omega
  calc
    x = announcer (firstAnnouncementTime announcer x) :=
      (firstAnnouncementTime_spec (hrange hx)).symm
    _ = announcer (firstAnnouncementTime announcer y) := by rw [htime]
    _ = y := firstAnnouncementTime_spec (hrange hy)

theorem adversaryFirst_disjoint_generatorFirst
    (adversary generator : ℕ → ℕ) :
    Disjoint (AdversaryFirst adversary generator)
      (GeneratorFirst adversary generator) := by
  rw [Set.disjoint_left]
  intro x hxA hxD
  obtain ⟨t, hat, hnoG⟩ := hxA
  obtain ⟨s, hgs, hnoA⟩ := hxD
  by_cases hst : s < t
  · exact hnoG s hst hgs
  · exact hnoA t (Nat.le_of_not_gt hst) hat

/-- Every value ever announced by the adversary has a first-announcing
party, even when the adversary does not enumerate the whole universe. -/
theorem range_subset_first_announcements
    (adversary generator : ℕ → ℕ) :
    Set.range adversary ⊆
      AdversaryFirst adversary generator ∪
        GeneratorFirst adversary generator := by
  classical
  intro x hx
  let t := Nat.find hx
  have hat : adversary t = x := Nat.find_spec hx
  have htmin : ∀ q, adversary q = x → t ≤ q := by
    intro q hq
    exact Nat.find_min' hx hq
  by_cases hgen : ∃ s, s < t ∧ generator s = x
  · obtain ⟨s, hst, hgs⟩ := hgen
    refine Set.mem_union_right _ ⟨s, hgs, ?_⟩
    intro q hqs haq
    exact (Nat.not_lt_of_ge (htmin q haq)) (lt_of_le_of_lt hqs hst)
  · refine Set.mem_union_left _ ⟨t, hat, ?_⟩
    intro s hst hgs
    exact hgen ⟨s, hst, hgs⟩

/-- If the adversary eventually announces every value, every value has a
unique first-announcing party. -/
theorem adversaryFirst_union_generatorFirst
    {adversary generator : ℕ → ℕ}
    (hsurj : Function.Surjective adversary) :
    AdversaryFirst adversary generator ∪
        GeneratorFirst adversary generator = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact range_subset_first_announcements adversary generator
    ⟨Classical.choose (hsurj x), Classical.choose_spec (hsurj x)⟩

/-- Exact presentations of the normalized target `Set.univ` satisfy the
surjectivity premise of the first-announcement partition. -/
theorem first_announcement_partition_of_presents_univ
    {adversary generator : ℕ → ℕ}
    (hP : Presents adversary Set.univ) :
    AdversaryFirst adversary generator ∪
        GeneratorFirst adversary generator = Set.univ := by
  apply adversaryFirst_union_generatorFirst
  intro x
  have hx : x ∈ Set.range adversary := by
    rw [hP]
    exact Set.mem_univ x
  exact hx

/-- Freshness properties of a play in which the adversary moves before the
generator in each round. -/
structure FreshPlay (adversary generator : ℕ → ℕ) : Prop where
  fresh_adversary : ∀ t s, s ≤ t → adversary s ≠ generator t
  fresh_generator : ∀ t s, s < t → generator s ≠ generator t

namespace FreshPlay

theorem generator_injective
    {adversary generator : ℕ → ℕ}
    (P : FreshPlay adversary generator) :
    Function.Injective generator := by
  intro s t hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact P.fresh_generator t s hlt hst
  · exact P.fresh_generator s t hgt hst.symm

end FreshPlay

end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Abstract.Announcements
section
set_option autoImplicit true

/-!
# First announcements compatibility import

The paper-independent first-announcement and fresh-play API now lives in
`GenLimit.Support.TurnTaking.Announcements`.  This module remains as a stable
compatibility import for the existing P39 development.
-/

end

-- GenLimit.Paper39_DenseGeneration.Abstract.PatientScope
section
set_option autoImplicit true

/-!
# An abstract certificate for the patient-scope density argument

This file isolates the finite counting argument used in Fact 3.13, Lemma 3.14,
and Theorem 3.15 of *Dense Language Generation Made Simple*.

It deliberately does **not** claim to implement the patient-scope state
machine.  A `PatientScopeCertificate` records the properties of a completed
trace that the machine proof must eventually supply:

* eventual validity and non-repetition of defender outputs;
* the ownership partition of the target;
* the injective, order-decreasing partner map from ordinary attacker wins to
  defender wins (Fact 3.13);
* a finite-prefix budget for switch losses (the conclusion supplied by the
  charging lemma).

The main theorem in this file derives the exact prefix-count inequality that
feeds the analytic lower-density calculation.  Keeping this layer separate
makes every assumption visible while the considerably longer machine and
charging invariants are formalized.
-/

namespace GenLimit
namespace PatientScope

/-- Elements of `S` in the strict natural-number prefix `{0, ..., n - 1}`. -/
noncomputable def prefixFinset (S : Set ℕ) (n : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range n).filter (fun x => x ∈ S)

@[simp] theorem mem_prefixFinset {S : Set ℕ} {n x : ℕ} :
    x ∈ prefixFinset S n ↔ x < n ∧ x ∈ S := by
  classical
  simp [prefixFinset]

/-- Cardinality of a set inside the strict prefix `{0, ..., n - 1}`. -/
noncomputable def prefixCount (S : Set ℕ) (n : ℕ) : ℕ :=
  (prefixFinset S n).card

/-- Attacker-owned target elements which are neither early exceptions nor
switch losses.  Fact 3.13 pairs precisely these elements with smaller
defender-owned target elements. -/
def ordinaryAttacker
    (target attacker switchLoss : Set ℕ) (earlyAttacker : Finset ℕ) : Set ℕ :=
  (attacker ∩ target) \ ((↑earlyAttacker : Set ℕ) ∪ switchLoss)

/-- Every attacker-owned target element in a finite prefix is either
ordinary, an early exception, or a switch loss. -/
theorem attackerTarget_prefix_subset_ordinary_early_switch
    (target attacker switchLoss : Set ℕ) (earlyAttacker : Finset ℕ)
    (n : ℕ) :
    prefixFinset (attacker ∩ target) n ⊆
      (prefixFinset
          (ordinaryAttacker target attacker switchLoss earlyAttacker) n ∪
        earlyAttacker) ∪ prefixFinset switchLoss n := by
  classical
  intro x hx
  have hx' := mem_prefixFinset.mp hx
  by_cases hearly : x ∈ earlyAttacker
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hearly)
  · by_cases hswitch : x ∈ switchLoss
    · exact Finset.mem_union_right _
        (mem_prefixFinset.mpr ⟨hx'.1, hswitch⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact mem_prefixFinset.mpr
        ⟨hx'.1, hx'.2, by simpa using ⟨hearly, hswitch⟩⟩

/--
An abstract trace certificate for the patient-scope algorithm.

`attacker` and `defender` are ownership sets: an element belongs to the party
that announced it first.  `output` enumerates the defender-owned elements.
The fields `output_injective` and `eventual_target` are the extensional content
of validity needed here.  The full machine bridge should additionally prove
that these sets are induced by the round-by-round game trace.
-/
structure PatientScopeCertificate where
  target : Language
  attacker : Set ℕ
  defender : Set ℕ
  output : ℕ → ℕ

  /-- Every defender-owned element is output, and every output is
  defender-owned. -/
  output_range : Set.range output = defender
  /-- The defender never repeats an output. -/
  output_injective : Function.Injective output
  /-- Lemma 3.12, stated at trace level. -/
  validFrom : ℕ
  eventual_target : ∀ t, validFrom ≤ t → output t ∈ target

  /-- Every target element is eventually owned by one of the two parties. -/
  target_covered : target ⊆ attacker ∪ defender
  /-- First ownership is unique. -/
  ownership_disjoint : Disjoint attacker defender

  /-- Attacker-owned target elements before the validity threshold. -/
  earlyAttacker : Finset ℕ
  /-- Attacker-owned target elements which falsify the preceding focus. -/
  switchLoss : Set ℕ
  switchLoss_subset : switchLoss ⊆ attacker ∩ target

  /-- The partner supplied by Fact 3.13. -/
  partner : ℕ → ℕ
  partner_mem : ∀ x,
    x ∈ ordinaryAttacker target attacker switchLoss earlyAttacker →
      partner x ∈ defender ∩ target
  partner_lt : ∀ x,
    x ∈ ordinaryAttacker target attacker switchLoss earlyAttacker →
      partner x < x
  partner_injective : Set.InjOn partner
    (ordinaryAttacker target attacker switchLoss earlyAttacker)

  /-- An explicit upper bound on switch losses in each prefix.  Lemma 3.14
  supplies `Nat.log2 (prefixCount target n)` here. -/
  switchBudget : ℕ → ℕ
  switch_prefix_le : ∀ n,
    prefixCount switchLoss n ≤ switchBudget n

namespace PatientScopeCertificate

variable (P : PatientScopeCertificate)

/-- Target elements first owned by the attacker. -/
noncomputable def attackerCount (n : ℕ) : ℕ :=
  prefixCount (P.attacker ∩ P.target) n

/-- Target elements first owned by the defender. -/
noncomputable def defenderCount (n : ℕ) : ℕ :=
  prefixCount (P.defender ∩ P.target) n

/-- Number of target elements in a universe prefix. -/
noncomputable def targetCount (n : ℕ) : ℕ :=
  prefixCount P.target n

/-- The certificate explicitly contains generation in the limit at the trace
level: outputs are eventually in the target and are never repeated. -/
theorem validity :
    ∃ T, (∀ t, T ≤ t → P.output t ∈ P.target) ∧
      Function.Injective P.output := by
  exact ⟨P.validFrom, P.eventual_target, P.output_injective⟩

/-- No output value is attacker-owned. -/
theorem output_not_attacker (t : ℕ) : P.output t ∉ P.attacker := by
  intro houtA
  have hout : P.output t ∈ P.defender := by
    rw [← P.output_range]
    exact ⟨t, rfl⟩
  exact Set.disjoint_left.1 P.ownership_disjoint
    houtA hout

/-- Fact 3.13 in the precise form used by counting: ordinary attacker wins
inject into strictly smaller defender-owned target elements. -/
theorem fact_3_12 :
    Set.InjOn P.partner
        (ordinaryAttacker P.target P.attacker P.switchLoss P.earlyAttacker) ∧
      ∀ x,
        x ∈ ordinaryAttacker
          P.target P.attacker P.switchLoss P.earlyAttacker →
        P.partner x ∈ P.defender ∩ P.target ∧ P.partner x < x := by
  refine ⟨P.partner_injective, ?_⟩
  intro x hx
  exact ⟨P.partner_mem x hx, P.partner_lt x hx⟩

/-- The order-decreasing partner map gives a finite-prefix injection. -/
theorem ordinary_prefix_le_defender (n : ℕ) :
    prefixCount
        (ordinaryAttacker P.target P.attacker P.switchLoss P.earlyAttacker) n
      ≤ P.defenderCount n := by
  classical
  unfold prefixCount defenderCount
  apply Finset.card_le_card_of_injOn P.partner
  · intro x hx
    have hxfin : x ∈ prefixFinset
        (ordinaryAttacker P.target P.attacker P.switchLoss P.earlyAttacker) n := hx
    have hx' : x < n ∧
        x ∈ ordinaryAttacker
          P.target P.attacker P.switchLoss P.earlyAttacker := by
      exact mem_prefixFinset.mp hxfin
    apply mem_prefixFinset.mpr
    exact ⟨lt_trans (P.partner_lt x hx'.2) hx'.1,
      P.partner_mem x hx'.2⟩
  · intro x hx y hy hxy
    have hx' : x ∈ ordinaryAttacker
        P.target P.attacker P.switchLoss P.earlyAttacker :=
      (mem_prefixFinset.mp (show x ∈ prefixFinset
        (ordinaryAttacker P.target P.attacker P.switchLoss P.earlyAttacker) n
        from hx)).2
    have hy' : y ∈ ordinaryAttacker
        P.target P.attacker P.switchLoss P.earlyAttacker :=
      (mem_prefixFinset.mp (show y ∈ prefixFinset
        (ordinaryAttacker P.target P.attacker P.switchLoss P.earlyAttacker) n
        from hy)).2
    exact P.partner_injective hx' hy' hxy

/-- The target ownership sets form a disjoint partition in every prefix. -/
theorem targetCount_eq (n : ℕ) :
    P.targetCount n = P.attackerCount n + P.defenderCount n := by
  classical
  let A := prefixFinset (P.attacker ∩ P.target) n
  let D := prefixFinset (P.defender ∩ P.target) n
  have hdis : Disjoint A D := by
    rw [Finset.disjoint_left]
    intro x hxA hxD
    have hxA' : x ∈ P.attacker := (mem_prefixFinset.mp hxA).2.1
    have hxD' : x ∈ P.defender := (mem_prefixFinset.mp hxD).2.1
    exact Set.disjoint_left.1 P.ownership_disjoint hxA' hxD'
  have hunion : prefixFinset P.target n = A ∪ D := by
    ext x
    simp only [mem_prefixFinset, Finset.mem_union, A, D]
    constructor
    · intro hx
      rcases P.target_covered hx.2 with hxA | hxD
      · exact Or.inl ⟨hx.1, hxA, hx.2⟩
      · exact Or.inr ⟨hx.1, hxD, hx.2⟩
    · rintro (⟨hxn, -, hxK⟩ | ⟨hxn, -, hxK⟩)
      · exact ⟨hxn, hxK⟩
      · exact ⟨hxn, hxK⟩
  unfold targetCount attackerCount defenderCount prefixCount
  rw [hunion, Finset.card_union_of_disjoint hdis]

/-- The finite-prefix inequality at the end of the combinatorial part of the
proof of Theorem 3.15.

In paper notation this is
`mu_n(A) ≤ mu_n(D ∩ K) + r + switchBudget(n)`.
-/
theorem attackerCount_le (n : ℕ) :
    P.attackerCount n ≤
      P.defenderCount n + P.earlyAttacker.card + P.switchBudget n := by
  classical
  let O := prefixFinset
    (ordinaryAttacker P.target P.attacker P.switchLoss P.earlyAttacker) n
  let S := prefixFinset P.switchLoss n
  have hsubset := attackerTarget_prefix_subset_ordinary_early_switch
    P.target P.attacker P.switchLoss P.earlyAttacker n
  have hcard : P.attackerCount n ≤ (O ∪ P.earlyAttacker ∪ S).card := by
    exact Finset.card_le_card hsubset
  have hunion : (O ∪ P.earlyAttacker ∪ S).card ≤
      O.card + P.earlyAttacker.card + S.card := by
    exact le_trans (Finset.card_union_le (O ∪ P.earlyAttacker) S)
      (Nat.add_le_add_right (Finset.card_union_le O P.earlyAttacker) S.card)
  have hord : O.card ≤ P.defenderCount n := by
    exact P.ordinary_prefix_le_defender n
  have hswitch : S.card ≤ P.switchBudget n := by
    exact P.switch_prefix_le n
  exact le_trans hcard <| le_trans hunion <|
    Nat.add_le_add (Nat.add_le_add hord (Nat.le_refl _)) hswitch

/-- Specialization when Lemma 3.14 supplies the logarithmic switch budget. -/
theorem attackerCount_le_log2
    (hlog : ∀ n,
      prefixCount P.switchLoss n ≤ Nat.log2 (P.targetCount n)) (n : ℕ) :
    P.attackerCount n ≤
      P.defenderCount n + P.earlyAttacker.card +
        Nat.log2 (P.targetCount n) := by
  -- Avoid imposing a relation between an arbitrary stored budget and the
  -- logarithmic one: reconstruct a certificate with the sharper budget.
  let Q : PatientScopeCertificate :=
    { P with
      switchBudget := fun m => Nat.log2 (P.targetCount m)
      switch_prefix_le := hlog }
  simpa [Q, attackerCount, defenderCount] using Q.attackerCount_le n

/-- In the normalized case `target = univ`, the ownership identity has the
form expected by the one-dimensional density endgame. -/
theorem normalized_counting
    (huniv : P.target = Set.univ) (n : ℕ) :
    P.attackerCount n + P.defenderCount n = n := by
  have h := P.targetCount_eq n
  calc
    P.attackerCount n + P.defenderCount n = P.targetCount n := h.symm
    _ = n := by
      simp [targetCount, prefixCount, prefixFinset, huniv]

/-- The ownership identity in the orientation used by the density theorem. -/
theorem normalized_partition
    (huniv : P.target = Set.univ) (n : ℕ) :
    P.defenderCount n + P.attackerCount n = n := by
  rw [Nat.add_comm]
  exact P.normalized_counting huniv n

/-- In the normalized target, the logarithmic charging lemma gives exactly
the counting inequality consumed by `lowerDensity_half_of_counting`. -/
theorem normalized_attackerCount_le_log2
    (huniv : P.target = Set.univ)
    (hlog : ∀ n,
      prefixCount P.switchLoss n ≤ Nat.log2 (P.targetCount n)) (n : ℕ) :
    P.attackerCount n ≤
      P.defenderCount n + P.earlyAttacker.card + Nat.log2 n := by
  have h := P.attackerCount_le_log2 hlog n
  have htarget : P.targetCount n = n := by
    simp [targetCount, prefixCount, prefixFinset, huniv]
  simpa [htarget] using h

end PatientScopeCertificate
end PatientScope
end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Abstract.GameTrace
section
set_option autoImplicit true

/-!
# Concrete game traces and patient-scope certificates

This file connects the abstract ownership sets in `PatientScopeCertificate`
to two concrete round-by-round announcement sequences.  It discharges the
ownership partition, output-range, and freshness parts of the certificate.
The patient-scope-specific partner and switch-loss properties remain named
inputs.
-/

namespace GenLimit
namespace PatientScope

/-- A play of the announcement game.  The adversary speaks first in round
`t`, followed by the generator. -/
structure GameTrace where
  target : Language
  adversary : ℕ → ℕ
  generator : ℕ → ℕ
  presents : Presents adversary target
  /-- The round-`t` output has not appeared in the adversary sequence through
  that round. -/
  fresh_adversary : ∀ t s, s ≤ t → adversary s ≠ generator t
  /-- The generator does not repeat one of its earlier outputs. -/
  fresh_generator : ∀ t s, s < t → generator s ≠ generator t
  validFrom : ℕ
  eventual_target : ∀ t, validFrom ≤ t → generator t ∈ target

namespace GameTrace

variable (G : GameTrace)

/-- Concrete attacker ownership set. -/
def attacker : Set ℕ := AdversaryFirst G.adversary G.generator

/-- Concrete defender ownership set. -/
def defender : Set ℕ := GeneratorFirst G.adversary G.generator

/-- Every generator output is defender-first because outputs are fresh after
the adversary's announcement in the same round. -/
theorem output_range : Set.range G.generator = G.defender := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl, G.fresh_adversary t⟩
  · rintro ⟨t, htx, -⟩
    exact ⟨t, htx⟩

theorem generator_injective : Function.Injective G.generator := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij' | hji'
  · exact G.fresh_generator j i hij' hij
  · exact G.fresh_generator i j hji' hij.symm

theorem target_covered : G.target ⊆ G.attacker ∪ G.defender := by
  intro x hx
  apply range_subset_first_announcements G.adversary G.generator
  rw [G.presents]
  exact hx

theorem ownership_disjoint : Disjoint G.attacker G.defender :=
  adversaryFirst_disjoint_generatorFirst G.adversary G.generator

/-- The full novelty statement supplied by the two freshness fields. -/
theorem eventual_validity_and_novelty :
    ∃ T, ∀ t, T ≤ t →
      G.generator t ∈ G.target ∧
      (∀ s, s ≤ t → G.adversary s ≠ G.generator t) ∧
      (∀ s, s < t → G.generator s ≠ G.generator t) := by
  exact ⟨G.validFrom, fun t ht =>
    ⟨G.eventual_target t ht, G.fresh_adversary t, G.fresh_generator t⟩⟩

/-- The finite exceptional set used in Theorem 3.15.  It includes attacker-first
values announced through the first valid round.  The extra round is needed
because Fact 3.13 pairs the round-`t` adversary value with the generator output
from round `t - 1`. -/
noncomputable def earlyAttacker : Finset ℕ := by
  classical
  exact (sample G.adversary (G.validFrom + 1)).filter
    (fun x => x ∈ G.attacker)

/-- Construct the theorem-level certificate from a concrete fresh trace.
Only Fact 3.13's partner and Lemma 3.14's switch budget remain to be supplied.
-/
noncomputable def toCertificate
    (switchLoss : Set ℕ)
    (hswitch : switchLoss ⊆ G.attacker ∩ G.target)
    (partner : ℕ → ℕ)
    (hpartnerMem : ∀ x,
      x ∈ ordinaryAttacker G.target G.attacker switchLoss G.earlyAttacker →
        partner x ∈ G.defender ∩ G.target)
    (hpartnerLt : ∀ x,
      x ∈ ordinaryAttacker G.target G.attacker switchLoss G.earlyAttacker →
        partner x < x)
    (hpartnerInj : Set.InjOn partner
      (ordinaryAttacker G.target G.attacker switchLoss G.earlyAttacker))
    (switchBudget : ℕ → ℕ)
    (hbudget : ∀ n, prefixCount switchLoss n ≤ switchBudget n) :
    PatientScopeCertificate where
  target := G.target
  attacker := G.attacker
  defender := G.defender
  output := G.generator
  output_range := G.output_range
  output_injective := G.generator_injective
  validFrom := G.validFrom
  eventual_target := G.eventual_target
  target_covered := G.target_covered
  ownership_disjoint := G.ownership_disjoint
  earlyAttacker := G.earlyAttacker
  switchLoss := switchLoss
  switchLoss_subset := hswitch
  partner := partner
  partner_mem := hpartnerMem
  partner_lt := hpartnerLt
  partner_injective := hpartnerInj
  switchBudget := switchBudget
  switch_prefix_le := hbudget

end GameTrace
end PatientScope
end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Abstract.Pairing
section
set_option autoImplicit true

/-!
# The predecessor pairing behind Fact 3.13

This file turns the local minimum-output comparison in a concrete game trace
into the global injective partner map used by the density count.  The finite
exception set includes the first valid round, so every paired predecessor is
already target-valid.
-/

namespace GenLimit
namespace PatientScope

namespace GameTrace

variable (G : GameTrace)

/-- First round in which the adversary announces `x`, defaulting to `0` for a
value outside the adversary range. -/
noncomputable abbrev firstAdversaryTime (x : ℕ) : ℕ :=
  GenLimit.firstAnnouncementTime G.adversary x

theorem firstAdversaryTime_spec {x : ℕ} (hx : x ∈ G.attacker) :
    G.adversary (G.firstAdversaryTime x) = x := by
  obtain ⟨t, htx, -⟩ := hx
  exact GenLimit.firstAnnouncementTime_spec ⟨t, htx⟩

theorem firstAdversaryTime_min {x t : ℕ} (hx : x ∈ G.attacker)
    (ht : G.adversary t = x) : G.firstAdversaryTime x ≤ t := by
  obtain ⟨w, hw, -⟩ := hx
  exact GenLimit.firstAnnouncementTime_min ⟨w, hw⟩ ht

theorem firstAdversaryTime_not_mem_sample {x : ℕ} (hx : x ∈ G.attacker) :
    x ∉ sample G.adversary (G.firstAdversaryTime x) := by
  obtain ⟨t, htx, -⟩ := hx
  exact GenLimit.firstAnnouncementTime_not_mem_sample ⟨t, htx⟩

theorem generator_ne_before_firstAdversaryTime
    {x s : ℕ} (hx : x ∈ G.attacker)
    (hs : s < G.firstAdversaryTime x) : G.generator s ≠ x := by
  have hxA := hx
  obtain ⟨t, htx, hnoGenerator⟩ := hx
  have hfirstLe : G.firstAdversaryTime x ≤ t :=
    G.firstAdversaryTime_min hxA htx
  exact hnoGenerator s (lt_of_lt_of_le hs hfirstLe)

/-- An ordinary attacker-first value occurs strictly after `validFrom`; this
is the one-round boundary adjustment needed by Fact 3.13. -/
theorem validFrom_lt_firstAdversaryTime
    {switchLoss : Set ℕ} {x : ℕ}
    (hx : x ∈ ordinaryAttacker
      G.target G.attacker switchLoss G.earlyAttacker) :
    G.validFrom < G.firstAdversaryTime x := by
  have hxA : x ∈ G.attacker := hx.1.1
  have hnotEarly : x ∉ G.earlyAttacker := by
    intro hearly
    exact hx.2 (Set.mem_union_left _ hearly)
  by_contra hnot
  have htime : G.firstAdversaryTime x < G.validFrom + 1 := by omega
  apply hnotEarly
  classical
  simp only [earlyAttacker, Finset.mem_filter]
  refine ⟨?_, hxA⟩
  rw [mem_sample_iff]
  exact ⟨G.firstAdversaryTime x, htime,
    G.firstAdversaryTime_spec hxA⟩

/-- Pair an attacker value with the generator output immediately before its
first adversary announcement. -/
noncomputable abbrev predecessorPartner (x : ℕ) : ℕ :=
  GenLimit.predecessorPartner G.adversary G.generator x

/-- Local minimum-output fact required from a concrete patient-scope run. -/
def HasPredecessorComparison (switchLoss : Set ℕ) : Prop :=
  ∀ t, G.validFrom < t →
    G.adversary t ∈ G.attacker →
    G.adversary t ∉ sample G.adversary t →
    G.adversary t ∉ switchLoss →
    G.generator (t - 1) < G.adversary t

theorem predecessorPartner_mem
    {switchLoss : Set ℕ}
    {x : ℕ}
    (hx : x ∈ ordinaryAttacker
      G.target G.attacker switchLoss G.earlyAttacker) :
    G.predecessorPartner x ∈ G.defender ∩ G.target := by
  have htime := G.validFrom_lt_firstAdversaryTime hx
  change G.validFrom <
    GenLimit.firstAnnouncementTime G.adversary x at htime
  refine ⟨?_, ?_⟩
  · rw [← G.output_range]
    exact ⟨G.firstAdversaryTime x - 1, rfl⟩
  · apply G.eventual_target
    omega

theorem predecessorPartner_lt
    {switchLoss : Set ℕ}
    (hcompare : G.HasPredecessorComparison switchLoss)
    {x : ℕ}
    (hx : x ∈ ordinaryAttacker
      G.target G.attacker switchLoss G.earlyAttacker) :
    G.predecessorPartner x < x := by
  have htime := G.validFrom_lt_firstAdversaryTime hx
  change G.validFrom <
    GenLimit.firstAnnouncementTime G.adversary x at htime
  have hxA : x ∈ G.attacker := hx.1.1
  have hspec := G.firstAdversaryTime_spec hxA
  have hAat : G.adversary (G.firstAdversaryTime x) ∈ G.attacker := by
    rw [hspec]
    exact hxA
  have hnotSwitch : G.adversary (G.firstAdversaryTime x) ∉ switchLoss := by
    rw [hspec]
    intro hswitch
    exact hx.2 (Set.mem_union_right _ hswitch)
  have hfresh : G.adversary (G.firstAdversaryTime x) ∉
      sample G.adversary (G.firstAdversaryTime x) := by
    simpa [hspec] using G.firstAdversaryTime_not_mem_sample hxA
  have h := hcompare (G.firstAdversaryTime x) htime hAat hfresh hnotSwitch
  change G.generator (G.firstAdversaryTime x - 1) < x
  simpa only [hspec] using h

theorem predecessorPartner_injective
    {switchLoss : Set ℕ} :
    Set.InjOn G.predecessorPartner
      (ordinaryAttacker G.target G.attacker switchLoss G.earlyAttacker) := by
  apply GenLimit.predecessorPartner_injOn G.generator_injective
  · intro x hx
    obtain ⟨t, htx, -⟩ := hx.1.1
    exact ⟨t, htx⟩
  · intro x hx
    have htime := G.validFrom_lt_firstAdversaryTime hx
    change G.validFrom <
      GenLimit.firstAnnouncementTime G.adversary x at htime
    exact lt_of_le_of_lt (Nat.zero_le G.validFrom) htime

end GameTrace
end PatientScope
end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Patient.Pairing
section
set_option autoImplicit true

/-!
# Fact 3.13 for the semantic patient-scope machine

This file instantiates the abstract predecessor pairing from `Abstract.Pairing` with
the semantic patient-scope run.  It is parameterized by an explicit validity
threshold and proof.  `Patient.Validity` provides those data when its
standalone theorem is imported by the final assembly module.

A switch round is one in which the arriving adversary value is outside the
pre-round focus.  The set `lateSwitchLoss` retains attacker-first values at
their fresh adversary occurrence after the validity threshold; it is the set
counted in Theorem 3.15.
-/

namespace GenLimit
namespace PatientMachine

/-- The concrete game trace generated by a semantic patient-scope run. -/
noncomputable def gameTrace
    (O : OracleFamily) (stream : ℕ → ℕ) (z validFrom : ℕ)
    (hP : Presents stream (O.language z))
    (hvalid : ∀ t, validFrom ≤ t → output O stream t ∈ O.language z) :
    PatientScope.GameTrace where
  target := O.language z
  adversary := stream
  generator := output O stream
  presents := hP
  fresh_adversary := fun t s hst => stream_ne_output O stream t s hst
  fresh_generator := fun _ _ hst => output_ne_of_lt O stream hst
  validFrom := validFrom
  eventual_target := hvalid

/-- Round `t` is a switch round when its arriving value falsifies the focus
stored before that announcement. -/
def SwitchRound
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) : Prop :=
  stream t ∉ O.language (run O stream t).focus

/-- The switch losses counted in Lemma 3.14: their fresh adversary occurrence
is strictly after the machine's validity threshold.  Early switch losses stay
in the finite exceptional set and are not charged logarithmically. -/
def lateSwitchLoss
    (O : OracleFamily) (stream : ℕ → ℕ) (validFrom : ℕ) : Set ℕ :=
  {x | x ∈ AdversaryFirst stream (output O stream) ∧
    ∃ t, validFrom < t ∧ stream t = x ∧ x ∉ sample stream t ∧
      SwitchRound O stream t}

theorem lateSwitchLoss_subset_attacker_target
    (O : OracleFamily) {stream : ℕ → ℕ} {z validFrom : ℕ}
    (hP : Presents stream (O.language z))
    (hvalid : ∀ t, validFrom ≤ t → output O stream t ∈ O.language z) :
    lateSwitchLoss O stream validFrom ⊆
      (gameTrace O stream z validFrom hP hvalid).attacker ∩ O.language z := by
  rintro x ⟨hxA, t, -, htx, -, -⟩
  refine ⟨?_, ?_⟩
  · simpa [gameTrace, PatientScope.GameTrace.attacker] using hxA
  · rw [← hP]
    exact ⟨t, htx⟩

/-- Every fresh attacker-first switch event after the validity threshold is
captured by `lateSwitchLoss`. -/
theorem mem_lateSwitchLoss_of_event
    (O : OracleFamily) (stream : ℕ → ℕ) {validFrom t : ℕ}
    (htime : validFrom < t)
    (hattacker : stream t ∈ AdversaryFirst stream (output O stream))
    (hfresh : stream t ∉ sample stream t)
    (hswitch : SwitchRound O stream t) :
    stream t ∈ lateSwitchLoss O stream validFrom :=
  ⟨hattacker, t, htime, rfl, hfresh, hswitch⟩

/-- At a fresh adversary occurrence of an attacker-first value, no earlier
machine output equals that value. -/
theorem no_output_before_fresh_attacker
    (O : OracleFamily) (stream : ℕ → ℕ) {t : ℕ}
    (hattacker : stream t ∈ AdversaryFirst stream (output O stream))
    (hfresh : stream t ∉ sample stream t) :
    ∀ r, r < t → output O stream r ≠ stream t := by
  obtain ⟨q, hq, hnoOutput⟩ := hattacker
  have htq : t ≤ q := by
    by_contra hnot
    have hqt : q < t := Nat.lt_of_not_ge hnot
    apply hfresh
    have hmem : stream q ∈ sample stream t := value_mem_sample hqt
    simpa [hq] using hmem
  intro r hrt
  exact hnoOutput r (lt_of_lt_of_le hrt htq)

/-- A fresh attacker-first value is absent from the machine's used-output set
immediately before its adversary occurrence. -/
theorem fresh_attacker_not_mem_used
    (O : OracleFamily) (stream : ℕ → ℕ) {t : ℕ}
    (hattacker : stream t ∈ AdversaryFirst stream (output O stream))
    (hfresh : stream t ∉ sample stream t) :
    stream t ∉ (run O stream (t - 1)).used := by
  intro hused
  rw [mem_run_used_iff] at hused
  obtain ⟨r, hr, hre⟩ := hused
  have hrt : r < t := lt_of_lt_of_le hr (Nat.sub_le t 1)
  exact no_output_before_fresh_attacker O stream hattacker hfresh r hrt hre

/-- Thresholded version used by Theorem 3.15.  Because this round is already
late, failure to belong to `lateSwitchLoss` proves that it is not a switch. -/
theorem previous_output_lt_of_not_lateSwitch
    (O : OracleFamily) (stream : ℕ → ℕ) {validFrom t : ℕ}
    (htime : validFrom < t)
    (hattacker : stream t ∈ AdversaryFirst stream (output O stream))
    (hfresh : stream t ∉ sample stream t)
    (hnotSwitch : stream t ∉ lateSwitchLoss O stream validFrom) :
    output O stream (t - 1) < stream t := by
  have hfocus : stream t ∈ O.language (run O stream t).focus := by
    by_contra hout
    exact hnotSwitch
      (mem_lateSwitchLoss_of_event O stream htime hattacker hfresh hout)
  have hnotUsed := fresh_attacker_not_mem_used
    O stream hattacker hfresh
  have havailable : Available O.language stream t
      (run O stream (t - 1)).used (run O stream t).focus (stream t) :=
    ⟨hfocus, hfresh, hnotUsed⟩
  have hle := previous_output_le O stream (by omega) havailable
  have hne : output O stream (t - 1) ≠ stream t :=
    no_output_before_fresh_attacker O stream hattacker hfresh
      (t - 1) (Nat.sub_lt (by omega) Nat.zero_lt_one)
  exact lt_of_le_of_ne hle hne

/-- The concrete machine trace satisfies the abstract comparison premise used
by `GameTrace.predecessorPartner_lt`. -/
theorem gameTrace_hasPredecessorComparison
    (O : OracleFamily) (stream : ℕ → ℕ) (z validFrom : ℕ)
    (hP : Presents stream (O.language z))
    (hvalid : ∀ t, validFrom ≤ t → output O stream t ∈ O.language z) :
    (gameTrace O stream z validFrom hP hvalid).HasPredecessorComparison
      (lateSwitchLoss O stream validFrom) := by
  intro t htime hattacker hfresh hnotSwitch
  have hattacker' :
      stream t ∈ AdversaryFirst stream (output O stream) := by
    simpa [gameTrace, PatientScope.GameTrace.attacker] using hattacker
  exact previous_output_lt_of_not_lateSwitch O stream htime
    hattacker' hfresh hnotSwitch

section Partner

variable (O : OracleFamily) (stream : ℕ → ℕ) (z validFrom : ℕ)
variable (hP : Presents stream (O.language z))
variable (hvalid : ∀ t, validFrom ≤ t → output O stream t ∈ O.language z)

local notation "G" => gameTrace O stream z validFrom hP hvalid

/-- The predecessor partner is a defender-first target value. -/
theorem predecessorPartner_mem_machine
    {x : ℕ}
    (hx : x ∈ PatientScope.ordinaryAttacker
      (G).target (G).attacker (lateSwitchLoss O stream validFrom)
        (G).earlyAttacker) :
    (G).predecessorPartner x ∈ (G).defender ∩ (G).target :=
  (G).predecessorPartner_mem hx

/-- Fact 3.13's strict order comparison for the machine partner. -/
theorem predecessorPartner_lt_machine
    {x : ℕ}
    (hx : x ∈ PatientScope.ordinaryAttacker
      (G).target (G).attacker (lateSwitchLoss O stream validFrom)
        (G).earlyAttacker) :
    (G).predecessorPartner x < x :=
  (G).predecessorPartner_lt
    (gameTrace_hasPredecessorComparison O stream z validFrom hP hvalid) hx

/-- Distinct ordinary attacker values have distinct predecessor partners. -/
theorem predecessorPartner_injective_machine :
    Set.InjOn (G).predecessorPartner
      (PatientScope.ordinaryAttacker
        (G).target (G).attacker (lateSwitchLoss O stream validFrom)
          (G).earlyAttacker) :=
  (G).predecessorPartner_injective

end Partner

end PatientMachine
end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Abstract.Charging
section
set_option autoImplicit true

/-!
# Abstract charging bound for switch losses

This module isolates the finite combinatorial core of Lemma 3.14.  A finite set
of losses is assigned distinct positive focus-change counts `τ`.  Loss `ℓ` has
a finite charge set containing at least `2 ^ τ ℓ` points, all lying in the
prefix `Finset.range n`.

The paper also states that charge sets belonging to different losses are
disjoint.  That fact is not needed for the logarithmic conclusion: among `w`
distinct positive counts, one is at least `w`, and its charge set alone has at
least `2 ^ w` elements.  Thus the results below use strictly weaker hypotheses
than the paper's charging argument.
-/

namespace GenLimit

/-- A finite injective family of positive natural-number labels contains a
label at least as large as the cardinality of the family. -/
theorem exists_card_le_of_injOn_pos
    {α : Type*} [DecidableEq α]
    (losses : Finset α) (τ : α → ℕ)
    (hpos : ∀ ℓ ∈ losses, 0 < τ ℓ)
    (hinj : Set.InjOn τ losses)
    (hne : losses.Nonempty) :
    ∃ ℓ ∈ losses, losses.card ≤ τ ℓ := by
  classical
  let values : Finset ℕ := losses.image τ
  have hvalues : values.Nonempty := hne.image τ
  let M := values.max' hvalues
  have hMmem : M ∈ values := values.max'_mem hvalues
  obtain ⟨ℓ, hℓ, hτℓ⟩ := Finset.mem_image.mp hMmem
  refine ⟨ℓ, hℓ, ?_⟩
  have hsubset : values ⊆ Finset.Icc 1 M := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Icc.mpr
      ⟨hpos a ha, Finset.le_max' values (τ a) hx⟩
  have hcard : values.card = losses.card :=
    Finset.card_image_of_injOn hinj
  have hle := Finset.card_le_card hsubset
  rw [Nat.card_Icc] at hle
  have hcardM : values.card ≤ M := by
    simpa using hle
  rw [← hcard, hτℓ]
  exact hcardM

/-- The exponential form of the charging lemma.  Pairwise disjointness of the
charge sets is not required. -/
theorem charging_pow_le_prefix
    {α : Type*} [DecidableEq α]
    (losses : Finset α) (τ : α → ℕ) (charge : α → Finset ℕ) (n : ℕ)
    (hpos : ∀ ℓ ∈ losses, 0 < τ ℓ)
    (hinj : Set.InjOn τ losses)
    (hsize : ∀ ℓ ∈ losses, 2 ^ τ ℓ ≤ (charge ℓ).card)
    (hprefix : ∀ ℓ ∈ losses, charge ℓ ⊆ Finset.range n)
    (hn : 0 < n) :
    2 ^ losses.card ≤ n := by
  classical
  by_cases hne : losses.Nonempty
  · obtain ⟨ℓ, hℓ, hcardτ⟩ :=
      exists_card_le_of_injOn_pos losses τ hpos hinj hne
    calc
      2 ^ losses.card ≤ 2 ^ τ ℓ :=
        Nat.pow_le_pow_right (by omega) hcardτ
      _ ≤ (charge ℓ).card := hsize ℓ hℓ
      _ ≤ (Finset.range n).card :=
        Finset.card_le_card (hprefix ℓ hℓ)
      _ = n := Finset.card_range n
  · have hempty : losses = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simpa [hempty] using (show 1 ≤ n by omega)

/-- Lemma 3.14 in integer form: the number of certified losses in a prefix of
size `n` is at most the base-two natural logarithm of `n`. -/
theorem charging_card_le_log_two
    {α : Type*} [DecidableEq α]
    (losses : Finset α) (τ : α → ℕ) (charge : α → Finset ℕ) (n : ℕ)
    (hpos : ∀ ℓ ∈ losses, 0 < τ ℓ)
    (hinj : Set.InjOn τ losses)
    (hsize : ∀ ℓ ∈ losses, 2 ^ τ ℓ ≤ (charge ℓ).card)
    (hprefix : ∀ ℓ ∈ losses, charge ℓ ⊆ Finset.range n)
    (hn : 0 < n) :
    losses.card ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  exact charging_pow_le_prefix losses τ charge n hpos hinj hsize hprefix hn

/-- The same result using Lean's specialized `Nat.log2`. -/
theorem charging_card_le_log2
    {α : Type*} [DecidableEq α]
    (losses : Finset α) (τ : α → ℕ) (charge : α → Finset ℕ) (n : ℕ)
    (hpos : ∀ ℓ ∈ losses, 0 < τ ℓ)
    (hinj : Set.InjOn τ losses)
    (hsize : ∀ ℓ ∈ losses, 2 ^ τ ℓ ≤ (charge ℓ).card)
    (hprefix : ∀ ℓ ∈ losses, charge ℓ ⊆ Finset.range n)
    (hn : 0 < n) :
    losses.card ≤ Nat.log2 n := by
  rw [Nat.log2_eq_log_two]
  exact charging_card_le_log_two losses τ charge n hpos hinj hsize hprefix hn

end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Abstract.TargetSwitchCharging
section
set_option autoImplicit true

/-!
# Switch-loss charging inside an arbitrary target

This is the target-relative form of Lemma 3.14.  A charge assigned to a loss
lies both in the target and strictly before the loss.  Hence a loss below a
raw prefix `n` has its whole charge inside the target portion of that prefix.
-/

namespace GenLimit
namespace PatientScope

/-- Charge data for switch losses in a possibly sparse target language. -/
structure TargetSwitchChargingCertificate
    (target switchLoss : Set ℕ) where
  tau : ℕ → ℕ
  charge : ℕ → Finset ℕ
  switchLoss_subset : switchLoss ⊆ target
  tau_pos : ∀ ℓ, ℓ ∈ switchLoss → 0 < tau ℓ
  tau_injective : Set.InjOn tau switchLoss
  charge_size : ∀ ℓ, ℓ ∈ switchLoss → 2 ^ tau ℓ ≤ (charge ℓ).card
  charge_target : ∀ ℓ, ℓ ∈ switchLoss → ↑(charge ℓ) ⊆ target
  charge_before_loss : ∀ ℓ, ℓ ∈ switchLoss → charge ℓ ⊆ Finset.range ℓ

namespace TargetSwitchChargingCertificate

variable {target switchLoss : Set ℕ}
    (Q : TargetSwitchChargingCertificate target switchLoss)

include Q

omit Q in
/-- Finite charging bound with an arbitrary finite container for the charge
sets. -/
private theorem charging_card_le_log2_finset
    {α : Type*} [DecidableEq α]
    (losses : Finset α) (tau : α → ℕ)
    (charge : α → Finset ℕ) (container : Finset ℕ)
    (hpos : ∀ ℓ ∈ losses, 0 < tau ℓ)
    (hinj : Set.InjOn tau losses)
    (hsize : ∀ ℓ ∈ losses, 2 ^ tau ℓ ≤ (charge ℓ).card)
    (hcontainer : ∀ ℓ ∈ losses, charge ℓ ⊆ container) :
    losses.card ≤ Nat.log2 container.card := by
  classical
  by_cases hne : losses.Nonempty
  · rw [Nat.log2_eq_log_two]
    apply Nat.le_log_of_pow_le Nat.one_lt_two
    obtain ⟨ℓ, hℓ, hcardTau⟩ :=
      exists_card_le_of_injOn_pos losses tau hpos hinj hne
    calc
      2 ^ losses.card ≤ 2 ^ tau ℓ :=
        Nat.pow_le_pow_right (by omega) hcardTau
      _ ≤ (charge ℓ).card := hsize ℓ hℓ
      _ ≤ container.card := Finset.card_le_card (hcontainer ℓ hℓ)
  · have hempty : losses = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty]

/-- Lemma 3.14 for an arbitrary target: losses in a raw prefix are bounded by
the logarithm of the number of target values in that prefix. -/
theorem prefixCount_le_log2_targetCount (n : ℕ) :
    prefixCount switchLoss n ≤ Nat.log2 (prefixCount target n) := by
  classical
  let losses := prefixFinset switchLoss n
  let targetPrefix := prefixFinset target n
  change losses.card ≤ Nat.log2 targetPrefix.card
  apply charging_card_le_log2_finset losses Q.tau Q.charge targetPrefix
  · intro ℓ hℓ
    exact Q.tau_pos ℓ (mem_prefixFinset.mp hℓ).2
  · intro x hx y hy hxy
    exact Q.tau_injective
      (mem_prefixFinset.mp hx).2 (mem_prefixFinset.mp hy).2 hxy
  · intro ℓ hℓ
    exact Q.charge_size ℓ (mem_prefixFinset.mp hℓ).2
  · intro ℓ hℓ x hx
    have hℓparts := mem_prefixFinset.mp hℓ
    have hxTarget : x ∈ target := Q.charge_target ℓ hℓparts.2 hx
    have hxltℓ : x < ℓ := Finset.mem_range.mp
      (Q.charge_before_loss ℓ hℓparts.2 hx)
    exact mem_prefixFinset.mpr
      ⟨lt_trans hxltℓ hℓparts.1, hxTarget⟩

end TargetSwitchChargingCertificate
end PatientScope
end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Patient.Certificate
section
set_option autoImplicit true

/-!
# Final patient-scope certificate assembly

This module chooses one canonical threshold at which the presented target is
both recursively critical and inside the patient scope.  The same threshold
controls eventual output validity, the finite early exception set, and the
late switch losses used in charging.

Given concrete target-relative charge data for those late switch losses, the
module assembles the `PatientScopeCertificate` consumed by Theorem 3.15.
-/

namespace GenLimit
namespace PatientMachine

/-- Canonical first threshold witnessing eventual target criticality. -/
noncomputable def criticalStart
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) : ℕ := by
  classical
  exact Nat.find (target_eventually_recursiveCritical hP)

theorem criticalStart_spec
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) :
    ∀ t, criticalStart O stream z hP ≤ t →
      RecursiveCritical O.language stream t z := by
  classical
  exact Nat.find_spec (target_eventually_recursiveCritical hP)

/-- Canonical first threshold witnessing eventual inclusion of the target
index in the scope. -/
noncomputable def scopeStart
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) : ℕ := by
  classical
  exact Nat.find (target_eventually_in_scope O stream hP)

theorem scopeStart_spec
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) :
    ∀ t, scopeStart O stream z hP ≤ t →
      z < (run O stream t).scope := by
  classical
  exact Nat.find_spec (target_eventually_in_scope O stream hP)

/-- Canonical common threshold for the settled patient-scope regime. -/
noncomputable def settledThreshold
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) : ℕ :=
  max (criticalStart O stream z hP) (scopeStart O stream z hP)

theorem settled_target_critical
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    {t : ℕ} (ht : settledThreshold O stream z hP ≤ t) :
    RecursiveCritical O.language stream t z := by
  apply criticalStart_spec O stream z hP t
  exact le_trans (Nat.le_max_left _ _) ht

theorem settled_target_in_scope
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    {t : ℕ} (ht : settledThreshold O stream z hP ≤ t) :
    z < (run O stream t).scope := by
  apply scopeStart_spec O stream z hP t
  exact le_trans (Nat.le_max_right _ _) ht

/-- Every output from the settled threshold onward lies in the target. -/
theorem settled_output_target
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    {t : ℕ} (ht : settledThreshold O stream z hP ≤ t) :
    output O stream t ∈ O.language z := by
  have ht' : settledThreshold O stream z hP ≤ t + 1 := by omega
  have hfocus := run_focus_isFocus O hP (t + 1)
  have hsub : O.language (run O stream (t + 1)).focus ⊆ O.language z :=
    focus_subset_target hfocus
      (settled_target_in_scope O stream z hP ht')
      (settled_target_critical O stream z hP ht')
  exact hsub (output_mem_round_focus O stream t)

/-- The concrete game trace at the canonical settled threshold. -/
noncomputable def settledGameTrace
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) : PatientScope.GameTrace :=
  gameTrace O stream z (settledThreshold O stream z hP) hP
    (fun _ ht => settled_output_target O stream z hP ht)

/-- The post-validity switch-loss set used by the final certificate. -/
noncomputable def settledSwitchLoss
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) : Set ℕ :=
  lateSwitchLoss O stream (settledThreshold O stream z hP)

@[simp] theorem settledGameTrace_target
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) :
    (settledGameTrace O stream z hP).target = O.language z := rfl

@[simp] theorem settledGameTrace_validFrom
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) :
    (settledGameTrace O stream z hP).validFrom =
      settledThreshold O stream z hP := rfl

theorem settledSwitchLoss_subset
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) :
    settledSwitchLoss O stream z hP ⊆
      (settledGameTrace O stream z hP).attacker ∩
        (settledGameTrace O stream z hP).target := by
  exact lateSwitchLoss_subset_attacker_target O hP
      (fun _ ht => settled_output_target O stream z hP ht)

/-- Assemble all non-charging parts of Theorem 3.15 with a supplied concrete
target-relative charging certificate.  Its budget is
`log2 (prefixCount target n)`, exactly the target-count form needed before the
paper's order-preserving normalization. -/
noncomputable def patientScopeCertificate
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    (Q : PatientScope.TargetSwitchChargingCertificate
      (O.language z) (settledSwitchLoss O stream z hP)) :
    PatientScope.PatientScopeCertificate := by
  let G := settledGameTrace O stream z hP
  let losses := settledSwitchLoss O stream z hP
  exact G.toCertificate losses
    (settledSwitchLoss_subset O stream z hP)
    G.predecessorPartner
    (fun _ hx => predecessorPartner_mem_machine O stream z
      (settledThreshold O stream z hP) hP
      (fun _ ht => settled_output_target O stream z hP ht) hx)
    (fun _ hx => predecessorPartner_lt_machine O stream z
      (settledThreshold O stream z hP) hP
      (fun _ ht => settled_output_target O stream z hP ht) hx)
    (predecessorPartner_injective_machine O stream z
      (settledThreshold O stream z hP) hP
      (fun _ ht => settled_output_target O stream z hP ht))
    (fun n => Nat.log2 (PatientScope.prefixCount (O.language z) n))
    (fun n => Q.prefixCount_le_log2_targetCount n)

@[simp] theorem patientScopeCertificate_target
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    (Q : PatientScope.TargetSwitchChargingCertificate
      (O.language z) (settledSwitchLoss O stream z hP)) :
    (patientScopeCertificate O stream z hP Q).target = O.language z := rfl

@[simp] theorem patientScopeCertificate_switchLoss
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    (Q : PatientScope.TargetSwitchChargingCertificate
      (O.language z) (settledSwitchLoss O stream z hP)) :
    (patientScopeCertificate O stream z hP Q).switchLoss =
      settledSwitchLoss O stream z hP := rfl

@[simp] theorem patientScopeCertificate_validFrom
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    (Q : PatientScope.TargetSwitchChargingCertificate
      (O.language z) (settledSwitchLoss O stream z hP)) :
    (patientScopeCertificate O stream z hP Q).validFrom =
      settledThreshold O stream z hP := rfl

/-- The assembled certificate carries the target-aware logarithmic switch
budget supplied by `Q`. -/
theorem patientScopeCertificate_switch_bound
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    (Q : PatientScope.TargetSwitchChargingCertificate
      (O.language z) (settledSwitchLoss O stream z hP)) (n : ℕ) :
    PatientScope.prefixCount
        (patientScopeCertificate O stream z hP Q).switchLoss n ≤
      Nat.log2
        ((patientScopeCertificate O stream z hP Q).targetCount n) := by
  simpa [PatientScope.PatientScopeCertificate.targetCount] using
    Q.prefixCount_le_log2_targetCount n

end PatientMachine
end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Patient.Departure
section
set_option autoImplicit true

/-!
# Patient departures

This file formalizes the historical invariant used in the charging proof for
the patient-scope algorithm.  Whenever a language is critical and lies below
the current focus, the machine previously left that language by an upward
scope-expansion step.  Such a departure carries both its positive `tau` label
and the preceding block of `2 ^ tau` rounds spent at the departing focus.
-/

namespace GenLimit
namespace PatientMachine

/-- Round `d` is an upward departure from language `i`: the pre-round focus is
`i`, the scope-expansion branch is taken, and the post-round focus is higher. -/
def UpwardDeparture
    (O : OracleFamily) (stream : ℕ → ℕ) (i d : ℕ) : Prop :=
  (run O stream d).focus = i ∧
    (run O stream (d + 1)).move = .expand ∧
    i < (run O stream (d + 1)).focus

/-- Departure rounds from `i` strictly before time `t`. -/
noncomputable def departureTimes
    (O : OracleFamily) (stream : ℕ → ℕ) (t i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range t).filter (UpwardDeparture O stream i)

@[simp] theorem mem_departureTimes
    {O : OracleFamily} {stream : ℕ → ℕ} {t i d : ℕ} :
    d ∈ departureTimes O stream t i ↔
      d < t ∧ UpwardDeparture O stream i d := by
  classical
  simp [departureTimes]

/-- Below a surviving old critical language, new criticality is exactly old
criticality. -/
theorem critical_iff_next_below_survivor
    {C : LanguageFamily} {stream : ℕ → ℕ} {t b i : ℕ}
    (hbold : RecursiveCritical C stream t b)
    (hbnew : RecursiveCritical C stream (t + 1) b)
    (hib : i ≤ b) :
    RecursiveCritical C stream (t + 1) i ↔
      RecursiveCritical C stream t i := by
  have hbfocus : IsFocus C stream t (b + 1) b := by
    exact ⟨Nat.lt_succ_self b, hbold,
      fun j hj _ => Nat.le_of_lt_succ hj⟩
  exact recursiveCritical_iff_of_focus_consistent
    (Nat.le_succ t) hbfocus (recursiveCritical_consistent hbnew)
    i (Nat.lt_succ_of_le hib)

/-- In a backtracking step, every new critical language strictly below the
new focus was already critical and strictly below the old focus.  In either
least-consistent fallback branch there is no such language. -/
theorem critical_below_backtrack_was_below_old_focus
    {C : LanguageFamily} {stream : ℕ → ℕ} {t i : ℕ} {old : State}
    (hfocus : IsFocus C stream t old.scope old.focus)
    (hfalsified : ¬ Consistent C stream (t + 1) old.focus)
    (hexists : ∃ j, Consistent C stream (t + 1) j)
    (hiNew : RecursiveCritical C stream (t + 1) i)
    (hiBelow : i < (backtrackDecision C stream t old).focus) :
    RecursiveCritical C stream t i ∧ i < old.focus := by
  classical
  let consistent := consistentIndices C stream (t + 1) old.scope
  by_cases hcon : consistent.Nonempty
  · let survivors := survivingCriticalIndices C stream t old.scope
    by_cases hsurv : survivors.Nonempty
    · let b := highestSurvivor C stream t old.scope old.focus
      have hb := highestSurvivor_spec (fallback := old.focus) hsurv
      have hback : (backtrackDecision C stream t old).focus = b := by
        simp [backtrackDecision_of_survivor hcon hsurv, b]
      have hib : i < b := by simpa [hback] using hiBelow
      have hiOld : RecursiveCritical C stream t i :=
        (critical_iff_next_below_survivor hb.2.1 hb.2.2.1
          (Nat.le_of_lt hib)).1 hiNew
      have hbOldFocus : b < old.focus := by
        have hlt := backtrackDecision_focus_lt_of_survivor
          hfocus hfalsified hcon hsurv
        rw [hback] at hlt
        exact hlt
      exact ⟨hiOld, lt_trans hib hbOldFocus⟩
    · let b := lowestConsistentInScope C stream (t + 1)
        old.scope old.focus
      have hb := lowestConsistentInScope_spec
        (fallback := old.focus) hcon
      have hback : (backtrackDecision C stream t old).focus = b := by
        simp [backtrackDecision_of_no_survivor hcon hsurv, b]
      have hib : i < b := by simpa [hback] using hiBelow
      exact False.elim
        (hb.2.2 i hib (recursiveCritical_consistent hiNew))
  · let b := lowestConsistent C stream (t + 1) old.focus
    have hb := lowestConsistent_spec (fallback := old.focus) hexists
    have hback : (backtrackDecision C stream t old).focus = b := by
      simp [backtrackDecision_of_empty_scope hcon hexists, b]
    have hib : i < b := by simpa [hback] using hiBelow
    exact False.elim (hb.2 i hib (recursiveCritical_consistent hiNew))

/-- Every critical index below the current focus has an earlier upward
departure from that same index. -/
theorem exists_upwardDeparture_of_critical_lt_focus_of_onModel
    (O : OracleFamily) {stream : ℕ → ℕ}
    (hOn : OnModel O stream) :
    ∀ t i,
      RecursiveCritical O.language stream t i →
      i < (run O stream t).focus →
      ∃ d, d < t ∧ UpwardDeparture O stream i d := by
  intro t
  induction t with
  | zero =>
      intro i _ hi
      simp [initialState] at hi
  | succ t ih =>
      intro i hiNew hiBelow
      let old := run O stream t
      have hfocus : IsFocus O.language stream t old.scope old.focus :=
        run_focus_isFocus_of_onModel O hOn t
      have hexists : ∃ j, Consistent O.language stream (t + 1) j :=
        hOn (t + 1)
      by_cases hsurvives :
          Consistent O.language stream (t + 1) old.focus
      · have hfixed := fixed_scope_one_step hfocus hsurvives
        by_cases hchanged :
            (run O stream (t + 1)).focus = old.focus
        · have hiOld : RecursiveCritical O.language stream t i := by
            have hiscope : i < old.scope := by
              exact lt_trans (hchanged ▸ hiBelow) hfocus.1
            exact (hfixed.1 i hiscope).1 hiNew
          have hiOldFocus : i < old.focus := by
            rw [← hchanged]
            exact hiBelow
          obtain ⟨d, hdt, hdep⟩ := ih i hiOld hiOldFocus
          exact ⟨d, lt_trans hdt (Nat.lt_succ_self t), hdep⟩
        · have hchangedDecision :
              (stableDecision O.language stream t old).focus ≠ old.focus := by
            simpa [run_succ, processRound, decide, hsurvives, old] using hchanged
          have hchangeSpec := stableDecision_changed
            hfocus hsurvives hchangedDecision
          have hnewFocus : (run O stream (t + 1)).focus = old.scope := by
            simpa [run_succ, processRound, decide, hsurvives, old]
              using hchangeSpec.2
          have hiscope : i < old.scope := by
            rw [← hnewFocus]
            exact hiBelow
          have hiOld : RecursiveCritical O.language stream t i :=
            (hfixed.1 i hiscope).1 hiNew
          have hile : i ≤ old.focus := hfocus.2.2 i hiscope hiOld
          rcases eq_or_lt_of_le hile with rfl | hilt
          · refine ⟨t, Nat.lt_succ_self t, ?_⟩
            refine ⟨rfl, ?_, ?_⟩
            · simp [run_succ, processRound, decide, hsurvives, old,
                stableDecision, hchangeSpec.1]
            · simpa [old] using hiBelow
          · obtain ⟨d, hdt, hdep⟩ := ih i hiOld hilt
            exact ⟨d, lt_trans hdt (Nat.lt_succ_self t), hdep⟩
      · have hiOldBelow :=
          critical_below_backtrack_was_below_old_focus
            hfocus hsurvives hexists hiNew (by
              simpa [run_succ, processRound, decide, hsurvives, old]
                using hiBelow)
        obtain ⟨d, hdt, hdep⟩ := ih i hiOldBelow.1 hiOldBelow.2
        exact ⟨d, lt_trans hdt (Nat.lt_succ_self t), hdep⟩

/-- Exact-presentation wrapper for the on-model historical theorem. -/
theorem exists_upwardDeparture_of_critical_lt_focus
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    ∀ t i,
      RecursiveCritical O.language stream t i →
      i < (run O stream t).focus →
      ∃ d, d < t ∧ UpwardDeparture O stream i d :=
  exists_upwardDeparture_of_critical_lt_focus_of_onModel O
    (onModel_of_presents O hP)

/-- The wait test holds at every upward departure. -/
theorem upwardDeparture_wait_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {i d : ℕ}
    (hOn : OnModel O stream)
    (hdep : UpwardDeparture O stream i d) :
    2 ^ (run O stream d).tau ≤ (run O stream d).age := by
  classical
  have hfocus := run_focus_isFocus_of_onModel O hOn d
  have hstable : Consistent O.language stream (d + 1)
      (run O stream d).focus := by
    by_contra hnot
    have hmove : (run O stream (d + 1)).move = .backtrack := by
      simp [run_succ, processRound, decide, hnot,
        backtrackDecision_move]
    rw [hdep.2.1] at hmove
    cases hmove
  have hchanged :
      (stableDecision O.language stream d (run O stream d)).focus ≠
        (run O stream d).focus := by
    have hrunChanged : (run O stream (d + 1)).focus ≠
        (run O stream d).focus := by
      rw [hdep.1]
      exact Nat.ne_of_gt hdep.2.2
    simpa [run_succ, processRound, decide, hstable] using hrunChanged
  exact (stableDecision_changed hfocus hstable hchanged).1

theorem upwardDeparture_wait
    {O : OracleFamily} {stream : ℕ → ℕ} {z i d : ℕ}
    (hP : Presents stream (O.language z))
    (hdep : UpwardDeparture O stream i d) :
    2 ^ (run O stream d).tau ≤ (run O stream d).age :=
  upwardDeparture_wait_of_onModel (onModel_of_presents O hP) hdep

/-- The exponential waiting block fits before the departure time. -/
theorem upwardDeparture_pow_le_time_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {i d : ℕ}
    (hOn : OnModel O stream)
    (hdep : UpwardDeparture O stream i d) :
    2 ^ (run O stream d).tau ≤ d := by
  exact le_trans (upwardDeparture_wait_of_onModel hOn hdep)
    (run_age_le_time O stream d)

theorem upwardDeparture_pow_le_time
    {O : OracleFamily} {stream : ℕ → ℕ} {z i d : ℕ}
    (hP : Presents stream (O.language z))
    (hdep : UpwardDeparture O stream i d) :
    2 ^ (run O stream d).tau ≤ d :=
  upwardDeparture_pow_le_time_of_onModel (onModel_of_presents O hP) hdep

/-- Every post-state in the `2 ^ tau` rounds preceding a departure has the
departing focus.  The output in round `d - 1 - k` is made in post-state
`d - k`. -/
theorem upwardDeparture_age_block_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {i d k : ℕ}
    (hOn : OnModel O stream)
    (hdep : UpwardDeparture O stream i d)
    (hk : k < 2 ^ (run O stream d).tau) :
    (run O stream (d - k)).focus = i := by
  have hkAge : k < (run O stream d).age :=
    lt_of_lt_of_le hk (upwardDeparture_wait_of_onModel hOn hdep)
  rw [run_focus_eq_of_lt_age O stream d k hkAge]
  exact hdep.1

theorem upwardDeparture_age_block
    {O : OracleFamily} {stream : ℕ → ℕ} {z i d k : ℕ}
    (hP : Presents stream (O.language z))
    (hdep : UpwardDeparture O stream i d)
    (hk : k < 2 ^ (run O stream d).tau) :
    (run O stream (d - k)).focus = i :=
  upwardDeparture_age_block_of_onModel
    (onModel_of_presents O hP) hdep hk

/-- The output in each charged predecessor round belongs to the departing
language. -/
theorem upwardDeparture_block_output_mem_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {i d k : ℕ}
    (hOn : OnModel O stream)
    (hdep : UpwardDeparture O stream i d)
    (hk : k < 2 ^ (run O stream d).tau) :
    output O stream (d - 1 - k) ∈ O.language i := by
  have hpTime := upwardDeparture_pow_le_time_of_onModel hOn hdep
  have hkTime : k < d := lt_of_lt_of_le hk hpTime
  have hindex : d - 1 - k + 1 = d - k := by omega
  have hout := output_mem_round_focus O stream (d - 1 - k)
  rw [hindex, upwardDeparture_age_block_of_onModel hOn hdep hk] at hout
  exact hout

theorem upwardDeparture_block_output_mem
    {O : OracleFamily} {stream : ℕ → ℕ} {z i d k : ℕ}
    (hP : Presents stream (O.language z))
    (hdep : UpwardDeparture O stream i d)
    (hk : k < 2 ^ (run O stream d).tau) :
    output O stream (d - 1 - k) ∈ O.language i :=
  upwardDeparture_block_output_mem_of_onModel
    (onModel_of_presents O hP) hdep hk

/-- If the departing language is contained in the target, every output in
the charged block belongs to the target. -/
theorem upwardDeparture_block_output_mem_target
    {O : OracleFamily} {stream : ℕ → ℕ} {z i d k : ℕ}
    (hP : Presents stream (O.language z))
    (hdep : UpwardDeparture O stream i d)
    (hsub : O.language i ⊆ O.language z)
    (hk : k < 2 ^ (run O stream d).tau) :
    output O stream (d - 1 - k) ∈ O.language z :=
  hsub (upwardDeparture_block_output_mem hP hdep hk)

/-- If a focus `i` survives until a later time at which the focus is higher,
then some intervening stable expansion departs upward from `i`. -/
theorem exists_upwardDeparture_between_of_onModel
    (O : OracleFamily) {stream : ℕ → ℕ} {a b i : ℕ}
    (hOn : OnModel O stream)
    (hab : a < b)
    (ha : (run O stream a).focus = i)
    (hb : i < (run O stream b).focus)
    (hcon : Consistent O.language stream b i) :
    ∃ d, a ≤ d ∧ d < b ∧ UpwardDeparture O stream i d := by
  generalize hn : b - a = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
      have ha1b : a + 1 ≤ b := Nat.succ_le_of_lt hab
      have hconNext : Consistent O.language stream (a + 1) i :=
        consistent_of_time_le ha1b hcon
      have hfocus := run_focus_isFocus_of_onModel O hOn a
      have hstable : Consistent O.language stream (a + 1)
          (run O stream a).focus := by simpa [ha] using hconNext
      have hleDecision := stableDecision_focus_le hfocus hstable
      have hle : i ≤ (run O stream (a + 1)).focus := by
        rw [run_succ_focus, decide, if_pos hstable]
        simpa [ha] using hleDecision
      by_cases heq : (run O stream (a + 1)).focus = i
      · have ha1ltb : a + 1 < b := by
          by_contra hnot
          have heqb : a + 1 = b := Nat.le_antisymm ha1b (Nat.le_of_not_gt hnot)
          rw [← heqb, heq] at hb
          exact (Nat.lt_irrefl i) hb
        have hdist : b - (a + 1) < n := by omega
        obtain ⟨d, ha1d, hdb, hdep⟩ :=
          ih (b - (a + 1)) hdist (a := a + 1) (b := b)
            ha1ltb heq hb hcon rfl
        exact ⟨d, le_trans (Nat.le_succ a) ha1d, hdb, hdep⟩
      · have hlt : i < (run O stream (a + 1)).focus := by omega
        have hchanged :
            (stableDecision O.language stream a (run O stream a)).focus ≠
              (run O stream a).focus := by
          have : (run O stream (a + 1)).focus ≠
              (run O stream a).focus := by
            rw [ha]
            exact heq
          simpa [run_succ, processRound, decide, hstable] using this
        have hwait := (stableDecision_changed hfocus hstable hchanged).1
        refine ⟨a, Nat.le_refl a, hab, ha, ?_, hlt⟩
        simp [run_succ, processRound, decide, hstable,
          stableDecision, hwait]

theorem exists_upwardDeparture_between
    (O : OracleFamily) {stream : ℕ → ℕ} {z a b i : ℕ}
    (hP : Presents stream (O.language z))
    (hab : a < b)
    (ha : (run O stream a).focus = i)
    (hb : i < (run O stream b).focus)
    (hcon : Consistent O.language stream b i) :
    ∃ d, a ≤ d ∧ d < b ∧ UpwardDeparture O stream i d :=
  exists_upwardDeparture_between_of_onModel O
    (onModel_of_presents O hP) hab ha hb hcon

/-- A certified downward landing is a backtracking endpoint which was already
critical immediately before the landing.  Late switch losses have this form
because the target is a surviving critical language. -/
structure CertifiedLanding
    (O : OracleFamily) (stream : ℕ → ℕ) (t i : ℕ) : Prop where
  oldCritical : RecursiveCritical O.language stream t i
  newFocus : (run O stream (t + 1)).focus = i
  belowOldFocus : i < (run O stream t).focus

/-- Latest departure before `t`, totalized by zero when there is none. -/
noncomputable def latestDeparture
    (O : OracleFamily) (stream : ℕ → ℕ) (t i : ℕ) : ℕ := by
  classical
  let ds := departureTimes O stream t i
  exact GenLimit.Support.greatestCandidateWithFallback ds 0

theorem latestDeparture_spec
    {O : OracleFamily} {stream : ℕ → ℕ} {t i : ℕ}
    (hne : (departureTimes O stream t i).Nonempty) :
    latestDeparture O stream t i < t ∧
      UpwardDeparture O stream i (latestDeparture O stream t i) := by
  classical
  let ds := departureTimes O stream t i
  have hmem : GenLimit.Support.greatestCandidateWithFallback ds 0 ∈ ds :=
    GenLimit.Support.greatestCandidateWithFallback_mem hne
  simpa [latestDeparture, ds] using mem_departureTimes.mp hmem

theorem departure_le_latest
    {O : OracleFamily} {stream : ℕ → ℕ} {t i d : ℕ}
    (_hne : (departureTimes O stream t i).Nonempty)
    (hd : d < t) (hdep : UpwardDeparture O stream i d) :
    d ≤ latestDeparture O stream t i := by
  classical
  let ds := departureTimes O stream t i
  have hdmem : d ∈ ds := mem_departureTimes.mpr ⟨hd, hdep⟩
  have hle := GenLimit.Support.le_greatestCandidateWithFallback
    (fallback := 0) hdmem
  simpa [latestDeparture, ds] using hle

theorem CertifiedLanding.departureTimes_nonempty_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {t i : ℕ}
    (hOn : OnModel O stream)
    (hland : CertifiedLanding O stream t i) :
    (departureTimes O stream t i).Nonempty := by
  obtain ⟨d, hdt, hdep⟩ :=
    exists_upwardDeparture_of_critical_lt_focus_of_onModel O hOn t i
      hland.oldCritical hland.belowOldFocus
  exact ⟨d, mem_departureTimes.mpr ⟨hdt, hdep⟩⟩

theorem CertifiedLanding.departureTimes_nonempty
    {O : OracleFamily} {stream : ℕ → ℕ} {z t i : ℕ}
    (hP : Presents stream (O.language z))
    (hland : CertifiedLanding O stream t i) :
    (departureTimes O stream t i).Nonempty :=
  hland.departureTimes_nonempty_of_onModel (onModel_of_presents O hP)

theorem CertifiedLanding.latestDeparture_spec_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {t i : ℕ}
    (hOn : OnModel O stream)
    (hland : CertifiedLanding O stream t i) :
    latestDeparture O stream t i < t ∧
      UpwardDeparture O stream i (latestDeparture O stream t i) :=
  PatientMachine.latestDeparture_spec
    (hland.departureTimes_nonempty_of_onModel hOn)

theorem CertifiedLanding.latestDeparture_spec
    {O : OracleFamily} {stream : ℕ → ℕ} {z t i : ℕ}
    (hP : Presents stream (O.language z))
    (hland : CertifiedLanding O stream t i) :
    latestDeparture O stream t i < t ∧
      UpwardDeparture O stream i (latestDeparture O stream t i) :=
  hland.latestDeparture_spec_of_onModel (onModel_of_presents O hP)

/-- Two successive certified landings at the same focus use strictly
increasing latest-departure rounds. -/
theorem latestDeparture_lt_of_certifiedLanding_same_focus_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {t u i : ℕ}
    (hOn : OnModel O stream)
    (htu : t < u)
    (ht : CertifiedLanding O stream t i)
    (hu : CertifiedLanding O stream u i) :
    latestDeparture O stream t i < latestDeparture O stream u i := by
  have htSpec := ht.latestDeparture_spec_of_onModel hOn
  have huNonempty := hu.departureTimes_nonempty_of_onModel hOn
  have ht1u : t + 1 < u := by
    by_contra hnot
    have hueq : u = t + 1 := by omega
    have hbelow := hu.belowOldFocus
    rw [hueq, ht.newFocus] at hbelow
    exact (Nat.lt_irrefl i) hbelow
  have hcon : Consistent O.language stream u i :=
    recursiveCritical_consistent hu.oldCritical
  obtain ⟨d, ht1d, hdu, hdep⟩ := exists_upwardDeparture_between_of_onModel
    O hOn ht1u ht.newFocus hu.belowOldFocus hcon
  have hdLatest : d ≤ latestDeparture O stream u i :=
    departure_le_latest huNonempty hdu hdep
  exact lt_of_lt_of_le (lt_trans htSpec.1 (lt_of_lt_of_le
    (Nat.lt_succ_self t) ht1d)) hdLatest

theorem latestDeparture_lt_of_certifiedLanding_same_focus
    {O : OracleFamily} {stream : ℕ → ℕ} {z t u i : ℕ}
    (hP : Presents stream (O.language z))
    (htu : t < u)
    (ht : CertifiedLanding O stream t i)
    (hu : CertifiedLanding O stream u i) :
    latestDeparture O stream t i < latestDeparture O stream u i :=
  latestDeparture_lt_of_certifiedLanding_same_focus_of_onModel
    (onModel_of_presents O hP) htu ht hu

/-- The canonical latest departure determines a certified landing's time and
focus. -/
theorem certifiedLanding_latestDeparture_injective_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {t u i j : ℕ}
    (hOn : OnModel O stream)
    (ht : CertifiedLanding O stream t i)
    (hu : CertifiedLanding O stream u j)
    (heq : latestDeparture O stream t i =
      latestDeparture O stream u j) :
    t = u ∧ i = j := by
  have htSpec := ht.latestDeparture_spec_of_onModel hOn
  have huSpec := hu.latestDeparture_spec_of_onModel hOn
  have hij : i = j := by
    calc
      i = (run O stream (latestDeparture O stream t i)).focus :=
        htSpec.2.1.symm
      _ = (run O stream (latestDeparture O stream u j)).focus := by rw [heq]
      _ = j := huSpec.2.1
  subst j
  refine ⟨?_, rfl⟩
  rcases lt_trichotomy t u with htu | htu | hut
  · have hlt := latestDeparture_lt_of_certifiedLanding_same_focus_of_onModel
      hOn htu ht hu
    exact False.elim ((Nat.ne_of_lt hlt) heq)
  · exact htu
  · have hlt := latestDeparture_lt_of_certifiedLanding_same_focus_of_onModel
      hOn hut hu ht
    exact False.elim ((Nat.ne_of_lt hlt) heq.symm)

theorem certifiedLanding_latestDeparture_injective
    {O : OracleFamily} {stream : ℕ → ℕ} {z t u i j : ℕ}
    (hP : Presents stream (O.language z))
    (ht : CertifiedLanding O stream t i)
    (hu : CertifiedLanding O stream u j)
    (heq : latestDeparture O stream t i =
      latestDeparture O stream u j) :
    t = u ∧ i = j :=
  certifiedLanding_latestDeparture_injective_of_onModel
    (onModel_of_presents O hP) ht hu heq

/-- Canonical focus-change label attached to a certified landing. -/
noncomputable def landingLabel
    (O : OracleFamily) (stream : ℕ → ℕ) (t i : ℕ) : ℕ :=
  (run O stream (latestDeparture O stream t i)).tau

/-- Tau labels of different upward-departure rounds are different. -/
theorem upwardDeparture_tau_injective
    (O : OracleFamily) (stream : ℕ → ℕ) :
    Set.InjOn (fun d => (run O stream d).tau)
      {d | ∃ i, UpwardDeparture O stream i d} := by
  intro d hd e he hlabel
  rcases lt_trichotomy d e with hde | rfl | hed
  · obtain ⟨i, hi⟩ := hd
    have hchange : (run O stream (d + 1)).focus ≠
        (run O stream d).focus := by
      exact Nat.ne_of_gt (hi.1 ▸ hi.2.2)
    have hstep := run_succ_tau_eq_succ_of_focus_ne O stream d hchange
    have hmono := run_tau_mono O stream (Nat.succ_le_of_lt hde)
    have hlt : (run O stream d).tau < (run O stream e).tau := by
      calc
        (run O stream d).tau < (run O stream (d + 1)).tau := by omega
        _ ≤ (run O stream e).tau := hmono
    exact False.elim ((Nat.ne_of_lt hlt) hlabel)
  · rfl
  · obtain ⟨i, hi⟩ := he
    have hchange : (run O stream (e + 1)).focus ≠
        (run O stream e).focus := by
      exact Nat.ne_of_gt (hi.1 ▸ hi.2.2)
    have hstep := run_succ_tau_eq_succ_of_focus_ne O stream e hchange
    have hmono := run_tau_mono O stream (Nat.succ_le_of_lt hed)
    have hlt : (run O stream e).tau < (run O stream d).tau := by
      calc
        (run O stream e).tau < (run O stream (e + 1)).tau := by omega
        _ ≤ (run O stream d).tau := hmono
    exact False.elim ((Nat.ne_of_lt hlt) hlabel.symm)

/-- Equal canonical labels force equality of certified landing times and
focus indices. -/
theorem certifiedLanding_label_injective_of_onModel
    {O : OracleFamily} {stream : ℕ → ℕ} {t u i j : ℕ}
    (hOn : OnModel O stream)
    (ht : CertifiedLanding O stream t i)
    (hu : CertifiedLanding O stream u j)
    (heq : landingLabel O stream t i = landingLabel O stream u j) :
    t = u ∧ i = j := by
  have htSpec := ht.latestDeparture_spec_of_onModel hOn
  have huSpec := hu.latestDeparture_spec_of_onModel hOn
  have hdepEq : latestDeparture O stream t i =
      latestDeparture O stream u j := by
    apply upwardDeparture_tau_injective O stream
    · exact ⟨i, htSpec.2⟩
    · exact ⟨j, huSpec.2⟩
    · exact heq
  exact certifiedLanding_latestDeparture_injective_of_onModel
    hOn ht hu hdepEq

theorem certifiedLanding_label_injective
    {O : OracleFamily} {stream : ℕ → ℕ} {z t u i j : ℕ}
    (hP : Presents stream (O.language z))
    (ht : CertifiedLanding O stream t i)
    (hu : CertifiedLanding O stream u j)
    (heq : landingLabel O stream t i = landingLabel O stream u j) :
    t = u ∧ i = j :=
  certifiedLanding_label_injective_of_onModel
    (onModel_of_presents O hP) ht hu heq

end PatientMachine
end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging
section
set_option autoImplicit true

/-!
# Charging from a stable target witness

The patient-scope charging argument does not require an exact presentation of
a family member.  Its common core only needs an eventually permanent critical
witness contained in the true target, eventual inclusion of that witness in
scope, and the ordinary on-model invariant.  Exact and partial presentations
instantiate this package in their respective certificate modules.
-/

namespace GenLimit
namespace PatientMachine

/-- The hypotheses shared by the exact- and partial-presentation charging
arguments. -/
structure StableTargetRun
    (O : OracleFamily) (stream : ℕ → ℕ) (K : Language) where
  witness : ℕ
  threshold : ℕ
  onModel : OnModel O stream
  critical : ∀ t, threshold ≤ t →
    RecursiveCritical O.language stream t witness
  inScope : ∀ t, threshold ≤ t → witness < (run O stream t).scope
  witness_subset_target : O.language witness ⊆ K
  adversary_target : ∀ t, stream t ∈ K

namespace StableTargetRun

variable {O : OracleFamily} {stream : ℕ → ℕ} {K : Language}
    (S : StableTargetRun O stream K)

theorem output_target {t : ℕ} (ht : S.threshold ≤ t) :
    output O stream t ∈ K := by
  have ht' : S.threshold ≤ t + 1 := le_trans ht (Nat.le_succ t)
  have hfocus := run_focus_isFocus_of_onModel O S.onModel (t + 1)
  have hsub : O.language (run O stream (t + 1)).focus ⊆
      O.language S.witness :=
    focus_subset_target hfocus (S.inScope (t + 1) ht')
      (S.critical (t + 1) ht')
  exact S.witness_subset_target
    (hsub (output_available_post_focus O stream t).1)

def IsSwitchTime (x t : ℕ) : Prop :=
  S.threshold < t ∧ stream t = x ∧ x ∉ sample stream t ∧
    SwitchRound O stream t

noncomputable def switchTime (x : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, S.IsSwitchTime x t then Nat.find h else 0

theorem switchTime_spec {x : ℕ}
    (hx : x ∈ lateSwitchLoss O stream S.threshold) :
    S.IsSwitchTime x (S.switchTime x) := by
  classical
  rcases hx with ⟨-, t, ht, htx, hfresh, hswitch⟩
  have hexists : ∃ q, S.IsSwitchTime x q :=
    ⟨t, ht, htx, hfresh, hswitch⟩
  simp [switchTime, hexists]
  exact Nat.find_spec hexists

noncomputable def landingFocus (x : ℕ) : ℕ :=
  (run O stream (S.switchTime x + 1)).focus

theorem certifiedLanding {x : ℕ}
    (hx : x ∈ lateSwitchLoss O stream S.threshold) :
    CertifiedLanding O stream (S.switchTime x) (S.landingFocus x) := by
  classical
  let t := S.switchTime x
  let old := run O stream t
  let i := S.landingFocus x
  have htime := S.switchTime_spec hx
  have htT : S.threshold ≤ t := Nat.le_of_lt htime.1
  have hfocus : IsFocus O.language stream t old.scope old.focus :=
    run_focus_isFocus_of_onModel O S.onModel t
  have hfalsified : ¬ Consistent O.language stream (t + 1) old.focus := by
    intro hcon
    exact htime.2.2.2
      (hcon (value_mem_sample (stream := stream) (Nat.lt_succ_self t)))
  have hwOld := S.critical t htT
  have hwNew := S.critical (t + 1) (by omega)
  have hwScope := S.inScope t htT
  have hcon :
      (consistentIndices O.language stream (t + 1) old.scope).Nonempty :=
    ⟨S.witness, mem_consistentIndices.mpr
      ⟨hwScope, recursiveCritical_consistent hwNew⟩⟩
  have hsurv :
      (survivingCriticalIndices O.language stream t old.scope).Nonempty :=
    ⟨S.witness, mem_survivingCriticalIndices.mpr
      ⟨hwScope, hwOld, hwNew⟩⟩
  let b := highestSurvivor O.language stream t old.scope old.focus
  have hb := highestSurvivor_spec (fallback := old.focus) hsurv
  have hnewEq : (run O stream (t + 1)).focus = b := by
    calc
      (run O stream (t + 1)).focus =
          (PatientMachine.decide O.language stream t old).focus := by simp [old]
      _ = (backtrackDecision O.language stream t old).focus := by
        simp [PatientMachine.decide, hfalsified]
      _ = b := by
        have hback := backtrackDecision_of_survivor hcon hsurv
        simpa [b] using congrArg Decision.focus hback
  have hiEq : i = b := by simpa [i, landingFocus] using hnewEq
  have hbelow : b < old.focus := by
    have hlt := backtrackDecision_focus_lt_of_survivor
      hfocus hfalsified hcon hsurv
    simpa [run_succ, processRound, PatientMachine.decide, hfalsified,
      backtrackDecision_of_survivor hcon hsurv, b] using hlt
  refine ⟨?_, ?_, ?_⟩
  · change RecursiveCritical O.language stream t i
    rw [hiEq]
    exact hb.2.1
  · change (run O stream (t + 1)).focus = i
    exact hnewEq.trans hiEq.symm
  · change i < old.focus
    rw [hiEq]
    exact hbelow

theorem landing_subset_target {x : ℕ}
    (hx : x ∈ lateSwitchLoss O stream S.threshold) :
    O.language (S.landingFocus x) ⊆ K := by
  let t := S.switchTime x
  let i := S.landingFocus x
  have hland := S.certifiedLanding hx
  have htime := S.switchTime_spec hx
  have htT : S.threshold ≤ t := Nat.le_of_lt htime.1
  have ht1T : S.threshold ≤ t + 1 := le_trans htT (Nat.le_succ t)
  have hw := S.critical t htT
  have hi := hland.oldCritical
  have hwNew := S.critical (t + 1) ht1T
  have hwScopeNew := S.inScope (t + 1) ht1T
  have hfocusNew := run_focus_isFocus_of_onModel O S.onModel (t + 1)
  have hwi : S.witness ≤ i := by
    have := hfocusNew.2.2 S.witness hwScopeNew hwNew
    simpa [i, landingFocus] using this
  exact Set.Subset.trans
    (recursiveCritical_subset_of_le hwi hw hi)
    S.witness_subset_target

noncomputable def departure (x : ℕ) : ℕ :=
  latestDeparture O stream (S.switchTime x) (S.landingFocus x)

noncomputable def tau (x : ℕ) : ℕ :=
  (run O stream (S.departure x)).tau

noncomputable def charge (x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 ^ S.tau x)).image fun k =>
    output O stream (S.departure x - 1 - k)

theorem departure_spec {x : ℕ}
    (hx : x ∈ lateSwitchLoss O stream S.threshold) :
    S.departure x < S.switchTime x ∧
      UpwardDeparture O stream (S.landingFocus x) (S.departure x) := by
  simpa [departure] using
    (S.certifiedLanding hx).latestDeparture_spec_of_onModel S.onModel

theorem tau_pos {x : ℕ}
    (_hx : x ∈ lateSwitchLoss O stream S.threshold) : 0 < S.tau x :=
  run_tau_pos O stream (S.departure x)

theorem tau_injective : Set.InjOn S.tau
    (lateSwitchLoss O stream S.threshold) := by
  intro x hx y hy hxy
  have hxLand := S.certifiedLanding hx
  have hyLand := S.certifiedLanding hy
  have hpair := certifiedLanding_label_injective_of_onModel S.onModel
    hxLand hyLand (by simpa [tau, departure, landingLabel] using hxy)
  have hxTime := S.switchTime_spec hx
  have hyTime := S.switchTime_spec hy
  calc
    x = stream (S.switchTime x) := hxTime.2.1.symm
    _ = stream (S.switchTime y) := by rw [hpair.1]
    _ = y := hyTime.2.1

theorem charge_card {x : ℕ}
    (hx : x ∈ lateSwitchLoss O stream S.threshold) :
    (S.charge x).card = 2 ^ S.tau x := by
  classical
  let d := S.departure x
  let p := 2 ^ S.tau x
  let rounds := Finset.range p
  let f : ℕ → ℕ := fun k => output O stream (d - 1 - k)
  have hdep := (S.departure_spec hx).2
  have hpTime : p ≤ d := by
    simpa [p, tau, d] using
      upwardDeparture_pow_le_time_of_onModel S.onModel hdep
  have hfInj : Set.InjOn f rounds := by
    intro k hk l hl hkl
    have hklt : k < p := by simpa [rounds] using hk
    have hllt : l < p := by simpa [rounds] using hl
    have hroundEq : d - 1 - k = d - 1 - l :=
      output_injective O stream hkl
    omega
  change (rounds.image f).card = p
  rw [Finset.card_image_of_injOn hfInj]
  exact Finset.card_range p

theorem charge_mem_target {x y : ℕ}
    (hx : x ∈ lateSwitchLoss O stream S.threshold)
    (hy : y ∈ S.charge x) : y ∈ K := by
  classical
  let d := S.departure x
  let p := 2 ^ S.tau x
  have hdep := (S.departure_spec hx).2
  have hsub := S.landing_subset_target hx
  rw [charge] at hy
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
  have hk' : k < 2 ^ (run O stream d).tau := by
    simpa [p, tau, d] using (Finset.mem_range.mp hk)
  exact hsub
    (upwardDeparture_block_output_mem_of_onModel S.onModel hdep hk')

theorem charge_lt_loss {x y : ℕ}
    (hx : x ∈ lateSwitchLoss O stream S.threshold)
    (hy : y ∈ S.charge x) : y < x := by
  classical
  let t := S.switchTime x
  let i := S.landingFocus x
  let d := S.departure x
  let p := 2 ^ S.tau x
  have htime := S.switchTime_spec hx
  have hdepSpec := S.departure_spec hx
  have hdep : UpwardDeparture O stream i d := hdepSpec.2
  have hdt : d < t := hdepSpec.1
  have hpTime : p ≤ d := by
    simpa [p, tau, d] using
      upwardDeparture_pow_le_time_of_onModel S.onModel hdep
  have hxAttacker : x ∈ AdversaryFirst stream (output O stream) := hx.1
  have hxFresh : x ∉ sample stream t := htime.2.2.1
  have hxStream : stream t = x := htime.2.1
  have hstreamAttacker : stream t ∈
      AdversaryFirst stream (output O stream) := by
    simpa [hxStream] using hxAttacker
  have hstreamFresh : stream t ∉ sample stream t := by
    simpa [hxStream] using hxFresh
  have hpostFocus := run_focus_isFocus_of_onModel O S.onModel (t + 1)
  have hxSample : x ∈ sample stream (t + 1) := by
    rw [mem_sample_iff]
    exact ⟨t, Nat.lt_succ_self t, hxStream⟩
  have hxLanding : x ∈ O.language i := by
    change x ∈ O.language (run O stream (t + 1)).focus
    exact (recursiveCritical_consistent hpostFocus.2.1) hxSample
  rw [charge] at hy
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
  have hkP : k < p := by simpa [p] using (Finset.mem_range.mp hk)
  let r := d - 1 - k
  have hrD : r < d := by
    have hpPos : 0 < p := by dsimp [p]; exact Nat.two_pow_pos _
    dsimp [r]
    omega
  have hrT : r < t := lt_trans hrD hdt
  have hr1T : r + 1 ≤ t := Nat.succ_le_of_lt hrT
  have hkTau : k < 2 ^ (run O stream d).tau := by
    simpa [p, tau, d] using hkP
  have hpostEq : (run O stream (r + 1)).focus = i := by
    have hblock := upwardDeparture_age_block_of_onModel
      S.onModel hdep hkTau
    have hindex : r + 1 = d - k := by dsimp [r]; omega
    rwa [hindex]
  have hxNotSample : x ∉ sample stream (r + 1) := by
    intro hm
    exact hxFresh (sample_mono hr1T hm)
  have hxNotUsed : x ∉ (run O stream r).used := by
    intro hm
    rw [mem_run_used_iff] at hm
    obtain ⟨s, hsr, hsx⟩ := hm
    have hst : s < t := lt_trans hsr hrT
    have hne := no_output_before_fresh_attacker
      O stream hstreamAttacker hstreamFresh s hst
    exact hne (by simpa [hxStream] using hsx)
  have hxAvailable : Available O.language stream (r + 1)
      (run O stream r).used (run O stream (r + 1)).focus x := by
    refine ⟨?_, hxNotSample, hxNotUsed⟩
    rw [hpostEq]
    exact hxLanding
  have hle : output O stream r ≤ x :=
    output_minimal_post_focus O stream r x hxAvailable
  have hne : output O stream r ≠ x := by
    have hne' := no_output_before_fresh_attacker
      O stream hstreamAttacker hstreamFresh r hrT
    simpa [hxStream] using hne'
  exact lt_of_le_of_ne hle hne

noncomputable def chargingCertificate :
    PatientScope.TargetSwitchChargingCertificate K
      (lateSwitchLoss O stream S.threshold) where
  tau := S.tau
  charge := S.charge
  switchLoss_subset := by
    intro x hx
    rcases hx.2 with ⟨t, -, htx, -, -⟩
    simpa [← htx] using S.adversary_target t
  tau_pos := fun _ hx => S.tau_pos hx
  tau_injective := S.tau_injective
  charge_size := by
    intro x hx
    rw [S.charge_card hx]
  charge_target := fun _ hx _ hy => S.charge_mem_target hx hy
  charge_before_loss := by
    intro x hx y hy
    exact Finset.mem_range.mpr (S.charge_lt_loss hx hy)

end StableTargetRun
end PatientMachine
end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Patient.Charging
section
set_option autoImplicit true

/-!
# Charging settled switch losses

This module instantiates the shared stable-target charging argument for an
exact presentation.  The settled target index is the permanent witness and
`settledThreshold` is the common stabilization threshold.
-/

namespace GenLimit
namespace PatientMachine

/-- The shared charging hypotheses supplied by an exact presentation after
the canonical settled threshold. -/
private noncomputable def settledStableTargetRun
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) :
    StableTargetRun O stream (O.language z) where
  witness := z
  threshold := settledThreshold O stream z hP
  onModel := onModel_of_presents O hP
  critical := fun _ ht => settled_target_critical O stream z hP ht
  inScope := fun _ ht => settled_target_in_scope O stream z hP ht
  witness_subset_target := Set.Subset.rfl
  adversary_target := by
    intro t
    rw [← hP]
    exact ⟨t, rfl⟩

/-- Concrete target-relative form of Lemma 3.14. -/
noncomputable def settledChargingCertificate
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) :
    PatientScope.TargetSwitchChargingCertificate
      (O.language z) (settledSwitchLoss O stream z hP) := by
  simpa [settledSwitchLoss, settledStableTargetRun] using
    (settledStableTargetRun O stream z hP).chargingCertificate

/-- Lemma 3.14 in ambient prefixes: the logarithm counts target elements,
so this also covers sparse targets without identifying the target with `ℕ`.
`settledSwitchLoss` excludes the finite initial segment before stabilization. -/
theorem lemma_3_14
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) (n : ℕ) :
    PatientScope.prefixCount (settledSwitchLoss O stream z hP) n ≤
      Nat.log2 (PatientScope.prefixCount (O.language z) n) :=
  (settledChargingCertificate O stream z hP).prefixCount_le_log2_targetCount n

end PatientMachine
end GenLimit

end

-- GenLimit.Core.OrderedDensity
section
set_option autoImplicit true

/-!
# Ordered relative density

This file records the ordered-density language shared by the three
Kleinberg--Wei papers.  In the notation of Definition 4.1 of
*Density Measures for Language Generation*, `enumeration` lists the elements
of the reference language `K` without repetition.  Density is measured in the
first `n` positions of that ordering, rather than in ambient natural-number
prefixes.
-/

namespace GenLimit
namespace KleinbergWei

open Filter

/-- A duplicate-free ordering of all strings in a language. -/
structure OrderedLanguage where
  carrier : Language
  enumeration : ℕ → ℕ
  enumeration_injective : Function.Injective enumeration
  range_enumeration : Set.range enumeration = carrier

namespace OrderedLanguage

/-- Number of the first `n` ordered strings of `K` which belong to `A`. -/
noncomputable def prefixCount (K : OrderedLanguage) (A : Language) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range n).filter fun i => K.enumeration i ∈ A).card

theorem prefixCount_le (K : OrderedLanguage) (A : Language) (n : ℕ) :
    K.prefixCount A n ≤ n := by
  classical
  simpa [prefixCount] using
    Finset.card_filter_le (s := Finset.range n) (p := fun i => K.enumeration i ∈ A)

/-- Ranks in the fixed ordering whose strings belong to `A`. -/
def rankSet (K : OrderedLanguage) (A : Language) : Set ℕ :=
  {i | K.enumeration i ∈ A}

/-- Elements of an arbitrary rank set below `n`. -/
noncomputable def rankPrefix (P : Set ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter fun i => i ∈ P

@[simp] theorem mem_rankPrefix {P : Set ℕ} {n i : ℕ} :
    i ∈ rankPrefix P n ↔ i < n ∧ i ∈ P := by
  classical
  simp [rankPrefix]

@[simp] theorem rankPrefix_rankSet_card
    (K : OrderedLanguage) (A : Language) (n : ℕ) :
    (rankPrefix (K.rankSet A) n).card = K.prefixCount A n :=
  rfl

theorem rankPrefix_subset_succ (P : Set ℕ) (n : ℕ) :
    rankPrefix P n ⊆ rankPrefix P (n + 1) := by
  classical
  intro i hi
  have hi' : i < n ∧ i ∈ P := mem_rankPrefix.mp hi
  exact mem_rankPrefix.mpr ⟨Nat.lt.step hi'.1, hi'.2⟩

/-- Adding one ordered position changes a prefix count by at most one. -/
theorem prefixCount_succ_le_add_one
    (K : OrderedLanguage) (A : Language) (n : ℕ) :
    K.prefixCount A (n + 1) ≤ K.prefixCount A n + 1 := by
  classical
  let old := rankPrefix (K.rankSet A) n
  let new := rankPrefix (K.rankSet A) (n + 1)
  have hsub : new ⊆ insert n old := by
    intro i hi
    by_cases hin : i = n
    · subst i
      simp
    · apply Finset.mem_insert_of_mem
      apply mem_rankPrefix.mpr
      have hi' := mem_rankPrefix.mp hi
      exact ⟨by omega, hi'.2⟩
  have hcard : new.card ≤ old.card + 1 := by
    calc
      new.card ≤ (insert n old).card := Finset.card_le_card hsub
      _ ≤ old.card + 1 := Finset.card_insert_le n old
  simpa [old, new] using hcard

/-- Outside finitely many exceptional source ranks, an injective charge that
moves rank `i` by at most `offset` embeds each source prefix into the shifted
output prefix. -/
theorem rankPrefix_card_le_shifted_output_add_exceptions
    (K : OrderedLanguage) (sourceRanks : Set ℕ) (output : Language)
    (charge : ℕ → ℕ) (offset : ℕ) (exceptions : Finset ℕ)
    (houtput : ∀ ⦃i : ℕ⦄, i ∈ sourceRanks → i ∉ exceptions →
      K.enumeration (charge i) ∈ output)
    (hle : ∀ ⦃i : ℕ⦄, i ∈ sourceRanks → i ∉ exceptions →
      charge i ≤ i + offset)
    (hinjective : Set.InjOn charge
      (sourceRanks \ (exceptions : Set ℕ)))
    (n : ℕ) :
    (rankPrefix sourceRanks n).card ≤
      K.prefixCount output (n + offset) + exceptions.card := by
  classical
  let sourcePrefix := rankPrefix sourceRanks n
  let clean := sourcePrefix \ exceptions
  let outputPrefix := rankPrefix (K.rankSet output) (n + offset)
  have hmaps : Set.MapsTo charge clean outputPrefix := by
    intro i hi
    have hiParts := Finset.mem_sdiff.mp hi
    have hiSource := (mem_rankPrefix.mp hiParts.1).2
    apply mem_rankPrefix.mpr
    refine ⟨?_, houtput hiSource hiParts.2⟩
    have hiRange := (mem_rankPrefix.mp hiParts.1).1
    have hcharge := hle hiSource hiParts.2
    omega
  have hinj : Set.InjOn charge clean := by
    intro i hi j hj hij
    apply hinjective
    · exact ⟨(mem_rankPrefix.mp (Finset.mem_sdiff.mp hi).1).2,
        (Finset.mem_sdiff.mp hi).2⟩
    · exact ⟨(mem_rankPrefix.mp (Finset.mem_sdiff.mp hj).1).2,
        (Finset.mem_sdiff.mp hj).2⟩
    · exact hij
  have hclean : clean.card ≤ outputPrefix.card :=
    Finset.card_le_card_of_injOn charge hmaps hinj
  have hcover : sourcePrefix ⊆ clean ∪ exceptions := by
    intro i hi
    by_cases hie : i ∈ exceptions
    · exact Finset.mem_union_right _ hie
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi, hie⟩)
  have hsource : sourcePrefix.card ≤ clean.card + exceptions.card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  simpa [sourcePrefix, clean, outputPrefix] using
    hsource.trans (Nat.add_le_add_right hclean _)

/-- Exception-free specialization of
`rankPrefix_card_le_shifted_output_add_exceptions`. -/
theorem rankPrefix_card_le_shifted_output
    (K : OrderedLanguage) (sourceRanks : Set ℕ) (output : Language)
    (charge : ℕ → ℕ) (offset : ℕ)
    (houtput : ∀ ⦃i : ℕ⦄, i ∈ sourceRanks →
      K.enumeration (charge i) ∈ output)
    (hle : ∀ ⦃i : ℕ⦄, i ∈ sourceRanks → charge i ≤ i + offset)
    (hinjective : Set.InjOn charge sourceRanks)
    (n : ℕ) :
    (rankPrefix sourceRanks n).card ≤
      K.prefixCount output (n + offset) := by
  simpa using K.rankPrefix_card_le_shifted_output_add_exceptions
    sourceRanks output charge offset ∅
    (fun {_i} hi _ => houtput hi) (fun {_i} hi _ => hle hi)
    (by simpa using hinjective) n

theorem prefixCount_mono
    (K : OrderedLanguage) {A B : Language} (hAB : A ⊆ B) (n : ℕ) :
    K.prefixCount A n ≤ K.prefixCount B n := by
  classical
  unfold prefixCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hAB hi.2⟩

@[simp] theorem prefixCount_empty (K : OrderedLanguage) (n : ℕ) :
    K.prefixCount (∅ : Language) n = 0 := by
  classical
  simp [prefixCount]

@[simp] theorem prefixCount_carrier (K : OrderedLanguage) (n : ℕ) :
    K.prefixCount K.carrier n = n := by
  classical
  have hmem : ∀ i, K.enumeration i ∈ K.carrier := by
    intro i
    rw [← K.range_enumeration]
    exact ⟨i, rfl⟩
  simp [prefixCount, hmem]

@[simp] theorem prefixCount_inter_carrier
    (K : OrderedLanguage) (A : Language) (n : ℕ) :
    K.prefixCount (A ∩ K.carrier) n = K.prefixCount A n := by
  classical
  unfold prefixCount
  congr 1
  ext i
  have hcarrier : K.enumeration i ∈ K.carrier := by
    rw [← K.range_enumeration]
    exact ⟨i, rfl⟩
  simp [hcarrier]

/-- The finite relative-density ratio in the first `n` positions.

The value at `n = 0` is set to zero; the asymptotic densities are unchanged
by this convention.
-/
noncomputable def prefixRatio
    (K : OrderedLanguage) (A : Language) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (K.prefixCount A n : ℝ) / n

@[simp] theorem prefixRatio_zero (K : OrderedLanguage) (A : Language) :
    K.prefixRatio A 0 = 0 := by
  simp [prefixRatio]

theorem prefixRatio_nonneg (K : OrderedLanguage) (A : Language) (n : ℕ) :
    0 ≤ K.prefixRatio A n := by
  by_cases hn : n = 0
  · simp [prefixRatio, hn]
  · simp only [prefixRatio, hn, if_false]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem prefixRatio_le_one (K : OrderedLanguage) (A : Language) (n : ℕ) :
    K.prefixRatio A n ≤ 1 := by
  by_cases hn : n = 0
  · simp [prefixRatio, hn]
  · simp only [prefixRatio, hn, if_false]
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    rw [div_le_one hnpos]
    exact_mod_cast K.prefixCount_le A n

theorem prefixRatio_mono
    (K : OrderedLanguage) {A B : Language} (hAB : A ⊆ B) (n : ℕ) :
    K.prefixRatio A n ≤ K.prefixRatio B n := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [prefixRatio, hn, if_false]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast K.prefixCount_mono hAB n)
      (Nat.cast_nonneg n)

/-- Definition 4.1: upper density of `A` in the ordered language `K`. -/
noncomputable def upperDensity (K : OrderedLanguage) (A : Language) : ℝ :=
  limsup (K.prefixRatio A) atTop

/-- Definition 4.1: lower density of `A` in the ordered language `K`. -/
noncomputable def lowerDensity (K : OrderedLanguage) (A : Language) : ℝ :=
  liminf (K.prefixRatio A) atTop

@[simp] theorem prefixRatio_empty (K : OrderedLanguage) (n : ℕ) :
    K.prefixRatio (∅ : Language) n = 0 := by
  simp [prefixRatio]

@[simp] theorem prefixRatio_carrier (K : OrderedLanguage) (n : ℕ) :
    K.prefixRatio K.carrier n = if n = 0 then 0 else 1 := by
  by_cases hn : n = 0
  · simp [prefixRatio, hn]
  · simp [prefixRatio, hn]

theorem upperDensity_nonneg (K : OrderedLanguage) (A : Language) :
    0 ≤ K.upperDensity A := by
  unfold upperDensity
  apply le_limsup_of_frequently_le
  · exact Frequently.of_forall (fun n => K.prefixRatio_nonneg A n)
  · exact isBoundedUnder_of ⟨1, fun n => K.prefixRatio_le_one A n⟩

theorem upperDensity_le_one (K : OrderedLanguage) (A : Language) :
    K.upperDensity A ≤ 1 := by
  unfold upperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop
      (fun n => K.prefixRatio_nonneg A n)
  · exact Eventually.of_forall (fun n => K.prefixRatio_le_one A n)

theorem lowerDensity_nonneg (K : OrderedLanguage) (A : Language) :
    0 ≤ K.lowerDensity A := by
  unfold lowerDensity
  apply le_liminf_of_le
  · exact isCoboundedUnder_ge_of_le atTop
      (fun n => K.prefixRatio_le_one A n)
  · exact Eventually.of_forall (fun n => K.prefixRatio_nonneg A n)

theorem lowerDensity_le_one (K : OrderedLanguage) (A : Language) :
    K.lowerDensity A ≤ 1 := by
  unfold lowerDensity
  apply liminf_le_of_frequently_le
  · exact (Eventually.of_forall
      (fun n => K.prefixRatio_le_one A n)).frequently
  · exact isBoundedUnder_of
      ⟨0, fun n => K.prefixRatio_nonneg A n⟩

theorem lowerDensity_mono
    (K : OrderedLanguage) {A B : Language} (hAB : A ⊆ B) :
    K.lowerDensity A ≤ K.lowerDensity B := by
  unfold lowerDensity
  apply liminf_le_liminf
  · exact Eventually.of_forall (K.prefixRatio_mono hAB)
  · exact isBoundedUnder_of
      ⟨0, fun n => K.prefixRatio_nonneg A n⟩
  · exact isCoboundedUnder_ge_of_le atTop
      (fun n => K.prefixRatio_le_one B n)

theorem upperDensity_mono
    (K : OrderedLanguage) {A B : Language} (hAB : A ⊆ B) :
    K.upperDensity A ≤ K.upperDensity B := by
  unfold upperDensity
  apply limsup_le_limsup
  · exact Eventually.of_forall (K.prefixRatio_mono hAB)
  · exact isCoboundedUnder_le_of_le atTop
      (fun n => K.prefixRatio_nonneg A n)
  · exact isBoundedUnder_of
      ⟨1, fun n => K.prefixRatio_le_one B n⟩

@[simp] theorem upperDensity_carrier (K : OrderedLanguage) :
    K.upperDensity K.carrier = 1 := by
  have htendsto : Tendsto (K.prefixRatio K.carrier) atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [prefixRatio_carrier, hn]
  exact htendsto.limsup_eq

@[simp] theorem lowerDensity_carrier (K : OrderedLanguage) :
    K.lowerDensity K.carrier = 1 := by
  have htendsto : Tendsto (K.prefixRatio K.carrier) atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [prefixRatio_carrier, hn]
  exact htendsto.liminf_eq

@[simp] theorem lowerDensity_inter_carrier
    (K : OrderedLanguage) (A : Language) :
    K.lowerDensity (A ∩ K.carrier) = K.lowerDensity A := by
  unfold lowerDensity prefixRatio
  congr 2
  funext n
  rw [K.prefixCount_inter_carrier]

/-- Shared analytic transfer for ordered lower density.

If, up to an asymptotically vanishing error, every source prefix ratio is at
most `q` times the corresponding output ratio, then the output lower density
is at least the source lower density divided by `q`. Paper-specific files
should prove their finite counting inequality and instantiate this theorem,
rather than duplicating the `liminf` argument. -/
theorem lowerDensity_div_le_of_eventually_prefixRatio_le
    (K : OrderedLanguage) (source output : Language)
    (q : ℝ) (hq : 0 < q) (error : ℕ → ℝ)
    (herror : Tendsto error atTop (nhds 0))
    (hprefix : ∀ᶠ n : ℕ in atTop,
      K.prefixRatio source n ≤ q * K.prefixRatio output n + error n) :
    K.lowerDensity source / q ≤ K.lowerDensity output := by
  unfold lowerDensity
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop
      (fun n => K.prefixRatio_le_one output n))
    (isBoundedUnder_of
      ⟨0, fun n => K.prefixRatio_nonneg output n⟩)).2
  intro y hy
  have hscaled :
      q * y < liminf (K.prefixRatio source) atTop := by
    have h := (lt_div_iff₀ hq).mp hy
    simpa [mul_comm] using h
  obtain ⟨r, hyr, hrDensity⟩ := exists_between hscaled
  have hrEventually :
      ∀ᶠ n : ℕ in atTop, r < K.prefixRatio source n :=
    eventually_lt_of_lt_liminf hrDensity
      (isBoundedUnder_of
        ⟨0, fun n => K.prefixRatio_nonneg source n⟩)
  have herrorEventually :
      ∀ᶠ n : ℕ in atTop, error n < r - q * y := by
    have hpositive : 0 < r - q * y := by linarith
    exact herror.eventually (Iio_mem_nhds hpositive)
  filter_upwards [hrEventually, herrorEventually, hprefix] with
      n hr hsmall hcount
  nlinarith

/-! ## Finite perturbations of the measured set -/

/-- A finite exceptional set can contribute at most its cardinality to any
ordered prefix count. -/
theorem prefixCount_le_ncard_of_finite
    (K : OrderedLanguage) {F : Language} (hF : F.Finite) (n : ℕ) :
    K.prefixCount F n ≤ hF.toFinset.card := by
  classical
  unfold prefixCount
  have hcardImage :
      (((Finset.range n).filter fun i => K.enumeration i ∈ F).image
          K.enumeration).card =
        ((Finset.range n).filter fun i => K.enumeration i ∈ F).card := by
    exact Finset.card_image_of_injective _ K.enumeration_injective
  rw [← hcardImage]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_image, Finset.mem_filter] at hx
  obtain ⟨i, ⟨_hiRange, hiF⟩, rfl⟩ := hx
  exact Set.Finite.mem_toFinset hF |>.2 hiF

/-- Every finite measured set has ordered lower density zero. -/
theorem lowerDensity_eq_zero_of_finite
    (K : OrderedLanguage) {F : Language} (hF : F.Finite) :
    K.lowerDensity F = 0 := by
  let B := hF.toFinset.card
  have hbound :
      ∀ n, K.prefixRatio F n ≤ (B : ℝ) / n := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [prefixRatio, hn, if_false]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast K.prefixCount_le_ncard_of_finite hF n
      · positivity
  have htendsto :
      Tendsto (K.prefixRatio F) atTop (nhds 0) := by
    apply squeeze_zero
      (fun n => K.prefixRatio_nonneg F n) hbound
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  exact htendsto.liminf_eq

/-- Prefix counts change by at most the finite asymmetric difference in the
first argument. -/
theorem prefixCount_le_add_ncard_diff
    (K : OrderedLanguage) {A B : Language}
    (hfinite : (A \ B).Finite) (n : ℕ) :
    K.prefixCount A n ≤ K.prefixCount B n + hfinite.toFinset.card := by
  classical
  let aIndices :=
    (Finset.range n).filter fun i => K.enumeration i ∈ A
  let bIndices :=
    (Finset.range n).filter fun i => K.enumeration i ∈ B
  let diffIndices :=
    (Finset.range n).filter fun i => K.enumeration i ∈ A \ B
  have hsub : aIndices ⊆ bIndices ∪ diffIndices := by
    intro i hi
    simp only [aIndices, bIndices, diffIndices, Finset.mem_filter,
      Finset.mem_union] at hi ⊢
    by_cases hiB : K.enumeration i ∈ B
    · exact Or.inl ⟨hi.1, hiB⟩
    · exact Or.inr ⟨hi.1, hi.2, hiB⟩
  have hcard : aIndices.card ≤ bIndices.card + diffIndices.card := by
    exact (Finset.card_le_card hsub).trans
      (Finset.card_union_le bIndices diffIndices)
  have hdiff : diffIndices.card ≤ hfinite.toFinset.card := by
    simpa [diffIndices, prefixCount] using
      K.prefixCount_le_ncard_of_finite hfinite n
  simpa [aIndices, bIndices, diffIndices, prefixCount] using
    hcard.trans (Nat.add_le_add_left hdiff _)

/-- Ratio form of `prefixCount_le_add_ncard_diff`.  The finite error is
displayed explicitly because it vanishes along `atTop`. -/
theorem prefixRatio_le_add_finiteError
    (K : OrderedLanguage) {A B : Language}
    (hfinite : (A \ B).Finite) (n : ℕ) :
    K.prefixRatio A n ≤
      K.prefixRatio B n + (hfinite.toFinset.card : ℝ) / n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnnonneg : (0 : ℝ) ≤ n := by positivity
    have hcount :
        (K.prefixCount A n : ℝ) ≤
          K.prefixCount B n + hfinite.toFinset.card := by
      exact_mod_cast K.prefixCount_le_add_ncard_diff hfinite n
    simp only [prefixRatio, hn, if_false]
    rw [← add_div]
    exact div_le_div_of_nonneg_right hcount hnnonneg

/-- Removing finitely many points from the measured set does not change its
ordered lower density.  The target ordering `K` is fixed; no claim is made
about changing the reference language or its ordering. -/
theorem lowerDensity_diff_finite
    (K : OrderedLanguage) (A : Language) {F : Language}
    (hF : F.Finite) :
    K.lowerDensity (A \ F) = K.lowerDensity A := by
  apply le_antisymm
  · exact K.lowerDensity_mono Set.diff_subset
  · have hfinite : (A \ (A \ F)).Finite := by
      apply hF.subset
      intro x hx
      by_contra hxF
      exact hx.2 ⟨hx.1, hxF⟩
    have herror :
        Tendsto (fun n : ℕ => (hfinite.toFinset.card : ℝ) / (n : ℝ))
          atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hle :=
      K.lowerDensity_div_le_of_eventually_prefixRatio_le
        A (A \ F) 1 (by norm_num)
        (fun n : ℕ => (hfinite.toFinset.card : ℝ) / (n : ℝ))
        herror
        (Eventually.of_forall fun n => by
          simpa using K.prefixRatio_le_add_finiteError hfinite n)
    simpa using hle

/-- Finite symmetric perturbations of the measured set preserve ordered
lower density.  As above, the reference ordering `K` itself is unchanged. -/
theorem lowerDensity_eq_of_finite_symmetricDifference
    (K : OrderedLanguage) {A B : Language}
    (hAB : (A \ B).Finite) (hBA : (B \ A).Finite) :
    K.lowerDensity A = K.lowerDensity B := by
  calc
    K.lowerDensity A = K.lowerDensity (A \ (A \ B)) :=
      (K.lowerDensity_diff_finite A hAB).symm
    _ = K.lowerDensity (B \ (B \ A)) := by
      congr 1
      ext x
      simp only [Set.mem_diff]
      tauto
    _ = K.lowerDensity B :=
      K.lowerDensity_diff_finite B hBA

/-! ## Upper density and finite perturbations -/

/-- Ordered prefix ratios are subadditive under union. -/
theorem prefixRatio_union_le
    (K : OrderedLanguage) (A B : Language) (n : ℕ) :
    K.prefixRatio (A ∪ B) n ≤
      K.prefixRatio A n + K.prefixRatio B n := by
  classical
  by_cases hn : n = 0
  · simp [hn]
  · simp only [prefixRatio, hn, if_false]
    rw [← add_div]
    apply div_le_div_of_nonneg_right
    · unfold prefixCount
      rw [← Nat.cast_add]
      norm_cast
      apply (Finset.card_le_card ?_).trans
        (Finset.card_union_le
          ((Finset.range n).filter fun i => K.enumeration i ∈ A)
          ((Finset.range n).filter fun i => K.enumeration i ∈ B))
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range,
        Finset.mem_union, Set.mem_union] at hi ⊢
      rcases hi.2 with hiA | hiB
      · exact Or.inl ⟨hi.1, hiA⟩
      · exact Or.inr ⟨hi.1, hiB⟩
    · exact Nat.cast_nonneg n

/-- Ordered upper density is subadditive under union. -/
theorem upperDensity_union_le
    (K : OrderedLanguage) (A B : Language) :
    K.upperDensity (A ∪ B) ≤
      K.upperDensity A + K.upperDensity B := by
  unfold upperDensity
  have hpoint :
      limsup (K.prefixRatio (A ∪ B)) atTop ≤
        limsup (fun n => K.prefixRatio A n + K.prefixRatio B n) atTop := by
    apply limsup_le_limsup
    · exact Eventually.of_forall (K.prefixRatio_union_le A B)
    · exact isCoboundedUnder_le_of_le atTop
        (fun n => K.prefixRatio_nonneg (A ∪ B) n)
    · exact isBoundedUnder_of
        ⟨2, fun n => by
          linarith [K.prefixRatio_le_one A n,
            K.prefixRatio_le_one B n]⟩
  apply hpoint.trans
  apply limsup_add_le
  · exact isBoundedUnder_of
      ⟨0, fun n => K.prefixRatio_nonneg A n⟩
  · exact isBoundedUnder_of
      ⟨1, fun n => K.prefixRatio_le_one A n⟩
  · exact isCoboundedUnder_le_of_le atTop
      (fun n => K.prefixRatio_nonneg B n)
  · exact isBoundedUnder_of
      ⟨1, fun n => K.prefixRatio_le_one B n⟩

/-- Every finite measured set has ordered upper density zero. -/
theorem upperDensity_eq_zero_of_finite
    (K : OrderedLanguage) {F : Language} (hF : F.Finite) :
    K.upperDensity F = 0 := by
  let B := hF.toFinset.card
  have hbound :
      ∀ n, K.prefixRatio F n ≤ (B : ℝ) / n := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [prefixRatio, hn, if_false]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast K.prefixCount_le_ncard_of_finite hF n
      · positivity
  have htendsto :
      Tendsto (K.prefixRatio F) atTop (nhds 0) := by
    apply squeeze_zero
      (fun n => K.prefixRatio_nonneg F n) hbound
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  exact htendsto.limsup_eq

/-- Removing finitely many measured points does not change ordered upper
density. -/
theorem upperDensity_diff_finite
    (K : OrderedLanguage) (A : Language) {F : Language}
    (hF : F.Finite) :
    K.upperDensity (A \ F) = K.upperDensity A := by
  apply le_antisymm
  · exact K.upperDensity_mono Set.diff_subset
  · have hsubset : A ⊆ (A \ F) ∪ F := by
      intro x hx
      by_cases hxF : x ∈ F
      · exact Or.inr hxF
      · exact Or.inl ⟨hx, hxF⟩
    calc
      K.upperDensity A ≤ K.upperDensity ((A \ F) ∪ F) :=
        K.upperDensity_mono hsubset
      _ ≤ K.upperDensity (A \ F) + K.upperDensity F :=
        K.upperDensity_union_le _ _
      _ = K.upperDensity (A \ F) := by
        rw [K.upperDensity_eq_zero_of_finite hF, add_zero]

/-- Finite symmetric perturbations preserve ordered upper density. -/
theorem upperDensity_eq_of_finite_symmetricDifference
    (K : OrderedLanguage) {A B : Language}
    (hAB : (A \ B).Finite) (hBA : (B \ A).Finite) :
    K.upperDensity A = K.upperDensity B := by
  calc
    K.upperDensity A = K.upperDensity (A \ (A \ B)) :=
      (K.upperDensity_diff_finite A hAB).symm
    _ = K.upperDensity (B \ (B \ A)) := by
      congr 1
      ext x
      simp only [Set.mem_diff]
      tauto
    _ = K.upperDensity B :=
      K.upperDensity_diff_finite B hBA

/-! ## Complements inside the reference language -/

/-- Every reference-prefix position lies either in `A` or in its complement
inside the reference carrier. -/
theorem prefixCount_diff_add
    (K : OrderedLanguage) (A : Language) (n : ℕ) :
    K.prefixCount (K.carrier \ A) n + K.prefixCount A n = n := by
  classical
  have hcarrier : ∀ i, K.enumeration i ∈ K.carrier := by
    intro i
    rw [← K.range_enumeration]
    exact ⟨i, rfl⟩
  unfold prefixCount
  simpa [hcarrier, Nat.add_comm] using
    (Finset.card_filter_add_card_filter_not
      (s := Finset.range n) (p := fun i => K.enumeration i ∈ A))

/-- At every nonempty prefix, the relative ratios of a set and its carrier
complement sum to one. -/
theorem prefixRatio_diff
    (K : OrderedLanguage) (A : Language) {n : ℕ} (hn : n ≠ 0) :
    K.prefixRatio (K.carrier \ A) n = 1 - K.prefixRatio A n := by
  simp only [prefixRatio, hn, if_false]
  have hsumNat := K.prefixCount_diff_add A n
  have hsumReal :
      (K.prefixCount (K.carrier \ A) n : ℝ) +
          (K.prefixCount A n : ℝ) = (n : ℝ) := by
    exact_mod_cast hsumNat
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  linarith

/-- Ordered lower density of a carrier complement is one minus the ordered
upper density.  This is the shared analytic identity behind recall-complement
bounds such as Paper 32 Lemma 4.7. -/
theorem lowerDensity_diff
    (K : OrderedLanguage) (A : Language) :
    K.lowerDensity (K.carrier \ A) = 1 - K.upperDensity A := by
  have heq :
      (fun n => K.prefixRatio (K.carrier \ A) n) =ᶠ[atTop]
        (fun n => 1 - K.prefixRatio A n) := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact K.prefixRatio_diff A hn
  unfold lowerDensity upperDensity
  calc
    liminf (fun n => K.prefixRatio (K.carrier \ A) n) atTop =
        liminf (fun n => 1 - K.prefixRatio A n) atTop := by
      unfold liminf
      rw [Filter.map_congr heq]
    _ = 1 - limsup (K.prefixRatio A) atTop := by
      apply liminf_const_sub
      · exact isBoundedUnder_of
          ⟨1, fun n => K.prefixRatio_le_one A n⟩
      · exact isCoboundedUnder_le_of_le atTop
          (fun n => K.prefixRatio_nonneg A n)

end OrderedLanguage
end KleinbergWei
end GenLimit

end

-- GenLimit.Core.NaturalDensity
section
set_option autoImplicit true

/-!
# Ordered density in the natural ordering

Every infinite language has a canonical increasing enumeration. Its ordered
lower density agrees with the ratio of counts in ambient natural-number
prefixes. This lets clients use the shared ordered-density definition while
proving estimates in ambient prefixes.
-/

namespace GenLimit.KleinbergWei.OrderedLanguage

open Filter
open scoped Classical

/-- An infinite language, enumerated in increasing numerical order. -/
noncomputable def increasing (K : Language) (hK : K.Infinite) : OrderedLanguage where
  carrier := K
  enumeration := Nat.nth (· ∈ K)
  enumeration_injective := Nat.nth_injective hK
  range_enumeration := Nat.range_nth_of_infinite hK

/-- The canonical enumeration respects the usual order on natural numbers. -/
theorem increasing_strictMono (K : Language) (hK : K.Infinite) :
    StrictMono (increasing K hK).enumeration :=
  Nat.nth_strictMono hK

/-- Counting the first `|K ∩ [0,n)|` target elements is the same as counting
inside the ambient prefix `[0,n)`. -/
theorem increasing_prefixCount (K : Language) (hK : K.Infinite)
    (A : Language) (n : ℕ) :
    (increasing K hK).prefixCount A (Nat.count (· ∈ K) n) =
      Nat.count (· ∈ A ∩ K) n := by
  unfold prefixCount
  rw [Nat.count_eq_card_filter_range (p := (· ∈ A ∩ K))]
  apply Finset.card_bij (fun i _ => Nat.nth (· ∈ K) i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact ⟨Nat.nth_lt_of_lt_count hi.1, hi.2, Nat.nth_mem_of_infinite hK i⟩
  · intro i _ j _ hij
    exact Nat.nth_injective hK hij
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_inter_iff] at hx
    refine ⟨Nat.count (· ∈ K) x, ?_, Nat.nth_count hx.2.2⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.count_strict_mono hx.2.2 hx.1), ?_⟩
    simpa only [increasing,Nat.nth_count hx.2.2] using hx.2.1

/-- Ambient target counts visit every rank and tend to infinity, so replacing
the prefix index by that count preserves the `atTop` filter. -/
theorem map_count_atTop (K : Language) (hK : K.Infinite) :
    map (Nat.count (· ∈ K)) atTop = atTop := by
  classical
  apply map_atTop_eq_of_gc (Nat.nth (· ∈ K)) 0 (Nat.count_monotone _)
  · intro a c _
    exact Nat.count_le_iff_le_nth (p := (· ∈ K)) hK
  · intro c _
    exact (Nat.count_nth_of_infinite (p := (· ∈ K)) hK c).ge

/-- Ordered lower density in the increasing target ordering is the ambient
prefix ratio. Intersecting with `K` makes this valid for every measured set. -/
theorem increasing_lowerDensity_eq_liminf (K : Language) (hK : K.Infinite)
    (A : Language) :
    (increasing K hK).lowerDensity A =
      liminf (fun n : ℕ =>
        (Nat.count (· ∈ A ∩ K) n : ℝ) / (Nat.count (· ∈ K) n : ℝ)) atTop := by
  have hratio : ∀ n,
      (increasing K hK).prefixRatio A (Nat.count (· ∈ K) n) =
        (Nat.count (· ∈ A ∩ K) n : ℝ) / (Nat.count (· ∈ K) n : ℝ) := by
    intro n
    by_cases hn : Nat.count (· ∈ K) n = 0
    · simp [hn]
    · simp only [prefixRatio, hn, if_false, increasing_prefixCount]
  calc
    (increasing K hK).lowerDensity A =
        liminf ((increasing K hK).prefixRatio A ∘ Nat.count (· ∈ K)) atTop := by
      rw [liminf_comp, map_count_atTop K hK]
      rfl
    _ = _ := congrArg (fun f : ℕ → ℝ => liminf f atTop) (funext hratio)

end GenLimit.KleinbergWei.OrderedLanguage

end

-- GenLimit.Support.Asymptotics.NatLog
section
set_option autoImplicit true

/-!
# Natural logarithm asymptotics

Shared asymptotic facts for the discrete base-two logarithm.  These estimates
are used by both P30's sparse catch-up construction and P39's charging
argument.
-/

open Filter
open scoped Topology

namespace GenLimit

/-- The discrete base-two logarithm is negligible compared with `n`. -/
theorem tendsto_natLog2_div :
    Tendsto (fun n : ℕ => (Nat.log2 n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hlogb :
      Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [id_eq] using
      (Real.isLittleO_logb_id_atTop (b := (2 : ℝ))).natCast_atTop.tendsto_div_nhds_zero
  exact squeeze_zero
    (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun n => div_le_div_of_nonneg_right (Real.log2_le_logb n) (Nat.cast_nonneg _))
    hlogb

end GenLimit

end

-- GenLimit.Support.Asymptotics.Liminf
section
set_option autoImplicit true

/-!
# Liminf transfer under vanishing additive error

A paper-independent endgame for asymptotic performance comparisons.  If a
bounded sequence is eventually at most another bounded-above sequence plus
an error tending to zero, then its liminf is at most the other's liminf.
-/

namespace GenLimit

open Filter

theorem liminf_le_liminf_of_eventually_le_add_tendsto_zero
    {u v error : ℕ → ℝ}
    (huNonneg : ∀ n, 0 ≤ u n) (huOne : ∀ n, u n ≤ 1)
    (hvOne : ∀ n, v n ≤ 1)
    (hcompare : ∀ᶠ n in atTop, u n ≤ v n + error n)
    (herror : Tendsto error atTop (nhds 0)) :
    liminf u atTop ≤ liminf v atTop := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have herrorSmall : ∀ᶠ n in atTop, error n ≤ ε :=
    ((tendsto_order.1 herror).2 ε hε).mono fun _ h => h.le
  have hshift : ∀ᶠ n in atTop, u n - ε ≤ v n := by
    filter_upwards [hcompare, herrorSmall] with n hcomp herr
    linarith
  have hlim :
      liminf (fun n => u n - ε) atTop ≤ liminf v atTop := by
    exact liminf_le_liminf hshift
      (isBoundedUnder_of ⟨-ε, fun n => by linarith [huNonneg n]⟩)
      (isCoboundedUnder_ge_of_le atTop hvOne)
  rw [liminf_sub_const atTop u ε
    (isCoboundedUnder_ge_of_le atTop huOne)
    (isBoundedUnder_of ⟨0, huNonneg⟩)] at hlim
  linarith

/-- A generic counting-to-lower-density transfer.  If `N` tends to infinity,
`D ≤ N`, and eventually `N ≤ qD + error` with `error / N → 0`, then the
lower limit of `D / N` is at least `1/q`. -/
theorem lowerDensity_inv_of_eventual_counting_atTop
    (N D error : ℕ → ℕ) (q : ℕ) (hq : 0 < q)
    (hN : Tendsto N atTop atTop)
    (hD : ∀ n, D n ≤ N n)
    (herror : Tendsto
      (fun n : ℕ => (error n : ℝ) / (N n : ℝ)) atTop (nhds 0))
    (hcount : ∀ᶠ n : ℕ in atTop, N n ≤ q * D n + error n) :
    (1 / (q : ℝ)) ≤
      liminf (fun n : ℕ => (D n : ℝ) / (N n : ℝ)) atTop := by
  let lower : ℕ → ℝ := fun n =>
    (1 / (q : ℝ)) - (error n : ℝ) / ((q : ℝ) * (N n : ℝ))
  have hscaled :
      Tendsto
        (fun n : ℕ => (error n : ℝ) / ((q : ℝ) * (N n : ℝ)))
        atTop (nhds 0) := by
    have hdiv := herror.div_const (q : ℝ)
    simpa [div_div, mul_comm] using hdiv
  have hlower : Tendsto lower atTop (nhds (1 / (q : ℝ))) := by
    simpa only [lower, sub_zero] using tendsto_const_nhds.sub hscaled
  have hNpos : ∀ᶠ n : ℕ in atTop, 0 < N n :=
    hN.eventually (eventually_gt_atTop 0)
  have hcompare : ∀ᶠ n : ℕ in atTop,
      lower n ≤ (D n : ℝ) / (N n : ℝ) := by
    filter_upwards [hNpos, hcount] with n hn hcountn
    have hnR : (0 : ℝ) < N n := by exact_mod_cast hn
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hcountR :
        (N n : ℝ) ≤ (q : ℝ) * (D n : ℝ) + (error n : ℝ) := by
      exact_mod_cast hcountn
    dsimp only [lower]
    rw [le_div_iff₀ hnR]
    field_simp [hqR.ne', hnR.ne']
    nlinarith
  have hratio_le_one :
      ∀ n, (D n : ℝ) / (N n : ℝ) ≤ 1 := by
    intro n
    by_cases hn : N n = 0
    · simp [hn]
    · have hnR : (0 : ℝ) < N n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_le_one hnR]
      exact_mod_cast hD n
  calc
    (1 / (q : ℝ)) = liminf lower atTop := hlower.liminf_eq.symm
    _ ≤ liminf (fun n : ℕ => (D n : ℝ) / (N n : ℝ)) atTop :=
      liminf_le_liminf hcompare hlower.isBoundedUnder_ge
        (isCoboundedUnder_ge_of_le atTop hratio_le_one)

end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Abstract.Density
section
set_option autoImplicit true

/-!
# The asymptotic counting argument for lower density

This module isolates the final analytic calculation in the proof of Theorem 3.15.
After the order-preserving reduction of the target language to `ℕ`, let `D n`
and `A n` count the first `n` target elements first announced by the generator
and adversary.  If these counts partition each prefix, and the charging
argument bounds `A n` by `D n + r + log₂ n`, then the generator has lower
density at least `1/2`.
-/

open Filter
open scoped Topology

namespace GenLimit

/-- A fixed constant plus `log₂ n` is negligible compared with `n`. -/
theorem tendsto_countingError_div (r : ℕ) :
    Tendsto (fun n : ℕ => ((r + Nat.log2 n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ => (r : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [Nat.cast_add, add_div, zero_add] using hr.add tendsto_natLog2_div

/-- The lower comparison sequence used in Theorem 3.15 tends to `1/2`. -/
theorem tendsto_half_sub_countingError (r : ℕ) :
    Tendsto
      (fun n : ℕ => (1 / 2 : ℝ) - ((r + Nat.log2 n : ℕ) : ℝ) / (2 * (n : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have h := (tendsto_countingError_div r).div_const (2 : ℝ)
  simpa [div_div, mul_comm] using tendsto_const_nhds.sub h

/-- The asymptotic counting core of Theorem 3.15.

`D n` and `A n` are the numbers among the first `n` target elements first
announced by the generator and adversary, respectively. The first assumption
says these two classes partition every prefix. The second is the charging
bound obtained from Fact 3.13 and Lemma 3.14.
-/
theorem lowerDensity_half_of_counting
    (D A : ℕ → ℕ) (r : ℕ)
    (hpartition : ∀ n, D n + A n = n)
    (hcharge : ∀ n, A n ≤ D n + r + Nat.log2 n) :
    (1 / 2 : ℝ) ≤ liminf (fun n : ℕ => (D n : ℝ) / (n : ℝ)) atTop := by
  have hD_le_n : ∀ n, D n ≤ n := fun n => by
    calc
      D n ≤ D n + A n := Nat.le_add_right _ _
      _ = n := hpartition n
  have hcount : ∀ᶠ n : ℕ in atTop,
      n ≤ 2 * D n + (r + Nat.log2 n) :=
    Filter.Eventually.of_forall fun n => by
      calc
        n = D n + A n := (hpartition n).symm
        _ ≤ D n + (D n + r + Nat.log2 n) :=
          Nat.add_le_add_left (hcharge n) _
        _ = 2 * D n + (r + Nat.log2 n) := by omega
  have h := GenLimit.lowerDensity_inv_of_eventual_counting_atTop
    id D (fun n => r + Nat.log2 n) 2 (by omega) tendsto_id
    hD_le_n (tendsto_countingError_div r) hcount
  simpa using h

end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity
section
set_option autoImplicit true

/-!
# Lower density in an arbitrary infinite target

The density definition is a wrapper around Core's ordered lower density,
using the increasing enumeration of the target. The equality with the
ambient-prefix formula lets the counting proofs keep their original prefixes.
For an infinite target `K`, its prefix count tends to infinity, so the
normalized error estimate still gives the same lower-density bound.
-/

open Filter
open scoped Topology

namespace GenLimit
namespace PatientScope

/-- Core's ordered lower density, specialized to the increasing enumeration
of the infinite target. -/
noncomputable def relativeLowerDensity (A K : Language) (hK : K.Infinite) : ℝ :=
  (KleinbergWei.OrderedLanguage.increasing K hK).lowerDensity A

/-- The Core specialization agrees with the paper's ambient-prefix formula
when the measured language is contained in the target. -/
theorem relativeLowerDensity_eq_liminf (A K : Language) (hK : K.Infinite)
    (hsub : A ⊆ K) :
    relativeLowerDensity A K hK =
      liminf (fun n : ℕ => (prefixCount A n : ℝ) / (prefixCount K n : ℝ))
        atTop := by
  classical
  simpa only [relativeLowerDensity, Set.inter_eq_left.mpr hsub,
    Nat.count_eq_card_filter_range, prefixCount, prefixFinset] using
    KleinbergWei.OrderedLanguage.increasing_lowerDensity_eq_liminf K hK A

/-- Prefix cardinality is the sum of the target's natural-valued indicator. -/
theorem prefixCount_eq_sum_indicator (K : Set ℕ) (n : ℕ) :
    prefixCount K n =
      ∑ k ∈ Finset.range n, K.indicator (fun _ => (1 : ℕ)) k := by
  classical
  change ((Finset.range n).filter fun x => x ∈ K).card = _
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ K <;> simp [Set.indicator, hx]

/-- Prefix counts are monotone under set inclusion. -/
theorem prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    prefixCount A n ≤ prefixCount B n := by
  classical
  unfold prefixCount
  apply Finset.card_le_card
  intro x hx
  have hx' := mem_prefixFinset.mp hx
  exact mem_prefixFinset.mpr ⟨hx'.1, hAB hx'.2⟩

/-- The number of elements of an infinite target in ambient prefixes tends
to infinity. -/
theorem tendsto_prefixCount_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (prefixCount K) atTop atTop := by
  have hsum :
      Tendsto
        (fun n : ℕ =>
          ∑ k ∈ Finset.range n, K.indicator (fun _ => (1 : ℕ)) k)
        atTop atTop :=
    (Set.infinite_iff_tendsto_sum_indicator_atTop
      (R := ℕ) (r := (1 : ℕ)) (by omega)).1 hK
  exact hsum.congr' <| Filter.Eventually.of_forall fun n =>
    (prefixCount_eq_sum_indicator K n).symm

/-- A counting theorem with an arbitrary denominator `N` which tends to
infinity.  This is the ambient-prefix analogue of
`lowerDensity_half_of_counting`. -/
theorem lowerDensity_half_of_counting_atTop
    (N D A : ℕ → ℕ) (r : ℕ)
    (hN : Tendsto N atTop atTop)
    (hpartition : ∀ n, D n + A n = N n)
    (hcharge : ∀ n, A n ≤ D n + r + Nat.log2 (N n)) :
    (1 / 2 : ℝ) ≤
      liminf (fun n : ℕ => (D n : ℝ) / (N n : ℝ)) atTop := by
  have hD_le_N : ∀ n, D n ≤ N n := fun n => by
    calc
      D n ≤ D n + A n := Nat.le_add_right _ _
      _ = N n := hpartition n
  have herror : Tendsto
      (fun n : ℕ => ((r + Nat.log2 (N n) : ℕ) : ℝ) / (N n : ℝ))
      atTop (𝓝 0) := by
    have hcomp := (tendsto_countingError_div r).comp hN
    simpa only [Function.comp_def] using hcomp
  have hcount : ∀ᶠ n : ℕ in atTop,
      N n ≤ 2 * D n + (r + Nat.log2 (N n)) :=
    Filter.Eventually.of_forall fun n => by
      calc
        N n = D n + A n := (hpartition n).symm
        _ ≤ D n + (D n + r + Nat.log2 (N n)) :=
          Nat.add_le_add_left (hcharge n) _
        _ = 2 * D n + (r + Nat.log2 (N n)) := by omega
  have h := GenLimit.lowerDensity_inv_of_eventual_counting_atTop
    N D (fun n => r + Nat.log2 (N n)) 2 (by omega) hN hD_le_N
    herror hcount
  simpa using h

/-- Exact arbitrary-target form of the lower-density calculation. -/
theorem lowerDensity_half_of_target_counting
    (K : Set ℕ) (hK : K.Infinite) (D A : ℕ → ℕ) (r : ℕ)
    (hpartition : ∀ n, D n + A n = prefixCount K n)
    (hcharge : ∀ n,
      A n ≤ D n + r + Nat.log2 (prefixCount K n)) :
    (1 / 2 : ℝ) ≤
      liminf
        (fun n : ℕ => (D n : ℝ) / (prefixCount K n : ℝ))
        atTop := by
  exact lowerDensity_half_of_counting_atTop
    (prefixCount K) D A r (tendsto_prefixCount_atTop hK)
    hpartition hcharge

end PatientScope
end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Abstract.TargetMain
section
set_option autoImplicit true

/-!
# Theorem 3.15 for an arbitrary infinite target

This is the abstract assembly of the paper's lower-density theorem without
normalizing the target to `Set.univ`.  The denominator is the number of target
elements in the ambient prefix, exactly as in the paper's definition.
-/

namespace GenLimit
namespace PatientScope
namespace PatientScopeCertificate

/-- The paper's lower density of defender-first target elements, measured in
ambient natural-number prefixes.  The finitely many prefixes with denominator
zero do not affect the limit inferior for an infinite target. -/
noncomputable def targetLowerDensity (P : PatientScopeCertificate)
    (hInfinite : P.target.Infinite) : ℝ :=
  relativeLowerDensity (P.defender ∩ P.target) P.target hInfinite

/-- Theorem 3.15 in its exact arbitrary-target form, assembled from the
ownership partition, Fact 3.13's partner injection, Lemma 3.14's target-aware
charging certificate, and the ambient-prefix asymptotic theorem. -/
theorem theorem_3_15_target
    (P : PatientScopeCertificate)
    (hInfinite : P.target.Infinite)
    (Q : TargetSwitchChargingCertificate P.target P.switchLoss) :
    (1 / 2 : ℝ) ≤ P.targetLowerDensity hInfinite := by
  have hpartition : ∀ n,
      P.defenderCount n + P.attackerCount n = prefixCount P.target n := by
    intro n
    calc
      P.defenderCount n + P.attackerCount n =
          P.attackerCount n + P.defenderCount n := Nat.add_comm _ _
      _ = P.targetCount n := (P.targetCount_eq n).symm
      _ = prefixCount P.target n := rfl
  have hlog : ∀ n,
      prefixCount P.switchLoss n ≤ Nat.log2 (P.targetCount n) := by
    intro n
    simpa only [targetCount] using Q.prefixCount_le_log2_targetCount n
  have hcharge : ∀ n,
      P.attackerCount n ≤
        P.defenderCount n + P.earlyAttacker.card +
          Nat.log2 (prefixCount P.target n) := by
    intro n
    simpa only [targetCount] using P.attackerCount_le_log2 hlog n
  have h := lowerDensity_half_of_target_counting
    P.target hInfinite P.defenderCount P.attackerCount
    P.earlyAttacker.card hpartition hcharge
  rw [targetLowerDensity,
    relativeLowerDensity_eq_liminf _ _ hInfinite Set.inter_subset_right]
  exact h

end PatientScopeCertificate
end PatientScope
end GenLimit

end

-- GenLimit.Paper39_DenseGeneration.Patient.Main
section
set_option autoImplicit true

/-!
# Operational patient-scope lower-density theorem

This module states Theorem 3.15 directly for the semantic patient-scope
machine.  Its numerator is the ambient-prefix count of values first announced
by the generator which belong to the presented target.
-/

namespace GenLimit
namespace PatientMachine

/-- Lower density achieved by the concrete patient-scope output on target
`O.language z`. -/
noncomputable def patientLowerDensity
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ) : ℝ :=
  PatientScope.relativeLowerDensity
    (GeneratorFirst stream (output O stream) ∩ O.language z)
    (O.language z) (O.infinite' z)

/-- The abstract certificate's target lower density is definitionally the
operational quantity above. -/
private theorem patientScopeCertificate_targetLowerDensity
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    (Q : PatientScope.TargetSwitchChargingCertificate
      (O.language z) (settledSwitchLoss O stream z hP)) :
    (patientScopeCertificate O stream z hP Q).targetLowerDensity (O.infinite' z) =
      patientLowerDensity O stream z := by
  rfl

/-- Operational form of Theorem 3.15.  It is uniform over the indexed family,
the target index, and every exact presentation of that target. -/
theorem patientScope_lowerDensity_half
    (O : OracleFamily) (stream : ℕ → ℕ) {z : ℕ}
    (hP : Presents stream (O.language z)) :
    (1 / 2 : ℝ) ≤ patientLowerDensity O stream z := by
  let Q := settledChargingCertificate O stream z hP
  let P := patientScopeCertificate O stream z hP Q
  have hInfinite : P.target.Infinite := by
    simpa [P] using O.infinite' z
  have hcharging :
      PatientScope.TargetSwitchChargingCertificate P.target P.switchLoss := by
    simpa [P] using Q
  have hhalf :=
    PatientScope.PatientScopeCertificate.theorem_3_15_target
      P hInfinite hcharging
  simpa [P, patientScopeCertificate_targetLowerDensity] using hhalf

/-- Definition 2.1 novelty together with Theorem 3.15 for the same run. -/
theorem patientScope_generation_and_lowerDensity
    (O : OracleFamily) (stream : ℕ → ℕ) {z : ℕ}
    (hP : Presents stream (O.language z)) :
    (∃ T, ∀ t, T ≤ t →
      output O stream t ∈ O.language z ∧
      (∀ s, s ≤ t → stream s ≠ output O stream t) ∧
      (∀ s, s < t → output O stream s ≠ output O stream t)) ∧
      (1 / 2 : ℝ) ≤ patientLowerDensity O stream z := by
  obtain ⟨T, hvalid⟩ := patient_validity O stream hP
  refine ⟨⟨T, ?_⟩, patientScope_lowerDensity_half O stream hP⟩
  intro t ht
  exact ⟨hvalid t ht, stream_ne_output O stream t,
    fun s hs => output_ne_of_lt O stream hs⟩

end PatientMachine
end GenLimit

end

-- MissionReplay
section
set_option autoImplicit true

namespace DenseLanguageGeneration.PatientScope
open ActiveLanguageGeneration.Hierarchy
open GenLimit.PatientMachine
open scoped Classical
noncomputable section

theorem history_succ (a : ℕ → ℕ+) (t : ℕ) :
    history a (t+1) = history a t ++ [a t] := by simp [history, List.range_succ]

theorem state_succ (L : Family) (a : ℕ → ℕ+) (t : ℕ) :
    stateAt L a (t+1) = step L (stateAt L a t) (a t) := by
  simp [stateAt,replay,history_succ,List.foldl_append]

theorem inputs_eq (L : Family) (a : ℕ → ℕ+) (t : ℕ) :
    (stateAt L a t).inputs = history a t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [state_succ,history_succ]; change _ ++ [_] = _; rw [ih]

theorem outputs_eq (L : Family) (a : ℕ → ℕ+) (t : ℕ) :
    (stateAt L a t).outputs = (List.range t).map (outputAt (generator L) a) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [state_succ,List.range_succ,List.map_append]
    change (stateAt L a t).outputs ++ [_] = _ ++ [_]
    apply congrArg₂ List.append ih
    congr 1
    change _ = (stateAt L a (t+1)).lastOutput
    rw [state_succ]
    rfl

theorem focus_from_critical (L : Family) (a : ℕ → ℕ) {t s f : ℕ}
    (hf : GenLimit.IsFocus (oracle L).language a t s f) :
    focusIndex L (history (encode ∘ a) t) s = some f := by
  classical
  have hex : (GenLimit.PatientMachine.criticalIndices (oracle L).language a t s).Nonempty :=
    ⟨f,GenLimit.PatientMachine.mem_criticalIndices.mpr ⟨hf.1,hf.2.1⟩⟩
  unfold focusIndex
  simp only [indices_transport, dif_pos hex, Option.some.injEq]
  apply le_antisymm
  · have hm := GenLimit.PatientMachine.mem_criticalIndices.mp (Finset.max'_mem _ hex)
    exact hf.2.2 _ hm.1 hm.2
  · exact Finset.le_max' _ _ (GenLimit.PatientMachine.mem_criticalIndices.mpr ⟨hf.1,hf.2.1⟩)

theorem leastFresh_available (F : Set ℕ+) (h b : List ℕ+)
    (hx : ∃ n, positive n ∈ F ∧ positive n ∉ h ∧ positive n ∉ b) :
    let y := leastFresh F h b
    y ∈ F ∧ y ∉ h ∧ y ∉ b ∧
      ∀ n, positive n ∈ F → positive n ∉ h → positive n ∉ b → y ≤ positive n := by
  classical
  simp only [leastFresh, dif_pos hx]
  obtain ⟨hF,hh,hb⟩ := Nat.find_spec hx
  refine ⟨hF,hh,hb,?_⟩
  intro n hn h₁ h₂
  have hle := Nat.find_min' hx ⟨hn,h₁,h₂⟩
  change Nat.find hx + 1 ≤ n+1
  omega

set_option linter.unusedVariables false in
/-- The previous round's least-fresh output rule proves the non-switch comparison
directly in the mission's finite-history model, before any stabilization. -/
theorem non_switch_announcements (L : Family) (i : ℕ) (a : ℕ → ℕ+)
    (ha : IsEnumeration (L i) a) (t : ℕ)
    (hnew : UnannouncedInput (generator L) a (t+1)) (hns : ¬SwitchLoss L a (t+1)) :
    a (t+1) ∈ focusAt L a (t+1) ∧ outputAt (generator L) a t ≤ a (t+1) ∧
    (∀ (hb : outputAt (generator L) a t ∈ (L i).val) (hx : a (t+1) ∈ (L i).val),
      rank (L i) ⟨outputAt (generator L) a t,hb⟩ ≤ rank (L i) ⟨a (t+1),hx⟩) := by
  classical
  have hf : a (t+1) ∈ focusAt L a (t+1) := Classical.not_not.mp hns
  have hxI : a (t+1) ∉ history a (t+1) := by
    intro h
    obtain ⟨s,hs,e⟩ := List.mem_map.mp h
    exact hnew.1 s (List.mem_range.mp hs) e
  have hxO : a (t+1) ∉ (stateAt L a t).outputs := by
    rw [outputs_eq]
    intro h
    obtain ⟨s,hs,e⟩ := List.mem_map.mp h
    exact hnew.2 s (by have := List.mem_range.mp hs; omega) e
  let F := focusAt L a (t+1)
  let h := history a (t+1)
  let b := (stateAt L a t).outputs
  have hx : positive (a (t+1)).natPred = a (t+1) := PNat.succPNat_natPred _
  have he : ∃ n, positive n ∈ F ∧ positive n ∉ h ∧ positive n ∉ b := by
    exact ⟨(a (t+1)).natPred, by rwa [hx], by rwa [hx], by rwa [hx]⟩
  have hy : outputAt (generator L) a t = leastFresh F h b := by
    change (stateAt L a (t+1)).lastOutput = _
    dsimp [F,h,b,focusAt]
    rw [state_succ]
    simp only [step, inputs_eq, ← history_succ]
  have hle : outputAt (generator L) a t ≤ a (t+1) := by
    rw [hy]
    have hm := (leastFresh_available F h b he).2.2.2 (a (t+1)).natPred
      (by rwa [hx]) (by rwa [hx]) (by rwa [hx])
    rwa [hx] at hm
  refine ⟨hf,hle,fun _ _ => ?_⟩
  unfold rank prefixCount
  apply Finset.card_le_card
  intro x hmem
  obtain ⟨hp,hL⟩ := Finset.mem_filter.mp hmem
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr
    ((Finset.mem_range.mp hk).trans_le hle), rfl⟩, hL⟩

end
end DenseLanguageGeneration.PatientScope

end

-- MissionBridge
section
set_option autoImplicit true

namespace DenseLanguageGeneration.PatientScope
open ActiveLanguageGeneration.Hierarchy
open GenLimit.PatientMachine
open scoped Classical
noncomputable section

variable (L : Family) (a : ℕ → ℕ)
local notation "O" => oracle L
local notation "b" => (encode ∘ a)

private theorem backtrack_scope_eq (t : ℕ) (u : GenLimit.PatientMachine.State)
    (ex : ∃ i, GenLimit.Consistent (oracle L).language a (t+1) i) :
    backtrackScope L (history b t) (history b (t+1)) u.scope =
      (backtrackDecision (oracle L).language a t u).scope := by
  classical
  have cs : (Finset.range u.scope).filter (Consistent L (history b (t+1))) =
      consistentIndices (oracle L).language a (t+1) u.scope := by
    ext i
    simp [consistent_transport]
  have surv : criticalIndices L (history b t) u.scope ∩ criticalIndices L (history b (t+1)) u.scope =
      survivingCriticalIndices (oracle L).language a t u.scope := by
    ext i
    simp only [indices_transport, Finset.mem_inter, mem_criticalIndices, mem_survivingCriticalIndices]
    tauto
  have ex' : ∃ i, Consistent L (history b (t+1)) i := by simpa [consistent_transport] using ex
  unfold backtrackScope
  simp only [cs,surv]
  by_cases hc : (consistentIndices (oracle L).language a (t+1) u.scope).Nonempty
  · by_cases hs : (survivingCriticalIndices (oracle L).language a t u.scope).Nonempty
    · simp [hc,hs,backtrackDecision,highestSurvivor,GenLimit.Support.greatestCandidateWithFallback]
    · simp [hc,hs,backtrackDecision,lowestConsistentInScope,GenLimit.Support.leastCandidateWithFallback]
  · rw [dif_neg hc,dif_pos ex',backtrackDecision_of_empty_scope hc ex]
    simp only [lowestConsistent,dif_pos ex]
    congr 1
    exact Nat.find_congr' (consistent_transport L a (t+1) _)

private def control (s v age : ℕ) (old : Option ℕ) (oldh h : List ℕ+) : ℕ × ℕ :=
  if ∃ i, old = some i ∧ Consistent L h i then
    if 2^v ≤ age then
      (s+1, if focusIndex L h (s+1) = old then v else v+1)
    else (s,v)
  else (backtrackScope L oldh h s,v+1)

private theorem step_eq (st : State) (x : ℕ+) :
    let h := st.inputs ++ [x]
    let old := focusIndex L st.inputs st.scope
    let c := control L st.scope st.tau st.age old st.inputs h
    let y := leastFresh (focusSet L h c.1) h st.outputs
    step L st x = ⟨h,st.outputs ++ [y],c.1,c.2,
      if focusIndex L h c.1 = old then st.age+1 else 1,y⟩ := rfl

private theorem control_eq {z : ℕ} (hp : GenLimit.Presents a ((oracle L).language z)) (t : ℕ) :
    let u := run O a t
    let d := GenLimit.PatientMachine.decide (oracle L).language a t u
    control L u.scope u.tau u.age (focusIndex L (history b t) u.scope)
      (history b t) (history b (t+1)) = (d.scope,d.tau) := by
  classical
  let u := run O a t
  have hf := run_focus_isFocus O hp t
  have old := focus_from_critical L a hf
  change focusIndex L (history b t) u.scope = some u.focus at old
  have ex := (onModel_of_presents O hp) (t+1)
  change control L u.scope u.tau u.age _ _ _ = _
  rw [control,old]
  simp only [Option.some.injEq,exists_eq_left',consistent_transport]
  by_cases hc : GenLimit.Consistent (oracle L).language a (t+1) u.focus
  · by_cases hw : 2^u.tau ≤ u.age
    · have hd := decide_isFocus hf ex
      have new := focus_from_critical L a hd
      change focusIndex L (history b (t+1)) (GenLimit.PatientMachine.decide _ _ _ u).scope =
        some (GenLimit.PatientMachine.decide _ _ _ u).focus at new
      simp [GenLimit.PatientMachine.decide, hc, stableDecision,hw] at new
      change _ = ((GenLimit.PatientMachine.decide _ _ _ u).scope,(GenLimit.PatientMachine.decide _ _ _ u).tau)
      simp [GenLimit.PatientMachine.decide,hc,stableDecision,hw,new]
    · change _ = ((GenLimit.PatientMachine.decide _ _ _ u).scope,(GenLimit.PatientMachine.decide _ _ _ u).tau)
      simp [GenLimit.PatientMachine.decide,hc,stableDecision,hw]
  · have hback := backtrack_scope_eq L a t u ex
    have htau : (backtrackDecision (oracle L).language a t u).tau = u.tau+1 := by
      by_cases hcs : (consistentIndices (oracle L).language a (t+1) u.scope).Nonempty <;>
        simp [backtrackDecision,hcs,ex]
    change _ = ((GenLimit.PatientMachine.decide _ _ _ u).scope,(GenLimit.PatientMachine.decide _ _ _ u).tau)
    rw [if_neg hc]
    simp only [GenLimit.PatientMachine.decide,if_neg hc,hback,htau]

theorem decode_presents {z : ℕ} {c : ℕ → ℕ+} (hp : IsEnumeration (L z) c) :
    GenLimit.Presents (Equiv.pnatEquivNat ∘ c) ((oracle L).language z) := by
  ext x
  constructor
  · rintro ⟨n,rfl⟩
    have hx : c n ∈ (L z).val := by rw [← hp.2]; exact ⟨n,rfl⟩
    change Equiv.pnatEquivNat.symm (Equiv.pnatEquivNat (c n)) ∈ (L z).val
    simpa using hx
  · intro hx
    change encode x ∈ (L z).val at hx
    rw [← hp.2] at hx
    obtain ⟨n,hn⟩ := hx
    refine ⟨n,?_⟩
    change Equiv.pnatEquivNat (c n) = x
    rw [hn]
    exact Equiv.pnatEquivNat.apply_symm_apply _

private theorem history_sample (t x : ℕ) :
    encode x ∈ history b t ↔ x ∈ GenLimit.sample a t := by
  rw [GenLimit.mem_sample_iff]
  simp only [history,List.mem_map,List.mem_range,Function.comp_apply]
  exact exists_congr fun i => and_congr_right fun _ => Equiv.pnatEquivNat.symm.injective.eq_iff

private theorem fresh_eq (t f : ℕ) (outs : List ℕ+) (used : Finset ℕ)
    (hused : ∀ x, encode x ∈ outs ↔ x ∈ used) :
    leastFresh (L f).val (history b (t+1)) outs =
      encode (leastAvailable (oracle L).language (oracle L).infinite' a (t+1) used f) := by
  have eq (x : ℕ) : (positive x ∈ (L f).val ∧ positive x ∉ history b (t+1) ∧ positive x ∉ outs) ↔
      Available (oracle L).language a (t+1) used f x := by
    change (encode x ∈ _ ∧ encode x ∉ _ ∧ encode x ∉ outs) ↔ _
    simp only [Available,history_sample,hused]
    rfl
  have e := available_exists (oracle L).language (oracle L).infinite' a (t+1) used f
  have e' : ∃ n, positive n ∈ (L f).val ∧ positive n ∉ history b (t+1) ∧ positive n ∉ outs := by
    obtain ⟨x,hx⟩ := e
    exact ⟨x,(eq x).mpr hx⟩
  simp only [leastFresh,dif_pos e',leastAvailable]
  apply congrArg encode
  exact Nat.find_congr' (eq _)

structure Agrees (t : ℕ) : Prop where
  scope : (stateAt L b t).scope = (run O a t).scope
  tau : (stateAt L b t).tau = (run O a t).tau
  age : (stateAt L b t).age = (run O a t).age
  used : ∀ x, encode x ∈ (stateAt L b t).outputs ↔ x ∈ (run O a t).used

private theorem advance {z : ℕ} (hp : GenLimit.Presents a ((oracle L).language z)) (t : ℕ) (ih : Agrees L a t) :
    Agrees L a (t+1) ∧ outputAt (generator L) b t = encode (output O a t) := by
  let u := run O a t
  let d := GenLimit.PatientMachine.decide (oracle L).language a t u
  let st := stateAt L b t
  have old := focus_from_critical L a (run_focus_isFocus O hp t)
  have new := focus_from_critical L a (run_focus_isFocus O hp (t+1))
  change focusIndex L (history b (t+1)) d.scope = some d.focus at new
  have ctl := control_eq L a hp t
  have ctl' : control L st.scope st.tau st.age (focusIndex L st.inputs st.scope)
      st.inputs (st.inputs ++ [b t]) = (d.scope,d.tau) := by
    simp only [st,inputs_eq,←history_succ,ih.scope, ih.tau, ih.age]
    exact ctl
  have fv : focusSet L (history b (t+1)) d.scope = (L d.focus).val := by
    simp [focusSet,new]
  have out := fresh_eq L a t d.focus st.outputs u.used ih.used
  have oh : leastFresh (focusSet L (st.inputs ++ [b t]) d.scope) (st.inputs ++ [b t]) st.outputs =
      encode (output O a t) := by
    simpa only [st,inputs_eq,←history_succ,fv,output_eq_leastAvailable,d,u] using
      (show leastFresh (focusSet L (history b (t+1)) d.scope) (history b (t+1)) st.outputs =
      encode (output O a t) by rw [fv,output_eq_leastAvailable]; exact out)
  have sc : step L st (b t) = ⟨st.inputs ++ [b t], st.outputs ++ [encode (output O a t)],
      d.scope, d.tau, (if d.focus = u.focus then u.age+1 else 1), encode (output O a t)⟩ := by
    rw [step_eq,ctl',oh]
    have hOld : focusIndex L st.inputs st.scope = some u.focus := by
      simpa only [st,inputs_eq,ih.scope] using old
    have hNew : focusIndex L (st.inputs ++ [b t]) d.scope = some d.focus := by
      simpa only [st,inputs_eq,←history_succ] using new
    rw [hOld,hNew,ih.age]
    simp only [Option.some.injEq]
    rfl
  have next : stateAt L b (t+1) = step L st (b t) := state_succ L b t
  constructor
  · constructor
    · rw [next,sc]; rfl
    · rw [next,sc]; rfl
    · rw [next,sc]; rfl
    · intro x
      rw [next,sc]
      simp only [List.mem_append,List.mem_singleton,run_succ,processRound_used,Finset.mem_insert,← output_eq_leastAvailable]
      exact (or_congr (ih.used x) Equiv.pnatEquivNat.symm.injective.eq_iff).trans or_comm
  · change (stateAt L b (t+1)).lastOutput = _
    rw [next,sc]

theorem replay_agrees {z : ℕ} (hp : GenLimit.Presents a ((oracle L).language z)) (t : ℕ) : Agrees L a t := by
  induction t with
  | zero => exact ⟨rfl,rfl,rfl,fun _ => by simp [stateAt,history,replay,initial,initialState]⟩
  | succ t ih => exact (advance L a hp t ih).1

theorem replay_output {z : ℕ} (hp : GenLimit.Presents a ((oracle L).language z)) (t : ℕ) :
    outputAt (generator L) b t = encode (output O a t) :=
  (advance L a hp t (replay_agrees L a hp t)).2

end
end DenseLanguageGeneration.PatientScope

end

-- GenLimit.Paper07_DensityMeasuresForLanguageGeneration.StrictCritical
section
set_option autoImplicit true

/-!
# #07 Density Measures: strict criticality

Definition 3.1, Claim 3.2, and Lemma 3.3 of Kleinberg--Wei,
*Density Measures for Language Generation* (arXiv:2504.14370v1).

The displayed Definition 3.1 includes the current language and would require
it to be a proper subset of itself. Following the sentence immediately after
the display, the definition below compares only with earlier indices.
-/

namespace GenLimit.KleinbergWei.DensityMeasures

/-- Corrected Definition 3.1: candidate n is consistent and is a proper
subset of every earlier consistent candidate. -/
def StrictCritical
    (C : LanguageFamily) (stream : ℕ → ℕ) (t n : ℕ) : Prop :=
  Consistent C stream t n ∧
    ∀ i, i < n → Consistent C stream t i → C n ⊂ C i

/-- Strictly critical languages form a proper descending chain. -/
theorem strictCritical_ssubset_of_lt
    {C : LanguageFamily} {stream : ℕ → ℕ} {t i j : ℕ}
    (hij : i < j)
    (hi : StrictCritical C stream t i)
    (hj : StrictCritical C stream t j) :
    C j ⊂ C i :=
  hj.2 i hij hi.1

/-- The least consistent candidate is strictly critical. -/
theorem least_consistent_strictCritical
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ}
    (hn : Consistent C stream t n)
    (hleast : ∀ i, i < n → ¬Consistent C stream t i) :
    StrictCritical C stream t n := by
  refine ⟨hn, ?_⟩
  intro i hin hicon
  exact False.elim ((hleast i hin) hicon)

/-- Claim 3.2: strict criticality persists while the language remains
consistent. The source proof's bound i < r is corrected to i < n. -/
theorem claim_3_2
    {C : LanguageFamily} {stream : ℕ → ℕ} {t r n : ℕ}
    (htr : t ≤ r)
    (hn : StrictCritical C stream t n)
    (hconsistent : Consistent C stream r n) :
    StrictCritical C stream r n := by
  refine ⟨hconsistent, ?_⟩
  intro i hin hi
  apply hn.2 i hin
  intro u hu
  exact hi (sample_mono htr hu)

/-- The target index is its first occurrence in the indexed family. -/
def FirstOccurrence (C : LanguageFamily) (z : ℕ) : Prop :=
  ∀ i, i < z → C i ≠ C z

/-- Lemma 3.3: the first occurrence of an exactly presented target is
strictly critical from some finite time onward. -/
theorem lemma_3_3
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    ∃ T, ∀ t, T ≤ t → StrictCritical C stream t z := by
  obtain ⟨T, hT⟩ :=
    finite_scope_eventually_consistent_iff_presented_subset
      (C := C) (stream := stream) (E := C z) hP z
  refine ⟨T, ?_⟩
  intro t ht
  refine ⟨presents_consistent hP, ?_⟩
  intro i hiz hi
  have hsub : C z ⊆ C i := (hT t ht i hiz).mp hi
  exact Set.ssubset_iff_subset_ne.mpr
    ⟨hsub, fun heq => hfirst i hiz heq.symm⟩

end GenLimit.KleinbergWei.DensityMeasures

end

-- GenLimit.Paper07_DensityMeasuresForLanguageGeneration.Accurate
section
set_option autoImplicit true

/-!
# #07 Density Measures: the accurate selector

The semantic, noncomputable Section 3 construction. Paper round t+1 uses
strict criticality at stage t and the newly revealed value at position t.
-/

namespace GenLimit.KleinbergWei.DensityMeasures

/-- Strictly critical indices in the visible scope n ≤ t. -/
noncomputable def scopedStrictCriticalIndices
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (t + 1)).filter (StrictCritical C stream t)

@[simp] theorem mem_scopedStrictCriticalIndices
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ} :
    n ∈ scopedStrictCriticalIndices C stream t ↔
      n ≤ t ∧ StrictCritical C stream t n := by
  classical
  simp [scopedStrictCriticalIndices, Nat.lt_succ_iff]

/-- The last visible strictly critical index, with default zero. -/
noncomputable def scopedFocus
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ := by
  classical
  let S := scopedStrictCriticalIndices C stream t
  exact GenLimit.Support.greatestCandidateWithFallback S 0

theorem scopedFocus_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {t z : ℕ}
    (hzt : z ≤ t)
    (hz : StrictCritical C stream t z) :
    scopedFocus C stream t ≤ t ∧
      StrictCritical C stream t (scopedFocus C stream t) ∧
      z ≤ scopedFocus C stream t := by
  classical
  let S := scopedStrictCriticalIndices C stream t
  have hzS : z ∈ S := by
    simpa [S] using mem_scopedStrictCriticalIndices.mpr ⟨hzt, hz⟩
  have hne : S.Nonempty := ⟨z, hzS⟩
  have hmaxS : GenLimit.Support.greatestCandidateWithFallback S 0 ∈ S :=
    GenLimit.Support.greatestCandidateWithFallback_mem hne
  have hparts :
      GenLimit.Support.greatestCandidateWithFallback S 0 ≤ t ∧
        StrictCritical C stream t
          (GenLimit.Support.greatestCandidateWithFallback S 0) := by
    simpa [S] using mem_scopedStrictCriticalIndices.mp hmaxS
  simpa [scopedFocus, S] using
    (show GenLimit.Support.greatestCandidateWithFallback S 0 ≤ t ∧
        StrictCritical C stream t
          (GenLimit.Support.greatestCandidateWithFallback S 0) ∧
        z ≤ GenLimit.Support.greatestCandidateWithFallback S 0 from
      ⟨hparts.1, hparts.2,
        GenLimit.Support.le_greatestCandidateWithFallback hzS⟩)

/-- A strict-critical language falsified by the new observation. -/
def BadStrictCritical
    (C : LanguageFamily) (stream : ℕ → ℕ) (t w n : ℕ) : Prop :=
  StrictCritical C stream t n ∧ w ∉ C n

/-- The first falsified strict-critical index, with an irrelevant default. -/
noncomputable def firstBadStrictCritical
    (C : LanguageFamily) (stream : ℕ → ℕ) (t w : ℕ) : ℕ := by
  classical
  exact if hbad : ∃ n, BadStrictCritical C stream t w n then
    Nat.find hbad
  else 0

theorem firstBadStrictCritical_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {t w : ℕ}
    (hbad : ∃ n, BadStrictCritical C stream t w n) :
    BadStrictCritical C stream t w (firstBadStrictCritical C stream t w) := by
  classical
  simp only [firstBadStrictCritical, dif_pos hbad]
  exact Nat.find_spec hbad

theorem firstBadStrictCritical_min
    {C : LanguageFamily} {stream : ℕ → ℕ} {t w n : ℕ}
    (hbad : ∃ n, BadStrictCritical C stream t w n)
    (hn : BadStrictCritical C stream t w n) :
    firstBadStrictCritical C stream t w ≤ n := by
  classical
  simp only [firstBadStrictCritical, dif_pos hbad]
  exact Nat.find_min' hbad hn

/-- Strict-critical indices before the first falsified one that contain the
new observation. -/
noncomputable def boundaryCandidates
    (C : LanguageFamily) (stream : ℕ → ℕ) (t w : ℕ) : Finset ℕ := by
  classical
  let b := firstBadStrictCritical C stream t w
  exact (Finset.range b).filter fun n =>
    StrictCritical C stream t n ∧ w ∈ C n

@[simp] theorem mem_boundaryCandidates
    {C : LanguageFamily} {stream : ℕ → ℕ} {t w n : ℕ} :
    n ∈ boundaryCandidates C stream t w ↔
      n < firstBadStrictCritical C stream t w ∧
        StrictCritical C stream t n ∧ w ∈ C n := by
  classical
  simp [boundaryCandidates]

/-- The two cases of the paper's selector at previous stage t. -/
noncomputable def selectIndex
    (C : LanguageFamily) (stream : ℕ → ℕ) (t w : ℕ) : ℕ := by
  classical
  if hall : ∀ n, StrictCritical C stream t n → w ∈ C n then
    exact scopedFocus C stream t
  else
    have hbad : ∃ n, BadStrictCritical C stream t w n := by
      simpa [BadStrictCritical] using hall
    let S := boundaryCandidates C stream t w
    exact if hS : S.Nonempty then S.max' hS
      else scopedFocus C stream t

/-- In the stable-target regime, the selected language is strictly critical,
no earlier than the target, and contained in the target. -/
theorem selectIndex_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {t w z : ℕ}
    (hzt : z ≤ t)
    (hz : StrictCritical C stream t z)
    (hw : w ∈ C z) :
    StrictCritical C stream t (selectIndex C stream t w) ∧
      z ≤ selectIndex C stream t w ∧
      C (selectIndex C stream t w) ⊆ C z := by
  classical
  by_cases hall : ∀ n, StrictCritical C stream t n → w ∈ C n
  · have hf := scopedFocus_spec hzt hz
    have hsel : selectIndex C stream t w = scopedFocus C stream t := by
      rw [selectIndex]
      simp only [dif_pos hall]
    rw [hsel]
    refine ⟨hf.2.1, hf.2.2, ?_⟩
    rcases eq_or_lt_of_le hf.2.2 with heq | hlt
    · simp [heq]
    · exact (strictCritical_ssubset_of_lt hlt hz hf.2.1).le
  · have hbad : ∃ n, BadStrictCritical C stream t w n := by
      simpa [BadStrictCritical] using hall
    let b := firstBadStrictCritical C stream t w
    have hb := firstBadStrictCritical_spec hbad
    have hzb : z < b := by
      have hle : z ≤ b := by
        by_contra hnot
        have hbz : b < z := Nat.lt_of_not_ge hnot
        have hsub : C z ⊆ C b :=
          (strictCritical_ssubset_of_lt hbz hb.1 hz).le
        exact hb.2 (hsub hw)
      exact lt_of_le_of_ne hle (fun heq => hb.2 (by simpa [heq] using hw))
    let S := boundaryCandidates C stream t w
    have hzS : z ∈ S := by
      simpa [S, b] using mem_boundaryCandidates.mpr ⟨hzb, hz, hw⟩
    have hne : S.Nonempty := ⟨z, hzS⟩
    have hsel : selectIndex C stream t w = S.max' hne := by
      rw [selectIndex]
      simp only [dif_neg hall]
      simp [S, hne]
    have hmS : S.max' hne ∈ S := Finset.max'_mem S hne
    have hmParts :
        StrictCritical C stream t (S.max' hne) ∧ w ∈ C (S.max' hne) := by
      exact (mem_boundaryCandidates.mp (by simpa [S] using hmS)).2
    have hzm : z ≤ S.max' hne := Finset.le_max' S z hzS
    rw [hsel]
    refine ⟨hmParts.1, hzm, ?_⟩
    rcases eq_or_lt_of_le hzm with heq | hlt
    · simp [heq]
    · exact (strictCritical_ssubset_of_lt hlt hz hmParts.1).le

/-- Round t+1 uses stage t and the new value stream t. -/
noncomputable def guessIndex
    (C : LanguageFamily) (stream : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => selectIndex C stream t (stream t)

/-- Eventual index validity of the guessed languages. -/
def IndexValidInLimit
    (C : LanguageFamily) (stream : ℕ → ℕ) (z : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t → C (guessIndex C stream t) ⊆ C z

/-- Proposition 3.4: the selector is eventually index-valid. -/
theorem proposition_3_4
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    IndexValidInLimit C stream z := by
  obtain ⟨T, hT⟩ := lemma_3_3 hP hfirst
  refine ⟨max (T + 1) (z + 1), ?_⟩
  intro r hr
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have htT : T ≤ t := by omega
  have hzt : z ≤ t := by omega
  have hz := hT t htT
  have hw : stream t ∈ C z := by
    rw [← hP]
    exact ⟨t, rfl⟩
  exact (selectIndex_spec hzt hz hw).2.2

end GenLimit.KleinbergWei.DensityMeasures

end

-- GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfinitelyOften
section
set_option autoImplicit true

/-!
# #07 Density Measures: accuracy infinitely often

Proposition 3.5 and Theorem 3.1 (Overview Theorem 2.1). The proof formalizes
the paper's changepoint argument for the least strict-critical index after the
target.
-/

namespace GenLimit.KleinbergWei.DensityMeasures

/-- The least strictly critical index after z, with an irrelevant default. -/
noncomputable def nextStrictCritical
    (C : LanguageFamily) (stream : ℕ → ℕ) (t z : ℕ) : ℕ := by
  classical
  exact if h : ∃ n, z < n ∧ StrictCritical C stream t n then
    Nat.find h
  else 0

theorem nextStrictCritical_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {t z : ℕ}
    (h : ∃ n, z < n ∧ StrictCritical C stream t n) :
    z < nextStrictCritical C stream t z ∧
      StrictCritical C stream t (nextStrictCritical C stream t z) := by
  classical
  simp only [nextStrictCritical, dif_pos h]
  exact Nat.find_spec h

theorem nextStrictCritical_min
    {C : LanguageFamily} {stream : ℕ → ℕ} {t z n : ℕ}
    (h : ∃ n, z < n ∧ StrictCritical C stream t n)
    (hn : z < n ∧ StrictCritical C stream t n) :
    nextStrictCritical C stream t z ≤ n := by
  classical
  simp only [nextStrictCritical, dif_pos h]
  exact Nat.find_min' h hn

/-- A natural-number sequence that is eventually nonincreasing eventually
stabilizes. -/
theorem eventually_constant_of_succ_le
    (a : ℕ → ℕ) (N : ℕ)
    (hstep : ∀ s, N ≤ s → a (s + 1) ≤ a s) :
    ∃ S, N ≤ S ∧ ∀ r, S ≤ r → a r = a S := by
  classical
  have hanti : AntitoneOn a (Set.Ici N) :=
    antitoneOn_nat_Ici_of_succ_le hstep
  have hreach : ∃ v, ∃ s, N ≤ s ∧ a s = v :=
    ⟨a N, N, le_rfl, rfl⟩
  let v := Nat.find hreach
  obtain ⟨S, hNS, haS⟩ := Nat.find_spec hreach
  refine ⟨S, hNS, ?_⟩
  intro r hSr
  have hNr : N ≤ r := le_trans hNS hSr
  have har_le : a r ≤ a S := hanti hNS hNr hSr
  have hv_le : v ≤ a r :=
    Nat.find_min' hreach ⟨r, hNr, rfl⟩
  have haS_le : a S ≤ a r := haS.trans_le hv_le
  exact le_antisymm har_le haS_le

theorem exists_increase_of_not_eventually_constant
    (a : ℕ → ℕ) (N : ℕ)
    (hnot : ¬∃ S, N ≤ S ∧ ∀ r, S ≤ r → a r = a S) :
    ∃ s, N ≤ s ∧ a s < a (s + 1) := by
  by_contra hinc
  have hstep : ∀ s, N ≤ s → a (s + 1) ≤ a s := by
    intro s hs
    have hnlt : ¬a s < a (s + 1) := by
      intro hlt
      exact hinc ⟨s, hs, hlt⟩
    omega
  exact hnot (eventually_constant_of_succ_le a N hstep)

/-- Accuracy means equality of guessed and target languages, not necessarily
equality of their family indices. -/
def AccurateAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (z r : ℕ) : Prop :=
  C (guessIndex C stream r) = C z

/-- Proposition 3.5: after every round there is a later accurate round. -/
theorem proposition_3_5
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    ∀ t, ∃ r, t ≤ r ∧ AccurateAt C stream z r := by
  obtain ⟨T, hT⟩ := lemma_3_3 hP hfirst
  intro t₀
  by_contra hfuture
  push_neg at hfuture
  let N := max T (max z t₀)
  have hTN : T ≤ N := le_trans (Nat.le_max_left _ _) le_rfl
  have hzN : z ≤ N :=
    le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have htN : t₀ ≤ N :=
    le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hExists :
      ∀ s, N ≤ s → ∃ n, z < n ∧ StrictCritical C stream s n := by
    intro s hs
    have hsT : T ≤ s := le_trans hTN hs
    have hzs : z ≤ s := le_trans hzN hs
    have hzcrit := hT s hsT
    have hw : stream s ∈ C z := by
      rw [← hP]
      exact ⟨s, rfl⟩
    let n := selectIndex C stream s (stream s)
    have hn := selectIndex_spec hzs hzcrit hw
    have hn_ne : n ≠ z := by
      intro hnz
      have hacc : AccurateAt C stream z (s + 1) := by
        simp [AccurateAt, guessIndex, n, hnz]
      exact hfuture (s + 1) (le_trans htN (by omega)) hacc
    exact ⟨n, lt_of_le_of_ne hn.2.1 hn_ne.symm, hn.1⟩
  let a : ℕ → ℕ := fun s => nextStrictCritical C stream s z
  have hnotconst :
      ¬∃ S, N ≤ S ∧ ∀ r, S ≤ r → a r = a S := by
    rintro ⟨S, hNS, hconst⟩
    have hES := hExists S hNS
    have haS := nextStrictCritical_spec hES
    have hzS : StrictCritical C stream S z :=
      hT S (le_trans hTN hNS)
    have hproper : C (a S) ⊂ C z :=
      strictCritical_ssubset_of_lt haS.1 hzS haS.2
    obtain ⟨u, huz, hua⟩ := Set.exists_of_ssubset hproper
    obtain ⟨U, hU⟩ := eventually_mem_sample_of_presents hP huz
    let r := max S U
    have hSr : S ≤ r := Nat.le_max_left _ _
    have hNr : N ≤ r := le_trans hNS hSr
    have hEr := hExists r hNr
    have har := nextStrictCritical_spec hEr
    have hEq : a r = a S := hconst r hSr
    have huSample : u ∈ sample stream r :=
      hU r (Nat.le_max_right _ _)
    have huAr : u ∈ C (a r) := har.2.1 huSample
    exact hua (by simpa [hEq] using huAr)
  obtain ⟨s, hNs, hincrease⟩ :=
    exists_increase_of_not_eventually_constant a N hnotconst
  have hEs := hExists s hNs
  have hEs1 := hExists (s + 1) (by omega)
  have ha := nextStrictCritical_spec hEs
  have hzcrit : StrictCritical C stream s z :=
    hT s (le_trans hTN hNs)
  have hwz : stream s ∈ C z := by
    rw [← hP]
    exact ⟨s, rfl⟩
  have ha_not_next : ¬StrictCritical C stream (s + 1) (a s) := by
    intro haNext
    have hmin := nextStrictCritical_min hEs1 ⟨ha.1, haNext⟩
    exact not_lt_of_ge hmin hincrease
  have ha_inconsistent : ¬Consistent C stream (s + 1) (a s) := by
    intro hcon
    exact ha_not_next (claim_3_2 (by omega) ha.2 hcon)
  have hwa : stream s ∉ C (a s) := by
    intro hmem
    apply ha_inconsistent
    intro u hu
    have hu' : u ∈ sample stream (s + 1) := by simpa using hu
    rw [mem_sample_iff] at hu'
    obtain ⟨q, hq, rfl⟩ := hu'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hqs | rfl
    · exact ha.2.1 (value_mem_sample hqs)
    · exact hmem
  have haBad : BadStrictCritical C stream s (stream s) (a s) :=
    ⟨ha.2, hwa⟩
  have hbad : ∃ n, BadStrictCritical C stream s (stream s) n :=
    ⟨a s, haBad⟩
  have hnoBadBefore :
      ∀ n, n < a s → ¬BadStrictCritical C stream s (stream s) n := by
    intro n hna hnBad
    by_cases hnz : n < z
    · have hsub : C z ⊆ C n :=
        (strictCritical_ssubset_of_lt hnz hnBad.1 hzcrit).le
      exact hnBad.2 (hsub hwz)
    · have hzn : z ≤ n := Nat.le_of_not_gt hnz
      rcases eq_or_lt_of_le hzn with rfl | hzn'
      · exact hnBad.2 hwz
      · have hmin := nextStrictCritical_min hEs ⟨hzn', hnBad.1⟩
        exact not_lt_of_ge hmin hna
  have hfirstBad :
      firstBadStrictCritical C stream s (stream s) = a s := by
    apply le_antisymm
    · exact firstBadStrictCritical_min hbad haBad
    · by_contra hnot
      have hlt : firstBadStrictCritical C stream s (stream s) < a s := by
        omega
      exact hnoBadBefore _ hlt (firstBadStrictCritical_spec hbad)
  let B := boundaryCandidates C stream s (stream s)
  have hzB : z ∈ B := by
    apply mem_boundaryCandidates.mpr
    exact ⟨by simpa [hfirstBad] using ha.1, hzcrit, hwz⟩
  have hBne : B.Nonempty := ⟨z, hzB⟩
  have hBmax : B.max' hBne = z := by
    apply le_antisymm
    · apply Finset.max'_le
      intro n hnB
      have hnParts := mem_boundaryCandidates.mp (by simpa [B] using hnB)
      by_contra hnle
      have hzn : z < n := Nat.lt_of_not_ge hnle
      have hmin := nextStrictCritical_min hEs ⟨hzn, hnParts.2.1⟩
      have hna : n < a s := by simpa [hfirstBad] using hnParts.1
      exact not_lt_of_ge hmin hna
    · exact Finset.le_max' B z hzB
  have hallFalse :
      ¬∀ n, StrictCritical C stream s n → stream s ∈ C n := by
    intro hall
    exact hwa (hall (a s) ha.2)
  have hselect : selectIndex C stream s (stream s) = z := by
    rw [selectIndex]
    simp only [dif_neg hallFalse]
    simp [B, hBne, hBmax]
  have hacc : AccurateAt C stream z (s + 1) := by
    simp [AccurateAt, guessIndex, hselect]
  exact hfuture (s + 1) (le_trans htN (by omega)) hacc

/-- Theorem 3.1: one selector is eventually index-valid and accurate at
arbitrarily late rounds. -/
theorem theorem_3_1
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    IndexValidInLimit C stream z ∧
      ∀ t, ∃ r, t ≤ r ∧ AccurateAt C stream z r :=
  ⟨proposition_3_4 hP hfirst, proposition_3_5 hP hfirst⟩

/-- Overview Theorem 2.1. -/
theorem theorem_2_1
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    IndexValidInLimit C stream z ∧
      ∀ t, ∃ r, t ≤ r ∧ AccurateAt C stream z r :=
  theorem_3_1 hP hfirst

end GenLimit.KleinbergWei.DensityMeasures

end

-- GenLimit.Paper30_TimeSensitiveLanguageGeneration.AccurateBridge
section
set_option autoImplicit true

/-!
# Appendix E: reuse of the P07 accurate selector

Appendix E's GCG construction assumes an `Accurate` subroutine whose guessed
language is eventually contained in the target and equals the target at
arbitrarily late rounds.  P07 already proves exactly that semantic guarantee
for its strict-critical selector.  This file records the dependency as a thin
bridge instead of duplicating the selector or its proof.

The bridge does not establish Theorem 4 by itself.  The documented
queue-totalized consumer and its checkpoint proof are in
`TotalizedGCGMachine`, `TotalizedGCGProgress`, and `TotalizedGCGMain`.
-/

namespace GenLimit.TimeSensitive

open GenLimit.KleinbergWei
open GenLimit.KleinbergWei.DensityMeasures

/-- The P07 strict-critical selector supplies the `Accurate` oracle contract
used by P30 Appendix E: eventual target containment and cofinally many exact
target guesses. -/
theorem appendix_E_accurate_oracle_from_paper07
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    IndexValidInLimit C stream z ∧
      ∀ t, ∃ r, t ≤ r ∧ AccurateAt C stream z r :=
  GenLimit.KleinbergWei.DensityMeasures.theorem_2_1 hP hfirst

end GenLimit.TimeSensitive

end

-- GenLimit.Paper30_TimeSensitiveLanguageGeneration.AccurateCausality
section
set_option autoImplicit true

/-!
# Prefix causality of the P07 accurate selector

P30's adversary speaks before the generator in each round.  To run the
repaired GCG against an adaptive presentation, the semantic P07 selector must
therefore be evaluable from the finite observation history available at that
round.  This module proves that `guessIndex C stream t` depends only on the
first `t` values of `stream`.

The result is extensional: no computability claim about the selector or the
language family is introduced.
-/

namespace GenLimit.TimeSensitive

open GenLimit.KleinbergWei.DensityMeasures

theorem consistent_iff_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t i : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    Consistent C stream₁ t i ↔ Consistent C stream₂ t i := by
  have hsample : sample stream₁ t = sample stream₂ t :=
    GenLimit.sample_eq_of_eq_on_prefix hstream
  simp only [Consistent, hsample]

theorem strictCritical_iff_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t i : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    StrictCritical C stream₁ t i ↔ StrictCritical C stream₂ t i := by
  unfold StrictCritical
  constructor
  · rintro ⟨hi, hminimal⟩
    refine ⟨(consistent_iff_of_eqOn_prefix hstream).mp hi, ?_⟩
    intro j hji hj
    exact hminimal j hji
      ((consistent_iff_of_eqOn_prefix hstream).mpr hj)
  · rintro ⟨hi, hminimal⟩
    refine ⟨(consistent_iff_of_eqOn_prefix hstream).mpr hi, ?_⟩
    intro j hji hj
    exact hminimal j hji
      ((consistent_iff_of_eqOn_prefix hstream).mp hj)

theorem scopedStrictCriticalIndices_eq_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    scopedStrictCriticalIndices C stream₁ t =
      scopedStrictCriticalIndices C stream₂ t := by
  classical
  ext i
  simp only [mem_scopedStrictCriticalIndices]
  exact and_congr_right fun _ => strictCritical_iff_of_eqOn_prefix hstream

theorem scopedFocus_eq_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    scopedFocus C stream₁ t = scopedFocus C stream₂ t := by
  classical
  simp only [scopedFocus]
  rw [scopedStrictCriticalIndices_eq_of_eqOn_prefix hstream]

theorem badStrictCritical_iff_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t w i : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    BadStrictCritical C stream₁ t w i ↔
      BadStrictCritical C stream₂ t w i := by
  unfold BadStrictCritical
  constructor
  · rintro ⟨hi, hw⟩
    exact ⟨(strictCritical_iff_of_eqOn_prefix hstream).mp hi, hw⟩
  · rintro ⟨hi, hw⟩
    exact ⟨(strictCritical_iff_of_eqOn_prefix hstream).mpr hi, hw⟩

theorem firstBadStrictCritical_eq_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t w : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    firstBadStrictCritical C stream₁ t w =
      firstBadStrictCritical C stream₂ t w := by
  classical
  by_cases hbad₁ : ∃ i, BadStrictCritical C stream₁ t w i
  · have hbad₂ : ∃ i, BadStrictCritical C stream₂ t w i := by
      obtain ⟨i, hi⟩ := hbad₁
      exact ⟨i, (badStrictCritical_iff_of_eqOn_prefix hstream).mp hi⟩
    simp only [firstBadStrictCritical, dif_pos hbad₁, dif_pos hbad₂]
    exact Nat.find_congr'
      (fun {_} => badStrictCritical_iff_of_eqOn_prefix hstream)
  · have hbad₂ : ¬∃ i, BadStrictCritical C stream₂ t w i := by
      intro h
      obtain ⟨i, hi⟩ := h
      exact hbad₁ ⟨i, (badStrictCritical_iff_of_eqOn_prefix hstream).mpr hi⟩
    simp [firstBadStrictCritical, hbad₁, hbad₂]

theorem boundaryCandidates_eq_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t w : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    boundaryCandidates C stream₁ t w =
      boundaryCandidates C stream₂ t w := by
  classical
  ext i
  simp only [mem_boundaryCandidates]
  rw [firstBadStrictCritical_eq_of_eqOn_prefix hstream]
  constructor
  · rintro ⟨hi, hcritical, hw⟩
    exact ⟨hi, (strictCritical_iff_of_eqOn_prefix hstream).mp hcritical, hw⟩
  · rintro ⟨hi, hcritical, hw⟩
    exact ⟨hi, (strictCritical_iff_of_eqOn_prefix hstream).mpr hcritical, hw⟩

theorem selectIndex_eq_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t w : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    selectIndex C stream₁ t w = selectIndex C stream₂ t w := by
  classical
  have hcritical : ∀ i,
      StrictCritical C stream₁ t i ↔ StrictCritical C stream₂ t i :=
    fun _ => strictCritical_iff_of_eqOn_prefix hstream
  have hall :
      (∀ i, StrictCritical C stream₁ t i → w ∈ C i) ↔
        ∀ i, StrictCritical C stream₂ t i → w ∈ C i := by
    constructor
    · intro h i hi
      exact h i ((hcritical i).mpr hi)
    · intro h i hi
      exact h i ((hcritical i).mp hi)
  by_cases h₁ : ∀ i, StrictCritical C stream₁ t i → w ∈ C i
  · have h₂ : ∀ i, StrictCritical C stream₂ t i → w ∈ C i := hall.mp h₁
    simp only [selectIndex, dif_pos h₁, dif_pos h₂]
    exact scopedFocus_eq_of_eqOn_prefix hstream
  · have h₂ : ¬∀ i, StrictCritical C stream₂ t i → w ∈ C i :=
      fun h => h₁ (hall.mpr h)
    simp only [selectIndex, dif_neg h₁, dif_neg h₂]
    rw [boundaryCandidates_eq_of_eqOn_prefix hstream]
    by_cases hS : (boundaryCandidates C stream₂ t w).Nonempty
    · simp [hS]
    · simp [hS, scopedFocus_eq_of_eqOn_prefix hstream]

/-- The P07 selector is causal at its paper-facing time index. -/
theorem guessIndex_eq_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    guessIndex C stream₁ t = guessIndex C stream₂ t := by
  cases t with
  | zero => rfl
  | succ t =>
      simp only [guessIndex]
      have hcurrent : stream₁ t = stream₂ t :=
        hstream t (Nat.lt_succ_self t)
      rw [← hcurrent]
      apply selectIndex_eq_of_eqOn_prefix
      intro n hn
      exact hstream n (hn.trans (Nat.lt_succ_self t))

end GenLimit.TimeSensitive

end

-- GenLimit.Paper30_TimeSensitiveLanguageGeneration.GCGCommon
section
set_option autoImplicit true

/-!
# Shared infrastructure for Generation via Consistent Guessing

This module contains the queue-policy-independent data and greedy output operation
shared by the printed strict-rise GCG skeleton and the queue-totalized repair.
It deliberately contains no candidate-queue policy and no stage transition.
-/

namespace GenLimit.TimeSensitive

open GenLimit.KleinbergWei
open GenLimit.KleinbergWei.DensityMeasures

/-- A family together with the canonical order inherited by each language.
The coherence field rules out assigning two different orders to equal sets. -/
structure CanonicallyOrderedFamily where
  language : LanguageFamily
  order : ℕ → OrderedLanguage
  carrier_eq : ∀ i, (order i).carrier = language i
  order_eq_of_language_eq :
    ∀ {i j}, language i = language j → (order i).enumeration = (order j).enumeration

namespace CanonicallyOrderedFamily

variable (F : CanonicallyOrderedFamily)

/-- Every family member is infinite because its canonical order is an
injective enumeration by all natural ranks. -/
theorem language_infinite (i : ℕ) : (F.language i).Infinite := by
  rw [← F.carrier_eq i, ← (F.order i).range_enumeration]
  exact Set.infinite_range_of_injective (F.order i).enumeration_injective

/-- The P07 semantic selector used as Appendix E's `Accurate` subroutine. -/
noncomputable def guess (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  guessIndex F.language stream t

end CanonicallyOrderedFamily

/-- Ranks eligible for the source's `OnTimeUnused` operation. -/
def OnTimeUnusedRank
    (O : OrderedLanguage) (used : Finset ℕ) (t r : ℕ) : Prop :=
  t < r ∧ O.enumeration r ∉ used

/-- Among `used.card + 1` ranks strictly after `t`, at least one has an
unused image under an injective language enumeration. -/
theorem exists_onTimeUnusedRank
    (O : OrderedLanguage) (used : Finset ℕ) (t : ℕ) :
    ∃ r, OnTimeUnusedRank O used t r := by
  classical
  let ranks := Finset.Icc (t + 1) (t + used.card + 1)
  by_contra h
  push_neg at h
  have hmaps : ∀ r ∈ ranks, O.enumeration r ∈ used := by
    intro r hr
    by_contra hnot
    exact h r
      ⟨Nat.lt_of_succ_le (Finset.mem_Icc.mp hr).1, hnot⟩
  have hsubset : ranks.image O.enumeration ⊆ used := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    exact hmaps r hr
  have hcardImage : (ranks.image O.enumeration).card = ranks.card := by
    exact Finset.card_image_iff.mpr fun a _ b _ hab =>
      O.enumeration_injective hab
  have hcardRanks : ranks.card = used.card + 1 := by
    simp only [ranks, Nat.card_Icc]
    omega
  have hle := Finset.card_le_card hsubset
  omega

/-- The least on-time rank whose language element has not been used. -/
noncomputable def onTimeUnusedRank
    (O : OrderedLanguage) (used : Finset ℕ) (t : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_onTimeUnusedRank O used t)

theorem onTimeUnusedRank_spec
    (O : OrderedLanguage) (used : Finset ℕ) (t : ℕ) :
    OnTimeUnusedRank O used t (onTimeUnusedRank O used t) :=
  by
    classical
    exact Nat.find_spec (exists_onTimeUnusedRank O used t)

theorem onTimeUnusedRank_min
    (O : OrderedLanguage) (used : Finset ℕ) (t : ℕ)
    {r : ℕ} (hr : OnTimeUnusedRank O used t r) :
    onTimeUnusedRank O used t ≤ r :=
  by
    classical
    exact Nat.find_min' (exists_onTimeUnusedRank O used t) hr

/-- Algorithm 2's first fresh member that has not missed its identity
deadline, expressed through the supplied canonical language order. -/
noncomputable def onTimeUnused
    (O : OrderedLanguage) (used : Finset ℕ) (t : ℕ) : ℕ :=
  O.enumeration (onTimeUnusedRank O used t)

theorem onTimeUnused_mem
    (O : OrderedLanguage) (used : Finset ℕ) (t : ℕ) :
    onTimeUnused O used t ∈ O.carrier := by
  rw [← O.range_enumeration]
  exact ⟨onTimeUnusedRank O used t, rfl⟩

theorem onTimeUnused_fresh
    (O : OrderedLanguage) (used : Finset ℕ) (t : ℕ) :
    onTimeUnused O used t ∉ used :=
  (onTimeUnusedRank_spec O used t).2

theorem onTimeUnused_onTime
    (O : OrderedLanguage) (used : Finset ℕ) (t : ℕ) :
    t < onTimeUnusedRank O used t :=
  (onTimeUnusedRank_spec O used t).1

/-- Values unavailable after the adversary has spoken in round `t`. -/
noncomputable def greedyUsed
    (stream : ℕ → ℕ) (t : ℕ) (outputs : List ℕ) : Finset ℕ :=
  sample stream (t + 1) ∪ outputs.toFinset

/-- Shared greedy output operation once a queue policy has selected the active
ordered language. -/
noncomputable def greedyRoundOutput
    (O : OrderedLanguage) (stream : ℕ → ℕ)
    (t : ℕ) (outputs : List ℕ) : ℕ :=
  onTimeUnused O (greedyUsed stream t outputs) t

/-- Turn a finite chronological output history into a total sequence.  Only
prefixes below `outputs.length` are semantically used by the machines. -/
def outputHistoryStream (outputs : List ℕ) : ℕ → ℕ :=
  fun t => outputs.getD t 0

end GenLimit.TimeSensitive

end

-- GenLimit.Paper30_TimeSensitiveLanguageGeneration.Definitions
section
set_option autoImplicit true

/-!
# Time-sensitive generation: deterministic definitions

Source: Atul Ganju, Travis McVoy, Shaddin Dughmi, and Shang-Hua Teng,
*A Theory of Time-Sensitive Language Generation: Sparse Hallucination Beats
Mode Collapse*, arXiv:2605.11302v2, Sections 1.1--3 and Appendix C.

The paper's generators are randomized.  This file deliberately isolates the
pathwise, finite-prefix objects to which the probability argument is later
applied: deadlines, timely credited strings, prefix-wise credit, and distinct
hallucinated outputs.  No probability space or runtime claim is hidden in
these definitions.

All prefixes are zero-based: `Finset.range n` represents the first `n`
positions.  A deadline value `D j` therefore exposes output indices strictly
below `D j`, exactly as the source's prefix `S_{D(j)}`.
-/

namespace GenLimit.TimeSensitive

open Filter
open GenLimit.KleinbergWei

/-- A monotone nondecreasing deadline function. -/
structure Deadline where
  toFun : ℕ → ℕ
  monotone' : Monotone toFun

instance : CoeFun Deadline (fun _ => ℕ → ℕ) :=
  ⟨Deadline.toFun⟩

/-- The additional unboundedness needed for the paper's generalized inverse
`min {n : D n ≥ t}` to exist at every time. -/
def Deadline.IsUnbounded (D : Deadline) : Prop :=
  ∀ t, ∃ n, t ≤ D n

/-- The generalized inverse used throughout Sections 2--3.

Unlike the paper's bare `min` notation, the definition records the
unboundedness witness needed to make the minimum total. -/
noncomputable def Deadline.inverse
    (D : Deadline) (hD : D.IsUnbounded) (t : ℕ) : ℕ :=
  Nat.find (hD t)

theorem Deadline.le_inverse_value
    (D : Deadline) (hD : D.IsUnbounded) (t : ℕ) :
    t ≤ D (D.inverse hD t) :=
  Nat.find_spec (hD t)

theorem Deadline.inverse_min
    (D : Deadline) (hD : D.IsUnbounded) {t n : ℕ}
    (hn : t ≤ D n) :
    D.inverse hD t ≤ n :=
  Nat.find_min' (hD t) hn

theorem Deadline.inverse_mono
    (D : Deadline) (hD : D.IsUnbounded) :
    Monotone (D.inverse hD) := by
  intro s t hst
  apply Deadline.inverse_min
  exact hst.trans (Deadline.le_inverse_value D hD t)

/-! ## Generalized-inverse diagnostics -/

/-- A monotone deadline for which the paper's bare generalized inverse is
undefined at every positive time. -/
def zeroDeadline : Deadline where
  toFun := fun _ => 0
  monotone' := fun _ _ _ => le_rfl

theorem zeroDeadline_not_unbounded :
    ¬zeroDeadline.IsUnbounded := by
  intro h
  obtain ⟨n, hn⟩ := h 1
  simp [zeroDeadline] at hn

/-- A non-strictly-monotone but unbounded deadline whose inverse hits only
even indices.  This records why a liminf argument cannot silently assume
that generalized-inverse indices range over every natural number. -/
def halfDeadline : Deadline where
  toFun := fun n => n / 2
  monotone' := fun _ _ h => Nat.div_le_div_right h

theorem halfDeadline_unbounded :
    halfDeadline.IsUnbounded := by
  intro t
  refine ⟨2 * t, ?_⟩
  simp [halfDeadline]

theorem halfDeadline_inverse
    (t : ℕ) :
    halfDeadline.inverse halfDeadline_unbounded t = 2 * t := by
  apply le_antisymm
  · apply Deadline.inverse_min
    simp [halfDeadline]
  · have hspec :=
      Deadline.le_inverse_value
        halfDeadline halfDeadline_unbounded t
    change t ≤ halfDeadline.inverse halfDeadline_unbounded t / 2 at hspec
    omega

theorem halfDeadline_inverse_even
    (t : ℕ) :
    Even (halfDeadline.inverse halfDeadline_unbounded t) := by
  rw [halfDeadline_inverse]
  exact ⟨t, by omega⟩

/-- Distinct values appearing in the first `n` positions of a sequence. -/
noncomputable def sequencePrefix
    (S : ℕ → α) (n : ℕ) : Finset α := by
  classical
  exact (Finset.range n).image S

theorem mem_sequencePrefix_iff
    (S : ℕ → α) (x : α) (n : ℕ) :
    x ∈ sequencePrefix S n ↔ ∃ k < n, S k = x := by
  classical
  simp [sequencePrefix]

theorem sequencePrefix_mono
    (S : ℕ → α) {m n : ℕ} (hmn : m ≤ n) :
    sequencePrefix S m ⊆ sequencePrefix S n := by
  classical
  intro x hx
  obtain ⟨k, hk, rfl⟩ := (mem_sequencePrefix_iff S x m).mp hx
  exact (mem_sequencePrefix_iff S (S k) n).mpr
    ⟨k, lt_of_lt_of_le hk hmn, rfl⟩

/-- The target strings among its first `i` ordered positions. -/
noncomputable def targetPrefix
    (R : ℕ → α) (i : ℕ) : Finset α :=
  sequencePrefix R i

/-- Definition 1.1's timely credited target strings: `R j` is credited only
when it occurs in the output prefix cut off by its own deadline `D j`. -/
noncomputable def timelyElements
    (S R : ℕ → α) (D : ℕ → ℕ) (i : ℕ) : Finset α := by
  classical
  exact ((Finset.range i).filter
    (fun j => R j ∈ sequencePrefix S (D j))).image R

/-- Definition 3's prefix-wise credited target strings: the common cutoff is
`F i`, rather than the individual cutoff `D j`. -/
noncomputable def prefixWiseElements
    (S R : ℕ → α) (F : ℕ → ℕ) (i : ℕ) : Finset α := by
  classical
  exact targetPrefix R i ∩ sequencePrefix S (F i)

/-- Finite element-wise timely density.  The empty prefix is assigned zero. -/
noncomputable def timelyDensity
    (S R : ℕ → α) (D : ℕ → ℕ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else (timelyElements S R D i).card / (i : ℝ)

/-- Definition 3: finite prefix-wise timely density. -/
noncomputable def prefixWiseDensity
    (S R : ℕ → α) (F : ℕ → ℕ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else (prefixWiseElements S R F i).card / (i : ℝ)

/-- Instance-level lower timely density.  The paper then infimizes this
quantity over targets, enumerations, and countable collections. -/
noncomputable def lowerTimelyDensity
    (S R : ℕ → α) (D : ℕ → ℕ) : ℝ :=
  liminf (timelyDensity S R D) atTop

/-- Definition 4's instance-level upper timely density. -/
noncomputable def upperTimelyDensity
    (S R : ℕ → α) (D : ℕ → ℕ) : ℝ :=
  limsup (timelyDensity S R D) atTop

/-- Definition 3's instance-level lower prefix-wise density. -/
noncomputable def lowerPrefixWiseDensity
    (S R : ℕ → α) (F : ℕ → ℕ) : ℝ :=
  liminf (prefixWiseDensity S R F) atTop

/-- Distinct generated values outside `L` by time `t`.  Under the paper's
fresh-output rule this is exactly `|A(E)_t \ L|`. -/
noncomputable def hallucinationCount
    (S : ℕ → α) (L : Set α) (t : ℕ) : ℕ := by
  classical
  exact ((sequencePrefix S t).filter fun x => x ∉ L).card

/-- Number of the first `i` target strings lying in an intermediate
language `L`. -/
noncomputable def targetIntersectionCount
    (R : ℕ → α) (L : Set α) (i : ℕ) : ℕ := by
  classical
  exact ((targetPrefix R i).filter fun x => x ∈ L).card

/-- Definition 1, with the limiting language's preference order made
explicit.  Indexing starts at zero instead of one. -/
structure MeasureZeroChain where
  limit : OrderedLanguage
  level : ℕ → Set ℕ
  nested : Monotone level
  union_eq : (⋃ j, level j) = limit.carrier
  sparse : ∀ j, limit.lowerDensity (level j) = 0

theorem MeasureZeroChain.level_subset_limit
    (C : MeasureZeroChain) (j : ℕ) :
    C.level j ⊆ C.limit.carrier := by
  intro x hx
  rw [← C.union_eq]
  exact Set.mem_iUnion.mpr ⟨j, hx⟩

theorem MeasureZeroChain.exists_level_of_mem
    (C : MeasureZeroChain) {x : ℕ}
    (hx : x ∈ C.limit.carrier) :
    ∃ j, x ∈ C.level j := by
  rw [← C.union_eq] at hx
  exact Set.mem_iUnion.mp hx

end GenLimit.TimeSensitive

end

-- GenLimit.Paper30_TimeSensitiveLanguageGeneration.DensityReduction
section
set_option autoImplicit true

/-!
# Deterministic density reductions

This file formalizes the finite, pathwise bookkeeping in Lemma 2
(Appendix-D Lemma 5) and Appendix-C Lemma 4 of
Ganju--McVoy--Dughmi--Teng, arXiv:2605.11302v2.

The analytic construction of the slowed deadline and the randomized
black-box generator are outside this module.  The results here are the exact
inequalities to which those asymptotic and probabilistic arguments reduce.
-/

namespace GenLimit.TimeSensitive

open Filter

/-- Element-wise credit is contained in prefix-wise credit at the current
deadline whenever deadlines are monotone.  This is the inequality
`μ_i ≤ μ_i^pfx` used at the end of Appendix-C Lemma 4. -/
theorem timelyElements_subset_prefixWiseElements
    (S R : ℕ → α) (D : Deadline) (i : ℕ) :
    timelyElements S R D i ⊆ prefixWiseElements S R D i := by
  classical
  intro x hx
  simp only [timelyElements, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range] at hx
  obtain ⟨j, ⟨hji, hjout⟩, rfl⟩ := hx
  have htarget : R j ∈ targetPrefix R i :=
    (mem_sequencePrefix_iff R (R j) i).mpr ⟨j, hji, rfl⟩
  have hdeadline : D j ≤ D i :=
    D.monotone' (Nat.le_of_lt hji)
  have hout : R j ∈ sequencePrefix S (D i) :=
    sequencePrefix_mono S hdeadline hjout
  exact Finset.mem_inter.mpr ⟨htarget, hout⟩

theorem timelyElements_card_le_prefixWiseElements_card
    (S R : ℕ → α) (D : Deadline) (i : ℕ) :
    (timelyElements S R D i).card ≤
      (prefixWiseElements S R D i).card := by
  classical
  exact Finset.card_le_card
    (timelyElements_subset_prefixWiseElements S R D i)

theorem timelyDensity_le_prefixWiseDensity
    (S R : ℕ → α) (D : Deadline) (i : ℕ) :
    timelyDensity S R D i ≤ prefixWiseDensity S R D i := by
  by_cases hi : i = 0
  · simp [timelyDensity, prefixWiseDensity, hi]
  · simp only [timelyDensity, prefixWiseDensity, hi, if_false]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast
        timelyElements_card_le_prefixWiseElements_card S R D i)
      (Nat.cast_nonneg i)

theorem timelyDensity_nonneg
    (S R : ℕ → α) (D : ℕ → ℕ) (i : ℕ) :
    0 ≤ timelyDensity S R D i := by
  unfold timelyDensity
  split <;> positivity

theorem timelyDensity_le_one
    (S R : ℕ → α) (D : ℕ → ℕ) (i : ℕ) :
    timelyDensity S R D i ≤ 1 := by
  by_cases hi : i = 0
  · simp [timelyDensity, hi]
  · simp only [timelyDensity, hi, if_false]
    have hiReal : (0 : ℝ) < i := by
      exact_mod_cast Nat.pos_of_ne_zero hi
    rw [div_le_one hiReal]
    have hcard :
        (timelyElements S R D i).card ≤ i := by
      classical
      unfold timelyElements
      exact
        (Finset.card_image_le.trans
          (Finset.card_filter_le _ _)).trans_eq
            (Finset.card_range i)
    exact_mod_cast hcard

theorem prefixWiseDensity_nonneg
    (S R : ℕ → α) (F : ℕ → ℕ) (i : ℕ) :
    0 ≤ prefixWiseDensity S R F i := by
  unfold prefixWiseDensity
  split <;> positivity

theorem prefixWiseDensity_le_one
    (S R : ℕ → α) (F : ℕ → ℕ) (i : ℕ) :
    prefixWiseDensity S R F i ≤ 1 := by
  by_cases hi : i = 0
  · simp [prefixWiseDensity, hi]
  · simp only [prefixWiseDensity, hi, if_false]
    have hiReal : (0 : ℝ) < i := by
      exact_mod_cast Nat.pos_of_ne_zero hi
    rw [div_le_one hiReal]
    have hcard : (prefixWiseElements S R F i).card ≤ i := by
      classical
      unfold prefixWiseElements targetPrefix sequencePrefix
      exact (Finset.card_le_card Finset.inter_subset_left).trans
        (Finset.card_image_le.trans_eq (Finset.card_range i))
    exact_mod_cast hcard

/-- Exact finite-prefix core of Appendix-D Lemma 5.

If at most the first `r` target positions have a deadline earlier than the
common prefix cutoff `F i`, then every prefix-wise credited string except
possibly those `r` strings is element-wise timely. -/
theorem prefixWiseElements_subset_timely_union_early
    (S R : ℕ → α)
    (D F : ℕ → ℕ) (i r : ℕ)
    (hcutoff :
      ∀ j, j < i → r ≤ j → F i ≤ D j) :
    ∀ x, x ∈ prefixWiseElements S R F i →
      x ∈ timelyElements S R D i ∨ x ∈ targetPrefix R r := by
  classical
  intro x hx
  by_cases hearly : x ∈ targetPrefix R r
  · exact Or.inr hearly
  · apply Or.inl
    have htarget := (Finset.mem_inter.mp hx).1
    have hout := (Finset.mem_inter.mp hx).2
    obtain ⟨j, hji, hjx⟩ :=
      (mem_sequencePrefix_iff R x i).mp htarget
    have hrj : r ≤ j := by
      by_contra hnot
      have hjr : j < r := Nat.lt_of_not_ge hnot
      exact hearly
        ((mem_sequencePrefix_iff R x r).mpr ⟨j, hjr, hjx⟩)
    have hout' : x ∈ sequencePrefix S (D j) :=
      sequencePrefix_mono S (hcutoff j hji hrj) hout
    simp only [timelyElements, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨j, ⟨hji, hjx ▸ hout'⟩, hjx⟩

/-- Cardinal form of the finite-prefix reduction:
`prefix-credit ≤ element-credit + r`. -/
theorem prefixWise_card_le_timely_card_add
    (S R : ℕ → α) (hR : Function.Injective R)
    (D F : ℕ → ℕ) (i r : ℕ)
    (hcutoff :
      ∀ j, j < i → r ≤ j → F i ≤ D j) :
    (prefixWiseElements S R F i).card ≤
      (timelyElements S R D i).card + r := by
  classical
  have hsubset :
      prefixWiseElements S R F i ⊆
        timelyElements S R D i ∪ targetPrefix R r := by
    intro x hx
    exact Finset.mem_union.mpr
      (prefixWiseElements_subset_timely_union_early
        S R D F i r hcutoff x hx)
  calc
    (prefixWiseElements S R F i).card
        ≤ (timelyElements S R D i ∪ targetPrefix R r).card :=
      Finset.card_le_card hsubset
    _ ≤ (timelyElements S R D i).card +
          (targetPrefix R r).card :=
      Finset.card_union_le _ _
    _ = (timelyElements S R D i).card + r := by
      rw [targetPrefix, sequencePrefix]
      rw [Finset.card_image_iff.mpr]
      · simp
      · intro a _ b _ hab
        exact hR hab

/-- Ratio form printed in Appendix D.1:
`μ_i ≥ μ_i^pfx - r(i)/i`. -/
theorem prefixWiseDensity_sub_exception_le_timelyDensity
    (S R : ℕ → α) (hR : Function.Injective R)
    (D F : ℕ → ℕ) {i r : ℕ} (hi : 0 < i)
    (hcutoff :
      ∀ j, j < i → r ≤ j → F i ≤ D j) :
    prefixWiseDensity S R F i - (r : ℝ) / i ≤
      timelyDensity S R D i := by
  have hi0 : i ≠ 0 := Nat.ne_of_gt hi
  simp only [prefixWiseDensity, timelyDensity, hi0, if_false]
  have hcard :=
    prefixWise_card_le_timely_card_add S R hR D F i r hcutoff
  have hcardReal :
      ((prefixWiseElements S R F i).card : ℝ) ≤
        (((timelyElements S R D i).card + r : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hiReal : (0 : ℝ) < i := by exact_mod_cast hi
  rw [sub_le_iff_le_add]
  calc
    ((prefixWiseElements S R F i).card : ℝ) / i
        ≤ ((timelyElements S R D i).card + r : ℕ) / (i : ℝ) := by
      exact div_le_div_of_nonneg_right hcardReal hiReal.le
    _ = ((timelyElements S R D i).card : ℝ) / i +
          (r : ℝ) / i := by
      push_cast
      ring

/-! ## Appendix-D's deadline-exception index -/

/-- The zero-based version of Appendix D's
`r(i) = max {j ≤ i : Dₑₗ(j) < Dₚ𝒻ₓ(i)}`.

Because target positions are zero-based in Lean, the number of exceptional
positions is the cardinality of the corresponding filtered prefix.  For a
monotone element-wise deadline those positions form an initial segment, so
this cardinality is also the cutoff used in the paper's density loss
`r(i) / i`. -/
def deadlineExceptionCount
    (D : Deadline) (F : ℕ → ℕ) (i : ℕ) : ℕ :=
  ((Finset.range i).filter fun j => D j < F i).card

theorem deadlineExceptionCount_le
    (D : Deadline) (F : ℕ → ℕ) (i : ℕ) :
    deadlineExceptionCount D F i ≤ i := by
  unfold deadlineExceptionCount
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range i)

/-- Monotonicity makes the early-deadline exceptions an initial segment:
every position at or beyond their count meets the common prefix cutoff. -/
theorem deadlineExceptionCount_cutoff
    (D : Deadline) (F : ℕ → ℕ) (i : ℕ) :
    ∀ j, j < i → deadlineExceptionCount D F i ≤ j →
      F i ≤ D j := by
  intro j hji hrj
  by_contra hnot
  have hjEarly : D j < F i := Nat.lt_of_not_ge hnot
  have hsubset :
      Finset.range (j + 1) ⊆
        (Finset.range i).filter (fun k => D k < F i) := by
    intro k hk
    have hkj : k ≤ j := by
      have hklt : k < j + 1 := Finset.mem_range.mp hk
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (lt_of_le_of_lt hkj hji),
        (D.monotone' hkj).trans_lt hjEarly⟩
  have hcard :
      j + 1 ≤ deadlineExceptionCount D F i := by
    simpa [deadlineExceptionCount] using Finset.card_le_card hsubset
  omega

/-- Appendix-D Lemma 5 with the source-defined exception count rather than
an abstract cutoff hypothesis. -/
theorem prefixWiseDensity_sub_deadlineException_le_timelyDensity
    (S R : ℕ → α) (hR : Function.Injective R)
    (D : Deadline) (F : ℕ → ℕ) {i : ℕ} (hi : 0 < i) :
    prefixWiseDensity S R F i -
        (deadlineExceptionCount D F i : ℝ) / i ≤
      timelyDensity S R D i := by
  exact prefixWiseDensity_sub_exception_le_timelyDensity
    S R hR D F hi (deadlineExceptionCount_cutoff D F i)

/-- The normalized exceptional-prefix loss used in Appendix D. -/
noncomputable def deadlineExceptionRatio
    (D : Deadline) (F : ℕ → ℕ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else (deadlineExceptionCount D F i : ℝ) / i

theorem deadlineExceptionRatio_nonneg
    (D : Deadline) (F : ℕ → ℕ) (i : ℕ) :
    0 ≤ deadlineExceptionRatio D F i := by
  by_cases hi : i = 0
  · simp [deadlineExceptionRatio, hi]
  · simp only [deadlineExceptionRatio, hi, if_false]
    positivity

theorem deadlineExceptionRatio_le_one
    (D : Deadline) (F : ℕ → ℕ) (i : ℕ) :
    deadlineExceptionRatio D F i ≤ 1 := by
  by_cases hi : i = 0
  · simp [deadlineExceptionRatio, hi]
  · simp only [deadlineExceptionRatio, hi, if_false]
    have hiReal : (0 : ℝ) < i := by
      exact_mod_cast Nat.pos_of_ne_zero hi
    rw [div_le_one hiReal]
    exact_mod_cast deadlineExceptionCount_le D F i

/-- Pointwise Appendix-D comparison, totalized at the empty prefix. -/
theorem prefixWiseDensity_le_timelyDensity_add_deadlineExceptionRatio
    (S R : ℕ → α) (hR : Function.Injective R)
    (D : Deadline) (F : ℕ → ℕ) (i : ℕ) :
    prefixWiseDensity S R F i ≤
      timelyDensity S R D i + deadlineExceptionRatio D F i := by
  by_cases hi : i = 0
  · simp [prefixWiseDensity, timelyDensity, deadlineExceptionRatio, hi]
  · have h :=
      prefixWiseDensity_sub_deadlineException_le_timelyDensity
        S R hR D F (Nat.pos_of_ne_zero hi)
    simpa [deadlineExceptionRatio, hi, sub_le_iff_le_add] using h

/-- The deterministic liminf endgame of Appendix-D Lemma 5.

Once the deadline construction supplies `r(i) / i → 0`, the prefix-wise
lower density cannot exceed the original element-wise lower density.  This
theorem isolates exactly the analytic conclusion; constructing the slowed
deadline and proving its exception ratio vanishes remain the paper's
countable-diagonal step. -/
theorem lowerPrefixWiseDensity_le_lowerTimelyDensity_of_exceptionRatio
    (S R : ℕ → α) (hR : Function.Injective R)
    (D : Deadline) (F : ℕ → ℕ)
    (hvanishing :
      Tendsto (deadlineExceptionRatio D F) atTop (nhds 0)) :
    lowerPrefixWiseDensity S R F ≤ lowerTimelyDensity S R D := by
  unfold lowerPrefixWiseDensity lowerTimelyDensity
  exact GenLimit.liminf_le_liminf_of_eventually_le_add_tendsto_zero
    (prefixWiseDensity_nonneg S R F)
    (prefixWiseDensity_le_one S R F)
    (timelyDensity_le_one S R D)
    (Eventually.of_forall
      (prefixWiseDensity_le_timelyDensity_add_deadlineExceptionRatio
        S R hR D F))
    hvanishing

/-- Pathwise finite decomposition in Appendix-C Lemma 4.

Every credited string in the first `i` target positions is either already in
the intermediate language `L`, or is a distinct output outside `L`. -/
theorem prefix_credit_le_target_intersection_add_hallucinations
    (S R : ℕ → α) (L : Set α) (i t : ℕ) :
    (prefixWiseElements S R (fun _ => t) i).card ≤
      targetIntersectionCount R L i + hallucinationCount S L t := by
  classical
  let inside :=
    (targetPrefix R i).filter fun x => x ∈ L
  let outside :=
    (sequencePrefix S t).filter fun x => x ∉ L
  have hsubset :
      prefixWiseElements S R (fun _ => t) i ⊆ inside ∪ outside := by
    intro x hx
    have hx' :
        x ∈ targetPrefix R i ∩ sequencePrefix S t := by
      simpa [prefixWiseElements] using hx
    rcases Finset.mem_inter.mp hx' with ⟨hxR, hxS⟩
    by_cases hxL : x ∈ L
    · exact Finset.mem_union_left _
        (by simpa [inside] using ⟨hxR, hxL⟩)
    · exact Finset.mem_union_right _
        (by simpa [outside] using ⟨hxS, hxL⟩)
  calc
    (prefixWiseElements S R (fun _ => t) i).card
        ≤ (inside ∪ outside).card :=
      Finset.card_le_card hsubset
    _ ≤ inside.card + outside.card :=
      Finset.card_union_le _ _
    _ = targetIntersectionCount R L i +
          hallucinationCount S L t := by
      rfl

/-- Eventual consistency gives a uniform finite bound on the number of
distinct hallucinated outputs.  This is the deterministic implication used
to derive Theorem 1 from the Hallucination Barrier. -/
theorem hallucinationCount_le_burnIn
    (S : ℕ → α) (L : Set α) {T t : ℕ}
    (hvalid : ∀ k, T ≤ k → S k ∈ L) :
    hallucinationCount S L t ≤ T := by
  classical
  have hsubset :
      (sequencePrefix S t).filter (fun x => x ∉ L) ⊆
        sequencePrefix S T := by
    intro x hx
    have hxparts := Finset.mem_filter.mp hx
    obtain ⟨k, hkt, hkx⟩ :=
      (mem_sequencePrefix_iff S x t).mp hxparts.1
    have hkT : k < T := by
      by_contra hnot
      exact hxparts.2 (hkx ▸ hvalid k (Nat.le_of_not_gt hnot))
    exact (mem_sequencePrefix_iff S x T).mpr ⟨k, hkT, hkx⟩
  calc
    hallucinationCount S L t
        ≤ (sequencePrefix S T).card := by
      exact Finset.card_le_card hsubset
    _ ≤ T := by
      unfold sequencePrefix
      simpa only [Finset.card_range] using
        (Finset.card_image_le (s := Finset.range T) (f := S))

/-- Appendix-C's pathwise inequality specialized to an eventually
consistent output sequence. -/
theorem prefix_credit_le_target_intersection_add_burnIn
    (S R : ℕ → α) (L : Set α) {T i t : ℕ}
    (hvalid : ∀ k, T ≤ k → S k ∈ L) :
    (prefixWiseElements S R (fun _ => t) i).card ≤
      targetIntersectionCount R L i + T := by
  exact
    (prefix_credit_le_target_intersection_add_hallucinations
      S R L i t).trans
      (Nat.add_le_add_left
        (hallucinationCount_le_burnIn S L hvalid) _)

end GenLimit.TimeSensitive

end

-- GenLimit.Paper30_TimeSensitiveLanguageGeneration.GreedyUpperDensity
section
set_option autoImplicit true

/-!
# Greedy upper-density core

Source: Ganju--McVoy--Dughmi--Teng, arXiv:2605.11302v2,
Section 4 and Appendix E, Algorithm 2 and Theorem 12.

The source's `GCG` proof repeatedly uses one deterministic fact: after a
finite burn-in, if the adversary can consume at most one still-available
string between generator moves, the greedy generator receives at least half
of the remaining finite prefix.  We formalize that ownership argument and
the exact threshold schedule `α_m = 1/2 - 2^{-m}`.

This is the finite combinatorial core used by the repaired stateful machine in
`TotalizedGCGProgress`.  The external optimality direction is separated in
`TurnTakingUpperBound`.
-/

namespace GenLimit.TimeSensitive

/-- Algorithm 2's stage threshold `α_m = 1/2 - 2^{-m}`. -/
noncomputable def gcgThreshold (m : ℕ) : ℝ :=
  (1 / 2 : ℝ) - (1 / 2 : ℝ) ^ m

theorem gcgThreshold_eq (m : ℕ) :
    gcgThreshold m = (1 / 2 : ℝ) - 1 / (2 : ℝ) ^ m := by
  simp [gcgThreshold, one_div, inv_pow]

theorem gcgThreshold_lt_half (m : ℕ) :
    gcgThreshold m < (1 / 2 : ℝ) := by
  unfold gcgThreshold
  have hpos : 0 < (1 / 2 : ℝ) ^ m := pow_pos (by norm_num) _
  linarith

theorem gcgThreshold_monotone : Monotone gcgThreshold := by
  intro m n hmn
  have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
  unfold gcgThreshold
  linarith

theorem tendsto_gcgThreshold :
    Filter.Tendsto gcgThreshold Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hpow :
      Filter.Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  change Filter.Tendsto
    (fun m : ℕ => (1 / 2 : ℝ) - (1 / 2 : ℝ) ^ m)
    Filter.atTop (nhds (1 / 2 : ℝ))
  simpa only [sub_zero] using tendsto_const_nhds.sub hpow

/-- The alternating-ownership inequality used in all three cases of the
Appendix-E proof.  `available` is partitioned between the generator and
adversary, and the adversary is never more than one move ahead. -/
theorem greedy_alternation_half
    [DecidableEq α]
    {available generated adversary : Finset α}
    (hdisjoint : Disjoint generated adversary)
    (hcover : generated ∪ adversary = available)
    (hahead : adversary.card ≤ generated.card + 1) :
    available.card / 2 ≤ generated.card := by
  have hcard :
      available.card = generated.card + adversary.card := by
    rw [← hcover, Finset.card_union_of_disjoint hdisjoint]
  omega

/-- Burn-in version of the same bound.

At most `2T` strings in the first `i` target positions can already be
unavailable at entry time `T` (late strings plus adversary-claimed strings).
The greedy alternation therefore credits at least
`⌊(i - 2T)/2⌋` strings, exactly the finite estimate printed in Appendix E. -/
theorem greedy_after_burnIn_bound
    [DecidableEq α]
    {prefixSet unavailable available generated adversary : Finset α}
    {i T : ℕ}
    (hprefix : prefixSet.card = i)
    (hpartition₁ : Disjoint unavailable available)
    (hcover₁ : unavailable ∪ available = prefixSet)
    (hunavailable : unavailable.card ≤ 2 * T)
    (hpartition₂ : Disjoint generated adversary)
    (hcover₂ : generated ∪ adversary = available)
    (hahead : adversary.card ≤ generated.card + 1) :
    (i - 2 * T) / 2 ≤ generated.card := by
  have havailable :
      i ≤ unavailable.card + available.card := by
    rw [← hprefix, ← hcover₁,
      Finset.card_union_of_disjoint hpartition₁]
  have hhalf :
      available.card / 2 ≤ generated.card :=
    greedy_alternation_half hpartition₂ hcover₂ hahead
  omega

/-- If the same stage continues indefinitely, any threshold below one half
is crossed once the printed finite greedy bound crosses it.  This packages
the last implication in the stage-termination argument without introducing
the unformalized `GCG` state machine. -/
theorem stage_crosses_threshold_of_greedy_bound
    {m i T credited : ℕ}
    (hgreedy : (i - 2 * T) / 2 ≤ credited)
    (hlarge :
      gcgThreshold m ≤
        (((i - 2 * T) / 2 : ℕ) : ℝ) / i) :
    gcgThreshold m ≤ (credited : ℝ) / i := by
  have hiReal : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  exact hlarge.trans
    (div_le_div_of_nonneg_right (by exact_mod_cast hgreedy) hiReal)

end GenLimit.TimeSensitive

end

-- GenLimit.Paper30_TimeSensitiveLanguageGeneration.TotalizedGCGMachine
section
set_option autoImplicit true

/-!
# A totalized GCG queue

The printed Algorithm 2 queues only strict-superset transitions.  Its proof
later treats every queued language as eventually target-valid, although the
`Accurate` contract provides validity only after an unknown finite time.  An
early non-target queue entry can therefore be the final entry and make the
printed machine inconsistent forever.

This module records the minimal semantic repair used for the existential
Theorem 4: queue every `Accurate` guess.  Stage `m` uses the guess from round
`m + 1`.  Every stage still employs the paper's literal `OnTimeUnused` rule
and advances only after crossing its prescribed density threshold.  Since
the queue is cofinal, finite early guesses are eventually left behind and
the P07 `Accurate` guarantees apply without any oracle for the unknown
validity time.
-/

namespace GenLimit.TimeSensitive

open GenLimit.KleinbergWei

structure TotalizedGCGState where
  stage : ℕ
  outputs : List ℕ

def TotalizedGCGState.initial : TotalizedGCGState :=
  ⟨0, []⟩

/-- Candidate used in round `t`; the time argument is retained to make the
causal interface explicit. -/
noncomputable def totalizedRoundActive
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    (_t : ℕ) (old : TotalizedGCGState) : ℕ :=
  F.guess stream (old.stage + 1)

noncomputable def totalizedRoundOutput
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    (t : ℕ) (old : TotalizedGCGState) : ℕ :=
  greedyRoundOutput (F.order (totalizedRoundActive F stream t old))
    stream t old.outputs

/-- One round of the repaired queue.  At round `t`, stage `m` has a next
queued guess exactly when `m < t`. -/
noncomputable def totalizedGCGStep
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    (t : ℕ) (old : TotalizedGCGState) : TotalizedGCGState := by
  classical
  let active := totalizedRoundActive F stream t old
  let output := totalizedRoundOutput F stream t old
  let outputs := old.outputs ++ [output]
  let crossed :=
    gcgThreshold (old.stage + 1) ≤
      timelyDensity (outputHistoryStream outputs)
        (F.order active).enumeration id (t + 1)
  exact
    { stage := if old.stage < t ∧ crossed then old.stage + 1 else old.stage
      outputs := outputs }

noncomputable def totalizedGCGRun
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) :
    ℕ → TotalizedGCGState
  | 0 => TotalizedGCGState.initial
  | t + 1 => totalizedGCGStep F stream t (totalizedGCGRun F stream t)

noncomputable def totalizedGCGOutput
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  totalizedRoundOutput F stream t (totalizedGCGRun F stream t)

@[simp] theorem totalizedGCGRun_zero
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) :
    totalizedGCGRun F stream 0 = TotalizedGCGState.initial := rfl

@[simp] theorem totalizedGCGRun_succ
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    totalizedGCGRun F stream (t + 1) =
      totalizedGCGStep F stream t (totalizedGCGRun F stream t) := rfl

theorem totalizedGCGRun_outputs_succ
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (totalizedGCGRun F stream (t + 1)).outputs =
      (totalizedGCGRun F stream t).outputs ++
        [totalizedGCGOutput F stream t] := by
  rfl

theorem totalizedGCGRun_outputs_length
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (totalizedGCGRun F stream t).outputs.length = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [totalizedGCGRun_outputs_succ, List.length_append, ih]
      simp

theorem totalizedGCGRun_outputs_eq
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (totalizedGCGRun F stream t).outputs =
      (List.range t).map (totalizedGCGOutput F stream) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [totalizedGCGRun_outputs_succ, ih]
      simp [List.range_succ]

theorem totalizedGCGRun_outputs_toFinset
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (totalizedGCGRun F stream t).outputs.toFinset =
      sequencePrefix (totalizedGCGOutput F stream) t := by
  classical
  ext x
  simp [totalizedGCGRun_outputs_eq, sequencePrefix]

theorem totalizedGCGOutput_not_mem_observed
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    totalizedGCGOutput F stream t ∉ sample stream (t + 1) := by
  intro h
  exact onTimeUnused_fresh _ _ _ (Finset.mem_union_left _ h)

theorem totalizedGCGOutput_not_mem_prior
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    totalizedGCGOutput F stream t ∉
      sequencePrefix (totalizedGCGOutput F stream) t := by
  rw [← totalizedGCGRun_outputs_toFinset]
  intro h
  exact onTimeUnused_fresh _ _ _ (Finset.mem_union_right _ h)

theorem totalizedGCG_freshPlay
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) :
    FreshPlay stream (totalizedGCGOutput F stream) := by
  constructor
  · intro t s hst heq
    apply totalizedGCGOutput_not_mem_observed F stream t
    rw [mem_sample_iff]
    exact ⟨s, by omega, heq⟩
  · intro t s hst heq
    apply totalizedGCGOutput_not_mem_prior F stream t
    rw [mem_sequencePrefix_iff]
    exact ⟨s, hst, heq⟩

theorem totalizedGCGOutput_mem_active
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    totalizedGCGOutput F stream t ∈
      F.language
        (F.guess stream ((totalizedGCGRun F stream t).stage + 1)) := by
  rw [← F.carrier_eq]
  exact onTimeUnused_mem _ _ _

theorem totalizedGCGRun_stage_mono_step
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (totalizedGCGRun F stream t).stage ≤
      (totalizedGCGRun F stream (t + 1)).stage := by
  simp only [totalizedGCGRun_succ, totalizedGCGStep]
  split <;> omega

theorem totalizedGCGRun_stage_le_time
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (totalizedGCGRun F stream t).stage ≤ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [totalizedGCGRun_succ, totalizedGCGStep]
      split <;> omega

theorem totalizedGCGRun_stage_mono
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) :
    Monotone fun t => (totalizedGCGRun F stream t).stage := by
  exact monotone_nat_of_le_succ
    (totalizedGCGRun_stage_mono_step F stream)

end GenLimit.TimeSensitive

end

-- GenLimit.Paper30_TimeSensitiveLanguageGeneration.OnlineTotalizedGCG
section
set_option autoImplicit true

/-!
# Finite-history realization of the repaired GCG

`TotalizedGCGMachine` is conveniently stated against a completed infinite
stream.  This module exposes the same round operation using only the finite
history visible after the adversary's current announcement.  The visible
history is extended by repeating its last value, and prefix causality of the
P07 selector proves that this arbitrary completion cannot affect the round.

The resulting state can be placed inside a joint adversary/generator
recursion without a circular infinite-stream definition.
-/

namespace GenLimit.TimeSensitive

/-- State of the finite-history repaired GCG immediately before a round. -/
structure OnlineTotalizedGCGState where
  stage : ℕ
  observations : List ℕ
  outputs : List ℕ

def OnlineTotalizedGCGState.initial : OnlineTotalizedGCGState :=
  ⟨0, [], []⟩

def OnlineTotalizedGCGState.base
    (state : OnlineTotalizedGCGState) : TotalizedGCGState :=
  ⟨state.stage, state.outputs⟩

/-- Any total completion of the observations through the current round.
Only its visible prefix is semantically used. -/
def onlineVisibleStream
    (state : OnlineTotalizedGCGState) (current : ℕ) : ℕ → ℕ :=
  GenLimit.Generic.historyThenFallback
    (state.observations ++ [current]) current

noncomputable def onlineTotalizedRoundOutput
    (F : CanonicallyOrderedFamily) (t : ℕ)
    (state : OnlineTotalizedGCGState) (current : ℕ) : ℕ :=
  totalizedRoundOutput F (onlineVisibleStream state current) t state.base

noncomputable def onlineTotalizedGCGStep
    (F : CanonicallyOrderedFamily) (t : ℕ)
    (state : OnlineTotalizedGCGState) (current : ℕ) :
    OnlineTotalizedGCGState :=
  let next := totalizedGCGStep F (onlineVisibleStream state current) t state.base
  { stage := next.stage
    observations := state.observations ++ [current]
    outputs := next.outputs }

noncomputable def onlineTotalizedGCGRun
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) :
    ℕ → OnlineTotalizedGCGState
  | 0 => OnlineTotalizedGCGState.initial
  | t + 1 => onlineTotalizedGCGStep F t
      (onlineTotalizedGCGRun F stream t) (stream t)

noncomputable def onlineTotalizedGCGOutput
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  onlineTotalizedRoundOutput F t
    (onlineTotalizedGCGRun F stream t) (stream t)

@[simp] theorem onlineTotalizedGCGRun_zero
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) :
    onlineTotalizedGCGRun F stream 0 = OnlineTotalizedGCGState.initial := rfl

@[simp] theorem onlineTotalizedGCGRun_succ
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    onlineTotalizedGCGRun F stream (t + 1) =
      onlineTotalizedGCGStep F t
        (onlineTotalizedGCGRun F stream t) (stream t) := rfl

theorem onlineTotalizedGCGRun_observations_eq
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (onlineTotalizedGCGRun F stream t).observations =
      (List.range t).map stream := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [onlineTotalizedGCGRun_succ]
      simp only [onlineTotalizedGCGStep, ih]
      simp [List.range_succ]

theorem onlineTotalizedGCGRun_outputs_length
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (onlineTotalizedGCGRun F stream t).outputs.length = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [onlineTotalizedGCGRun_succ]
      simp only [onlineTotalizedGCGStep, totalizedGCGStep,
        OnlineTotalizedGCGState.base]
      simp [ih]

theorem onlineVisibleStream_run_eq
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ)
    (t n : ℕ) (hn : n < t + 1) :
    onlineVisibleStream (onlineTotalizedGCGRun F stream t) (stream t) n =
      stream n := by
  rw [onlineVisibleStream,
    onlineTotalizedGCGRun_observations_eq]
  simp only [GenLimit.Generic.historyThenFallback]
  have hlength :
      ((List.range t).map stream ++ [stream t]).length = t + 1 := by simp
  rw [dif_pos (by simpa [hlength] using hn)]
  by_cases hnt : n < t
  · simp [List.get_eq_getElem, hnt]
  · have hntEq : n = t := by omega
    subst n
    simp [List.get_eq_getElem]

theorem totalizedRoundActive_eq_of_eqOn_prefix
    (F : CanonicallyOrderedFamily)
    {stream₁ stream₂ : ℕ → ℕ} {t : ℕ} {state : TotalizedGCGState}
    (hstage : state.stage ≤ t)
    (hstream : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    totalizedRoundActive F stream₁ t state =
      totalizedRoundActive F stream₂ t state := by
  unfold totalizedRoundActive CanonicallyOrderedFamily.guess
  apply guessIndex_eq_of_eqOn_prefix
  intro n hn
  apply hstream n
  omega

theorem totalizedRoundOutput_eq_of_eqOn_prefix
    (F : CanonicallyOrderedFamily)
    {stream₁ stream₂ : ℕ → ℕ} {t : ℕ} {state : TotalizedGCGState}
    (hstage : state.stage ≤ t)
    (hstream : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    totalizedRoundOutput F stream₁ t state =
      totalizedRoundOutput F stream₂ t state := by
  unfold totalizedRoundOutput greedyRoundOutput greedyUsed
  rw [totalizedRoundActive_eq_of_eqOn_prefix F hstage hstream]
  rw [sample_eq_of_eq_on_prefix hstream]

theorem totalizedGCGStep_eq_of_eqOn_prefix
    (F : CanonicallyOrderedFamily)
    {stream₁ stream₂ : ℕ → ℕ} {t : ℕ} {state : TotalizedGCGState}
    (hstage : state.stage ≤ t)
    (hstream : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    totalizedGCGStep F stream₁ t state =
      totalizedGCGStep F stream₂ t state := by
  classical
  unfold totalizedGCGStep
  rw [totalizedRoundActive_eq_of_eqOn_prefix F hstage hstream]
  rw [totalizedRoundOutput_eq_of_eqOn_prefix F hstage hstream]

/-- The finite-history machine is extensionally the original repaired GCG
on every completed stream. -/
theorem onlineTotalizedGCGRun_base_eq
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    (onlineTotalizedGCGRun F stream t).base =
      totalizedGCGRun F stream t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [onlineTotalizedGCGRun_succ, totalizedGCGRun_succ]
      simp only [onlineTotalizedGCGStep, OnlineTotalizedGCGState.base]
      change
        totalizedGCGStep F
            (onlineVisibleStream (onlineTotalizedGCGRun F stream t) (stream t))
            t (onlineTotalizedGCGRun F stream t).base =
          totalizedGCGStep F stream t (totalizedGCGRun F stream t)
      rw [show
        totalizedGCGStep F
            (onlineVisibleStream (onlineTotalizedGCGRun F stream t) (stream t))
            t (onlineTotalizedGCGRun F stream t).base =
          totalizedGCGStep F stream t
            (onlineTotalizedGCGRun F stream t).base by
        apply totalizedGCGStep_eq_of_eqOn_prefix F
        · rw [ih]
          exact totalizedGCGRun_stage_le_time F stream t
        · exact onlineVisibleStream_run_eq F stream t]
      rw [ih]

theorem onlineTotalizedGCGOutput_eq
    (F : CanonicallyOrderedFamily) (stream : ℕ → ℕ) (t : ℕ) :
    onlineTotalizedGCGOutput F stream t =
      totalizedGCGOutput F stream t := by
  unfold onlineTotalizedGCGOutput onlineTotalizedRoundOutput
  rw [totalizedRoundOutput_eq_of_eqOn_prefix F
    (by rw [onlineTotalizedGCGRun_base_eq]
        exact totalizedGCGRun_stage_le_time F stream t)
    (onlineVisibleStream_run_eq F stream t)]
  rw [onlineTotalizedGCGRun_base_eq]
  rfl

end GenLimit.TimeSensitive

end

-- GenLimit.Paper30_TimeSensitiveLanguageGeneration.GreedyAsymptotics
section
set_option autoImplicit true

/-!
# Greedy half-density asymptotics

Source: Ganju--McVoy--Dughmi--Teng, arXiv:2605.11302v2,
Section 4 and Appendix E, Algorithm 2 and Theorem 12.

`GreedyUpperDensity` proves the finite ownership estimate printed in
Appendix E.  This file closes its elementary asymptotic endgame: for every
fixed burn-in time `T`, the ratio

`⌊(i - 2T) / 2⌋ / i`

converges to one half.  Consequently every stage threshold
`αₘ = 1/2 - 2⁻ᵐ` is eventually crossed whenever the finite ownership bound
continues to hold.

This is a deterministic statement about a sequence of credited-cardinality
bounds.  `TotalizedGCGProgress` connects it to the repaired stateful machine;
the separate optimality direction is in `TurnTakingUpperBound`.
-/

namespace GenLimit.TimeSensitive

open Filter

/-- The normalized finite lower bound from Appendix E after burn-in `T`. -/
noncomputable def greedyBurnInRatio (T i : ℕ) : ℝ :=
  ((((i - 2 * T) / 2 : ℕ) : ℝ) / i)

theorem greedyBurnInRatio_nonneg (T i : ℕ) :
    0 ≤ greedyBurnInRatio T i := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The finite greedy lower-bound ratio never exceeds one half. -/
theorem greedyBurnInRatio_le_half (T i : ℕ) :
    greedyBurnInRatio T i ≤ (1 / 2 : ℝ) := by
  by_cases hi : i = 0
  · simp [greedyBurnInRatio, hi]
  · have hiReal : (0 : ℝ) < i := by
      exact_mod_cast Nat.pos_of_ne_zero hi
    rw [greedyBurnInRatio, div_le_iff₀ hiReal]
    have hNat : 2 * ((i - 2 * T) / 2) ≤ i := by
      omega
    have hReal :
        (2 : ℝ) * (((i - 2 * T) / 2 : ℕ) : ℝ) ≤ i := by
      exact_mod_cast hNat
    linarith

/-- The gap from one half is at most the fixed burn-in error `(T+1)/i`. -/
theorem half_sub_greedyBurnInRatio_le
    (T : ℕ) {i : ℕ} (hi : 0 < i) :
    (1 / 2 : ℝ) - greedyBurnInRatio T i ≤
      ((T + 1 : ℕ) : ℝ) / i := by
  have hiReal : (0 : ℝ) < i := by
    exact_mod_cast hi
  rw [greedyBurnInRatio, sub_le_iff_le_add, ← add_div,
    le_div_iff₀ hiReal]
  have hNat :
      i ≤ 2 * ((i - 2 * T) / 2) + 2 * (T + 1) := by
    omega
  have hReal :
      (i : ℝ) ≤
        2 * (((i - 2 * T) / 2 : ℕ) : ℝ) +
          2 * ((T + 1 : ℕ) : ℝ) := by
    exact_mod_cast hNat
  linarith

/-- For fixed burn-in, Appendix E's exact finite greedy ratio converges to
one half. -/
theorem tendsto_greedyBurnInRatio (T : ℕ) :
    Tendsto (greedyBurnInRatio T) atTop (nhds (1 / 2 : ℝ)) := by
  have herror :
      Tendsto
        (fun i : ℕ => (1 / 2 : ℝ) - greedyBurnInRatio T i)
        atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun i =>
        sub_nonneg.mpr (greedyBurnInRatio_le_half T i)
    · filter_upwards [eventually_gt_atTop 0] with i hi
      exact half_sub_greedyBurnInRatio_le T hi
    · simpa using
        tendsto_const_div_atTop_nhds_zero_nat
          (((T + 1 : ℕ) : ℝ))
  have hreconstruct :
      Tendsto
        (fun i : ℕ =>
          (1 / 2 : ℝ) -
            ((1 / 2 : ℝ) - greedyBurnInRatio T i))
        atTop (nhds (1 / 2 : ℝ)) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 / 2 : ℝ))
          atTop (nhds (1 / 2 : ℝ))).sub herror
  exact hreconstruct.congr'
    (Filter.Eventually.of_forall fun i => by ring)

/-- Every Algorithm-2 threshold is eventually below the finite greedy
lower-bound ratio. -/
theorem eventually_gcgThreshold_le_greedyBurnInRatio
    (m T : ℕ) :
    ∀ᶠ i in atTop, gcgThreshold m ≤ greedyBurnInRatio T i := by
  filter_upwards [
    (tendsto_greedyBurnInRatio T).eventually
      (lt_mem_nhds (gcgThreshold_lt_half m))] with i hi
  exact hi.le

/-- Deterministic stage-termination endgame from Appendix E.

If a continuing stage satisfies the printed greedy cardinality bound
eventually, then its credited ratio eventually reaches the stage threshold.
The connection to the concrete repaired state machine is proved in
`TotalizedGCGProgress`; no runtime-complexity claim is made here. -/
theorem stage_eventually_crosses_threshold
    (m T : ℕ) (credited : ℕ → ℕ)
    (hgreedy :
      ∀ᶠ i in atTop, (i - 2 * T) / 2 ≤ credited i) :
    ∀ᶠ i in atTop,
      gcgThreshold m ≤ (credited i : ℝ) / i := by
  filter_upwards [
    hgreedy,
    eventually_gcgThreshold_le_greedyBurnInRatio m T] with i hbound hratio
  exact stage_crosses_threshold_of_greedy_bound hbound hratio

end GenLimit.TimeSensitive

end

-- GenLimit.Paper30_TimeSensitiveLanguageGeneration.TheoremFour
section
set_option autoImplicit true

/-!
# Theorem 4: checkpoint-to-upper-density endgame

Source: Ganju--McVoy--Dughmi--Teng, arXiv:2605.11302v2,
Section 4 and Appendix E, Theorems 4 and 12.

The paper's GCG argument produces arbitrarily late checkpoints whose timely
density reaches the stage threshold `αₘ = 1/2 - 2⁻ᵐ`.  The theorem below
closes the remaining `limsup` argument: cofinal checkpoints for every stage
imply timely upper density at least one half.

This is the reusable analytic endpoint.  `TotalizedGCGMain` now discharges
the checkpoint premise for the documented repaired queue; the source-faithful
strict-rise skeleton retains a separately recorded consistency gap.
-/

namespace GenLimit.TimeSensitive

open Filter

/-- A cofinal family of GCG threshold checkpoints gives timely upper density
at least one half under the identity deadline.

This packages the final analytic implication in Theorems 4/12 without hiding
the state-machine invariant in an existential wrapper. -/
theorem theorem_4_density_endgame
    (S R : ℕ → α)
    (hcheckpoints : ∀ m : ℕ,
      ∃ᶠ i : ℕ in atTop,
        gcgThreshold m ≤ timelyDensity S R id i) :
    (1 / 2 : ℝ) ≤ upperTimelyDensity S R id := by
  have hbounded :
      IsBoundedUnder LE.le atTop (timelyDensity S R id) :=
    isBoundedUnder_of
      ⟨1, fun i => timelyDensity_le_one S R id i⟩
  have hstage : ∀ m : ℕ,
      gcgThreshold m ≤ upperTimelyDensity S R id := by
    intro m
    unfold upperTimelyDensity
    exact le_limsup_of_frequently_le (hcheckpoints m) hbounded
  apply le_of_tendsto tendsto_gcgThreshold
  exact Eventually.of_forall hstage

/-- Equivalent explicit-cofinality interface for the same endgame.  This is
often the most convenient form for a concrete GCG run: after any requested
time `N`, provide a later checkpoint for stage `m`. -/
theorem theorem_4_density_endgame_of_cofinal_checkpoints
    (S R : ℕ → α)
    (hcheckpoints : ∀ m N : ℕ, ∃ i : ℕ,
      N ≤ i ∧ gcgThreshold m ≤ timelyDensity S R id i) :
    (1 / 2 : ℝ) ≤ upperTimelyDensity S R id := by
  apply theorem_4_density_endgame S R
  intro m
  rw [frequently_atTop]
  intro N
  exact hcheckpoints m N

end GenLimit.TimeSensitive

end

-- GenLimit.Support.TurnTaking.Pairing
section
set_option autoImplicit true

/-!
# Finite turn-taking pairing

This module isolates the paper-independent combinatorial core of the
Kleinberg--Wei turn-taking argument.  Ordinary credited elements have
injective, disjoint partners in the same finite prefix; a separate exceptional
set accounts for sparse catch-up rounds.
-/

namespace GenLimit.TurnTaking

/-- If every ordinary credit has a distinct non-credit partner in the same
prefix and there are at most `e` exceptional credits, then credits occupy at
most half the prefix up to the exceptional budget. -/
theorem finite_upper_bound
    [DecidableEq α]
    {prefixSet credited paired exceptions : Finset α}
    (partner : α → α) {i e : ℕ}
    (hprefix : prefixSet.card = i)
    (hcreditedPrefix : credited ⊆ prefixSet)
    (hcreditCover : credited ⊆ paired ∪ exceptions)
    (hpairedCredit : paired ⊆ credited)
    (hexceptions : exceptions.card ≤ e)
    (hpartnerPrefix : ∀ x ∈ paired, partner x ∈ prefixSet)
    (hpartnerOutside : ∀ x ∈ paired, partner x ∉ credited)
    (hpartnerInj : Set.InjOn partner paired) :
    2 * credited.card ≤ i + 2 * e := by
  let partners := paired.image partner
  have hpartnersCard : partners.card = paired.card := by
    apply Finset.card_image_iff.mpr
    intro x hx y hy hxy
    exact hpartnerInj hx hy hxy
  have hdisjoint : Disjoint paired partners := by
    rw [Finset.disjoint_left]
    intro x hxPaired hxPartner
    obtain ⟨y, hyPaired, hyx⟩ := Finset.mem_image.mp hxPartner
    have hxCredit : x ∈ credited := hpairedCredit hxPaired
    exact hpartnerOutside y hyPaired (hyx ▸ hxCredit)
  have hunionSubset : paired ∪ partners ⊆ prefixSet := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxPaired | hxPartner
    · exact hcreditedPrefix (hpairedCredit hxPaired)
    · obtain ⟨y, hyPaired, hyx⟩ := Finset.mem_image.mp hxPartner
      exact hyx ▸ hpartnerPrefix y hyPaired
  have hpairedTwice : 2 * paired.card ≤ i := by
    have hcard := Finset.card_le_card hunionSubset
    rw [Finset.card_union_of_disjoint hdisjoint, hpartnersCard,
      hprefix] at hcard
    omega
  have hcreditCard : credited.card ≤ paired.card + exceptions.card := by
    exact (Finset.card_le_card hcreditCover).trans (Finset.card_union_le _ _)
  omega

end GenLimit.TurnTaking

end

-- GenLimit.Paper30_TimeSensitiveLanguageGeneration.TurnTakingUpperBound
section
set_option autoImplicit true

/-!
# Kleinberg--Wei turn-taking upper bound

The paper-independent finite pairing theorem now lives in
`GenLimit.Support.TurnTaking.Pairing`; this module preserves its P30-facing
name and supplies the timely-density analytic specialization behind the
optimality sentence cited by P30.  A timely generator-owned prefix is split
into ordinary credits and sparse catch-up exceptions.  Every ordinary credit
has an injective, disjoint adversary-owned partner in the same target prefix.
Consequently at most half the prefix, up to the sparse exception budget, can
be timely generator credit.

The theorem is deliberately phrased as a reusable certificate.  P30's
concrete finite-history instantiation and adaptive exact presentation are in
`OnlineTotalizedGCG`, `AdaptivePresentationExact`, and `AdaptiveUpperBound`.
P39 itself did not formalize that adversary construction.
-/

namespace GenLimit.TimeSensitive

open Filter

/-- Compatibility alias for the shared finite turn-taking pairing theorem. -/
alias turnTaking_finite_upper_bound :=
  GenLimit.TurnTaking.finite_upper_bound

/-- The normalized catch-up budget used by the asymptotic upper bound. -/
noncomputable def catchupRatio (exceptions : ℕ → ℕ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else (exceptions i : ℝ) / i

theorem catchupRatio_nonneg (exceptions : ℕ → ℕ) (i : ℕ) :
    0 ≤ catchupRatio exceptions i := by
  unfold catchupRatio
  split <;> positivity

/-- Analytic Kleinberg--Wei upper endpoint: an eventual finite pairing bound
with a vanishing catch-up fraction forces upper timely density at most one
half. -/
theorem upperTimelyDensity_le_half_of_turnTaking
    (S R : ℕ → α) (exceptions : ℕ → ℕ)
    (hfinite : ∀ᶠ i in atTop,
      2 * (timelyElements S R id i).card ≤ i + 2 * exceptions i)
    (hvanishing : Tendsto (catchupRatio exceptions) atTop (nhds 0)) :
    upperTimelyDensity S R id ≤ (1 / 2 : ℝ) := by
  let upper : ℕ → ℝ := fun i =>
    (1 / 2 : ℝ) + catchupRatio exceptions i
  have hupperTendsto : Tendsto upper atTop (nhds (1 / 2 : ℝ)) := by
    simpa [upper] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ))
        atTop (nhds (1 / 2 : ℝ))).add hvanishing
  have hcompare : ∀ᶠ i in atTop,
      timelyDensity S R id i ≤ upper i := by
    filter_upwards [hfinite, eventually_gt_atTop 0] with i hi hiPos
    have hiReal : (0 : ℝ) < i := by exact_mod_cast hiPos
    have hiCast :
        (2 : ℝ) * ((timelyElements S R id i).card : ℝ) ≤
          (i : ℝ) + 2 * (exceptions i : ℝ) := by
      exact_mod_cast hi
    simp only [timelyDensity, Nat.ne_of_gt hiPos, if_false,
      upper, catchupRatio]
    rw [div_le_iff₀ hiReal]
    field_simp
    nlinarith
  unfold upperTimelyDensity
  have hlimsup :
      limsup (timelyDensity S R id) atTop ≤ limsup upper atTop := by
    exact limsup_le_limsup hcompare
      (isCoboundedUnder_le_of_le atTop
        (fun i => timelyDensity_nonneg S R id i))
      hupperTendsto.isBoundedUnder_le
  exact hlimsup.trans_eq hupperTendsto.limsup_eq

end GenLimit.TimeSensitive

end

-- GenLimit.Paper30_TimeSensitiveLanguageGeneration.AdaptivePresentation
section
set_option autoImplicit true

/-!
# Sparse adaptive presentation for the half-density upper bound

This module implements the Kleinberg--Wei turn-taking adversary needed by
P30 Theorem 4.  Ordinary rounds announce the least target-ranked point not
previously used by either player.  At the sparse rounds `2^(n+1)`, the
adversary catches up with target-valued generator output number `n`.

The catch-up schedule makes the resulting stream an exact presentation while
using only logarithmically many exceptional rounds in each prefix.  The joint
run is defined from the finite-history GCG step, so the adversary never reads
the current or future generator output.
-/

namespace GenLimit.TimeSensitive

open Filter
open GenLimit.KleinbergWei

/-- The finite set already owned by either player before the next round. -/
def adaptiveUsed (state : OnlineTotalizedGCGState) : Finset ℕ :=
  state.observations.toFinset ∪ state.outputs.toFinset

def UnusedTargetRank
    (O : OrderedLanguage) (used : Finset ℕ) (r : ℕ) : Prop :=
  O.enumeration r ∉ used

theorem exists_unusedTargetRank
    (O : OrderedLanguage) (used : Finset ℕ) :
    ∃ r, UnusedTargetRank O used r := by
  classical
  by_contra h
  push_neg at h
  have hsubset :
      (Finset.range (used.card + 1)).image O.enumeration ⊆ used := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    exact not_not.mp (h r)
  have hcard :
      ((Finset.range (used.card + 1)).image O.enumeration).card =
        used.card + 1 := by
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro a _ b _ hab
      exact O.enumeration_injective hab
  have := Finset.card_le_card hsubset
  rw [hcard] at this
  omega

/-- Least target rank not yet used by either player. -/
noncomputable def leastUnusedTargetRank
    (O : OrderedLanguage) (used : Finset ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_unusedTargetRank O used)

noncomputable def leastUnusedTarget
    (O : OrderedLanguage) (used : Finset ℕ) : ℕ :=
  O.enumeration (leastUnusedTargetRank O used)

theorem leastUnusedTargetRank_spec
    (O : OrderedLanguage) (used : Finset ℕ) :
    UnusedTargetRank O used (leastUnusedTargetRank O used) := by
  classical
  exact Nat.find_spec (exists_unusedTargetRank O used)

theorem leastUnusedTargetRank_min
    (O : OrderedLanguage) (used : Finset ℕ) {r : ℕ}
    (hr : UnusedTargetRank O used r) :
    leastUnusedTargetRank O used ≤ r := by
  classical
  exact Nat.find_min' (exists_unusedTargetRank O used) hr

theorem leastUnusedTarget_mem
    (O : OrderedLanguage) (used : Finset ℕ) :
    leastUnusedTarget O used ∈ O.carrier := by
  rw [← O.range_enumeration]
  exact ⟨leastUnusedTargetRank O used, rfl⟩

theorem leastUnusedTarget_fresh
    (O : OrderedLanguage) (used : Finset ℕ) :
    leastUnusedTarget O used ∉ used :=
  leastUnusedTargetRank_spec O used

/-- Round `2^(n+1)` is reserved for catching up output number `n`. -/
def IsCatchupRound (t : ℕ) : Prop :=
  ∃ n, t = 2 ^ (n + 1)

noncomputable instance (t : ℕ) : Decidable (IsCatchupRound t) :=
  Classical.propDecidable _

noncomputable def catchupIndex (t : ℕ) : ℕ :=
  if h : IsCatchupRound t then Nat.find h else 0

theorem catchupIndex_spec {t : ℕ} (h : IsCatchupRound t) :
    t = 2 ^ (catchupIndex t + 1) := by
  simp only [catchupIndex, dif_pos h]
  exact Nat.find_spec h

theorem catchupIndex_scheduled (n : ℕ) :
    catchupIndex (2 ^ (n + 1)) = n := by
  have hcatch : IsCatchupRound (2 ^ (n + 1)) := ⟨n, rfl⟩
  have hspec := catchupIndex_spec hcatch
  apply Nat.succ.inj
  apply Nat.pow_right_injective (a := 2) (by omega)
  simpa using hspec.symm

theorem index_lt_scheduled_time (n : ℕ) :
    n < 2 ^ (n + 1) := by
  exact n.lt_two_pow_self.trans_le
    (Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.le_succ n))

/-- The target-valued output scheduled at a catch-up round, with the least
unused target point as a harmless fallback. -/
noncomputable def catchupCandidate
    (O : OrderedLanguage) (state : OnlineTotalizedGCGState) (t : ℕ) : ℕ :=
  state.outputs.getD (catchupIndex t)
    (leastUnusedTarget O (adaptiveUsed state))

/-- One adaptive adversary announcement. -/
noncomputable def adaptiveAnnouncement
    (O : OrderedLanguage) (state : OnlineTotalizedGCGState) (t : ℕ) : ℕ := by
  classical
  let fallback := leastUnusedTarget O (adaptiveUsed state)
  if hcatch : IsCatchupRound t then
    let candidate := catchupCandidate O state t
    exact if candidate ∈ O.carrier then candidate else fallback
  else
    exact fallback

/-- Joint adversary/GCG run after `t` complete rounds. -/
noncomputable def adaptiveGCGRun
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) :
    ℕ → OnlineTotalizedGCGState
  | 0 => OnlineTotalizedGCGState.initial
  | t + 1 =>
      let old := adaptiveGCGRun F O t
      let current := adaptiveAnnouncement O old t
      onlineTotalizedGCGStep F t old current

noncomputable def adaptivePresentation
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) : ℕ :=
  adaptiveAnnouncement O (adaptiveGCGRun F O t) t

noncomputable def adaptiveGCGOutput
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) : ℕ :=
  onlineTotalizedRoundOutput F t (adaptiveGCGRun F O t)
    (adaptivePresentation F O t)

@[simp] theorem adaptiveGCGRun_zero
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) :
    adaptiveGCGRun F O 0 = OnlineTotalizedGCGState.initial := rfl

@[simp] theorem adaptiveGCGRun_succ
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) :
    adaptiveGCGRun F O (t + 1) =
      onlineTotalizedGCGStep F t (adaptiveGCGRun F O t)
        (adaptivePresentation F O t) := rfl

theorem adaptiveGCGRun_observations_succ
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) :
    (adaptiveGCGRun F O (t + 1)).observations =
      (adaptiveGCGRun F O t).observations ++
        [adaptivePresentation F O t] := by
  rfl

theorem adaptiveGCGRun_outputs_succ
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) :
    (adaptiveGCGRun F O (t + 1)).outputs =
      (adaptiveGCGRun F O t).outputs ++ [adaptiveGCGOutput F O t] := by
  rfl

theorem adaptiveGCGRun_observations_eq
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) :
    (adaptiveGCGRun F O t).observations =
      (List.range t).map (adaptivePresentation F O) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [adaptiveGCGRun_observations_succ, ih]
      simp [List.range_succ]

theorem adaptiveGCGRun_outputs_eq
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) :
    (adaptiveGCGRun F O t).outputs =
      (List.range t).map (adaptiveGCGOutput F O) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [adaptiveGCGRun_outputs_succ, ih]
      simp [List.range_succ]

theorem adaptiveGCGRun_eq_onlineRun
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) :
    adaptiveGCGRun F O t =
      onlineTotalizedGCGRun F (adaptivePresentation F O) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [adaptiveGCGRun_succ, onlineTotalizedGCGRun_succ, ← ih]

/-- The jointly defined output is exactly the repaired GCG output on the
jointly defined adaptive presentation. -/
theorem adaptiveGCGOutput_eq_totalized
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) :
    adaptiveGCGOutput F O t =
      totalizedGCGOutput F (adaptivePresentation F O) t := by
  rw [← onlineTotalizedGCGOutput_eq]
  unfold adaptiveGCGOutput onlineTotalizedGCGOutput
  rw [← adaptiveGCGRun_eq_onlineRun]

theorem adaptivePresentation_mem_target
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) :
    adaptivePresentation F O t ∈ O.carrier := by
  classical
  unfold adaptivePresentation adaptiveAnnouncement
  by_cases hcatch : IsCatchupRound t
  · simp only [dif_pos hcatch]
    by_cases hcandidate :
        catchupCandidate O (adaptiveGCGRun F O t) t ∈ O.carrier
    · simp [hcandidate]
    · simp [hcandidate, leastUnusedTarget_mem]
  · simp [hcatch, leastUnusedTarget_mem]

end GenLimit.TimeSensitive

end

-- GenLimit.Paper30_TimeSensitiveLanguageGeneration.AdaptivePresentationExact
section
set_option autoImplicit true

/-!
# Exactness of the sparse adaptive presentation

The ordinary least-unused rounds enumerate every target point not claimed by
the generator.  The exponentially sparse catch-up rounds enumerate every
target point that the generator did claim.  Together these two mechanisms
make the adaptive stream an exact presentation of the ordered target.
-/

namespace GenLimit.TimeSensitive

open GenLimit.KleinbergWei

theorem adaptiveGCGRun_outputs_getD
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage)
    {n t : ℕ} (hnt : n < t) (fallback : ℕ) :
    (adaptiveGCGRun F O t).outputs.getD n fallback =
      adaptiveGCGOutput F O n := by
  rw [adaptiveGCGRun_outputs_eq]
  rw [List.getD_eq_getElem _ _ (by simpa using hnt)]
  simp

theorem adaptivePresentation_eq_least_of_not_catchup
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage)
    {t : ℕ} (hcatch : ¬IsCatchupRound t) :
    adaptivePresentation F O t =
      leastUnusedTarget O (adaptiveUsed (adaptiveGCGRun F O t)) := by
  classical
  simp [adaptivePresentation, adaptiveAnnouncement, hcatch]

theorem adaptivePresentation_not_mem_used_of_not_catchup
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage)
    {t : ℕ} (hcatch : ¬IsCatchupRound t) :
    adaptivePresentation F O t ∉ adaptiveUsed (adaptiveGCGRun F O t) := by
  rw [adaptivePresentation_eq_least_of_not_catchup F O hcatch]
  exact leastUnusedTarget_fresh O _

theorem adaptivePresentation_ne_prior_of_not_catchup
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage)
    {s t : ℕ} (hst : s < t) (hcatch : ¬IsCatchupRound t) :
    adaptivePresentation F O t ≠ adaptivePresentation F O s := by
  intro heq
  apply adaptivePresentation_not_mem_used_of_not_catchup F O hcatch
  apply Finset.mem_union_left
  rw [adaptiveGCGRun_observations_eq]
  simp
  exact ⟨s, hst, heq.symm⟩

theorem odd_not_catchup (k : ℕ) :
    ¬IsCatchupRound (2 * k + 1) := by
  rintro ⟨n, hn⟩
  have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by
    simp [pow_succ, Nat.mul_comm]
  omega

theorem odd_adaptivePresentation_injective
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) :
    Function.Injective
      (fun k => adaptivePresentation F O (2 * k + 1)) := by
  intro a b hab
  rcases lt_trichotomy a b with hablt | rfl | hbalt
  · have htime : 2 * a + 1 < 2 * b + 1 := by omega
    exfalso
    exact (adaptivePresentation_ne_prior_of_not_catchup F O htime
      (odd_not_catchup b)) hab.symm
  · rfl
  · have htime : 2 * b + 1 < 2 * a + 1 := by omega
    exfalso
    exact (adaptivePresentation_ne_prior_of_not_catchup F O htime
      (odd_not_catchup a)) hab

/-- The repaired GCG is fresh against the current and all earlier adaptive
announcements, and never repeats one of its own outputs. -/
theorem adaptiveGCG_freshPlay
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) :
    FreshPlay (adaptivePresentation F O) (adaptiveGCGOutput F O) := by
  have hout : adaptiveGCGOutput F O =
      totalizedGCGOutput F (adaptivePresentation F O) := by
    funext t
    exact adaptiveGCGOutput_eq_totalized F O t
  rw [hout]
  exact totalizedGCG_freshPlay F (adaptivePresentation F O)

theorem adaptiveGCGOutput_injective
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) :
    Function.Injective (adaptiveGCGOutput F O) :=
  (adaptiveGCG_freshPlay F O).generator_injective

theorem adaptivePresentation_at_scheduled_output
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (n : ℕ)
    (hmem : adaptiveGCGOutput F O n ∈ O.carrier) :
    adaptivePresentation F O (2 ^ (n + 1)) =
      adaptiveGCGOutput F O n := by
  classical
  have hcatch : IsCatchupRound (2 ^ (n + 1)) := ⟨n, rfl⟩
  have hnt : n < 2 ^ (n + 1) := index_lt_scheduled_time n
  have hcandidate :
      catchupCandidate O (adaptiveGCGRun F O (2 ^ (n + 1)))
          (2 ^ (n + 1)) = adaptiveGCGOutput F O n := by
    simp only [catchupCandidate, catchupIndex_scheduled]
    exact adaptiveGCGRun_outputs_getD F O hnt _
  simp [adaptivePresentation, adaptiveAnnouncement, hcatch,
    hcandidate, hmem]

theorem target_rank_unused_of_never_announced_or_generated
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage)
    {j t : ℕ}
    (hadv : ∀ q, adaptivePresentation F O q ≠ O.enumeration j)
    (hgen : ∀ q, adaptiveGCGOutput F O q ≠ O.enumeration j) :
    UnusedTargetRank O (adaptiveUsed (adaptiveGCGRun F O t)) j := by
  intro hused
  rcases Finset.mem_union.mp hused with hobserved | houtput
  · rw [adaptiveGCGRun_observations_eq] at hobserved
    simp only [List.mem_toFinset, List.mem_map, List.mem_range] at hobserved
    obtain ⟨q, hqt, hq⟩ := hobserved
    exact hadv q hq
  · rw [adaptiveGCGRun_outputs_eq] at houtput
    simp only [List.mem_toFinset, List.mem_map, List.mem_range] at houtput
    obtain ⟨q, hqt, hq⟩ := houtput
    exact hgen q hq

theorem odd_adaptivePresentation_mem_lower_prefix_of_never
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage)
    {j k : ℕ}
    (hadv : ∀ q, adaptivePresentation F O q ≠ O.enumeration j)
    (hgen : ∀ q, adaptiveGCGOutput F O q ≠ O.enumeration j) :
    adaptivePresentation F O (2 * k + 1) ∈
      targetPrefix O.enumeration j := by
  let t := 2 * k + 1
  have hnotCatch : ¬IsCatchupRound t := odd_not_catchup k
  have hjUnused :
      UnusedTargetRank O (adaptiveUsed (adaptiveGCGRun F O t)) j :=
    target_rank_unused_of_never_announced_or_generated F O hadv hgen
  have hle :
      leastUnusedTargetRank O (adaptiveUsed (adaptiveGCGRun F O t)) ≤ j :=
    leastUnusedTargetRank_min O _ hjUnused
  have hne :
      leastUnusedTargetRank O (adaptiveUsed (adaptiveGCGRun F O t)) ≠ j := by
    intro heq
    apply hadv t
    rw [adaptivePresentation_eq_least_of_not_catchup F O hnotCatch]
    exact congrArg O.enumeration heq
  change adaptivePresentation F O (2 * k + 1) ∈
    sequencePrefix O.enumeration j
  rw [mem_sequencePrefix_iff]
  refine ⟨leastUnusedTargetRank O (adaptiveUsed (adaptiveGCGRun F O t)),
    lt_of_le_of_ne hle hne, ?_⟩
  rw [adaptivePresentation_eq_least_of_not_catchup F O hnotCatch]
  rfl

/-- Every target point not generated by the repaired GCG must occur on an
ordinary least-unused adversary round. -/
theorem target_mem_adaptivePresentation_of_not_generated
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage)
    {x : ℕ} (hx : x ∈ O.carrier)
    (hgen : x ∉ Set.range (adaptiveGCGOutput F O)) :
    x ∈ Set.range (adaptivePresentation F O) := by
  obtain ⟨j, hj⟩ : ∃ j, O.enumeration j = x := by
    rw [← O.range_enumeration] at hx
    exact hx
  by_contra hadvRange
  have hadv : ∀ q, adaptivePresentation F O q ≠ O.enumeration j := by
    intro q hq
    apply hadvRange
    exact ⟨q, hq.trans hj⟩
  have hgen' : ∀ q, adaptiveGCGOutput F O q ≠ O.enumeration j := by
    intro q hq
    apply hgen
    exact ⟨q, hq.trans hj⟩
  have hinfinite :
      (Set.range fun k => adaptivePresentation F O (2 * k + 1)).Infinite :=
    Set.infinite_range_of_injective
      (odd_adaptivePresentation_injective F O)
  have hsubset :
      Set.range (fun k => adaptivePresentation F O (2 * k + 1)) ⊆
        (↑(targetPrefix O.enumeration j) : Set ℕ) := by
    rintro _ ⟨k, rfl⟩
    exact odd_adaptivePresentation_mem_lower_prefix_of_never F O hadv hgen'
  exact (targetPrefix O.enumeration j).finite_toSet.not_infinite
    (hinfinite.mono hsubset)

/-- The sparse adaptive stream is an exact presentation of the target. -/
theorem adaptivePresentation_presents
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) :
    Presents (adaptivePresentation F O) O.carrier := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    exact adaptivePresentation_mem_target F O t
  · intro x hx
    by_cases hgen : x ∈ Set.range (adaptiveGCGOutput F O)
    · obtain ⟨n, hn⟩ := hgen
      refine ⟨2 ^ (n + 1), ?_⟩
      rw [adaptivePresentation_at_scheduled_output F O n]
      · exact hn
      · simpa [hn] using hx
    · exact target_mem_adaptivePresentation_of_not_generated F O hx hgen

end GenLimit.TimeSensitive

end

-- GenLimit.Paper30_TimeSensitiveLanguageGeneration.GreedyRun
section
set_option autoImplicit true

/-!
# Stable greedy stages in GCG

This file proves the rank-aware predecessor pairing used when one stage of
Algorithm 2 remains on a fixed canonically ordered language.  It reuses the
shared first-announcement partition, but counts prefixes in the language's
canonical order rather than in the ambient natural-number order.

The key conclusion is finite: after a fixed burn-in, every adversary-first
target value outside a finite exceptional prefix is paired injectively with
an earlier, timely generator-first value.  A later module converts this
pairing into the cardinal bound which forces a GCG stage to terminate.
-/

namespace GenLimit.TimeSensitive

open GenLimit
open GenLimit.KleinbergWei

/-- First time at which the adversary announces `x`.  The fallback branch is
never used once membership in the adversary range has been established. -/
noncomputable abbrev firstAdversaryTime
    (adversary : ℕ → ℕ) (x : ℕ) : ℕ :=
  GenLimit.firstAnnouncementTime adversary x

theorem firstAdversaryTime_spec
    {adversary : ℕ → ℕ} {x : ℕ} (hx : x ∈ Set.range adversary) :
    adversary (firstAdversaryTime adversary x) = x :=
  GenLimit.firstAnnouncementTime_spec hx

theorem firstAdversaryTime_min
    {adversary : ℕ → ℕ} {x t : ℕ} (hx : x ∈ Set.range adversary)
    (ht : adversary t = x) :
    firstAdversaryTime adversary x ≤ t := by
  exact GenLimit.firstAnnouncementTime_min hx ht

theorem firstAdversaryTime_not_mem_sample
    {adversary : ℕ → ℕ} {x : ℕ} (hx : x ∈ Set.range adversary) :
    x ∉ sample adversary (firstAdversaryTime adversary x) :=
  GenLimit.firstAnnouncementTime_not_mem_sample hx

/-- From round `T` onward, the generator literally performs the
`OnTimeUnused` operation for one fixed ordered language. -/
def GreedyFrom
    (O : OrderedLanguage) (adversary generator : ℕ → ℕ) (T : ℕ) : Prop :=
  ∀ t, T ≤ t →
    generator t =
      onTimeUnused O
        (sample adversary (t + 1) ∪ sequencePrefix generator t) t

theorem greedyFrom_mem
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ} {T t : ℕ}
    (hgreedy : GreedyFrom O adversary generator T) (ht : T ≤ t) :
    generator t ∈ O.carrier := by
  rw [hgreedy t ht]
  exact onTimeUnused_mem _ _ _

theorem greedyFrom_rank_onTime
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ} {T t : ℕ}
    (hgreedy : GreedyFrom O adversary generator T) (ht : T ≤ t) :
    ∃ r, generator t = O.enumeration r ∧ t < r := by
  refine ⟨onTimeUnusedRank O
      (sample adversary (t + 1) ∪ sequencePrefix generator t) t, ?_,
    onTimeUnused_onTime _ _ _⟩
  rw [hgreedy t ht]
  rfl

/-- If a canonical-rank `j` value belongs to the adversary and was not
generated first, a stable greedy stage starting before `j` forces its first
adversary occurrence to happen by time `j`. -/
theorem firstAdversaryTime_le_rank
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ} {T j : ℕ}
    (hgreedy : GreedyFrom O adversary generator T)
    (hjT : T < j)
    (hadv : O.enumeration j ∈ AdversaryFirst adversary generator) :
    firstAdversaryTime adversary (O.enumeration j) ≤ j := by
  let x := O.enumeration j
  have hxRange : x ∈ Set.range adversary := by
    obtain ⟨q, hq, -⟩ := hadv
    exact ⟨q, hq⟩
  by_contra hnot
  have hjfirst : j < firstAdversaryTime adversary x :=
    Nat.lt_of_not_ge hnot
  have hjpos : 0 < j := lt_of_le_of_lt (Nat.zero_le T) hjT
  let used :=
    sample adversary ((j - 1) + 1) ∪ sequencePrefix generator (j - 1)
  have hxNotObserved : x ∉ sample adversary ((j - 1) + 1) := by
    have hnotSample := firstAdversaryTime_not_mem_sample hxRange
    intro hx
    apply hnotSample
    rw [mem_sample_iff] at hx ⊢
    obtain ⟨s, hs, hsx⟩ := hx
    exact ⟨s, lt_of_lt_of_le hs (by omega), hsx⟩
  have hxNotGenerated : x ∉ sequencePrefix generator (j - 1) := by
    intro hx
    obtain ⟨s, hs, hsx⟩ :=
      (mem_sequencePrefix_iff generator x (j - 1)).mp hx
    obtain ⟨q, hqx, hnoGenerator⟩ := hadv
    have hfirstq : firstAdversaryTime adversary x ≤ q :=
      firstAdversaryTime_min hxRange hqx
    exact hnoGenerator s (lt_trans hs (by omega)) hsx
  have hjEligible : OnTimeUnusedRank O used (j - 1) j := by
    refine ⟨by omega, ?_⟩
    exact Finset.notMem_union.mpr ⟨hxNotObserved, hxNotGenerated⟩
  have hleast : onTimeUnusedRank O used (j - 1) = j := by
    apply le_antisymm
    · exact onTimeUnusedRank_min O used (j - 1) hjEligible
    · have := onTimeUnused_onTime O used (j - 1)
      omega
  have houtput : generator (j - 1) = x := by
    rw [hgreedy (j - 1) (by omega)]
    change O.enumeration (onTimeUnusedRank O used (j - 1)) = x
    rw [hleast]
  obtain ⟨q, hqx, hnoGenerator⟩ := hadv
  have hfirstq : firstAdversaryTime adversary x ≤ q :=
    firstAdversaryTime_min hxRange hqx
  exact hnoGenerator (j - 1) (by omega) houtput

/-- Pair an adversary-first value with the generator output immediately
before its first adversary occurrence. -/
noncomputable abbrev greedyPartner
    (adversary generator : ℕ → ℕ) (x : ℕ) : ℕ :=
  GenLimit.predecessorPartner adversary generator x

/-- An output produced before canonical rank `k` is timely for the identity
deadline at that rank. -/
theorem mem_timelyElements_of_output_before_rank
    (O : OrderedLanguage) (generator : ℕ → ℕ)
    {q k i : ℕ} (hki : k < i) (hqk : q < k)
    (hout : generator q = O.enumeration k) :
    O.enumeration k ∈ timelyElements generator O.enumeration id i := by
  classical
  simp only [timelyElements, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range]
  refine ⟨k, ⟨hki, ?_⟩, rfl⟩
  rw [mem_sequencePrefix_iff]
  exact ⟨q, by simpa using hqk, hout⟩

/-- The predecessor partner of a late adversary-first value has a strictly
smaller canonical rank and is timely in every later target prefix. -/
theorem greedyPartner_mem_timely
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T i j : ℕ}
    (hgreedy : GreedyFrom O adversary generator T)
    (hTj : T < j)
    (hTfirst : T < firstAdversaryTime adversary (O.enumeration j))
    (hji : j < i)
    (hadv : O.enumeration j ∈ AdversaryFirst adversary generator) :
    greedyPartner adversary generator (O.enumeration j) ∈
      timelyElements generator O.enumeration id i := by
  let x := O.enumeration j
  let q := firstAdversaryTime adversary x
  have hTq : T < q := by
    simpa [q, x] using hTfirst
  have hxRange : x ∈ Set.range adversary := by
    obtain ⟨w, hw, -⟩ := hadv
    exact ⟨w, hw⟩
  have hqj : q ≤ j := by
    exact firstAdversaryTime_le_rank hgreedy hTj hadv
  have hqpos : 0 < q := lt_of_le_of_lt (Nat.zero_le T) hTfirst
  let used := sample adversary ((q - 1) + 1) ∪
    sequencePrefix generator (q - 1)
  have hxNotObserved : x ∉ sample adversary ((q - 1) + 1) := by
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt hqpos))] using
        (firstAdversaryTime_not_mem_sample hxRange)
  have hxNotGenerated : x ∉ sequencePrefix generator (q - 1) := by
    intro hx
    obtain ⟨s, hs, hsx⟩ :=
      (mem_sequencePrefix_iff generator x (q - 1)).mp hx
    obtain ⟨w, hwx, hnoGenerator⟩ := hadv
    have hqw : q ≤ w := firstAdversaryTime_min hxRange hwx
    exact hnoGenerator s (lt_trans hs (by omega)) hsx
  have hjEligible : OnTimeUnusedRank O used (q - 1) j := by
    refine ⟨by omega, ?_⟩
    exact Finset.notMem_union.mpr ⟨hxNotObserved, hxNotGenerated⟩
  let k := onTimeUnusedRank O used (q - 1)
  have hkj : k ≤ j := onTimeUnusedRank_min O used (q - 1) hjEligible
  have hqk : q - 1 < k := onTimeUnused_onTime O used (q - 1)
  have hout : generator (q - 1) = O.enumeration k := by
    rw [hgreedy (q - 1) (by omega : T ≤ q - 1)]
    change onTimeUnused O used (q - 1) = O.enumeration k
    rfl
  have hkne : k ≠ j := by
    intro hkjEq
    obtain ⟨w, hwx, hnoGenerator⟩ := hadv
    have hqw : q ≤ w := firstAdversaryTime_min hxRange hwx
    apply hnoGenerator (q - 1) (by omega)
    rw [hout, hkjEq]
  have hkjStrict : k < j := lt_of_le_of_ne hkj hkne
  change generator (q - 1) ∈ timelyElements generator O.enumeration id i
  rw [hout]
  exact mem_timelyElements_of_output_before_rank O generator
    (lt_trans hkjStrict hji) hqk hout

/-- Predecessor pairing is injective on values whose first adversary time is
strictly after `T`; positivity removes the predecessor boundary ambiguity. -/
theorem greedyPartner_injOn
    {adversary generator : ℕ → ℕ} {T : ℕ}
    (hplay : FreshPlay adversary generator) :
    Set.InjOn (greedyPartner adversary generator)
      {x | x ∈ Set.range adversary ∧
        T < firstAdversaryTime adversary x} := by
  apply GenLimit.predecessorPartner_injOn hplay.generator_injective
  · intro x hx
    exact hx.1
  · intro x hx
    exact lt_of_le_of_lt (Nat.zero_le T) hx.2

/-! ## Finite rank-prefix accounting -/

theorem targetPrefix_card_ordered (O : OrderedLanguage) (i : ℕ) :
    (targetPrefix O.enumeration i).card = i := by
  letI : DecidableEq ℕ := Classical.decEq ℕ
  rw [targetPrefix, sequencePrefix]
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro a _ b _ hab
    exact O.enumeration_injective hab

theorem sequencePrefix_card_le (S : ℕ → ℕ) (i : ℕ) :
    (sequencePrefix S i).card ≤ i := by
  letI : DecidableEq ℕ := Classical.decEq ℕ
  rw [sequencePrefix]
  simpa only [Finset.card_range] using
    (Finset.card_image_le (s := Finset.range i) (f := S))

theorem sample_card_le (S : ℕ → ℕ) (i : ℕ) :
    (sample S i).card ≤ i := by
  unfold sample
  simpa only [Finset.card_range] using
    (Finset.card_image_le (s := Finset.range i) (f := S))

noncomputable def adversaryFirstPrefix
    (O : OrderedLanguage) (adversary generator : ℕ → ℕ)
    (i : ℕ) : Finset ℕ := by
  classical
  exact (targetPrefix O.enumeration i).filter fun x =>
    x ∈ AdversaryFirst adversary generator

noncomputable def generatorFirstPrefix
    (O : OrderedLanguage) (adversary generator : ℕ → ℕ)
    (i : ℕ) : Finset ℕ := by
  classical
  exact (targetPrefix O.enumeration i).filter fun x =>
    x ∈ GeneratorFirst adversary generator

@[simp] theorem mem_adversaryFirstPrefix
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ} {i x : ℕ} :
    x ∈ adversaryFirstPrefix O adversary generator i ↔
      x ∈ targetPrefix O.enumeration i ∧
        x ∈ AdversaryFirst adversary generator := by
  classical
  simp [adversaryFirstPrefix]

@[simp] theorem mem_generatorFirstPrefix
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ} {i x : ℕ} :
    x ∈ generatorFirstPrefix O adversary generator i ↔
      x ∈ targetPrefix O.enumeration i ∧
        x ∈ GeneratorFirst adversary generator := by
  classical
  simp [generatorFirstPrefix]

/-- Adversary-first values in the first `i` canonical ranks that are outside
both burn-in exception sets. -/
noncomputable def lateAdversaryPrefix
    (O : OrderedLanguage) (adversary generator : ℕ → ℕ)
    (T i : ℕ) : Finset ℕ := by
  classical
  exact (targetPrefix O.enumeration i).filter fun x =>
    x ∈ AdversaryFirst adversary generator ∧
      x ∉ targetPrefix O.enumeration (T + 1) ∧
      x ∉ sample adversary (T + 1)

/-- Generator-first values in the first `i` canonical ranks that were not
already emitted during burn-in. -/
noncomputable def lateGeneratorPrefix
    (O : OrderedLanguage) (adversary generator : ℕ → ℕ)
    (T i : ℕ) : Finset ℕ := by
  classical
  exact (targetPrefix O.enumeration i).filter fun x =>
    x ∈ GeneratorFirst adversary generator ∧
      x ∉ sequencePrefix generator T

@[simp] theorem mem_lateAdversaryPrefix
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T i x : ℕ} :
    x ∈ lateAdversaryPrefix O adversary generator T i ↔
      x ∈ targetPrefix O.enumeration i ∧
        x ∈ AdversaryFirst adversary generator ∧
        x ∉ targetPrefix O.enumeration (T + 1) ∧
        x ∉ sample adversary (T + 1) := by
  classical
  simp [lateAdversaryPrefix]

@[simp] theorem mem_lateGeneratorPrefix
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T i x : ℕ} :
    x ∈ lateGeneratorPrefix O adversary generator T i ↔
      x ∈ targetPrefix O.enumeration i ∧
        x ∈ GeneratorFirst adversary generator ∧
        x ∉ sequencePrefix generator T := by
  classical
  simp [lateGeneratorPrefix]

theorem lateAdversaryPrefix_card_le_timely
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T i : ℕ}
    (hplay : FreshPlay adversary generator)
    (hgreedy : GreedyFrom O adversary generator T) :
    (lateAdversaryPrefix O adversary generator T i).card ≤
      (timelyElements generator O.enumeration id i).card := by
  classical
  apply Finset.card_le_card_of_injOn (greedyPartner adversary generator)
  · intro x hx
    have hxFin : x ∈ lateAdversaryPrefix O adversary generator T i := hx
    rw [mem_lateAdversaryPrefix] at hxFin
    replace hx := hxFin
    obtain ⟨hxPrefix, hxAdv, hxNotRanks, hxNotSample⟩ := hx
    obtain ⟨j, hji, hjx⟩ :=
      (mem_sequencePrefix_iff O.enumeration x i).mp hxPrefix
    have hTj : T < j := by
      by_contra hnot
      apply hxNotRanks
      exact (mem_sequencePrefix_iff O.enumeration x (T + 1)).mpr
        ⟨j, by omega, hjx⟩
    have hxRange : x ∈ Set.range adversary := by
      obtain ⟨q, hqx, -⟩ := hxAdv
      exact ⟨q, hqx⟩
    have hTfirst : T < firstAdversaryTime adversary x := by
      by_contra hnot
      apply hxNotSample
      rw [mem_sample_iff]
      exact ⟨firstAdversaryTime adversary x, by omega,
        firstAdversaryTime_spec hxRange⟩
    subst x
    exact greedyPartner_mem_timely hgreedy hTj hTfirst hji hxAdv
  · intro x hx y hy hxy
    have hxFin : x ∈ lateAdversaryPrefix O adversary generator T i := hx
    have hyFin : y ∈ lateAdversaryPrefix O adversary generator T i := hy
    rw [mem_lateAdversaryPrefix] at hxFin hyFin
    replace hx := hxFin
    replace hy := hyFin
    have hxRange : x ∈ Set.range adversary := by
      obtain ⟨q, hqx, -⟩ := hx.2.1
      exact ⟨q, hqx⟩
    have hyRange : y ∈ Set.range adversary := by
      obtain ⟨q, hqy, -⟩ := hy.2.1
      exact ⟨q, hqy⟩
    have hxLate : T < firstAdversaryTime adversary x := by
      by_contra hnot
      exact hx.2.2.2 ((mem_sample_iff).mpr
        ⟨firstAdversaryTime adversary x, by omega,
          firstAdversaryTime_spec hxRange⟩)
    have hyLate : T < firstAdversaryTime adversary y := by
      by_contra hnot
      exact hy.2.2.2 ((mem_sample_iff).mpr
        ⟨firstAdversaryTime adversary y, by omega,
          firstAdversaryTime_spec hyRange⟩)
    exact greedyPartner_injOn hplay ⟨hxRange, hxLate⟩
      ⟨hyRange, hyLate⟩ hxy

theorem lateGeneratorPrefix_subset_timely
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T i : ℕ}
    (hgreedy : GreedyFrom O adversary generator T) :
    lateGeneratorPrefix O adversary generator T i ⊆
      timelyElements generator O.enumeration id i := by
  classical
  intro x hx
  rw [mem_lateGeneratorPrefix] at hx
  obtain ⟨hxPrefix, hxGen, hxNotEarly⟩ := hx
  obtain ⟨j, hji, hjx⟩ :=
    (mem_sequencePrefix_iff O.enumeration x i).mp hxPrefix
  obtain ⟨t, htx, -⟩ := hxGen
  have hTt : T ≤ t := by
    by_contra hnot
    apply hxNotEarly
    exact (mem_sequencePrefix_iff generator x T).mpr
      ⟨t, Nat.lt_of_not_ge hnot, htx⟩
  obtain ⟨k, hgenk, htk⟩ := greedyFrom_rank_onTime hgreedy hTt
  have hkj : k = j := by
    apply O.enumeration_injective
    rw [← hgenk, htx, hjx]
  subst k
  rw [← hjx]
  exact mem_timelyElements_of_output_before_rank O generator hji htk
    (htx.trans hjx.symm)

/-- After burn-in, every canonical value is first announced by one of the two
players even when the adversary does not enumerate the active language.  If
the adversary never announces the value, the literal greedy rule takes it no
later than its canonical rank. -/
theorem canonical_value_first_announced
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T j : ℕ}
    (hgreedy : GreedyFrom O adversary generator T)
    (hTj : T < j) :
    O.enumeration j ∈ AdversaryFirst adversary generator ∪
      GeneratorFirst adversary generator := by
  let x := O.enumeration j
  by_cases hxRange : x ∈ Set.range adversary
  · exact range_subset_first_announcements adversary generator hxRange
  · apply Set.mem_union_right
    by_cases hbefore : ∃ s, s < j ∧ generator s = x
    · obtain ⟨s, hsj, hsx⟩ := hbefore
      refine ⟨s, hsx, ?_⟩
      intro q hqs hqx
      exact hxRange ⟨q, hqx⟩
    · have hjpos : 0 < j := lt_of_le_of_lt (Nat.zero_le T) hTj
      let used := sample adversary ((j - 1) + 1) ∪
        sequencePrefix generator (j - 1)
      have hxNotObserved : x ∉ sample adversary ((j - 1) + 1) := by
        intro hx
        rw [mem_sample_iff] at hx
        obtain ⟨q, -, hqx⟩ := hx
        exact hxRange ⟨q, hqx⟩
      have hxNotGenerated : x ∉ sequencePrefix generator (j - 1) := by
        intro hx
        obtain ⟨s, hs, hsx⟩ :=
          (mem_sequencePrefix_iff generator x (j - 1)).mp hx
        exact hbefore ⟨s, lt_trans hs (by omega), hsx⟩
      have hjEligible : OnTimeUnusedRank O used (j - 1) j := by
        exact ⟨by omega,
          Finset.notMem_union.mpr ⟨hxNotObserved, hxNotGenerated⟩⟩
      have hleast : onTimeUnusedRank O used (j - 1) = j := by
        apply le_antisymm
        · exact onTimeUnusedRank_min O used (j - 1) hjEligible
        · have := onTimeUnused_onTime O used (j - 1)
          omega
      have hout : generator (j - 1) = x := by
        rw [hgreedy (j - 1) (by omega)]
        change O.enumeration (onTimeUnusedRank O used (j - 1)) = x
        rw [hleast]
      refine ⟨j - 1, hout, ?_⟩
      intro q hq hqx
      exact hxRange ⟨q, hqx⟩

/-- Restricting the preceding coverage to a finite canonical prefix leaves
only the first `T + 1` ranks as an explicit exception set. -/
theorem targetPrefix_card_le_announcement_cards_add_burnIn
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T : ℕ} (hgreedy : GreedyFrom O adversary generator T) (i : ℕ) :
    i ≤
      (adversaryFirstPrefix O adversary generator i).card +
      (generatorFirstPrefix O adversary generator i).card + (T + 1) := by
  classical
  let A := adversaryFirstPrefix O adversary generator i
  let G := generatorFirstPrefix O adversary generator i
  have hcover : targetPrefix O.enumeration i ⊆
      (A ∪ G) ∪ targetPrefix O.enumeration (T + 1) := by
    intro x hx
    obtain ⟨j, hji, hjx⟩ :=
      (mem_sequencePrefix_iff O.enumeration x i).mp hx
    by_cases hTj : T < j
    · rcases canonical_value_first_announced hgreedy hTj with hxA | hxG
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (mem_adversaryFirstPrefix.mpr ⟨hx, by simpa [hjx] using hxA⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (mem_generatorFirstPrefix.mpr ⟨hx, by simpa [hjx] using hxG⟩))
    · exact Finset.mem_union_right _
        ((mem_sequencePrefix_iff O.enumeration x (T + 1)).mpr
          ⟨j, by omega, hjx⟩)
  calc
    i = (targetPrefix O.enumeration i).card :=
      (targetPrefix_card_ordered O i).symm
    _ ≤ ((A ∪ G) ∪ targetPrefix O.enumeration (T + 1)).card :=
      Finset.card_le_card hcover
    _ ≤ (A.card + G.card) +
        (targetPrefix O.enumeration (T + 1)).card :=
      (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ = (adversaryFirstPrefix O adversary generator i).card +
        (generatorFirstPrefix O adversary generator i).card + (T + 1) := by
      rw [targetPrefix_card_ordered]

/-- Exact finite bound for a stable greedy stage.  The explicit `4T + 3`
term accounts for the partition boundary, early canonical ranks, early
adversary announcements, and early generator outputs. -/
theorem stableGreedy_card_bound
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T i : ℕ}
    (hplay : FreshPlay adversary generator)
    (hgreedy : GreedyFrom O adversary generator T) :
    i ≤ 2 * (timelyElements generator O.enumeration id i).card +
      (4 * T + 3) := by
  classical
  let A := adversaryFirstPrefix O adversary generator i
  let G := generatorFirstPrefix O adversary generator i
  let LA := lateAdversaryPrefix O adversary generator T i
  let LG := lateGeneratorPrefix O adversary generator T i
  have hAcover : A ⊆
      (LA ∪ targetPrefix O.enumeration (T + 1)) ∪ sample adversary (T + 1) := by
    intro x hx
    have hx' : x ∈ targetPrefix O.enumeration i ∧
        x ∈ AdversaryFirst adversary generator :=
      mem_adversaryFirstPrefix.mp (show x ∈ A from hx)
    by_cases hrank : x ∈ targetPrefix O.enumeration (T + 1)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hrank)
    by_cases hsample : x ∈ sample adversary (T + 1)
    · exact Finset.mem_union_right _ hsample
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hx'.1, hx'.2, hrank, hsample⟩
  have hGcover : G ⊆ LG ∪ sequencePrefix generator T := by
    intro x hx
    have hx' : x ∈ targetPrefix O.enumeration i ∧
        x ∈ GeneratorFirst adversary generator :=
      mem_generatorFirstPrefix.mp (show x ∈ G from hx)
    by_cases hearly : x ∈ sequencePrefix generator T
    · exact Finset.mem_union_right _ hearly
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hx'.1, hx'.2, hearly⟩)
  have hAcard : A.card ≤
      (timelyElements generator O.enumeration id i).card + 2 * (T + 1) := by
    calc
      A.card ≤ ((LA ∪ targetPrefix O.enumeration (T + 1)) ∪
          sample adversary (T + 1)).card := Finset.card_le_card hAcover
      _ ≤ LA.card + (targetPrefix O.enumeration (T + 1)).card +
          (sample adversary (T + 1)).card := by
        exact (Finset.card_union_le _ _).trans
          (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      _ ≤ (timelyElements generator O.enumeration id i).card +
          (T + 1) + (T + 1) := by
        exact Nat.add_le_add
          (Nat.add_le_add
            (lateAdversaryPrefix_card_le_timely hplay hgreedy)
            (Nat.le_of_eq (targetPrefix_card_ordered O (T + 1))))
          (sample_card_le adversary (T + 1))
      _ = (timelyElements generator O.enumeration id i).card +
          2 * (T + 1) := by omega
  have hGcard : G.card ≤
      (timelyElements generator O.enumeration id i).card + T := by
    calc
      G.card ≤ (LG ∪ sequencePrefix generator T).card :=
        Finset.card_le_card hGcover
      _ ≤ LG.card + (sequencePrefix generator T).card :=
        Finset.card_union_le _ _
      _ ≤ (timelyElements generator O.enumeration id i).card + T := by
        exact Nat.add_le_add
          (Finset.card_le_card (lateGeneratorPrefix_subset_timely hgreedy))
          (sequencePrefix_card_le generator T)
  have hpartition : i ≤ A.card + G.card + (T + 1) := by
    simpa [A, G] using
      targetPrefix_card_le_announcement_cards_add_burnIn hgreedy i
  change i ≤ 2 * (timelyElements generator O.enumeration id i).card +
    (4 * T + 3)
  omega

/-- A stable literal greedy stage eventually crosses every GCG threshold.
This is the rank-aware, machine-ready form of Appendix E's finite ownership
argument. -/
theorem stableGreedy_eventually_crosses_threshold
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T m : ℕ}
    (hplay : FreshPlay adversary generator)
    (hgreedy : GreedyFrom O adversary generator T) :
    ∀ᶠ i in Filter.atTop,
      gcgThreshold m ≤ timelyDensity generator O.enumeration id i := by
  have hcard : ∀ i,
      (i - 2 * (2 * T + 2)) / 2 ≤
        (timelyElements generator O.enumeration id i).card := by
    intro i
    have hbound := stableGreedy_card_bound
      (i := i) hplay hgreedy
    omega
  have hcross := stage_eventually_crosses_threshold m (2 * T + 2)
    (fun i => (timelyElements generator O.enumeration id i).card)
    (Filter.Eventually.of_forall hcard)
  filter_upwards [hcross, Filter.eventually_gt_atTop 0] with i hi hpos
  simpa [timelyDensity, Nat.ne_of_gt hpos] using hi

end GenLimit.TimeSensitive

end

-- GenLimit.Paper30_TimeSensitiveLanguageGeneration.AdaptiveUpperBound
section
set_option autoImplicit true

/-!
# The adaptive half-density upper bound

Every timely target point first emitted on an ordinary round is paired with
the least-unused target point announced immediately before it.  The partner
has lower target rank, is never emitted by the generator, and the pairing is
injective.  Only the exponentially sparse catch-up rounds are exceptions;
there are at most `log2 i` of them before target rank `i`.
-/

namespace GenLimit.TimeSensitive

open Filter
open GenLimit.KleinbergWei

noncomputable def firstGeneratorTime
    (generator : ℕ → ℕ) (x : ℕ) : ℕ := by
  classical
  exact if h : x ∈ Set.range generator then Nat.find h else 0

theorem firstGeneratorTime_spec
    {generator : ℕ → ℕ} {x : ℕ} (hx : x ∈ Set.range generator) :
    generator (firstGeneratorTime generator x) = x := by
  classical
  simp only [firstGeneratorTime, dif_pos hx]
  exact Nat.find_spec hx

theorem firstGeneratorTime_min
    {generator : ℕ → ℕ} {x : ℕ} (hx : x ∈ Set.range generator)
    {t : ℕ} (ht : generator t = x) :
    firstGeneratorTime generator x ≤ t := by
  classical
  simp only [firstGeneratorTime, dif_pos hx]
  exact Nat.find_min' hx ht

theorem mem_timelyElements_iff_p30
    {S R : ℕ → ℕ} {D : ℕ → ℕ} {i x : ℕ} :
    x ∈ timelyElements S R D i ↔
      ∃ j, j < i ∧ R j = x ∧ ∃ q, q < D j ∧ S q = R j := by
  classical
  simp only [timelyElements, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range, mem_sequencePrefix_iff]
  constructor
  · rintro ⟨j, ⟨hji, q, hqD, hq⟩, hjx⟩
    exact ⟨j, hji, hjx, q, hqD, hq⟩
  · rintro ⟨j, hji, hjx, q, hqD, hq⟩
    exact ⟨j, ⟨hji, q, hqD, hq⟩, hjx⟩

theorem mem_timelyElements_rank_firstGeneratorTime
    {O : OrderedLanguage} {generator : ℕ → ℕ} {i x : ℕ}
    (hx : x ∈ timelyElements generator O.enumeration id i) :
    ∃ j, j < i ∧ O.enumeration j = x ∧
      firstGeneratorTime generator x < j ∧
      generator (firstGeneratorTime generator x) = x := by
  obtain ⟨j, hji, hjx, q, hqj, hq⟩ :=
    mem_timelyElements_iff_p30.mp hx
  have hxRange : x ∈ Set.range generator := ⟨q, hq.trans hjx⟩
  refine ⟨j, hji, hjx, ?_, firstGeneratorTime_spec hxRange⟩
  exact (firstGeneratorTime_min hxRange (hq.trans hjx)).trans_lt hqj

noncomputable def adaptiveCredited
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (i : ℕ) :
    Finset ℕ :=
  timelyElements (adaptiveGCGOutput F O) O.enumeration id i

noncomputable def adaptiveExceptionalCredits
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (i : ℕ) :
    Finset ℕ := by
  classical
  exact (adaptiveCredited F O i).filter fun x =>
    IsCatchupRound (firstGeneratorTime (adaptiveGCGOutput F O) x)

noncomputable def adaptivePairedCredits
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (i : ℕ) :
    Finset ℕ :=
  adaptiveCredited F O i \ adaptiveExceptionalCredits F O i

noncomputable def adaptivePartner
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (x : ℕ) : ℕ :=
  adaptivePresentation F O
    (firstGeneratorTime (adaptiveGCGOutput F O) x)

@[simp] theorem mem_adaptiveExceptionalCredits
    {F : CanonicallyOrderedFamily} {O : OrderedLanguage} {i x : ℕ} :
    x ∈ adaptiveExceptionalCredits F O i ↔
      x ∈ adaptiveCredited F O i ∧
        IsCatchupRound (firstGeneratorTime (adaptiveGCGOutput F O) x) := by
  classical
  simp [adaptiveExceptionalCredits]

@[simp] theorem mem_adaptivePairedCredits
    {F : CanonicallyOrderedFamily} {O : OrderedLanguage} {i x : ℕ} :
    x ∈ adaptivePairedCredits F O i ↔
      x ∈ adaptiveCredited F O i ∧
        ¬IsCatchupRound (firstGeneratorTime (adaptiveGCGOutput F O) x) := by
  classical
  constructor
  · intro hx
    have hcredit := (Finset.mem_sdiff.mp hx).1
    have hnotExceptional := (Finset.mem_sdiff.mp hx).2
    refine ⟨hcredit, ?_⟩
    intro hcatch
    exact hnotExceptional
      (mem_adaptiveExceptionalCredits.mpr ⟨hcredit, hcatch⟩)
  · rintro ⟨hcredit, hnotCatch⟩
    exact Finset.mem_sdiff.mpr ⟨hcredit, fun hexception =>
      hnotCatch (mem_adaptiveExceptionalCredits.mp hexception).2⟩

theorem adaptivePartner_mem_targetPrefix
    {F : CanonicallyOrderedFamily} {O : OrderedLanguage} {i x : ℕ}
    (hx : x ∈ adaptivePairedCredits F O i) :
    adaptivePartner F O x ∈ targetPrefix O.enumeration i := by
  classical
  have hxCredit := (mem_adaptivePairedCredits.mp hx).1
  have hqOrdinary := (mem_adaptivePairedCredits.mp hx).2
  obtain ⟨j, hji, hjx, hqj, hqx⟩ :=
    mem_timelyElements_rank_firstGeneratorTime hxCredit
  let q := firstGeneratorTime (adaptiveGCGOutput F O) x
  let used := adaptiveUsed (adaptiveGCGRun F O q)
  have hjUnused : UnusedTargetRank O used j := by
    intro hused
    rcases Finset.mem_union.mp hused with hobserved | houtput
    · rw [adaptiveGCGRun_observations_eq] at hobserved
      simp only [List.mem_toFinset, List.mem_map, List.mem_range] at hobserved
      obtain ⟨s, hsq, hs⟩ := hobserved
      exact (adaptiveGCG_freshPlay F O).fresh_adversary q s
        (Nat.le_of_lt hsq) (hs.trans (hjx.trans hqx.symm))
    · rw [adaptiveGCGRun_outputs_eq] at houtput
      simp only [List.mem_toFinset, List.mem_map, List.mem_range] at houtput
      obtain ⟨s, hsq, hs⟩ := houtput
      have hxmin : q ≤ s :=
        firstGeneratorTime_min ⟨q, hqx⟩ (hs.trans hjx)
      omega
  have hle : leastUnusedTargetRank O used ≤ j :=
    leastUnusedTargetRank_min O used hjUnused
  have hpartner : adaptivePartner F O x = leastUnusedTarget O used := by
    exact adaptivePresentation_eq_least_of_not_catchup F O hqOrdinary
  have hne : leastUnusedTargetRank O used ≠ j := by
    intro heq
    have heqValues : adaptivePartner F O x = x := by
      rw [hpartner]
      exact (congrArg O.enumeration heq).trans hjx
    exact (adaptiveGCG_freshPlay F O).fresh_adversary q q le_rfl
      (heqValues.trans hqx.symm)
  change adaptivePartner F O x ∈ sequencePrefix O.enumeration i
  rw [mem_sequencePrefix_iff]
  refine ⟨leastUnusedTargetRank O used,
    (lt_of_le_of_ne hle hne).trans hji, ?_⟩
  exact hpartner.symm

theorem adaptivePartner_not_mem_credited
    {F : CanonicallyOrderedFamily} {O : OrderedLanguage} {i x : ℕ}
    (hx : x ∈ adaptivePairedCredits F O i) :
    adaptivePartner F O x ∉ adaptiveCredited F O i := by
  classical
  intro hpartnerCredit
  have hqOrdinary := (mem_adaptivePairedCredits.mp hx).2
  let q := firstGeneratorTime (adaptiveGCGOutput F O) x
  have hpartnerEq : adaptivePartner F O x =
      leastUnusedTarget O (adaptiveUsed (adaptiveGCGRun F O q)) :=
    adaptivePresentation_eq_least_of_not_catchup F O hqOrdinary
  obtain ⟨k, hki, hkpartner, hrk, hrpartner⟩ :=
    mem_timelyElements_rank_firstGeneratorTime hpartnerCredit
  let r := firstGeneratorTime (adaptiveGCGOutput F O) (adaptivePartner F O x)
  by_cases hrq : r < q
  · apply leastUnusedTarget_fresh O (adaptiveUsed (adaptiveGCGRun F O q))
    rw [← hpartnerEq]
    apply Finset.mem_union_right
    rw [adaptiveGCGRun_outputs_eq]
    simp only [List.mem_toFinset, List.mem_map, List.mem_range]
    exact ⟨r, hrq, hrpartner⟩
  · exact (adaptiveGCG_freshPlay F O).fresh_adversary r q
      (Nat.le_of_not_gt hrq) (by
        simpa [adaptivePartner, q, r] using hrpartner.symm)

theorem adaptivePartner_injOn
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (i : ℕ) :
    Set.InjOn (adaptivePartner F O) (adaptivePairedCredits F O i) := by
  intro x hx y hy hxy
  have hxCredit := (mem_adaptivePairedCredits.mp hx).1
  have hyCredit := (mem_adaptivePairedCredits.mp hy).1
  have hxOrdinary := (mem_adaptivePairedCredits.mp hx).2
  have hyOrdinary := (mem_adaptivePairedCredits.mp hy).2
  obtain ⟨_, _, _, _, hxSpec⟩ :=
    mem_timelyElements_rank_firstGeneratorTime hxCredit
  obtain ⟨_, _, _, _, hySpec⟩ :=
    mem_timelyElements_rank_firstGeneratorTime hyCredit
  let qx := firstGeneratorTime (adaptiveGCGOutput F O) x
  let qy := firstGeneratorTime (adaptiveGCGOutput F O) y
  have htime : qx = qy := by
    rcases lt_trichotomy qx qy with hlt | heq | hgt
    · exact False.elim
        ((adaptivePresentation_ne_prior_of_not_catchup F O hlt hyOrdinary) hxy.symm)
    · exact heq
    · exact False.elim
        ((adaptivePresentation_ne_prior_of_not_catchup F O hgt hxOrdinary) hxy)
  calc
    x = adaptiveGCGOutput F O qx := hxSpec.symm
    _ = adaptiveGCGOutput F O qy := by rw [htime]
    _ = y := hySpec

noncomputable def catchupRounds (i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range i).filter IsCatchupRound

@[simp] theorem mem_catchupRounds {i q : ℕ} :
    q ∈ catchupRounds i ↔ q < i ∧ IsCatchupRound q := by
  classical
  simp [catchupRounds]

theorem catchupIndex_lt_log2_of_lt
    {q i : ℕ} (hcatch : IsCatchupRound q) (hqi : q < i) :
    catchupIndex q < Nat.log2 i := by
  have hqpos : q ≠ 0 := by
    rw [catchupIndex_spec hcatch]
    positivity
  have hipos : i ≠ 0 := by omega
  have hlogq : Nat.log2 q = catchupIndex q + 1 := by
    calc
      Nat.log2 q = Nat.log 2 q := Nat.log2_eq_log_two
      _ = Nat.log 2 (2 ^ (catchupIndex q + 1)) := by
        rw [← catchupIndex_spec hcatch]
      _ = catchupIndex q + 1 := Nat.log_pow (by omega : 1 < 2) _
  have hmono : Nat.log2 q ≤ Nat.log2 i := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right (Nat.le_of_lt hqi)
  omega

theorem catchupIndex_injOn (i : ℕ) :
    Set.InjOn catchupIndex (catchupRounds i) := by
  intro q hq r hr hindex
  have hqCatch := (mem_catchupRounds.mp hq).2
  have hrCatch := (mem_catchupRounds.mp hr).2
  calc
    q = 2 ^ (catchupIndex q + 1) := catchupIndex_spec hqCatch
    _ = 2 ^ (catchupIndex r + 1) := by rw [hindex]
    _ = r := (catchupIndex_spec hrCatch).symm

theorem catchupRounds_card_le_log2 (i : ℕ) :
    (catchupRounds i).card ≤ Nat.log2 i := by
  classical
  have h := Finset.card_le_card_of_injOn
    (s := catchupRounds i) (t := Finset.range (Nat.log2 i)) catchupIndex
    (by
      intro q hq
      apply Finset.mem_coe.mpr
      apply Finset.mem_range.mpr
      exact catchupIndex_lt_log2_of_lt
        (mem_catchupRounds.mp hq).2 (mem_catchupRounds.mp hq).1)
    (catchupIndex_injOn i)
  simpa only [Finset.card_range] using h

theorem adaptiveExceptionalCredits_card_le_log2
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (i : ℕ) :
    (adaptiveExceptionalCredits F O i).card ≤ Nat.log2 i := by
  classical
  apply le_trans
    (Finset.card_le_card_of_injOn
      (firstGeneratorTime (adaptiveGCGOutput F O))
      (s := adaptiveExceptionalCredits F O i)
      (t := catchupRounds i) ?_ ?_)
    (catchupRounds_card_le_log2 i)
  · intro x hx
    change firstGeneratorTime (adaptiveGCGOutput F O) x ∈ catchupRounds i
    rw [mem_catchupRounds]
    have hxCredit := (mem_adaptiveExceptionalCredits.mp hx).1
    obtain ⟨j, hji, hjx, hqj, hqx⟩ :=
      mem_timelyElements_rank_firstGeneratorTime hxCredit
    exact ⟨hqj.trans hji, (mem_adaptiveExceptionalCredits.mp hx).2⟩
  · intro x hx y hy htime
    have hxCredit := (mem_adaptiveExceptionalCredits.mp hx).1
    have hyCredit := (mem_adaptiveExceptionalCredits.mp hy).1
    obtain ⟨_, _, _, _, hxSpec⟩ :=
      mem_timelyElements_rank_firstGeneratorTime hxCredit
    obtain ⟨_, _, _, _, hySpec⟩ :=
      mem_timelyElements_rank_firstGeneratorTime hyCredit
    calc
      x = adaptiveGCGOutput F O
          (firstGeneratorTime (adaptiveGCGOutput F O) x) := hxSpec.symm
      _ = adaptiveGCGOutput F O
          (firstGeneratorTime (adaptiveGCGOutput F O) y) := by rw [htime]
      _ = y := hySpec

/-- Finite turn-taking certificate for the concrete adaptive presentation. -/
theorem adaptive_turnTaking_finite_bound
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (i : ℕ) :
    2 * (timelyElements (adaptiveGCGOutput F O)
        O.enumeration id i).card ≤ i + 2 * Nat.log2 i := by
  classical
  apply turnTaking_finite_upper_bound
    (prefixSet := targetPrefix O.enumeration i)
    (credited := adaptiveCredited F O i)
    (paired := adaptivePairedCredits F O i)
    (exceptions := adaptiveExceptionalCredits F O i)
    (partner := adaptivePartner F O)
    (e := Nat.log2 i)
  · exact targetPrefix_card_ordered O i
  · intro x hx
    obtain ⟨j, hji, rfl, q, hqj, hq⟩ :=
      mem_timelyElements_iff_p30.mp hx
    exact (mem_sequencePrefix_iff O.enumeration (O.enumeration j) i).mpr
      ⟨j, hji, rfl⟩
  · intro x hx
    by_cases hexception : x ∈ adaptiveExceptionalCredits F O i
    · exact Finset.mem_union_right _ hexception
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hx, hexception⟩)
  · exact Finset.sdiff_subset
  · exact adaptiveExceptionalCredits_card_le_log2 F O i
  · exact fun x hx => adaptivePartner_mem_targetPrefix hx
  · exact fun x hx => adaptivePartner_not_mem_credited hx
  · exact adaptivePartner_injOn F O i

theorem catchupRatio_log2_tendsto_zero :
    Tendsto (catchupRatio Nat.log2) atTop (nhds 0) := by
  have heq : catchupRatio Nat.log2 =
      fun n : ℕ => (Nat.log2 n : ℝ) / (n : ℝ) := by
    funext n
    by_cases hn : n = 0 <;> simp [catchupRatio, hn]
  rw [heq]
  exact GenLimit.tendsto_natLog2_div

/-- The concrete adaptive exact presentation forces the repaired GCG's
instance-level timely upper density to be at most one half. -/
theorem adaptive_upperTimelyDensity_le_half
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) :
    upperTimelyDensity (adaptiveGCGOutput F O) O.enumeration id ≤
      (1 / 2 : ℝ) := by
  apply upperTimelyDensity_le_half_of_turnTaking _ _ Nat.log2
  · exact Filter.Eventually.of_forall
      (adaptive_turnTaking_finite_bound F O)
  · exact catchupRatio_log2_tendsto_zero

end GenLimit.TimeSensitive

end

-- UpperBound
section
set_option autoImplicit true

/-! Section 2 of STOC submission 335. An arbitrary deterministic competitor is a
function on finite input histories. At time 2^(j+1), present target rank j if
necessary. On ordinary rounds take the lowest rank unused by either party. -/
namespace DenseSubmission
open GenLimit GenLimit.KleinbergWei GenLimit.TimeSensitive Filter
open scoped Classical
noncomputable section

structure Position where
  inputs : List ℕ
  outputs : Finset ℕ

def Position.used (p : Position) := p.inputs.toFinset ∪ p.outputs

def announcement (O : OrderedLanguage) (p : Position) (t : ℕ) : ℕ :=
  if IsCatchupRound t ∧ O.enumeration (catchupIndex t) ∉ p.inputs then
    O.enumeration (catchupIndex t)
  else leastUnusedTarget O p.used

def play (O : OrderedLanguage) (G : List ℕ → ℕ) : ℕ → Position
  | 0 => ⟨[], ∅⟩
  | t+1 =>
    let p := play O G t
    let h := p.inputs ++ [announcement O p t]
    ⟨h, insert (G h) p.outputs⟩

variable (O : OrderedLanguage) (G : List ℕ → ℕ)

def adv (t : ℕ) := announcement O (play O G t) t
def output (t : ℕ) := G ((List.range (t + 1)).map (adv O G))

theorem play_inputs (t : ℕ) : (play O G t).inputs = (List.range t).map (adv O G) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (play O G t).inputs ++ [adv O G t] = _
    rw [ih, List.range_succ]
    simp

theorem mem_inputs (x t : ℕ) :
    x ∈ (play O G t).inputs ↔ ∃ s < t, adv O G s = x := by
  simp [play_inputs]

theorem mem_outputs (x t : ℕ) :
    x ∈ (play O G t).outputs ↔ ∃ s < t, output O G s = x := by
  induction t with
  | zero => simp [play]
  | succ t ih =>
    have e : G ((play O G t).inputs ++ [adv O G t]) = output O G t := by
      simp [output, play_inputs, List.range_succ]
    change x ∈ insert (G ((play O G t).inputs ++ [adv O G t])) (play O G t).outputs ↔ _
    rw [e, Finset.mem_insert, ih]
    constructor
    · rintro (h | ⟨s, hs, h⟩)
      · exact ⟨t, by omega, h.symm⟩
      · exact ⟨s, by omega, h⟩
    · rintro ⟨s, hs, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hst | rfl
      · exact Or.inr ⟨s, hst, h⟩
      · exact Or.inl h.symm

theorem mem_used (x t : ℕ) :
    x ∈ (play O G t).used ↔
    (∃ s < t, adv O G s = x) ∨ (∃ s < t, output O G s = x) := by
  simp [Position.used, mem_inputs, mem_outputs]

theorem used_mono {s t : ℕ} (hst : s ≤ t) :
    (play O G s).used ⊆ (play O G t).used := by
  intro x hx
  rw [mem_used] at hx ⊢
  rcases hx with ⟨a, ha, e⟩ | ⟨a, ha, e⟩
  · exact Or.inl ⟨a, lt_of_lt_of_le ha hst, e⟩
  · exact Or.inr ⟨a, lt_of_lt_of_le ha hst, e⟩

theorem adv_fresh (t : ℕ) : adv O G t ∉ (play O G t).inputs := by
  unfold adv announcement
  split
  · exact ‹_ ∧ _›.2
  · intro h
    exact leastUnusedTarget_fresh _ _ (Finset.mem_union_left _ (List.mem_toFinset.mpr h))

theorem adv_injective : Function.Injective (adv O G) := by
  intro s t e
  apply le_antisymm
  · exact le_of_not_gt (fun h => adv_fresh O G s ((mem_inputs O G _ _).mpr ⟨t,h,e.symm⟩))
  · exact le_of_not_gt (fun h => adv_fresh O G t ((mem_inputs O G _ _).mpr ⟨s,h,e⟩))

theorem adv_presents : Presents (adv O G) O.carrier := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    unfold adv announcement
    split
    · rw [← O.range_enumeration]; exact ⟨_, rfl⟩
    · exact leastUnusedTarget_mem _ _
  · rw [← O.range_enumeration]
    rintro ⟨j, rfl⟩
    let t := 2 ^ (j + 1)
    have hidx : catchupIndex t = j := catchupIndex_scheduled j
    by_cases h : O.enumeration j ∈ (play O G t).inputs
    · obtain ⟨s, _, hs⟩ := (mem_inputs O G _ _).mp h
      exact ⟨s, hs⟩
    · exact ⟨t, by simp [adv, announcement, hidx, h, show IsCatchupRound t from ⟨j, rfl⟩]⟩

def cutoff (t : ℕ) := leastUnusedTargetRank O (play O G t).used

theorem cut_unused (t : ℕ) : O.enumeration (cutoff O G t) ∉ (play O G t).used :=
  leastUnusedTargetRank_spec _ _

theorem before_cut {j t : ℕ} (hj : j < cutoff O G t) :
    O.enumeration j ∈ (play O G t).used := by
  by_contra h
  exact (not_le_of_gt hj) (leastUnusedTargetRank_min O _ h)

theorem ordinary_rank {s : ℕ} (hs : ¬IsCatchupRound s) :
    adv O G s = O.enumeration (cutoff O G s) := by
  simp [adv, announcement, hs, cutoff, leastUnusedTarget]

theorem ordinary_cut_lt {s t : ℕ} (hst : s < t) (hs : ¬IsCatchupRound s) :
    cutoff O G s < cutoff O G t := by
  have hle : cutoff O G s ≤ cutoff O G t :=
    leastUnusedTargetRank_min O _ (fun h => cut_unused O G t (used_mono O G hst.le h))
  apply lt_of_le_of_ne hle
  intro e
  apply cut_unused O G t
  apply (mem_used O G _ _).mpr
  exact Or.inl ⟨s, hst, (ordinary_rank O G hs).trans (congrArg O.enumeration e)⟩

def owned := GeneratorFirst (adv O G) (output O G)

theorem ordinary_not_owned {s : ℕ} (hs : ¬IsCatchupRound s) : adv O G s ∉ owned O G := by
  rintro ⟨q, hq, hf⟩
  by_cases h : q < s
  · apply cut_unused O G s
    exact (mem_used O G _ _).mpr (Or.inr ⟨q, h, hq.trans (ordinary_rank O G hs)⟩)
  · exact hf s (by omega) rfl

theorem before_cut_owned_time {j t : ℕ} (hj : j < cutoff O G t)
    (ho : O.enumeration j ∈ owned O G) :
    firstGeneratorTime (output O G) (O.enumeration j) < t := by
  obtain ⟨q, hq, hfirst⟩ := ho
  have hqMin := firstGeneratorTime_min ⟨q, hq⟩ hq
  rcases (mem_used O G _ _).mp (before_cut O G hj) with ⟨s, hs, he⟩ | ⟨s, hs, he⟩
  · have : q < s := by
      by_contra! hle
      exact hfirst s hle he
    omega
  · exact (firstGeneratorTime_min ⟨s, he⟩ he).trans_lt hs

theorem count_bounds (t : ℕ) :
    let n := cutoff O G t
    let d := O.prefixCount (owned O G) n
    d ≤ t ∧ t ≤ n - d + Nat.log2 t := by
  classical
  let n := cutoff O G t
  let D := (Finset.range n).filter fun j => O.enumeration j ∈ owned O G
  let A := Finset.range n \ D
  let B := Finset.range t \ catchupRounds t
  have hD : D.card ≤ t := by
    have h := Finset.card_le_card_of_injOn (s := D) (t := Finset.range t)
      (fun j => firstGeneratorTime (output O G) (O.enumeration j)) (by
        intro j hj
        have p := Finset.mem_filter.mp hj
        exact Finset.mem_range.mpr (before_cut_owned_time O G (Finset.mem_range.mp p.1) p.2)) (by
        intro i hi j hj h
        have hr (k : ℕ) (hk : k ∈ D) : O.enumeration k ∈ Set.range (output O G) := by
          obtain ⟨q, hq, _⟩ := (Finset.mem_filter.mp hk).2
          exact ⟨q, hq⟩
        apply O.enumeration_injective
        rw [← firstGeneratorTime_spec (hr i hi), ← firstGeneratorTime_spec (hr j hj)]
        exact congrArg (output O G) h)
    simpa using h
  have hB : B.card ≤ A.card :=
    Finset.card_le_card_of_injOn (cutoff O G) (by
      intro s hs
      obtain ⟨hlt, hnc⟩ := Finset.mem_sdiff.mp hs
      have hst := Finset.mem_range.mp hlt
      have hcatch : ¬IsCatchupRound s := fun h => hnc (mem_catchupRounds.mpr ⟨hst,h⟩)
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_range.mpr (ordinary_cut_lt O G hst hcatch), ?_⟩
      intro hD
      have h := (Finset.mem_filter.mp hD).2
      rw [← ordinary_rank O G hcatch] at h
      exact ordinary_not_owned O G hcatch h) (by
      intro s hs u hu hsu
      have ordinary (v : ℕ) (hv : v ∈ B) : ¬IsCatchupRound v := by
        have p := Finset.mem_sdiff.mp hv
        exact fun h => p.2 (mem_catchupRounds.mpr ⟨Finset.mem_range.mp p.1,h⟩)
      apply adv_injective O G
      rw [ordinary_rank O G (ordinary s hs), ordinary_rank O G (ordinary u hu), hsu])
  have hA := Finset.card_sdiff_add_card_eq_card (show D ⊆ Finset.range n from Finset.filter_subset _ _)
  have hC : catchupRounds t ⊆ Finset.range t := fun _ h =>
    Finset.mem_range.mpr (mem_catchupRounds.mp h).1
  have hT := Finset.card_sdiff_add_card_eq_card hC
  change A.card + D.card = (Finset.range n).card at hA
  change B.card + (catchupRounds t).card = (Finset.range t).card at hT
  rw [Finset.card_range] at hA hT
  have he := catchupRounds_card_le_log2 t
  change D.card ≤ t ∧ t ≤ n - D.card + Nat.log2 t
  omega

/-- Every deterministic competitor admits a legal, repetition-free full enumeration
with relative lower density at most one half, even for an arbitrary target order. -/
theorem ordered_upper_bound : O.lowerDensity (owned O G) ≤ 1 / 2 := by
  by_contra! hlower
  let c : ℝ := (1 / 2 + O.lowerDensity (owned O G)) / 2
  have hhalf : (1 / 2 : ℝ) < c := by dsimp [c]; linarith
  have hc : c < O.lowerDensity (owned O G) := by dsimp [c]; linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_lt_of_lt_liminf hc
      (isBoundedUnder_of ⟨0, O.prefixRatio_nonneg (owned O G)⟩))
  let ε := min (c - 1 / 2) (1 / 2)
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (GenLimit.tendsto_natLog2_div.eventually (gt_mem_nhds hε))
  let t := max T (2 * N + 2)
  have ht : T ≤ t := le_max_left _ _
  have htN : 2 * N + 2 ≤ t := le_max_right _ _
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  let n := cutoff O G t
  let d := O.prefixCount (owned O G) n
  have hd : d ≤ n := O.prefixCount_le _ _
  have ⟨b₁,b₂⟩ := count_bounds O G t
  change d ≤ t at b₁
  change t ≤ n - d + Nat.log2 t at b₂
  have hn₁ : t ≤ n + Nat.log2 t := by omega
  have hn₂ : 2 * d ≤ n + Nat.log2 t := by omega
  have hlog := (div_lt_iff₀ htpos).mp (hT t ht)
  have hlogHalf : (Nat.log2 t : ℝ) < 1/2 * t :=
    hlog.trans_le (mul_le_mul_of_nonneg_right (min_le_right _ _) htpos.le)
  have hnr : (t : ℝ) ≤ n + (Nat.log2 t : ℝ) := by exact_mod_cast hn₁
  have hnHalf : (t : ℝ) / 2 < n := by linarith
  have hN' : (2 : ℝ) * N + 2 ≤ t := by exact_mod_cast htN
  have hNn : N ≤ n := by exact_mod_cast (show (N : ℝ) ≤ n by linarith)
  have hnp : (0 : ℝ) < n := by linarith
  have hnp' : n ≠ 0 := by exact_mod_cast hnp.ne'
  have hcRatio := hN n hNn
  simp only [OrderedLanguage.prefixRatio, hnp', if_false] at hcRatio
  change c < (d : ℝ) / n at hcRatio
  have hcCount := (lt_div_iff₀ hnp).mp hcRatio
  have hdCount : (2 : ℝ) * d ≤ n + (Nat.log2 t : ℝ) := by exact_mod_cast hn₂
  have hlogC : (Nat.log2 t : ℝ) < (c - 1/2) * t :=
    hlog.trans_le (mul_le_mul_of_nonneg_right (min_le_left _ _) htpos.le)
  have hmul := mul_lt_mul_of_pos_left (show (t : ℝ) < 2 * n by linarith)
    (show 0 < c - 1/2 by linarith)
  nlinarith

/-- The ordinary numerical order on an arbitrary infinite language, with the
source's ambient-prefix definition of lower density. -/
theorem deterministic_upper_bound (K : Language) (hK : K.Infinite) (g : List ℕ → ℕ) :
    ∃ a : ℕ → ℕ, Function.Injective a ∧ Presents a K ∧
      liminf (fun n : ℕ =>
        (Nat.count (· ∈ GeneratorFirst a (fun t => g ((List.range (t+1)).map a)) ∩ K) n : ℝ) /
          (Nat.count (· ∈ K) n : ℝ)) atTop ≤ 1 / 2 := by
  let O := OrderedLanguage.increasing K hK
  refine ⟨adv O g, adv_injective O g, adv_presents O g, ?_⟩
  have h := ordered_upper_bound O g
  rw [show O = OrderedLanguage.increasing K hK from rfl,
      OrderedLanguage.increasing_lowerDensity_eq_liminf] at h
  exact h

end
end DenseSubmission

end

-- MissionUpper
section
set_option autoImplicit true

/-! The Section 2 upper bound in the public mission's unmodified definitions. -/

open ActiveLanguageGeneration.Hierarchy Filter GenLimit
open scoped Classical
noncomputable section
namespace DenseLanguageGeneration.PatientScope

private theorem positive_injective : Function.Injective positive :=
  Equiv.pnatEquivNat.symm.injective

private theorem prefixCount_transport (S : Set ℕ+) (n : ℕ) :
    prefixCount S n = Nat.count (fun j => positive j ∈ S) n := by
  classical
  rw [Nat.count_eq_card_filter_range, prefixCount, ambientPrefix, Finset.filter_image,
    Finset.card_image_of_injective _ positive_injective]

private theorem output_transport (G : Generator ℕ+) (a : ℕ → ℕ) (t : ℕ) :
    positive ((G (((List.range (t+1)).map a).map positive)).natPred) =
      outputAt G (positive ∘ a) t := by
  change (Equiv.pnatEquivNat.symm (Equiv.pnatEquivNat _)) = _
  rw [Equiv.symm_apply_apply]
  simp [outputAt, inputHistory, List.map_map]

/-- The right conjunct of the public mission, using its exact positive-integer
ownership and ambient-prefix density. -/
theorem competitor_upper_bound (L : Family) (i : ℕ) (G : Generator ℕ+) :
    ∃ a : ℕ → ℕ+, IsEnumeration (L i) a ∧ lowerDensity G (L i) a ≤ 1 / 2 := by
  classical
  let K : Set ℕ := positive ⁻¹' (L i).val
  have hK : K.Infinite := by
    have h : K = Equiv.pnatEquivNat '' (L i).val := by
      ext j
      change Equiv.pnatEquivNat.symm j ∈ (L i).val ↔ _
      constructor
      · intro h
        exact ⟨Equiv.pnatEquivNat.symm j, h, Equiv.pnatEquivNat.apply_symm_apply j⟩
      · rintro ⟨x,hx,rfl⟩
        simpa using hx
    rw [h]
    exact (L i).property.image Equiv.pnatEquivNat.injective.injOn
  let g : List ℕ → ℕ := fun l => (G (l.map positive)).natPred
  obtain ⟨a, hinj, ha, hbound⟩ := DenseSubmission.deterministic_upper_bound K hK g
  let b := positive ∘ a
  have hren : ∀ x : ℕ+, positive x.natPred = x := PNat.succPNat_natPred
  have henum : IsEnumeration (L i) b := by
    refine ⟨positive_injective.comp hinj, ?_⟩
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      have h : a t ∈ K := by rw [← ha]; exact ⟨t,rfl⟩
      exact h
    · intro hx
      have h : x.natPred ∈ K := by change positive x.natPred ∈ (L i).val; rwa [hren]
      rw [← ha] at h
      obtain ⟨s, hs⟩ := h
      exact ⟨s, (congrArg positive hs).trans (hren x)⟩
  refine ⟨b, henum, ?_⟩
  let y := fun t => g ((List.range (t+1)).map a)
  have hout : ∀ t, positive (y t) = outputAt G b t := output_transport G a
  have howner (j : ℕ) : positive j ∈ defenderOwned G b ↔ j ∈ GeneratorFirst a y := by
    constructor
    · rintro ⟨t,hy,hf⟩
      exact ⟨t,positive_injective ((hout t).trans hy),
        fun s hs e => hf s hs (congrArg positive e)⟩
    · rintro ⟨t,hy,hf⟩
      exact ⟨t,(hout t).symm.trans (congrArg positive hy),
        fun s hs e => hf s hs (positive_injective e)⟩
  have he (n : ℕ) : ratio G (L i) b n =
      (Nat.count (· ∈ GeneratorFirst a y ∩ K) n : ℝ) / (Nat.count (· ∈ K) n : ℝ) := by
    have heq : (fun j => positive j ∈ defenderOwned G b ∩ (L i).val) =
        (fun j => j ∈ GeneratorFirst a y ∩ K) := by
      funext j
      exact propext (and_congr_left fun _ => howner j)
    rw [ratio, prefixCount_transport, prefixCount_transport]
    have count_congr (p q : ℕ → Prop) (d₁ : DecidablePred p) (d₂ : DecidablePred q) (hpq : p = q) :
        @Nat.count p d₁ n = @Nat.count q d₂ n := by
      subst q
      have ed : d₁ = d₂ := Subsingleton.elim _ _
      rw [ed]
    apply congrArg₂ (fun u v : ℕ => (u : ℝ) / (v : ℝ))
    · apply count_congr
      exact heq
    · apply count_congr
      rfl

  change liminf (ratio G (L i) b) atTop ≤ _
  rw [funext he]
  exact hbound

end DenseLanguageGeneration.PatientScope
end

end

-- MissionOptimal
section
set_option autoImplicit true

namespace DenseLanguageGeneration.PatientScope
open ActiveLanguageGeneration.Hierarchy GenLimit.PatientMachine Filter
open scoped Classical
noncomputable section

variable (L : Family) (a : ℕ → ℕ)
local notation "O" => oracle L
local notation "b" => (encode ∘ a)

private theorem owner_transport {i : ℕ} (hp : GenLimit.Presents a ((oracle L).language i)) (x : ℕ) :
    encode x ∈ defenderOwned (generator L) b ↔ x ∈ GenLimit.GeneratorFirst a (output O a) := by
  have hi := Equiv.pnatEquivNat.symm.injective
  constructor
  · rintro ⟨t,ht,hf⟩
    rw [replay_output L a hp t] at ht
    exact ⟨t,hi ht,fun s hs e => hf s hs (congrArg encode e)⟩
  · rintro ⟨t,ht,hf⟩
    exact ⟨t,(replay_output L a hp t).trans (congrArg encode ht),fun s hs e => hf s hs (hi e)⟩

private theorem count_transport (S : Set ℕ+) (n : ℕ) :
    prefixCount S n = GenLimit.PatientScope.prefixCount (encode ⁻¹' S) n := by
  have hi : Function.Injective positive := Equiv.pnatEquivNat.symm.injective
  rw [prefixCount,ambientPrefix,GenLimit.PatientScope.prefixCount,GenLimit.PatientScope.prefixFinset,
    Finset.filter_image,Finset.card_image_of_injective _ hi]
  rfl

theorem density_transport {i : ℕ} (hp : GenLimit.Presents a ((oracle L).language i)) :
    lowerDensity (generator L) (L i) b = patientLowerDensity O a i := by
  classical
  have eq : encode ⁻¹' (defenderOwned (generator L) b ∩ (L i).val) =
      GenLimit.GeneratorFirst a (output O a) ∩ (oracle L).language i := by
    ext x
    exact and_congr_left fun _ => owner_transport L a hp x
  rw [patientLowerDensity, GenLimit.PatientScope.relativeLowerDensity_eq_liminf _ _ _ Set.inter_subset_right]
  apply congrArg (fun f : ℕ → ℝ => liminf f atTop)
  funext n
  simp only [ratio,count_transport,eq]
  rfl

theorem generates_encoded {i : ℕ} (hp : GenLimit.Presents a ((oracle L).language i)) :
    Generates (generator L) (L i) b := by
  obtain ⟨⟨T,h⟩,_⟩ := patientScope_generation_and_lowerDensity O a hp
  refine ⟨T,?_⟩
  intro t ht
  obtain ⟨hx,hin,hout⟩ := h t ht
  change outputAt (generator L) b t ∈ (L i).val ∧ _
  rw [replay_output L a hp t]
  refine ⟨hx,?_⟩
  rintro (⟨s,hs,e⟩ | ⟨s,hs,e⟩)
  · exact hin s hs (Equiv.pnatEquivNat.symm.injective e)
  · rw [replay_output L a hp s] at e
    exact hout s hs (Equiv.pnatEquivNat.symm.injective e)

theorem settled_encoded {i : ℕ} (hp : GenLimit.Presents a ((oracle L).language i)) :
    SettledFrom L i b (settledThreshold O a i hp) := by
  intro t ht
  have cr := settled_target_critical O a i hp ht
  have sc := settled_target_in_scope O a i hp ht
  have fo := run_focus_isFocus O hp t
  refine ⟨(critical_transport L a t i).mpr cr,(replay_agrees L a hp t).scope ▸ sc,?_⟩
  simp only [focusAt,focusSet,(replay_agrees L a hp t).scope, focus_from_critical L a fo]
  intro x hx
  have inj : encode x.natPred = x := Equiv.pnatEquivNat.symm_apply_apply _
  have e : x.natPred ∈ (oracle L).language (run O a t).focus := by
    change encode x.natPred ∈ (L (run O a t).focus).val
    rwa [inj]
  simpa only [oracle,Set.mem_preimage,inj] using (GenLimit.focus_subset_target fo sc cr e)

private theorem encode_decode (c : ℕ → ℕ+) : encode ∘ (Equiv.pnatEquivNat ∘ c) = c := by
  funext n
  exact Equiv.pnatEquivNat.symm_apply_apply (c n)

/-- Lemma 3.12 with the public validity and stabilization predicates. -/
theorem validity (L : Family) (i : ℕ) (a : ℕ → ℕ+) (ha : IsEnumeration (L i) a) :
    Generates (generator L) (L i) a ∧ ∃ T : ℕ, SettledFrom L i a T := by
  let c := Equiv.pnatEquivNat ∘ a
  have hp := decode_presents L ha
  rw [← encode_decode a]
  exact ⟨generates_encoded L c hp, ⟨_,settled_encoded L c hp⟩⟩

/-- Theorem 3.15 with precisely the public mission's operational generator,
its arbitrary-language denominator, and its universal competitor quantifiers. -/
theorem optimal_lower_density :
    (∀ (L : Family) (i : ℕ) (a : ℕ → ℕ+), IsEnumeration (L i) a →
      Generates (generator L) (L i) a ∧ (1/2:ℝ) ≤ lowerDensity (generator L) (L i) a) ∧
    (∀ (L : Family) (i : ℕ) (G : Generator ℕ+), ∃ a : ℕ → ℕ+,
      IsEnumeration (L i) a ∧ lowerDensity G (L i) a ≤ (1/2:ℝ)) := by
  refine ⟨?_,competitor_upper_bound⟩
  intro L i a ha
  let c := Equiv.pnatEquivNat ∘ a
  have hp := decode_presents L ha
  rw [← encode_decode a]
  exact ⟨generates_encoded L c hp,(density_transport L c hp).symm ▸ patientScope_lowerDensity_half (oracle L) c hp⟩

end
end DenseLanguageGeneration.PatientScope

#print axioms DenseLanguageGeneration.PatientScope.validity
#print axioms DenseLanguageGeneration.PatientScope.optimal_lower_density

end

open DenseLanguageGeneration.PatientScope ActiveLanguageGeneration.Hierarchy in
theorem solution (L : Family) (i : ℕ) (a : ℕ → ℕ+)
    (ha : IsEnumeration (L i) a) :
    Generates (generator L) (L i) a ∧ ∃ T : ℕ, SettledFrom L i a T  := DenseLanguageGeneration.PatientScope.validity L i a ha
