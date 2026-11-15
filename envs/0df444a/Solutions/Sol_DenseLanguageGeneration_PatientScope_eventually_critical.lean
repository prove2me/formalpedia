-- Prove2me | solution 1 for DenseLanguageGeneration.PatientScope.eventually_critical
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:23:24.558217+00:00
-- url     : https://prove2.me/submissions/1b6b8732-0f98-4298-9552-c499c166c901

import Definitions.Def_DenseLanguageGeneration_PatientScope_criticalChain
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic

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

open DenseLanguageGeneration.PatientScope ActiveLanguageGeneration.Hierarchy in
theorem solution (L : Family) (i : ℕ) (a : ℕ → ℕ+)
    (ha : IsEnumeration (L i) a) :
    ∃ T : ℕ, ∀ t ≥ T, Critical L (history a t) i  := DenseLanguageGeneration.PatientScope.eventually_critical L i a ha
