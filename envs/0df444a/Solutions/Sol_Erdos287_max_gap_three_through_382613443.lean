-- Prove2me | solution 1 for Erdos287.max_gap_three_through_382613443
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T10:28:02.3539+00:00
-- url     : https://prove2.me/submissions/5db2628c-3c81-445b-a432-cb91977b1b7e

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/- Adapted from Reza Ramji and contributors, erdos-287-lean, commit 2b2ecb1022cc3bfe249d9733003d3488f2d3027f. The modules were joined, the unfolding in P287.Part1 was made explicit for this Lean version, and a mission-format wrapper was added. -/
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

/- Source module P287.Part1. -/
/- ASSEMBLY: `erdos_287.variants.prime_conjecture_implies`, kernel-clean.

Given the prime conjecture (for all large N there is a prime P in [N,2N] with
(P+1)/2 prime), every Egyptian fraction representation of 1 with enough terms has
a gap of at least 3.

Proof.  Let M = s(k-1) and N = M/2.  The hypothesis gives a prime P in [N,2N]
with Q = (P+1)/2 prime.
  * P >= M/2 gives 3P > M, so the multiples of P that are <= M are exactly P and
    2P: `lemA_two` then says NO element is divisible by P, in particular P is not
    a term.
  * Q >= M/4 gives 5Q > M, so the multiples of Q that are <= M lie in
    {Q,2Q,3Q,4Q}: `lemA_four` says no element is divisible by Q, and 2Q = P+1, so
    P+1 is not a term either.
  * n_1 <= M/2 <= P by the counting bound, and P < M because M itself IS a term
    while P is not.  So P and P+1 both lie strictly inside the range.
  * `gap_three_of_two_missing` turns two consecutive missing values into a gap >= 3.

No analysis anywhere: the only inequalities used are counting and divisibility.
-/

namespace PCI

open Finset
variable {p : ℕ}


open Finset

variable {p : ℕ}

/-- A term of negative valuation dominates one of non-negative valuation. -/
theorem val_add_of_neg [Fact (Nat.Prime p)] {x y : ℚ}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x + y ≠ 0)
    (hx : padicValRat p x < 0) (hy : 0 ≤ padicValRat p y) :
    padicValRat p (x + y) = padicValRat p x := by
  have hne : padicValRat p x ≠ padicValRat p y := by omega
  rw [padicValRat.add_eq_min hxy hx0 hy0 hne]
  exact min_eq_left (by omega)

/-- A finite sum of positive rationals of non-negative valuation has non-negative
valuation. -/
theorem val_sum_nonneg [Fact (Nat.Prime p)] {B : Finset ℕ} {f : ℕ → ℚ}
    (hpos : ∀ n ∈ B, 0 < f n) (hval : ∀ n ∈ B, 0 ≤ padicValRat p (f n)) :
    0 ≤ padicValRat p (∑ n ∈ B, f n) := by
  classical
  induction B using Finset.induction with
  | empty => simp
  | insert a B ha ih =>
      have hpos' : ∀ n ∈ B, 0 < f n := fun n hn => hpos n (mem_insert_of_mem hn)
      have hval' : ∀ n ∈ B, 0 ≤ padicValRat p (f n) := fun n hn => hval n (mem_insert_of_mem hn)
      have hsum := ih hpos' hval'
      rw [Finset.sum_insert ha]
      rcases Finset.eq_empty_or_nonempty B with rfl | hB
      · simpa using hval a (mem_insert_self a _)
      · have hBpos : 0 < ∑ n ∈ B, f n := Finset.sum_pos hpos' hB
        have hane : f a ≠ 0 := ne_of_gt (hpos a (mem_insert_self a _))
        have hbne : (∑ n ∈ B, f n) ≠ 0 := ne_of_gt hBpos
        have htot : f a + ∑ n ∈ B, f n ≠ 0 :=
          ne_of_gt (add_pos (hpos a (mem_insert_self a _)) hBpos)
        exact le_trans (le_min (hval a (mem_insert_self a _)) hsum)
          (padicValRat.min_le_padicValRat_add htot)

/-- **Lemma A′, split form.** If the p-divisible part of the sum has valuation −1
and the rest has valuation ≥ 0, the whole sum has valuation −1, hence is not 1. -/
theorem sum_ne_one_of_val_neg [Fact (Nat.Prime p)] {A B : Finset ℕ} {f : ℕ → ℚ}
    (hApos : ∀ n ∈ A, 0 < f n) (hBpos : ∀ n ∈ B, 0 < f n)
    (hA : A.Nonempty)
    (hAval : padicValRat p (∑ n ∈ A, f n) < 0)
    (hBval : ∀ n ∈ B, 0 ≤ padicValRat p (f n)) :
    (∑ n ∈ A, f n) + (∑ n ∈ B, f n) ≠ 1 := by
  classical
  have hApos' : 0 < ∑ n ∈ A, f n := Finset.sum_pos hApos hA
  rcases Finset.eq_empty_or_nonempty B with rfl | hB
  · simp only [Finset.sum_empty, add_zero]
    intro h
    rw [h] at hAval
    simp only [padicValRat.one] at hAval
    omega
  · have hBpos' : 0 < ∑ n ∈ B, f n := Finset.sum_pos hBpos hB
    have hval := val_add_of_neg (p := p) (ne_of_gt hApos') (ne_of_gt hBpos')
      (ne_of_gt (add_pos hApos' hBpos')) hAval (val_sum_nonneg hBpos hBval)
    intro h
    rw [h] at hval
    simp only [padicValRat.one] at hval
    omega


/-- ν_p(a / (b·p)) = −1 when p divides neither a nor b. -/
theorem val_frac [Fact (Nat.Prime p)] {a b : ℕ} (hp : 1 < p)
    (ha : 0 < a) (hb : 0 < b) (hap : ¬ p ∣ a) (hbp : ¬ p ∣ b) :
    padicValRat p ((a : ℚ) / ((b : ℚ) * (p : ℚ))) = -1 := by
  have hpp : (0:ℚ) < p := by positivity
  have hane : (a : ℚ) ≠ 0 := by positivity
  have hbne : (b : ℚ) ≠ 0 := by positivity
  have hpne : (p : ℚ) ≠ 0 := ne_of_gt hpp
  rw [padicValRat.div hane (by positivity), padicValRat.mul hbne hpne,
      padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd hap, padicValNat.eq_zero_of_not_dvd hbp,
      padicValNat.self hp]
  simp

/-- **Lemma A′ for the window {p, 2p}.** If p > 3 and every element of `T`
divisible by p is p or 2p, and at least one such element is present, then the
reciprocals of `T` do not sum to 1.

This is exactly the instance `prime_conjecture_implies` needs for the prime
p ∈ (M/3, M], whose only multiples in the window are p and 2p. -/
theorem lemA_two [Fact (Nat.Prime p)] (hp : 3 < p) {T : Finset ℕ}
    (hTpos : ∀ n ∈ T, 0 < n)
    (hdvd : ∀ n ∈ T, p ∣ n → n = p ∨ n = 2 * p)
    (hex : ∃ n ∈ T, p ∣ n) :
    ∑ n ∈ T, ((n : ℚ))⁻¹ ≠ 1 := by
  classical
  have hp1 : 1 < p := by omega
  have hppos : 0 < p := by omega
  set A := T.filter (fun n => p ∣ n) with hAdef
  set B := T.filter (fun n => ¬ p ∣ n) with hBdef
  have hsplit : (∑ n ∈ A, ((n : ℚ))⁻¹) + (∑ n ∈ B, ((n : ℚ))⁻¹)
      = ∑ n ∈ T, ((n : ℚ))⁻¹ := Finset.sum_filter_add_sum_filter_not T _ _
  -- positivity on both parts
  have hApos : ∀ n ∈ A, (0:ℚ) < ((n : ℚ))⁻¹ := by
    intro n hn
    have h1 := hTpos n (Finset.mem_of_mem_filter n hn)
    have h2 : (0:ℚ) < n := by exact_mod_cast h1
    exact inv_pos.mpr h2
  have hBpos : ∀ n ∈ B, (0:ℚ) < ((n : ℚ))⁻¹ := by
    intro n hn
    have h1 := hTpos n (Finset.mem_of_mem_filter n hn)
    have h2 : (0:ℚ) < n := by exact_mod_cast h1
    exact inv_pos.mpr h2
  -- B has non-negative valuation termwise
  have hBval : ∀ n ∈ B, 0 ≤ padicValRat p ((n : ℚ))⁻¹ := by
    intro n hn
    have hnd : ¬ p ∣ n := (Finset.mem_filter.mp hn).2
    rw [padicValRat.inv, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]
    simp
  -- A is nonempty and contained in {p, 2p}
  obtain ⟨n0, hn0T, hn0d⟩ := hex
  have hAne : A.Nonempty := ⟨n0, Finset.mem_filter.mpr ⟨hn0T, hn0d⟩⟩
  have hAsub : A ⊆ ({p, 2 * p} : Finset ℕ) := by
    intro x hx
    obtain ⟨hxT, hxd⟩ := Finset.mem_filter.mp hx
    rcases hdvd x hxT hxd with rfl | rfl <;> simp
  -- evaluate the p-part: it is 1/p, 1/(2p) or 3/(2p), all of valuation −1
  have hne2 : p ≠ 2 * p := by omega
  have hAval : padicValRat p (∑ n ∈ A, ((n : ℚ))⁻¹) < 0 := by
    have hcases : A = {p} ∨ A = {2 * p} ∨ A = {p, 2 * p} := by
      by_cases h1 : p ∈ A <;> by_cases h2 : 2 * p ∈ A
      · exact Or.inr (Or.inr (Finset.Subset.antisymm hAsub (by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption)))
      · refine Or.inl (Finset.Subset.antisymm ?_ (by simpa using h1))
        intro x hx
        have hx' := hAsub hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx' ⊢
        rcases hx' with rfl | rfl
        · rfl
        · exact absurd hx h2
      · refine Or.inr (Or.inl (Finset.Subset.antisymm ?_ (by simpa using h2)))
        intro x hx
        have hx' := hAsub hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx' ⊢
        rcases hx' with rfl | rfl
        · exact absurd hx h1
        · rfl
      · obtain ⟨x, hx⟩ := hAne
        have hx' := hAsub hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
        rcases hx' with rfl | rfl
        · exact absurd hx h1
        · exact absurd hx h2
    have hpd : ¬ p ∣ 1 := by
      intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    have hpd2 : ¬ p ∣ 2 := by
      intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    have hpd3 : ¬ p ∣ 3 := by
      intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    rcases hcases with h | h | h
    · rw [h, Finset.sum_singleton]
      have : ((p : ℚ))⁻¹ = ((1 : ℕ) : ℚ) / (((1 : ℕ) : ℚ) * (p : ℚ)) := by
        push_cast; ring
      rw [this, val_frac hp1 (by norm_num) (by norm_num) hpd hpd]
      norm_num
    · rw [h, Finset.sum_singleton]
      have hpq : (0:ℚ) < p := by positivity
      have : ((((2 * p : ℕ)) : ℚ))⁻¹ = ((1 : ℕ) : ℚ) / (((2 : ℕ) : ℚ) * (p : ℚ)) := by
        push_cast; ring
      rw [this, val_frac hp1 (by norm_num) (by norm_num) hpd hpd2]
      norm_num
    · rw [h, Finset.sum_pair hne2]
      have hpq : (0:ℚ) < p := by positivity
      have : ((p : ℚ))⁻¹ + ((((2 * p : ℕ)) : ℚ))⁻¹
          = ((3 : ℕ) : ℚ) / (((2 : ℕ) : ℚ) * (p : ℚ)) := by
        push_cast
        field_simp
        ring
      rw [this, val_frac hp1 (by norm_num) (by norm_num) hpd3 hpd2]
      norm_num
  rw [← hsplit]
  exact sum_ne_one_of_val_neg hApos hBpos hAne hAval hBval


/-- **Lemma A′ for the window {p,2p,3p,4p}** — the instance needed for
q = (P+1)/2 in `prime_conjecture_implies`.

The 16 subsets are never enumerated. Clearing denominators by 12p turns each term
into an integer 12/m ∈ {12,6,4,3}, so the p-part equals k/(12p) with k a positive
integer; k ≤ 4·12 = 48 < p because |A| ≤ 4 and every weight is ≤ 12. Then
`val_frac` gives valuation −1. -/
theorem lemA_four [Fact (Nat.Prime p)] (hp : 48 < p) {T : Finset ℕ}
    (hTpos : ∀ n ∈ T, 0 < n)
    (hdvd : ∀ n ∈ T, p ∣ n → n = p ∨ n = 2 * p ∨ n = 3 * p ∨ n = 4 * p)
    (hex : ∃ n ∈ T, p ∣ n) :
    ∑ n ∈ T, ((n : ℚ))⁻¹ ≠ 1 := by
  classical
  have hp1 : 1 < p := by omega
  have hppos : 0 < p := by omega
  have hpQ : (0:ℚ) < p := by exact_mod_cast hppos
  have hpne : (p:ℚ) ≠ 0 := ne_of_gt hpQ
  set A := T.filter (fun n => p ∣ n) with hAdef
  set B := T.filter (fun n => ¬ p ∣ n) with hBdef
  have hsplit : (∑ n ∈ A, ((n : ℚ))⁻¹) + (∑ n ∈ B, ((n : ℚ))⁻¹)
      = ∑ n ∈ T, ((n : ℚ))⁻¹ := Finset.sum_filter_add_sum_filter_not T _ _
  have hApos : ∀ n ∈ A, (0:ℚ) < ((n : ℚ))⁻¹ := by
    intro n hn
    have h1 := hTpos n (Finset.mem_of_mem_filter n hn)
    have h2 : (0:ℚ) < n := by exact_mod_cast h1
    exact inv_pos.mpr h2
  have hBpos : ∀ n ∈ B, (0:ℚ) < ((n : ℚ))⁻¹ := by
    intro n hn
    have h1 := hTpos n (Finset.mem_of_mem_filter n hn)
    have h2 : (0:ℚ) < n := by exact_mod_cast h1
    exact inv_pos.mpr h2
  have hBval : ∀ n ∈ B, 0 ≤ padicValRat p ((n : ℚ))⁻¹ := by
    intro n hn
    have hnd : ¬ p ∣ n := (Finset.mem_filter.mp hn).2
    rw [padicValRat.inv, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]
    simp
  obtain ⟨n0, hn0T, hn0d⟩ := hex
  have hAne : A.Nonempty := ⟨n0, Finset.mem_filter.mpr ⟨hn0T, hn0d⟩⟩
  have hAsub : A ⊆ ({p, 2 * p, 3 * p, 4 * p} : Finset ℕ) := by
    intro x hx
    obtain ⟨hxT, hxd⟩ := Finset.mem_filter.mp hx
    rcases hdvd x hxT hxd with rfl | rfl | rfl | rfl <;> simp
  -- membership in A pins n to one of four values
  have hAcases : ∀ n ∈ A, n = p ∨ n = 2*p ∨ n = 3*p ∨ n = 4*p := by
    intro n hn
    obtain ⟨hxT, hxd⟩ := Finset.mem_filter.mp hn
    exact hdvd n hxT hxd
  -- weights after clearing denominators by 12p; `rw [h]` not `rfl`, so that the
  -- substitution cannot rename the prime `p` itself
  have hw : ∀ x ∈ A, 12 * p / x = 12 ∨ 12 * p / x = 6 ∨ 12 * p / x = 4
      ∨ 12 * p / x = 3 := by
    intro x hx
    rcases hAcases x hx with h | h | h | h
    · exact Or.inl (by rw [h]; exact Nat.mul_div_cancel _ hppos)
    · exact Or.inr (Or.inl (by
        rw [h, show 12 * p = 6 * (2 * p) from by ring]
        exact Nat.mul_div_cancel _ (by omega)))
    · exact Or.inr (Or.inr (Or.inl (by
        rw [h, show 12 * p = 4 * (3 * p) from by ring]
        exact Nat.mul_div_cancel _ (by omega))))
    · exact Or.inr (Or.inr (Or.inr (by
        rw [h, show 12 * p = 3 * (4 * p) from by ring]
        exact Nat.mul_div_cancel _ (by omega))))
  have hterm : ∀ x ∈ A, ((x : ℚ))⁻¹ = ((12 * p / x : ℕ) : ℚ) / (12 * (p:ℚ)) := by
    intro x hx
    have hxpos : 0 < x := hTpos x (Finset.mem_of_mem_filter x hx)
    have hxQ : (0:ℚ) < x := by exact_mod_cast hxpos
    rcases hAcases x hx with h | h | h | h
    · rw [h, show (12 * p / p : ℕ) = 12 from Nat.mul_div_cancel _ hppos]
      push_cast; field_simp
    · rw [h, show (12 * p / (2 * p) : ℕ) = 6 from by
        rw [show 12 * p = 6 * (2 * p) from by ring]
        exact Nat.mul_div_cancel _ (by omega)]
      push_cast; field_simp; ring
    · rw [h, show (12 * p / (3 * p) : ℕ) = 4 from by
        rw [show 12 * p = 4 * (3 * p) from by ring]
        exact Nat.mul_div_cancel _ (by omega)]
      push_cast; field_simp; ring
    · rw [h, show (12 * p / (4 * p) : ℕ) = 3 from by
        rw [show 12 * p = 3 * (4 * p) from by ring]
        exact Nat.mul_div_cancel _ (by omega)]
      push_cast; field_simp; ring
  have hsumA : ∑ n ∈ A, ((n : ℚ))⁻¹
      = ((∑ n ∈ A, (12 * p / n) : ℕ) : ℚ) / (12 * (p:ℚ)) := by
    rw [Finset.sum_congr rfl hterm]
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    push_cast
    ring
  have hwpos : ∀ x ∈ A, 0 < 12 * p / x := by
    intro x hx; rcases hw x hx with h | h | h | h <;> omega
  have hwle : ∀ x ∈ A, 12 * p / x ≤ 12 := by
    intro x hx; rcases hw x hx with h | h | h | h <;> omega
  set k := ∑ n ∈ A, (12 * p / n) with hkdef
  have hkpos : 0 < k := Finset.sum_pos hwpos hAne
  have hcard : A.card ≤ 4 := by
    refine le_trans (Finset.card_le_card hAsub) ?_
    exact le_trans (Finset.card_insert_le _ _) (by
      refine Nat.succ_le_succ ?_
      exact le_trans (Finset.card_insert_le _ _) (by
        refine Nat.succ_le_succ ?_
        exact le_trans (Finset.card_insert_le _ _) (by simp)))
  have hkle : k ≤ 48 := by
    calc k ≤ A.card * 12 := Finset.sum_le_card_nsmul A _ 12 hwle
      _ ≤ 4 * 12 := by exact Nat.mul_le_mul_right _ hcard
      _ = 48 := by norm_num
  have hpk : ¬ p ∣ k := by
    intro h
    have := Nat.le_of_dvd hkpos h
    omega
  have hp12 : ¬ p ∣ 12 := by
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hAval : padicValRat p (∑ n ∈ A, ((n : ℚ))⁻¹) < 0 := by
    rw [hsumA]
    have : ((k:ℕ) : ℚ) / (12 * (p:ℚ)) = ((k:ℕ) : ℚ) / (((12:ℕ):ℚ) * (p:ℚ)) := by
      push_cast; ring
    rw [this, val_frac hp1 hkpos (by norm_num) hpk hp12]
    norm_num
  rw [← hsplit]
  exact sum_ne_one_of_val_neg hApos hBpos hAne hAval hBval



/-- `max_gap` byte-identical to FormalConjectures/ErdosProblems/287.lean. -/
def max_gap (k : ℕ) (s : Fin k → ℕ ) : ℕ  :=
   Finset.sup Finset.univ (fun i : Fin (k - 1) =>
      s  ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)

theorem gap_three_of_two_missing {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    {m : ℕ}
    (hlo : s ⟨0, by omega⟩ ≤ m) (hhi : m + 1 ≤ s ⟨k - 1, by omega⟩)
    (hm : ∀ i, s i ≠ m) (hm1 : ∀ i, s i ≠ m + 1) :
    3 ≤ max_gap k s := by
  classical
  set I := Finset.univ.filter (fun i : Fin k => s i < m) with hIdef
  have h0mem : (⟨0, by omega⟩ : Fin k) ∈ I := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases lt_or_eq_of_le hlo with h | h
    · exact h
    · exact absurd h (hm _)
  have hIne : I.Nonempty := ⟨_, h0mem⟩
  have hjmem : I.max' hIne ∈ I := I.max'_mem hIne
  have hjlt : s (I.max' hIne) < m := (Finset.mem_filter.mp hjmem).2
  -- the maximiser is not the final index
  have hjlast : ((I.max' hIne : Fin k) : ℕ) + 1 < k := by
    by_contra hcon
    push_neg at hcon
    have hval : ((I.max' hIne : Fin k) : ℕ) = k - 1 := by
      have := (I.max' hIne).isLt; omega
    have heq : (I.max' hIne : Fin k) = (⟨k - 1, by omega⟩ : Fin k) := Fin.ext hval
    rw [heq] at hjlt
    omega
  -- its successor is at least m + 2
  have hj'notmem : (⟨((I.max' hIne : Fin k) : ℕ) + 1, hjlast⟩ : Fin k) ∉ I := by
    intro hmem
    have hle := Finset.le_max' I _ hmem
    rw [Fin.le_def] at hle
    simp only at hle
    omega
  have hj'ge : m ≤ s ⟨((I.max' hIne : Fin k) : ℕ) + 1, hjlast⟩ := by
    by_contra hcon
    push_neg at hcon
    exact hj'notmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)
  have hj'ge2 : m + 2 ≤ s ⟨((I.max' hIne : Fin k) : ℕ) + 1, hjlast⟩ := by
    have h1 := hm ⟨((I.max' hIne : Fin k) : ℕ) + 1, hjlast⟩
    have h2 := hm1 ⟨((I.max' hIne : Fin k) : ℕ) + 1, hjlast⟩
    omega
  -- that gap is one of the terms of the sup
  have hidx : ((I.max' hIne : Fin k) : ℕ) < k - 1 := by omega
  have hterm : s ⟨((I.max' hIne : Fin k) : ℕ) + 1, hjlast⟩ - s (I.max' hIne)
      ≤ max_gap k s := by
    have := Finset.le_sup (f := fun i : Fin (k - 1) =>
      s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)
      (Finset.mem_univ (⟨((I.max' hIne : Fin k) : ℕ), hidx⟩ : Fin (k - 1)))
    simpa [max_gap] using this
  omega

/-- **n₁ ≤ M/2, by counting — no analysis.**
1 = Σ 1/sᵢ < k/s₀ strictly (every later term is smaller, and k ≥ 2), so s₀ < k;
and strict monotonicity gives s(k-1) ≥ s₀ + (k-1). Hence 2·s₀ ≤ s(k-1). -/
theorem two_mul_first_le_last {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (hpos : 0 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1) :
    2 * s ⟨0, by omega⟩ ≤ s ⟨k - 1, by omega⟩ := by
  classical
  have h0 : (0:ℚ) < (s ⟨0, by omega⟩ : ℚ) := by exact_mod_cast hpos
  -- strict monotonicity forces linear growth
  have hgrow : ∀ (i : ℕ) (h : i < k), s ⟨0, by omega⟩ + i ≤ s ⟨i, h⟩ := by
    intro i
    induction i with
    | zero => intro h; simp
    | succ n ih =>
        intro h
        have hn : n < k := by omega
        have hstep : s ⟨n, hn⟩ < s ⟨n + 1, h⟩ := by
          apply hmono; simp [Fin.lt_def]
        have := ih hn
        omega
  -- every term is ≤ 1/s₀, and the term at index 1 is strictly smaller
  have hle : ∀ i ∈ Finset.univ, ((s i : ℚ))⁻¹ ≤ ((s ⟨0, by omega⟩ : ℚ))⁻¹ := by
    intro i _
    have hmono' : s ⟨0, by omega⟩ ≤ s i := by
      rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
      · have : i = (⟨0, by omega⟩ : Fin k) := Fin.ext h
        rw [this]
      · exact le_of_lt (hmono (by simp [Fin.lt_def]; omega))
    have h1 : (0:ℚ) < (s i : ℚ) := by
      have : 0 < s i := lt_of_lt_of_le hpos hmono'
      exact_mod_cast this
    have : (s ⟨0, by omega⟩ : ℚ) ≤ (s i : ℚ) := by exact_mod_cast hmono'
    gcongr
  have hone : ∃ i ∈ Finset.univ, ((s i : ℚ))⁻¹ < ((s ⟨0, by omega⟩ : ℚ))⁻¹ := by
    refine ⟨⟨1, by omega⟩, Finset.mem_univ _, ?_⟩
    have hlt : s ⟨0, by omega⟩ < s ⟨1, by omega⟩ := by
      apply hmono; simp [Fin.lt_def]
    have h1 : (0:ℚ) < (s ⟨1, by omega⟩ : ℚ) := by
      have : 0 < s ⟨1, by omega⟩ := lt_trans hpos hlt
      exact_mod_cast this
    have : (s ⟨0, by omega⟩ : ℚ) < (s ⟨1, by omega⟩ : ℚ) := by exact_mod_cast hlt
    gcongr
  have hsumlt : (1:ℚ) < (k : ℚ) * ((s ⟨0, by omega⟩ : ℚ))⁻¹ := by
    rw [← hsum]
    calc ∑ i : Fin k, ((s i : ℚ))⁻¹
        < ∑ _i : Fin k, ((s ⟨0, by omega⟩ : ℚ))⁻¹ := Finset.sum_lt_sum hle hone
      _ = (k : ℚ) * ((s ⟨0, by omega⟩ : ℚ))⁻¹ := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- hence s₀ < k
  have hs0k : s ⟨0, by omega⟩ < k := by
    have hkey : (s ⟨0, by omega⟩ : ℚ) < (k : ℚ) := by
      have h1 : (1:ℚ) * (s ⟨0, by omega⟩ : ℚ)
          < ((k : ℚ) * ((s ⟨0, by omega⟩ : ℚ))⁻¹) * (s ⟨0, by omega⟩ : ℚ) :=
        by exact mul_lt_mul_of_pos_right hsumlt h0
      rw [one_mul, inv_mul_cancel_right₀ (ne_of_gt h0)] at h1
      exact h1
    exact_mod_cast hkey
  have hlast := hgrow (k - 1) (by omega)
  omega


/-! ### helpers -/

/-- Strict monotonicity forces linear growth from the first term. -/
theorem growth {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s) :
    ∀ (i : ℕ) (h : i < k), s ⟨0, by omega⟩ + i ≤ s ⟨i, h⟩ := by
  intro i
  induction i with
  | zero => intro h; simp
  | succ n ih =>
      intro h
      have hn : n < k := by omega
      have hstep : s ⟨n, hn⟩ < s ⟨n + 1, h⟩ := by apply hmono; simp [Fin.lt_def]
      have := ih hn
      omega


end PCI

/- Source module P287.LemAGenMod. -/
/- LEMMA A′ IN GENERAL: any multiplier window {p, 2p, …, tp}.

`lemA_two` and `lemA_four` were the windows t = 2 and t = 4, each proved by its own
case analysis.  This subsumes both, for every t at once, with no case analysis at
all — the denominator-clearing argument never needed the window to be fixed.

Setup: p prime, T a finite set of positive integers whose p-divisible elements all
have the form m·p with 1 ≤ m ≤ t, at least one of them present.  Put
L = t! (any common multiple of 1..t works; t! keeps the Lean trivial — the sharp
choice lcm(1,…,t) ≈ e^t would give the tighter threshold t ≲ ln p rather than
t ≲ ln p / ln ln p).  For n = m·p in the p-part, L·p/n = L/m is an INTEGER (m ∣ L), so
the p-part equals k/(L·p) with

        k = Σ L/m,      0 < k ≤ |A|·L ≤ t·L.

Hence if p > t·L, then p divides neither k nor L, the p-part has valuation −1, and
by ultrametricity the whole sum has valuation −1 ≠ 0 = v_p(1).

Side condition p > t·t!.  With lcm(1,…,t) in place of t! this is exactly the
A(M) ≈ ln M threshold measured in attempts/008-conditional/window.py.
-/

namespace LemAGen

open Finset

variable {p : ℕ}

theorem val_add_of_neg [Fact (Nat.Prime p)] {x y : ℚ}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x + y ≠ 0)
    (hx : padicValRat p x < 0) (hy : 0 ≤ padicValRat p y) :
    padicValRat p (x + y) = padicValRat p x := by
  have hne : padicValRat p x ≠ padicValRat p y := by omega
  rw [padicValRat.add_eq_min hxy hx0 hy0 hne]
  exact min_eq_left (by omega)

theorem val_sum_nonneg [Fact (Nat.Prime p)] {B : Finset ℕ} {f : ℕ → ℚ}
    (hpos : ∀ n ∈ B, 0 < f n) (hval : ∀ n ∈ B, 0 ≤ padicValRat p (f n)) :
    0 ≤ padicValRat p (∑ n ∈ B, f n) := by
  classical
  induction B using Finset.induction with
  | empty => simp
  | insert a B ha ih =>
      have hpos' : ∀ n ∈ B, 0 < f n := fun n hn => hpos n (mem_insert_of_mem hn)
      have hval' : ∀ n ∈ B, 0 ≤ padicValRat p (f n) := fun n hn =>
        hval n (mem_insert_of_mem hn)
      have hsum := ih hpos' hval'
      rw [Finset.sum_insert ha]
      rcases Finset.eq_empty_or_nonempty B with rfl | hB
      · simpa using hval a (mem_insert_self a _)
      · have hBpos : 0 < ∑ n ∈ B, f n := Finset.sum_pos hpos' hB
        have htot : f a + ∑ n ∈ B, f n ≠ 0 :=
          ne_of_gt (add_pos (hpos a (mem_insert_self a _)) hBpos)
        exact le_trans (le_min (hval a (mem_insert_self a _)) hsum)
          (padicValRat.min_le_padicValRat_add htot)

theorem sum_ne_one_of_val_neg [Fact (Nat.Prime p)] {A B : Finset ℕ} {f : ℕ → ℚ}
    (hApos : ∀ n ∈ A, 0 < f n) (hBpos : ∀ n ∈ B, 0 < f n) (hA : A.Nonempty)
    (hAval : padicValRat p (∑ n ∈ A, f n) < 0)
    (hBval : ∀ n ∈ B, 0 ≤ padicValRat p (f n)) :
    (∑ n ∈ A, f n) + (∑ n ∈ B, f n) ≠ 1 := by
  classical
  have hApos' : 0 < ∑ n ∈ A, f n := Finset.sum_pos hApos hA
  rcases Finset.eq_empty_or_nonempty B with rfl | hB
  · simp only [Finset.sum_empty, add_zero]
    intro h
    rw [h] at hAval
    simp only [padicValRat.one] at hAval
    omega
  · have hBpos' : 0 < ∑ n ∈ B, f n := Finset.sum_pos hBpos hB
    have hval := val_add_of_neg (p := p) (ne_of_gt hApos') (ne_of_gt hBpos')
      (ne_of_gt (add_pos hApos' hBpos')) hAval (val_sum_nonneg hBpos hBval)
    intro h
    rw [h] at hval
    simp only [padicValRat.one] at hval
    omega

theorem val_frac [Fact (Nat.Prime p)] {a b : ℕ} (hp : 1 < p)
    (ha : 0 < a) (hb : 0 < b) (hap : ¬ p ∣ a) (hbp : ¬ p ∣ b) :
    padicValRat p ((a : ℚ) / ((b : ℚ) * (p : ℚ))) = -1 := by
  have hpp : (0:ℚ) < p := by positivity
  have hane : (a : ℚ) ≠ 0 := by positivity
  have hbne : (b : ℚ) ≠ 0 := by positivity
  rw [padicValRat.div hane (by positivity), padicValRat.mul hbne (ne_of_gt hpp),
      padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd hap, padicValNat.eq_zero_of_not_dvd hbp,
      padicValNat.self hp]
  simp

/-- **Lemma A′, general window.** -/
theorem lemA_gen {t : ℕ} [Fact (Nat.Prime p)] (ht : 1 ≤ t)
    (hp : t * (Nat.factorial t) < p)
    {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n)
    (hdvd : ∀ n ∈ T, p ∣ n → ∃ m, 1 ≤ m ∧ m ≤ t ∧ n = m * p)
    (hex : ∃ n ∈ T, p ∣ n) :
    ∑ n ∈ T, ((n : ℚ))⁻¹ ≠ 1 := by
  classical
  set L := Nat.factorial t with hLdef
  have hLpos : 0 < L := Nat.factorial_pos t
  have hp1 : 1 < p := by
    have : 1 ≤ t * L := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hppos : 0 < p := by omega
  have hpQ : (0:ℚ) < p := by exact_mod_cast hppos
  set A := T.filter (fun n => p ∣ n) with hAdef
  set B := T.filter (fun n => ¬ p ∣ n) with hBdef
  have hsplit : (∑ n ∈ A, ((n : ℚ))⁻¹) + (∑ n ∈ B, ((n : ℚ))⁻¹)
      = ∑ n ∈ T, ((n : ℚ))⁻¹ := Finset.sum_filter_add_sum_filter_not T _ _
  have hApos : ∀ n ∈ A, (0:ℚ) < ((n : ℚ))⁻¹ := by
    intro n hn
    have h1 := hTpos n (Finset.mem_of_mem_filter n hn)
    have h2 : (0:ℚ) < n := by exact_mod_cast h1
    exact inv_pos.mpr h2
  have hBpos : ∀ n ∈ B, (0:ℚ) < ((n : ℚ))⁻¹ := by
    intro n hn
    have h1 := hTpos n (Finset.mem_of_mem_filter n hn)
    have h2 : (0:ℚ) < n := by exact_mod_cast h1
    exact inv_pos.mpr h2
  have hBval : ∀ n ∈ B, 0 ≤ padicValRat p ((n : ℚ))⁻¹ := by
    intro n hn
    have hnd : ¬ p ∣ n := (Finset.mem_filter.mp hn).2
    rw [padicValRat.inv, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]
    simp
  obtain ⟨n0, hn0T, hn0d⟩ := hex
  have hAne : A.Nonempty := ⟨n0, Finset.mem_filter.mpr ⟨hn0T, hn0d⟩⟩
  have hAcases : ∀ n ∈ A, ∃ m, 1 ≤ m ∧ m ≤ t ∧ n = m * p := by
    intro n hn
    obtain ⟨hnT, hnd⟩ := Finset.mem_filter.mp hn
    exact hdvd n hnT hnd
  -- every element of A lies in the image of {1,…,t} under (· * p)
  have hAsub : A ⊆ (Finset.Icc 1 t).image (fun m => m * p) := by
    intro n hn
    obtain ⟨m, hm1, hmt, rfl⟩ := hAcases n hn
    exact Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr ⟨hm1, hmt⟩, rfl⟩
  have hcard : A.card ≤ t := by
    refine le_trans (Finset.card_le_card hAsub) ?_
    refine le_trans (Finset.card_image_le) ?_
    simp [Nat.card_Icc]
  -- the cleared weight of each element
  have hw : ∀ n ∈ A, 0 < L * p / n ∧ L * p / n ≤ L
      ∧ ((n : ℚ))⁻¹ = ((L * p / n : ℕ) : ℚ) / ((L:ℚ) * (p:ℚ)) := by
    intro n hn
    obtain ⟨m, hm1, hmt, rfl⟩ := hAcases n hn
    have hmL : m ∣ L := Nat.dvd_factorial hm1 hmt
    have hmpos : 0 < m := hm1
    have hdiv : L * p / (m * p) = L / m := by
      rw [Nat.mul_div_mul_right _ _ hppos]
    have hLm : L / m * m = L := Nat.div_mul_cancel hmL
    refine ⟨?_, ?_, ?_⟩
    · rw [hdiv]; exact Nat.div_pos (Nat.le_of_dvd hLpos hmL) hmpos
    · rw [hdiv]; exact Nat.div_le_self _ _
    · rw [hdiv]
      have hmQ : (0:ℚ) < m := by exact_mod_cast hmpos
      have hcast : ((L / m : ℕ) : ℚ) = (L:ℚ) / (m:ℚ) := by
        rw [eq_div_iff (ne_of_gt hmQ)]
        exact_mod_cast hLm
      rw [hcast]
      have hLQ : (0:ℚ) < L := by exact_mod_cast hLpos
      push_cast
      field_simp
  have hterm : ∀ n ∈ A, ((n : ℚ))⁻¹ = ((L * p / n : ℕ) : ℚ) / ((L:ℚ) * (p:ℚ)) :=
    fun n hn => (hw n hn).2.2
  have hsumA : ∑ n ∈ A, ((n : ℚ))⁻¹
      = ((∑ n ∈ A, (L * p / n) : ℕ) : ℚ) / ((L:ℚ) * (p:ℚ)) := by
    rw [Finset.sum_congr rfl hterm]
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    push_cast
    ring
  set k := ∑ n ∈ A, (L * p / n) with hkdef
  have hkpos : 0 < k := Finset.sum_pos (fun n hn => (hw n hn).1) hAne
  have hkle : k ≤ t * L := by
    calc k ≤ A.card * L := Finset.sum_le_card_nsmul A _ L (fun n hn => (hw n hn).2.1)
      _ ≤ t * L := Nat.mul_le_mul_right _ hcard
  have hpk : ¬ p ∣ k := by
    intro h; have := Nat.le_of_dvd hkpos h; omega
  have hpL : ¬ p ∣ L := by
    intro h
    have := Nat.le_of_dvd hLpos h
    have : 1 * L ≤ t * L := Nat.mul_le_mul_right _ ht
    omega
  have hAval : padicValRat p (∑ n ∈ A, ((n : ℚ))⁻¹) < 0 := by
    rw [hsumA, val_frac hp1 hkpos hLpos hpk hpL]
    norm_num
  rw [← hsplit]
  exact sum_ne_one_of_val_neg hApos hBpos hAne hAval hBval


end LemAGen

/- Source module P287.RuleB. -/
/- RULE B: the unique q-adic maximiser is not a term.

If `q^e ≤ M < 2·q^e` then `q^e` is the ONLY element of `[1, M]` whose q-adic
valuation reaches `e`: anything else divisible by `q^e` is at least `2q^e > M`.
Clearing denominators therefore leaves exactly one term coprime to `q` while the
total, `1`, is not — so `q^e` cannot be a term.

At `e = 1` this is Lemma A′ at `t = 1`; only `e ≥ 2` is new, and that is exactly
what the small-M end of the ladder needs (the prime powers 8, 16, 25, 32). Rule A
alone leaves the residue {9,10,11,21,22,23,33,…,38} uncovered.

The three helper lemmas here generalise `LemAGen.val_add_of_neg`,
`val_sum_nonneg` and `sum_ne_one_of_val_neg`, which all assume the non-exceptional
terms have valuation ≥ 0. Here they have valuation ≥ 1 - e, which is negative once
e ≥ 2, so the comparison has to be against the exceptional term's own valuation
rather than against zero.
-/

namespace RuleB

open Finset

variable {p : ℕ}

/-- Ultrametricity: a strictly smallest valuation wins, with no reference to 0. -/
theorem val_add_of_lt [Fact (Nat.Prime p)] {x y : ℚ}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x + y ≠ 0)
    (hlt : padicValRat p x < padicValRat p y) :
    padicValRat p (x + y) = padicValRat p x := by
  have hne : padicValRat p x ≠ padicValRat p y := by omega
  rw [padicValRat.add_eq_min hxy hx0 hy0 hne]
  exact min_eq_left (by omega)

/-- A sum of positive terms all of valuation ≥ c has valuation ≥ c, for c ≤ 0. -/
theorem val_sum_ge [Fact (Nat.Prime p)] {B : Finset ℕ} {f : ℕ → ℚ} {c : ℤ}
    (hc : c ≤ 0) (hpos : ∀ n ∈ B, 0 < f n) (hval : ∀ n ∈ B, c ≤ padicValRat p (f n)) :
    c ≤ padicValRat p (∑ n ∈ B, f n) := by
  classical
  induction B using Finset.induction with
  | empty => simpa using hc
  | insert a B ha ih =>
      have hpos' : ∀ n ∈ B, 0 < f n := fun n hn => hpos n (mem_insert_of_mem hn)
      have hval' : ∀ n ∈ B, c ≤ padicValRat p (f n) := fun n hn =>
        hval n (mem_insert_of_mem hn)
      have hsum := ih hpos' hval'
      rw [Finset.sum_insert ha]
      rcases Finset.eq_empty_or_nonempty B with rfl | hB
      · simpa using hval a (mem_insert_self a _)
      · have hBpos : 0 < ∑ n ∈ B, f n := Finset.sum_pos hpos' hB
        have htot : f a + ∑ n ∈ B, f n ≠ 0 :=
          ne_of_gt (add_pos (hpos a (mem_insert_self a _)) hBpos)
        exact le_trans (le_min (hval a (mem_insert_self a _)) hsum)
          (padicValRat.min_le_padicValRat_add htot)

/-- If one block has valuation `c < 0` and every other term beats it strictly,
the total cannot be `1`. -/
theorem sum_ne_one_of_val_lt [Fact (Nat.Prime p)] {A B : Finset ℕ} {f : ℕ → ℚ} {c : ℤ}
    (hApos : ∀ n ∈ A, 0 < f n) (hBpos : ∀ n ∈ B, 0 < f n) (hA : A.Nonempty)
    (hAval : padicValRat p (∑ n ∈ A, f n) = c) (hc : c < 0)
    (hBval : ∀ n ∈ B, c < padicValRat p (f n)) :
    (∑ n ∈ A, f n) + (∑ n ∈ B, f n) ≠ 1 := by
  classical
  have hApos' : 0 < ∑ n ∈ A, f n := Finset.sum_pos hApos hA
  rcases Finset.eq_empty_or_nonempty B with rfl | hB
  · simp only [Finset.sum_empty, add_zero]
    intro h
    rw [h] at hAval
    simp only [padicValRat.one] at hAval
    omega
  · have hBpos' : 0 < ∑ n ∈ B, f n := Finset.sum_pos hBpos hB
    have hBge : c + 1 ≤ padicValRat p (∑ n ∈ B, f n) :=
      val_sum_ge (by omega) hBpos (fun n hn => by have := hBval n hn; omega)
    have hlt : padicValRat p (∑ n ∈ A, f n) < padicValRat p (∑ n ∈ B, f n) := by
      omega
    have hval := val_add_of_lt (p := p) (ne_of_gt hApos') (ne_of_gt hBpos')
      (ne_of_gt (add_pos hApos' hBpos')) hlt
    intro h
    rw [h] at hval
    simp only [padicValRat.one] at hval
    omega

/-- **Rule B.** `q^e` is the unique element of `[1,M]` of maximal `q`-adic
valuation as soon as `M < 2·q^e`, and therefore is not a term. -/
theorem ruleB {q e M : ℕ} [Fact (Nat.Prime q)] (he : 1 ≤ e)
    {T : Finset ℕ} (hTpos : ∀ n ∈ T, 0 < n) (hTle : ∀ n ∈ T, n ≤ M)
    (hhi : M < 2 * q ^ e)
    (hsum : ∑ n ∈ T, ((n : ℚ))⁻¹ = 1) :
    q ^ e ∉ T := by
  classical
  intro hx
  have hq : Nat.Prime q := Fact.out
  have hq1 : 1 < q := hq.one_lt
  have hxpos : 0 < q ^ e := pow_pos (by omega) e
  -- the valuation of the exceptional term
  have hpvx : padicValNat q (q ^ e) = e := by
    first
    | exact padicValNat.prime_pow_self q e
    | exact padicValNat.prime_pow e
    | simp
  -- every other term has strictly smaller q-adic valuation
  have hother : ∀ n ∈ T.erase (q ^ e), padicValNat q n < e := by
    intro n hn
    obtain ⟨hne, hnT⟩ := Finset.mem_erase.mp hn
    by_contra hc
    push_neg at hc
    have hdvd : q ^ e ∣ n :=
      dvd_trans (pow_dvd_pow q hc) (pow_padicValNat_dvd)
    obtain ⟨j, hj⟩ := hdvd
    have hnpos := hTpos n hnT
    have hnle := hTle n hnT
    have hj2 : 2 ≤ j := by
      rcases Nat.lt_or_ge j 2 with h | h
      · interval_cases j <;> simp_all <;> omega
      · exact h
    have : q ^ e * 2 ≤ q ^ e * j := Nat.mul_le_mul_left _ hj2
    omega
  -- split off the exceptional term and compare valuations
  have hsplit : ((q ^ e : ℕ) : ℚ)⁻¹ + ∑ n ∈ T.erase (q ^ e), ((n : ℚ))⁻¹
      = ∑ n ∈ T, ((n : ℚ))⁻¹ := by
    first
    | exact Finset.add_sum_erase T _ hx
    | exact Finset.add_sum_erase _ _ hx
    | simp [Finset.add_sum_erase, hx]
  refine sum_ne_one_of_val_lt (p := q) (A := ({q ^ e} : Finset ℕ))
    (B := T.erase (q ^ e)) (f := fun n => ((n : ℚ))⁻¹) (c := -(e : ℤ))
    ?_ ?_ ⟨q ^ e, Finset.mem_singleton_self _⟩ ?_ (by omega) ?_ ?_
  · intro n hn
    rw [Finset.mem_singleton] at hn
    subst hn
    have : (0:ℚ) < ((q ^ e : ℕ) : ℚ) := by exact_mod_cast hxpos
    exact inv_pos.mpr this
  · intro n hn
    have := hTpos n (Finset.mem_of_mem_erase hn)
    have h2 : (0:ℚ) < (n : ℚ) := by exact_mod_cast this
    exact inv_pos.mpr h2
  · rw [Finset.sum_singleton, padicValRat.inv, padicValRat.of_nat, hpvx]
  · intro n hn
    have hlt := hother n hn
    have hnpos := hTpos n (Finset.mem_of_mem_erase hn)
    have h2 : (0:ℚ) < (n : ℚ) := by exact_mod_cast hnpos
    rw [padicValRat.inv, padicValRat.of_nat]
    omega
  · rw [Finset.sum_singleton, hsplit]
    exact hsum


end RuleB

/- Source module P287.StepAB. -/
/- Rungs that may use EITHER exclusion rule on either side.

`StepA.step_gap` fixes both exclusions to be rule A (Lemma A′ at a prime factor).
That is enough for every M ≥ 39, but the residue {9,10,11,21,22,23,33,…,38} needs
rule B (`RuleB.ruleB`, the unique q-adic maximiser) at the prime powers 8, 16, 25,
32. So the rung is split into three reusable pieces:

  `setup`        — the Finset of terms, with positivity, the bound by M, and the sum;
  `notTermA` / `notTermB` — one exclusion each, in the form `∀ i, s i ≠ n`;
  `gap_of_excl`  — the glue: two consecutive excluded interior values give a gap ≥ 3.

Interiority still uses only the counting bound `2·n₁ ≤ M`.
-/

namespace StepAB

open Finset

theorem setup {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1) :
    (∀ x ∈ Finset.image s Finset.univ, 0 < x) ∧
    (∀ x ∈ Finset.image s Finset.univ, x ≤ s ⟨k - 1, by omega⟩) ∧
    (∑ x ∈ Finset.image s Finset.univ, ((x : ℚ))⁻¹ = 1) := by
  classical
  have hmono_le : ∀ i : Fin k, s ⟨0, by omega⟩ ≤ s i := by
    intro i
    rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
    · have : i = (⟨0, by omega⟩ : Fin k) := Fin.ext h
      rw [this]
    · exact le_of_lt (hmono (by simp [Fin.lt_def]; omega))
  have hle_last : ∀ i : Fin k, s i ≤ s ⟨k - 1, by omega⟩ := by
    intro i
    rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt i.isLt) with h | h
    · have : i = (⟨k - 1, by omega⟩ : Fin k) := Fin.ext h
      rw [this]
    · exact le_of_lt (hmono (by simp [Fin.lt_def]; omega))
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    have := hmono_le i; omega
  · intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    have := hle_last i; omega
  · rw [Finset.sum_image (hmono.injective.injOn)]; exact hsum

/-- Rule A: `n` is not a term, because some prime `p ∣ n` satisfies Lemma A′. -/
theorem notTermA {p t n : ℕ} (hp : Nat.Prime p) (ht : 1 ≤ t)
    (hpf : t * Nat.factorial t < p) {a : ℕ} (hna : n = a * p)
    {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hhi : s ⟨k - 1, by omega⟩ < (t + 1) * p) :
    ∀ i, s i ≠ n := by
  classical
  obtain ⟨hTpos, hTle, hsumT⟩ := setup hk s hmono h1 hsum
  have hno : ¬ ∃ x ∈ Finset.image s Finset.univ, p ∣ x := by
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    intro hex
    refine LemAGen.lemA_gen (p := p) (t := t) ht hpf hTpos ?_ hex hsumT
    intro x hx hdvd
    obtain ⟨j, hj⟩ := hdvd
    have hxle := hTle x hx
    have hxpos := hTpos x hx
    have hjt : j ≤ t := by
      by_contra hc
      push_neg at hc
      have hmul : p * (t + 1) ≤ p * j := Nat.mul_le_mul_left _ hc
      have e1 : p * (t + 1) = (t + 1) * p := Nat.mul_comm _ _
      omega
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hpp
      · simp at hj; omega
      · exact hpp
    exact ⟨j, hj1, hjt, by rw [hj]; ring⟩
  intro i hi
  refine hno ⟨n, ?_, ⟨a, by rw [hna]; ring⟩⟩
  rw [← hi]; exact Finset.mem_image_of_mem s (Finset.mem_univ i)

/-- Rule B: `n = q^e` is not a term, because it is the unique element of the
window of maximal `q`-adic valuation. -/
theorem notTermB {q e n : ℕ} (hq : Nat.Prime q) (he : 1 ≤ e) (hn : n = q ^ e)
    {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hhi : s ⟨k - 1, by omega⟩ < 2 * n) :
    ∀ i, s i ≠ n := by
  classical
  obtain ⟨hTpos, hTle, hsumT⟩ := setup hk s hmono h1 hsum
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  rw [hn] at hhi
  have hno := RuleB.ruleB (q := q) (e := e) (M := s ⟨k - 1, by omega⟩) he
    hTpos hTle hhi hsumT
  intro i hi
  refine hno ?_
  rw [← hn, ← hi]; exact Finset.mem_image_of_mem s (Finset.mem_univ i)

/-- The glue: two consecutive excluded values, both interior, give a gap ≥ 3. -/
theorem gap_of_excl {n k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hlo : n + 2 ≤ s ⟨k - 1, by omega⟩)
    (hint : s ⟨k - 1, by omega⟩ ≤ 2 * n + 1)
    (hexn : ∀ i, s i ≠ n) (hexn1 : ∀ i, s i ≠ n + 1) :
    3 ≤ PCI.max_gap k s := by
  have hs0 : s ⟨0, by omega⟩ ≤ n := by
    have := PCI.two_mul_first_le_last hk s hmono (by omega) hsum
    omega
  exact PCI.gap_three_of_two_missing hk s hs0 (by omega) hexn hexn1

/-- **The largest term is never a prime power.** Rule B excludes `q^e` whenever
`M < 2q^e`, and `M = q^e` satisfies that trivially — but `M` is a term. This kills
the two M values ({4, 8}) for which no pair of consecutive interior exclusions
exists, and it is why the base case needs no exhaustive search at all. -/
theorem max_prime_pow {q e : ℕ} (hq : Nat.Prime q) (he : 1 ≤ e)
    {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ) (hmono : StrictMono s)
    (h1 : 1 < s ⟨0, by omega⟩) (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hM : s ⟨k - 1, by omega⟩ = q ^ e) : False := by
  have hpos : 0 < q ^ e := pow_pos hq.pos e
  have hno := notTermB (q := q) (e := e) (n := q ^ e) hq he rfl hk s hmono h1 hsum
    (by omega)
  exact hno ⟨k - 1, by omega⟩ hM


end StepAB

/- Source module P287.Base. -/
/- The base case M ≤ 8, with no exhaustive search.

`StepAB.max_prime_pow` says the largest term is never a prime power, which
disposes of M = 4, 5, 7, 8 outright — including the two values {4, 8} for which no
pair of consecutive interior exclusions exists. M ≥ 4 because 2·n₁ ≤ M and n₁ ≥ 2.
Only M = 6 needs a rung, and it gets the cheapest one there is: 4 = 2² is excluded
by rule B and 5 is excluded by rule A at t = 1.
-/

namespace Base

theorem base_gap {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hhi : s ⟨k - 1, by omega⟩ ≤ 8) :
    3 ≤ PCI.max_gap k s := by
  have h2 := PCI.two_mul_first_le_last hk s hmono (by omega) hsum
  by_cases c4 : s ⟨k - 1, by omega⟩ = 4
  · exact (StepAB.max_prime_pow (q := 2) (e := 2) (by norm_num) (by norm_num)
      hk s hmono h1 hsum (by norm_num [c4])).elim
  by_cases c5 : s ⟨k - 1, by omega⟩ = 5
  · exact (StepAB.max_prime_pow (q := 5) (e := 1) (by norm_num) (by norm_num)
      hk s hmono h1 hsum (by norm_num [c5])).elim
  by_cases c7 : s ⟨k - 1, by omega⟩ = 7
  · exact (StepAB.max_prime_pow (q := 7) (e := 1) (by norm_num) (by norm_num)
      hk s hmono h1 hsum (by norm_num [c7])).elim
  by_cases c8 : s ⟨k - 1, by omega⟩ = 8
  · exact (StepAB.max_prime_pow (q := 2) (e := 3) (by norm_num) (by norm_num)
      hk s hmono h1 hsum (by norm_num [c8])).elim
  -- only M = 6 survives; 4 and 5 are consecutive exclusions, both interior
  refine StepAB.gap_of_excl (n := 4) hk s hmono h1 hsum (by omega) (by omega) ?_ ?_
  · exact StepAB.notTermB (q := 2) (e := 2) (n := 4) (by norm_num) (by norm_num)
      (by norm_num) hk s hmono h1 hsum (by omega)
  · exact StepAB.notTermA (p := 5) (t := 1) (n := 5) (a := 1) (by norm_num)
      (by norm_num) (by norm_num [Nat.factorial]) (by norm_num) hk s hmono h1 hsum
      (by omega)


end Base

/- Source module P287.LowLadder. -/
/- The low end of the ladder: M in [9, 38], where rule A alone is not enough
   and the prime-power rule B supplies the missing exclusions.
   Generated by attempts/012-downward/gen_low.py. -/

namespace LowLadder

/-- **#287 holds for every largest term M in [9, 38].** -/
theorem low_gap {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hlo : 9 ≤ s ⟨k - 1, by omega⟩)
    (hhi : s ⟨k - 1, by omega⟩ ≤ 38) :
    3 ≤ PCI.max_gap k s := by
  by_cases c0 : s ⟨k - 1, by omega⟩ ≤ 15
  · refine StepAB.gap_of_excl (n := 7) hk s hmono h1 hsum (by omega) (by omega) ?_ ?_
    · exact StepAB.notTermA (p := 7) (t := 2) (n := 7) (a := 1) (by norm_num) (by norm_num)
        (by norm_num [Nat.factorial]) (by norm_num) hk s hmono h1 hsum (by omega)
    · exact StepAB.notTermB (q := 2) (e := 3) (n := 8) (by norm_num) (by norm_num) (by norm_num)
        hk s hmono h1 hsum (by omega)
  push_neg at c0
  by_cases c1 : s ⟨k - 1, by omega⟩ ≤ 20
  · refine StepAB.gap_of_excl (n := 13) hk s hmono h1 hsum (by omega) (by omega) ?_ ?_
    · exact StepAB.notTermA (p := 13) (t := 2) (n := 13) (a := 1) (by norm_num) (by norm_num)
        (by norm_num [Nat.factorial]) (by norm_num) hk s hmono h1 hsum (by omega)
    · exact StepAB.notTermA (p := 7) (t := 2) (n := 14) (a := 2) (by norm_num) (by norm_num)
        (by norm_num [Nat.factorial]) (by norm_num) hk s hmono h1 hsum (by omega)
  push_neg at c1
  by_cases c2 : s ⟨k - 1, by omega⟩ ≤ 31
  · refine StepAB.gap_of_excl (n := 16) hk s hmono h1 hsum (by omega) (by omega) ?_ ?_
    · exact StepAB.notTermB (q := 2) (e := 4) (n := 16) (by norm_num) (by norm_num) (by norm_num)
        hk s hmono h1 hsum (by omega)
    · exact StepAB.notTermA (p := 17) (t := 2) (n := 17) (a := 1) (by norm_num) (by norm_num)
        (by norm_num [Nat.factorial]) (by norm_num) hk s hmono h1 hsum (by omega)
  push_neg at c2
  by_cases c3 : s ⟨k - 1, by omega⟩ ≤ 38
  · refine StepAB.gap_of_excl (n := 26) hk s hmono h1 hsum (by omega) (by omega) ?_ ?_
    · exact StepAB.notTermA (p := 13) (t := 2) (n := 26) (a := 2) (by norm_num) (by norm_num)
        (by norm_num [Nat.factorial]) (by norm_num) hk s hmono h1 hsum (by omega)
    · exact StepAB.notTermB (q := 3) (e := 3) (n := 27) (by norm_num) (by norm_num) (by norm_num)
        hk s hmono h1 hsum (by omega)
  push_neg at c3
  omega


end LowLadder

/- Source module P287.StepA. -/
/- One rung of the DOWNWARD ladder for Erdős #287.

Earlier rungs (`StepGen`, `StepGen2`) insisted the two consecutive forced-out
integers be `2p` and `2p+1` with both `p` and `2p+1` prime — a Sophie Germain
pair. That was an accident of how the argument was first written, and it is what
kept the kernel-verified segment floating at 2.46e28: Sophie Germain pairs run
out at small scale.

This rung drops that. It asks only for two consecutive integers `n` and `n+1`
each carrying SOME prime factor big enough for Lemma A′:

  * `p ∣ n` with `p > tp · tp!` and `M < (tp+1)·p`, so every multiple of `p` in
    the window is `j·p` with `j ≤ tp` and `lemA_gen` kills all of them — in
    particular `n`;
  * `q ∣ n+1` likewise;
  * interiority needs only `M ≤ 2n+1`, i.e. `n ≥ ⌊M/2⌋ ≥ n₁`, which follows from
    the counting bound `2·n₁ ≤ M` (`PCI.two_mul_first_le_last`) — no analytic
    bound on the window is required.

Witnesses of this shape exist for every `M ≥ 39` (measured to 2·10⁵), so a ladder
of these rungs reaches all the way down to the small-`M` base case.
-/

namespace StepA

open Finset

theorem step_gap {p q n a b tp tq : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (htp : 1 ≤ tp) (htq : 1 ≤ tq)
    (hpf : tp * Nat.factorial tp < p) (hqf : tq * Nat.factorial tq < q)
    (hna : n = a * p) (hnb : n + 1 = b * q)
    {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hlo : n + 2 ≤ s ⟨k - 1, by omega⟩)
    (hhip : s ⟨k - 1, by omega⟩ < (tp + 1) * p)
    (hhiq : s ⟨k - 1, by omega⟩ < (tq + 1) * q)
    (hint : s ⟨k - 1, by omega⟩ ≤ 2 * n + 1) :
    3 ≤ PCI.max_gap k s := by
  classical
  set M := s ⟨k - 1, by omega⟩ with hMdef
  set T : Finset ℕ := Finset.image s Finset.univ with hTdef
  have hsumT : ∑ x ∈ T, ((x : ℚ))⁻¹ = 1 := by
    rw [hTdef, Finset.sum_image (hmono.injective.injOn)]; exact hsum
  have hmono_le : ∀ i : Fin k, s ⟨0, by omega⟩ ≤ s i := by
    intro i
    rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
    · have : i = (⟨0, by omega⟩ : Fin k) := Fin.ext h
      rw [this]
    · exact le_of_lt (hmono (by simp [Fin.lt_def]; omega))
  have hle_last : ∀ i : Fin k, s i ≤ M := by
    intro i
    rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt i.isLt) with h | h
    · have : i = (⟨k - 1, by omega⟩ : Fin k) := Fin.ext h
      rw [this]
    · exact le_of_lt (hmono (by simp [Fin.lt_def]; omega))
  have hTpos : ∀ x ∈ T, 0 < x := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    have := hmono_le i; omega
  have hTle : ∀ x ∈ T, x ≤ M := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    have := hle_last i; omega
  -- no term is divisible by p: its multiples in the window are j·p with j ≤ tp
  have hnoP : ¬ ∃ x ∈ T, p ∣ x := by
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    intro hex
    refine LemAGen.lemA_gen (p := p) (t := tp) htp hpf hTpos ?_ hex hsumT
    intro x hx hdvd
    obtain ⟨j, hj⟩ := hdvd
    have hxle := hTle x hx
    have hxpos := hTpos x hx
    have hjt : j ≤ tp := by
      by_contra hc
      push_neg at hc
      have hmul : p * (tp + 1) ≤ p * j := Nat.mul_le_mul_left _ hc
      have e1 : p * (tp + 1) = (tp + 1) * p := Nat.mul_comm _ _
      omega
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hpp
      · simp at hj; omega
      · exact hpp
    exact ⟨j, hj1, hjt, by rw [hj]; ring⟩
  -- likewise for q
  have hnoQ : ¬ ∃ x ∈ T, q ∣ x := by
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    intro hex
    refine LemAGen.lemA_gen (p := q) (t := tq) htq hqf hTpos ?_ hex hsumT
    intro x hx hdvd
    obtain ⟨j, hj⟩ := hdvd
    have hxle := hTle x hx
    have hxpos := hTpos x hx
    have hjt : j ≤ tq := by
      by_contra hc
      push_neg at hc
      have hmul : q * (tq + 1) ≤ q * j := Nat.mul_le_mul_left _ hc
      have e1 : q * (tq + 1) = (tq + 1) * q := Nat.mul_comm _ _
      omega
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hpp
      · simp at hj; omega
      · exact hpp
    exact ⟨j, hj1, hjt, by rw [hj]; ring⟩
  have hnnot : ∀ i, s i ≠ n := by
    intro i hi
    refine hnoP ⟨n, ?_, ⟨a, by rw [hna]; ring⟩⟩
    rw [← hi]; exact Finset.mem_image_of_mem s (Finset.mem_univ i)
  have hn1not : ∀ i, s i ≠ n + 1 := by
    intro i hi
    refine hnoQ ⟨n + 1, ?_, ⟨b, by rw [hnb]; ring⟩⟩
    rw [← hi]; exact Finset.mem_image_of_mem s (Finset.mem_univ i)
  have hs0 : s ⟨0, by omega⟩ ≤ n := by
    have := PCI.two_mul_first_le_last hk s hmono (by omega) hsum
    omega
  exact PCI.gap_three_of_two_missing hk s hs0 (by omega) hnnot hn1not


end StepA

/- Source module P287.Ladder. -/
/- The DOWNWARD ladder for Erdős #287: one contiguous kernel-verified range,
   anchored just above the small-M base case rather than floating at 1e28.
   Generated by attempts/012-downward/gen_ladder.py. -/

namespace Ladder

/-- **#287 holds for every largest term M in [39, 382613443].**

    24 rungs, each a pair of consecutive integers both forced out of the
    representation by Lemma A′ at one of their prime factors. -/
theorem ladder_gap {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hlo : 39 ≤ s ⟨k - 1, by omega⟩)
    (hhi : s ⟨k - 1, by omega⟩ ≤ 382613443) :
    3 ≤ PCI.max_gap k s := by
  by_cases c0 : s ⟨k - 1, by omega⟩ ≤ 75
  · exact StepA.step_gap (p := 37) (q := 19) (n := 37) (a := 1) (b := 2) (tp := 3) (tq := 3)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c0
  by_cases c1 : s ⟨k - 1, by omega⟩ ≤ 147
  · exact StepA.step_gap (p := 73) (q := 37) (n := 73) (a := 1) (b := 2) (tp := 3) (tq := 3)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c1
  by_cases c2 : s ⟨k - 1, by omega⟩ ≤ 211
  · exact StepA.step_gap (p := 53) (q := 107) (n := 106) (a := 2) (b := 1) (tp := 3) (tq := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c2
  by_cases c3 : s ⟨k - 1, by omega⟩ ≤ 387
  · exact StepA.step_gap (p := 193) (q := 97) (n := 193) (a := 1) (b := 2) (tp := 4) (tq := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c3
  by_cases c4 : s ⟨k - 1, by omega⟩ ≤ 765
  · exact StepA.step_gap (p := 191) (q := 383) (n := 382) (a := 2) (b := 1) (tp := 4) (tq := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c4
  by_cases c5 : s ⟨k - 1, by omega⟩ ≤ 1515
  · exact StepA.step_gap (p := 757) (q := 379) (n := 757) (a := 1) (b := 2) (tp := 5) (tq := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c5
  by_cases c6 : s ⟨k - 1, by omega⟩ ≤ 2973
  · exact StepA.step_gap (p := 743) (q := 1487) (n := 1486) (a := 2) (b := 1) (tp := 5) (tq := 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c6
  by_cases c7 : s ⟨k - 1, by omega⟩ ≤ 5925
  · exact StepA.step_gap (p := 1481) (q := 2963) (n := 2962) (a := 2) (b := 1) (tp := 5) (tq := 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c7
  by_cases c8 : s ⟨k - 1, by omega⟩ ≤ 11757
  · exact StepA.step_gap (p := 2939) (q := 5879) (n := 5878) (a := 2) (b := 1) (tp := 5) (tq := 6)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c8
  by_cases c9 : s ⟨k - 1, by omega⟩ ≤ 23465
  · exact StepA.step_gap (p := 3911) (q := 5867) (n := 11733) (a := 3) (b := 2) (tp := 5) (tq := 6)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c9
  by_cases c10 : s ⟨k - 1, by omega⟩ ≤ 46797
  · exact StepA.step_gap (p := 11699) (q := 23399) (n := 23398) (a := 2) (b := 1) (tp := 6) (tq := 6)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c10
  by_cases c11 : s ⟨k - 1, by omega⟩ ≤ 93485
  · exact StepA.step_gap (p := 23371) (q := 15581) (n := 46742) (a := 2) (b := 3) (tp := 6) (tq := 6)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c11
  by_cases c12 : s ⟨k - 1, by omega⟩ ≤ 186907
  · exact StepA.step_gap (p := 31151) (q := 46727) (n := 93453) (a := 3) (b := 2) (tp := 6) (tq := 7)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c12
  by_cases c13 : s ⟨k - 1, by omega⟩ ≤ 373783
  · exact StepA.step_gap (p := 62297) (q := 46723) (n := 186891) (a := 3) (b := 4) (tp := 7) (tq := 7)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c13
  by_cases c14 : s ⟨k - 1, by omega⟩ ≤ 747555
  · exact StepA.step_gap (p := 373777) (q := 186889) (n := 373777) (a := 1) (b := 2) (tp := 8) (tq := 7)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c14
  by_cases c15 : s ⟨k - 1, by omega⟩ ≤ 1494645
  · exact StepA.step_gap (p := 373661) (q := 747323) (n := 747322) (a := 2) (b := 1) (tp := 8) (tq := 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c15
  by_cases c16 : s ⟨k - 1, by omega⟩ ≤ 2989287
  · exact StepA.step_gap (p := 1494643) (q := 373661) (n := 1494643) (a := 1) (b := 4) (tp := 8) (tq := 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c16
  by_cases c17 : s ⟨k - 1, by omega⟩ ≤ 5978453
  · exact StepA.step_gap (p := 1494613) (q := 996409) (n := 2989226) (a := 2) (b := 3) (tp := 8) (tq := 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c17
  by_cases c18 : s ⟨k - 1, by omega⟩ ≤ 11956903
  · exact StepA.step_gap (p := 1992817) (q := 1494613) (n := 5978451) (a := 3) (b := 4) (tp := 8) (tq := 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c18
  by_cases c19 : s ⟨k - 1, by omega⟩ ≤ 23913453
  · exact StepA.step_gap (p := 5978363) (q := 11956727) (n := 11956726) (a := 2) (b := 1) (tp := 9) (tq := 9)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c19
  by_cases c20 : s ⟨k - 1, by omega⟩ ≤ 47826903
  · exact StepA.step_gap (p := 23913451) (q := 5978363) (n := 23913451) (a := 1) (b := 4) (tp := 9) (tq := 9)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c20
  by_cases c21 : s ⟨k - 1, by omega⟩ ≤ 95653443
  · exact StepA.step_gap (p := 47826721) (q := 23913361) (n := 47826721) (a := 1) (b := 2) (tp := 10) (tq := 9)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c21
  by_cases c22 : s ⟨k - 1, by omega⟩ ≤ 191306775
  · exact StepA.step_gap (p := 95653387) (q := 23913347) (n := 95653387) (a := 1) (b := 4) (tp := 10) (tq := 9)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c22
  by_cases c23 : s ⟨k - 1, by omega⟩ ≤ 382613443
  · exact StepA.step_gap (p := 63768907) (q := 95653361) (n := 191306721) (a := 3) (b := 2) (tp := 10) (tq := 10)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by norm_num) (by norm_num) hk s hmono h1 hsum
      (by omega) (by omega) (by omega) (by omega)
  push_neg at c23
  omega


end Ladder

/- Source module P287.Main. -/
/- Erdős #287, kernel-verified for every largest term below 3.8·10⁸.

    base_gap    M ≤ 8            StepAB.max_prime_pow, one rung
    low_gap     9 ≤ M ≤ 38       4 rungs, rules A and B
    ladder_gap  39 ≤ M ≤ 3.8e8   24 rungs, rule A only

No exhaustive search anywhere, and nothing rests on Python.
-/

namespace Main

/-- **Erdős #287 holds for every representation whose largest term is at most
382 613 443.** -/
theorem erdos287_below {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (h1 : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1)
    (hhi : s ⟨k - 1, by omega⟩ ≤ 382613443) :
    3 ≤ PCI.max_gap k s := by
  by_cases c1 : s ⟨k - 1, by omega⟩ ≤ 8
  · exact Base.base_gap hk s hmono h1 hsum c1
  push_neg at c1
  by_cases c2 : s ⟨k - 1, by omega⟩ ≤ 38
  · exact LowLadder.low_gap hk s hmono h1 hsum (by omega) c2
  push_neg at c2
  exact Ladder.ladder_gap hk s hmono h1 hsum (by omega) hhi


end Main

open Finset

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hbound : f (k - 1) ≤ 382613443) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  let s : Fin k → ℕ := fun i => f i
  have hmono' : StrictMono s := fun i j hij => hmono i j hij j.isLt
  have hsum' : ∑ i : Fin k, ((s i : ℚ))⁻¹ = 1 := by
    change (∑ i : Fin k, ((f i.val : ℚ))⁻¹) = 1
    rw [Fin.sum_univ_eq_sum_range (fun i => ((f i : ℚ))⁻¹)]
    simpa only [one_div] using hsum
  have hresult := Main.erdos287_below hk s hmono' (hf1 0 (by omega)) hsum' hbound
  by_contra! hno
  have hsup : PCI.max_gap k s ≤ 2 := by
    unfold PCI.max_gap
    refine Finset.sup_le ?_
    intro i _
    have hi : (i : ℕ) < k - 1 := i.isLt
    exact Nat.le_of_lt_succ (hno i (by omega))
  omega

