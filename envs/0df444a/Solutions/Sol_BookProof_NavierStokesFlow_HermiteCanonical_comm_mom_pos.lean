-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteCanonical.comm_mom_pos
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:59:46.896249+00:00
-- url     : https://prove2.me/submissions/6b075b2e-2901-4a0b-a1bd-d7d47a0357e5

import Definitions.Def_ChapterNavierStokesHermiteCanonical
/-
Adapted from Leonardo Pedro, timepiece at commit61595bc.
Copyright 2026 Leonardo Pedro. Changes: Prove2Me imports and checked wrapper theorem.

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


   Copyright 2026 Leonardo Pedro

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
-- Adapted from Leonardo Pedro's timepiece, commit 61595bc, ChapterNavierStokesHermiteCanonical.lean.
-- Copyright 2026 Leonardo Pedro. SPDX-License-Identifier: Apache-2.0.
-- Changes: replaced BookProof imports with the published Prove2Me definitions; retained checked source proofs.
namespace BookProof.NavierStokesFlow.HermiteCanonical
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
variable {κ : ℝ}
@[simp] theorem ann_coe (x : lpFiniteModes ℕ) (n : ℕ) :
    (((ann x : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n
      = (Real.sqrt (n + 1) : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) (n + 1) := rfl

@[simp] theorem cre_coe (x : lpFiniteModes ℕ) (n : ℕ) :
    (((cre x : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n
      = (Real.sqrt n : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) (n - 1) := rfl

theorem sqrt_mul_sqrt (r : ℝ) (hr : 0 ≤ r) : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr]

theorem ann_ann_coe (x : lpFiniteModes ℕ) (n : ℕ) :
    (((ann (ann x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n
      = (Real.sqrt ((n : ℝ) + 1) : ℂ) * (Real.sqrt ((n : ℝ) + 2) : ℂ)
        * ((x : L2I ℕ) : ℕ → ℂ) (n + 2) := by
  rw [ann_coe, ann_coe]
  push_cast
  ring_nf

theorem cre_cre_coe_add_two (x : lpFiniteModes ℕ) (k : ℕ) :
    (((cre (cre x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) (k + 2)
      = (Real.sqrt ((k : ℝ) + 2) : ℂ) * (Real.sqrt ((k : ℝ) + 1) : ℂ)
        * ((x : L2I ℕ) : ℕ → ℂ) k := by
  rw [cre_coe, cre_coe]
  have h1 : (k + 2 - 1) = k + 1 := by omega
  have h2 : (k + 1 - 1) = k := by omega
  rw [h1, h2]
  push_cast
  ring

theorem cre_cre_coe_zero (x : lpFiniteModes ℕ) :
    (((cre (cre x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) 0 = 0 := by
  rw [cre_coe]
  simp

theorem cre_cre_coe_one (x : lpFiniteModes ℕ) :
    (((cre (cre x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) 1 = 0 := by
  rw [cre_coe, cre_coe]
  simp

theorem ann_cre_coe (x : lpFiniteModes ℕ) (n : ℕ) :
    (((ann (cre x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n
      = ((n : ℂ) + 1) * ((x : L2I ℕ) : ℕ → ℂ) n := by
  rw [ann_coe, cre_coe]
  have h1 : (n + 1 - 1) = n := by omega
  rw [h1]
  push_cast
  rw [← mul_assoc, sqrt_mul_sqrt _ (by positivity)]
  push_cast
  ring

theorem cre_ann_coe (x : lpFiniteModes ℕ) (n : ℕ) :
    (((cre (ann x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n
      = (n : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) n := by
  rw [cre_coe]
  cases n with
  | zero => simp
  | succ k =>
      rw [ann_coe]
      have h1 : (k + 1 - 1) = k := by omega
      rw [h1]
      push_cast
      rw [← mul_assoc, sqrt_mul_sqrt _ (by positivity)]
      push_cast
      ring

theorem comm_ann_cre : ann.comp cre - cre.comp ann = LinearMap.id := by
  refine LinearMap.ext fun x => Subtype.ext (lp.ext (funext fun n => ?_))
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, Submodule.coe_sub,
    lp.coeFn_sub, Pi.sub_apply, ann_cre_coe, cre_ann_coe]
  ring

theorem bracket_DS :
    (cre - ann).comp (cre + ann) - (cre + ann).comp (cre - ann) = (-2 : ℂ) • LinearMap.id := by
  refine LinearMap.ext fun x => Subtype.ext (lp.ext (funext fun n => ?_))
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_add, map_sub, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul,
    lp.coeFn_sub, lp.coeFn_add, lp.coeFn_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ann_cre_coe, cre_ann_coe]
  ring

theorem sq_diff :
    (cre + ann).comp (cre + ann) - (cre - ann).comp (cre - ann)
      = (2 : ℂ) • (cre.comp ann + ann.comp cre) := by
  refine LinearMap.ext fun x => Subtype.ext (lp.ext (funext fun n => ?_))
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    map_add, map_sub, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul,
    lp.coeFn_sub, lp.coeFn_add, lp.coeFn_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem anti_DS :
    (cre - ann).comp (cre + ann) + (cre + ann).comp (cre - ann)
      = (2 : ℂ) • (cre.comp cre - ann.comp ann) := by
  refine LinearMap.ext fun x => Subtype.ext (lp.ext (funext fun n => ?_))
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    map_add, map_sub, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul,
    lp.coeFn_sub, lp.coeFn_add, lp.coeFn_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem sqrt_half_sq (hκ : 0 ≤ κ) :
    (Real.sqrt (κ / 2) : ℂ) * (Real.sqrt (κ / 2) : ℂ) = (κ : ℂ) / 2 := by
  rw [sqrt_mul_sqrt _ (by positivity)]
  push_cast
  ring

theorem sqrt_half_mul_inv (hκ : 0 < κ) :
    (Real.sqrt (κ / 2) : ℂ) * ((1 / Real.sqrt (2 * κ) : ℝ) : ℂ) = 1 / 2 := by
  have hreal : Real.sqrt (κ / 2) * (1 / Real.sqrt (2 * κ)) = 1 / 2 := by
    rw [Real.sqrt_div hκ.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    nlinarith [h2, hk]
  rw [← Complex.ofReal_mul, hreal]
  norm_num

theorem drift_eq (hκ : 0 < κ) : drift κ = (κ : ℂ) • pos κ := by
  rw [drift, pos, smul_smul]
  congr 1
  have hne : Real.sqrt (2 * κ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by linarith)
  have hmul : Real.sqrt (κ / 2) * Real.sqrt (2 * κ) = κ := by
    rw [← Real.sqrt_mul (by positivity)]
    have hsq : κ / 2 * (2 * κ) = κ ^ 2 := by ring
    rw [hsq, Real.sqrt_sq hκ.le]
  have hreal : Real.sqrt (κ / 2) = κ * (1 / Real.sqrt (2 * κ)) := by
    rw [eq_comm, mul_one_div, div_eq_iff hne]
    exact hmul.symm
  rw [← Complex.ofReal_mul, ← hreal]

theorem comm_mom_pos (hκ : 0 < κ) :
    (mom κ).comp (pos κ) - (pos κ).comp (mom κ) = (-Complex.I) • LinearMap.id := by
  have hs : Complex.I * (Real.sqrt (κ / 2) : ℂ) * ((1 / Real.sqrt (2 * κ) : ℝ) : ℂ) * (-2)
      = -Complex.I := by
    linear_combination (-2 * Complex.I) * sqrt_half_mul_inv hκ
  refine LinearMap.ext fun x => Subtype.ext (lp.ext (funext fun n => ?_))
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, mom, pos, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.add_apply, map_smul, map_add, map_sub,
    Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, lp.coeFn_sub, lp.coeFn_add,
    lp.coeFn_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    ann_cre_coe, cre_ann_coe]
  linear_combination (((x : L2I ℕ) : ℕ → ℂ) n) * hs

theorem amp_eq_sqrt_mul (κ : ℝ) (n : ℕ) :
    amp κ n = (κ / 2) * (Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 2)) := by
  rw [amp, ← Real.sqrt_mul (by positivity)]

theorem comparison_eq (hκ : 0 ≤ κ) :
    (lpFiniteModes ℕ).subtype.comp
        ((mom κ).comp (mom κ) + (drift κ).comp (drift κ) + LinearMap.id)
      = (diagMax (oscSymbol κ)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol κ))) := by
  have hsq : (mom κ).comp (mom κ) + (drift κ).comp (drift κ)
      = (κ : ℂ) • (cre.comp ann + ann.comp cre) := by
    have h1 : (mom κ).comp (mom κ)
        = (-((Real.sqrt (κ / 2) : ℂ) * (Real.sqrt (κ / 2) : ℂ))) •
          (cre - ann).comp (cre - ann) := by
      simp only [mom, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
      congr 1
      have : Complex.I * Complex.I = -1 := Complex.I_mul_I
      ring_nf
      rw [Complex.I_sq]
      ring
    have h2 : (drift κ).comp (drift κ)
        = ((Real.sqrt (κ / 2) : ℂ) * (Real.sqrt (κ / 2) : ℂ)) • (cre + ann).comp (cre + ann) := by
      simp only [drift, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
    have hexp : (cre + ann).comp (cre + ann)
        = (cre - ann).comp (cre - ann) + (2 : ℂ) • (cre.comp ann + ann.comp cre) := by
      rw [← sq_diff]
      abel
    rw [h1, h2, sqrt_half_sq hκ, hexp]
    module
  refine LinearMap.ext fun x => lp.ext (funext fun n => ?_)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, hsq, Submodule.subtype_apply,
    LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_add, Submodule.coe_smul,
    lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, diagMax_coe,
    ann_cre_coe, cre_ann_coe, Submodule.inclusion_apply]
  simp only [oscSymbol]
  push_cast
  ring

private theorem parent_shift2_zero {M : Type*} [Zero M] (g : ℕ → M) : shift2 g 0 = 0 := rfl
private theorem parent_shift2_one {M : Type*} [Zero M] (g : ℕ → M) : shift2 g 1 = 0 := rfl
private theorem parent_nsH_coe (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) (m : ℕ) :
    ((nsH κ hκ x : L2I ℕ) : ℕ → ℂ) m = hFun κ (((x : L2I ℕ) : ℕ → ℂ)) m := rfl
theorem hamiltonian_eq (hκ : 0 ≤ κ) :
    (lpFiniteModes ℕ).subtype.comp
        (((1 : ℂ) / 2) • ((mom κ).comp (drift κ) + (drift κ).comp (mom κ)))
      = (nsH κ hκ).comp (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol κ))) := by
  have hsym : (mom κ).comp (drift κ) + (drift κ).comp (mom κ)
      = (Complex.I * (κ : ℂ)) • (cre.comp cre - ann.comp ann) := by
    have h1 : (mom κ).comp (drift κ)
        = (Complex.I * ((Real.sqrt (κ / 2) : ℂ) * (Real.sqrt (κ / 2) : ℂ))) •
          (cre - ann).comp (cre + ann) := by
      simp only [mom, drift, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
      congr 1
      ring
    have h2 : (drift κ).comp (mom κ)
        = (Complex.I * ((Real.sqrt (κ / 2) : ℂ) * (Real.sqrt (κ / 2) : ℂ))) •
          (cre + ann).comp (cre - ann) := by
      simp only [mom, drift, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
      congr 1
      ring
    rw [h1, h2, ← smul_add, anti_DS, sqrt_half_sq hκ, smul_smul]
    congr 1
    ring
  refine LinearMap.ext fun x => lp.ext (funext fun m => ?_)
  simp only [LinearMap.comp_apply, hsym, Submodule.subtype_apply, LinearMap.smul_apply,
    Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, LinearMap.sub_apply,
    Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, parent_nsH_coe, Submodule.inclusion_apply]
  rw [hFun, ann_ann_coe]
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · rw [cre_cre_coe_zero]
      simp only [parent_shift2_zero]
      rw [amp_eq_sqrt_mul]
      push_cast
      ring
    · rw [cre_cre_coe_one]
      simp only [parent_shift2_one]
      rw [amp_eq_sqrt_mul]
      push_cast
      ring
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    rw [cre_cre_coe_add_two, shift2_add_two, amp_eq_sqrt_mul, amp_eq_sqrt_mul]
    push_cast
    ring

end BookProof.NavierStokesFlow.HermiteCanonical

#print axioms BookProof.NavierStokesFlow.HermiteCanonical.hamiltonian_eq

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.comm_mom_pos
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
























variable {κ : ℝ}
theorem solution (hκ : 0 < κ) :
    (mom κ).comp (pos κ) - (pos κ).comp (mom κ) = (-Complex.I) • LinearMap.id := by
  apply BookProof.NavierStokesFlow.HermiteCanonical.comm_mom_pos <;> assumption
#print axioms solution
