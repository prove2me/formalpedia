-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianCanonical.lagT_coreState
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:59:44.493771+00:00
-- url     : https://prove2.me/submissions/cb6d5fed-705a-4d42-924b-372c0e1b1999

import Definitions.Def_ChapterNavierStokesLagrangianCanonical
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
-- Adapted from Leonardo Pedro's timepiece at61595bc. Copyright2026LeonardoPedro.
-- SPDX-License-Identifier: Apache-2.0. Imports adapted to the Prove2Me platform definitions.
namespace BookProof.NavierStokesFlow
namespace CanonicalVector
open LpNat FarisLavine IkebeKato ThreeComponent ShiftHamiltonian SignedShift
theorem raise_comm (i k : Fin 3) (β : Vel) : raise i (raise k β) = raise k (raise i β) := by
  funext j
  by_cases hji : j = i <;> by_cases hjk : j = k
  · subst hji; subst hjk; simp [raise]
  · subst hji; rw [raise_self, raise_of_ne hjk, raise_of_ne hjk, raise_self]
  · subst hjk; rw [raise_of_ne hji, raise_self, raise_self, raise_of_ne hji]
  · rw [raise_of_ne hji, raise_of_ne hjk, raise_of_ne hjk, raise_of_ne hji]

theorem lower_comm (i k : Fin 3) (β : Vel) : lower i (lower k β) = lower k (lower i β) := by
  funext j
  by_cases hji : j = i <;> by_cases hjk : j = k
  · subst hji; subst hjk; simp [lower]
  · subst hji; rw [lower_self, lower_of_ne hjk, lower_of_ne hjk, lower_self]
  · subst hjk; rw [lower_of_ne hji, lower_self, lower_self, lower_of_ne hji]
  · rw [lower_of_ne hji, lower_of_ne hjk, lower_of_ne hjk, lower_of_ne hji]

@[simp] theorem lower_raise (i : Fin 3) (β : Vel) : lower i (raise i β) = β := by
  funext j
  by_cases hji : j = i
  · subst hji; rw [lower_self, raise_self]; omega
  · rw [lower_of_ne hji, raise_of_ne hji]

theorem lower_raise_of_ne {i k : Fin 3} (h : i ≠ k) (β : Vel) :
    lower k (raise i β) = raise i (lower k β) := by
  funext j
  by_cases hji : j = i <;> by_cases hjk : j = k
  · exact absurd (hji ▸ hjk ▸ rfl) h
  · subst hji; rw [lower_of_ne hjk, raise_self, raise_self, lower_of_ne hjk]
  · subst hjk; rw [lower_self, raise_of_ne hji, raise_of_ne hji, lower_self]
  · rw [lower_of_ne hjk, raise_of_ne hji, raise_of_ne hji, lower_of_ne hjk]

@[simp] theorem crd_ann (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (ann i x) = aFun i (crd x) := rfl

@[simp] theorem crd_cre (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (cre i x) = cFun i (crd x) := rfl

@[simp] theorem crd_add (x y : lpFiniteModes Vel) : crd (x + y) = crd x + crd y := by
  funext β; simp [crd]

@[simp] theorem crd_smul (a : ℂ) (x : lpFiniteModes Vel) : crd (a • x) = a • crd x := by
  funext β; simp [crd]

@[simp] theorem crd_sub (x y : lpFiniteModes Vel) : crd (x - y) = crd x - crd y := by
  funext β; simp [crd]

theorem crd_injective : Function.Injective crd := by
  intro x y h
  exact Subtype.ext (lp.ext h)

@[simp] theorem aFun_add (i : Fin 3) (X Y : Vel → ℂ) :
    aFun i (X + Y) = aFun i X + aFun i Y := by
  funext β; simp [aFun]; ring

@[simp] theorem aFun_sub (i : Fin 3) (X Y : Vel → ℂ) :
    aFun i (X - Y) = aFun i X - aFun i Y := by
  funext β; simp [aFun]; ring

@[simp] theorem aFun_smul (i : Fin 3) (a : ℂ) (X : Vel → ℂ) :
    aFun i (a • X) = a • aFun i X := by
  funext β; simp [aFun]; ring

@[simp] theorem cFun_add (i : Fin 3) (X Y : Vel → ℂ) :
    cFun i (X + Y) = cFun i X + cFun i Y := by
  funext β; simp [cFun]; ring

@[simp] theorem cFun_sub (i : Fin 3) (X Y : Vel → ℂ) :
    cFun i (X - Y) = cFun i X - cFun i Y := by
  funext β; simp [cFun]; ring

@[simp] theorem cFun_smul (i : Fin 3) (a : ℂ) (X : Vel → ℂ) :
    cFun i (a • X) = a • cFun i X := by
  funext β; simp [cFun]; ring

theorem aFun_comm (i k : Fin 3) (X : Vel → ℂ) : aFun i (aFun k X) = aFun k (aFun i X) := by
  by_cases hik : i = k
  · rw [hik]
  · funext β
    simp only [aFun, raise_of_ne (Ne.symm hik), raise_of_ne hik, raise_comm i k β]
    ring

theorem cFun_comm (i k : Fin 3) (X : Vel → ℂ) : cFun i (cFun k X) = cFun k (cFun i X) := by
  by_cases hik : i = k
  · rw [hik]
  · funext β
    simp only [cFun, lower_of_ne (Ne.symm hik), lower_of_ne hik, lower_comm i k β]
    ring

theorem aFun_cFun_of_ne {i k : Fin 3} (h : i ≠ k) (X : Vel → ℂ) :
    aFun i (cFun k X) = cFun k (aFun i X) := by
  funext β
  simp only [aFun, cFun, raise_of_ne (Ne.symm h), lower_of_ne h,
    lower_raise_of_ne h β]
  ring

theorem aFun_cFun_self (i : Fin 3) (X : Vel → ℂ) :
    aFun i (cFun i X) = fun β => (((β i : ℝ) + 1 : ℝ) : ℂ) * X β := by
  funext β
  simp only [aFun, cFun, raise_self, lower_raise]
  rw [show ((β i + 1 : ℕ) : ℝ) = ((β i : ℝ) + 1) from by push_cast; ring,
    ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]

theorem cFun_aFun_self (i : Fin 3) (X : Vel → ℂ) :
    cFun i (aFun i X) = fun β => ((β i : ℝ) : ℂ) * X β := by
  funext β
  rcases Nat.eq_zero_or_pos (β i) with h0 | hpos
  · simp [cFun, h0]
  · have h1 : (1 : ℕ) ≤ β i := hpos
    have hcast : (((β i - 1 : ℕ) : ℝ) + 1) = ((β i : ℝ)) := by
      push_cast [Nat.cast_sub h1]
      ring
    simp only [cFun, aFun, lower_self, raise_lower i hpos, hcast]
    rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]

theorem ann_comm (i k : Fin 3) : (ann i).comp (ann k) = (ann k).comp (ann i) :=
  LinearMap.ext fun x => crd_injective (by
    simp only [LinearMap.comp_apply, crd_ann]
    exact aFun_comm i k (crd x))

theorem cre_comm (i k : Fin 3) : (cre i).comp (cre k) = (cre k).comp (cre i) :=
  LinearMap.ext fun x => crd_injective (by
    simp only [LinearMap.comp_apply, crd_cre]
    exact cFun_comm i k (crd x))

theorem comm_ann_cre_of_ne {i k : Fin 3} (h : i ≠ k) :
    (ann i).comp (cre k) = (cre k).comp (ann i) :=
  LinearMap.ext fun x => crd_injective (by
    simp only [LinearMap.comp_apply, crd_ann, crd_cre]
    exact aFun_cFun_of_ne h (crd x))

theorem comm_ann_cre (i : Fin 3) :
    (ann i).comp (cre i) - (cre i).comp (ann i) = LinearMap.id := by
  refine LinearMap.ext fun x => crd_injective ?_
  funext β
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, crd_sub,
    crd_ann, crd_cre, Pi.sub_apply, aFun_cFun_self, cFun_aFun_self]
  push_cast
  ring

theorem inv_sqrt_two_sq : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ)
    = ((1 / 2 : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem comm_mom_pos (i : Fin 3) :
    (mom i).comp (pos i) - (pos i).comp (mom i) = (-Complex.I) • LinearMap.id := by
  have hcomm : (cre i - ann i).comp (cre i + ann i) - (cre i + ann i).comp (cre i - ann i)
      = (-2 : ℂ) • LinearMap.id := by
    have h := comm_ann_cre i
    have hexp : (cre i - ann i).comp (cre i + ann i) - (cre i + ann i).comp (cre i - ann i)
        = (-2 : ℂ) • ((ann i).comp (cre i) - (cre i).comp (ann i)) := by
      simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_sub, LinearMap.sub_comp]
      module
    rw [hexp, h]
  have hscal : Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) * (-2)
      = -Complex.I := by
    have h := inv_sqrt_two_sq
    push_cast at h ⊢
    linear_combination (-2 * Complex.I) * h
  have hL : (mom i).comp (pos i) - (pos i).comp (mom i)
      = (Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ)) •
        ((cre i - ann i).comp (cre i + ann i) - (cre i + ann i).comp (cre i - ann i)) := by
    simp only [mom, pos, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
    module
  rw [hL, hcomm, smul_smul, hscal]

theorem comm_mom_pos_of_ne {i k : Fin 3} (h : i ≠ k) :
    (mom i).comp (pos k) = (pos k).comp (mom i) := by
  have h1 : (ann i).comp (cre k) = (cre k).comp (ann i) := comm_ann_cre_of_ne h
  have h2 : (cre i).comp (ann k) = (ann k).comp (cre i) :=
    (comm_ann_cre_of_ne (Ne.symm h)).symm
  have h3 : (ann i).comp (ann k) = (ann k).comp (ann i) := ann_comm i k
  have h4 : (cre i).comp (cre k) = (cre k).comp (cre i) := cre_comm i k
  simp only [mom, pos, LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.comp_add, LinearMap.add_comp, LinearMap.sub_comp, LinearMap.comp_sub,
    h1, h2, h3, h4]
  module
end CanonicalVector
namespace LagrangianCanonical
open LpNat FarisLavine IkebeKato FullEsa LagrangianEsa LagrangianKatoRellich
open CanonicalVector ThreeComponent
@[simp] theorem crd_numOp (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (numOp i x) = fun β => ((β i : ℝ) : ℂ) * crd x β := by
  simp only [numOp, LinearMap.comp_apply, crd_cre, crd_ann]
  exact cFun_aFun_self i (crd x)

theorem ann_comp_cre_eq (i : Fin 3) :
    (ann i).comp (cre i) = (cre i).comp (ann i) + LinearMap.id :=
  (sub_eq_iff_eq_add.mp (comm_ann_cre i)).trans (add_comm _ _)

theorem posSq_add_momSq (i : Fin 3) :
    (pos i).comp (pos i) + (mom i).comp (mom i)
      = (2 : ℂ) • numOp i + LinearMap.id := by
  have hhalf : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    rw [inv_sqrt_two_sq]; norm_num
  have h1 : (pos i).comp (pos i)
      = (1 / 2 : ℂ) • ((cre i + ann i).comp (cre i + ann i)) := by
    simp only [pos, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, hhalf]
  have h2 : (mom i).comp (mom i)
      = (-(1 / 2 : ℂ)) • ((cre i - ann i).comp (cre i - ann i)) := by
    simp only [mom, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
    congr 1
    have : Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ) * (Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ))
        = (Complex.I * Complex.I)
          * (((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ)) := by ring
    rw [this, hhalf, Complex.I_mul_I]
    ring
  have hPM : (cre i + ann i).comp (cre i + ann i) - (cre i - ann i).comp (cre i - ann i)
      = (2 : ℂ) • ((cre i).comp (ann i)) + (2 : ℂ) • ((ann i).comp (cre i)) := by
    simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_sub, LinearMap.sub_comp]
    module
  have hsplit : (pos i).comp (pos i) + (mom i).comp (mom i)
      = (1 / 2 : ℂ) • ((cre i + ann i).comp (cre i + ann i)
          - (cre i - ann i).comp (cre i - ann i)) := by
    rw [h1, h2]; module
  rw [hsplit, hPM, ann_comp_cre_eq i]
  simp only [numOp]
  module


variable (nu : ℝ)
theorem omega_pos (hnu : 0 < nu) : 0 < omega nu := Real.sqrt_pos.mpr (by linarith)

theorem omega_sq (hnu : 0 ≤ nu) : omega nu * omega nu = 2 * nu :=
  Real.mul_self_sqrt (by linarith)

theorem comm_lagP_lagQ (hnu : 0 < nu) (i : Fin 3) :
    (lagP nu i).comp (lagQ nu i) - (lagQ nu i).comp (lagP nu i)
      = (-Complex.I) • LinearMap.id := by
  have hpos : 0 < Real.sqrt (omega nu) := Real.sqrt_pos.mpr (omega_pos nu hnu)
  have hscal : ((Real.sqrt (omega nu) : ℝ) : ℂ) * (((Real.sqrt (omega nu))⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hpos), Complex.ofReal_one]
  have hL : (lagP nu i).comp (lagQ nu i) - (lagQ nu i).comp (lagP nu i)
      = (((Real.sqrt (omega nu) : ℝ) : ℂ) * (((Real.sqrt (omega nu))⁻¹ : ℝ) : ℂ)) •
        ((mom i).comp (pos i) - (pos i).comp (mom i)) := by
    simp only [lagP, lagQ, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
    rw [mul_comm ((((Real.sqrt (omega nu))⁻¹ : ℝ)) : ℂ) (((Real.sqrt (omega nu) : ℝ)) : ℂ)]
    module
  rw [hL, comm_mom_pos i, hscal, one_smul]

theorem comm_lagP_lagQ_of_ne {i k : Fin 3} (h : i ≠ k) :
    (lagP nu i).comp (lagQ nu k) = (lagQ nu k).comp (lagP nu i) := by
  simp only [lagP, lagQ, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
    comm_mom_pos_of_ne h]
  rw [mul_comm]

theorem half_lagPSq_add_nu_lagQSq (hnu : 0 < nu) (i : Fin 3) :
    (1 / 2 : ℂ) • (lagP nu i).comp (lagP nu i)
        + ((nu : ℝ) : ℂ) • (lagQ nu i).comp (lagQ nu i)
      = ((omega nu : ℝ) : ℂ) • numOp i + ((omega nu / 2 : ℝ) : ℂ) • LinearMap.id := by
  have hw : 0 < omega nu := omega_pos nu hnu
  have hsq : Real.sqrt (omega nu) * Real.sqrt (omega nu) = omega nu :=
    Real.mul_self_sqrt (le_of_lt hw)
  have hspos : 0 < Real.sqrt (omega nu) := Real.sqrt_pos.mpr hw
  have hP : (lagP nu i).comp (lagP nu i) = ((omega nu : ℝ) : ℂ) • (mom i).comp (mom i) := by
    simp only [lagP, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, ← Complex.ofReal_mul,
      hsq]
  have hQ : (lagQ nu i).comp (lagQ nu i)
      = (((omega nu)⁻¹ : ℝ) : ℂ) • (pos i).comp (pos i) := by
    have hinv : (Real.sqrt (omega nu))⁻¹ * (Real.sqrt (omega nu))⁻¹ = (omega nu)⁻¹ := by
      rw [← mul_inv, hsq]
    simp only [lagQ, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, ← Complex.ofReal_mul,
      hinv]
  have hnuw : nu * (omega nu)⁻¹ = omega nu / 2 := by
    have h2 : omega nu * omega nu = 2 * nu := omega_sq nu (le_of_lt hnu)
    field_simp
    linarith [h2]
  have hcombine : (1 / 2 : ℂ) • (((omega nu : ℝ) : ℂ) • (mom i).comp (mom i))
        + ((nu : ℝ) : ℂ) • ((((omega nu)⁻¹ : ℝ) : ℂ) • (pos i).comp (pos i))
      = ((omega nu / 2 : ℝ) : ℂ) • ((pos i).comp (pos i) + (mom i).comp (mom i)) := by
    have hs : ((nu : ℝ) : ℂ) * (((omega nu)⁻¹ : ℝ) : ℂ) = ((omega nu / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, hnuw]
    have hs2 : (1 / 2 : ℂ) * ((omega nu : ℝ) : ℂ) = ((omega nu / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    simp only [smul_smul, hs, hs2]
    module
  rw [hP, hQ, hcombine, posSq_add_momSq i]
  have hs3 : ((omega nu / 2 : ℝ) : ℂ) * (2 : ℂ) = ((omega nu : ℝ) : ℂ) := by
    push_cast
    ring
  simp only [smul_add, smul_smul, hs3]

@[simp] theorem lagCanData_drive (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    (lagCanData nu hnu f).drive = (lagCanData nu hnu f).P := rfl

theorem crd_coreState (β γ : Vel) : crd (coreState β) γ = if γ = β then 1 else 0 := by
  classical
  simp [crd, coreState, lp.single_apply, Pi.single_apply]

theorem numOp_coreState (i : Fin 3) (β : Vel) :
    numOp i (coreState β) = ((β i : ℝ) : ℂ) • coreState β := by
  classical
  refine crd_injective ?_
  funext γ
  rw [crd_numOp, crd_smul]
  by_cases hγ : γ = β
  · subst hγ
    simp [crd_coreState]
  · simp [crd_coreState, hγ]

theorem lagT_coreState (β : Vel) :
    lagT nu (coreState β) = ((lagLam nu β : ℝ) : ℂ) • coreState β := by
  simp only [lagT, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.id_apply, numOp_coreState, ← Finset.sum_smul, smul_smul, ← add_smul, lagLam]
  congr 1
  push_cast
  ring

theorem coreState_total (w : L2I Vel)
    (hw : ∀ β : Vel, (inner ℂ ((coreState β : lpFiniteModes Vel) : L2I Vel) w : ℂ) = 0) :
    w = 0 := by
  ext β
  have h := hw β
  rw [show ((coreState β : lpFiniteModes Vel) : L2I Vel) = lp.single 2 β 1 from rfl,
    lp.inner_single_left] at h
  simpa using h

end LagrangianCanonical
end BookProof.NavierStokesFlow
#print axioms BookProof.NavierStokesFlow.LagrangianCanonical.lagT_coreState

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.lagT_coreState
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent














variable (nu : ℝ)
theorem solution (β : Vel) :
    lagT nu (coreState β) = ((lagLam nu β : ℝ) : ℂ) • coreState β := by
  apply BookProof.NavierStokesFlow.LagrangianCanonical.lagT_coreState <;> assumption
#print axioms solution
