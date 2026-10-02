-- Prove2me | solution 1 for BenderSuzuki.External.huppert_II_6_11_projective_action
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T13:45:21.408086+00:00
-- url     : https://prove2.me/submissions/5fd59472-b631-4222-9d38-30d48aba89d7

/-
Original formalization: Qiuzhen-CFSG/CFSG and original source authors.
Commit 96b2a02085dc678f3e0a97b334c31ada599c55fd; Apache-2.0.
arexychen: declaration extraction, exact-environment replay, packaging and validation.
Retained mathematical proof bodies are unchanged. Source scopes/visibility and
upload entry names are adapted; accepted cut theorems are imported.

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
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Projectivization.Independence

set_option autoImplicit false
namespace CFSGPackProjectiveAction

section Source6
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/BenderSuzuki/External/Huppert/II/theorem_6_11.lean
/-!
# Huppert II.6.11

The projective special linear group acts doubly transitively on projective
space.  The finite-field degree formula is recorded separately.
-/

namespace BenderSuzuki
namespace External

open scoped LinearAlgebra.Projectivization

universe u

private instance huppert611SLDistribMulAction
    {K : Type u} [Field K] (n : ℕ) :
    DistribMulAction (Matrix.SpecialLinearGroup (Fin n) K) (Fin n → K) :=
  DistribMulAction.compHom (Fin n → K)
    (Matrix.SpecialLinearGroup.toLin' :
      Matrix.SpecialLinearGroup (Fin n) K →* (Fin n → K) ≃ₗ[K] (Fin n → K))

private instance huppert611SLSMulCommClass
    {K : Type u} [Field K] (n : ℕ) :
    SMulCommClass (Matrix.SpecialLinearGroup (Fin n) K) K (Fin n → K) where
  smul_comm A c v := (Matrix.SpecialLinearGroup.toLin' A).map_smul c v

private theorem huppert611_center_mem_projective_perm_ker
    {K : Type u} [Field K] (n : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin n) K)
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)) :
    A ∈ (MulAction.toPermHom (Matrix.SpecialLinearGroup (Fin n) K)
      (ℙ K (Fin n → K))).ker := by
  rw [MonoidHom.mem_ker]
  ext x
  induction x using Projectivization.ind with
  | h v hv =>
      obtain ⟨r, _hrpow, hscalar⟩ :=
        Matrix.SpecialLinearGroup.mem_center_iff.mp hA
      rw [Equiv.Perm.coe_one, id_eq]
      change A • Projectivization.mk K v hv = Projectivization.mk K v hv
      rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
      refine ⟨r, ?_⟩
      change r • v = (Matrix.SpecialLinearGroup.toLin' A) v
      rw [Matrix.SpecialLinearGroup.toLin'_apply]
      funext i
      rw [← hscalar]
      simp [Matrix.toLin'_apply]

private theorem huppert611_mem_center_of_projective_trivial
    {K : Type u} [Field K] (n : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin n) K)
    (hfix : ∀ x : ℙ K (Fin n → K), A • x = x) :
    A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
  have hcolinear :
      ∀ v : Fin n → K,
        ¬ LinearIndependent K ![v, (Matrix.SpecialLinearGroup.toLin' A) v] := by
    intro v
    by_cases hv : v = 0
    · subst v
      intro hli
      exact (hli.ne_zero 0) rfl
    · rw [LinearIndependent.pair_iff' hv]
      simp only [not_forall, not_not]
      have hp := hfix (Projectivization.mk K v hv)
      rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at hp
      exact hp
  obtain ⟨c, hc⟩ :=
    LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
      (f := (Matrix.SpecialLinearGroup.toLin' A).toLinearMap) hcolinear
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨c, ?_, ?_⟩
  · have hdet :
        LinearMap.det (Matrix.SpecialLinearGroup.toLin' A).toLinearMap = 1 := by
      rw [Matrix.SpecialLinearGroup.toLin'_to_linearMap, LinearMap.det_toLin']
      exact A.property
    rw [hc] at hdet
    simpa using hdet
  · have hm := congrArg LinearMap.toMatrix' hc
    have hm' : (A : Matrix (Fin n) (Fin n) K) =
        c • (1 : Matrix (Fin n) (Fin n) K) := by
      simpa [Matrix.SpecialLinearGroup.toLin'_to_linearMap,
        LinearMap.toMatrix_id] using hm
    calc
      Matrix.scalar (Fin n) c = c • (1 : Matrix (Fin n) (Fin n) K) := by
        simpa using (Matrix.smul_one_eq_diagonal (m := Fin n) c).symm
      _ = (A : Matrix (Fin n) (Fin n) K) := hm'.symm

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

private def huppert611_pairIndex {n : ℕ} (hn : 2 ≤ n) (i : Fin 2) : Fin n :=
  finCongr (Nat.add_sub_of_le hn) (finSumFinEquiv (Sum.inl i))

@[simp] private theorem huppert611_reindexEquiv_pairIndex
    {n : ℕ} (hn : 2 ≤ n) {E : Type*} (eTail : Fin (n - 2) ≃ E) (i : Fin 2) :
    ((finCongr (Nat.add_sub_of_le hn).symm).trans <|
      finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) eTail))
        (huppert611_pairIndex hn i) = Sum.inl i := by
  simp only [huppert611_pairIndex, Equiv.trans_apply]
  have hcast :
      finCongr (Nat.add_sub_of_le hn).symm
          (finCongr (Nat.add_sub_of_le hn) (finSumFinEquiv (Sum.inl i))) =
        finSumFinEquiv (Sum.inl i) := by
    apply Fin.ext
    rfl
  rw [hcast, finSumFinEquiv.symm_apply_apply]
  rfl

@[simp] private theorem huppert611_sumExtend_apply_inl
    {K : Type u} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {v : Fin 2 → V} (hv : LinearIndependent K v) (i : Fin 2) :
    Module.Basis.sumExtend hv (Sum.inl i) = v i := by
  classical
  unfold Module.Basis.sumExtend
  dsimp only
  rw [Module.Basis.reindex_apply]
  let s := Set.range v
  let e : Fin 2 ≃ s := Equiv.ofInjective v hv.injective
  let b := hv.linearIndepOn_id.extend (Set.subset_univ s)
  change (Module.Basis.extend hv.linearIndepOn_id)
    ((Trans.trans (Equiv.sumCongr e (Equiv.refl {x : V // x ∈ b \ s}))
      (Equiv.Set.sumDiffSubset (hv.linearIndepOn_id.subset_extend _)))
        (Sum.inl i)) = v i
  have happ :
      (Trans.trans (Equiv.sumCongr e (Equiv.refl {x : V // x ∈ b \ s}))
        (Equiv.Set.sumDiffSubset (hv.linearIndepOn_id.subset_extend _)))
          (Sum.inl i) =
        Equiv.Set.sumDiffSubset (hv.linearIndepOn_id.subset_extend _)
          (Sum.inl (e i)) := rfl
  rw [happ, Equiv.Set.sumDiffSubset_apply_inl,
    Module.Basis.extend_apply_self]
  rfl

private noncomputable def huppert611_projectivePairBasis
    {K : Type u} [Field K] {n : ℕ} (hn : 2 ≤ n)
    (a b : ℙ K (Fin n → K)) (hab : a ≠ b) :
    Module.Basis (Fin n) K (Fin n → K) := by
  let v : Fin 2 → (Fin n → K) := Projectivization.rep ∘ ![a, b]
  have hv : LinearIndependent K v := by
    have hp : Projectivization.Independent ![a, b] :=
      (Projectivization.independent_pair_iff_ne a b).2 hab
    exact Projectivization.independent_iff.mp hp
  let bs := Module.Basis.sumExtend hv
  let E := Module.Basis.sumExtendIndex hv
  letI : Fintype (Fin 2 ⊕ E) :=
    bs.fintypeIndexOfRankLtAleph0 (by simp)
  letI : Finite E := Finite.of_injective
    (fun x : E => (Sum.inr x : Fin 2 ⊕ E))
    (fun _ _ h => Sum.inr.inj h)
  letI : Fintype E := Fintype.ofFinite E
  have hcardE : Fintype.card E = n - 2 := by
    have hdim := Module.finrank_eq_card_basis bs
    have hdim' : n = Nat.card (Fin 2 ⊕ E) := by
      simpa [E, bs, Nat.card_eq_fintype_card] using hdim
    rw [Nat.card_sum, Nat.card_fin] at hdim'
    rw [Nat.card_eq_fintype_card] at hdim'
    omega
  let eTail : Fin (n - 2) ≃ E := Fintype.equivOfCardEq (by simpa using hcardE.symm)
  have hsum : 2 + (n - 2) = n := Nat.add_sub_of_le hn
  let e : Fin n ≃ Fin 2 ⊕ E :=
    (finCongr hsum.symm).trans <|
      (finSumFinEquiv).symm.trans (Equiv.sumCongr (Equiv.refl _) eTail)
  exact bs.reindex e.symm

private theorem huppert611_projectivePairBasis_pairIndex
    {K : Type u} [Field K] {n : ℕ} (hn : 2 ≤ n)
    (a b : ℙ K (Fin n → K)) (hab : a ≠ b) (i : Fin 2) :
    huppert611_projectivePairBasis hn a b hab (huppert611_pairIndex hn i) =
      ![a.rep, b.rep] i := by
  classical
  simp only [huppert611_projectivePairBasis, Module.Basis.reindex_apply,
    Equiv.symm_symm]
  rw [huppert611_reindexEquiv_pairIndex]
  rw [huppert611_sumExtend_apply_inl]
  fin_cases i <;> rfl

/-- Huppert II.6.11: the natural faithful action of `PSL(n,K)` on projective
space is doubly transitive. -/
theorem _root_.solution
    {K : Type u} [Field K] (n : ℕ) (hn : 2 ≤ n) :
    let SL := Matrix.SpecialLinearGroup (Fin n) K
    let PSL := Matrix.ProjectiveSpecialLinearGroup (Fin n) K
    let P := ℙ K (Fin n → K)
    ∃ rho : PSL →* Equiv.Perm P,
      Function.Injective rho ∧
      (∀ (A : SL) (z : P),
        rho (QuotientGroup.mk' (Subgroup.center SL) A) z =
          (Matrix.GeneralLinearGroup.toLin
            (A : GL (Fin n) K)).toLinearEquiv • z) ∧
      (∀ a b c d : P, a ≠ b → c ≠ d →
        ∃ g : PSL, rho g a = c ∧ rho g b = d) := by
  classical
  dsimp only
  let SL := Matrix.SpecialLinearGroup (Fin n) K
  let PSL := Matrix.ProjectiveSpecialLinearGroup (Fin n) K
  let P := ℙ K (Fin n → K)
  let permHom : SL →* Equiv.Perm P := MulAction.toPermHom SL P
  let hcenter_le_ker : Subgroup.center SL ≤ permHom.ker := by
    intro A hA
    exact huppert611_center_mem_projective_perm_ker n A hA
  let rho : PSL →* Equiv.Perm P :=
    QuotientGroup.lift (Subgroup.center SL) permHom hcenter_le_ker
  have hrho : Function.Injective rho := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    constructor
    · intro hx
      rcases QuotientGroup.mk'_surjective (Subgroup.center SL) x with ⟨A, rfl⟩
      rw [MonoidHom.mem_ker] at hx
      have hperm : permHom A = 1 := by
        change (rho.comp (QuotientGroup.mk' (Subgroup.center SL))) A = 1 at hx
        rw [show rho.comp (QuotientGroup.mk' (Subgroup.center SL)) = permHom by
          exact QuotientGroup.lift_comp_mk' (Subgroup.center SL) permHom hcenter_le_ker] at hx
        exact hx
      have hfix : ∀ z : P, A • z = z := by
        intro z
        have hz := congrArg (fun f : Equiv.Perm P => f z) hperm
        simpa [permHom] using hz
      have hcenter := huppert611_mem_center_of_projective_trivial n A hfix
      rw [Subgroup.mem_bot]
      exact (QuotientGroup.eq_one_iff A).mpr hcenter
    · intro hx
      rw [Subgroup.mem_bot] at hx
      simp [hx]
  have hrho_apply :
      ∀ (A : SL) (z : P),
        rho (QuotientGroup.mk' (Subgroup.center SL) A) z =
          (Matrix.GeneralLinearGroup.toLin
            (A : GL (Fin n) K)).toLinearEquiv • z := by
    intro A z
    change A • z = _
    rfl
  refine ⟨rho, hrho, hrho_apply, ?_⟩
  intro a b c d hab hcd
  let ba := huppert611_projectivePairBasis hn a b hab
  let bc := huppert611_projectivePairBasis hn c d hcd
  let std := Pi.basisFun K (Fin n)
  let A : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    ba.equiv std (Equiv.refl _)
  let B : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    std.equiv bc (Equiv.refl _)
  let correction : Kˣ := (LinearEquiv.det B * LinearEquiv.det A)⁻¹
  let w : Fin n → Kˣ := fun j =>
    if j = huppert611_pairIndex hn 0 then correction else 1
  let D : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    std.equiv (std.unitsSMul w) (Equiv.refl _)
  let gLin : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    A.trans (D.trans B)
  have hdetD : LinearEquiv.det D = correction := by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    change LinearMap.det (D : (Fin n → K) →ₗ[K] (Fin n → K)) =
      (correction : K)
    rw [Module.Basis.det_basis, Module.Basis.det_unitsSMul_self]
    rw [Finset.prod_eq_single (huppert611_pairIndex hn 0)]
    · simp [w]
    · intro j _ hj
      simp [w, hj]
    · simp
  have hdetg : LinearEquiv.det gLin = 1 := by
    simp only [gLin, LinearEquiv.det_trans, hdetD]
    simp [correction, mul_comm]
  have hg (i : Fin 2) :
      gLin (![a.rep, b.rep] i) =
        (w (huppert611_pairIndex hn i) : K) • ![c.rep, d.rep] i := by
    rw [← huppert611_projectivePairBasis_pairIndex hn a b hab i]
    change B (D (A (ba (huppert611_pairIndex hn i)))) = _
    rw [show A (ba (huppert611_pairIndex hn i)) =
        std (huppert611_pairIndex hn i) by
      exact Module.Basis.equiv_apply (b := ba) _ std (Equiv.refl _)]
    rw [show D (std (huppert611_pairIndex hn i)) =
        (std.unitsSMul w) (huppert611_pairIndex hn i) by
      exact Module.Basis.equiv_apply (b := std) _ (std.unitsSMul w) (Equiv.refl _)]
    rw [Module.Basis.unitsSMul_apply]
    change B ((w (huppert611_pairIndex hn i) : K) •
      std (huppert611_pairIndex hn i)) = _
    rw [B.map_smul]
    rw [show B (std (huppert611_pairIndex hn i)) =
        bc (huppert611_pairIndex hn i) by
      exact Module.Basis.equiv_apply (b := std) _ bc (Equiv.refl _)]
    rw [huppert611_projectivePairBasis_pairIndex hn c d hcd i]
  let M : Matrix (Fin n) (Fin n) K :=
    LinearMap.toMatrix' (gLin : (Fin n → K) →ₗ[K] (Fin n → K))
  have hMdet : M.det = 1 := by
    have h := congrArg Units.val hdetg
    simpa [M, LinearEquiv.coe_det] using h
  let S : SL := ⟨M, hMdet⟩
  have hSlin : Matrix.SpecialLinearGroup.toLin' S = gLin := by
    apply (LinearEquiv.toLinearMap_injective.eq_iff).mp
    change Matrix.toLin' (LinearMap.toMatrix'
      (gLin : (Fin n → K) →ₗ[K] (Fin n → K))) =
      (gLin : (Fin n → K) →ₗ[K] (Fin n → K))
    exact Matrix.toLin'_toMatrix' _
  let q : PSL := QuotientGroup.mk' (Subgroup.center SL) S
  refine ⟨q, ?_, ?_⟩
  · change S • a = c
    rw [← Projectivization.mk_rep a, ← Projectivization.mk_rep c,
      Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
    refine ⟨(w (huppert611_pairIndex hn 0) : K), ?_⟩
    change (w (huppert611_pairIndex hn 0) : K) • c.rep =
      (Matrix.SpecialLinearGroup.toLin' S) a.rep
    rw [hSlin]
    simpa using (hg 0).symm
  · change S • b = d
    rw [← Projectivization.mk_rep b, ← Projectivization.mk_rep d,
      Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
    refine ⟨(w (huppert611_pairIndex hn 1) : K), ?_⟩
    change (w (huppert611_pairIndex hn 1) : K) • d.rep =
      (Matrix.SpecialLinearGroup.toLin' S) b.rep
    rw [hSlin]
    simpa using (hg 1).symm


end External
end BenderSuzuki


end Source6

end CFSGPackProjectiveAction
