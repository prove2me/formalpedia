-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.mul_eq_one_of_covolume_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:01:31.424861+00:00
-- url     : https://prove2.me/submissions/f6dcfeb6-7bca-4fe4-a589-d163a2831035

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
import Definitions.Def_Lemmata_GeneralBFactSecondVersion_Imports
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_cp_congr
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_cp_prod
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_exists_ne_zero_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
namespace Formalism.IrreducibleCountingLemmas.Z.BN
theorem _root_.solution {k A : Type} [Field k] [Ring A] [Algebra k A] : ∀ (n : ℕ) (V W : Type)
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k V] [FiniteDimensional k W], Module.finrank k V = n →
    IsSemisimpleModule A V → IsSemisimpleModule A W →
    (∀ a : A, cp k V a = cp k W a) → Nonempty (V ≃ₗ[A] W) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V W _ _ _ _ _ _ _ _ _ _ hn hV hW h
  have hdim : Module.finrank k V = Module.finrank k W := by
    have := congrArg natDegree (h 0)
    simpa [cp, LinearMap.charpoly_natDegree] using this
  by_cases hV0 : Subsingleton V
  · have hW0 : Subsingleton W := by
      rw [← Module.finrank_zero_iff (R := k)] at hV0 ⊢
      omega
    exact ⟨0⟩
  · rw [not_subsingleton_iff_nontrivial] at hV0
    obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule A V
    have key : ∀ a : A, (∀ w : W, a • w = 0) → ∀ s : S, a • s = 0 := by
      intro a ha s
      by_contra hne
      obtain ⟨u, hu⟩ := IsSimpleModule.toSpanSingleton_surjective A hne s
      have hu' : (u * a) • s = s := by simpa [mul_smul] using hu
      have hcW : Algebra.lsmul k k W (u * a) = 0 := by
        ext w
        simp [ha]
      have hnil : IsNilpotent (Algebra.lsmul k k V (u * a)) := by
        rw [LinearMap.isNilpotent_iff_charpoly]
        have h1 := h (u * a)
        unfold cp at h1
        rw [h1, hcW, hdim]
        exact (LinearMap.isNilpotent_iff_charpoly (0 : Module.End k W)).mp IsNilpotent.zero
      obtain ⟨m, hm⟩ := hnil
      have hfix : ∀ j : ℕ, ((Algebra.lsmul k k V (u * a)) ^ j) (s : V) = s := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          rw [pow_succ, Module.End.mul_apply]
          have : (Algebra.lsmul k k V (u * a)) (s : V) = s := by
            have := congrArg (Subtype.val) hu'
            simpa [mul_smul] using this
          rw [this, ihj]
      have hs0 : (s : V) = 0 := by
        rw [← hfix m, hm]
        simp
      apply hne
      have : s = 0 := by exact_mod_cast hs0
      rw [this, smul_zero]
    obtain ⟨f, hf⟩ := exists_ne_zero_hom (k := k) key
    have hsurj : Function.Surjective f := LinearMap.surjective_of_ne_zero hf
    obtain ⟨V', hV'⟩ := exists_isCompl S
    obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.ker f)
    let eV : (S × V') ≃ₗ[A] V := Submodule.prodEquivOfIsCompl S V' hV'
    let eC : C ≃ₗ[A] S :=
      (Submodule.quotientEquivOfIsCompl (LinearMap.ker f) C hC).symm ≪≫ₗ
        f.quotKerEquivOfSurjective hsurj
    let eW : (S × LinearMap.ker f) ≃ₗ[A] W :=
      (LinearEquiv.prodCongr eC.symm (LinearEquiv.refl A _)) ≪≫ₗ
        (LinearEquiv.prodComm A _ _) ≪≫ₗ Submodule.prodEquivOfIsCompl (LinearMap.ker f) C hC
    have h' : ∀ a : A, cp k V' a = cp k (LinearMap.ker f) a := by
      intro a
      have h1 : cp k S a * cp k V' a = cp k S a * cp k (LinearMap.ker f) a := by
        rw [← cp_prod, ← cp_prod, cp_congr eV, cp_congr eW, h a]
      exact mul_left_cancel₀ (LinearMap.charpoly_monic _).ne_zero h1
    have hlt : Module.finrank k V' < n := by
      have h1 : Module.finrank k (S × V') = Module.finrank k V :=
        LinearEquiv.finrank_eq (eV.restrictScalars k)
      rw [Module.finrank_prod] at h1
      have : Nontrivial S := IsSimpleModule.nontrivial A S
      have h2 : 0 < Module.finrank k S := Module.finrank_pos
      omega
    obtain ⟨e'⟩ := ih _ hlt V' (LinearMap.ker f) rfl inferInstance inferInstance h'
    exact ⟨eV.symm ≪≫ₗ (LinearEquiv.prodCongr (LinearEquiv.refl A _) e') ≪≫ₗ eW⟩
end Formalism.IrreducibleCountingLemmas.Z.BN
