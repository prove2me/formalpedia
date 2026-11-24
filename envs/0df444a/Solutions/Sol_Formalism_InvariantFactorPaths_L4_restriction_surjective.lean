-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.restriction_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:27:24.115118+00:00
-- url     : https://prove2.me/submissions/bfa3ef6f-9abf-44df-81f1-c915f2e6046a

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mem_xsp
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mem_y
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_of_free
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_last_letter_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_restriction_mem_space
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycond_mono
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycond_late
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_free_ycond_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pol_zero_free
import Theorems.Thm_Formalism_CountingSumsFrames_pol_finiteDimensional
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_top
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_raising_degree_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_raising_keeps_early_letters
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_raising_keeps_last_letter
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_restriction_raising_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (hΩ : OmegaInj) (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (hv : LL.vec (Fin.last K) = true)
    (hTP : ∀ Mt : WithTop ℤ, ∃ P, IsTypeProj p LL (K + 1) (univ.erase ρ) {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} P) :
    ∀ (o : ℕ), ∀ x ∈ XSp p (setLast LL o) J M ρ,
      ∃ h ∈ Y p (setLast LL o) J M, resL p (Fin.last K, ρ) 0 h = x := by
  intro o
  induction o with
  | zero =>
    intro x hx
    rw [mem_xsp] at hx
    obtain ⟨hxP, hxF, hxk⟩ := hx
    refine ⟨x, (mem_y _ J M x).mpr ⟨hxP, fun k => ?_⟩, resL_of_free _ x hxF⟩
    by_cases hk : K + 1 ≤ J k
    · rw [ycond_late _ (J k) hk]
      exact free_ycond_succ LL hv (M k) (Submodule.mem_inf.mpr ⟨((hxk k).1 hk).1, pol_zero_free LL x hxP⟩)
    · exact (hxk k).2 hk
  | succ o ih =>
    by_cases hfin : ∃ k, K + 1 ≤ J k ∧ M k ≠ ⊤
    ·
      obtain ⟨k1, hk1, hM1⟩ := hfin
      have hne : (univ.filter fun k => K + 1 ≤ J k).Nonempty := ⟨k1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk1⟩⟩
      obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image _ M hne
      have hk0' : K + 1 ≤ J k0 := (Finset.mem_filter.mp hk0).2
      have hmin' : ∀ k, K + 1 ≤ J k → M k0 ≤ M k := fun k hk =>
        hmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
      have hM0 : M k0 ≠ ⊤ := fun h => hM1 (top_le_iff.mp (h ▸ hmin' k1 hk1))
      obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hM0
      set X1 := XSp p (setLast LL (o + 1)) J M ρ with hX1
      set R := (Y p (setLast LL (o + 1)) J M).map (resL p (Fin.last K, ρ) 0) with hR
      have hRle : R ≤ X1 := Submodule.map_le_iff_le_comap.mpr fun h hh =>
        restriction_mem_space (setLast LL (o + 1)) J M ρ hr hρ hv hTP h hh

      have hU : ∀ a : Fin r, ∀ h ∈ Y p (setLast LL o) J M, Uop p LL c univ a h ∈ Y p (setLast LL (o + 1)) J M := by
        intro a h hh
        rw [mem_y] at hh ⊢
        refine ⟨raising_degree_holds p K r LL c univ a o h hh.1, fun k => ?_⟩
        by_cases hk : K + 1 ≤ J k
        · have h1 : h ∈ YCond p LL (K + 1) ((c : ℤ) : WithTop ℤ) := by
            have := hh.2 k0
            rw [ycond_late _ (J k0) hk0', ← hc] at this
            exact this
          rw [ycond_late _ (J k) hk]
          exact ycond_mono LL (K + 1) _ _ (hc ▸ hmin' k hk) (raising_keeps_last_letter p K r LL c a hv h h1)
        · exact raising_keeps_early_letters p K r LL c univ a (J k) (M k) (by omega) h (hh.2 k)
      have hOm : ∀ x ∈ X1, Omega p LL c ρ x ∈ R := by
        intro x hx
        unfold Omega
        rw [LinearMap.sum_apply]
        refine Submodule.sum_mem _ fun a ha => ?_
        have haρ : a ≠ ρ := (Finset.mem_erase.mp ha).1
        obtain ⟨h, hh, hres⟩ := ih _ (pderiv_last_letter_mem LL J M ρ a o hr hρ hv hTP haρ x hx)
        rw [LinearMap.comp_apply]
        have e : dW p K a x = pderiv (Fin.last K, a) x := rfl
        rw [e, ← hres]
        have := restriction_raising_holds p K r LL c ρ a h haρ
        rw [resL_apply, ← this]
        exact Submodule.mem_map_of_mem (f := resL p (Fin.last K, ρ) 0) (hU a h hh)
      have hinj : ∀ x ∈ X1, Omega p LL c ρ x = 0 → x = 0 := by
        intro x hx h0
        have hx' := (mem_xsp _ J M ρ x).mp hx
        refine hΩ p K r LL ρ c o hr hρ hv x (Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hx'.1, hx'.2.1⟩, ?_⟩) h0
        rw [hc]
        exact ((hx'.2.2 k0).1 hk0').2
      have hXP : X1 ≤ Pol p r (setLast LL (o + 1)) := fun x hx => ((mem_xsp _ J M ρ x).mp hx).1
      have := pol_finiteDimensional (p := p) (r := r) (setLast LL (o + 1))
      have : FiniteDimensional ℚ_[p] X1 := Submodule.finiteDimensional_of_le hXP
      let f : X1 →ₗ[ℚ_[p]] X1 := (Omega p LL c ρ).restrict (fun x hx => hRle (hOm x hx))
      have hfi : Function.Injective f := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro y hy
        have : Omega p LL c ρ (y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) = 0 := congrArg Subtype.val hy
        exact Subtype.ext (hinj y y.2 this)
      have hfs : Function.Surjective f := LinearMap.injective_iff_surjective.mp hfi
      intro x hx
      obtain ⟨y, hy⟩ := hfs ⟨x, hx⟩
      have hxy : Omega p LL c ρ (y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) = x := congrArg Subtype.val hy
      have hxR : x ∈ R := hxy ▸ hOm y y.2
      obtain ⟨h, hh, hres⟩ := Submodule.mem_map.mp hxR
      exact ⟨h, hh, hres⟩
    ·
      intro x hx
      rw [mem_xsp] at hx
      obtain ⟨hxP, hxF, hxk⟩ := hx
      refine ⟨x, (mem_y _ J M x).mpr ⟨hxP, fun k => ?_⟩, resL_of_free _ x hxF⟩
      by_cases hk : K + 1 ≤ J k
      · have : M k = ⊤ := by
          by_contra hne
          exact hfin ⟨k, hk, hne⟩
        rw [this, Formalism.CountingSumsFrames.ycond_top]
        exact Submodule.mem_top
      · exact (hxk k).2 hk
end Formalism.InvariantFactorPaths.L4
