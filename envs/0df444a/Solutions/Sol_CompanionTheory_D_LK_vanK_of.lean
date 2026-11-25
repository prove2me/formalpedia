-- Prove2me | solution 1 for CompanionTheory.D.LK.vanK_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:48:11.885664+00:00
-- url     : https://prove2.me/submissions/8cf263bd-4cca-434c-98c0-f681cb4b0b89

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialCommutesWeightOperator
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KTypeCount
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_DoubleSumReduceSecond
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_FilterAll
import Theorems.Thm_CompanionTheory_D_LK_casK_comm
import Theorems.Thm_CompanionTheory_D_LK_wt_split
import Theorems.Thm_CompanionTheory_D_LK_filter_all
import Theorems.Thm_CompanionTheory_D_LK_exists_poly
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_LK_Ft_apply
import Theorems.Thm_CompanionTheory_D_LK_K_type_count
import Theorems.Thm_CompanionTheory_D_LK_differential_commutes_weight_operator
import Theorems.Thm_CompanionTheory_D_LK_lift_bd
import Theorems.Thm_CompanionTheory_D_LK_sup_of_supp
import Theorems.Thm_UpperTheory_Reformulated_B_P6_r26a_PositivityTheory_D_LK_casK_comm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car
open Formalism.REAL (GlRel KHighest IsWeight CasK)
open PI.UpqRep (rhoC nsq lowK)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
variable {n : ℕ} {ε : Fin n → Bool}
namespace CompanionTheory.D.LK
theorem _root_.solution (hC : COK) (hP : WtProj) (hM : WtMajor) : VanK := by
  intro n ε lam V _ _ E hl hE hU hF hmin B j z hB hz hwt hb
  set τ := lowK ε lam + (2 : ℝ) • rhoC ε with hτ
  have hzw : ∀ A, IsWeight E (τ - wt A) (z A) := fun A c => by
    have := congrFun (hwt c) A
    rw [Ft_apply, filter_all, Pi.smul_apply] at this
    rw [eq_sub_of_add_eq this, Pi.sub_apply, Complex.ofReal_sub, sub_smul]
  obtain ⟨w, hw, e⟩ := hC n ε V E hE B j (τ - wt B) z hz (fun c => funext fun A => by
    by_cases h : z A = 0
    · simp [Ft_apply, h]
    · rw [Ft_apply, hzw A c, Pi.smul_apply, ← add_smul, Pi.sub_apply, Pi.sub_apply, wt_split (ε := ε) A, (hz A h).1]
      congr 1; push_cast; ring) hb
  choose S hS hSt hmem using hF
  let W : Submodule ℂ V := ⨆ A, S (z A)
  haveI : ∀ A, FiniteDimensional ℂ (S (z A)) := fun A => hS _
  have hWs : KStab ε E W := fun a b h v hv =>
    (iSup_le fun A y hy => Submodule.mem_iSup_of_mem A (hSt _ a b h y hy) : W ≤ W.comap (E a b)) hv
  obtain ⟨q, hq⟩ := exists_poly (CasK ε E) (fun x y => by
      simp only [CasK, LinearMap.sum_apply, sum_inner, inner_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h
      · rw [Module.End.mul_apply, Module.End.mul_apply, hU a b h, hU b a h.symm]
      · simp) W (fun x hx => by
      simp only [CasK, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      split_ifs with h
      · exact hWs a b h _ (hWs b a h.symm _ hx)
      · simp) (nsq (τ - wt B - rhoC ε) - nsq (rhoC ε))
  have hcq : ∀ c d, ε c = ε d → ∀ x, Polynomial.aeval (CasK ε E) q (E c d x) = E c d (Polynomial.aeval (CasK ε E) q x) :=
    fun c d h x => by
      have : Commute (E c d) (Polynomial.aeval (CasK ε E) q) := by
        rw [Polynomial.aeval_eq_sum_range]
        exact Commute.sum_right _ _ _ fun k _ => ((casK_comm hE h).pow_right k).smul_right _
      exact (LinearMap.congr_fun this.eq x).symm
  have h0 : z + lift n (Polynomial.aeval (CasK ε E) q) (bd ε E w) = 0 := by
    funext A
    by_contra hne
    rw [← e] at hne
    have hA : z A ≠ 0 := fun h => hne (by simp [h])
    obtain ⟨ν, y, hy0, hy, hs, hd, hc⟩ := hM n ε V E hE hU (fun x => ⟨S x, hS x, hSt x, hmem x⟩) (τ - wt A) _ _ hne
      (fun c => by
        simp only [Pi.add_apply, lift_apply, Pi.sub_apply, Pi.smul_apply]
        rw [map_add, ← hcq c c rfl, map_sub, map_smul, ← Module.End.mul_apply, (casK_comm hE rfl).eq,
          Module.End.mul_apply, hzw A c]
        simp only [map_smul, map_sub, smul_add, smul_sub, Pi.sub_apply, smul_comm ((τ c - wt A c : ℝ) : ℂ)])
      (hq (z A) (Submodule.mem_iSup_of_mem A (hmem _)) _ rfl)
    have hA1 := (hz A hA).1
    refine absurd (hmin ν y hy0 hy) (not_le.2 (K_type_count n ε lam ν B (A.filter (cpt ε)) hl hB
      (fun i hi => (mem_filter.1 (hA1.symm ▸ hi :)).2) (fun i hi => (mem_filter.1 hi).2) hd (fun w hw' => ?_) ?_))
    · convert hc w hw' using 2
      funext c
      simp only [Pi.sub_apply, wt_split (ε := ε) A, hA1, hτ]
      ring
    · have h1 : nsq (τ - wt B - rhoC ε) = nsq (ν + rhoC ε) := by
        have := Complex.ofReal_injective hs
        linarith
      rw [← h1]
      congr 1
      rw [hτ, two_smul]
      abel
  have h1 : bd ε E (-lift n (Polynomial.aeval (CasK ε E) q) w) = z := by
    rw [map_neg, ← lift_bd _ E E fun i hi x => hcq _ _ hi x]
    exact (eq_neg_of_add_eq_zero_left h0).symm
  obtain ⟨t, ht1, ht2, ht3⟩ := hP n (allT n) ε V E hE hU (fun x => ⟨S x, hS x, hSt x, hmem x⟩) (bd ε E)
    (differential_commutes_weight_operator n _ ε V E (fun _ _ _ => rfl) hE) τ _ (h1.symm ▸ hwt)
  exact ⟨t, sup_of_supp hw fun A h => ht3 A (by simp [h]), ht1, ht2.trans h1⟩
end CompanionTheory.D.LK
