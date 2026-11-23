-- Prove2me | solution 1 for CompanionTheory.D.LK.K_type_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:23.868362+00:00
-- url     : https://prove2.me/submissions/f3ce931b-82b4-4dc2-8625-a3ef92a25e92

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KTypeCount
import Theorems.Thm_CompanionTheory_D_LK_ind_eq
import Theorems.Thm_CompanionTheory_D_LK_wt_eq
import Theorems.Thm_CompanionTheory_D_LK_sc_anti
import Theorems.Thm_CompanionTheory_D_LK_rhoC_eq
import Theorems.Thm_CompanionTheory_D_LK_exists_sort
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_abs_sig
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_normSq_le
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_pair_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_pair_lt
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_rho_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_sig_anti
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_sig_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_term_le
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
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open GlobalTheory.CompanionTheory.DSNormLt (sig sig_anti sig_mul pair_eq term_le normSq_le pair_lt abs_sig rho_eq)
open PI.UpqRep
variable {n : ℕ}
namespace CompanionTheory.D.LK
theorem _root_.solution : NumK := by
  intro n ε lam ν B C hl hB hBn hC _ hdom hn
  set κ := lowK ε lam + rhoC ε - wt B with hκ
  set μ := lowK ε lam + (2 : ℝ) • rhoC ε - wt B - wt C with hμ
  obtain ⟨w, hw, hs⟩ := exists_sort ε κ
  obtain ⟨m, hm, hm2⟩ := hdom w hw
  have i1 : ∑ a, κ (w a) * μ (w a) ≤ ∑ a, κ (w a) * ν a := by
    rw [← sub_nonneg, ← Finset.sum_sub_distrib]
    have e : ∀ a, κ (w a) * ν a - κ (w a) * μ (w a) = ∑ c, ∑ d, (m c d : ℝ) * (κ (w a) * root c d a) := fun a => by
      have := congrFun hm2 a
      simp only [Pi.sub_apply, Function.comp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [← mul_sub, this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_nonneg fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_nonneg fun d _ => ?_
    rw [← Finset.mul_sum]
    by_cases h0 : m c d = 0
    · simp [h0]
    · refine mul_nonneg (Nat.cast_nonneg _) ?_
      simp only [root, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', mem_univ, if_true, sub_nonneg]
      exact hs c d (hm c d h0).1 (hm c d h0).2
  let tC : Fin n → Fin n → ℝ := fun a b => 2 * (ind C a b - ind C b a) - sc ε a b
  have htC : ∀ a b, |tC a b| ≤ if ε a = ε b then 1 else 0 := fun a b => by
    simp only [tC, ind_eq, sc, sig]
    rcases lt_trichotomy a b with h | h | h
    · simp only [dif_pos h, dif_neg h.not_gt, if_pos h]
      by_cases h1 : (⟨(a, b), h⟩ : Pos n) ∈ C
      · have : ε a = ε b := hC _ h1
        simp [h1, this]; norm_num
      · simp only [h1, if_false]; split_ifs <;> simp
    · subst h; simp
    · simp only [dif_pos h, dif_neg h.not_gt, if_pos h, if_neg h.not_gt]
      by_cases h1 : (⟨(b, a), h⟩ : Pos n) ∈ C
      · have : ε a = ε b := (hC _ h1).symm
        simp [h1, this]; norm_num
      · simp only [h1, if_false]; split_ifs <;> simp
  have i2 : ∑ a, κ a * (wt C a - rhoC ε a) ≤ ∑ a, κ (w a) * rhoC ε a := by
    have p1 := pair_eq tC (fun a b => by simp only [tC]; rw [sc_anti ε a b]; ring) κ
    have p2 := pair_eq (sc ε) (sc_anti ε) fun a => κ (w a)
    have e : ∀ a, wt C a - rhoC ε a = (∑ b, tC a b) / 2 := fun a => by
      simp only [tC]
      rw [wt_eq, rhoC_eq, Finset.sum_sub_distrib (f := fun b => 2 * (ind C a b - ind C b a)), ← Finset.mul_sum]
      ring
    simp only [e]
    simp only [rhoC_eq]
    have : ∑ a, ∑ b, tC a b * (κ a - κ b) ≤ ∑ a, ∑ b, sc ε a b * (κ (w a) - κ (w b)) := by
      calc _ ≤ ∑ a, ∑ b, (if ε a = ε b then 1 else 0) * |κ a - κ b| :=
            Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => (le_abs_self _).trans (by
              rw [abs_mul]; exact mul_le_mul_of_nonneg_right (htC a b) (abs_nonneg _))
        _ = ∑ a, ∑ b, (if ε (w a) = ε (w b) then 1 else 0) * |κ (w a) - κ (w b)| := by
            rw [← Equiv.sum_comp w]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Equiv.sum_comp w]
        _ = _ := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            rw [hw, hw, sc, sig]
            by_cases h : ε a = ε b
            · rcases lt_trichotomy a b with h1 | h1 | h1
              · simp [h, h1, abs_of_nonneg (sub_nonneg.2 (hs a b h1 h))]
              · simp [h1]
              · simp [h, h1, h1.not_gt, abs_of_nonpos (sub_nonpos.2 (hs b a h1 h.symm))]
            · simp [h]
    linarith
  have hκw : ∀ a, κ (w a) = ν a + rhoC ε a := by
    have e1 : ∑ a, κ a * κ a = ∑ a, κ (w a) * μ (w a) + ∑ a, κ a * (wt C a - rhoC ε a) := by
      rw [Equiv.sum_comp w fun a => κ a * μ a, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [hκ, hμ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have e2 : ∑ a, κ (w a) * κ (w a) = ∑ a, κ a * κ a := Equiv.sum_comp w fun a => κ a * κ a
    have e3 : ∑ a, (κ (w a) - (ν a + rhoC ε a)) ^ 2 = ∑ a, κ (w a) * κ (w a) - 2 * ∑ a, κ (w a) * ν a -
        2 * ∑ a, κ (w a) * rhoC ε a + ∑ a, (ν a + rhoC ε a) * (ν a + rhoC ε a) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    have hn' : ∑ a, (ν a + rhoC ε a) * (ν a + rhoC ε a) = ∑ a, κ a * κ a := hn
    have h0 : ∑ a, (κ (w a) - (ν a + rhoC ε a)) ^ 2 = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    intro a
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 h0 a (mem_univ _)
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  let t : Fin n → Fin n → ℝ := fun a b =>
    (sig a b - sc ε a b) - 2 * (ind B a b - ind B b a) + sc ε (w.symm a) (w.symm b)
  have hws : ∀ c, ε (w.symm c) = ε c := fun c => by rw [← hw, Equiv.apply_symm_apply]
  have ta : ∀ a b, t b a = -t a b := fun a b => by
    simp only [t]; rw [sig_anti a b, sc_anti ε a b, sc_anti ε (w.symm a)]; ring
  have tb : ∀ a b, a < b → |t a b| ≤ 1 := fun a b h => by
    simp only [t, ind_eq, dif_pos h, dif_neg h.not_gt, sc, hws]
    by_cases h1 : ε a = ε b
    · rw [if_neg fun h2 => hBn _ h2 h1]
      simpa [h1] using abs_sig _ _
    · simp only [if_neg h1, sig, if_pos h]
      split_ifs <;> norm_num
  have tb' : ∀ a b, |t a b| ≤ 1 := fun a b => by
    rcases lt_trichotomy a b with h | h | h
    · exact tb a b h
    · subst h
      have := ta a a
      rw [show t a a = 0 by linarith]; simp
    · rw [ta, abs_neg]; exact tb b a h
  obtain ⟨⟨⟨c, d⟩, hcd⟩, hi⟩ := hB
  have hne : t c d = -sig c d := by
    have h1 : ¬ε c = ε d := hBn _ hi
    have hcd' : c < d := hcd
    simp only [t, ind_eq, dif_pos hcd', dif_neg hcd'.not_gt, sc, hws, if_neg h1, if_pos hi, sig, if_pos hcd']
    norm_num
  have j1 := pair_lt t ta tb' hl c d (ne_of_lt hcd) hne
  have j2 := normSq_le t ta tb'
  have f1 : ∀ a, (ν + (2 : ℝ) • rhoC ε) (w.symm a) = lam a + (∑ b, t a b) / 2 := fun a => by
    have h1 := hκw (w.symm a)
    have h2 := rho_eq ε a
    have h3 := rhoC_eq ε a
    have h4 := rhoC_eq ε (w.symm a)
    rw [← Equiv.sum_comp w.symm] at h4
    have h5 := wt_eq B a
    simp only [hκ, lowK, Equiv.apply_symm_apply, Pi.add_apply, Pi.sub_apply] at h1
    simp only [t, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
    rw [Finset.sum_sub_distrib (f := fun b => sig a b - sc ε a b), Finset.sum_sub_distrib (f := fun b => sig a b),
      ← Finset.mul_sum]
    linarith
  have f2 : ∀ a, (lowK ε lam + (2 : ℝ) • rhoC ε) a = lam a + (∑ b, sig a b) / 2 := fun a => by
    have := rho_eq ε a
    simp only [lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have ex : ∀ y : Fin n → ℝ, ∑ a, (lam a + y a) * (lam a + y a) =
      ∑ a, lam a ^ 2 + 2 * ∑ a, lam a * y a + ∑ a, y a ^ 2 := fun y => by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  unfold vNormSq nsq dot
  rw [← Equiv.sum_comp w.symm]
  simp only [f1, f2]
  rw [ex, ex]
  linarith
end CompanionTheory.D.LK
