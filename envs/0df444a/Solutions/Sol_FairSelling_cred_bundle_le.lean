-- Prove2me | solution 1 for FairSelling.cred_bundle_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:14:19.33173+00:00
-- url     : https://prove2.me/submissions/8c9597b3-4394-4c0a-881e-b52e8ff3e501

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsProp6
import Definitions.Def_RequestProject_TwoThirdsGlue
import Definitions.Def_RequestProject_TwoThirdsDescent
import Theorems.Thm_FairSelling_CanonExists_mono


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
omit [Fintype G] [DecidableEq κ]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {ε : ℝ}
    (bg : ι → Finset G) (wit : κ → G) (bidx : κ → ι) (cred : κ → ℝ)
    {R : Finset G} {Q : Finset κ}
    (hwit_mem : ∀ b ∈ Q, wit b ∈ bg (bidx b))
    (hcred_wit : ∀ b ∈ Q, cred b ≤ vbar w p (wit b) + ε)
    (hbval : ∀ j, vbarSum w p (bg j) ≤ 3 * ε)
    (hwit_out : ∀ b ∈ Q, wit b ∉ R)
    (hinj : Set.InjOn wit ↑Q) (j : ι) :
    ∑ b ∈ Q.filter (fun b => bidx b = j), cred b
      ≤ (3 * ε - vbarSum w p (bg j ∩ R))
          + ((Q.filter (fun b => bidx b = j)).card : ℝ) * ε := by
  classical
  have hv0 : ∀ g, 0 ≤ vbar w p g := fun g => le_trans (hp g) (le_max_left _ _)
  set F : Finset κ := Q.filter (fun b => bidx b = j) with hF
  have hsub : F.image wit ⊆ bg j \ R := by
    intro g hg
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hg
    have hbQ : b ∈ Q := (Finset.mem_filter.mp hb).1
    have hbj : bidx b = j := (Finset.mem_filter.mp hb).2
    exact Finset.mem_sdiff.mpr ⟨by rw [← hbj]; exact hwit_mem b hbQ, hwit_out b hbQ⟩
  have hinjF : Set.InjOn wit ↑F :=
    hinj.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)
  have h1 : ∑ b ∈ F, vbar w p (wit b) = ∑ g ∈ F.image wit, vbar w p g := by
    rw [Finset.sum_image (fun x hx y hy h => hinjF hx hy h)]
  have h2 : ∑ g ∈ F.image wit, vbar w p g ≤ ∑ g ∈ bg j \ R, vbar w p g :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => hv0 g)
  have h3 : (∑ g ∈ bg j \ R, vbar w p g) + (∑ g ∈ bg j ∩ R, vbar w p g)
      = ∑ g ∈ bg j, vbar w p g := by
    have hdisj : Disjoint (bg j \ R) (bg j ∩ R) := Finset.disjoint_left.mpr fun x h1 h2 =>
      (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).2
    have hunion : (bg j \ R) ∪ (bg j ∩ R) = bg j := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [← Finset.sum_union hdisj, hunion]
  have h4 : ∑ b ∈ F, cred b ≤ ∑ b ∈ F, (vbar w p (wit b) + ε) :=
    Finset.sum_le_sum (fun b hb => hcred_wit b (Finset.mem_filter.mp hb).1)
  have h5 : ∑ b ∈ F, (vbar w p (wit b) + ε) = (∑ b ∈ F, vbar w p (wit b)) + (F.card : ℝ) * ε := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have h6 := hbval j
  simp only [vbarSum] at h6 ⊢
  rw [h5] at h4
  rw [h1] at h4
  linarith
end FairSelling
