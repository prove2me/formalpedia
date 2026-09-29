-- Prove2me | solution 1 for BookProof.BRSTNilpotent.brst_charge_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:58:37.559475+00:00
-- url     : https://prove2.me/submissions/6b29a8eb-2392-4019-affe-6b57a1d96c35

-- Generated from ChapterBRSTNilpotent.lean — solution of BookProof.BRSTNilpotent.brst_charge_nilpotent
import Mathlib
import Definitions.Def_ChapterBRSTNilpotent
import Theorems.Thm_BookProof_BRSTNilpotent_beta_move
import Theorems.Thm_BookProof_BRSTNilpotent_quartic_term_zero
import Theorems.Thm_BookProof_BRSTNilpotent_contracted_terms_zero
open BookProof.BRSTNilpotent













variable {R : Type*} [Ring R] [Algebra ℝ R]
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (f : Fin n → Fin n → Fin n → ℝ) (χ β : Fin n → R)
    (hCAR : GhostCAR χ β)
    (hf12 : ∀ a b c, f a b c = -f b a c)
    (hjac : ∀ a b c h : Fin n,
      ∑ e, (f a b e * f e c h + f b c e * f e a h + f c a e * f e b h) = 0) :
    Q f χ β * Q f χ β = 0 := by

  -- Apply the definitions of `Q` and `beta_move` to expand `Q * Q`.
  have h_expand : Q f χ β * Q f χ β = ∑ a,    ∑ b, ∑ e, ∑ d, ∑ g, ∑ h, (f a b e * f d g h) • (χ a *
      χ b * β e * χ d * χ g * β h) := by
    unfold Q;
    simp only [Finset.sum_mul _ _ _, Finset.mul_sum, mul_smul_comm, Algebra.smul_mul_assoc,
        smul_smul];
    ac_rfl;
  -- Apply `beta_move` to rewrite each term in the expansion.
  have h_rewrite : ∀ a b e d g h,    χ a * χ b * β e * χ d * χ g * β h = (if e = d then χ a * χ b *
      χ g * β h else 0) - (if e = g then χ a * χ b * χ d * β h else 0) + χ a * χ b * χ d * χ g * β e
          * β h := by
    intro a b e d g h;
    convert congr_arg ( fun x => χ a * χ b * x * β h ) ( beta_move χ β hCAR e d g ) using 1 <;> simp
        [ mul_assoc ];
    simp [ mul_add, add_mul, mul_assoc, sub_mul, mul_sub ];
  -- Substitute the rewritten terms back into the expansion.
  have h_substitute : Q f χ β * Q f χ β = (∑ a, ∑ b, ∑ e, ∑ g, ∑ h, (f a b e * f e g h) • (χ a * χ b
      * χ g * β h)) - (∑ a, ∑ b, ∑ e, ∑ d, ∑ h, (f a b e * f d e h) • (χ a * χ b * χ d * β h)) + (∑
          a, ∑ b, ∑ e, ∑ d, ∑ g, ∑ h, (f a b e * f d g h) • (χ a * χ b * χ d * χ g * β e * β h)) :=
              by
    rw [ h_expand ];
    simp only [h_rewrite, smul_add, smul_sub, Finset.sum_add_distrib];
    simp ;
  -- Apply the contracted_terms_zero lemma to the second term.
  have h_contracted : ∑ a,    ∑ b,    ∑ e,    ∑ d,    ∑ h,    (f a b e * f d e h) • (χ a * χ b * χ d
      * β h) = -∑ a,    ∑ b, ∑ e, ∑ g, ∑ h, (f a b e * f e g h) • (χ a * χ b * χ g * β h) := by
    simp only [← Finset.sum_neg_distrib];
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl
        fun e he => Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun h hh => ?_;
    rw [ hf12 d e h ] ; ring;
    rw [ neg_smul ];
  convert h_substitute using 1;
  rw [ h_contracted, sub_neg_eq_add, add_assoc, quartic_term_zero f χ β hCAR ];
  rw [ contracted_terms_zero f χ β hCAR hjac, zero_add, zero_add ]
