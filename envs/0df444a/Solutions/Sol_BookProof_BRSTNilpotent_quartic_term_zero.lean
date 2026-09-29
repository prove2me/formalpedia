-- Prove2me | solution 1 for BookProof.BRSTNilpotent.quartic_term_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:32:05.262519+00:00
-- url     : https://prove2.me/submissions/25be44a1-716d-40fc-996f-d5903a2a9557

-- Generated from ChapterBRSTNilpotent.lean — solution of BookProof.BRSTNilpotent.quartic_term_zero
import Mathlib
import Definitions.Def_ChapterBRSTNilpotent
import Theorems.Thm_BookProof_BRSTNilpotent_chi_swap4
open BookProof.BRSTNilpotent













variable {R : Type*} [Ring R] [Algebra ℝ R]
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (f : Fin n → Fin n → Fin n → ℝ) (χ β : Fin n → R)
    (hCAR : GhostCAR χ β) :
    (∑ a, ∑ b, ∑ e, ∑ d, ∑ g, ∑ h,
      (f a b e * f d g h) • (χ a * χ b * χ d * χ g * β e * β h)) = 0 := by

  by_contra h_nonzero;
  -- Reindex the sum by swapping the two index-triples `(a,b,e) ↔ (d,g,h)`.
  have h_reindex : ∑ a : Fin n,    ∑ b : Fin n,    ∑ e : Fin n,    ∑ d : Fin n,    ∑ g : Fin n,    ∑
      h : Fin n,    (f a b e * f d g h) • (χ a * χ b * χ d * χ g * β e * β h) = ∑ a : Fin n,    ∑ b
          : Fin n,    ∑ e : Fin n,    ∑ d : Fin n,    ∑ g : Fin n, ∑ h : Fin n, (f a b e * f d g h)
              • (χ d * χ g * χ a * χ b * β h * β e) := by
    simp only [Finset.sum_sigma'];
    apply Finset.sum_bij (fun x _ => ⟨x.snd.snd.snd.fst, x.snd.snd.snd.snd.fst,
        x.snd.snd.snd.snd.snd, x.fst, x.snd.fst, x.snd.snd.fst⟩);
    · simp;
    · grind;
    · simp only [Finset.univ_sigma_univ, Finset.mem_univ, exists_const, Sigma.exists, forall_const];
      exact fun b => ⟨ b.2.2.2.1, b.2.2.2.2.1, b.2.2.2.2.2, b.1, b.2.1, b.2.2.1, rfl ⟩;
    · simp [ mul_assoc, mul_comm ];
  -- Simplify the summand using the properties of the ghost operators.
  have h_simplify : ∀ a b e d g h : Fin n,    (f a b e * f d g h) • (χ d * χ g * χ a * χ b * β h * β
      e) = -(f a b e * f d g h) • (χ a * χ b * χ d * χ g * β e * β h) := by
    intro a b e d g h
    have h_simplify : β h * β e = - (β e * β h) := by
      exact eq_neg_of_add_eq_zero_left ( hCAR.betabeta _ _ );
    simp [ mul_assoc, h_simplify ];
    simp only [← mul_assoc, chi_swap4 χ β hCAR];
  simp only [h_simplify] at h_reindex;
  simp only [neg_smul, Finset.sum_neg_distrib] at h_reindex;
  rw [ eq_neg_iff_add_eq_zero ] at h_reindex;
  simp [ ← two_smul ℝ, h_nonzero ] at h_reindex
