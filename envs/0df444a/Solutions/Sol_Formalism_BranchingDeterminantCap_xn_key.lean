-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:15.226935+00:00
-- url     : https://prove2.me/submissions/0aa90470-53f4-4557-832a-b90ebf566fac

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_minor_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_part1
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_part2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
variable {r n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (ι : κ → Fin r) (hι : Function.Injective ι) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ)
    (f : MvPolynomial (Fin r × Fin n) ℂ) (m : ℂ)
    (h0 : ∀ t : Fin n, t.val < p → ∑ b : κ, X (ι b, t) * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f = 0)
    (h1 : ∑ b : κ, X (ι b, (⟨p, hp⟩ : Fin n)) * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f = C m * f) :
    ∑ b : κ, pderiv (ι b, (⟨p, hp⟩ : Fin n))
        (initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp * f) =
      C ((Fintype.card κ : ℂ) - p + m) * (initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) * f) := by
  have hsplit : ∀ b : κ, pderiv (ι b, (⟨p, hp⟩ : Fin n))
      (initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp * f) =
      initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f +
      f * (if b ∈ Finset.univ.image a then 0 else initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp)) := by
    intro b
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, xn_part1 ι hι hp a b]
  simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [xn_part2 ι hp a f m h0 h1]
  by_cases ha : Function.Injective a
  · have hsum : ∑ b : κ, (if b ∈ Finset.univ.image a then (0 : MvPolynomial (Fin r × Fin n) ℂ)
        else initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp)) =
        ((Fintype.card κ : MvPolynomial (Fin r × Fin n) ℂ) - p) *
          initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) := by
      rw [Finset.sum_congr rfl fun b _ => (show (if b ∈ Finset.univ.image a then
          (0 : MvPolynomial (Fin r × Fin n) ℂ) else initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp)) =
          initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) - (if b ∈ Finset.univ.image a then
          initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) else 0) by split_ifs <;> simp)]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, Finset.card_image_of_injective _ ha]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hsum, map_add, map_sub, map_natCast, map_natCast]
    ring
  · have hz : initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) = 0 :=
      xn_minor_zero _ _ fun h => ha h.of_comp
    simp [hz]
end Formalism.BranchingDeterminantCap
