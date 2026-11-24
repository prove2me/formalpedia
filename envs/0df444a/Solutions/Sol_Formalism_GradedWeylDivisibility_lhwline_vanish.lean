-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_vanish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:01.943929+00:00
-- url     : https://prove2.me/submissions/8d8f2abf-3ae0-4b3e-882e-8e835f6fbe66

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_RInv_of
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_CInv_of
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_elim_inv
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_elim_offdiag
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {K : Type} [Field K] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution [Infinite K] (g : MvPolynomial (Fin r × Fin n) K)
    (hR : ∀ a b : Fin r, a < b → rowGen K a b g = Polynomial.C g)
    (hC : ∀ l j : Fin n, l < j → ∀ c : K, colAdd K l j c g = g)
    (hD : ∀ D : Fin r × Fin n → K,
      (∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → D (a, j) = 0) → eval D g = 0) :
    g = 0 := by
  let I : Fin r × Fin n → K := fun v => if (v.1 : ℕ) = v.2 then 1 else 0
  have hmin : ∀ (s : ℕ) (hr : s ≤ r) (hn : s ≤ n), lpMinor K s hr hn ≠ 0 := by
    intro s hr hn h
    have h2 := congrArg (eval I) h
    rw [map_zero, lpMinor, RingHom.map_det] at h2
    have h3 : (eval I).mapMatrix (Matrix.of fun p q : Fin s =>
        (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) K)) = 1 := by
      ext p q
      simp [I, Matrix.one_apply, Fin.ext_iff]
    rw [h3, Matrix.det_one] at h2
    exact one_ne_zero h2
  let Q : MvPolynomial (Fin r × Fin n) K := ∏ s : Fin (min r n),
    lpMinor K (s.val + 1) (by have := s.isLt; have := min_le_left r n; omega)
      (by have := s.isLt; have := min_le_right r n; omega)
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun s _ => hmin _ _ _)
  have hgQ : g * Q = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx0 : eval x Q = 0
    · rw [hx0, mul_zero]
    · have hx : ∀ (s : ℕ) (hr : s + 1 ≤ r) (hn : s + 1 ≤ n), eval x (lpMinor K (s + 1) hr hn) ≠ 0 := by
        intro s hr hn
        have hs : s < min r n := lt_min hr hn
        simp only [Q, map_prod] at hx0
        exact (Finset.prod_ne_zero_iff.mp hx0) ⟨s, hs⟩ (Finset.mem_univ _)
      have hinv := lhwline_elim_inv (fun z : Fin r × Fin n → K => eval z g)
        (lhwline_RInv_of g hR) (lhwline_CInv_of g hC) (min r n) x
      rw [show eval x g = eval (lhwline_elim (min r n) x) g from hinv.symm, hD _ (fun a j h => lhwline_elim_offdiag x hx a j h), zero_mul]
  rcases mul_eq_zero.mp hgQ with h | h
  · exact h
  · exact absurd h hQ
end Formalism.GradedWeylDivisibility
