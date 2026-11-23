-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.height_descent_of_r3_r2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:51.883521+00:00
-- url     : https://prove2.me/submissions/79d57b8d-9b67-444b-83be-408bfd88b2f2

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_constantCoeff_pi0_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (h3 : UnitFactorQ) (hb : PowerSeriesFreeBasis) : HeightDescent := by
  intro l _ O _ _ hl n h P Q hPQ
  have hs : HasSubst (pi0 l O) := HasSubst.of_constantCoeff_zero' (constantCoeff_pi0_eq_zero l O)
  obtain ⟨g, hg, -⟩ := h3 l O hl
  have hl1 : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  let Φ : O⟦X⟧ →ₐ[O] O⟦X⟧ := substAlgHom hs
  have hinc : ∀ a, inc l O a = Φ a := fun a => (congrFun (coe_substAlgHom hs) a).symm
  have hΦX : Φ X = pi0 l O := by rw [← hinc]; exact subst_X hs
  have hΦq : Φ ((X - C (l : O)) ^ h) = q0 l O ^ h := by
    have hC : (C (l : O) : O⟦X⟧) = ((l : ℕ) : O⟦X⟧) := by simp
    rw [map_pow, map_sub, hΦX, hC, map_natCast, q0, hC]
  choose G hG using fun a b => (hb l O hl ((g : O⟦X⟧) ^ h * Q a b)).exists
  have key : ∀ a b, (fun j : Fin (l - 1) => ∑ c, P a c * G c b j) =
      (fun j : Fin (l - 1) => if j = ⟨0, hl1⟩ then
        (X - C (l : O)) ^ h * (1 : Matrix (Fin n) (Fin n) O⟦X⟧) a b else 0) := by
    intro a b
    apply (hb l O hl (q0 l O ^ h * (1 : Matrix (Fin n) (Fin n) O⟦X⟧) a b)).unique
    · have e1 : q0 l O ^ h * (1 : Matrix (Fin n) (Fin n) O⟦X⟧) a b =
          (g : O⟦X⟧) ^ h * (P.map (inc l O) * Q) a b := by
        rw [hPQ, Matrix.smul_apply, smul_eq_mul, hg, mul_pow]; ring
      rw [e1, Matrix.mul_apply, Finset.mul_sum]
      simp only [Matrix.map_apply]
      calc ∑ c, (g : O⟦X⟧) ^ h * (inc l O (P a c) * Q c b)
          = ∑ c, inc l O (P a c) * ∑ j, inc l O (G c b j) * X ^ (j : ℕ) := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [← hG c b]; ring
        _ = ∑ j, inc l O (∑ c, P a c * G c b j) * X ^ (j : ℕ) := by
            simp only [hinc, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => by ring
    · rw [Finset.sum_eq_single (⟨0, hl1⟩ : Fin (l - 1))]
      · rw [if_pos rfl, hinc, map_mul, hΦq]
        by_cases hab : a = b
        · subst hab; simp
        · simp [Matrix.one_apply_ne hab]
      · intro j _ hj
        rw [if_neg hj, hinc, map_zero, zero_mul]
      · intro hx; exact absurd (Finset.mem_univ _) hx
  refine ⟨Matrix.of fun a b => G a b ⟨0, hl1⟩, ?_⟩
  ext1 a b
  have := congrFun (key a b) ⟨0, hl1⟩
  simp only [if_pos] at this
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  simpa using this
end Formalism.CohomologicalDescent.HeightDescentMinors
