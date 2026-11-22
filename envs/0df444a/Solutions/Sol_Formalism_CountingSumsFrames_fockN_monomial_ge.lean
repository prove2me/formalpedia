-- Prove2me | solution 1 for Formalism.CountingSumsFrames.fockN_monomial_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:51:11.09681+00:00
-- url     : https://prove2.me/submissions/c986aa43-041c-4904-94c5-673826e55b6f

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_fock_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters N) (z : MvPolynomial (Fin N × Fin r) ℚ_[p]) (m0 : Fin N × Fin r →₀ ℕ)
    (hm0 : MultiDeg LL m0) (hc : ‖coeff m0 z‖ = 1) : 1 ≤ ‖fockN p LL z (monomial m0 1)‖ := by
  classical
  have hne : coeff m0 z ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  have hmem : m0 ∈ z.support := mem_support_iff.mpr hne
  unfold fockN
  rw [fock_monomial z m0 hmem]
  have hF : (m0.prod fun _ k => (k.factorial : ℚ_[p])) = ∏ v : Fin N × Fin r, ((m0 v).factorial : ℚ_[p]) :=
    Finsupp.prod_fintype _ _ (fun _ => by simp)
  have hdiv : ∀ i : Fin N, ∃ D : ℕ, (LL.deg i).factorial = (∏ c : Fin r, (m0 (i, c)).factorial) * D := by
    intro i
    rw [← hm0 i]
    exact Nat.prod_factorial_dvd_factorial_sum _ _
  choose D hD using hdiv
  have hprod : (∏ i, ((LL.deg i).factorial : ℚ_[p])) =
      (∏ v : Fin N × Fin r, ((m0 v).factorial : ℚ_[p])) * ((∏ i, D i : ℕ) : ℚ_[p]) := by
    rw [Fintype.prod_prod_type, Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hD i]; push_cast; rfl
  rw [hF, hprod]
  have hF0 : (∏ v : Fin N × Fin r, ((m0 v).factorial : ℚ_[p])) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => by exact_mod_cast (Nat.factorial_pos _).ne'
  have hD0 : ((∏ i, D i : ℕ) : ℚ_[p]) ≠ 0 := by
    have : (∏ i, D i) ≠ 0 := by
      intro h0
      obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp h0
      have := hD i; rw [hi, mul_zero] at this; exact (Nat.factorial_pos _).ne' this
    exact_mod_cast this
  rw [mul_comm (∏ v : Fin N × Fin r, ((m0 v).factorial : ℚ_[p])) _, mul_div_mul_comm, div_self hF0, mul_one, norm_div, hc]
  have hle : ‖((∏ i, D i : ℕ) : ℚ_[p])‖ ≤ 1 := by
    have := Padic.norm_int_le_one (p := p) ((∏ i, D i : ℕ) : ℤ)
    simpa using this
  have hpos : 0 < ‖((∏ i, D i : ℕ) : ℚ_[p])‖ := norm_pos_iff.mpr hD0
  rw [le_div_iff₀ hpos, one_mul]
  exact hle
end Formalism.CountingSumsFrames
