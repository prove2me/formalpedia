-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.independence_bound_of_span_raw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:00:52.18355+00:00
-- url     : https://prove2.me/submissions/ad9d9955-afe7-4bca-a1fb-1f5799245379

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_mm_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_mm_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_mm_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_mm_of_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_mm_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_valuation_nonneg_of_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_frob_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_exists_rel
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_Good_comb
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow
import Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_Cart_Good_c0__int_185a1ab43a5f
import Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_Cart_c0__comb_22429d26040d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
variable {C : Type} [Field C] {V : VF C}
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
namespace Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
theorem _root_.solution [IsAlgClosed C] (X : Cart V d I J) (a : ZMod d) (m : ℕ)
    (hR2 : ∀ (w : I → C) (x : ℕ → I ⊕ J → C), X.Good a w x → (∀ q, V.MM (X.c0' x q)) → ∀ c, V.MM (w c))
    (e : Fin m → J → C)
    (hspan : ∀ (w : I → C) (x : ℕ → I ⊕ J → C), X.Good a w x → (∀ c, V.MM (X.V2 x c)) →
      ∃ b : Fin m → C, ∀ q, V.MM (X.c0' x q ^ V.l - ∑ r, b r * e r q))
    (N : ℕ) (w : Fin N → I → C) (x : Fin N → ℕ → I ⊕ J → C) (hg : ∀ ν, X.Good a (w ν) (x ν))
    (hV : ∀ ν c, V.MM (X.V2 (x ν) c)) (hind : IndepMod V w) : N ≤ m := by
  by_contra hN; push Not at hN
  choose b hb using fun ν => hspan (w ν) (x ν) (hg ν) (hV ν)
  obtain ⟨β, hβi, ⟨ν0, hν0⟩, hrel⟩ := exists_rel (V := V) hN b
  have hl2 : 0 < V.l ^ 2 := pow_pos V.l_prime.pos 2
  choose c hc using fun ν => IsAlgClosed.exists_pow_nat_eq (β ν) hl2
  have hci : ∀ ν, V.Ge 0 (c ν) := fun ν => valuation_nonneg_of_pow (by rw [hc ν]; exact hβi ν) hl2.ne'
  have hG := Cart.Good.comb (X := X) Finset.univ (co := c) (fun ν _ => hci ν) (fun ν _ => hg ν)
  have hz : ∀ ν q, V.Ge 0 (X.c0' (x ν) q) := fun ν q => (hg ν).c0'_int q
  have hc0 : ∀ q, V.MM (X.c0' (∑ ν, teich V.l (c ν) (x ν)) q) := by
    intro q
    rw [Cart.c0'_comb]
    apply mm_of_pow (n := V.l)
    have h1 := frob_sum Finset.univ (fun ν => c ν ^ V.l * X.c0' (x ν) q)
      (fun ν _ => VF.Ge.mul_int ((hci ν).pow _) (hz ν q))
    have e1 : ∀ ν, (c ν ^ V.l * X.c0' (x ν) q) ^ V.l = β ν * X.c0' (x ν) q ^ V.l := by
      intro ν; rw [mul_pow, ← pow_mul, ← hc ν, sq]
    simp only [e1] at h1
    have h2 : V.MM (∑ ν, β ν * (X.c0' (x ν) q ^ V.l - ∑ r, b ν r * e r q)) :=
      mm_sum fun ν _ => mm_mul_int (hβi ν) (hb ν q)
    have h3 : ∑ ν, β ν * (∑ r, b ν r * e r q) = 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun r _ => ?_
      calc ∑ ν, β ν * (b ν r * e r q) = (∑ ν, β ν * b ν r) * e r q := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
        _ = 0 := by rw [hrel r, zero_mul]
    have e2 : (∑ ν, c ν ^ V.l * X.c0' (x ν) q) ^ V.l =
        ((∑ ν, c ν ^ V.l * X.c0' (x ν) q) ^ V.l - ∑ ν, β ν * X.c0' (x ν) q ^ V.l) +
          ∑ ν, β ν * (X.c0' (x ν) q ^ V.l - ∑ r, b ν r * e r q) + ∑ ν, β ν * (∑ r, b ν r * e r q) := by
      simp only [mul_sub, Finset.sum_sub_distrib]; ring
    rw [e2, h3, add_zero]
    exact mm_add h1 h2
  have hw := hR2 _ _ hG hc0
  have hcm := hind c hci (fun y => by
    have := hw y
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this)
  apply hν0
  rw [← hc ν0]
  exact mm_pow (hcm ν0) hl2.ne'
end Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
