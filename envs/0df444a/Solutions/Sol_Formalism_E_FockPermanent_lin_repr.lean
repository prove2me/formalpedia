-- Prove2me | solution 1 for Formalism.E.FockPermanent.lin_repr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:23:47.570563+00:00
-- url     : https://prove2.me/submissions/b2fa913d-1310-4bf5-8e64-9579b4cbf321

import Definitions.Def_Formalism_FockGram_StatementFock
import Definitions.Def_Formalism_FockGram_FockGramProofs_FockPerm
import Theorems.Thm_Formalism_E_FockPermanent_deg1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix MvPolynomial
noncomputable section
open Formalism Formalism.E
open Formalism.E.FockPermanent
variable {R τ : Type*} [CommRing R]
namespace Formalism.E.FockPermanent
theorem _root_.solution (x : MvPolynomial τ R) (hx : x.IsHomogeneous 1) :
    x = ∑ k ∈ x.vars, C (x.coeff (Finsupp.single k 1)) * X k := by
  classical
  ext n
  rw [coeff_sum]
  simp only [coeff_C_mul, coeff_X]
  by_cases h0 : x.coeff n = 0
  · rw [h0]; symm
    apply sum_eq_zero
    intro k _
    split_ifs with h
    · rw [h, h0, mul_one]
    · rw [mul_zero]
  · have hd : n.degree = 1 := by
      by_contra hd; exact h0 (hx.coeff_eq_zero hd)
    obtain ⟨k, rfl⟩ := deg1 n hd
    rw [sum_eq_single k]
    · simp
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro h; exact hb (Finsupp.single_left_injective one_ne_zero h)
    · intro hk; exfalso; apply hk
      rw [mem_vars]
      exact ⟨Finsupp.single k 1, mem_support_iff.mpr h0, by simp⟩
end Formalism.E.FockPermanent
