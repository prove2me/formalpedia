-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gn_quad_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:43:13.195375+00:00
-- url     : https://prove2.me/submissions/c8efb2c7-b434-4316-a163-2e213e226ddf

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
import Theorems.Thm_Formalism_QuantumDeterminants_gn_gram_ff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hz : inWb k r z)
    (hzz : (herm (Hpk k r) z z).re ≤ 0)
    (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) (hc : ∀ b, c (Sum.inr b) = 0) :
    (star c ⬝ᵥ (gramM k r z z' g *ᵥ c)).re ≤ 0 := by
  have key : star c ⬝ᵥ (gramM k r z z' g *ᵥ c) =
      star (c (Sum.inl (Fin.last r))) * (herm (Hpk k r) z z * c (Sum.inl (Fin.last r))) := by
    simp only [_root_.dotProduct, Matrix.mulVec, Fintype.sum_sum_type, hc, star_zero, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero, Pi.star_apply]
    rw [Finset.sum_eq_single (Fin.last r)]
    · rw [Finset.sum_eq_single (Fin.last r)]
      · rw [gn_gram_ff k r z z' g hz, if_pos ⟨rfl, rfl⟩]
      · intro b _ hb
        rw [gn_gram_ff k r z z' g hz, if_neg, zero_mul]
        rintro ⟨_, h2⟩
        exact hb (Fin.ext h2)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · intro a _ ha
      rw [Finset.sum_eq_zero, mul_zero]
      intro b _
      rw [gn_gram_ff k r z z' g hz, if_neg, zero_mul]
      rintro ⟨h1, _⟩
      exact ha (Fin.ext h1)
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h1 : star (c (Sum.inl (Fin.last r))) * c (Sum.inl (Fin.last r)) =
      (Complex.normSq (c (Sum.inl (Fin.last r))) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    first | rfl | skip
  rw [key, show star (c (Sum.inl (Fin.last r))) * (herm (Hpk k r) z z * c (Sum.inl (Fin.last r))) =
      herm (Hpk k r) z z * (star (c (Sum.inl (Fin.last r))) * c (Sum.inl (Fin.last r))) by ring, h1,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith [Complex.normSq_nonneg (c (Sum.inl (Fin.last r)))]
end Formalism.QuantumDeterminants
