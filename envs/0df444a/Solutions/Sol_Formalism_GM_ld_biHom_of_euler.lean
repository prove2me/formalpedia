-- Prove2me | solution 1 for Formalism.GM.ld_biHom_of_euler
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:11.652118+00:00
-- url     : https://prove2.me/submissions/17dc1e67-8e57-4ce0-94ec-dafa67b72927

import Definitions.Def_Formalism_MahlerMeasure_LevelDecompR
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ}
namespace Formalism.GM
theorem _root_.solution [CharZero k] {a b : ℕ} {g : MvPolynomial σ k}
    (hW : ∑ c, X (w c) * pderiv (w c) g = (a : k) • g)
    (hE : ∑ c, X (e c) * pderiv (e c) g = (b : k) • g) : BiHom w e a b g := by
  classical
  unfold BiHom
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm
  have hterm : ∀ i : σ, MvPolynomial.coeff m (X i * pderiv i g) = (m i : k) * MvPolynomial.coeff m g := by
    intro i
    rw [MvPolynomial.coeff_X_mul']
    split_ifs with hs
    · have hmi : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)
      have e1 : m - Finsupp.single i 1 + Finsupp.single i 1 = m :=
        tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hmi)
      have e2 : (((m - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : k) + 1 = (m i : k) := by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_same, ← Nat.cast_add_one, Nat.sub_add_cancel hmi]
      rw [MvPolynomial.coeff_pderiv, e1, e2, mul_comm]
    · simp at hs
      simp [hs]
  have key : ∀ (v : Fin r → σ) (n : ℕ), ∑ c, X (v c) * pderiv (v c) g = (n : k) • g → ∑ c, m (v c) = n := by
    intro v n hv
    have hcoef := congrArg (MvPolynomial.coeff m) hv
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul] at hcoef
    simp only [hterm] at hcoef
    rw [← Finset.sum_mul] at hcoef
    have hc := mul_right_cancel₀ hm hcoef
    exact_mod_cast hc
  exact ⟨key w a hW, key e b hE⟩
end Formalism.GM
