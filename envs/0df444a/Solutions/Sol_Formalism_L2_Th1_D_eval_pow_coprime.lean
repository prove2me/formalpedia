-- Prove2me | solution 1 for Formalism.L2.Th1.D.eval_pow_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:55:59.440823+00:00
-- url     : https://prove2.me/submissions/bad40ba4-0b1a-4264-ba79-fef1986ebd2f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusOnRingA

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
variable (l : ℕ) [Fact l.Prime]
namespace Formalism.L2.Th1.D
theorem _root_.solution {K : Type*} [Field K] [CharZero K] {n k : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (hcop : Nat.Coprime k n) (P : Polynomial ℤ)
    (h : P.eval₂ (Int.castRingHom K) ζ = 0) : P.eval₂ (Int.castRingHom K) (ζ ^ k) = 0 := by
  have h1 : Polynomial.aeval ζ P = 0 := by
    rw [Polynomial.aeval_def]
    exact h
  have hd : minpoly ℤ ζ ∣ P := minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hn) h1
  rw [hζ.minpoly_eq_pow_coprime hcop] at hd
  obtain ⟨Q, rfl⟩ := hd
  have h2 : Polynomial.aeval (ζ ^ k) (minpoly ℤ (ζ ^ k)) = 0 := minpoly.aeval _ _
  rw [Polynomial.aeval_def] at h2
  rw [Polynomial.eval₂_mul]
  exact mul_eq_zero_of_left h2 _
end Formalism.L2.Th1.D
