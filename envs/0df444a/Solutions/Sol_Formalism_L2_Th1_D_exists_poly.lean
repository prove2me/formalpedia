-- Prove2me | solution 1 for Formalism.L2.Th1.D.exists_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:56:00.341605+00:00
-- url     : https://prove2.me/submissions/56ed2711-f7ef-4366-b3d3-511880514fb4

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
theorem _root_.solution (r : MonoidAlgebra ℤ (muSub l)) :
    ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ∀ m : ℕ, n ∣ m → 0 < m → ∀ ζ : ℂ_[l], IsPrimitiveRoot ζ m →
      ∃ P : Polynomial ℤ, ∀ k : ℕ, P.eval₂ (Int.castRingHom ℂ_[l]) (ζ ^ k) = evK l k r := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    obtain ⟨n, hn, hln, hg⟩ := g.2
    refine ⟨n, hn, hln, fun m hnm hm ζ hζ => ?_⟩
    have hgm : (g : ℂ_[l]) ^ m = 1 := by
      obtain ⟨c, rfl⟩ := hnm
      rw [pow_mul, hg, one_pow]
    have : NeZero m := ⟨hm.ne'⟩
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hgm
    refine ⟨Polynomial.X ^ i, fun k => ?_⟩
    rw [evK_of, ← hi, Polynomial.eval₂_pow, Polynomial.eval₂_X, ← pow_mul, ← pow_mul, mul_comm]
  | add x y hx hy =>
    obtain ⟨n, hn, hln, hP⟩ := hx
    obtain ⟨n', hn', hln', hP'⟩ := hy
    refine ⟨n * n', Nat.mul_pos hn hn', fun h => ?_, fun m hnm hm ζ hζ => ?_⟩
    · rcases (Fact.out : l.Prime).dvd_mul.mp h with h | h
      exacts [hln h, hln' h]
    · obtain ⟨P, hP⟩ := hP m (dvd_trans (dvd_mul_right _ _) hnm) hm ζ hζ
      obtain ⟨P', hP'⟩ := hP' m (dvd_trans (dvd_mul_left _ _) hnm) hm ζ hζ
      exact ⟨P + P', fun k => by rw [Polynomial.eval₂_add, map_add, hP, hP']⟩
  | smul a x hx =>
    obtain ⟨n, hn, hln, hP⟩ := hx
    refine ⟨n, hn, hln, fun m hnm hm ζ hζ => ?_⟩
    obtain ⟨P, hP⟩ := hP m hnm hm ζ hζ
    exact ⟨Polynomial.C a * P, fun k => by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, hP, zsmul_eq_mul, map_mul, map_intCast, eq_intCast]⟩
end Formalism.L2.Th1.D
