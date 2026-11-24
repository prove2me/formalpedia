-- Prove2me | solution 1 for Formalism.L2.G.exists_sq_eq_intCast_of_not_dvd_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:12:19.427827+00:00
-- url     : https://prove2.me/submissions/74aa4966-779a-463f-a097-0f78b16dfe60

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
import Theorems.Thm_Formalism_L2_G_isSquare_algebraMap
import Theorems.Thm_Formalism_L2_G_sq_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n]
namespace Formalism.L2.G
theorem _root_.solution (hp2 : p ≠ 2) (z : ℤ) (hz : ¬ (p : ℤ) ∣ z) : ∃ y : W2 p n, y ^ 2 = (z : W2 p n) := by
  obtain ⟨r, hr⟩ := isSquare_algebraMap p n hp2 (z : F1 p n)
  have hz0 : ((z : ℤ) : F2 p n) ≠ 0 := by
    rw [ne_eq, CharP.intCast_eq_zero_iff (F2 p n) p]; exact hz
  have hc : (z : W2 p n).coeff 0 = r * r := by
    have : WittVector.constantCoeff (z : W2 p n) = ((z : ℤ) : F2 p n) := map_intCast _ _
    rw [← hr, map_intCast]
    exact this
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hz0
    rw [← map_intCast (algebraMap (F1 p n) (F2 p n)), hr, mul_zero]
  have h2 : (2 : F2 p n) ≠ 0 := by
    have : ((2 : ℕ) : F2 p n) ≠ 0 := by
      rw [ne_eq, CharP.cast_eq_zero_iff (F2 p n) p]
      intro hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hdvd)
    simpa using this
  exact sq_lift p n _ r hc hr0 h2
end Formalism.L2.G
