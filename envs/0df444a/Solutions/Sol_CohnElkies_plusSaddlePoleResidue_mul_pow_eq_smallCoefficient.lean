-- Prove2me | solution 1 for CohnElkies.plusSaddlePoleResidue_mul_pow_eq_smallCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/ee8b7677-643b-4a5d-afcf-d12ccce4eea0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusSaddlePoleResidue_explicit_real
import Theorems.Thm_CohnElkies_saddleSmallRadiusVariable_neg_pow
import Theorems.Thm_CohnElkies_saddleSmallRadiusPhase_pole_factorization

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (n : ℕ) (r : ℝ) :
    plusSaddlePoleResidue ε ℓ n *
        ((r ^ (2 * n) : ℝ) : ℂ) =
      ((saddleOriginValue ε ℓ *
        ((-saddleSmallRadiusVariable ε r) ^ n /
          (n.factorial : ℝ)) *
        plusSaddleSmallRadiusCoefficient ε ℓ n : ℝ) : ℂ) := by
  have hb : beta ε ≠ 0 := (beta_pos hε).ne'
  have hfac : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero n)
  have hpi :
      Real.pi ^ (ℓ / 2 + (n : ℝ)) =
        Real.pi ^ (ℓ / 2) * Real.pi ^ n :=
    Real.rpow_add_natCast Real.pi_ne_zero (ℓ / 2) n
  have hphase := saddleSmallRadiusPhase_pole_factorization
    ε ℓ n
  have hy := saddleSmallRadiusVariable_neg_pow ε r n
  rw [plusSaddlePoleResidue_explicit_real hℓ n,
    ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  unfold saddleOriginValue plusSaddleSmallRadiusCoefficient
  rw [hpi, hphase, hy]
  field_simp [hb, hfac]
end CohnElkies
