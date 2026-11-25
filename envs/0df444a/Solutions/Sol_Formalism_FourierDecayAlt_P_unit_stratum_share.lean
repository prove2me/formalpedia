-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.unit_stratum_share
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:55:07.085706+00:00
-- url     : https://prove2.me/submissions/4b49704e-1966-428c-966a-f1ec7bfe73b1

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Minors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block32EqZeroOfUnipotent
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x9_cornerCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open Formalism.FourierDecayAlt.P.S3x9 Formalism.FourierDecayAlt.S3 Matrix
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.UnitStratumShare := by
  intro K _ _ r k X₀ u hu
  classical
  set q := Fintype.card K with hq
  have hq1 : 1 ≤ q := Fintype.card_pos
  set κ := Nat.card {Z : Matrix (Idx r k) (Idx r k) K // b31 Z = 0} with hκ
  have c1 : Nat.card {M : Matrix (Idx r k) (Idx r k) K //
        ∀ (l : ℕ) (hl : l ≤ r), cm (X₀ + u * b31 M) l hl ≠ 0} =
      (q ^ (r ^ 2 - r) * (q - 1) ^ r) * κ := by
    rw [Nat.card_congr (splitEquiv K r k
      (fun Y => ∀ (l : ℕ) (hl : l ≤ r), cm (X₀ + u * Y) l hl ≠ 0)), Nat.card_prod,
      ← cornerCount K r]
    congr 1
    exact Nat.card_congr ((affEquiv X₀ u hu).subtypeEquiv fun Y => Iff.rfl)
  have c2 : Nat.card (Matrix (Idx r k) (Idx r k) K) = q ^ (r ^ 2) * κ := by
    have h0 : Nat.card (Matrix (Idx r k) (Idx r k) K) =
        Nat.card {M : Matrix (Idx r k) (Idx r k) K // (fun _ => True) (b31 M)} :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial).symm
    rw [h0, Nat.card_congr (splitEquiv K r k (fun _ => True)), Nat.card_prod,
      Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)]
    congr 1
    show Nat.card (Fin r → Fin r → K) = _
    simp [← pow_mul, sq, hq]
  rw [c1, c2]
  have hr : r ^ 2 = (r ^ 2 - r) + r := by
    have : r ≤ r ^ 2 := by nlinarith [Nat.zero_le r]
    omega
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  push_cast [Nat.cast_sub hq1]
  conv_rhs => rw [hr, pow_add]
  have : (1 - 1 / (q : ℝ)) ^ r * (q : ℝ) ^ r = ((q : ℝ) - 1) ^ r := by
    rw [← mul_pow]; congr 1; field_simp
  calc (q : ℝ) ^ (r ^ 2 - r) * ((q : ℝ) - 1) ^ r * κ
      = (q : ℝ) ^ (r ^ 2 - r) * ((1 - 1 / (q : ℝ)) ^ r * (q : ℝ) ^ r) * κ := by rw [this]
    _ = _ := by ring
end Formalism.FourierDecayAlt.P
