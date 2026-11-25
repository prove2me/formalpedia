-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.chebyshev_to_threshold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:35:52.240026+00:00
-- url     : https://prove2.me/submissions/dae3c19f-65cc-466e-8fc8-f37c593c7458

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.ChebToThreshold := by
  intro L f d pl sa al bt κ len lv be X B Mx hκ hlen hba hsa h1 h2
  have hc : κ ^ (1 - (d : ℤ)) * κ ^ d = κ := by
    rw [← zpow_natCast, ← zpow_add₀ hκ.ne']
    simp
  set c := κ ^ (1 - (d : ℤ)) with hcdef
  have hcpos : 0 < c := zpow_pos hκ _
  have e1 : ∏ a, sa a = c ^ L * ∏ a, lv (pl a) := by
    simp only [hsa, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have e2 : ∏ a, (1 / 2 : ℝ) * (4 / (bt a - al a)) ^ d = ∏ a : Fin L, (1 / 2 : ℝ) * (4 / len) ^ d := by
    simp only [hba]
  have e3 : ∏ a, κ * be (pl a) = c ^ L * (κ ^ d) ^ L * ∏ a, be (pl a) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow, hc]
  have e4 : ∏ a, (1 / 2 : ℝ) * be (pl a) * (4 * κ / len) ^ d =
      (∏ a : Fin L, (1 / 2 : ℝ) * (4 / len) ^ d) * (κ ^ d) ^ L * ∏ a, be (pl a) := by
    have hterm : ∀ a : Fin L, (1 / 2 : ℝ) * be (pl a) * (4 * κ / len) ^ d =
        ((1 / 2 : ℝ) * (4 / len) ^ d) * κ ^ d * be (pl a) := by
      intro a
      rw [show 4 * κ / len = (4 / len) * κ by ring, mul_pow]
      ring
    rw [Finset.prod_congr rfl (fun a _ => hterm a), Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const (κ ^ d), Finset.card_univ, Fintype.card_fin]
  rw [e2, e1] at h1
  rw [e3] at h2
  rw [e4]
  have hPh : 0 ≤ ∏ a : Fin L, (1 / 2 : ℝ) * (4 / len) ^ d :=
    Finset.prod_nonneg (fun a _ => by positivity)
  have hcL : 0 < c ^ L := pow_pos hcpos L
  have key : c ^ L * ((∏ a, lv (pl a)) * X) ≤
      c ^ L * ((∏ a : Fin L, (1 / 2 : ℝ) * (4 / len) ^ d) * (κ ^ d) ^ L * (∏ a, be (pl a)) * Mx) := by
    calc c ^ L * ((∏ a, lv (pl a)) * X) = c ^ L * (∏ a, lv (pl a)) * X := by ring
      _ ≤ (∏ a : Fin L, (1 / 2 : ℝ) * (4 / len) ^ d) * B := h1
      _ ≤ (∏ a : Fin L, (1 / 2 : ℝ) * (4 / len) ^ d) *
            ((c ^ L * (κ ^ d) ^ L * ∏ a, be (pl a)) * Mx) := mul_le_mul_of_nonneg_left h2 hPh
      _ = _ := by ring
  exact le_of_mul_le_mul_left key hcL
end Formalism.FourierDecayAlt.P
