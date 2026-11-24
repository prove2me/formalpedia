-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.volumeFactor_mul_sq_div_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:26.449838+00:00
-- url     : https://prove2.me/submissions/661e121d-3074-49cb-866e-a33fdf4ceaa3

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_volumeFactor_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (k r : ℕ) (C G T g v Dr loss' JHS Jop dim : ℝ) (hk : 1 ≤ k)
    (hC : 0 < C) (hG : 0 < G) (hT : 0 < T) (hg : 0 < g) (hv : 0 < v) (hDr : 0 < Dr)
    (hdim : 0 < dim) (hJop : 0 ≤ Jop)
    (hABS : Jop ≤ loss' * (C / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r))
    (hrank : JHS ^ 2 ≤ dim * Jop ^ 2) :
    nv k r G T g v * JHS ^ 2 / dim ≤
      (Real.exp 1 * Real.pi / (k * v)) ^ k * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k *
        (loss' ^ 2 * (C / (k * v)) ^ (2 * r * (k - 2 - r)) *
          Dr⁻¹ ^ (2 * (k - 2 - r))) := by
  have hVF : 0 ≤ (Real.exp 1 * Real.pi / (k * v)) ^ k * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k := by
    positivity
  have h1 : JHS ^ 2 / dim ≤ Jop ^ 2 := by rw [div_le_iff₀ hdim]; nlinarith
  have h2 : Jop ^ 2 ≤ (loss' * (C / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r)) ^ 2 :=
    pow_le_pow_left₀ hJop hABS 2
  have h3 : (loss' * (C / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r)) ^ 2 =
      loss' ^ 2 * (C / (k * v)) ^ (2 * r * (k - 2 - r)) * Dr⁻¹ ^ (2 * (k - 2 - r)) := by ring
  rw [volumeFactor_eq k r G T g v]
  calc _ = (Real.exp 1 * Real.pi / (k * v)) ^ k * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k *
        (JHS ^ 2 / dim) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3.le)) hVF
end Formalism.HermitianLatticeCounting.P
