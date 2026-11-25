-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prodMinGainBaseLe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:05:07.659345+00:00
-- url     : https://prove2.me/submissions/38aeb73e-1f8e-4315-a10a-847016902fec

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_minGainBaseLe
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_div_pow_gainExponent_le

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
theorem _root_.solution : ProdMinX := by
  intro ι _ k r C C₁ C₂ T' g ν t hk hC h2 hlog hT' hg hν ht hkt hprodν hprodt
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hCk : (C / k) ^ Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r ≤ ((k:ℝ) ^ r)⁻¹ :=
    div_pow_gainExponent_le k r C hk hC h2 hlog
  have hpt : ∀ v, min 1 (Formalism.HermitianLatticeCounting.LatticeSumBounds.xv k r C (ν v) (t v) g) ≤
      min (ν v) T' * t v * (g⁻¹ ^ (2 * r + 2) * ((k:ℝ) ^ r)⁻¹) := by
    intro v
    refine (minGainBaseLe k r C (ν v) T' (t v) g hk hC (hν v) hT' (ht v) hg (hkt v)).trans ?_
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.xv
    have hm : 0 < min (ν v) T' := lt_min (hν v) hT'
    have h0 : 0 ≤ min (ν v) T' * t v * g⁻¹ ^ (2 * r + 2) :=
      mul_nonneg (mul_nonneg hm.le (ht v).le) (by positivity)
    calc min (ν v) T' * t v * g⁻¹ ^ (2 * r + 2) * (C / k) ^ Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r
          ≤ min (ν v) T' * t v * g⁻¹ ^ (2 * r + 2) * ((k:ℝ) ^ r)⁻¹ :=
          mul_le_mul_of_nonneg_left hCk h0
      _ = min (ν v) T' * t v * (g⁻¹ ^ (2 * r + 2) * ((k:ℝ) ^ r)⁻¹) := by ring
  have hnn : ∀ v, 0 ≤ min 1 (Formalism.HermitianLatticeCounting.LatticeSumBounds.xv k r C (ν v) (t v) g) := by
    intro v
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.xv
    have h1 := hν v
    have h3 := ht v
    exact le_min zero_le_one (mul_nonneg (mul_nonneg (mul_nonneg h1.le h3.le) (by positivity))
      (Real.rpow_nonneg (div_nonneg (by linarith) hk0.le) _))
  have hPmin : 0 ≤ ∏ v, min (ν v) T' :=
    Finset.prod_nonneg (fun v _ => (lt_min (hν v) hT').le)
  calc ∏ v, min 1 (Formalism.HermitianLatticeCounting.LatticeSumBounds.xv k r C (ν v) (t v) g)
        ≤ ∏ v, (min (ν v) T' * t v * (g⁻¹ ^ (2 * r + 2) * ((k:ℝ) ^ r)⁻¹)) :=
        Finset.prod_le_prod (fun v _ => hnn v) (fun v _ => hpt v)
    _ = (∏ v, min (ν v) T') * (∏ v, t v) *
          (g⁻¹ ^ (2 * r + 2) * ((k:ℝ) ^ r)⁻¹) ^ Fintype.card ι := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    _ ≤ (C₁ * g) ^ Fintype.card ι * C₂ *
          (g⁻¹ ^ (2 * r + 2) * ((k:ℝ) ^ r)⁻¹) ^ Fintype.card ι := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hprodν hprodt (Finset.prod_nonneg (fun v _ => (ht v).le))
          (hPmin.trans hprodν)
    _ = C₂ * (C₁ * g * g⁻¹ ^ (2 * r + 2) * ((k:ℝ) ^ r)⁻¹) ^ Fintype.card ι := by ring
end Formalism.HermitianLatticeCounting.P
