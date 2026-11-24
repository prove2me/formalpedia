-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prodHyperbolicRatioSqLe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:41.170959+00:00
-- url     : https://prove2.me/submissions/dd5d9009-8853-4c09-a3fc-f733829bbc60

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hyperbolicRatioLe
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_maxInvSinhSqLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
private theorem finset_prod_max_one_nonneg {ι : Type*} (s : Finset ι) (y : ι → ℝ) :
    0 ≤ ∏ v ∈ s, max 1 (y v) :=
  Finset.prod_nonneg (fun _ _ => zero_le_one.trans (le_max_left _ _))
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : DegFactorBound := by
  intro ι _ sh ch G Dr T T' HH hTT hsc hG hDr hGeq hHH1 hHH2 hHH3
  have hTT0 : 0 ≤ T * T' := by linarith
  have hHH0 : 0 ≤ HH := le_trans (pow_nonneg hTT0 _) hHH1
  have hper : ∀ v, ((1 + ch v) / sh v) ^ 2 ≤
      9 * (T * T' * max 1 (Dr v ^ 2) * max 1 (1 / G v)) := by
    intro v
    obtain ⟨hs, hc, he⟩ := hsc v
    have h1 := hyperbolicRatioLe (sh v) (ch v) hs hc he
    have h0 : 0 ≤ (1 + ch v) / sh v := by positivity
    have h2 : ((1 + ch v) / sh v) ^ 2 ≤ (3 * max 1 (1 / sh v)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    have h3 : max 1 (1 / sh v) ^ 2 ≤ max 1 (1 / sh v ^ 2) := by
      rcases le_total (1 / sh v) 1 with h | h
      · rw [max_eq_left h, one_pow]; exact le_max_left _ _
      · rw [max_eq_right h, div_pow, one_pow]; exact le_max_right _ _
    have h4 := maxInvSinhSqLe (sh v) (G v) T T' (Dr v) hs (hG v) (hDr v) hTT (hGeq v)
    calc ((1 + ch v) / sh v) ^ 2 ≤ (3 * max 1 (1 / sh v)) ^ 2 := h2
      _ = 9 * max 1 (1 / sh v) ^ 2 := by ring
      _ ≤ 9 * (T * T' * max 1 (Dr v ^ 2) * max 1 (1 / G v)) := by linarith
  rw [← Finset.prod_pow]
  calc ∏ v, ((1 + ch v) / sh v) ^ 2
        ≤ ∏ v, (9 * (T * T' * max 1 (Dr v ^ 2) * max 1 (1 / G v))) :=
        Finset.prod_le_prod (fun v _ => sq_nonneg _) (fun v _ => hper v)
    _ = 9 ^ Fintype.card ι * ((T * T') ^ Fintype.card ι * (∏ v, max 1 (Dr v ^ 2)) *
          ∏ v, max 1 (1 / G v)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
          Finset.prod_const, Finset.prod_const, Finset.card_univ]
    _ ≤ 9 ^ Fintype.card ι * (HH * HH * HH) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (mul_le_mul hHH1 hHH2 (finset_prod_max_one_nonneg _ _) hHH0) hHH3
          (finset_prod_max_one_nonneg _ _) (mul_nonneg hHH0 hHH0)
    _ = 9 ^ Fintype.card ι * HH ^ 3 := by ring
end Formalism.HermitianLatticeCounting.P
