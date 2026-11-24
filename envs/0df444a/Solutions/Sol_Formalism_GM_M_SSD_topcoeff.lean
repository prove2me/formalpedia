-- Prove2me | solution 1 for Formalism.GM.M.SSD.topcoeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:57.762813+00:00
-- url     : https://prove2.me/submissions/38d6cbef-c61c-4352-8084-9330a6ca8983

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_SSD_eq_of_le_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.SSD
open MvPolynomial Finset
variable {σ ι K ι' : Type} [Field K] [DecidableEq σ] [Fintype ι] (sv : ι → σ)
namespace Formalism.GM.M.SSD
theorem _root_.solution (a : ι' → ι → ℕ) (ha : Function.Injective a) (P : ι' → MvPolynomial σ K → Prop)
    (h1 : ∀ L v, P L v → ∀ m ∈ v.support, sd sv m ≤ a L)
    (s : Finset ι') (v : ι' → MvPolynomial σ K) (hv : ∀ L ∈ s, P L (v L)) (L : ι') (hL : L ∈ s)
    (hmax : ∀ L' ∈ s, ∑ k, a L' k ≤ ∑ k, a L k) (m : σ →₀ ℕ) (hm : sd sv m = a L) :
    coeff m (∑ L' ∈ s, v L') = coeff m (v L) := by
  rw [coeff_sum, Finset.sum_eq_single L]
  · intro L' hL' hne'
    by_contra hc'
    have hle := h1 L' (v L') (hv L' hL') m (mem_support_iff.mpr hc')
    rw [hm] at hle
    exact hne' (ha (eq_of_le_sum hle (hmax L' hL')).symm)
  · intro h; exact absurd hL h
end Formalism.GM.M.SSD
