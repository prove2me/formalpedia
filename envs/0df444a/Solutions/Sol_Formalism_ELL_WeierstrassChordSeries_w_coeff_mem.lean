-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.w_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:57.698447+00:00
-- url     : https://prove2.me/submissions/80f14140-0624-4f23-8e4c-0453bf7d3306

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_it_spec
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_it_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K] (W : WeierstrassCurve K)
variable {W}
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution {w : PowerSeries K} (hw : WFixed W w) (m : ℕ) :
    coeff m w ∈ Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K) := by
  have h := (it_spec hw (m + 1)).1
  rw [PowerSeries.X_pow_dvd_iff] at h
  have hm := h m (Nat.lt_succ_self m)
  rw [map_sub, sub_eq_zero] at hm
  rw [hm]
  obtain ⟨p, hp⟩ := RingHom.mem_range.mp (it_mem
    (Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)) Algebra.subset_adjoin (m + 1))
  rw [← hp, PowerSeries.coeff_map]
  exact (coeff m p).2
end Formalism.ELL.WeierstrassChordSeries
