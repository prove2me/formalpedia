-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.cro_dofN_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:14:49.5618+00:00
-- url     : https://prove2.me/submissions/9c3a32c8-c4a4-4e2d-81e0-c771c04631e3

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
import Theorems.Thm_Formalism_L2_Pj_Crude_ordGe_one_iff
import Theorems.Thm_Formalism_L2_Pj_Crude_OrdGe_mul
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_ordGe_sum
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_ordGe_pderiv
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_constCoeff_ev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (F : Fin d → PS k 2 d)
    (hF : ∀ i j, coeff (Finsupp.single ((1 : Fin 2), i) 1) (F j) = if i = j then 1 else 0)
    (b : Fin n) (v : Fin d → k) {t : ℕ} {X : PS k n d} (hX : OrdGe (t + 1) X) :
    OrdGe (t + 1) (DofN F b v X - Lin b v X) := by
  unfold DofN Lin
  rw [← Finset.sum_sub_distrib]
  refine cro_ordGe_sum _ _ fun j _ => ?_
  beta_reduce
  rw [← sub_mul]
  have key : ∀ A : PS k n d, constantCoeff A = v j →
      OrdGe (t + 1) ((A - C (v j)) * pderiv k (b, j) X) := by
    intro A hA
    have h1 : OrdGe 1 (A - C (v j)) := by
      rw [ordGe_one_iff, map_sub, hA, MvPowerSeries.constantCoeff_C, sub_self]
    have h3 := OrdGe.mul h1 (cro_ordGe_pderiv hX (b, j))
    rwa [add_comm] at h3
  apply key
  have hc : ∀ i, constantCoeff (ev ![pt k d b, 0] ((pderiv k ((1 : Fin 2), i)) (F j))) =
      if i = j then 1 else 0 := by
    intro i
    rw [cro_constCoeff_ev]
    · rw [← hF i j]
      first
        | (show coeff (0 + Finsupp.single ((1 : Fin 2), i) 1) (F j) *
              (((0 : Fin 2 × Fin d →₀ ℕ) ((1 : Fin 2), i) : k) + 1) = _
           simp)
        | (unfold pderiv
           show coeff 0 (pderivFun ((1 : Fin 2), i) (F j)) = _
           unfold pderivFun
           simp)
    · intro p l
      fin_cases p <;> simp [pt]
  rw [map_sum]
  first
    | (simp only [map_mul, MvPowerSeries.constantCoeff_C, hc]
       simp)
    | simp [hc]
end Formalism.L2.Pj.Crude
