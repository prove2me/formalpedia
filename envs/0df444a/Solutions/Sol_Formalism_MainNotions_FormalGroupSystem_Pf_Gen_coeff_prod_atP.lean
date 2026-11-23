-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.Gen.coeff_prod_atP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:35.890991+00:00
-- url     : https://prove2.me/submissions/56af7f5b-7f70-454c-a0ff-731e01042e0e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_coeff_atP_single
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_coeff_atP_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset
variable {K Pl : Type} [CommRing K] {ι : Pl → Type}
variable [Fintype Pl]
variable [DecidableEq Pl]
namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen
theorem _root_.solution (g : ∀ v, MvPowerSeries (ι v) K) (n : (Σ v, ι v) →₀ ℕ) :
    MvPowerSeries.coeff n (∏ v, atP v (g v)) = ∏ v, MvPowerSeries.coeff (eqv n v) (g v) := by
  classical
  rw [MvPowerSeries.coeff_prod]
  let l0 : Pl →₀ ((Σ v, ι v) →₀ ℕ) :=
    Finsupp.equivFunOnFinite.symm fun v => eqv.symm (Pi.single v (eqv n v))
  have hl0 : ∀ v, l0 v = eqv.symm (Pi.single v (eqv n v)) := fun v => rfl
  have hmem : l0 ∈ Finset.finsuppAntidiag Finset.univ n := by
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    calc ∑ v ∈ Finset.univ, l0 v = ∑ v, eqv.symm (Pi.single v (eqv n v)) :=
          Finset.sum_congr rfl fun v _ => hl0 v
      _ = n := by rw [← map_sum, Finset.univ_sum_single, AddEquiv.symm_apply_apply]
  rw [Finset.sum_eq_single_of_mem l0 hmem]
  · exact Finset.prod_congr rfl fun v _ => by rw [hl0]; exact coeff_atP_single v (g v) (eqv n v)
  · intro l hl hne
    rw [Finset.mem_finsuppAntidiag] at hl
    by_contra hprod
    apply hne
    have hall : ∀ v, ∃ m, l v = eqv.symm (Pi.single v m) := by
      intro v
      by_contra hv
      push_neg at hv
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ v) (coeff_atP_eq_zero v (g v) (l v) hv))
    choose m hm using hall
    have hn : n = eqv.symm m := by
      rw [← hl.1]
      calc ∑ v ∈ Finset.univ, l v = ∑ v, eqv.symm (Pi.single v (m v)) :=
            Finset.sum_congr rfl fun v _ => hm v
        _ = eqv.symm m := by rw [← map_sum, Finset.univ_sum_single]
    ext1 v
    rw [hm v, hl0, hn, AddEquiv.apply_symm_apply]
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
