-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.Gen.jp_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:57.213956+00:00
-- url     : https://prove2.me/submissions/6ac45239-9038-4228-9de2-95264181e72e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_jp_eq_sum
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_coeff_prod_atP
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_coeff_prod_rename
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_fac_eq

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
namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen
theorem _root_.solution {K A Pl : Type} [CommRing K] [CommRing A] [Algebra K A] [Fintype Pl] [DecidableEq Pl] {ι : Pl → Type}
    [∀ v, Fintype (ι v)] (P : ∀ v, MvPolynomial (ι v) A) (g : ∀ v, MvPowerSeries (ι v) K) :
    jp (∏ v, MvPolynomial.rename (Sigma.mk v) (P v)) (∏ v, atP v (g v)) = ∏ v, jp (P v) (g v) := by
  classical
  have hsub : (∏ v, MvPolynomial.rename (Sigma.mk v) (P v)).support ⊆
      (Fintype.piFinset fun v => (P v).support).image eqv.symm := by
    intro n hn
    rw [MvPolynomial.mem_support_iff, coeff_prod_rename] at hn
    rw [Finset.mem_image]
    refine ⟨eqv n, ?_, AddEquiv.symm_apply_apply _ _⟩
    rw [Fintype.mem_piFinset]
    intro v
    rw [MvPolynomial.mem_support_iff]
    exact fun h0 => hn (Finset.prod_eq_zero (Finset.mem_univ v) h0)
  rw [jp_eq_sum _ _ _ hsub, Finset.sum_image (fun x _ y _ h => eqv.symm.injective h)]
  unfold jp
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_prod_atP, coeff_prod_rename, fac_eq]
  simp only [AddEquiv.apply_symm_apply, Algebra.smul_def, Nat.cast_prod, map_mul, map_prod,
    Finset.prod_mul_distrib]
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
