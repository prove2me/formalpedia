-- Prove2me | solution 1 for Formalism.GM.M.FB.hom_aeval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:06.055866+00:00
-- url     : https://prove2.me/submissions/db254c92-d400-43be-8800-4fa12ae405de

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_hom_freezeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc

set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.M.FB
theorem _root_.solution (LL : Letters N) (ρ : Fin r) (f : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hf : f ∈ Pol p r LL) :
    IsWeightedHomogeneous (wL N r) (aeval (freezeSub p LL ρ) f) LL.total := by
  have hsupp := (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 hf
  rw [f.as_sum, map_sum, ← MvPolynomial.mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule, MvPolynomial.aeval_monomial]
  have hdeg : MultiDeg LL m := hsupp (Finset.mem_coe.2 hm)
  have hpr : IsWeightedHomogeneous (wL N r)
      (m.prod fun v k => (freezeSub p LL ρ v) ^ k) (∑ v ∈ m.support, m v • 1) :=
    MvPolynomial.IsWeightedHomogeneous.prod _ _ _
      (fun v _ => (hom_freezeSub LL ρ v).pow (m v))
  have hC := MvPolynomial.isWeightedHomogeneous_C (R := ℚ_[p]) (wL N r) (coeff m f)
  have key := hC.mul hpr
  have hs : ∑ v ∈ m.support, m v • 1 = ∑ v, m v := by
    simp only [smul_eq_mul, mul_one]
    exact Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by simpa using hv)
  convert key using 1
  · rfl
  · rw [hs, zero_add, Fintype.sum_prod_type]
    simp only [Letters.total]
    exact (Finset.sum_congr rfl fun i _ => hdeg i).symm
end Formalism.GM.M.FB
