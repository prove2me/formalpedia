-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.fock_ext_reduce
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:47.314997+00:00
-- url     : https://prove2.me/submissions/4a5a4ef9-37f1-40c1-a79c-b75a1c24c10b

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ltr_isL
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_eq_sum
import Theorems.Thm_Formalism_CountingSumsFrames_TO_eq_sum_sl
import Theorems.Thm_Formalism_CountingSumsFrames_TO_sl_isF
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isL_monomial_ltr
import Theorems.Thm_Formalism_CountingSumsFrames_TO_fock_mul_mono
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_sum_left
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_sum_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last



set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (j0 : ℕ)
    (A φ1 φ2 : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) (c : ℚ_[p])
    (Cs : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hA : ∀ g q, IsL (fsj N r j0) q → A (g * q) = A g * q)
    (hAF : ∀ g, IsF (fsj N r j0) g → IsF (fsj N r j0) (A g))
    (h1 : ∀ x, IsF (fsj N r j0) (φ1 x)) (h2 : ∀ x, IsF (fsj N r j0) (φ2 x))
    (hcore : ∀ g ∈ Cs, ∀ g' ∈ Cs, fock p (A g) (φ1 g') = c * fock p (φ2 g) g')
    (u u' : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hu : ∀ m, slc (fsj N r j0) m u ∈ Cs)
    (hu' : ∀ m, slc (fsj N r j0) m u' ∈ Cs) :
    fock p (A u) (ext (fsj N r j0) φ1 u') = c * fock p (ext (fsj N r j0) φ2 u) u' := by
  classical
  set S : Finset (Fin N × Fin r →₀ ℕ) := (u.support ∪ u'.support).image (ltr (fsj N r j0)) with hS
  have hSu : ∀ m ∈ u.support, ltr (fsj N r j0) m ∈ S := fun m hm =>
    Finset.mem_image_of_mem _ (Finset.mem_union_left _ hm)
  have hSu' : ∀ m ∈ u'.support, ltr (fsj N r j0) m ∈ S := fun m hm =>
    Finset.mem_image_of_mem _ (Finset.mem_union_right _ hm)
  have hSl : ∀ m ∈ S, ∀ v, m v ≠ 0 → ¬ fsj N r j0 v := by
    intro m hm
    obtain ⟨m0, _, rfl⟩ := Finset.mem_image.mp hm
    exact ltr_isL _ m0
  have hSL : ∀ m ∈ S, IsL (fsj N r j0) (monomial m (1 : ℚ_[p])) := by
    intro m hm
    obtain ⟨m0, _, rfl⟩ := Finset.mem_image.mp hm
    exact isL_monomial_ltr _ m0 1
  have hAu : A u = ∑ m ∈ S, A (slc (fsj N r j0) m u) * monomial m 1 := by
    conv_lhs => rw [eq_sum_sl (fsj N r j0) u S hSu]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m hm => hA _ _ (hSL m hm)
  rw [hAu, ext_eq_sum (fsj N r j0) φ1 u' S hSu', ext_eq_sum (fsj N r j0) φ2 u S hSu]
  conv_rhs => rw [eq_sum_sl (fsj N r j0) u' S hSu']
  rw [gammaIntegralityLemmas.fock_sum_left, gammaIntegralityLemmas.fock_sum_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [gammaIntegralityLemmas.fock_sum_right, gammaIntegralityLemmas.fock_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' hm' => ?_
  rw [fock_mul_mono j0 (hAF _ (sl_isF _ m u)) (h1 _) m m' (hSl m hm) (hSl m' hm'),
    fock_mul_mono j0 (h2 _) (sl_isF _ m' u') m m' (hSl m hm) (hSl m' hm')]
  split_ifs with h
  · rw [hcore _ (hu m) _ (hu' m')]; ring
  · simp
end Formalism.CountingSumsFrames.TO
