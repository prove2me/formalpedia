-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.weight_zero_span_highest
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:24.685825+00:00
-- url     : https://prove2.me/submissions/ae6efe17-adba-40cc-97bc-41a5d28ce2e2

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_graded_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_psum_sub
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Dle_trans
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Dle_add_right
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_wt_le_of_mem
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_top_of_mem
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_weight_wL
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_wOut_zero
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_weight_cov_monomial
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_dle_cov
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_wt_le_of_mem
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
import Theorems.Thm_Formalism_GM_M_FB_weight_wL
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
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution [NeZero r] (LL : Letters N) (j0 : ℕ) (iK : Fin N) (hiK : (iK : ℕ) < j0)
    (hvK : LL.vec iK = false) (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (la : Fin r → ℤ)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hF : (GA p LL j0).IsHW la F) (u : ℕ) :
    ∀ x ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ (GA p LL j0).gS {F},
        ∃ s ∈ weightedHomogeneousSubmodule ℚ_[p] (wOut N r iK) 0 ⊓
          weightedHomogeneousSubmodule ℚ_[p] (wL N r) (Pi.single iK (u : ℤ)), x = g * s},
      (∀ μ, ¬ Dle μ (la - (u : ℤ) • Pi.single ρ 1) → (GA p LL j0).comp μ x = 0) ∧
      (GA p LL j0).comp (la - (u : ℤ) • Pi.single ρ 1) x ∈ Submodule.span ℚ_[p] {X (iK, ρ) ^ u * F} := by
  classical
  set G := GA p LL j0 with hG
  set la' := la - (u : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) with hla'
  let Ωs : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    { carrier := {x | (∀ μ, ¬ Dle μ la' → G.comp μ x = 0) ∧ G.comp la' x ∈ Submodule.span ℚ_[p] {X (iK, ρ) ^ u * F}}
      add_mem' := by
        intro x y hx hy
        exact ⟨fun μ hμ => by rw [map_add, hx.1 μ hμ, hy.1 μ hμ, add_zero], by rw [map_add]; exact Submodule.add_mem _ hx.2 hy.2⟩
      zero_mem' := ⟨fun μ _ => map_zero _, by rw [map_zero]; exact Submodule.zero_mem _⟩
      smul_mem' := by
        intro c x hx
        exact ⟨fun μ hμ => by rw [map_smul, hx.1 μ hμ, smul_zero], by rw [map_smul]; exact Submodule.smul_mem _ c hx.2⟩ }
  suffices hsuff : Submodule.span ℚ_[p] {x | ∃ g ∈ G.gS {F}, ∃ s ∈ weightedHomogeneousSubmodule ℚ_[p] (wOut N r iK) 0 ⊓
      weightedHomogeneousSubmodule ℚ_[p] (wL N r) (Pi.single iK (u : ℤ)), x = g * s} ≤ Ωs from
    fun x hx => hsuff hx
  rw [Submodule.span_le]
  rintro _ ⟨g, hg, s, hs, rfl⟩
  obtain ⟨S, hS⟩ := G.dec g
  rw [← G.sum_comp g S hS, Finset.sum_mul]
  refine Ωs.sum_mem fun ν _ => ?_
  conv => arg 2; arg 2; rw [s.as_sum]
  rw [Finset.mul_sum]
  refine Ωs.sum_mem fun m hm => ?_

  have hm1 : ∀ v : Fin N × Fin r, v.1 ≠ iK → m v = 0 := wOut_zero ((Submodule.mem_inf.mp hs).1 (mem_support_iff.mp hm))
  have hm2 : ∑ c, m (iK, c) = u := by
    have := congrFun ((Submodule.mem_inf.mp hs).2 (mem_support_iff.mp hm)) iK
    rw [weight_wL] at this
    simp only [Pi.single_eq_same] at this
    exact_mod_cast this
  set wm : Fin r → ℤ := fun c => -((m (iK, c) : ℕ) : ℤ) with hwm
  have hwmm : Finsupp.weight (wv LL j0) m = wm := weight_cov_monomial LL j0 iK hiK hvK m hm1
  have hy : G.comp ν g * monomial m (coeff m s) ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL j0) (ν + wm) := by
    have := (weightedHomogeneousComponent_isWeightedHomogeneous (w := wv LL j0) ν g).mul
      (isWeightedHomogeneous_monomial (wv LL j0) m (coeff m s) hwmm)
    exact this
  have hcomp : ∀ μ, G.comp μ (G.comp ν g * monomial m (coeff m s)) =
      if μ = ν + wm then G.comp ν g * monomial m (coeff m s) else 0 := fun μ =>
    weightedHomogeneousComponent_of_mem hy
  by_cases h0 : G.comp ν g = 0
  · rw [h0, zero_mul]; exact Ωs.zero_mem
  have hgν : G.comp ν g ∈ G.gS {F} := G.graded_of (G.gS_stable _) ν g hg
  have hν : Dle ν la := G.wt_le_of_mem hF hgν (by rw [G.idem, if_pos rfl]; exact h0)
  have hle : Dle (ν + wm) la' := by
    refine Dle_trans (Dle_add_right hν wm) ?_
    have h1 := Dle_add_right (dle_cov ρ hρ u (fun c => m (iK, c)) hm2) la
    rw [hla', sub_eq_add_neg, ← neg_smul]
    simpa [add_comm] using h1
  refine ⟨fun μ hμ => ?_, ?_⟩
  · rw [hcomp, if_neg]; rintro rfl; exact hμ hle
  · rw [hcomp]
    split_ifs with heq
    ·
      have hν' : ν = la' - wm := eq_sub_of_add_eq heq.symm
      have hps := hν.1 (r - 1)
      rw [hν', hla', psum_sub, psum_sub] at hps
      have hp0 : psum ((u : ℤ) • (Pi.single ρ 1 : Fin r → ℤ)) (r - 1) = 0 := by
        unfold psum
        refine Finset.sum_eq_zero fun c _ => ?_
        split_ifs with h
        · have : c ≠ ρ := fun h' => by subst h'; omega
          simp [Pi.single_apply, this]
        · rfl
      have hpw : psum wm (r - 1) = -∑ c : Fin r, (if (c : ℕ) < r - 1 then ((m (iK, c) : ℕ) : ℤ) else 0) := by
        unfold psum; rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs <;> simp [hwm]
      rw [hp0, hpw] at hps
      have hnn : ∀ c ∈ (Finset.univ : Finset (Fin r)), (0 : ℤ) ≤ (if (c : ℕ) < r - 1 then ((m (iK, c) : ℕ) : ℤ) else 0) := by
        intro c _; split_ifs <;> simp
      have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (by linarith [Finset.sum_nonneg hnn])
      have hmc : ∀ c, c ≠ ρ → m (iK, c) = 0 := by
        intro c hc
        have hlt : (c : ℕ) < r - 1 := by
          have := c.isLt
          have : (c : ℕ) ≠ ρ := fun h => hc (Fin.ext h)
          omega
        have := hz c (Finset.mem_univ c)
        rw [if_pos hlt] at this
        exact_mod_cast this
      have hmρ : m (iK, ρ) = u := by
        rw [← hm2, Finset.sum_eq_single ρ (fun c _ hc => hmc c hc) (by simp)]
      have hmeq : m = Finsupp.single (iK, ρ) u := by
        ext v
        by_cases hv1 : v.1 = iK
        · by_cases hv2 : v.2 = ρ
          · have : v = (iK, ρ) := Prod.ext hv1 hv2
            subst this; rw [Finsupp.single_eq_same, hmρ]
          · have : v = (iK, v.2) := Prod.ext hv1 rfl
            rw [this, hmc v.2 hv2, Finsupp.single_eq_of_ne]
            intro h; exact hv2 (Prod.mk.inj h).2
        · rw [hm1 v hv1, Finsupp.single_eq_of_ne]
          intro h; exact hv1 (Prod.mk.inj h).1
      have hwmρ : wm = -((u : ℤ) • (Pi.single ρ 1 : Fin r → ℤ)) := by
        funext c
        simp only [hwm, Pi.neg_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
        by_cases hc : c = ρ
        · subst hc; simp [hmρ]
        · simp [hmc c hc, hc]
      have hνla : ν = la := by rw [hν', hwmρ, hla']; abel
      obtain ⟨c', hc'⟩ := G.comp_top_of_mem hF hg
      have hmono : monomial m (coeff m s) = coeff m s • (X (iK, ρ) ^ u : MvPolynomial (Fin N × Fin r) ℚ_[p]) := by
        rw [hmeq, X_pow_eq_monomial, smul_monomial, smul_eq_mul, mul_one]
      rw [hνla, hc', hmono, smul_mul_smul_comm, mul_comm F]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · exact Submodule.zero_mem _
end Formalism.GM.DimensionMonotonicity
