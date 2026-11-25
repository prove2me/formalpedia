-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.columnsStatement_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:21:03.80337+00:00
-- url     : https://prove2.me/submissions/f1643783-ea65-48f3-8b59-6f1902411c0f

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupOnCopies
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_onCopies_iff
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_ev_mem
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_ev_cc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_single_point_const_coeff
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_single_point_mem_subspace
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_value_split
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_cc_exp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_expS_add
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_subst_mem


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution : ColumnsStatement := by
  intro R _ d O _ _ B k _ _ _ h w0 h0 m n S f₁ f₂ ι _ cp u P₁ P₂ hf1 hf2 hP1 hP2
  classical
  have gcc : ∀ b : Fin n, constantCoeff (ev (n := n) ![pt k d b] (B.hL k h w0)) = 0 :=
    fun b => ev_cc _ (single_point_const_coeff b) _ h0
  have xcc : ∀ T : Finset (Fin n),
      constantCoeff ((m : k) • ∑ b ∈ T, ev (n := n) ![pt k d b] (B.hL k h w0)) = 0 := by
    intro T
    rw [smul_eq_C_mul, map_mul, map_sum]
    simp [gcc]
  have xmem : ∀ T : Finset (Fin n),
      ((m : k) • ∑ b ∈ T, ev (n := n) ![pt k d b] (B.hL k h w0)) ∈ subV k (Vc d T) :=
    fun T => Subalgebra.smul_mem _
      (sum_mem fun b hb => ev_mem _ _ (single_point_const_coeff b) (single_point_mem_subspace T b hb) _) _
  have emem : ∀ T : Finset (Fin n),
      FB.expS k ((m : k) • ∑ b ∈ T, ev (n := n) ![pt k d b] (B.hL k h w0)) ∈ subV k (Vc d T) := by
    intro T
    unfold FB.expS
    rw [PowerSeries.subst_def]
    exact subst_mem _ (hasSubst_of_constantCoeff_zero fun _ => xcc T) (fun _ => xmem T) _
  have ecc : ∀ T : Finset (Fin n),
      constantCoeff (FB.expS k ((m : k) • ∑ b ∈ T, ev (n := n) ![pt k d b] (B.hL k h w0))) = 1 := by
    intro T
    unfold FB.expS
    exact cc_exp _ (xcc T)
  have hE : FB.expS k ((m : k) • ∑ b : Fin n, ev (n := n) ![pt k d b] (B.hL k h w0)) =
      FB.expS k ((m : k) • ∑ b ∈ S, ev (n := n) ![pt k d b] (B.hL k h w0)) *
        FB.expS k ((m : k) • ∑ b ∈ Sᶜ, ev (n := n) ![pt k d b] (B.hL k h w0)) := by
    rw [← Finset.sum_add_sum_compl S, smul_add]
    unfold FB.expS
    exact expS_add _ _ (xcc S) (xcc Sᶜ)
  have key := value_split (B.FK k) cp u S P₁ P₂ hP1 hP2 f₁ f₂ _ _ ((onCopies_iff _ _).1 hf1)
    ((onCopies_iff _ _).1 hf2) (emem S) (emem Sᶜ) (ecc S) (ecc Sᶜ)
  rw [← hE] at key
  exact key
end Formalism.MainNotions.ModuliIntegralCharts.H1
