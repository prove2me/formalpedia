-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.DescP.nabL_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:04:09.06698+00:00
-- url     : https://prove2.me/submissions/b204f8ca-5f86-4c17-8f6c-a4df1d585d09

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescJet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_DescP_const_dpolyN_eq_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_DescP_hiOrd_sub_trunc
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_DescP_coe_eq_sum

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
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.DescP
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {n d : ℕ}
namespace Formalism.L2.FormalSeriesBounds.DescP
theorem _root_.solution (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (G : PS k n d) (f : PS k n d) :
    nabL F cp u P G f = ∑ μ ∈ (trunc' k (cst P.totalDegree) f).support,
      MvPolynomial.coeff μ (trunc' k (cst P.totalDegree) f) * nabL F cp u P G (monomial μ (1 : k)) := by
  set T : PS k n d := ((trunc' k (cst P.totalDegree) f : MvPolynomial _ k) : PS k n d) with hTdef
  have h0 : nabL F cp u P G (f - T) = 0 := by
    show constantCoeff (DpolyN F cp u P ((f - T) * G)) = 0
    rw [mul_comm]
    exact const_dpolyN_eq_zero F cp u P ((hiOrd_sub_trunc f P.totalDegree).mul_left G)
  have hsplit : nabL F cp u P G f = nabL F cp u P G (f - T) + nabL F cp u P G T := by
    rw [← map_add, sub_add_cancel]
  rw [hsplit, h0, zero_add, hTdef, coe_eq_sum, map_sum]
  simp only [map_smul, smul_eq_mul]
end Formalism.L2.FormalSeriesBounds.DescP
