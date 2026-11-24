-- Prove2me | solution 1 for Formalism.ELL.LogarithmWeight.log_comp_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:39.67338+00:00
-- url     : https://prove2.me/submissions/da469ae5-1a6b-48d6-b7a2-43cf9d3cecdc

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LogWeight
import Theorems.Thm_Formalism_ELL_LogarithmWeight_coeff_subst_eq_sum
import Theorems.Thm_Formalism_ELL_LogarithmWeight_subst_ga_eq
import Theorems.Thm_Formalism_G_homComp_statement
import Theorems.Thm_Formalism_G_log_exists_unique
import Theorems.Thm_Formalism_G_log_iff_hom_additive


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
open Formalism Formalism.ELL Formalism.ELL.LogarithmWeight
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.LogarithmWeight
theorem _root_.solution [CharZero K] {F : FormalGroup K} {e l : PowerSeries K} (p : K) (hp : p ≠ 0)
    (he : IsHom F F e) (he1 : coeff 1 e = p) (hl : IsLog F l) :
    l.subst e = p • l := by
  have hlh : IsHom F FormalGroup.𝔾ₐ l := ((Formalism.G.log_iff_hom_additive K F l).mp hl).1
  have hh := Formalism.G.homComp_statement K F F FormalGroup.𝔾ₐ e l he hlh
  have h1 : coeff 1 (l.subst e) = p := by
    rw [coeff_subst_eq_sum he.1]
    simp [Finset.sum_range_succ, hl.2.1, he1]
  have hF : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hg : IsLog F (p⁻¹ • l.subst e) := by
    refine ⟨?_, ?_, ?_⟩
    · simp [hh.1]
    · rw [map_smul, h1, smul_eq_mul, inv_mul_cancel₀ hp]
    · simp only [atX, atY]
      rw [PowerSeries.subst_smul hF, hh.2, subst_ga_eq _ hh.1,
        PowerSeries.subst_smul (PowerSeries.HasSubst.X 0),
        PowerSeries.subst_smul (PowerSeries.HasSubst.X 1), smul_add]
  have := (Formalism.G.log_exists_unique K F).unique hg hl
  calc l.subst e = p • (p⁻¹ • l.subst e) := by rw [smul_smul, mul_inv_cancel₀ hp, one_smul]
    _ = p • l := by rw [this]
end Formalism.ELL.LogarithmWeight
