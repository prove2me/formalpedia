-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW.NCovAd_fin_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:18:37.48733+00:00
-- url     : https://prove2.me/submissions/df6194a0-afad-4d65-ae4b-b1d36c8ee96e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IntAdCpctOpen
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_CompactCovering_NCovAd
import Theorems.Thm_PIW_AdelClassFin_DictRing_af_approx
import Theorems.Thm_PIW_AdelClassFin_DictRing_af_denom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Metric
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RescaleCore Formalism.L2.SG.Pf.RescaleCore.NCov
open Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW
theorem _root_.solution (a : Af F) : ∃ x : F, a - algebraMap F (Af F) x ∈ Formalism.UG.intAd F := by
  obtain ⟨m, hm, hma⟩ := PIW.AdelClassFin.DictRing.af_denom a
  obtain ⟨β, y, hy, hβ⟩ := PIW.AdelClassFin.DictRing.af_approx _ hma m hm
  refine ⟨(β : F) / m, ?_⟩
  have hmF : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
  have hcast : ((m : ℕ) : Af F) = algebraMap F (Af F) (m : F) := (map_natCast _ m).symm
  have hu : IsUnit ((m : ℕ) : Af F) := by
    rw [hcast]
    exact (isUnit_iff_ne_zero.2 hmF).map _
  have e1 : ((m : ℕ) : Af F) * (a - algebraMap F (Af F) ((β : F) / m)) = (m : Af F) * y := by
    rw [mul_sub, hβ, hcast, ← map_mul, mul_div_cancel₀ _ hmF,
      IsScalarTower.algebraMap_apply (𝓞 F) F (Af F)]
    ring
  rw [hu.mul_left_cancel e1]
  exact hy
end Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW
