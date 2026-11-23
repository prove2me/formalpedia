-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.exists_norm_eq_rpow_rat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:46.850522+00:00
-- url     : https://prove2.me/submissions/a4242021-6237-4f54-be88-98ef931dc328

import Definitions.Def_Formalism_GaussJetBounds_StatementV
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_TheoremAMatrixEntries
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_l_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (l : ℕ) [hl : Fact l.Prime] (q : ℚ) :
    ∃ c : ℂ_[l], ‖c‖ = ‖(l : ℂ_[l])‖ ^ (q : ℝ) := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq ((l : ℂ_[l]) ^ q.num) q.pos
  refine ⟨c, ?_⟩
  have hπ := norm_l_pos l
  have h1 : ‖c‖ ^ q.den = ‖(l : ℂ_[l])‖ ^ q.num := by
    rw [← norm_pow, hc, norm_zpow]
  have hden : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
  have h2 : (‖(l : ℂ_[l])‖ ^ (q : ℝ)) ^ q.den = ‖(l : ℂ_[l])‖ ^ q.num := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hπ.le, ← Real.rpow_intCast]
    congr 1
    have : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den q).symm
    rw [this]
    field_simp
  exact (pow_left_inj₀ (norm_nonneg c) (Real.rpow_nonneg hπ.le _) q.den_nz).1 (h1.trans h2.symm)
end Formalism.DworkPowerSeriesWeights
