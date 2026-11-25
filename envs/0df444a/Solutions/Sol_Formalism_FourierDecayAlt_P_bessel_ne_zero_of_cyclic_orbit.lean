-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.bessel_ne_zero_of_cyclic_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:09:23.562805+00:00
-- url     : https://prove2.me/submissions/d958596b-ddc9-496e-a0d0-f6f2a62984a5

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_smooth_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_smooth_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_smooth_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_smooth_translate
import Theorems.Thm_PI_UnitaryGroupMassFormula_LowSmooth_lowSmooth_of_kFinSmooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open PI.UpqRep
open TranslationBesselVanishing
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.ThreeDimData.DDNzOfCyc := by
  intro hCyc hKF k r ε lam H _ _ _ σ w0 Wp _ _ z c π hlam hds hlow Bm hB hzero x hx
  obtain ⟨hadd, -, -, C, Ws, hWs, hbd⟩ := hB
  have hw0 : w0 ∈ smoothVecs (k := k) (r := r) σ :=
    PI.UnitaryGroupMassFormula.LowSmooth.lowSmooth_of_kFinSmooth hKF k r ε lam H σ w0 hlam hds hlow
  by_contra hne
  have hpos : 0 < ‖Bm x‖ := norm_pos_iff.mpr hne
  have h2 : 0 < 2 * (|C| + 1) := by positivity
  set δ : ℝ := ‖Bm x‖ / (2 * (|C| + 1)) with hδdef
  have hδ : 0 < δ := div_pos hpos h2
  obtain ⟨N, cc, g, hg, hsum⟩ := hCyc k r ε lam H σ w0 hlam hds hlow x hx Ws hWs δ hδ
  set y : H := ∑ i, cc i • σ (g i) w0 with hy
  have hysm : y ∈ smoothVecs (k := k) (r := r) σ :=
    Finset.sum_induction _ (· ∈ smoothVecs (k := k) (r := r) σ) (fun a b ha hb => smooth_add ha hb)
      smooth_zero (fun i _ => smooth_smul _ (smooth_translate hds hw0 (hg i)))
  have hyDD : y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σ w0 :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g i, hg i, rfl⟩))
  have hxy : x - y ∈ smoothVecs (k := k) (r := r) σ := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ y]
    exact smooth_add hx (smooth_smul _ hysm)
  have hsplit : Bm x = Bm (x - y) + Bm y := by
    rw [← hadd _ hxy _ hysm, sub_add_cancel]
  have hBy : Bm y = 0 := hzero y hyDD
  have hb := hbd (x - y) hxy
  have hS0 : 0 ≤ (Ws.map fun w => ‖dsigW σ w (x - y)‖).sum := by
    apply List.sum_nonneg
    intro a ha
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp ha
    exact norm_nonneg _
  have hlt : ‖Bm x‖ < ‖Bm x‖ :=
    calc ‖Bm x‖ = ‖Bm (x - y)‖ := by rw [hsplit, hBy, add_zero]
      _ ≤ C * (Ws.map fun w => ‖dsigW σ w (x - y)‖).sum := hb
      _ ≤ |C| * (Ws.map fun w => ‖dsigW σ w (x - y)‖).sum :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hS0
      _ ≤ |C| * δ := mul_le_mul_of_nonneg_left hsum.le (abs_nonneg C)
      _ < ‖Bm x‖ := by
          rw [hδdef, ← mul_div_assoc, div_lt_iff₀ h2]
          nlinarith [abs_nonneg C, hpos]
  exact lt_irrefl _ hlt
end Formalism.FourierDecayAlt.P
