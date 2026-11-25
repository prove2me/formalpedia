-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.MC.pointMX_of_partner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:38:24.793894+00:00
-- url     : https://prove2.me/submissions/0e30577f-3a68-4702-a310-457f66e59419

import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_TheoremMXB
import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_PartnerMeanProofs_GammaZeroIntegral
import Theorems.Thm_Formalism_GM_TM_polZ_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.MC
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO Formalism.InvariantFactorPaths.OddLevelGainBounds.TB MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.MC
theorem _root_.solution (hBad : BadCrit) (hP : PartnerMX) : PointMX := by
  intro p _ N r _ _ LL T Xb E κ lgv e1 n ρ hp2 hr hρ hT hE hS hdeg hlg hκ hκ' hPP hW nb f U V dg fw hf hUV hfw
  obtain ⟨L₁, hL₁, hsat, hprim, hrank⟩ :=
    hP p N r LL T Xb E κ lgv e1 n ρ hp2 hr hρ hT hE hS hdeg hlg hκ hκ' hPP hW nb f U V dg fw hf hUV hfw
  have hfin : Module.Finite ℤ_[p] (YZ p (r := r) (LL.setTies T n) T.J T.thr) := by
    haveI : IsNoetherian ℤ_[p] (PolZ p r (LL.setTies T n)) :=
      isNoetherian_of_fg_of_noetherian _ (polZ_fg (LL.setTies T n))
    haveI : IsNoetherian ℤ_[p] (YZ p (r := r) (LL.setTies T n) T.J T.thr) :=
      isNoetherian_of_le (fun x hx => by unfold YZ at hx; exact hx.2)
    infer_instance
  have hb : bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
      (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + κ) + κ⌋ ≤
      Module.finrank ℤ_[p] (YZ p (r := r) (LL.setTies T n) T.J T.thr) - Module.finrank ℤ_[p] L₁ :=
    hBad p (MvPolynomial (Fin N × Fin r) ℚ_[p])
      (fockBil (LL.setTies T n) (T.phis p (LL.setTies T n))) (YZ p (r := r) (LL.setTies T n) T.J T.thr) L₁
      ⌊(T.t : ℝ) * (E + κ) + κ⌋ hfin hL₁ hsat hprim
  exact le_trans (Nat.cast_le.mpr hb) hrank
end Formalism.InvariantFactorPaths.MC
