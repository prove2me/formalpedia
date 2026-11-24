-- Prove2me | solution 1 for Formalism.L2.Th1.F.thetaLine_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:26:15.466415+00:00
-- url     : https://prove2.me/submissions/0cc416cb-5d18-493f-b17d-e53a862e2568

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_le_sub_of_add_le
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_semiChar_mul_self
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_eq_of_eventuallyEq_punctured
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_eventually_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open ThreeTermRelation
namespace Formalism.L2.Th1.F
theorem _root_.solution (h1 : EllipticOnePole) (hq : SgStarQuasi) (hb : SgStarBasic) : ThetaLine := by
  intro L F hF hfe
  obtain ⟨hd, -, hzero, hder, -⟩ := hb L
  have hmer : ∀ z, MeromorphicAt (fun z => F z / sgStar L z) z := fun z =>
    (hF.analyticAt z).meromorphicAt.div (hd.analyticAt z).meromorphicAt
  have hper : IsPeriodic L (fun z => F z / sgStar L z) := by
    intro ω hω z
    have e1 := hfe ω hω z
    have e2 := hq L ω z hω
    have e3 := semiChar_mul_self L ω
    have hχ : (semiChar L ω)⁻¹ = semiChar L ω := inv_eq_of_mul_eq_one_left e3
    unfold opU at e1
    have hE : Complex.exp (-(Real.pi : ℂ) * herm L z ω - (Real.pi : ℂ) * herm L ω ω / 2)
        = (Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2))⁻¹ := by
      rw [← Complex.exp_neg]; congr 1; ring
    rw [hE] at e1
    show F (z + ω) / sgStar L (z + ω) = F z / sgStar L z
    rw [e2, ← e1, div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv, hχ]
    ring
  have han : ∀ z, z ∉ L.lattice → AnalyticAt ℂ (fun z => F z / sgStar L z) z := fun z hz =>
    (hF.analyticAt z).div (hd.analyticAt z) (fun h => hz ((hzero z).1 h))
  have hord0 : meromorphicOrderAt (sgStar L) 0 = 1 := by
    rw [(hd.analyticAt 0).meromorphicOrderAt_eq,
      (hd.analyticAt 0).analyticOrderAt_eq_one_of_zero_deriv_ne_zero ((hzero 0).2 (zero_mem _))
        (by rw [hder]; exact one_ne_zero)]
    rfl
  obtain ⟨c, hc⟩ := h1 L (fun z => F z / sgStar L z) 0 hmer hper
    (fun z hz => (han z (by simpa using hz)).meromorphicOrderAt_nonneg) (by
      have hF0 := (hF.analyticAt 0).meromorphicOrderAt_nonneg
      rw [fun_meromorphicOrderAt_div (hF.analyticAt 0).meromorphicAt (hd.analyticAt 0).meromorphicAt,
        hord0]
      have := le_sub_of_add_le (o := meromorphicOrderAt F 0) (m := 1) (k := -1) (by simpa using hF0)
      simpa using this)
  have hoff : ∀ z, z ∉ L.lattice → F z = c * sgStar L z := by
    intro z hz
    have := hc z (han z hz).continuousAt
    have hne : sgStar L z ≠ 0 := fun h => hz ((hzero z).1 h)
    field_simp at this
    rw [this, mul_comm]
  refine ⟨c, fun z => ?_⟩
  refine eq_of_eventuallyEq_punctured (f := F) (g := fun z => c * sgStar L z)
    hF.continuous.continuousAt (continuous_const.mul hd.continuous).continuousAt ?_
  filter_upwards [eventually_notMem L z] with x hx using hoff x hx
end Formalism.L2.Th1.F
