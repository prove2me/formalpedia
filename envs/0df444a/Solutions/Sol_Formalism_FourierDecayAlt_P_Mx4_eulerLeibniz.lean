-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.eulerLeibniz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:44:28.507435+00:00
-- url     : https://prove2.me/submissions/59c4c0cb-c5c7-49dd-a941-80d41d9b41f5

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution : EulerLeibniz := by
  intro r v f g
  ext γ
  have hf : (euler v f).support ⊆ f.support := by
    intro γ h
    simp only [euler, LinearMap.coe_mk, AddHom.coe_mk, HahnSeries.mem_support, ne_eq, mul_eq_zero, not_or] at h
    exact h.2
  have hg : (euler v g).support ⊆ g.support := by
    intro γ h
    simp only [euler, LinearMap.coe_mk, AddHom.coe_mk, HahnSeries.mem_support, ne_eq, mul_eq_zero, not_or] at h
    exact h.2
  rw [HahnSeries.coeff_add, HahnSeries.coeff_mul_left' f.isPWO_support hf,
    HahnSeries.coeff_mul_right' g.isPWO_support hg, ← Finset.sum_add_distrib]
  show ((ofLex γ v : ℤ) : ℂ) * (f * g).coeff γ = _
  rw [HahnSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨a, b⟩ h
  have hab : a + b = γ := (Finset.mem_addAntidiagonal.1 h).2.2
  subst hab
  show _ = (((ofLex a v : ℤ) : ℂ) * f.coeff a) * g.coeff b + f.coeff a * (((ofLex b v : ℤ) : ℂ) * g.coeff b)
  have : ((ofLex (a + b) v : ℤ) : ℂ) = ((ofLex a v : ℤ) : ℂ) + ((ofLex b v : ℤ) : ℂ) := by
    have h2 : ofLex (a + b) v = ofLex a v + ofLex b v := rfl
    rw [h2]; push_cast; ring
  rw [this]; ring
end Formalism.FourierDecayAlt.P.Mx4
