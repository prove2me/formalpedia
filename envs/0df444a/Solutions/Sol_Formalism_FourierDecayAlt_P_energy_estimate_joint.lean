-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.energy_estimate_joint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:38:18.689027+00:00
-- url     : https://prove2.me/submissions/f061fcc9-1a9c-4c40-8e4c-16c479fcf3e8

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.LE.EstEJoint := by
  intro E W _ D S loc hN hRO hAdm hwt hgram hJ0 hEL
  intro w hw
  obtain ⟨hwW, hcnt⟩ := Finset.mem_filter.mp hw
  have hlim : ∀ v, Filter.Tendsto (fun ε : ℝ => (S v).principalHermitianLattice ε (loc w v)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((S v).size (loc w v) * (S v).jn)) := by
    intro v
    obtain ⟨hadm, hlen⟩ := hAdm w hwW v
    exact hEL v (loc w v) hadm (by rw [hN v]; omega)
  have hprod := tendsto_finset_prod Finset.univ (fun v _ => hlim v)
  have hsize : ∀ v, (S v).size (loc w v) ≠ 0 := by
    intro v
    obtain ⟨⟨hin, -⟩, -⟩ := hAdm w hwW v
    intro h0
    rw [Formalism.FourierDecayAlt.LE.Sys.size, List.prod_eq_zero_iff] at h0
    obtain ⟨x, hx, hx0⟩ := List.mem_map.mp h0
    have hP : (S v).P x.2 = 0 := abs_eq_zero.mp hx0
    obtain ⟨s, -, hs⟩ := Finset.prod_eq_zero_iff.mp hP
    have hxin := hin x hx
    exact hRO v s (by rw [show -(S v).lam s = x.2 by linarith]; exact hxin)
  have hjn : ∀ v, (S v).jn = (S v).jsq := fun v =>
    congrArg (MeasureTheory.integral (S v).B.μ) (funext (hJ0 v))
  have hlim2 := hprod.div_const (D.wt w)
  have hval : (∏ v, (S v).size (loc w v) * (S v).jn) / D.wt w = ∏ v, (S v).jsq := by
    rw [hwt w hwW, Finset.prod_mul_distrib, mul_div_right_comm,
      div_self (Finset.prod_ne_zero_iff.mpr (fun v _ => hsize v)), one_mul]
    exact Finset.prod_congr rfl (fun v _ => hjn v)
  rw [← hval]
  refine hlim2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  show (∏ v, (S v).principalHermitianLattice ε (loc w v)) / D.wt w = (D.gram ε 0 w [] []).re / D.wt w
  rw [hgram ε hε w hwW]
end Formalism.FourierDecayAlt.P
