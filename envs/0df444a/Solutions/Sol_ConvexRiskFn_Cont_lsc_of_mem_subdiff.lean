-- Prove2me | solution 1 for ConvexRiskFn.Cont.lsc_of_mem_subdiff
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T03:58:22.065181+00:00
-- url     : https://prove2.me/submissions/df360468-8926-4389-9652-ae9ffc9ade71

import Definitions.Def_ConvexRiskFn_Cont_Setting
set_option autoImplicit false
open ConvexRiskFn.Cont Filter Topology

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : E → EReal) (Xbar : E) (l : E →L[ℝ] ℝ) (hl : l ∈ subdiff ρ Xbar) :
    LowerSemicontinuousAt ρ Xbar := by
  let g : E → EReal := fun X => ρ Xbar+((l (X-Xbar):ℝ):EReal)
  have hg : Continuous g := by
    by_cases ht : ρ Xbar=⊤
    · have he : g=fun _ => (⊤:EReal) := by
        funext X
        change ρ Xbar+((l (X-Xbar):ℝ):EReal)=⊤
        rw [ht,EReal.top_add_coe]
      rw [he]; exact continuous_const
    · by_cases hb : ρ Xbar=⊥
      · have he : g=fun _ => (⊥:EReal) := by
          funext X
          change ρ Xbar+((l (X-Xbar):ℝ):EReal)=⊥
          rw [hb]
          rfl
        rw [he]; exact continuous_const
      · have hc : ρ Xbar=(((ρ Xbar).toReal:ℝ):EReal) := (EReal.coe_toReal ht hb).symm
        have he : g=fun X => (((ρ Xbar).toReal+l (X-Xbar):ℝ):EReal) := by
          funext X
          change ρ Xbar+((l (X-Xbar):ℝ):EReal)=_
          rw [hc,← EReal.coe_add]
          simp only [EReal.toReal_coe]
        rw [he]
        exact continuous_coe_real_ereal.comp
          (continuous_const.add (l.continuous.comp (continuous_id.sub continuous_const)))
  have hzero : g Xbar=ρ Xbar := by simp [g]
  rw [lowerSemicontinuousAt_iff]
  intro b hb
  have he := (lowerSemicontinuousAt_iff.mp (hg.lowerSemicontinuous Xbar)) b
    (show b < g Xbar by rwa [hzero])
  filter_upwards [he] with X hX
  exact hX.trans_le (hl X)


#print axioms solution

open ConvexRiskFn.Cont Filter Topology
namespace ConvexRiskFn.Cont

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : E → EReal) (Xbar : E) (l : E →L[ℝ] ℝ) (hl : l ∈ subdiff ρ Xbar) :
    LowerSemicontinuousAt ρ Xbar := by
  exact solution ρ Xbar l hl

end ConvexRiskFn.Cont

#print axioms solution
