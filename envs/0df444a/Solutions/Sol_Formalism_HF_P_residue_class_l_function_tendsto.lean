-- Prove2me | solution 1 for Formalism.HF.P.residue_class_l_function_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:11.108799+00:00
-- url     : https://prove2.me/submissions/c49383a8-5421-49e3-b42d-f857eb6868df

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt Complex LSeries
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
variable {q : ℕ} [NeZero q] {a : ZMod q}
namespace Formalism.HF.P
theorem _root_.solution (a : ZMod q) :
    Tendsto (fun x : ℝ ↦ (x - 1) * (LFunctionResidueClassAux a x).re) (𝓝[>] 1) (𝓝 0) := by
  have hc : ContinuousWithinAt (fun x : ℝ ↦ LFunctionResidueClassAux a x) (Set.Ioi 1) 1 := by
    have h1 : ContinuousWithinAt (LFunctionResidueClassAux a) {s : ℂ | 1 ≤ s.re} ((1 : ℝ) : ℂ) :=
      continuousOn_LFunctionResidueClassAux a _ (by simp)
    exact h1.comp Complex.continuous_ofReal.continuousWithinAt
      (fun x hx => by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; exact le_of_lt hx)
  have hre : Tendsto (fun x : ℝ ↦ (LFunctionResidueClassAux a x).re) (𝓝[>] 1)
      (𝓝 (LFunctionResidueClassAux a ((1 : ℝ) : ℂ)).re) :=
    (Complex.continuous_re.tendsto _).comp hc.tendsto
  have hlin : Tendsto (fun x : ℝ ↦ x - 1) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun x : ℝ ↦ x - 1) (𝓝 1) (𝓝 (1 - 1)) := (continuous_id.sub continuous_const).tendsto 1
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  simpa using hlin.mul hre
end Formalism.HF.P
