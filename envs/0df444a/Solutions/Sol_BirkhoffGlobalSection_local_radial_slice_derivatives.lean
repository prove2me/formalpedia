-- Prove2me | solution 1 for BirkhoffGlobalSection.local_radial_slice_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:39:28.623198+00:00
-- url     : https://prove2.me/submissions/ae4fb97c-d35d-4ef8-b471-2c4d9670594f

import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
import Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_exterior_derivative
import Theorems.Thm_BirkhoffGlobalSection_radial_rescaling_contact_pullback
import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_characteristic_normalization
import Theorems.Thm_BirkhoffGlobalSection_smooth_radial_gauge_chart
import Theorems.Thm_ConvexAnalysis_radial_derivative_pos_of_inward_negative
import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false




set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (s : E)
    (hc : ContDiffAt ℝ 2 F s) :
    let f : ℝ → ℝ := fun t => F (t • s)
    deriv f 1 = fderiv ℝ F s s ∧
      deriv (deriv f) 1 = fderiv ℝ (fun x => fderiv ℝ F x s) s s := by
  let P : ℝ → E := fun t => t • s
  let f : ℝ → ℝ := F ∘ P
  let G : E → ℝ := fun x => fderiv ℝ F x s
  have hP (t : ℝ) : HasDerivAt P s t := by
    simpa only [P, id_eq, one_smul] using (hasDerivAt_id t).smul_const s
  have hPc : Continuous P := continuous_id.smul continuous_const
  have hP1 : P 1 = s := one_smul ℝ s
  have hf : HasDerivAt f (fderiv ℝ F s s) 1 :=
    (hc.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 1 (hP 1) hP1.symm
  have hGc : ContDiffAt ℝ 1 G s :=
    (hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hg : HasDerivAt (G ∘ P) (fderiv ℝ G s s) 1 :=
    hGc.differentiableAt_one.hasFDerivAt.comp_hasDerivAt_of_eq 1 (hP 1) hP1.symm
  have hPt : Filter.Tendsto P (nhds 1) (nhds s) := by
    simpa only [hP1] using hPc.continuousAt.tendsto (x := 1)
  have heq : deriv f =ᶠ[nhds 1] G ∘ P := by
    filter_upwards [hPt.eventually (hc.eventually (by norm_num))] with t ht
    exact (ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hP t) |>.deriv
  exact ⟨hf.deriv, (hg.congr_of_eventuallyEq heq).deriv⟩
