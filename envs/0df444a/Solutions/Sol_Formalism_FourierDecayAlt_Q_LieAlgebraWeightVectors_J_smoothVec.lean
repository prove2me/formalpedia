-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.J_smoothVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:30:37.693965+00:00
-- url     : https://prove2.me/submissions/ebc3e4a0-3f97-49b5-8ff0-e7bfce890053

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_one_uw
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_exp_uw
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_uw_glev
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_uw_slev
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' (Fin.last r) D) (hπ'1 : π' 1 = 1)
    {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) (v : Wq) : J g v ∈ SmVec k r z π := by
  intro h hh X hX
  have h1' : (1 : Mx k r) ∈ UWset k r z' := sv_one_uw z'
  have he : ∀ t : ℝ, π (h * NormedSpace.exp ((t : ℂ) • X)) (J g v) =
      J (h * NormedSpace.exp ((t : ℂ) • X) * g) v := by
    intro t
    have hm := hJ.2.2.2 g hg _ (WeylGroupFacts.uw_mul hh (sv_exp_uw hX t)) 1 h1'
    rw [Matrix.mul_one] at hm
    rw [hm]
    simp [hπ'1]
  have hfun : (fun t : ℝ => π (h * NormedSpace.exp ((t : ℂ) • X)) (J g v)) =
      fun t : ℝ => J (h * NormedSpace.exp ((t : ℂ) • X) * g) v := funext he
  rw [hfun]
  have hhg : h * g ∈ Glev k r (Fin.last r) ∩ D := by
    refine ⟨sv_uw_glev hh hg.1, ?_⟩
    have := hD.2 g hg h (sv_uw_slev hh _) 1 (sv_uw_slev h1' _)
    simpa using this
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hJ.1 (h * g) hhg
  have hd : DifferentiableAt ℝ F (h * g) :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hc : HasDerivAt (fun t : ℝ => h * NormedSpace.exp ((t : ℂ) • X) * g)
      (mulRightRealCLM g (h * NormedSpace.exp (((0 : ℝ) : ℂ) • X) * X)) 0 :=
    (mulRightRealCLM g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (B5.curve_hasDerivAt h X 0)
  have hc0 : h * g = h * NormedSpace.exp (((0 : ℝ) : ℂ) • X) * g := by
    simp [NormedSpace.exp_zero]
  have hFc : DifferentiableAt ℝ (fun t : ℝ => F (h * NormedSpace.exp ((t : ℂ) • X) * g)) 0 :=
    (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0).differentiableAt
  have hFv : DifferentiableAt ℝ (fun t : ℝ => F (h * NormedSpace.exp ((t : ℂ) • X) * g) v) 0 :=
    ((ContinuousLinearMap.apply ℂ Wp v).restrictScalars ℝ).differentiableAt.comp (0 : ℝ) hFc
  refine hFv.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, h * NormedSpace.exp ((t : ℂ) • X) * g ∈ U :=
    hc.continuousAt.preimage_mem_nhds (by rw [← hc0]; exact hU.mem_nhds hgU)
  filter_upwards [hmem] with t ht
  rw [hFe _ ht (sv_uw_glev (WeylGroupFacts.uw_mul hh (sv_exp_uw hX t)) hg.1)]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
