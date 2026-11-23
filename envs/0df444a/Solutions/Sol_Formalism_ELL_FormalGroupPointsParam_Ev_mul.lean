-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsParam.Ev.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:14.129974+00:00
-- url     : https://prove2.me/submissions/814511f1-9dff-4194-83a5-0d5bce164e0d

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.FormalGroupPointsParam
open Formalism.G
variable {K : Type u} [NormedField K]
variable [CompleteSpace K]
namespace Formalism.ELL.FormalGroupPointsParam
namespace Ev
theorem _root_.solution {f g : PowerSeries K} {t a b : K} (hf : Ev f t a) (hg : Ev g t b) :
    Ev (f * g) t (a * b) := by
  have key : ∀ n, coeff n (f * g) * t ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (coeff kl.1 f * t ^ kl.1) * (coeff kl.2 g * t ^ kl.2) := by
    intro n
    rw [coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hkl, pow_add]; ring
  have e1 : (fun n => ‖coeff n (f * g) * t ^ n‖) = fun n =>
      ‖∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (coeff kl.1 f * t ^ kl.1) * (coeff kl.2 g * t ^ kl.2)‖ :=
    funext fun n => by rw [key n]
  have e2 : (fun n => coeff n (f * g) * t ^ n) = fun n =>
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (coeff kl.1 f * t ^ kl.1) * (coeff kl.2 g * t ^ kl.2) :=
    funext key
  refine ⟨?_, ?_⟩
  · show Summable (fun n => ‖coeff n (f * g) * t ^ n‖)
    rw [e1]
    exact summable_norm_sum_mul_antidiagonal_of_summable_norm (f := fun n => coeff n f * t ^ n)
      (g := fun n => coeff n g * t ^ n) hf.1 hg.1
  · show ∑' n, coeff n (f * g) * t ^ n = a * b
    rw [e2, ← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (f := fun n => coeff n f * t ^ n)
      (g := fun n => coeff n g * t ^ n) hf.1 hg.1]
    exact congrArg₂ (· * ·) hf.2 hg.2
end Ev
end Formalism.ELL.FormalGroupPointsParam
