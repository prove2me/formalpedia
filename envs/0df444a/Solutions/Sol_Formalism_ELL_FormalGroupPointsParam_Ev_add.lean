-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsParam.Ev.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:34.013801+00:00
-- url     : https://prove2.me/submissions/5a2f5e71-b711-474c-8494-bfc57f7d2c48

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
    Ev (f + g) t (a + b) := by
  refine ⟨?_, ?_⟩
  · refine (hf.1.add hg.1).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    simp only [map_add, add_mul]
    exact norm_add_le _ _
  · unfold evalPS
    simp only [map_add, add_mul]
    rw [hf.1.of_norm.tsum_add hg.1.of_norm]
    exact congrArg₂ (· + ·) hf.2 hg.2
end Ev
end Formalism.ELL.FormalGroupPointsParam
