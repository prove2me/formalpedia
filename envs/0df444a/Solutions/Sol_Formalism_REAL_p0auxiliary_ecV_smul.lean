-- Prove2me | solution 1 for Formalism.REAL.p0auxiliary_ecV_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:01:21.370671+00:00
-- url     : https://prove2.me/submissions/11b576d0-c037-4998-b819-45391ea8e6cc

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_LieOperatorConjHolds
import Theorems.Thm_Formalism_REAL_p0auxiliary_ecV_add
import Theorems.Thm_Formalism_REAL_p0auxiliary_ecV_real
import Theorems.Thm_Formalism_REAL_p0auxiliary_ecV_I

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable (hl : RdLinV) {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : Matrix (Fin n) (Fin n) ℂ → E} {g : Matrix (Fin n) (Fin n) ℂ}
include hl
namespace Formalism.REAL
theorem _root_.solution (hf : SmoothOnGV ε f) (hg : inUJ ε g) (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    EcV ε (c • Z) f g = c • EcV ε Z f g := by
  have hc : c • Z = (c.re : ℂ) • Z + (c.im : ℂ) • (Complex.I • Z) := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  rw [hc, p0auxiliary_ecV_add hl hf hg, p0auxiliary_ecV_real hl hf hg, p0auxiliary_ecV_real hl hf hg,
    p0auxiliary_ecV_I hl, smul_smul, ← add_smul, Complex.re_add_im]
end Formalism.REAL
