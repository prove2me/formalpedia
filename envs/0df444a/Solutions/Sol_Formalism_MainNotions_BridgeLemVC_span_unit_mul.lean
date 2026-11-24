-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVC.span_unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:38:58.668838+00:00
-- url     : https://prove2.me/submissions/e357f083-9e18-44d2-9fa4-bd3a983b0499

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVR
import Definitions.Def_Formalism_FlagUnipotentLattices_ArithmeticIdentityEntries
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVC
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemVC
theorem _root_.solution (w : (𝓞 K)ˣ) (N : Submodule (𝓞 K) K) :
    Submodule.span (𝓞 K) {algebraMap (𝓞 K) K (w : 𝓞 K)} * N = N := by
  ext y
  rw [Submodule.mem_span_singleton_mul]
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [← Algebra.smul_def]
    exact N.smul_mem _ hn
  · intro hy
    refine ⟨((w⁻¹ : (𝓞 K)ˣ) : 𝓞 K) • y, N.smul_mem _ hy, ?_⟩
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
end Formalism.MainNotions.BridgeLemVC
