-- Prove2me | solution 1 for Formalism.L2.DIV.map_restr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:55.128368+00:00
-- url     : https://prove2.me/submissions/c7e4099a-8a3e-48b2-bd91-f23be2a9a5b0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_P2M_Formalism_L2_DIV_map_conjTranspose__e871e98cff26

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {n d : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K)
    (hE : ∀ i a, σ (star (E i a)) = starRingEnd ℂ (σ (E i a))) :
    (Eᴴ * H * E).map σ = restrMetC (E.map σ) (H.map σ) := by
  rw [Matrix.map_mul, Matrix.map_mul, map_conjTranspose' σ E hE, restrMetC]
end Formalism.L2.DIV
