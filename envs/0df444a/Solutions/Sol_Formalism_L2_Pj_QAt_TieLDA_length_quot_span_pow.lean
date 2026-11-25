-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLDA.length_quot_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:41:37.157044+00:00
-- url     : https://prove2.me/submissions/01aabcac-a96a-474a-9b7a-c514b4f8b2a7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.TieLDA
open TensorProduct Module
namespace Formalism.L2.Pj.QAt.TieLDA
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {p : R} (hp : Irreducible p) (e : ℕ) : Module.length R (R ⧸ R ∙ p ^ e) = e := by
  have hm : IsLocalRing.maximalIdeal R = Ideal.span {p} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer p).1 hp
  have h := IsDiscreteValuationRing.length_quotient_pow_maximalIdeal R e
  rw [hm, Ideal.span_singleton_pow] at h
  exact h
end Formalism.L2.Pj.QAt.TieLDA
