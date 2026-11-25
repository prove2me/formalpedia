-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLDA.smulR_def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:42:46.821086+00:00
-- url     : https://prove2.me/submissions/f68c1841-6be0-43f3-8c4f-de05eb5a3d50

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
variable {K K₁ : Type*} [Field K] [Field K₁] [Algebra K K₁]
attribute [local instance] modT
attribute [local instance] modR
variable {U : Type*} [AddCommGroup U] [Module K U]
variable {R : Type*} [CommRing R] [Algebra R K] [Module R U] [IsScalarTower R K U]
namespace Formalism.L2.Pj.QAt.TieLDA
theorem _root_.solution (r : R) (l : K₁ ⊗[K] U) : r • l = algebraMap R K r • l := rfl
end Formalism.L2.Pj.QAt.TieLDA
