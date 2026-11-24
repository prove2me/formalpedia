-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.det_conjQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:02:23.880591+00:00
-- url     : https://prove2.me/submissions/fdbd44be-250c-4ff4-9669-29925c33b32b

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_MemHatMapGlob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Comp
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.Comp
theorem _root_.solution (Q : Matrix m n E) (Q' : Matrix n m E) (h1 : Q * Q' = 1) (h2 : Q' * Q = 1) (g : GL n 𝒜) :
    ((conjQ Q Q' h1 h2 g : GL m 𝒜) : Matrix m m 𝒜).det = (g : Matrix n n 𝒜).det :=
  Matrix.det_conj_of_mul_eq_one (map_mul_map Q Q' h1) (map_mul_map Q' Q h2)
end Formalism.L2.GlobalTheoryTheory.Comp
