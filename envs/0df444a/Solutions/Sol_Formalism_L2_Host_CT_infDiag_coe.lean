-- Prove2me | solution 1 for Formalism.L2.Host.CT.infDiag_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:12:31.072004+00:00
-- url     : https://prove2.me/submissions/deea3394-058a-483e-8e8b-c8ef599155eb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open Formalism Formalism.L2 Formalism.L2.Host Formalism.L2.Host.CT
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀
variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]
namespace Formalism.L2.Host.CT
theorem _root_.solution (k : Eˣ) :
    ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) (k : E), 1) := by
  classical
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  apply Prod.ext
  · funext u
    have h := map_prod ((Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) u).comp
      (RingHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)) : AdeleRing (𝓞 E) E →+* u.Completion)
      (fun i => ((((infIdele E i).comp (atInf i)) k : Ideles E) : AdeleRing (𝓞 E) E)) Finset.univ
    refine h.trans ?_
    rw [Finset.prod_eq_single u]
    · show Pi.mulSingle u _ u = _
      rw [Pi.mulSingle_eq_same]
      rfl
    · intro w _ hw
      show Pi.mulSingle w _ u = 1
      exact Pi.mulSingle_eq_of_ne (Ne.symm hw) _
    · intro h
      exact absurd (Finset.mem_univ u) h
  · have h := map_prod ((RingHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)) :
      AdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 E) E)
      (fun i => ((((infIdele E i).comp (atInf i)) k : Ideles E) : AdeleRing (𝓞 E) E)) Finset.univ
    refine h.trans ?_
    exact Finset.prod_eq_one fun w _ => rfl
end Formalism.L2.Host.CT
