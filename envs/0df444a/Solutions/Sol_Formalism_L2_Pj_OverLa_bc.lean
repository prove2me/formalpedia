-- Prove2me | solution 1 for Formalism.L2.Pj.OverLa.bc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:41.061802+00:00
-- url     : https://prove2.me/submissions/e700e786-3239-4558-9730-f79fa60a5c8a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open scoped WithZero
open Formalism Formalism.L2 Formalism.L2.Pj
attribute [instance] CDVR.cr CDVR.dom CDVR.dvr CDVR.cpl CDVR.ch0
variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K]
variable {la : HeightOneSpectrum R} {V : Type} {K' : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Field K'] [Algebra V K'] [IsFractionRing V K']
namespace Formalism.L2.Pj
namespace OverLa
theorem _root_.solution {ι : K →+* K'} {e : ℕ} (ho : OverLa la V ι e) {V' K'' : Type} [CommRing V']
    [IsDomain V'] [IsDiscreteValuationRing V'] [Field K''] [Algebra V' K''] [IsFractionRing V' K'']
    (i : K' →+* K'') {r : ℕ} (hr : 0 < r) (hi : ∀ x, vV V' (i x) = (r : ℤ) * vV V x) :
    OverLa la V' (i.comp ι) (r * e) :=
  ⟨Nat.mul_pos hr ho.1, fun a => by rw [RingHom.comp_apply, hi, ho.2 a]; push_cast; ring⟩
end OverLa
end Formalism.L2.Pj
