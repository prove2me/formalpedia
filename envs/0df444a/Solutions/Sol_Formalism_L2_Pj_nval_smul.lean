-- Prove2me | solution 1 for Formalism.L2.Pj.nval_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:58.355667+00:00
-- url     : https://prove2.me/submissions/a43ac9fd-5a1e-4781-8a0f-91b89a663fcf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Theorems.Thm_Formalism_L2_Pj_nval_of_ne
import Theorems.Thm_Formalism_L2_Pj_nval_mul

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
theorem _root_.solution {ι : K →+* K'} {e : ℕ} (ho : OverLa la V ι e) {a : K} (ha : a ≠ 0) (x : K') :
    nval V e (ι a * x) = (((vLa la a : ℤ) : ℝ) : EReal) + nval V e x := by
  rw [nval_mul, nval_of_ne ((map_ne_zero ι).2 ha), ho.2 a]
  congr 1
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  congr 1; push_cast; field_simp
end Formalism.L2.Pj
