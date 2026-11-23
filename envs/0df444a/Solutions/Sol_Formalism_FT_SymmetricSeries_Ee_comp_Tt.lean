-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.Ee_comp_Tt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:34.049514+00:00
-- url     : https://prove2.me/submissions/6ec173e5-3dbd-4143-b5eb-f75b994a787c

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Theorems.Thm_Formalism_FT_SymmetricSeries_esymm_hsymm_rel
import Theorems.Thm_Formalism_FT_SymmetricSeries_aeval_tri

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.FT Formalism.FT.SymmetricSeries
variable (R : Type*) [CommRing R] (n : ℕ)
variable {R n}
variable (R n)
variable {R n}
namespace Formalism.FT.SymmetricSeries
theorem _root_.solution : (Ee R n).comp (Tt R n) = Eh R n := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, Tt, Ee, Eh, MvPolynomial.aeval_X]
  exact aeval_tri (fun i => MvPolynomial.esymm (Fin n) R i) (fun i => MvPolynomial.hsymm (Fin n) R i)
    (MvPolynomial.esymm_zero _ _) (MvPolynomial.hsymm_zero _ _)
    (fun k hk _ => esymm_hsymm_rel k hk) (j + 1) (by have := j.isLt; omega)
end Formalism.FT.SymmetricSeries
