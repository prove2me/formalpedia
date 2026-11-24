-- Prove2me | solution 1 for Formalism.L2.DIV.transLat_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:05.654883+00:00
-- url     : https://prove2.me/submissions/09edac57-7ea9-4be5-b0b0-a0a726d4691d

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_localization_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    {T T' : Submodule (𝓞 K) (Pol K ι n)} (h : T ≤ T') (M : ι → Submodule (𝓞 K) (Fin n → K)) :
    transLat lam T M ≤ transLat lam T' M :=
  iInf_mono fun w => iInf_mono fun _ => iInf_mono fun _ => Submodule.comap_mono (localization_mono w.asIdeal h)
end Formalism.L2.DIV
