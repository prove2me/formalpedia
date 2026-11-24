-- Prove2me | solution 1 for Formalism.L2.DIV.isBasisAt_gLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:24:25.81667+00:00
-- url     : https://prove2.me/submissions/be2fbddb-1c01-48e0-bf10-a0fdbca5b9af

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_colLat_mul
import Theorems.Thm_Formalism_L2_DIV_localization_gLat
import Theorems.Thm_Formalism_L2_DIV_gLat_injective

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
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
namespace Formalism.L2.DIV
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (g B : GL (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) :
    IsBasisAt w (gLat g M) (g * B) ↔ IsBasisAt w M B := by
  unfold IsBasisAt
  rw [colLat_mul, localization_gLat, localization_gLat]
  exact (gLat_injective g).eq_iff
end Formalism.L2.DIV
