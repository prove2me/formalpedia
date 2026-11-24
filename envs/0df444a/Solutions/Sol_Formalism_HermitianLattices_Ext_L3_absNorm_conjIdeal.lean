-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.absNorm_conjIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:09.388109+00:00
-- url     : https://prove2.me/submissions/fff5f555-3ea8-403d-8874-d9244eda5b79

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSubMemOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_absNorm_eq_card
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjIdeal_eq_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (P : Ideal (𝓞 K)) :
    Ideal.absNorm (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) = Ideal.absNorm P := by
  rw [absNorm_eq_card, absNorm_eq_card]
  let e : 𝓞 K ≃+* 𝓞 K :=
    { conjO K with
      invFun := conjO K
      left_inv := fun x => conjO_conjO x
      right_inv := fun x => conjO_conjO x }
  have h : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.map (e : 𝓞 K →+* 𝓞 K) := by
    rw [conjIdeal_eq_map]
    rfl
  exact (Nat.card_congr (Ideal.quotientEquiv P _ e h).toEquiv).symm
end Formalism.HermitianLattices.Ext.L3
