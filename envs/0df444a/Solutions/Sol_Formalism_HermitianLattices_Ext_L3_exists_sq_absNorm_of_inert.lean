-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.exists_sq_absNorm_of_inert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:08.221013+00:00
-- url     : https://prove2.me/submissions/dc1a9abb-7704-46fb-96d5-eda0fd2afb97

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSubMemOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjIdeal_eq_comap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_sub_conjO_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_absNorm_eq_card
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_exists_sq_card_quot


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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    ∃ q : ℕ, Ideal.absNorm P = q ^ 2 := by
  rw [conjIdeal_eq_comap] at hc
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  rw [absNorm_eq_card]
  exact SplitPrimeIdeals.exists_sq_card_quot conjO_conjO hP hc hθ
end Formalism.HermitianLattices.Ext.L3
