-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.nO_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:30:51.072352+00:00
-- url     : https://prove2.me/submissions/395b957c-4d5a-4e3b-ab22-d4b8ad7656a4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nO_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nO_unif_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_NO_exists_mul_eq_unif_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {z : K}
    (hz : z ∈ pK K 𝔭 0) (hz0 : z ≠ 0) : nO 𝔭 z ≠ 0 := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  obtain ⟨m, w, hw, e⟩ := NO.exists_mul_eq_unif_pow h𝔭 hπ hz hz0
  have h1 := nO_mul h𝔭 hz hz0 hw
  rw [e, nO_unif_pow hK hF h𝔭 hπ hπ'] at h1
  intro h0
  rw [h0, zero_mul] at h1
  exact pow_ne_zero _ (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact idealPowerSpanBounds.ne_bot h𝔭) h1
end Formalism.HermitianLattices.Ext.L3.D2
