-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.relIndex_sesqL_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:26:21.720932+00:00
-- url     : https://prove2.me/submissions/752434ec-b322-44bb-8cde-59959072043f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqMapMulKer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_relIndex_eq_map_mul_ker
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_exists_skew_unit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_map_symF_sesqL
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_map_smul_hermL
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (A₀ B₀ : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k k' : ℕ}
    (hle : sesqL (locF 𝔭 B₀) 𝔭 k' ≤ sesqL (locF 𝔭 A₀) 𝔭 k) :
    (sesqL (locF 𝔭 B₀) 𝔭 k').relIndex (sesqL (locF 𝔭 A₀) 𝔭 k) =
      (hermL (locF 𝔭 B₀) 𝔭 k').relIndex (hermL (locF 𝔭 A₀) 𝔭 k) ^ 2 := by
  obtain ⟨δ, hδ, hδ0, hδ1, hδ2⟩ := J.exists_skew_unit hK hF h𝔭
  rw [J.relIndex_eq_map_mul_ker J.symF hle, J.map_symF_sesqL hK hF _ h𝔭, J.map_symF_sesqL hK hF _ h𝔭,
    ← J.map_smul_hermL _ h𝔭 k' hδ hδ0 hδ1 hδ2, ← J.map_smul_hermL _ h𝔭 k hδ hδ0 hδ1 hδ2,
    AddSubgroup.relIndex_map_map_of_injective, sq]
  intro s t hst
  have := congrArg (fun u => δ⁻¹ • u) hst
  simpa [smul_smul, inv_mul_cancel₀ hδ0] using this
end Formalism.HermitianLattices.Ext.L3.D2
