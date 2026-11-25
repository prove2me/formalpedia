-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.redCount_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:03:37.685187+00:00
-- url     : https://prove2.me/submissions/6429115f-3ccb-418b-bb8d-6e7666bccc4a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCountPosBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_IsE_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_akCount_eq_mul_basis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_isE_eA
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_sigmaCount_pos_basis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_sigmaCount_succ_basis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_aniso_of_totPosDef
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_exists_gram
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_exists_basis_locF


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
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {j : ℕ} (hj : eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ j) :
    redCount h (locF 𝔭 A₀) 𝔭 (j + 1) = Ideal.absNorm 𝔭 ^ (finrank K V ^ 2) * redCount h (locF 𝔭 A₀) 𝔭 j := by
  obtain ⟨b, hbL, hb⟩ := LocalSpans.exists_basis_locF hA₀ h𝔭
  obtain ⟨H, hH, -⟩ := LocF.exists_gram hA₀i b hbL
  have hd' := LocF.aniso_of_totPosDef hd
  have : Fact (IsFixF K F) := ⟨hF⟩
  rw [← hb] at hj ⊢
  have he := HU.isE_eA hK hF hd' b h𝔭
  generalize eA h (locF 𝔭 (Submodule.span (𝓞 K) (Set.range b))) 𝔭 = e at hj he ⊢
  have h1 := HU.akCount_eq_mul_basis hK hs hd' b hH h𝔭 he (by omega : e ≤ j + 1) (by omega)
  have h2 := HU.akCount_eq_mul_basis hK hs hd' b hH h𝔭 (he.mono (Nat.le_succ e)) (by omega : e + 1 ≤ j)
    (by omega)
  have h3 := HU.sigmaCount_succ_basis hK hs hd' b hH h𝔭 he (le_refl e)
  have h4 := HU.sigmaCount_pos_basis h b hH h𝔭 e
  rw [Fintype.card_fin] at h3
  rw [show j + 1 + e = j + (e + 1) by omega, h2, h3] at h1
  apply Nat.eq_of_mul_eq_mul_right h4
  rw [← h1]
  ring
end Formalism.HermitianLattices.Ext.L3
