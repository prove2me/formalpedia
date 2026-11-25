-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.akCount_eq_redCount_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:29:31.219028+00:00
-- url     : https://prove2.me/submissions/7af252c4-95bb-41f2-a77b-9b00c43ed934

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCountPosBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_akCount_eq_mul_basis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_isE_eA
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
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 2 * eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ k) :
    akCount h (locF 𝔭 A₀) 𝔭 k =
      redCount h (locF 𝔭 A₀) 𝔭 (k - eA h (locF 𝔭 A₀) 𝔭) * sigmaCount h (locF 𝔭 A₀) 𝔭 (eA h (locF 𝔭 A₀) 𝔭) := by
  obtain ⟨b, hbL, hb⟩ := LocalSpans.exists_basis_locF hA₀ h𝔭
  obtain ⟨H, hH, -⟩ := LocF.exists_gram hA₀i b hbL
  have hd' := LocF.aniso_of_totPosDef hd
  have : Fact (IsFixF K F) := ⟨hF⟩
  rw [← hb] at hk ⊢
  have he := HU.isE_eA hK hF hd' b h𝔭
  generalize eA h (locF 𝔭 (Submodule.span (𝓞 K) (Set.range b))) 𝔭 = e at hk he ⊢
  obtain ⟨j, rfl⟩ : ∃ j, k = j + e := ⟨k - e, by omega⟩
  rw [Nat.add_sub_cancel]
  exact HU.akCount_eq_mul_basis hK hs hd' b hH h𝔭 he (by omega) (by omega)
end Formalism.HermitianLattices.Ext.L3
