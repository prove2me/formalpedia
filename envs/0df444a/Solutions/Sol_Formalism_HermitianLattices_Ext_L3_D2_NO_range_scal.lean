-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.NO.range_scal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:11:42.378812+00:00
-- url     : https://prove2.me/submissions/b09f8dad-adc8-4c0d-baff-63d0c5ce6ace

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK_iff_unif


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
open Formalism.HermitianLattices.Ext.L3.D2.NO
namespace Formalism.HermitianLattices.Ext.L3.D2.NO
theorem _root_.solution {κ : Type} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭)
    (hπ' : π ∉ 𝔭 ^ 2) (k : ℕ) :
    (scal κ 𝔭 (algebraMap F K (π : F) ^ k)).range = matL 𝔭 k (fun _ _ => 1) (fun _ _ => 1) := by
  ext M
  constructor
  · rintro ⟨v, rfl⟩ i j
    exact ⟨_, (mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨_, (v (i, j)).2, rfl⟩, rfl⟩
  · intro hM
    have h1 : ∀ p : κ × κ, ∃ b ∈ pK K 𝔭 0, M p.1 p.2 = algebraMap F K (π : F) ^ k * b := by
      intro p
      obtain ⟨w, hw, e⟩ := hM p.1 p.2
      rw [one_mul, one_mul] at e
      rw [e]
      exact (mem_pK_iff_unif h𝔭 hπ hπ').1 hw
    choose b hb e using h1
    refine ⟨fun p => ⟨b p, hb p⟩, ?_⟩
    ext i j
    exact (e (i, j)).symm
end Formalism.HermitianLattices.Ext.L3.D2.NO
