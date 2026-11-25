-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinD.alphaN_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:27:56.609924+00:00
-- url     : https://prove2.me/submissions/460ddce1-fa19-4f60-8952-bd85363efc7f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscrIdealSmulLeIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocFSpanConsBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsTotPosDefOfSmul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinA_nkCount_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_alphaN_eq_of_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinD
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.PinD
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) (hs' : (algebraMap F K (c : F) • h).IsSymm)
    (hd' : IsTotPosDef (algebraMap F K (c : F) • h)) (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ≠ 0) :
    alphaN (algebraMap F K (c : F) • h) L 𝔭 (c * n) =
      (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 c * alphaN h L 𝔭 n := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have key : ∀ k, 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 + vF 𝔭 c ≤ k →
      (nkCount (algebraMap F K (c : F) • h) L 𝔭 k (c * n) : ℝ) /
          (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) =
        (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 c * alphaN h L 𝔭 n := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + vF 𝔭 c := ⟨k - vF 𝔭 c, by omega⟩
    rw [PinA.nkCount_smul hK hF hs hd hL hLi h𝔭 hc n (k := m + vF 𝔭 c) (by omega), Nat.add_sub_cancel,
      alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn (k := m) (by omega)]
    push_cast
    have h2 : 2 * vF 𝔭 c * finrank K V = vF 𝔭 c * (2 * finrank K V - 1) + vF 𝔭 c := by
      have h3 : 2 * finrank K V = (2 * finrank K V - 1) + 1 := by omega
      calc 2 * vF 𝔭 c * finrank K V = vF 𝔭 c * (2 * finrank K V) := by ring
        _ = vF 𝔭 c * ((2 * finrank K V - 1) + 1) := by rw [← h3]
        _ = _ := by ring
    rw [h2, show (m + vF 𝔭 c) * (2 * finrank K V - 1) =
        m * (2 * finrank K V - 1) + vF 𝔭 c * (2 * finrank K V - 1) by ring, pow_add, pow_add]
    field_simp <;> ring
  exact (tendsto_const_nhds.congr'
    (Filter.eventually_atTop.2 ⟨_, fun k hk => (key k hk).symm⟩)).limUnder_eq
end Formalism.HermitianLattices.Ext.L3.PinD
