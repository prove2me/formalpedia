-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.eq_zero_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:47:59.000846+00:00
-- url     : https://prove2.me/submissions/b6adaa61-dda1-4ed3-889e-48a261d333ba

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsEquivOfMemEndL
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_notMem_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_pow_zero_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_mem_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_algebraMap_comp
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff
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
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {v : V} (hv : ∀ j : ℕ, v ∈ extP K 𝔭 ^ j • locF 𝔭 A₀) :
    v = 0 := by
  have := h𝔭.isPrime
  have h0 : v ∈ locF 𝔭 A₀ := by simpa [pow_zero_smul] using hv 0
  obtain ⟨t, ht, htv⟩ := (LocalSpans.mem_locF 𝔭 A₀ v).1 h0
  have h1 : ∀ j : ℕ, ι t • v ∈ extP K 𝔭 ^ j • A₀ := fun j =>
    localizedQuotients.mem_smul_of_mem_smul_locF h𝔭 A₀ j htv (Submodule.smul_mem _ _ (hv j))
  have : Module.Finite (𝓞 K) ↥A₀ := Module.Finite.iff_fg.2 hA₀.fg
  have h2 : (⟨ι t • v, htv⟩ : ↥A₀) ∈ (⨅ i : ℕ, extP K 𝔭 ^ i • ⊤ : Submodule (𝓞 K) ↥A₀) := by
    rw [Submodule.mem_iInf]
    intro j
    rw [Submodule.mem_smul_top_iff]
    exact h1 j
  obtain ⟨r, hr⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff (extP K 𝔭) _).1 h2
  have hr' : (r : 𝓞 K) • (ι t • v) = ι t • v := congrArg Subtype.val hr
  have hr1 : (r : 𝓞 K) ≠ 1 := by
    intro e
    have h3 : (1 : 𝓞 K) ∈ extP K 𝔭 ^ 1 := by rw [pow_one, ← e]; exact r.2
    have h4 : (1 : 𝓞 F) ∈ 𝔭 ^ 1 := (idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 1 1).1 (by simpa using h3)
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h4))
  have h5 : (algebraMap (𝓞 K) K ((r : 𝓞 K) - 1) * algebraMap F K (t : F)) • v = 0 := by
    rw [mul_smul, ← MeanB.algebraMap_comp, algebraMap_smul, algebraMap_smul, sub_smul, hr', one_smul,
      sub_self]
  rcases smul_eq_zero.1 h5 with h6 | h6
  · rcases mul_eq_zero.1 h6 with h7 | h7
    · exact absurd (sub_eq_zero.1 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).1 h7)) hr1
    · exact absurd h7 (notMem_ne_zero ht)
  · exact h6
end Formalism.HermitianLattices.Ext.L3.D2
