-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinF.newton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:00:11.975278+00:00
-- url     : https://prove2.me/submissions/5a15b9ea-d460-412e-adc5-9bd575862c0c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeVdLeOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySeventh
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsExactLift
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_algebraMap_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_algebraMap_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_traceDeterminantCongruences_exists_trace_one
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinF
open idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.PinF
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {N : ℕ} (hN : 1 ≤ N) {y : V}
    (hy : y ∈ L) {a : 𝓞 F} (ha : h y y = algebraMap (𝓞 K) K (ι a)) (ha1 : a - 1 ∈ 𝔭 ^ N) :
    ∃ y' ∈ L, ∃ a' : 𝓞 F, h y' y' = algebraMap (𝓞 K) K (ι a') ∧ a' - 1 ∈ 𝔭 ^ (N + 1) ∧
      y' - y ∈ (extP K 𝔭 ^ N • L : Submodule (𝓞 K) V) := by
  obtain ⟨c, hc⟩ := traceDeterminantCongruences.exists_trace_one hK hF h𝔭 1
  have hc' : c + conjO K c - 1 ∈ extP K 𝔭 ^ 1 := hc
  rw [pow_one] at hc'
  have hEm : ι (a - 1) ∈ extP K 𝔭 ^ N := localizedQuotients.ι_mem_pow ha1
  have hEc : conjO K (ι (a - 1)) = ι (a - 1) := idealPowerSpanBounds.conjO_map hF (a - 1)
  obtain ⟨ν, hν⟩ : ∃ ν : 𝓞 F, ι ν = conjO K (1 - ι (a - 1) * c) * (1 - ι (a - 1) * c) := by
    have : conjO K (conjO K (1 - ι (a - 1) * c) * (1 - ι (a - 1) * c)) =
        conjO K (1 - ι (a - 1) * c) * (1 - ι (a - 1) * c) := by
      rw [map_mul, WA.conjO_conjO, mul_comm]
    exact (conjO_eq_iff_mem_range hF _).1 this
  have ha' : ι a = 1 + ι (a - 1) := by rw [map_sub, map_one]; ring
  refine ⟨(1 - ι (a - 1) * c) • y, L.smul_mem _ hy, ν * a, ?_, ?_, ?_⟩
  · rw [← algebraMap_smul K (1 - ι (a - 1) * c) y]
    simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, starRingEnd_apply]
    rw [ha, map_mul, hν, map_mul, map_mul, WA.algebraMap_conjO]
    ring
  · rw [← idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 (N + 1) (ν * a - 1)]
    have key : ι (ν * a - 1) = ι (a - 1) * (-(c + conjO K c - 1)) +
        ι (a - 1) * ι (a - 1) * (conjO K c * c - (c + conjO K c) + ι (a - 1) * conjO K c * c) := by
      rw [map_sub (algebraMap (𝓞 F) (𝓞 K)) (ν * a) 1, map_mul, hν, ha', map_one, map_sub, map_one,
        map_mul, hEc]
      ring
    rw [key]
    refine Ideal.add_mem _ ?_ ?_
    · rw [pow_succ]
      exact Ideal.mul_mem_mul hEm ((Ideal.neg_mem_iff _).2 hc')
    · refine Ideal.mul_mem_right _ _ ?_
      refine Ideal.pow_le_pow_right (by omega : N + 1 ≤ N + N) ?_
      rw [pow_add]
      exact Ideal.mul_mem_mul hEm hEm
  · have : (1 - ι (a - 1) * c) • y - y = (-(ι (a - 1) * c)) • y := by
      rw [sub_smul, one_smul, neg_smul]; abel
    rw [this]
    exact Submodule.smul_mem_smul ((Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ hEm)) hy
end Formalism.HermitianLattices.Ext.L3.PinF
