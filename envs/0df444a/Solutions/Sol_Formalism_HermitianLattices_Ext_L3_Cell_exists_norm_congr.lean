-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.exists_norm_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:48:33.882927+00:00
-- url     : https://prove2.me/submissions/becf7b26-f0f3-470e-9336-51c6ef8605ab

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOfNormRepCountNeZero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_of_normRepCount_ne_zero
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_one_lt_absNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_maximal_over
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localDensity
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)}
namespace Formalism.HermitianLattices.Ext.L3.Cell
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F}
    (hc : c ∉ 𝔭) : ∃ α : 𝓞 K, ∃ ν : 𝓞 F, conjO K α * α = ι ν ∧ ν - c ∈ 𝔭 := by
  obtain ⟨P, hP, hPp⟩ := exists_maximal_over hK hF h𝔭
  have hcP : ι c ∉ P := fun h => hc (hPp ▸ Ideal.mem_comap.2 h)
  have hN := IdealNormInequalities.one_lt_absNorm hP
  have key : ∃ α : 𝓞 K, conjO K α * α - ι c ∈ P := by
    obtain ⟨h1, h2⟩ := localDensity K hK P hP 1 1 le_rfl le_rfl (ι c) (conjO_map hF c) hcP
    by_cases hc' : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
    · have h3 := h1 hc'
      have hs : 0 < Real.sqrt (Ideal.absNorm P : ℝ) := Real.sqrt_pos.2 (by linarith)
      have hpos : (0 : ℝ) < (normRepCount K (P ^ 1) 1 (ι c) : ℝ) := by
        rw [h3]
        refine mul_pos (pow_pos hs _) ?_
        have : (0 : ℝ) < Real.sqrt (Ideal.absNorm P : ℝ) ^ (-((1 : ℕ) : ℤ)) := zpow_pos hs _
        linarith
      obtain ⟨α, hα⟩ := exists_of_normRepCount_ne_zero (by exact_mod_cast hpos.ne')
      exact ⟨α, by simpa using hα⟩
    · have h3 := h2 hc'
      have hpos : (0 : ℝ) < (normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ 1) 1 (ι c) : ℝ) := by
        rw [h3]
        refine mul_pos (pow_pos (by linarith) _) ?_
        have : (Ideal.absNorm P : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := by
          rw [Nat.cast_one, zpow_neg_one]
          exact inv_lt_one_of_one_lt₀ hN
        linarith
      obtain ⟨α, hα⟩ := exists_of_normRepCount_ne_zero (by exact_mod_cast hpos.ne')
      rw [pow_one] at hα
      exact ⟨α, Ideal.mul_le_left hα⟩
  obtain ⟨α, hα⟩ := key
  obtain ⟨ν, hν⟩ := (conjO_eq_iff_mem_range hF (conjO K α * α)).1 (by
    rw [map_mul, conjO_conjO, mul_comm])
  refine ⟨α, ν, hν.symm, ?_⟩
  rw [← hPp, Ideal.mem_comap, map_sub, hν]
  exact hα
end Formalism.HermitianLattices.Ext.L3.Cell
