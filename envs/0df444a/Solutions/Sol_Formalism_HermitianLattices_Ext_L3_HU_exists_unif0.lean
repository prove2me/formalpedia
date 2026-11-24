-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.exists_unif0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:53.122258+00:00
-- url     : https://prove2.me/submissions/2909c8a1-11ef-475c-90f8-f66a7f4bc0e6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ π₀ ∈ 𝔭, π₀ ∉ 𝔭 ^ 2 ∧ ∃ s₀ : 𝓞 F, s₀ ∉ 𝔭 ∧ Ideal.span {s₀} * 𝔭 ≤ Ideal.span {π₀} := by
  have hne : 𝔭 ≠ ⊥ := fun h0 =>
    RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr (h0 ▸ h𝔭))
  obtain ⟨π₀, hπ1, hπ2⟩ : ∃ x ∈ 𝔭 ^ 1, x ∉ 𝔭 ^ (1 + 1) := by
    have hlt : 𝔭 ^ (1 + 1) < 𝔭 ^ 1 := Ideal.pow_succ_lt_pow hne 1
    obtain ⟨x, hx1, hx2⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx1, hx2⟩
  rw [pow_one] at hπ1
  have hπ2' : π₀ ∉ 𝔭 ^ 2 := hπ2
  obtain ⟨J, hJ⟩ : 𝔭 ∣ Ideal.span {π₀} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hπ1)
  have hJ𝔭 : ¬ J ≤ 𝔭 := by
    intro hle
    apply hπ2'
    have h3 : Ideal.span {π₀} ≤ 𝔭 ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right hle
    exact h3 (Ideal.subset_span rfl)
  obtain ⟨s₀, hsJ, hs𝔭⟩ := SetLike.not_le_iff_exists.mp hJ𝔭
  refine ⟨π₀, hπ1, hπ2', s₀, hs𝔭, ?_⟩
  rw [hJ, mul_comm 𝔭 J]
  exact Ideal.mul_mono_left ((Ideal.span_singleton_le_iff_mem _).mpr hsJ)
end Formalism.HermitianLattices.Ext.L3.HU
