-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.exists_fillO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:54.51912+00:00
-- url     : https://prove2.me/submissions/307dada0-8de0-47dd-99a4-ee4b5929e0aa

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_pow_le_span_mul_sup
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} {c k : ℕ}
    (hd : d ∉ 𝔭 ^ (c + 1)) (hck : c ≤ k) {s : 𝓞 K} (hs : s ∈ extP K 𝔭 ^ k) :
    ∃ r ∈ extP K 𝔭 ^ (k - c), s - ι d * r ∈ extP K 𝔭 ^ (k + 1) := by
  have h := pow_le_span_mul_sup h𝔭.isPrime (ne_bot h𝔭) hd hck
  have h2 := Ideal.map_mono (f := ι) h
  simp only [Ideal.map_sup, Ideal.map_mul, Ideal.map_span, Set.image_singleton,
    Ideal.map_pow] at h2
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (h2 hs)
  obtain ⟨r, hr, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
  refine ⟨r, hr, ?_⟩
  rw [← hyz, add_sub_cancel_left]
  exact hz
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
