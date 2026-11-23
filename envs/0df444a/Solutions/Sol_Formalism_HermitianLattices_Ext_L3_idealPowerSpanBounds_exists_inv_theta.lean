-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.exists_inv_theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:48:48.480953+00:00
-- url     : https://prove2.me/submissions/d451b84a-9fc5-4bc8-9d03-3e97e11479de

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {δ : 𝓞 K} (hδ : Ideal.span {δ} ⊔ extP K 𝔭 = ⊤) (N : ℕ) :
    ∃ e : 𝓞 K, δ * e - 1 ∈ extP K 𝔭 ^ N := by
  have h : Ideal.span {δ} ⊔ extP K 𝔭 ^ N = ⊤ := by
    first
    | exact Ideal.sup_pow_eq_top hδ
    | exact Ideal.isCoprime_iff_sup_eq.mp ((Ideal.isCoprime_iff_sup_eq.mpr hδ).pow_right)
  have h1 : (1 : 𝓞 K) ∈ Ideal.span {δ} ⊔ extP K 𝔭 ^ N := by
    rw [h]
    exact Submodule.mem_top
  obtain ⟨y, hy, w, hw, hyw⟩ := Submodule.mem_sup.mp h1
  obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  refine ⟨e, ?_⟩
  have e2 : δ * e - 1 = -w := by
    rw [← hyw]
    ring
  rw [e2]
  exact neg_mem hw
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
