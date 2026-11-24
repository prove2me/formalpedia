-- Prove2me | solution 1 for Formalism.L2.Col.exists_pow_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:02:18.584514+00:00
-- url     : https://prove2.me/submissions/9b931b6c-528d-431e-bab1-ca719cefaec4

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
import Theorems.Thm_Formalism_L2_Col_length_ow_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (w : HeightOneSpectrum (𝓞 K)) (Q : Type) [AddCommGroup Q] [Module (Ow w) Q] [Module (𝓞 K) Q]
  [IsScalarTower (𝓞 K) (Ow w) Q]
namespace Formalism.L2.Col
theorem _root_.solution (hQ : Module.length (Ow w) Q ≠ ⊤) (x : Q) :
    ∃ n : ℕ, ∀ c ∈ w.asIdeal ^ n, c • x = 0 := by
  let f : Ow w →ₗ[Ow w] Q := LinearMap.toSpanSingleton (Ow w) Q x
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro h
    apply hQ
    have := Module.length_le_of_injective f (LinearMap.ker_eq_bot.1 h)
    rw [length_ow_self] at this
    exact top_le_iff.1 this
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Ow w)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := (LinearMap.ker f : Ideal (Ow w))) hker hπ
  refine ⟨n, fun c hc => ?_⟩
  have h1 : algebraMap (𝓞 K) (Ow w) c ∈ LinearMap.ker f := by
    rw [hn, ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]
    exact (algebraMap_mem_maximalIdeal_pow_iff w c n).2 hc
  have h2 : algebraMap (𝓞 K) (Ow w) c • x = 0 := h1
  rwa [algebraMap_smul] at h2
end Formalism.L2.Col
