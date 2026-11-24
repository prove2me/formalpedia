-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.integral_spanO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:47:23.08647+00:00
-- url     : https://prove2.me/submissions/eb5714d0-7b7a-46ec-8e86-702db46ff45a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormalise
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdLeOneOfBasis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_form_eq


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)}
namespace Formalism.HermitianLattices.Ext.L3.Cell
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {N : ℕ} (e : Basis (Fin N) K V) (A' : Fin N → 𝓞 F)
    (ho : ∀ i j, i ≠ j → h (e i) (e j) = 0) (hn : ∀ i, h (e i) (e i) = κ (ι (A' i))) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (spanO e) := by
  intro x hx y hy
  have hH : ∀ i j, κ ((Matrix.diagonal fun i => ι (A' i)) i j) = h (e i) (e j) := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq, hn]
    · rw [Matrix.diagonal_apply_ne _ hij, map_zero, ho i j hij]
  have := form_eq h e hH ⟨x, hx⟩ ⟨y, hy⟩
  exact Submodule.mem_one.2 ⟨_, this.symm⟩
end Formalism.HermitianLattices.Ext.L3.Cell
