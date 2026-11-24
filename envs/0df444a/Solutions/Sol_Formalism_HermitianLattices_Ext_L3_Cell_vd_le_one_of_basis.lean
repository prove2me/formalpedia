-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.vd_le_one_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:46:55.671555+00:00
-- url     : https://prove2.me/submissions/51f80003-c747-4a58-bf78-1678bd47a5cb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormalise
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdLeOneOfBasis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff


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
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {N : ℕ} (hN : finrank K V = N)
    (e : Basis (Fin N) K V) (A' : Fin N → 𝓞 F)
    (ho : ∀ i j, i ≠ j → h (e i) (e j) = 0) (hn : ∀ i, h (e i) (e i) = κ (ι (A' i)))
    (hprod : ∏ i, A' i ∉ 𝔭 ^ 2) : vd h (spanO e) 𝔭 ≤ 1 := by
  subst hN
  unfold vd
  refine csSup_le' fun E hE => ?_
  by_contra hlt
  apply hprod
  rw [← mem_pow_iff (K := K)]
  apply Ideal.pow_le_pow_right (by omega : 2 ≤ E)
  apply hE
  refine Ideal.subset_span ⟨e, fun i => Submodule.subset_span ⟨i, rfl⟩, ?_⟩
  have : (Matrix.of fun i j => h (e i) (e j)) = Matrix.diagonal fun i => κ (ι (A' i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq, Matrix.of_apply, hn]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.of_apply, ho i j hij]
  rw [this, Matrix.det_diagonal, map_prod, map_prod]
end Formalism.HermitianLattices.Ext.L3.Cell
