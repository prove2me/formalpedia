-- Prove2me | solution 1 for Formalism.HN.PlaceLattice.exists_denom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:11.773667+00:00
-- url     : https://prove2.me/submissions/18767990-1d26-4db3-96c0-bb3e23a8af7b

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceLattice
variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HN.PlaceLattice
theorem _root_.solution {ι' : Type} [Fintype ι'] (e : ι' → V) (N : Submodule (𝓞 K) V) (hN : N.FG)
    (hsub : ∀ x ∈ N, x ∈ Submodule.span K (Set.range e)) :
    ∃ y : ℤ, y ≠ 0 ∧ N ≤ Submodule.span (𝓞 K) (Set.range fun a => ((y : K)⁻¹) • e a) := by
  classical
  obtain ⟨S, rfl⟩ := hN
  have hc : ∀ x : S, ∃ c : ι' → K, ∑ j, c j • e j = (x : V) := fun x =>
    (Submodule.mem_span_range_iff_exists_fun K).1 (hsub x (Submodule.subset_span x.2))
  choose c hc using hc
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.biUnion fun x : S => Finset.univ.image (c x))
  refine ⟨y, hy0, ?_⟩
  rw [Submodule.span_le]
  intro x hx
  have hyK : (y : K) ≠ 0 := Int.cast_ne_zero.2 hy0
  suffices h : ∑ j, c ⟨x, hx⟩ j • e j ∈ Submodule.span (𝓞 K) (Set.range fun a => ((y : K)⁻¹) • e a) by
    rwa [hc ⟨x, hx⟩] at h
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨r, hr⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).1
    (hy (c ⟨x, hx⟩ j) (Finset.mem_biUnion.2 ⟨⟨x, hx⟩, Finset.mem_univ _,
      Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩))
  have : c ⟨x, hx⟩ j • e j = r • ((y : K)⁻¹ • e j) := by
    rw [← algebraMap_smul K r, hr, smul_smul, zsmul_eq_mul, mul_assoc, mul_comm (c _ _),
      ← mul_assoc, mul_inv_cancel₀ hyK, one_mul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
end Formalism.HN.PlaceLattice
