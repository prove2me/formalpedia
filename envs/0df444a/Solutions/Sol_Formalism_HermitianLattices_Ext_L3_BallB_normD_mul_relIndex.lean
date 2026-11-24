-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.normD_mul_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:41.895283+00:00
-- url     : https://prove2.me/submissions/4d966efc-a179-4d7a-a170-3ee13c95cf28

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormSpanSingletonEq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_discrIdeal_span
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_absNorm_span_singleton_eq
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_absNorm_discrIdeal_of_le
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BallB
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (b : Basis (Fin (finrank K V)) K V)
    (hb : ∀ i, b i ∈ L)
    (hidx : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) :
    normD h L * ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) =
      ∏ w : InfinitePlace K, w (gdet h b) := by
  haveI : IsTotallyComplex K := hK.1
  have hint : ∀ i j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = h (b i) (b j) := fun i j =>
    Submodule.mem_one.1 (hLi _ (hb i) _ (hb j))
  choose c hc using hint
  have hg : algebraMap (𝓞 K) K (Matrix.of fun i j => c i j).det = gdet h b := by
    rw [RingHom.map_det]
    unfold gdet
    congr 1
    ext i j
    simp [hc]
  have hle : Submodule.span (𝓞 K) (Set.range b) ≤ L :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i)
  obtain ⟨n, hn⟩ : ∃ n, (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup = n :=
    ⟨_, rfl⟩
  rw [hn] at hidx ⊢
  have hN := absNorm_discrIdeal_of_le hK hLi b n (Submodule.span (𝓞 K) (Set.range b)) hle hn hidx
  rw [discrIdeal_span b hg] at hN
  have hS := absNorm_span_singleton_eq (Matrix.of fun i j => c i j).det
  rw [hg] at hS
  have hprod : (0 : ℝ) ≤ ∏ w : InfinitePlace K, w (gdet h b) :=
    Finset.prod_nonneg (fun w _ => w.1.nonneg _)
  have key : ((n : ℝ) * Real.sqrt (Ideal.absNorm (discrIdeal h L) : ℝ)) ^ 2 =
      (∏ w : InfinitePlace K, w (gdet h b)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← hS, hN]
    push_cast
    ring
  unfold normD
  rw [← Real.sqrt_sq hprod, ← key, Real.sqrt_sq (by positivity)]
  ring
end Formalism.HermitianLattices.Ext.L3.BallB
