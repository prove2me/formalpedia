-- Prove2me | solution 1 for Formalism.L2.SG.Pf.WuDec.integrable_and_integral_pi_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:17.479282+00:00
-- url     : https://prove2.me/submissions/5d2154b7-9704-4b23-b0e1-5d7ce01d4be4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_TensInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.WuDec
namespace Formalism.L2.SG.Pf.WuDec
theorem _root_.solution :
  ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ v, MeasurableSpace (X v)] (μ : ∀ v, Measure (X v))
    [∀ v, SigmaFinite (μ v)] (V : ι → Type) [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
    [∀ v, FiniteDimensional ℂ (V v)] (Vπ : Type) [NormedAddCommGroup Vπ] [InnerProductSpace ℂ Vπ]
    [FiniteDimensional ℂ Vπ] (tens : (∀ v, V v) → Vπ),
    (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) → Submodule.span ℂ (Set.range tens) = ⊤ →
    ∀ G : ∀ v, X v → V v, (∀ v, Integrable (G v) (μ v)) →
      Integrable (fun y : ∀ v, X v => tens (fun v => G v (y v))) (Measure.pi μ) ∧
        ∫ y, tens (fun v => G v (y v)) ∂(Measure.pi μ) = tens (fun v => ∫ t, G v t ∂(μ v)) := by
  intro ι _ X _ μ _ V _ _ _ Vπ _ _ _ tens hi hspan G hG
  have hcoord : ∀ w : Vπ, Integrable (fun y : ∀ v, X v => ⟪w, tens fun v => G v (y v)⟫_ℂ)
      (Measure.pi μ) := by
    intro w
    have hw : w ∈ Submodule.span ℂ (Set.range tens) := by rw [hspan]; exact Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      simp_rw [hi]
      exact Integrable.fintype_prod_dep (fun v => (hG v).const_inner (z v))
    | zero =>
      simp only [inner_zero_left]
      exact integrable_zero _ _ _
    | add x y _ _ hx hy =>
      simp only [inner_add_left]
      exact hx.add hy
    | smul a x _ hx =>
      simp only [inner_smul_left]
      exact hx.const_mul _
  have hFint : Integrable (fun y : ∀ v, X v => tens fun v => G v (y v)) (Measure.pi μ) := by
    have e : (fun y : ∀ v, X v => tens fun v => G v (y v)) = fun y =>
        ∑ i, ⟪stdOrthonormalBasis ℂ Vπ i, tens fun v => G v (y v)⟫_ℂ • stdOrthonormalBasis ℂ Vπ i :=
      funext fun y => ((stdOrthonormalBasis ℂ Vπ).sum_repr' _).symm
    rw [e]
    exact integrable_finset_sum _ fun i _ => (hcoord _).smul_const _
  refine ⟨hFint, ?_⟩
  refine ext_inner_left ℂ fun w => ?_
  have hw : w ∈ Submodule.span ℂ (Set.range tens) := by rw [hspan]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    rw [← integral_inner hFint]
    simp_rw [hi]
    refine (integral_fintype_prod_eq_prod (fun v t => ⟪z v, G v t⟫_ℂ)).trans ?_
    exact Finset.prod_congr rfl fun v _ => integral_inner (hG v) (z v)
  | zero => simp only [inner_zero_left]
  | add x y _ _ hx hy => rw [inner_add_left, inner_add_left, hx, hy]
  | smul a x _ hx => rw [inner_smul_left, inner_smul_left, hx]
end Formalism.L2.SG.Pf.WuDec
