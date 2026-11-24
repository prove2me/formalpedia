-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.DualLatticeEmbeddings.zdual_eq_yv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:20:47.173706+00:00
-- url     : https://prove2.me/submissions/6778c7cc-e9c0-43c6-9bb8-31318c7c530f

import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_SumUliftFinsetFinTwoExpand
import Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_inner_yv
import Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_exists_int_smul_mem
import Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_mem_Mz
import Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_span_Mz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ} [StarRing K] [IsTotallyComplex K]
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
theorem _root_.solution (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hXf : ∀ v, IsUnit (Xf v).det)
    (X : Submodule (𝓞 K) (Fin n → K)) (hX : Submodule.span K (X : Set (Fin n → K)) = ⊤)
    (y : Amb K n) (hy : y ∈ Formalism.HadamardInequality.zdual (Mz Xf X)) :
    ∃ ξ : Fin n → K, y = yv Xf ξ ∧
      ∀ x ∈ X, Algebra.trace ℚ K (∑ i, ξ i * x i) ∈ Set.range (Int.cast : ℤ → ℚ) := by
  classical
  set Rz := Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf with hRz
  let φ : (Fin n → K) →+ ℝ := AddMonoidHom.mk' (fun x => inner ℝ (Rz x) y)
    (fun a b => by simp only [map_add, inner_add_left])
  have hφ : ∀ x, φ x = inner ℝ (Rz x) y := fun x => rfl
  have hint : ∀ x ∈ X, ∃ k : ℤ, φ x = k := fun x hx => hy (Rz x) ((mem_Mz Xf X _).2 ⟨x, hx, rfl⟩)
  have hrat : ∀ v, ∃ q : ℚ, (q : ℝ) = φ v := by
    intro v
    obtain ⟨N, hN0, hNv⟩ := exists_int_smul_mem X hX v
    obtain ⟨k, hk⟩ := hint _ hNv
    rw [map_zsmul, zsmul_eq_mul] at hk
    have hN : (N : ℝ) ≠ 0 := Int.cast_ne_zero.2 hN0
    refine ⟨(k : ℚ) / N, ?_⟩
    push_cast
    rw [← hk]
    field_simp
  choose ψ0 hψ0 using hrat
  let ψa : (Fin n → K) →+ ℚ := AddMonoidHom.mk' ψ0 (fun a b => by
    have h := hψ0 (a + b)
    rw [map_add, ← hψ0 a, ← hψ0 b] at h
    exact_mod_cast h)
  let ψ : (Fin n → K) →ₗ[ℚ] ℚ := ψa.toRatLinearMap
  have hψ : ∀ v, (ψ v : ℝ) = φ v := fun v => hψ0 v
  let B := (Algebra.traceForm ℚ K).toDual (traceForm_nondegenerate ℚ K)
  let ξ : Fin n → K := fun i => B.symm (ψ ∘ₗ LinearMap.single ℚ (fun _ : Fin n => K) i)
  have hξ : ∀ i a, Algebra.trace ℚ K (ξ i * a) = ψ (Pi.single i a) := by
    intro i a
    have h := LinearMap.BilinForm.toDual_def (traceForm_nondegenerate ℚ K) (m := ξ i) (n := a)
    rw [Algebra.traceForm_apply] at h
    rw [← h]
    show (B (B.symm _)) a = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have htr : ∀ x, Algebra.trace ℚ K (∑ i, ξ i * x i) = ψ x := by
    intro x
    rw [map_sum]
    simp_rw [hξ]
    rw [← map_sum, Finset.univ_sum_single]
  refine ⟨ξ, ?_, fun x hx => ?_⟩
  · have horth : ∀ x, inner ℝ (Rz x) (y - yv Xf ξ) = 0 := by
      intro x
      rw [inner_sub_right, inner_yv Xf hXf, htr, hψ, hφ, sub_self]
    have hspan : ∀ z ∈ Submodule.span ℝ (Mz Xf X : Set (Amb K n)), inner ℝ z (y - yv Xf ξ) = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, -, rfl⟩ := (mem_Mz Xf X z).1 hz
        exact horth x
      | zero => simp
      | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
      | smul r a _ ha => rw [real_inner_smul_left, ha, mul_zero]
    have h0 := hspan (y - yv Xf ξ) (by rw [span_Mz Xf hXf X hX]; trivial)
    rw [inner_self_eq_zero, sub_eq_zero] at h0
    exact h0
  · obtain ⟨k, hk⟩ := hint x hx
    refine ⟨k, ?_⟩
    rw [htr]
    have : (ψ x : ℝ) = (k : ℝ) := by rw [hψ, hk]
    exact_mod_cast this.symm
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
