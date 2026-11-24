-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.metric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:03:17.998794+00:00
-- url     : https://prove2.me/submissions/5e58bfe7-c6db-42a6-ae20-ee75d7dc6949

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_fc_smul
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_maj_sum_left
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_maj_sum_right
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_maj_smul_left
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_maj_smul_right
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_normAt_eq_sqrt
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_normAt_eq_norm
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_opNormAt_le_of_points
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_charFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField Matrix
noncomputable section
namespace Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
namespace BlockMetrics
section Forms
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)
end Forms
end BlockMetrics
open BlockMetrics
private theorem normAt_smul_indefinite_real {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (a : K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (a • x) = ‖v.embedding a‖ * Formalism.HermitianLatticesTheory.normAt b X v x := by
  rw [normAt_eq_norm, normAt_eq_norm, fc_smul, WithLp.toLp_smul, norm_smul]
private theorem normAt_add_le {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x y : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (x + y) ≤ Formalism.HermitianLatticesTheory.normAt b X v x + Formalism.HermitianLatticesTheory.normAt b X v y := by
  rw [normAt_eq_norm, normAt_eq_norm, normAt_eq_norm, Formalism.HermitianLatticesTheory.fcoord_add, WithLp.toLp_add]
  exact norm_add_le _ _
private theorem normAt_finset_sum_le {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) {α : Type} (s : Finset α)
    (f : α → V) :
    Formalism.HermitianLatticesTheory.normAt b X v (∑ a ∈ s, f a) ≤ ∑ a ∈ s, Formalism.HermitianLatticesTheory.normAt b X v (f a) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using (normAt_smul_indefinite_real b X v (0 : K) (0 : V)).le
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (normAt_add_le b X v _ _).trans (add_le_add le_rfl ih)
end Formalism.IndefR.LatticeTransfer
end
end

set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open BlockMetrics
namespace Formalism.IndefR.LatticeTransfer
theorem _root_.solution : Metric := by
  intro K _ _ _ _ G _ _ V _ _ _ _ ι _ _ b X ρ hX hU
  have hinv : ∀ (g : G) (y : V), ρ g (ρ g⁻¹ y) = y := by
    intro g y
    show (ρ g * ρ g⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hρ : ∀ (v : InfinitePlace K) (g : G) (x y : V),
      Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) y = Formalism.HermitianLatticesTheory.majAt b X v x (ρ g⁻¹ y) := by
    intro v g x y
    calc Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) y
        = Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) (ρ g (ρ g⁻¹ y)) := by rw [hinv]
      _ = Formalism.HermitianLatticesTheory.majAt b X v x (ρ g⁻¹ y) := hU v g x _
  refine ⟨fun T _ _ _ τ v x y => ?_, fun H χ g v => ?_⟩
  · have hc := fun g => (charFacts K G T τ g).2 v.embedding
    have hc1 : starRingEnd ℂ (v.embedding (charOf τ 1 / (Fintype.card G : K))) =
        v.embedding (charOf τ 1 / (Fintype.card G : K)) := by
      have h1 := (hc 1).1
      rw [inv_one] at h1
      simp only [map_div₀, map_natCast]
      rw [starRingEnd_apply, ← h1]
    simp only [Formalism.IndefR.TransferLatticeStatement.eS, LinearMap.smul_apply, LinearMap.sum_apply]
    rw [maj_smul_left, maj_smul_right, maj_sum_left, maj_sum_right, hc1]
    congr 1
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
    have hg := (hc g⁻¹).1
    rw [inv_inv] at hg
    simp only [Equiv.inv_apply, inv_inv]
    rw [hρ, ← hg]
  · have hρn : ∀ (k : G) (z : V), Formalism.HermitianLatticesTheory.normAt b X v (ρ k z) = Formalism.HermitianLatticesTheory.normAt b X v z := by
      intro k z; rw [normAt_eq_sqrt, hU, ← normAt_eq_sqrt]
    have hχ : ∀ h : H, ‖v.embedding (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)‖ = 1 := by
      intro h
      rw [InfinitePlace.norm_embedding_eq]
      have ht : χ h⁻¹ ∈ NumberField.Units.torsion K := χ.isOfFinOrder (isOfFinOrder_of_finite h⁻¹)
      exact (NumberField.Units.mem_torsion K).1 ht v
    refine opNormAt_le_of_points b X hX _ v 1 zero_le_one fun f => ?_
    rw [one_mul, LinearMap.comp_apply]
    simp only [Formalism.IndefR.TransferLatticeStatement.epP, LinearMap.smul_apply, LinearMap.sum_apply]
    rw [normAt_smul_indefinite_real]
    refine (mul_le_mul_of_nonneg_left (normAt_finset_sum_le b X v _ _) (norm_nonneg _)).trans ?_
    simp only [normAt_smul_indefinite_real, hχ, hρn, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      map_inv₀, map_natCast, norm_inv, Complex.norm_natCast]
    rw [Fintype.card_eq_nat_card, ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.card_pos (α := H)).ne'), one_mul]
end Formalism.IndefR.LatticeTransfer
