-- Prove2me | solution 1 for CompanionTheory.Split.normaliser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:05:01.559575+00:00
-- url     : https://prove2.me/submissions/83dbe331-6fb1-4e29-b058-f9eae1dca499

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
import Theorems.Thm_CompanionTheory_Split_mem_KL
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_CartanDecomp
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut TensorProduct Formalism.UG Formalism.L2
noncomputable section
open CompanionTheory CompanionTheory.Split
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => maximalRealSubfield L
variable (s : SplitPlace L)
namespace CompanionTheory.Split
theorem _root_.solution {ϖ : s.v.adicCompletion L⁺} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (t : GL (Fin n) (s.v.adicCompletion L⁺)) (ht : ∀ k ∈ KL s n, t * k * t⁻¹ ∈ KL s n) :
    ∃ u ∈ KL s n, ∀ h, t * h * t⁻¹ = u * h * u⁻¹ := by
  have h0 : ϖ ≠ 0 := fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  obtain ⟨a, -, k₁, h₁, k₂, h₂, e⟩ := Final.CartanDecomp L⁺ s.v n ϖ
    (show Valued.v ϖ ≤ 1 by rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num) hϖ t
  obtain ⟨d, rfl⟩ : ∃ d, t = k₁ * d * k₂ := ⟨k₁⁻¹ * t * k₂⁻¹, by group⟩
  have hd : (d : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) = diagPow L⁺ s.v ϖ a := by
    rw [Units.val_mul, Units.val_mul] at e
    exact (Units.mul_right_inj k₁).1 ((Units.mul_left_inj k₂).1 e)
  have hle : ∀ i j, a j ≤ a i := fun i j => by
    rcases eq_or_ne i j with rfl | hij
    · exact le_rfl
    let E : GL (Fin n) (s.v.adicCompletion L⁺) := ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
      by rw [Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hij, neg_add_cancel, Matrix.transvection_zero]⟩
    have hE : ∀ c : s.v.adicCompletion L⁺, Valued.v c ≤ 1 → ∀ p q, Valued.v (Matrix.transvection i j c p q) ≤ 1 :=
      fun c hc p q => by
        rw [Matrix.transvection, Matrix.add_apply]
        refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
        · rw [Matrix.one_apply]; split_ifs <;> simp
        · rw [Matrix.single_apply]; split_ifs <;> simp [hc]
    have hEK : E ∈ KL s n := (mem_KL s).2 ⟨hE 1 (by simp), hE (-1) (by simp)⟩
    have hM : d * E * d⁻¹ ∈ KL s n := by
      have := (KL s n).mul_mem ((KL s n).mul_mem ((KL s n).inv_mem h₁)
        (ht _ ((KL s n).mul_mem ((KL s n).mul_mem ((KL s n).inv_mem h₂) hEK) h₂))) h₁
      rwa [show k₁⁻¹ * (k₁ * d * k₂ * (k₂⁻¹ * E * k₂) * (k₁ * d * k₂)⁻¹) * k₁ = d * E * d⁻¹ by group] at this
    have h3 := ((mem_KL s).1 hM).1 i j
    have h4' : ((d * E * d⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) *
        ((d : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) =
        ((d : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) *
          ((E : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) := by
      rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
    have h4 := congrArg (fun M : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺) => M i j) h4'
    simp only [hd, diagPow, Matrix.mul_diagonal, Matrix.diagonal_mul] at h4
    have h5 : ((E : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j = 1 := by
      simp [E, Matrix.transvection, hij]
    have h6 := mul_le_mul_left h3 (Valued.v (ϖ ^ a j))
    rw [← map_mul, h4, h5, mul_one, one_mul, map_zpow₀, map_zpow₀, hϖ, ← WithZero.exp_zsmul, ← WithZero.exp_zsmul,
      WithZero.exp_le_exp] at h6
    simpa using h6
  have hc : ∀ h, d * h = h * d := fun h => Units.ext (Matrix.ext fun i j => by
    rw [Units.val_mul, Units.val_mul, hd, diagPow, Matrix.mul_diagonal, Matrix.diagonal_mul,
      le_antisymm (hle j i) (hle i j), mul_comm])
  refine ⟨k₁ * k₂, (KL s n).mul_mem h₁ h₂, fun h => ?_⟩
  rw [show k₁ * d * k₂ * h * (k₁ * d * k₂)⁻¹ = k₁ * (d * (k₂ * h * k₂⁻¹)) * d⁻¹ * k₁⁻¹ by group, hc]
  group
end CompanionTheory.Split
