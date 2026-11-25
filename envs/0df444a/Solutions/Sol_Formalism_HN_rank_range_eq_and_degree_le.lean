-- Prove2me | solution 1 for Formalism.HN.rank_range_eq_and_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:58:23.858801+00:00
-- url     : https://prove2.me/submissions/63268cd0-6604-47b4-9de0-99aff5965a9d

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq
import Theorems.Thm_Formalism_F_covolEqGram
import Theorems.Thm_Formalism_F_covol_pos
import Theorems.Thm_Formalism_F_det_gram_basis_pos
import Theorems.Thm_Formalism_F_gramDetLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Submodule
noncomputable section
namespace Formalism.HN
section SlopeTestRemainingChoices
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
private lemma le_of_forall_nat_mul_le_mul_add {a b K : ℝ}
    (h : ∀ n : ℕ, 0 < n → (n : ℝ) * a ≤ n * b + K) : a ≤ b := by
  by_contra hab
  push_neg at hab
  have hpos : 0 < a - b := sub_pos.mpr hab
  obtain ⟨n, hn⟩ := exists_nat_gt (K / (a - b))
  have h1 := h (n + 1) n.succ_pos
  push_cast at h1
  have h2 : ((n : ℝ) + 1) * (a - b) ≤ K := by linarith
  have h3 : (n : ℝ) + 1 ≤ K / (a - b) := (le_div_iff₀ hpos).mpr h2
  linarith
private lemma norm_sum_sub_round_smul_le_sum_norm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ι : Type*} [Fintype ι] (v : ι → X) (t : ι → ℝ) :
    ‖∑ i, (t i - (round (t i) : ℝ)) • v i‖ ≤ ∑ i, ‖v i‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  have h1 := abs_sub_round (t i)
  have h2 := norm_nonneg (v i)
  have h3 := abs_nonneg (t i - (round (t i) : ℝ))
  nlinarith
private lemma norm_sum_smul_map_le_mul_of_bounded {A : Submodule ℤ E} {B : Submodule ℤ F} (e : A →ₗ[ℤ] B)
    (C : ℝ) (hC : 0 ≤ C) (h : ∀ y, ‖((e y : B) : F)‖ ≤ C * ‖(y : E)‖) {ι : Type*} [Fintype ι]
    (b : ι → A) (c : ι → ℝ) :
    ‖∑ i, c i • ((e (b i) : B) : F)‖ ≤ C * ‖∑ i, c i • ((b i : A) : E)‖ := by
  apply le_of_forall_nat_mul_le_mul_add (K := C * ∑ i, ‖((b i : A) : E)‖ + ∑ i, ‖((e (b i) : B) : F)‖)
  intro n _
  have hnn : (0 : ℝ) ≤ n := n.cast_nonneg

  have hyE : (((∑ i, round ((n : ℝ) * c i) • b i : A)) : E) =
      ∑ i, ((round ((n : ℝ) * c i) : ℤ) : ℝ) • ((b i : A) : E) := by
    simp [Submodule.coe_sum, Int.cast_smul_eq_zsmul]
  have heF : ((e (∑ i, round ((n : ℝ) * c i) • b i) : B) : F) =
      ∑ i, ((round ((n : ℝ) * c i) : ℤ) : ℝ) • ((e (b i) : B) : F) := by
    simp [map_sum, map_zsmul, Submodule.coe_sum, Int.cast_smul_eq_zsmul]
  have dF : (n : ℝ) • ∑ i, c i • ((e (b i) : B) : F) =
      ((e (∑ i, round ((n : ℝ) * c i) • b i) : B) : F) +
        ∑ i, ((n : ℝ) * c i - (round ((n : ℝ) * c i) : ℝ)) • ((e (b i) : B) : F) := by
    rw [heF, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← add_smul]
    congr 1
    ring
  have dE : (((∑ i, round ((n : ℝ) * c i) • b i : A)) : E) =
      (n : ℝ) • ∑ i, c i • ((b i : A) : E) -
        ∑ i, ((n : ℝ) * c i - (round ((n : ℝ) * c i) : ℝ)) • ((b i : A) : E) := by
    rw [hyE, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← sub_smul]
    congr 1
    ring
  have r1 := norm_sum_sub_round_smul_le_sum_norm (fun i => ((e (b i) : B) : F)) (fun i => (n : ℝ) * c i)
  have r2 := norm_sum_sub_round_smul_le_sum_norm (fun i => ((b i : A) : E)) (fun i => (n : ℝ) * c i)
  have k1 : (n : ℝ) * ‖∑ i, c i • ((e (b i) : B) : F)‖ ≤
      ‖((e (∑ i, round ((n : ℝ) * c i) • b i) : B) : F)‖ + ∑ i, ‖((e (b i) : B) : F)‖ := by
    have := norm_smul (n : ℝ) (∑ i, c i • ((e (b i) : B) : F))
    rw [Real.norm_of_nonneg hnn] at this
    rw [← this, dF]
    exact (norm_add_le _ _).trans (add_le_add le_rfl r1)
  have k2 : ‖(((∑ i, round ((n : ℝ) * c i) • b i : A)) : E)‖ ≤
      (n : ℝ) * ‖∑ i, c i • ((b i : A) : E)‖ + ∑ i, ‖((b i : A) : E)‖ := by
    rw [dE]
    refine (norm_sub_le _ _).trans (add_le_add ?_ r2)
    rw [norm_smul, Real.norm_of_nonneg hnn]
  have k3 := h (∑ i, round ((n : ℝ) * c i) • b i)
  nlinarith [mul_le_mul_of_nonneg_left k2 hC]
end SlopeTestRemainingChoices
universe uR uV uW uE uF
end Formalism.HN
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
namespace Formalism.HN
theorem _root_.solution {G : Type*} [AddCommGroup G] (α : G →+ E) (β : G →+ F)
    (hαβ : ∀ g, α g = 0 → β g = 0) (hβα : ∀ g, β g = 0 → α g = 0)
    [DiscreteTopology (LinearMap.range α.toIntLinearMap)]
    [DiscreteTopology (LinearMap.range β.toIntLinearMap)]
    (C : ℝ) (hC : 0 < C) (h : ∀ g, ‖β g‖ ≤ C * ‖α g‖) :
    Formalism.F.rk (LinearMap.range β.toIntLinearMap) = Formalism.F.rk (LinearMap.range α.toIntLinearMap) ∧
    Formalism.F.deg (LinearMap.range α.toIntLinearMap) -
              (Formalism.F.rk (LinearMap.range α.toIntLinearMap) : ℝ) * Real.log C ≤
      Formalism.F.deg (LinearMap.range β.toIntLinearMap) := by
  have hker : LinearMap.ker α.toIntLinearMap = LinearMap.ker β.toIntLinearMap := by
    ext g
    simp only [LinearMap.mem_ker]
    exact ⟨hαβ g, hβα g⟩
  let e : LinearMap.range α.toIntLinearMap ≃ₗ[ℤ] LinearMap.range β.toIntLinearMap :=
    (α.toIntLinearMap.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hker)).trans
      β.toIntLinearMap.quotKerEquivRange
  have he : ∀ g : G, ((e ⟨α g, g, rfl⟩ : LinearMap.range β.toIntLinearMap) : F) = β g := by
    intro g
    simp only [e, LinearEquiv.trans_apply]
    erw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hy : ∀ y, ‖((e.toLinearMap y : LinearMap.range β.toIntLinearMap) : F)‖ ≤
      C * ‖(y : E)‖ := by
    rintro ⟨_, g, rfl⟩
    have h1 := he g
    have h2 := h g
    rw [← h1] at h2
    exact h2
  have hrk : Module.finrank ℤ (LinearMap.range α.toIntLinearMap) =
      Module.finrank ℤ (LinearMap.range β.toIntLinearMap) := e.finrank_eq
  refine ⟨by simp only [Formalism.F.rk]; exact hrk.symm, ?_⟩
  let b := Module.finBasis ℤ (LinearMap.range α.toIntLinearMap)
  have hA := Formalism.F.covolEqGram E (LinearMap.range α.toIntLinearMap) _ b
  have hB := Formalism.F.covolEqGram F (LinearMap.range β.toIntLinearMap) _ (b.map e)
  simp only [Basis.map_apply] at hB
  have hG := Formalism.F.gramDetLe E F _ (fun i => ((b i : LinearMap.range α.toIntLinearMap) : E))
    (fun i => ((e (b i) : LinearMap.range β.toIntLinearMap) : F)) C
    (fun c => norm_sum_smul_map_le_mul_of_bounded e.toLinearMap C hC.le hy b c)
  simp only [Fintype.card_fin] at hG
  have hvpos := Formalism.F.covol_pos (LinearMap.range α.toIntLinearMap)
  have hwpos := Formalism.F.covol_pos (LinearMap.range β.toIntLinearMap)
  have hdet := Formalism.F.det_gram_basis_pos (LinearMap.range α.toIntLinearMap) b
  have hle : Formalism.F.covol (LinearMap.range β.toIntLinearMap) ≤
      C ^ Module.finrank ℤ (LinearMap.range α.toIntLinearMap) *
        Formalism.F.covol (LinearMap.range α.toIntLinearMap) := by
    rw [hA, hB]
    calc _ ≤ Real.sqrt (C ^ (2 * Module.finrank ℤ (LinearMap.range α.toIntLinearMap)) *
          (Matrix.gram ℝ (fun i => ((b i : LinearMap.range α.toIntLinearMap) : E))).det) :=
          Real.sqrt_le_sqrt hG
      _ = _ := by
          rw [Real.sqrt_mul (by positivity), pow_mul', Real.sqrt_sq (by positivity)]
  have hlog := Real.log_le_log hwpos hle
  rw [Real.log_mul (by positivity) hvpos.ne', Real.log_pow] at hlog
  simp only [Formalism.F.deg, Formalism.F.rk]
  linarith
end Formalism.HN
