-- Prove2me | solution 1 for Formalism.HermitianLattices.ExpSeriesBivariate.integralInverse_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:07.960302+00:00
-- url     : https://prove2.me/submissions/70d2652f-3ec0-4e48-86a2-47b61ce2678f

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_LegendreCoefficient
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_IntegralInverse
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_inverse_integral_vector
import Theorems.Thm_Formalism_FG_solve_exists_vector
import Theorems.Thm_Formalism_FG_subst_injective_vector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.HermitianLattices.ExpSeriesBivariate
open Finset
private theorem g3cw2_lin_integral {K : Type} [NormedField K] [IsUltrametricDist K] {σ τ : Type}
    [Fintype σ] (a : σ → K) (ha : ∀ k, ‖a k‖ ≤ 1) (g : σ → MvPowerSeries τ K)
    (hg : ∀ k, Formalism.G.IntegralMv (g k)) :
    Formalism.G.IntegralMv (∑ k, MvPowerSeries.C (a k) * g k) := by
  intro d
  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [MvPowerSeries.coeff_C_mul, norm_mul]
  exact mul_le_one₀ (ha k) (norm_nonneg _) (hg k d)
private theorem g3cw2_subst_lin {K : Type} [Field K] {σ ρ τ : Type} [Fintype σ]
    (a : σ → K) (g : σ → MvPowerSeries ρ K) (h : ρ → MvPowerSeries τ K)
    (hh : MvPowerSeries.HasSubst h) :
    MvPowerSeries.subst h (∑ k, MvPowerSeries.C (a k) * g k) =
      ∑ k, MvPowerSeries.C (a k) * MvPowerSeries.subst h (g k) := by
  rw [← MvPowerSeries.coe_substAlgHom (R := K) hh, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_C]
private theorem g3cw2_inv_lin {K : Type} [Field K] {σ τ : Type} [Fintype σ] [DecidableEq σ]
    (J J' : Matrix σ σ K) (hJ : J * J' = 1) (a : σ → MvPowerSeries τ K) (i : σ) :
    ∑ j, MvPowerSeries.C (J i j) * ∑ k, MvPowerSeries.C (J' j k) * a k = a i := by
  calc ∑ j, MvPowerSeries.C (J i j) * ∑ k, MvPowerSeries.C (J' j k) * a k
      = ∑ j, ∑ k, MvPowerSeries.C (J i j * J' j k) * a k := by
        simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
    _ = ∑ k, ∑ j, MvPowerSeries.C (J i j * J' j k) * a k := Finset.sum_comm
    _ = ∑ k, MvPowerSeries.C ((J * J') i k) * a k := by
        simp_rw [← Finset.sum_mul, ← map_sum, Matrix.mul_apply]
    _ = a i := by
        rw [hJ]
        simp [Matrix.one_apply]
end Formalism.HermitianLattices.ExpSeriesBivariate
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ExpSeriesBivariate
open Finset
namespace Formalism.HermitianLattices.ExpSeriesBivariate
theorem _root_.solution : IntegralInverse := by
  intro K _ _ σ _ _ T J' hT0 hTI hJ'I hLJ
  set L : Matrix σ σ K := Matrix.of fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (T i) with hL
  have hJL : J' * L = 1 := (Matrix.mul_eq_one_comm_of_card_eq σ σ K rfl).mp hLJ
  have hTs : MvPowerSeries.HasSubst T := MvPowerSeries.hasSubst_of_constantCoeff_zero hT0

  let f : σ → MvPowerSeries σ K := fun j => ∑ i, MvPowerSeries.C (J' j i) * T i
  have hf0 : ∀ j, MvPowerSeries.constantCoeff (f j) = 0 := by
    intro j
    simp [f, map_sum, hT0]
  have hfI : ∀ j, Formalism.G.IntegralMv (f j) := fun j => g3cw2_lin_integral _ (fun i => hJ'I j i) _ hTI
  have hfId : Formalism.FG.IsIdMod2 f := by
    refine ⟨hf0, fun j m => ?_⟩
    have h1 : MvPowerSeries.coeff (Finsupp.single m 1) (f j) = (J' * L) j m := by
      simp only [f, map_sum, MvPowerSeries.coeff_C_mul, Matrix.mul_apply, hL, Matrix.of_apply]
    rw [h1, hJL, Matrix.one_apply]
    simp [eq_comm]
  have hTf : ∀ i, T i = ∑ j, MvPowerSeries.C (L i j) * f j := fun i => (g3cw2_inv_lin L J' hLJ T i).symm
  have hXI : ∀ k : σ, Formalism.G.IntegralMv (MvPowerSeries.X k : MvPowerSeries σ K) := by
    intro k d
    rw [MvPowerSeries.coeff_X]
    split_ifs <;> simp
  let G : σ → MvPowerSeries σ K := fun j => ∑ k, MvPowerSeries.C (J' j k) * MvPowerSeries.X k
  have hG0 : ∀ j, MvPowerSeries.constantCoeff (G j) = 0 := by
    intro j
    simp [G, map_sum]
  obtain ⟨X', hX'0, hX'⟩ := Formalism.FG.solve_exists_vector K σ σ f G hfId hG0
  have hX's : MvPowerSeries.HasSubst X' := MvPowerSeries.hasSubst_of_constantCoeff_zero hX'0
  have hX'I : ∀ i, Formalism.G.IntegralMv (X' i) := by
    refine Formalism.FG.inverse_integral_vector K σ σ (fun D => ∀ j, Formalism.G.IntegralMv (D j)) f hfId ?_ ?_ ?_ X' hX'0 ?_
    · intro a b ha hb j d
      rw [Pi.sub_apply, map_sub]
      rw [sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le (ha j d) (by rw [norm_neg]; exact hb j d))
    · intro P hP0 hPI j
      exact Formalism.FG.IntegralSubstitution.integralSubstV (f j) P (hfI j) hP0 hPI
    · intro D hD N _ _ j d _
      exact hD j d
    · intro j
      show Formalism.G.IntegralMv (MvPowerSeries.subst X' (f j))
      rw [hX' j]
      exact g3cw2_lin_integral _ (fun k => hJ'I j k) _ hXI
  refine ⟨X', hX'0, hX'I, fun i => ?_, fun i => ?_⟩
  · rw [hTf i, g3cw2_subst_lin _ f X' hX's]
    simp_rw [hX']
    exact g3cw2_inv_lin L J' hLJ (fun k => MvPowerSeries.X k) i
  ·
    have key := Formalism.FG.subst_injective_vector K σ σ f (fun i => MvPowerSeries.subst T (X' i))
      (fun i => MvPowerSeries.X i) hfId
      (fun i => MvPowerSeries.constantCoeff_subst_eq_zero hTs hT0 (hX'0 i))
      (fun i => MvPowerSeries.constantCoeff_X i) (fun j => ?_)
    · exact congrFun key i
    · rw [← MvPowerSeries.subst_comp_subst_apply hX's hTs, hX' j]
      show MvPowerSeries.subst T (G j) = MvPowerSeries.subst MvPowerSeries.X (f j)
      rw [MvPowerSeries.subst_self, g3cw2_subst_lin _ _ T hTs]
      simp_rw [MvPowerSeries.subst_X hTs]
      rfl
end Formalism.HermitianLattices.ExpSeriesBivariate
