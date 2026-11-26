-- Prove2me | solution 1 for Eden.singularValueFunction_integer_evolution_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:53:59.805381+00:00
-- url     : https://prove2.me/submissions/820494f3-1f1a-439c-804d-37f77999d4ac

import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_IntegerGrowthBounds
import Theorems.Thm_Eden_singularValues_evolution_bounds
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_singularValueFunction_integer_eq_fin_prod
import Theorems.Thm_Eden_singularValueFunction_zero
import Theorems.Thm_Eden_singularValues_evolution_pos
import Theorems.Thm_Eden_spectralProduct_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.singularValueFunction_zero
attribute [local simp] Eden.spectralProduct_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5)
    {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor) :
    Real.exp ((k : ℝ) * (-c * t)) ≤
        singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k ∧
      singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k ≤
        Real.exp ((k : ℝ) * (3 * t)) := by
  rw [singularValueFunction_integer_eq_fin_prod _ hk]
  constructor
  · calc
      _ = ∏ _i : Fin k, Real.exp (-c * t) := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul]
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
        (fun i _ => (singularValues_evolution_bounds hc ht hp (Fin.castLE hk i)).1)
  · calc
      _ ≤ ∏ _i : Fin k, Real.exp (3 * t) := Finset.prod_le_prod
        (fun i _ => (singularValues_evolution_pos c ht p (Fin.castLE hk i)).le)
        (fun i _ => (singularValues_evolution_bounds hc ht hp (Fin.castLE hk i)).2)
      _ = _ := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul]
end Eden
