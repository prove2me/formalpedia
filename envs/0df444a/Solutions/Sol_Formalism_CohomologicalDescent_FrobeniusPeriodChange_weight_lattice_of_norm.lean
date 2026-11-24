-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.weight_lattice_of_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:23:14.114103+00:00
-- url     : https://prove2.me/submissions/b4bc1c0a-9918-431f-b3b4-c4ce58de1995

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_order_descent_holds
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_pi0SubstHom_apply
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_pi0Subst_det_map
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_localization_facts_hold
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_one_add_X_smul_sub_C_dvd
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_constantCoeff_conj_diagonal_rescale
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_charpoly_diagonal_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_diagonal_minors_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_height_descent_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_inc_X_sub_l_eq_q0
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_inc_pow
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_linear_prime_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_roots_descent_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_theta_congruence_padic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : LatWOfN := by
  intro ι l h n _ O L _ _ _ _ I _ ζ em jj N u c U' hl2 hu hζ hζI hem hloc hU hN
  obtain ⟨hP5, hTh, hloc4⟩ := hN
  have hl3 : 1 ∈ Finset.Ioo 0 l := by
    have := (Fact.out : l.Prime).two_le
    rw [Finset.mem_Ioo]; omega
  have hsum : ∀ i (J : Finset (Fin n)),
      ((∑ j ∈ J, (U' i j).toNat : ℕ) : ℤ) = ∑ j ∈ J, U' i j := by
    intro i J
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun j _ => Int.toNat_of_nonneg (hU i j))
  have hW1 : ∀ i, ∃ M : Matrix (Fin n) (Fin n) O⟦X⟧,
      N.P i * M = ((X - C (l : O)) ^ h) • (1 : Matrix (Fin n) (Fin n) O⟦X⟧) := by
    intro i
    obtain ⟨Q, hQ⟩ := hP5 i
    exact height_descent_holds l O hl2 n h (N.P i) Q hQ
  obtain ⟨hlI, hl0, hq0X, hev⟩ :=
    localization_facts_hold l O L I ζ em (u : ℤ_[l]) 1 (jj 1) hl2 hζ hζI hem hl3 (hloc 1 hl3)
  refine ⟨hW1, ?_, ?_, hTh, ?_⟩
  ·
    intro i r S hS f g hf hg
    obtain ⟨m', hm'⟩ := roots_descent_holds l O I ζ hl2 hζ hζI S ((N.P i).submatrix f g).det (by
      intro b hb
      have hbI : ζ ^ b - 1 ∈ I := by
        have h1 : ζ ^ b - 1 = (ζ - 1) * ∑ i ∈ Finset.range b, ζ ^ i := (mul_geom_sum ζ b).symm
        rw [h1]
        exact I.mul_mem_right _ hζI
      obtain ⟨hC, hX, -⟩ := hloc b hb
      refine order_descent_holds O I (ζ ^ b - 1) L em (jj b) hbI hem hC hX S _ ?_
      obtain ⟨G, H, hGH, -⟩ := hloc4 i b hb
      rw [pi0Subst_det_map, ← Matrix.submatrix_map, hGH]
      refine diagonal_minors_holds L⟦X⟧ n r S X (fun a => (U' i a).toNat) G H ?_ f g hf hg
      intro J hJ
      have h1 := hS J hJ
      rw [← hsum i J] at h1
      exact_mod_cast h1)
    exact ⟨m', hm'⟩
  ·
    intro i
    obtain ⟨M, hM⟩ := hW1 i
    have hdet := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← pow_mul]
      at hdet
    have hp : Prime (X - C (l : O) : O⟦X⟧) := linear_prime_holds O I (l : O) hlI
    obtain ⟨e, -, hass⟩ := (dvd_prime_pow hp (h * n)).1 ⟨M.det, hdet.symm⟩
    obtain ⟨G, H, hGH, -⟩ := hloc4 i 1 hl3
    have h1 : Associated ((jj 1).comp (pi0SubstHom l O) (N.P i).det)
        ((jj 1).comp (pi0SubstHom l O) ((X - C (l : O)) ^ e)) := hass.map _
    rw [RingHom.comp_apply, RingHom.comp_apply, pi0SubstHom_apply, pi0SubstHom_apply,
      inc_pow, inc_X_sub_l_eq_q0, map_pow, pi0Subst_det_map, hGH, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum] at h1
    have hG : IsUnit (G : Matrix (Fin n) (Fin n) L⟦X⟧).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 G.isUnit
    have hH : IsUnit (H : Matrix (Fin n) (Fin n) L⟦X⟧).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 H.isUnit
    have h2 : Associated ((X : L⟦X⟧) ^ (∑ j, (U' i j).toNat))
        ((G : Matrix (Fin n) (Fin n) L⟦X⟧).det * X ^ (∑ j, (U' i j).toNat) *
          (H : Matrix (Fin n) (Fin n) L⟦X⟧).det) :=
      ((associated_mul_unit_left _ _ hH).trans (associated_unit_mul_left _ _ hG)).symm
    have h3 : Associated ((X : L⟦X⟧) ^ (∑ j, (U' i j).toNat)) ((X : L⟦X⟧) ^ e) :=
      (h2.trans h1).trans (hq0X.pow_pow)
    have hXu : ¬ IsUnit (X : L⟦X⟧) := PowerSeries.X_prime.not_isUnit
    have h4 : ∑ j, (U' i j).toNat = e :=
      le_antisymm ((pow_dvd_pow_iff X_ne_zero hXu).1 h3.dvd)
        ((pow_dvd_pow_iff X_ne_zero hXu).1 h3.symm.dvd)
    have h5 : (∑ j, U' i j).toNat = e := by
      rw [← hsum i Finset.univ, Int.toNat_natCast, h4]
    rw [h5]
    obtain ⟨v, hv⟩ := hass.symm
    exact ⟨v, by rw [← hv, mul_comm]⟩
  ·
    intro i
    choose e he using fun j => theta_congruence_padic l u c (U' i j) hu
    refine ⟨fun j => -(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j, he, ?_⟩
    obtain ⟨G, H, -, hγ⟩ := hloc4 i 1 hl3
    have hk := constantCoeff_conj_diagonal_rescale _ _ _ _ hγ
    have hA : ((1 + (X : O⟦X⟧) • N.D i).map (fun y => jj 1 (inc l O y))).map constantCoeff =
        (1 + (l : O) • N.Th i).map em := by
      ext1 x y
      rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]
      exact hev _ _ (one_add_X_smul_sub_C_dvd (l : O) (N.D i) (N.Th i) (hTh i) x y)
    rw [hA] at hk
    have hunit : ∀ j, (u : ℤ_[l]) ^ (U' i j).toNat *
        (1 + (l : ℤ_[l]) * (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j)) = 1 := by
      intro j
      rw [← he j, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
      have : u ^ (U' i j).toNat * u ^ (-(U' i j)) = 1 := by
        rw [← zpow_natCast, Int.toNat_of_nonneg (hU i j), ← zpow_add, add_neg_cancel, zpow_zero]
      rw [this, Units.val_one]
    let G0 : (Matrix (Fin n) (Fin n) L)ˣ :=
      Units.map (RingHom.mapMatrix (constantCoeff (R := L))).toMonoidHom G
    have hG0 : (G0 : Matrix (Fin n) (Fin n) L) =
        (G : Matrix (Fin n) (Fin n) L⟦X⟧).map constantCoeff := rfl
    refine charpoly_diagonal_holds O L em n (N.Th i) (1 + (l : O) • N.Th i) (l : O)
      (fun j => algebraMap ℤ_[l] O (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j)) G0 hem hl0
      rfl ?_
    rw [hG0]
    have hdd : Matrix.diagonal (fun j => em (algebraMap ℤ_[l] O (u : ℤ_[l])) ^ (U' i j).toNat) *
        Matrix.diagonal (fun j => em (1 + (l : O) *
          algebraMap ℤ_[l] O (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j))) =
        (1 : Matrix (Fin n) (Fin n) L) := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext j
      have := congrArg (fun z => em (algebraMap ℤ_[l] O z)) (hunit j)
      simp only [map_mul, map_pow, map_add, map_one, map_natCast] at this
      simp only [map_mul, map_add, map_one, map_natCast]
      exact this
    calc (1 + (l : O) • N.Th i).map em * (G : Matrix (Fin n) (Fin n) L⟦X⟧).map constantCoeff
        = (1 + (l : O) • N.Th i).map em * (G : Matrix (Fin n) (Fin n) L⟦X⟧).map constantCoeff *
            (Matrix.diagonal (fun j => em (algebraMap ℤ_[l] O (u : ℤ_[l])) ^ (U' i j).toNat) *
            Matrix.diagonal (fun j => em (1 + (l : O) *
              algebraMap ℤ_[l] O (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j)))) := by
          rw [hdd, Matrix.mul_one]
      _ = (G : Matrix (Fin n) (Fin n) L⟦X⟧).map constantCoeff *
            Matrix.diagonal (fun j => em (1 + (l : O) *
              algebraMap ℤ_[l] O (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j))) := by
          rw [← Matrix.mul_assoc, hk]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
