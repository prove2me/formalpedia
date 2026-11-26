-- Prove2me | solution 1 for FD1D.FiniteKernel.stationary_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:02.41937+00:00
-- url     : https://prove2.me/submissions/111dd77e-8e09-4dd6-90fb-2a8e708b09cb

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
import Theorems.Thm_FD1D_FiniteKernel_pow_nonneg
import Theorems.Thm_FD1D_FiniteKernel_stationary_mass_pos

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]
namespace FD1D.FiniteKernel
theorem _root_.solution [DecidableEq α] [Nonempty α]
    {K : FiniteKernel α} (hirr : K.Irreducible)
    {μ ν : FiniteLaw α}
    (hμ : K.IsStationary μ) (hν : K.IsStationary ν) :
    μ = ν := by
  let ratio : α → ℝ := fun x => μ.mass x / ν.mass x
  obtain ⟨x₀, _, hx₀⟩ :=
    Finset.exists_max_image (Finset.univ : Finset α) ratio
      Finset.univ_nonempty
  have hνpos (x : α) : 0 < ν.mass x :=
    stationary_mass_pos hirr hν x
  have hratio_le (x : α) : ratio x ≤ ratio x₀ :=
    hx₀ x (Finset.mem_univ x)
  have hmass_le (x : α) :
      μ.mass x ≤ ratio x₀ * ν.mass x :=
    (div_le_iff₀ (hνpos x)).mp (hratio_le x)
  have hratio_eq (y : α) : ratio y = ratio x₀ := by
    apply le_antisymm (hratio_le y)
    by_contra hnot
    have hylt : ratio y < ratio x₀ := lt_of_not_ge hnot
    obtain ⟨n, hyn⟩ := hirr y x₀
    have hle (z : α) :
        μ.mass z * K.pow n z x₀ ≤
          (ratio x₀ * ν.mass z) * K.pow n z x₀ :=
      mul_le_mul_of_nonneg_right (hmass_le z) (K.pow_nonneg n z x₀)
    have hyMass : μ.mass y < ratio x₀ * ν.mass y :=
      (div_lt_iff₀ (hνpos y)).mp hylt
    have hyterm :
        μ.mass y * K.pow n y x₀ <
          (ratio x₀ * ν.mass y) * K.pow n y x₀ :=
      mul_lt_mul_of_pos_right hyMass hyn
    have hsumlt :
        (∑ z, μ.mass z * K.pow n z x₀) <
          ∑ z, (ratio x₀ * ν.mass z) * K.pow n z x₀ :=
      Finset.sum_lt_sum
        (fun z _ => hle z)
        ⟨y, Finset.mem_univ y, hyterm⟩
    have hμsum :
        ∑ z, μ.mass z * K.pow n z x₀ = μ.mass x₀ := by
      rw [← K.mass_iterate n μ x₀, hμ.iterate n]
    have hνsum :
        ∑ z, ν.mass z * K.pow n z x₀ = ν.mass x₀ := by
      rw [← K.mass_iterate n ν x₀, hν.iterate n]
    have hcontra : μ.mass x₀ < μ.mass x₀ := by
      calc
        μ.mass x₀ = ∑ z, μ.mass z * K.pow n z x₀ := hμsum.symm
        _ < ∑ z, (ratio x₀ * ν.mass z) * K.pow n z x₀ := hsumlt
        _ = ratio x₀ * ∑ z, ν.mass z * K.pow n z x₀ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _
          ring
        _ = ratio x₀ * ν.mass x₀ := by rw [hνsum]
        _ = μ.mass x₀ := by
          exact div_mul_cancel₀ _ (ne_of_gt (hνpos x₀))
    exact (lt_irrefl _ hcontra).elim
  have hmass (x : α) : μ.mass x = ratio x₀ * ν.mass x := by
    have hx := hratio_eq x
    exact (div_eq_iff (ne_of_gt (hνpos x))).mp hx
  have hsum : (1 : ℝ) = ratio x₀ := by
    calc
      1 = ∑ x, μ.mass x := μ.sum_mass.symm
      _ = ∑ x, ratio x₀ * ν.mass x := by
        apply Finset.sum_congr rfl
        intro x _
        exact hmass x
      _ = ratio x₀ * ∑ x, ν.mass x := (Finset.mul_sum _ _ _).symm
      _ = ratio x₀ := by rw [ν.sum_mass, mul_one]
  apply FiniteLaw.ext
  intro x
  rw [hmass x, ← hsum, one_mul]
end FD1D.FiniteKernel
