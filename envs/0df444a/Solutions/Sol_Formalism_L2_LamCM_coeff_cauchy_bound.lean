-- Prove2me | solution 1 for Formalism.L2.LamCM.coeff_cauchy_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:18.433897+00:00
-- url     : https://prove2.me/submissions/3b7ace8c-98d3-452b-9a8e-9dc3e8f63e53

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
import Theorems.Thm_Formalism_L2_LamCM_geom_root_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace Formalism.L2.LamCM
theorem _root_.solution : CoeffCauchy := by
  unfold CoeffCauchy
  intro V _ G ρ S μ hρ hS
  classical
  set N : ℕ := (∑ ν ∈ G.support, ∑ v, ν v) + (∑ v, μ v) + 1 with hNdef
  have hN : 0 < N := Nat.succ_pos _
  have hνN : ∀ ν ∈ G.support, ∀ v, ν v < N := by
    intro ν hν v
    have h1 : ν v ≤ ∑ w, ν w := Finset.single_le_sum (fun w _ => Nat.zero_le _) (Finset.mem_univ v)
    have h2 : ∑ w, ν w ≤ ∑ ν' ∈ G.support, ∑ w, ν' w :=
      Finset.single_le_sum (f := fun ν' => ∑ w, ν' w) (fun _ _ => Nat.zero_le _) hν
    omega
  have hμN : ∀ v, μ v < N := by
    intro v
    have h1 : μ v ≤ ∑ w, μ w := Finset.single_le_sum (fun w _ => Nat.zero_le _) (Finset.mem_univ v)
    omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hζdef
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN.ne'
  have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one hN.ne'
  let z : (V → Fin N) → V → ℂ := fun k v => (ρ v : ℂ) * ζ ^ (k v : ℕ)
  have hz : ∀ k v, ‖z k v‖ ≤ ρ v := by
    intro k v
    simp only [z, norm_mul, norm_pow, hζn, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact le_of_eq (abs_of_pos (hρ v))
  have inner : ∀ ν ∈ G.support, ∑ k : V → Fin N,
      MvPolynomial.coeff ν G * (∏ v, z k v ^ ν v) * ∏ v, ζ⁻¹ ^ ((k v : ℕ) * μ v) =
      if ν = μ then (N : ℂ) ^ Fintype.card V * (MvPolynomial.coeff μ G * ∏ v, (ρ v : ℂ) ^ μ v) else 0 := by
    intro ν hν
    have hprod : ∀ k : V → Fin N, (∏ v, z k v ^ ν v) * ∏ v, ζ⁻¹ ^ ((k v : ℕ) * μ v) =
        (∏ v, (ρ v : ℂ) ^ ν v) * ∏ v, (ζ ^ ν v * ζ⁻¹ ^ μ v) ^ (k v : ℕ) := by
      intro k
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun v _ => by simp only [z]; ring)
    have hsum1 : ∑ k : V → Fin N, MvPolynomial.coeff ν G * (∏ v, z k v ^ ν v) * ∏ v, ζ⁻¹ ^ ((k v : ℕ) * μ v) =
        MvPolynomial.coeff ν G * ((∏ v, (ρ v : ℂ) ^ ν v) *
          ∑ k : V → Fin N, ∏ v, (ζ ^ ν v * ζ⁻¹ ^ μ v) ^ (k v : ℕ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by rw [mul_assoc, hprod k])
    have hsumk : ∑ k : V → Fin N, ∏ v, (ζ ^ ν v * ζ⁻¹ ^ μ v) ^ (k v : ℕ) =
        ∏ v, ∑ j : Fin N, (ζ ^ ν v * ζ⁻¹ ^ μ v) ^ (j : ℕ) := by
      rw [Fintype.prod_sum]
    have hgeom : ∀ v, ∑ j : Fin N, (ζ ^ ν v * ζ⁻¹ ^ μ v) ^ (j : ℕ) = if ν v = μ v then (N : ℂ) else 0 := fun v =>
      (Fin.sum_univ_eq_sum_range (fun j => (ζ ^ ν v * ζ⁻¹ ^ μ v) ^ j) N).trans
        (geom_root_sum hζ (hνN ν hν v) (hμN v))
    have hprodif : ∏ v, (if ν v = μ v then (N : ℂ) else 0) = if ν = μ then (N : ℂ) ^ Fintype.card V else 0 := by
      split_ifs with h
      · simp [h]
      · obtain ⟨v, hv⟩ : ∃ v, ν v ≠ μ v := by
          by_contra hc
          push_neg at hc
          exact h (Finsupp.ext hc)
        exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)
    rw [hsum1, hsumk, Finset.prod_congr rfl (fun v _ => hgeom v), hprodif]
    split_ifs with h
    · rw [h]
      ring
    · simp
  have hexp : ∀ k : V → Fin N, MvPolynomial.eval (z k) G * ∏ v, ζ⁻¹ ^ ((k v : ℕ) * μ v) =
      ∑ ν ∈ G.support, MvPolynomial.coeff ν G * (∏ v, z k v ^ ν v) * ∏ v, ζ⁻¹ ^ ((k v : ℕ) * μ v) := by
    intro k
    rw [MvPolynomial.eval_eq', Finset.sum_mul]
  have key : ∑ k : V → Fin N, MvPolynomial.eval (z k) G * ∏ v, ζ⁻¹ ^ ((k v : ℕ) * μ v) =
      (N : ℂ) ^ Fintype.card V * (MvPolynomial.coeff μ G * ∏ v, (ρ v : ℂ) ^ μ v) := by
    rw [Finset.sum_congr rfl (fun k _ => hexp k), Finset.sum_comm, Finset.sum_congr rfl inner]
    rw [Finset.sum_eq_single μ (fun ν _ hν => if_neg hν) (fun hμ => by
      have h0 : MvPolynomial.coeff μ G = 0 := by
        by_contra h
        exact hμ (MvPolynomial.mem_support_iff.mpr h)
      rw [if_pos rfl, h0]
      simp)]
    rw [if_pos rfl]
  have hbound : ‖(N : ℂ) ^ Fintype.card V * (MvPolynomial.coeff μ G * ∏ v, (ρ v : ℂ) ^ μ v)‖ ≤
      (N : ℝ) ^ Fintype.card V * S := by
    rw [← key]
    calc ‖∑ k : V → Fin N, MvPolynomial.eval (z k) G * ∏ v, ζ⁻¹ ^ ((k v : ℕ) * μ v)‖
        ≤ ∑ k : V → Fin N, ‖MvPolynomial.eval (z k) G * ∏ v, ζ⁻¹ ^ ((k v : ℕ) * μ v)‖ := norm_sum_le _ _
      _ ≤ ∑ _k : V → Fin N, S := by
          apply Finset.sum_le_sum
          intro k _
          rw [norm_mul, norm_prod]
          simp only [norm_pow, norm_inv, hζn, inv_one, one_pow, Finset.prod_const_one, mul_one]
          exact hS (z k) (hz k)
      _ = (N : ℝ) ^ Fintype.card V * S := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  simp only [norm_mul, norm_pow, norm_prod, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast] at hbound
  have hpos : (0:ℝ) < (N : ℝ) ^ Fintype.card V := pow_pos (Nat.cast_pos.mpr hN) _
  have habs : ∏ v, |ρ v| ^ μ v = ∏ v, ρ v ^ μ v :=
    Finset.prod_congr rfl (fun v _ => by rw [abs_of_pos (hρ v)])
  rw [habs] at hbound
  exact le_of_mul_le_mul_left hbound hpos
end Formalism.L2.LamCM
