-- Prove2me | solution 1 for EisensteinSeries.sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/62569af8-a07d-5730-9bd8-c74f309f7f70

import Mathlib
import Definitions.Def_EisensteinSeries_EisensteinG
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EisensteinSeries_sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow

set_option autoImplicit false

set_option maxHeartbeats 4000000 in
open scoped Real in

theorem solution
    (N : ℕ) [NeZero N] (a : ZMod N) (ha : a ≠ 0) {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : UpperHalfPlane) :
    ∑ e : ZMod N, EisensteinSeries.eisensteinG N k ![a, e] z =
      ((-2 * π * Complex.I) ^ k / (Nat.factorial (k - 1) : ℂ)) *
        ∑' n : ℕ, (∑ d ∈ n.divisors,
            ((if ((n / d : ℕ) : ZMod N) = a then (d : ℂ) ^ (k - 1) else 0) +
              (if ((n / d : ℕ) : ZMod N) = -a then (d : ℂ) ^ (k - 1) else 0))) *
          Complex.exp (2 * π * Complex.I * z) ^ n := by
  classical

  obtain ⟨q, hq⟩ : ∃ q : ℂ, q = Complex.exp (2 * π * Complex.I * z) := ⟨_, rfl⟩
  have hqn : ‖q‖ < 1 := hq ▸ UpperHalfPlane.norm_exp_two_pi_I_lt_one z
  obtain ⟨C, hC⟩ : ∃ C : ℂ, C = (-2 * π * Complex.I) ^ k / (Nat.factorial (k - 1) : ℂ) := ⟨_, rfl⟩
  rw [← hC, ← hq]
  have hk1 : 1 ≤ k - 1 := by omega
  have hkk : k - 1 + 1 = k := by omega
  have hk3 : (3 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hkeven : Even (-(k : ℤ)) := (Int.even_coe_nat k |>.mpr hk2).neg

  let f : (Fin 2 → ℤ) → ℂ := fun v => EisensteinSeries.eisSummand k v z
  have hfsum : Summable fun v => ‖f v‖ := EisensteinSeries.summable_norm_eisSummand hk3 z

  let S : Set (Fin 2 → ℤ) := {v | ((v 0 : ℤ) : ZMod N) = a}

  have h1 : ∑ e : ZMod N, EisensteinSeries.eisensteinG N k ![a, e] z = ∑' v, S.indicator f v := by
    have hS : ∀ e : ZMod N, EisensteinSeries.eisensteinG N k ![a, e] z =
        ∑' v, ({v : Fin 2 → ℤ | ((↑) : ℤ → ZMod N) ∘ v = ![a, e]}).indicator f v := by
      intro e
      rw [EisensteinSeries.eisensteinG, ← tsum_subtype]
      rfl
    simp_rw [hS]
    rw [← Summable.tsum_finsetSum (fun e _ => (hfsum.of_norm.indicator _))]
    refine tsum_congr fun v => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hv : v ∈ S
    · have hv' : ((v 0 : ℤ) : ZMod N) = a := hv
      rw [if_pos hv, Finset.sum_eq_single ((v 1 : ℤ) : ZMod N)]
      · rw [if_pos]
        funext i
        fin_cases i <;> simp [hv']
      · intro e _ hne
        rw [if_neg]
        intro h
        apply hne
        have := congrFun h 1
        simpa using this.symm
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hv]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [if_neg]
      intro h
      apply hv
      show ((v 0 : ℤ) : ZMod N) = a
      have := congrFun h 0
      simpa using this

  let row : ℤ → ℂ := fun m => ∑' n : ℤ, f ![m, n]
  let F : ℤ × ℤ → ℂ := (S.indicator f) ∘ (finTwoArrowEquiv ℤ).symm
  have hF : ∀ p : ℤ × ℤ, F p = if ((p.1 : ℤ) : ZMod N) = a then f ![p.1, p.2] else 0 := fun p => by
    simp only [F, Function.comp_apply, finTwoArrowEquiv_symm_apply, Set.indicator_apply, S,
      Set.mem_setOf_eq, Matrix.cons_val_zero]
  have hFsum : Summable F := (Equiv.summable_iff _).mpr (hfsum.of_norm.indicator S)
  obtain ⟨G, hG⟩ : ∃ G : ℤ → ℂ, G = fun m => if ((m : ℤ) : ZMod N) = a then row m else 0 := ⟨_, rfl⟩
  have h2 : ∑' v, S.indicator f v = ∑' m : ℤ, G m := by
    rw [← ((finTwoArrowEquiv ℤ).symm.tsum_eq (S.indicator f)), show
      (fun c : ℤ × ℤ => S.indicator f ((finTwoArrowEquiv ℤ).symm c)) = F from rfl, hFsum.tsum_prod]
    refine tsum_congr fun m => ?_
    simp only [hF, hG]
    split_ifs with hm
    · rfl
    · exact tsum_zero

  have hGsum : Summable G := by
    refine hFsum.prod.congr fun m => ?_
    simp only [hF, hG]
    split_ifs with hm
    · rfl
    · exact tsum_zero
  have hrowsum : Summable row := by

    have hall : Summable (f ∘ (finTwoArrowEquiv ℤ).symm) := (Equiv.summable_iff _).mpr hfsum.of_norm
    refine hall.prod.congr fun m => ?_
    simp only [Function.comp_apply, finTwoArrowEquiv_symm_apply]
    rfl
  have hrow_neg : ∀ m : ℤ, row (-m) = row m := by
    intro m
    simp only [row]
    rw [← (Equiv.neg ℤ).tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [f, Equiv.neg_apply, EisensteinSeries.eisSummand, Matrix.cons_val_zero,
      Matrix.cons_val_one, Int.cast_neg]
    rw [neg_mul, ← neg_add, hkeven.neg_zpow]

  have hG0 : ∀ m : ℕ, G (m : ℤ) = (if ((m : ℕ) : ZMod N) = a then (1 : ℂ) else 0) * row m := fun m => by
    rw [hG]
    dsimp only
    rw [Int.cast_natCast, boole_mul]
  have hGneg : ∀ m : ℕ, G (-((m : ℤ) + 1)) =
      (if (((m + 1 : ℕ)) : ZMod N) = -a then (1 : ℂ) else 0) * row ((m : ℤ) + 1) := fun m => by
    rw [hG]
    dsimp only
    rw [hrow_neg, boole_mul]
    have : ((((-((m : ℤ) + 1)) : ℤ) : ZMod N) = a) ↔ (((m + 1 : ℕ) : ZMod N) = -a) := by
      push_cast
      rw [neg_eq_iff_eq_neg]
    simp only [this]
  have hsumA : Summable fun m : ℕ => (if ((m : ℕ) : ZMod N) = a then (1 : ℂ) else 0) * row m := by
    have := hGsum.comp_injective Nat.cast_injective
    refine this.congr fun m => ?_
    exact hG0 m
  have hsumB : Summable fun m : ℕ => (if ((m : ℕ) : ZMod N) = -a then (1 : ℂ) else 0) * row m := by

    have := hrowsum.comp_injective Nat.cast_injective
    refine Summable.of_norm_bounded this.norm fun m => ?_
    simp only [Function.comp_apply, norm_mul]
    split_ifs <;> simp
  have h3 : ∑' m : ℤ, G m =
      ∑' m : ℕ, ((if ((m : ℕ) : ZMod N) = a then (1 : ℂ) else 0) +
        (if ((m : ℕ) : ZMod N) = -a then (1 : ℂ) else 0)) * row m := by
    have hinj : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := by
      intro x y h
      simp only [neg_inj, add_left_inj, Nat.cast_inj] at h
      exact h
    have hsN : Summable fun n : ℕ => G (n : ℤ) := hGsum.comp_injective Nat.cast_injective
    have hsNeg : Summable fun n : ℕ => G (-((n : ℤ) + 1)) := hGsum.comp_injective hinj
    rw [tsum_of_nat_of_neg_add_one (f := G) hsN hsNeg]
    simp only [hG0, hGneg]
    have hB' : ∑' m : ℕ, (if ((m + 1 : ℕ) : ZMod N) = -a then (1 : ℂ) else 0) * row ((m : ℤ) + 1) =
        ∑' m : ℕ, (if ((m : ℕ) : ZMod N) = -a then (1 : ℂ) else 0) * row m := by
      rw [hsumB.tsum_eq_zero_add]
      have h0 : ¬ ((0 : ℕ) : ZMod N) = -a := by
        rw [Nat.cast_zero, eq_comm, neg_eq_zero]
        exact ha
      rw [if_neg h0, zero_mul, zero_add]
      push_cast
      rfl
    rw [hB', ← hsumA.tsum_add hsumB]
    exact tsum_congr fun m => by ring

  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℂ, w = fun m =>
      (if ((m : ℕ) : ZMod N) = a then (1 : ℂ) else 0) + (if ((m : ℕ) : ZMod N) = -a then (1 : ℂ) else 0) :=
    ⟨_, rfl⟩
  have hw0 : w 0 = 0 := by
    have h1 : ¬ ((0 : ℕ) : ZMod N) = a := by rw [Nat.cast_zero]; exact fun h => ha h.symm
    have h2 : ¬ ((0 : ℕ) : ZMod N) = -a := by
      rw [Nat.cast_zero, eq_comm, neg_eq_zero]; exact ha
    rw [hw]
    dsimp only
    rw [if_neg h1, if_neg h2, add_zero]
  have hwnorm : ∀ m, ‖w m‖ ≤ 2 := fun m => by
    rw [hw]
    dsimp only
    refine (norm_add_le _ _).trans ?_
    have : ∀ P : Prop, ∀ _ : Decidable P, ‖(if P then (1 : ℂ) else 0)‖ ≤ 1 := by
      intro P _; split_ifs <;> simp
    linarith [this (((m : ℕ) : ZMod N) = a) inferInstance, this (((m : ℕ) : ZMod N) = -a) inferInstance]

  have hNP : ∀ (h : ℕ → ℂ), h 0 = 0 → Summable (fun n => h (n + 1)) →
      ∑' n : ℕ, h n = ∑' n : ℕ+, h n := fun h h0 hs => by
    rw [tsum_eq_zero_add' hs, h0, zero_add, tsum_pnat_eq_tsum_succ]

  have hrow : ∀ m : ℕ+, row m = C * ∑' d : ℕ+, (((d : ℕ) : ℂ) ^ (k - 1)) * q ^ ((m : ℕ) * (d : ℕ)) := by
    intro m
    have hm : 0 < (m : ℕ) := m.pos
    have hz' : 0 < (((m : ℕ) : ℂ) * (z : ℂ)).im := by
      simpa [Complex.mul_im] using mul_pos (Nat.cast_pos.mpr hm : (0 : ℝ) < m) z.im_pos
    have H := EisensteinSeries.qExpansion_identity (k := k - 1) hk1 ⟨((m : ℕ) : ℂ) * z, hz'⟩
    rw [hkk] at H
    have hlhs : row m = ∑' n : ℤ, 1 / (((⟨((m : ℕ) : ℂ) * z, hz'⟩ : UpperHalfPlane) : ℂ) + n) ^ k := by
      refine tsum_congr fun n => ?_
      simp only [f, EisensteinSeries.eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [zpow_neg, zpow_natCast, one_div]
      push_cast
      rfl
    rw [hlhs, H, ← hC]
    congr 1

    have hqm : Complex.exp (2 * π * Complex.I * (((⟨((m : ℕ) : ℂ) * z, hz'⟩ : UpperHalfPlane) : ℂ)))
        = q ^ (m : ℕ) := by
      rw [UpperHalfPlane.coe_mk, hq, ← Complex.exp_nat_mul]
      congr 1
      ring
    simp_rw [hqm, ← pow_mul]
    refine hNP (fun d => ((d : ℂ) ^ (k - 1)) * q ^ ((m : ℕ) * d)) (by
      simp [zero_pow (by omega : k - 1 ≠ 0)]) ?_
    have hqn' : ‖q ^ (m : ℕ)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hqn (by omega)
    have := summable_pow_mul_geometric_of_norm_lt_one (k - 1) hqn'
    simp_rw [← pow_mul] at this
    exact (summable_nat_add_iff 1).mpr this

  let gP : ℕ+ × ℕ+ → ℂ := fun c => w c.1 * ((((c.2 : ℕ) : ℂ) ^ (k - 1)) * q ^ ((c.1 : ℕ) * (c.2 : ℕ)))
  have hgP : Summable gP := by
    refine Summable.of_norm_bounded ((summable_prod_mul_pow (𝕜 := ℂ) (k - 1) hqn).norm.mul_left 2)
      fun c => ?_
    simp only [gP, norm_mul]
    gcongr
    exact hwnorm _
  have h5 : ∑' m : ℕ, ((if ((m : ℕ) : ZMod N) = a then (1 : ℂ) else 0) +
        (if ((m : ℕ) : ZMod N) = -a then (1 : ℂ) else 0)) * row m = C * ∑' c : ℕ+ × ℕ+, gP c := by
    have e : (fun m : ℕ => ((if ((m : ℕ) : ZMod N) = a then (1 : ℂ) else 0) +
        (if ((m : ℕ) : ZMod N) = -a then (1 : ℂ) else 0)) * row m) = fun m => w m * row m := by
      rw [hw]
    rw [e]
    have hsw : Summable (fun m : ℕ => w (m + 1) * row ((m + 1 : ℕ) : ℤ)) := by
      have := (hsumA.add hsumB)
      have h' : Summable fun m : ℕ => w m * row m := by
        refine this.congr fun m => ?_
        rw [hw]
        dsimp only
        ring
      exact (summable_nat_add_iff 1).mpr h'
    rw [hNP (fun m => w m * row m) (by simp [hw0]) hsw, hgP.tsum_prod, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    rw [hrow m, ← mul_assoc, mul_comm (w m) C, mul_assoc, ← tsum_mul_left]

  have h6 : ∑' c : ℕ+ × ℕ+, gP c =
      ∑' n : ℕ+, (∑ i ∈ (n : ℕ).divisors, w ((n : ℕ) / i) * ((i : ℂ) ^ (k - 1))) * q ^ (n : ℕ) := by
    have hs' : Summable (fun c : (n : ℕ+) × {x // x ∈ (n : ℕ).divisorsAntidiagonal} =>
        gP (sigmaAntidiagonalEquivProd c)) := sigmaAntidiagonalEquivProd.summable_iff.mpr hgP
    rw [← sigmaAntidiagonalEquivProd.tsum_eq, hs'.tsum_sigma]
    refine tsum_congr fun n => ?_
    simp only [tsum_fintype, Finset.univ_eq_attach, sigmaAntidiagonalEquivProd,
      divisorsAntidiagonalFactors, Equiv.coe_fn_mk, PNat.mk_coe, gP]
    rw [Finset.sum_attach ((n : ℕ).divisorsAntidiagonal)
      (fun p : ℕ × ℕ => w p.1 * (((p.2 : ℂ) ^ (k - 1)) * q ^ (p.1 * p.2))),
      Nat.sum_divisorsAntidiagonal' (fun x y => w x * (((y : ℂ) ^ (k - 1)) * q ^ (x * y))),
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hi)]
    ring

  rw [h1, h2, h3, h5, h6]
  congr 1
  have hfin : Summable fun n : ℕ+ =>
      (∑ i ∈ (n : ℕ).divisors, w ((n : ℕ) / i) * ((i : ℂ) ^ (k - 1))) * q ^ (n : ℕ) := by
    have hs' : Summable (fun c : (n : ℕ+) × {x // x ∈ (n : ℕ).divisorsAntidiagonal} =>
        gP (sigmaAntidiagonalEquivProd c)) := sigmaAntidiagonalEquivProd.summable_iff.mpr hgP
    refine hs'.sigma.congr fun n => ?_
    simp only [tsum_fintype, Finset.univ_eq_attach, sigmaAntidiagonalEquivProd,
      divisorsAntidiagonalFactors, Equiv.coe_fn_mk, PNat.mk_coe, gP]
    rw [Finset.sum_attach ((n : ℕ).divisorsAntidiagonal)
      (fun p : ℕ × ℕ => w p.1 * (((p.2 : ℂ) ^ (k - 1)) * q ^ (p.1 * p.2))),
      Nat.sum_divisorsAntidiagonal' (fun x y => w x * (((y : ℂ) ^ (k - 1)) * q ^ (x * y))),
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hi)]
    ring
  symm
  refine (hNP (fun n : ℕ => (∑ d ∈ n.divisors,
      ((if ((n / d : ℕ) : ZMod N) = a then (d : ℂ) ^ (k - 1) else 0) +
        (if ((n / d : ℕ) : ZMod N) = -a then (d : ℂ) ^ (k - 1) else 0))) * q ^ n)
    (by simp) ?_).trans ?_
  ·
    have := (Equiv.pnatEquivNat.symm.summable_iff).mpr hfin
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe, Nat.succ_eq_add_one, hw]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_mul, boole_mul, boole_mul]
    split_ifs <;> rfl
  · refine tsum_congr fun n => ?_
    rw [hw]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [add_mul, boole_mul, boole_mul]

end S_EisensteinSeries_sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow
end P2MW
export P2MW.S_EisensteinSeries_sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow (solution)
