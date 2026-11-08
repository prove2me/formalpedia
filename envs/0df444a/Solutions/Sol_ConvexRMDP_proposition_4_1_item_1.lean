-- Prove2me | solution 1 for ConvexRMDP.proposition_4_1_item_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:26:09.003318+00:00
-- url     : https://prove2.me/submissions/cf1823f3-58d4-4ade-9b5a-9b59eea473fb

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP_regOp

namespace Aux_CR41

open ConvexRMDP

variable {S A : Type*} [Fintype S] [Fintype A]

theorem simplex_sum (p : S → ℝ) (hp : p ∈ stdSimplex ℝ S) : ∑ s, p s = 1 := hp.2
theorem simplex_nn (p : S → ℝ) (hp : p ∈ stdSimplex ℝ S) (s : S) : 0 ≤ p s := hp.1 s

theorem dot_le (p : S → ℝ) (hp : p ∈ stdSimplex ℝ S) (v w : S → ℝ) (d : ℝ)
    (h : ∀ s, v s ≤ w s + d) : ∑ s, p s * v s ≤ ∑ s, p s * w s + d := by
  have : ∑ s, p s * v s ≤ ∑ s, p s * (w s + d) :=
    Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (h s) (simplex_nn p hp s))
  rw [Finset.sum_congr rfl (fun s _ => mul_add (p s) (w s) d), Finset.sum_add_distrib,
    ← Finset.sum_mul, simplex_sum p hp, one_mul] at this
  exact this

theorem worst_bdd (M : RMDP S A) (v : S → ℝ) (s : S) (a : A) :
    BddBelow ((fun p : S → ℝ => ∑ s', p s' * v s') '' M.U s a) := by
  refine ⟨-(∑ s', |v s'|), ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hpS := M.U_subset s a hp
  have : ∀ s', -|v s'| ≤ p s' * v s' := by
    intro s'
    have h1 := simplex_nn p hpS s'
    have h2 : p s' ≤ 1 := by
      rw [← simplex_sum p hpS]
      exact Finset.single_le_sum (fun i _ => simplex_nn p hpS i) (Finset.mem_univ s')
    have := neg_abs_le (v s')
    have := le_abs_self (v s')
    nlinarith [abs_nonneg (v s')]
  calc -(∑ s', |v s'|) = ∑ s', -|v s'| := by rw [Finset.sum_neg_distrib]
    _ ≤ ∑ s', p s' * v s' := Finset.sum_le_sum (fun s' _ => this s')

theorem worst_shift (M : RMDP S A) (v w : S → ℝ) (d : ℝ) (h : ∀ s, v s ≤ w s + d) (s : S) (a : A) :
    M.worst v s a ≤ M.worst w s a + d := by
  unfold RMDP.worst
  have hle : sInf ((fun p : S → ℝ => ∑ s', p s' * v s') '' M.U s a) - d ≤
      sInf ((fun p : S → ℝ => ∑ s', p s' * w s') '' M.U s a) := by
    apply le_csInf ((M.U_nonempty s a).image _)
    rintro _ ⟨p, hp, rfl⟩
    have h1 := csInf_le (worst_bdd M v s a) ⟨p, hp, rfl⟩
    have h2 := dot_le p (M.U_subset s a hp) v w d h
    simp only at h1
    linarith
  linarith

theorem kl_nonneg [Nonempty A] (π : A → ℝ) (hπ : π ∈ stdSimplex ℝ A) :
    0 ≤ kl π (fun _ => 1 / (Fintype.card A : ℝ)) := by
  unfold kl
  show 0 ≤ ∑ a, π a * Real.log (π a / (1 / (Fintype.card A : ℝ)))
  have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ a, π a - 1 / (Fintype.card A : ℝ) ≤ π a * Real.log (π a / (1 / (Fintype.card A : ℝ))) := by
    intro a
    have h0 := simplex_nn π hπ a
    rcases h0.eq_or_lt with h | h
    · rw [← h]; simp
    · have hy : 0 < π a * Fintype.card A := mul_pos h hc
      have hk := Real.one_sub_inv_le_log_of_pos hy
      rw [show π a / (1 / (Fintype.card A : ℝ)) = π a * Fintype.card A by field_simp]
      have : π a * (1 - (π a * Fintype.card A)⁻¹) = π a - 1 / (Fintype.card A : ℝ) := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_left hk h.le]
  have := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hterm a)
  rw [Finset.sum_sub_distrib, simplex_sum π hπ, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at this
  have e : (Fintype.card A : ℝ) * (1 / (Fintype.card A : ℝ)) = 1 := by field_simp
  linarith

end Aux_CR41

open ConvexRMDP Aux_CR41 in
theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) :
    Monotone (M.regOp b) ∧ ContractingWith ⟨M.γ, M.γ_pos.le⟩ (M.regOp b) := by
  classical
  have hγ0 := M.γ_pos.le
  -- the objective
  set F : (S → ℝ) → S → (A → ℝ) → ℝ := fun v s π => ∑ a, π a * (M.r s a + M.γ * M.worst v s a)
      - kl π (fun _ => 1 / (Fintype.card A : ℝ)) / b with hF
  have hreg : ∀ v s, M.regOp b v s = sSup ((F v s) '' stdSimplex ℝ A) := fun v s => rfl
  obtain ⟨a0⟩ := ‹Nonempty A›
  have hne : (stdSimplex ℝ A).Nonempty := ⟨Pi.single a0 1, by
    refine ⟨fun a => ?_, ?_⟩
    · by_cases h : a = a0 <;> simp [Pi.single_apply, h]
    · simp⟩
  -- worst is bounded above by some value
  have hworst_up : ∀ v s a, M.worst v s a ≤ ∑ s', |v s'| := by
    intro v s a
    obtain ⟨p, hp⟩ := M.U_nonempty s a
    have hpS := M.U_subset s a hp
    unfold RMDP.worst
    refine (csInf_le (worst_bdd M v s a) ⟨p, hp, rfl⟩).trans ?_
    apply Finset.sum_le_sum; intro s' _
    have h1 := simplex_nn p hpS s'
    have h2 : p s' ≤ 1 := by
      rw [← simplex_sum p hpS]
      exact Finset.single_le_sum (fun i _ => simplex_nn p hpS i) (Finset.mem_univ s')
    have := le_abs_self (v s')
    nlinarith [abs_nonneg (v s')]
  have hbdd : ∀ v s, BddAbove ((F v s) '' stdSimplex ℝ A) := by
    intro v s
    refine ⟨∑ a, (|M.r s a| + M.γ * ∑ s', |v s'|), ?_⟩
    rintro _ ⟨π, hπ, rfl⟩
    simp only [hF]
    have hkl := kl_nonneg π hπ
    have hk : 0 ≤ kl π (fun _ => 1 / (Fintype.card A : ℝ)) / b := div_nonneg hkl hb.le
    have : ∑ a, π a * (M.r s a + M.γ * M.worst v s a) ≤ ∑ a, (|M.r s a| + M.γ * ∑ s', |v s'|) := by
      apply Finset.sum_le_sum; intro a _
      have h1 := simplex_nn π hπ a
      have h2 : π a ≤ 1 := by
        rw [← simplex_sum π hπ]
        exact Finset.single_le_sum (fun i _ => simplex_nn π hπ i) (Finset.mem_univ a)
      have hw := hworst_up v s a
      have hr := le_abs_self (M.r s a)
      have hs : 0 ≤ ∑ s', |v s'| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hwlow : -(∑ s', |v s'|) ≤ M.worst v s a := by
        obtain ⟨p, hp⟩ := M.U_nonempty s a
        unfold RMDP.worst
        apply le_csInf ((M.U_nonempty s a).image _)
        rintro _ ⟨p', hp', rfl⟩
        have hpS := M.U_subset s a hp'
        have : ∀ s', -|v s'| ≤ p' s' * v s' := by
          intro s'
          have h1 := simplex_nn p' hpS s'
          have h2 : p' s' ≤ 1 := by
            rw [← simplex_sum p' hpS]
            exact Finset.single_le_sum (fun i _ => simplex_nn p' hpS i) (Finset.mem_univ s')
          have := neg_abs_le (v s')
          have := le_abs_self (v s')
          nlinarith [abs_nonneg (v s')]
        calc -(∑ s', |v s'|) = ∑ s', -|v s'| := by rw [Finset.sum_neg_distrib]
          _ ≤ ∑ s', p' s' * v s' := Finset.sum_le_sum (fun s' _ => this s')
      have hRW : |M.r s a + M.γ * M.worst v s a| ≤ |M.r s a| + M.γ * ∑ s', |v s'| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos M.γ_pos]
        have : |M.worst v s a| ≤ ∑ s', |v s'| := abs_le.mpr ⟨by linarith, hw⟩
        nlinarith
      have := le_abs_self (M.r s a + M.γ * M.worst v s a)
      have h3 : π a * (M.r s a + M.γ * M.worst v s a) ≤ π a * |M.r s a + M.γ * M.worst v s a| :=
        mul_le_mul_of_nonneg_left this h1
      have h4 : π a * |M.r s a + M.γ * M.worst v s a| ≤ |M.r s a + M.γ * M.worst v s a| := by
        nlinarith [abs_nonneg (M.r s a + M.γ * M.worst v s a)]
      linarith
    linarith
  -- key comparison
  have hcomp : ∀ v w : S → ℝ, ∀ d : ℝ, 0 ≤ d → (∀ s, v s ≤ w s + d) →
      ∀ s, M.regOp b v s ≤ M.regOp b w s + M.γ * d := by
    intro v w d hd h s
    rw [hreg, hreg]
    apply csSup_le (hne.image _)
    rintro _ ⟨π, hπ, rfl⟩
    have h1 := le_csSup (hbdd w s) ⟨π, hπ, rfl⟩
    have h2 : F v s π ≤ F w s π + M.γ * d := by
      simp only [hF]
      have : ∑ a, π a * (M.r s a + M.γ * M.worst v s a) ≤
          ∑ a, π a * (M.r s a + M.γ * M.worst w s a) + M.γ * d := by
        have hh : ∀ a, π a * (M.r s a + M.γ * M.worst v s a) ≤
            π a * (M.r s a + M.γ * M.worst w s a) + π a * (M.γ * d) := by
          intro a
          have hwa := worst_shift M v w d h s a
          have h0 := simplex_nn π hπ a
          nlinarith [mul_le_mul_of_nonneg_left hwa (mul_nonneg h0 hγ0)]
        calc ∑ a, π a * (M.r s a + M.γ * M.worst v s a)
            ≤ ∑ a, (π a * (M.r s a + M.γ * M.worst w s a) + π a * (M.γ * d)) :=
              Finset.sum_le_sum (fun a _ => hh a)
          _ = ∑ a, π a * (M.r s a + M.γ * M.worst w s a) + M.γ * d := by
              rw [Finset.sum_add_distrib, ← Finset.sum_mul, simplex_sum π hπ, one_mul]
      linarith
    linarith
  refine ⟨fun v w hvw s => ?_, ?_, ?_⟩
  · have := hcomp v w 0 le_rfl (fun s => by simp [hvw s]) s
    simpa using this
  · exact NNReal.coe_lt_coe.mp
      (by simpa using M.γ_lt_one : ((⟨M.γ, M.γ_pos.le⟩ : NNReal) : ℝ) < ((1 : NNReal) : ℝ))
  · apply LipschitzWith.of_dist_le_mul
    intro v w
    show dist (M.regOp b v) (M.regOp b w) ≤ M.γ * dist v w
    have hd := dist_nonneg (x := v) (y := w)
    rw [dist_pi_le_iff (mul_nonneg hγ0 hd)]
    intro s
    have hvw : ∀ s, v s ≤ w s + dist v w := by
      intro s
      have := dist_le_pi_dist v w s
      rw [Real.dist_eq] at this
      linarith [le_abs_self (v s - w s)]
    have hwv : ∀ s, w s ≤ v s + dist v w := by
      intro s
      have := dist_le_pi_dist v w s
      rw [Real.dist_eq] at this
      linarith [neg_abs_le (v s - w s)]
    have h1 := hcomp v w _ hd hvw s
    have h2 := hcomp w v _ hd hwv s
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
