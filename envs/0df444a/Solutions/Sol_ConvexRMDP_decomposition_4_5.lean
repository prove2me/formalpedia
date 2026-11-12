-- Prove2me | solution 1 for ConvexRMDP.decomposition_4_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T23:11:30.6366+00:00
-- url     : https://prove2.me/submissions/a4aa338c-ec94-41bb-be42-d9ffad899558

import Definitions.Def_ConvexRMDP_RMDP_regOp
import Definitions.Def_ConvexRMDP_RMDP_tOp
import Theorems.Thm_ConvexRMDP_display_4_3

namespace _M7DecompHelper

open ConvexRMDP

lemma exp_mul_sInf {E : Set ℝ} (hne : E.Nonempty) (hbdd : BddBelow E) {c : ℝ} (hc : 0 < c) :
    Real.exp (c * sInf E) = sInf ((fun t : ℝ => Real.exp (c * t)) '' E) := by
  let I : ℝ := sInf ((fun t : ℝ => Real.exp (c * t)) '' E)
  have hle : Real.exp (c * sInf E) ≤ I := by
    refine le_csInf (hne.image _) ?_
    rintro _ ⟨t, ht, rfl⟩
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (csInf_le hbdd ht) hc.le)
  have hI_pos : 0 < I := (Real.exp_pos _).trans_le hle
  have hbdd_img : BddBelow ((fun t : ℝ => Real.exp (c * t)) '' E) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, -, rfl⟩
    exact (Real.exp_pos _).le
  have hlog_le : Real.log I / c ≤ sInf E := by
    refine le_csInf hne fun t ht => ?_
    have hIt : I ≤ Real.exp (c * t) := csInf_le hbdd_img ⟨t, ht, rfl⟩
    have hlog : Real.log I ≤ c * t := by
      have h1 := Real.log_le_log hI_pos hIt
      rwa [Real.log_exp] at h1
    rw [div_le_iff₀ hc]
    linarith
  have hc_le : Real.log I ≤ c * sInf E := by
    rw [div_le_iff₀ hc] at hlog_le
    linarith
  have hge : I ≤ Real.exp (c * sInf E) := by
    calc I = Real.exp (Real.log I) := (Real.exp_log hI_pos).symm
      _ ≤ Real.exp (c * sInf E) := Real.exp_le_exp.mpr hc_le
  exact le_antisymm hle hge

lemma worst_set_bddBelow {S A : Type*} [Fintype S] [Fintype A]
    (M : RMDP S A) (w : S → ℝ) (s : S) (a : A) :
    BddBelow ((fun p : S → ℝ => ∑ s', p s' * w s') '' M.U s a) := by
  refine ⟨-∑ s' : S, |w s'|, ?_⟩
  rintro _ ⟨p, hpU, rfl⟩
  have hp : p ∈ stdSimplex ℝ S := M.U_subset s a hpU
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun s' _ => ?_
  have hp_le : p s' ≤ 1 := (mem_Icc_of_mem_stdSimplex hp s').2
  have h1 : -|w s'| ≤ -(p s' * |w s'|) := by
    linarith [mul_le_mul_of_nonneg_right hp_le (abs_nonneg (w s'))]
  have h2 : -(p s' * |w s'|) ≤ p s' * w s' := by
    have hneg : -|w s'| ≤ w s' := neg_abs_le (w s')
    have hm := mul_le_mul_of_nonneg_left hneg (hp.1 s')
    linarith
  exact h1.trans h2

lemma rpow_prod_sInf_eq {S A : Type*} [Fintype S] [Fintype A]
    (M : RMDP S A) {x : S → ℝ} (hx : ∀ s, 0 < x s) (s : S) (a : A) :
    sInf ((fun p : S → ℝ => ∏ s', x s' ^ (M.γ * p s')) '' M.U s a) =
      Real.exp (M.γ * M.worst (fun s' => Real.log (x s')) s a) := by
  let w : S → ℝ := fun s' => Real.log (x s')
  have hprod : ∀ p : S → ℝ,
      (∏ s', x s' ^ (M.γ * p s')) = Real.exp (M.γ * ∑ s', p s' * w s') := by
    intro p
    have hterm : ∀ s' : S, x s' ^ (M.γ * p s') = Real.exp (w s' * (M.γ * p s')) := by
      intro s'
      calc x s' ^ (M.γ * p s')
          = (Real.exp (w s')) ^ (M.γ * p s') := by simp [w, Real.exp_log (hx s')]
        _ = Real.exp (w s' * (M.γ * p s')) := (Real.exp_mul (w s') (M.γ * p s')).symm
    simp_rw [hterm]
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    ring
  have himg : ((fun p : S → ℝ => ∏ s', x s' ^ (M.γ * p s')) '' M.U s a) =
      (fun t : ℝ => Real.exp (M.γ * t)) '' ((fun p : S → ℝ => ∑ s', p s' * w s') '' M.U s a) := by
    rw [← Set.image_comp]
    refine Set.image_congr fun p _ => hprod p
  rw [himg, ← exp_mul_sInf ((M.U_nonempty s a).image _) (worst_set_bddBelow M w s a) M.γ_pos]
  rfl

end _M7DecompHelper

open ConvexRMDP

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) :
    (∀ v : S → ℝ, M.regOp b v = fun s => logB b (M.tOp b (fun s' => expB b (v s')) s)) ∧
      ∀ x : S → ℝ, (∀ s, 0 < x s) → ∀ s, 0 < M.tOp b x s := by
  have hcard_pos : 0 < (Fintype.card A : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have homega_pos : ∀ s a, 0 < M.omega b s a := fun s a => by
    unfold RMDP.omega expB
    exact div_pos (Real.exp_pos _) hcard_pos
  have htOp_pos : ∀ x : S → ℝ, (∀ s, 0 < x s) → ∀ s, 0 < M.tOp b x s := by
    intro x hx s
    unfold RMDP.tOp
    refine Finset.sum_pos (fun a _ => ?_) Finset.univ_nonempty
    rw [_M7DecompHelper.rpow_prod_sInf_eq M hx s a]
    exact mul_pos (homega_pos s a) (Real.exp_pos _)
  refine ⟨fun v => ?_, htOp_pos⟩
  ext s
  rw [display_4_3 M b hb v s]
  unfold logB
  congr 1
  have hx : ∀ s', 0 < expB b (v s') := fun s' => Real.exp_pos _
  have hlog_expB : (fun s' => Real.log (expB b (v s'))) = fun s' => b * v s' := by
    ext s'
    unfold expB
    exact Real.log_exp (b * v s')
  have hworst_scale : ∀ a : A,
      M.worst (fun s' => b * v s') s a = b * M.worst v s a := by
    intro a
    unfold RMDP.worst
    let E := (fun p : S → ℝ => ∑ s', p s' * v s') '' M.U s a
    have himg : ((fun p : S → ℝ => ∑ s', p s' * (b * v s')) '' M.U s a) =
        (fun t : ℝ => b * t) '' E := by
      dsimp [E]
      rw [← Set.image_comp]
      refine Set.image_congr fun p _ => ?_
      dsimp [Function.comp]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      ring
    rw [himg]
    have hne : E.Nonempty := (M.U_nonempty s a).image _
    have hbdd : BddBelow E := _M7DecompHelper.worst_set_bddBelow M v s a
    have hbdd_b : BddBelow ((fun t : ℝ => b * t) '' E) := by
      obtain ⟨L, hL⟩ := hbdd
      refine ⟨b * L, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      exact mul_le_mul_of_nonneg_left (hL ht) hb.le
    refine le_antisymm ?_ ?_
    · have hdiv : sInf ((fun t : ℝ => b * t) '' E) / b ≤ sInf E := by
        refine le_csInf hne fun t ht => ?_
        rw [div_le_iff₀ hb]
        have hbt : sInf ((fun t : ℝ => b * t) '' E) ≤ b * t := csInf_le hbdd_b ⟨t, ht, rfl⟩
        linarith
      rw [div_le_iff₀ hb] at hdiv
      linarith
    · refine le_csInf (hne.image _) ?_
      rintro _ ⟨t, ht, rfl⟩
      exact mul_le_mul_of_nonneg_left (csInf_le hbdd ht) hb.le
  have htOp_eq : M.tOp b (fun s' => expB b (v s')) s =
      ∑ a, (1 / (Fintype.card A : ℝ)) *
        Real.exp (b * M.r s a + b * M.γ * M.worst v s a) := by
    unfold RMDP.tOp
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [_M7DecompHelper.rpow_prod_sInf_eq M hx s a, hlog_expB, hworst_scale a]
    unfold RMDP.omega expB
    have hexp_eq : Real.exp (b * M.r s a) * Real.exp (M.γ * (b * M.worst v s a)) =
        Real.exp (b * M.r s a + b * M.γ * M.worst v s a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc Real.exp (b * M.r s a) / (Fintype.card A : ℝ) * Real.exp (M.γ * (b * M.worst v s a))
        = (1 / (Fintype.card A : ℝ)) *
            (Real.exp (b * M.r s a) * Real.exp (M.γ * (b * M.worst v s a))) := by ring
      _ = (1 / (Fintype.card A : ℝ)) *
            Real.exp (b * M.r s a + b * M.γ * M.worst v s a) := by rw [hexp_eq]
  rw [htOp_eq]
