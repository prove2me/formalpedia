-- Prove2me | solution 1 for FramingFulfillment.RFF.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T15:20:16.042848+00:00
-- url     : https://prove2.me/submissions/d9db61d8-ee46-4d09-b6f6-26f4eb195dd3

import Mathlib
import Definitions.Def_FramingFulfillment_RFF_Model
import Theorems.Thm_FramingFulfillment_RFF_lemma_2
import Theorems.Thm_FramingFulfillment_RFF_lemma_3
import Theorems.Thm_FramingFulfillment_RFF_framing_decomposition_exists
import Theorems.Thm_FramingFulfillment_RFF_lemma_5
import Theorems.Thm_FramingFulfillment_RFF_det_stationary
import Theorems.Thm_FramingFulfillment_RFF_rff_gap_upper

open FramingFulfillment.RFF Finset

namespace RFFAux

lemma le_finMax {α : Type*} {s : Finset α} {f : α → ℝ} {a : α} (ha : a ∈ s) :
    f a ≤ Inst.finMax s f := by
  unfold Inst.finMax
  rw [dif_pos ⟨a, ha⟩]
  exact Finset.le_sup' f ha

lemma vnn (P : Inst) (hP : P.Standing) : ∀ i j r, 0 ≤ P.v i j r := by
  obtain ⟨-, -, -, -, -, -, hvpos, hv0, -, -⟩ := hP
  intro i j r
  by_cases h : r = P.noDisp
  · rw [h, hv0]
  · exact (hvpos i j r h).le

lemma rhoTil_nonneg {I R : ℕ} {x : Fin I → Fin R → ℝ} (d : FramingDecomp x)
    (φ : Fin I → Fin R) : 0 ≤ rhoTil d φ := by
  classical
  unfold rhoTil
  refine Finset.sum_nonneg fun l _ => ?_
  split_ifs
  · exact (d.isDecomp.1 l).1.le
  · exact le_rfl

lemma rho_nonneg (P : Inst) (hP : P.Standing) (j : Fin P.J) {x : Fin P.I → Fin P.R → ℝ}
    (d : FramingDecomp x) (φ : Fin P.I → Fin P.R) : 0 ≤ P.rho j d φ := by
  unfold Inst.rho
  split_ifs
  · refine div_nonneg (mul_nonneg (rhoTil_nonneg d φ) ?_) ?_
    · have : 0 ≤ ∑ i, P.vPhi j φ i := Finset.sum_nonneg fun i _ => vnn P hP _ _ _
      linarith
    · have : 0 ≤ ∑ φ' ∈ P.Omega, rhoTil d φ' * ∑ i, P.vPhi j φ' i :=
        Finset.sum_nonneg fun φ' _ => mul_nonneg (rhoTil_nonneg d φ')
          (Finset.sum_nonneg fun i _ => vnn P hP _ _ _)
      linarith
  · exact le_rfl

/-- If `ρ(φ) > 0` then every coordinate of `φ` carries positive mass in `x`. -/
lemma x_pos_of_rho_pos (P : Inst) (j : Fin P.J) {x : Fin P.I → Fin P.R → ℝ}
    (d : FramingDecomp x) (φ : Fin P.I → Fin P.R) (h : 0 < P.rho j d φ) (i : Fin P.I) :
    0 < x i (φ i) := by
  classical
  have hrt : 0 < rhoTil d φ := by
    unfold Inst.rho at h
    split_ifs at h with hm
    · by_contra hc
      push Not at hc
      have h0 : rhoTil d φ = 0 := le_antisymm hc (rhoTil_nonneg d φ)
      rw [h0] at h; simp at h
    · exact absurd h (lt_irrefl 0)
  unfold rhoTil at hrt
  obtain ⟨l, -, hl⟩ := Finset.exists_lt_of_sum_lt (s := univ)
    (f := fun _ => (0:ℝ)) (by simpa using hrt)
  have hc : ∀ i r, φ i = r ↔ d.B l (Fin.castAdd (Itil x) i) r = 1 := by
    by_contra hc
    rw [if_neg hc] at hl
    exact lt_irrefl _ hl
  obtain ⟨hα, -, hBl, hrep⟩ := d.isDecomp
  have hx := hrep (Fin.castAdd (Itil x) i) (φ i)
  simp only [Bmat, Fin.addCases_left] at hx
  rw [hx]
  have hnn : ∀ l', 0 ≤ d.α l' * d.B l' (Fin.castAdd (Itil x) i) (φ i) := by
    intro l'
    refine mul_nonneg (hα l').1.le ?_
    rcases (hBl l').1 (Fin.castAdd (Itil x) i) (φ i) with h | h <;> rw [h] <;> norm_num
  calc (0:ℝ) < d.α l * d.B l (Fin.castAdd (Itil x) i) (φ i) := by
        rw [(hc i (φ i)).1 rfl, mul_one]; exact (hα l).1
    _ ≤ _ := Finset.single_le_sum (fun l' _ => hnn l') (Finset.mem_univ l)

theorem rff_le_opt (P : Inst) (hP : P.Standing) (s : DETSol P) (hs : s ∈ P.DETFeasible)
    (dec : ∀ (t : Fin P.T) (j : Fin P.J), FramingDecomp (s.x t j)) :
    ∀ n, n ≤ P.T → ∀ C, P.rffValue s dec n C ≤ P.optValue n C := by
  classical
  obtain ⟨h10a, h10b, h10c, -, h10e, h10f⟩ := hs
  have hP' := hP
  obtain ⟨-, -, -, -, hlam, hlamsum, hvpos, hv0, -, hQR⟩ := hP'
  have hv := vnn P hP
  intro n
  induction n with
  | zero => intro _ C; simp [Inst.rffValue, Inst.optValue]
  | succ n ih =>
    intro hn C
    have ihn := ih (by omega)
    rw [Inst.rffValue, dif_pos hn, Inst.optValue]
    set t : Fin P.T := ⟨P.T - (n + 1), by omega⟩ with ht
    have hb_nn : ∀ j φ i, 0 ≤ P.buyProb j φ i := by
      intro j φ i
      unfold Inst.buyProb
      refine div_nonneg (hv _ _ _) ?_
      have : 0 ≤ ∑ k, P.vPhi j φ k := Finset.sum_nonneg fun k _ => hv _ _ _
      linarith
    have hb_sum : ∀ j φ, 0 ≤ 1 - ∑ i, P.buyProb j φ i := by
      intro j φ
      unfold Inst.buyProb
      rw [← Finset.sum_div]
      have h0 : 0 ≤ ∑ k, P.vPhi j φ k := Finset.sum_nonneg fun k _ => hv _ _ _
      rw [sub_nonneg, div_le_one (by linarith)]
      linarith
    refine add_le_add ?_ (Finset.sum_le_sum fun j _ => ?_)
    · refine mul_le_mul_of_nonneg_left (ihn C) ?_
      linarith
    · by_cases hlj : P.lam j = 0
      · simp [hlj]
      have hlpos : 0 < P.lam j := lt_of_le_of_ne (hlam j).1 (Ne.symm hlj)
      refine mul_le_mul_of_nonneg_left ?_ (hlam j).1
      set G : (Fin P.I → Fin P.R) → ℝ := fun φ =>
        (∑ i, P.buyProb j φ i *
            (P.p i (φ i) + Inst.finMax (univ.filter (fun k => 0 < C i k))
              (fun k => P.optValue n (P.take C i k) - P.c i j k))) +
        (1 - ∑ i, P.buyProb j φ i) * P.optValue n C with hG
      have L3 := FramingFulfillment.RFF.lemma_3 P hP j (s.x t j) (h10a t j) (h10b t j)
        (h10e t j) (dec t j)
      calc _ ≤ ∑ φ ∈ P.Omega, P.rho j (dec t j) φ * Inst.finMax (P.admissible C) G := by
            refine Finset.sum_le_sum fun φ hφ => ?_
            rcases (rho_nonneg P hP j (dec t j) φ).lt_or_eq with hρ | hρ
            swap
            · rw [← hρ]; simp
            refine mul_le_mul_of_nonneg_left ?_ hρ.le
            have hadm : P.hideOut C φ ∈ P.admissible C := by
              simp only [Inst.admissible, Finset.mem_filter]
              refine ⟨?_, fun i hi => by simp [Inst.hideOut, hi]⟩
              simp only [Inst.Omega, Finset.mem_filter, Finset.mem_univ, true_and] at hφ ⊢
              intro r
              by_cases hr : r = P.noDisp
              · subst hr
                calc _ ≤ (univ : Finset (Fin P.I)).card := Finset.card_le_univ _
                  _ = P.I := by simp
                  _ ≤ _ := hQR
              · refine le_trans (Finset.card_le_card ?_) (hφ r)
                intro i hi
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
                unfold Inst.hideOut at hi
                by_cases h0 : ∑ k, C i k = 0
                · rw [if_pos h0] at hi; exact absurd hi.symm hr
                · rwa [if_neg h0] at hi
            refine le_trans ?_ (le_finMax (f := G) hadm)
            simp only [hG]
            refine add_le_add (Finset.sum_le_sum fun i _ => ?_)
              (mul_le_mul_of_nonneg_left (ihn C) (hb_sum _ _))
            rcases (hb_nn j (P.hideOut C φ) i).lt_or_eq with hb | hb
            swap
            · rw [← hb]; simp
            refine mul_le_mul_of_nonneg_left (add_le_add_right ?_ _) hb.le
            -- the product is displayed and in stock
            have hdisp : P.hideOut C φ i ≠ P.noDisp := by
              intro h
              unfold Inst.buyProb Inst.vPhi at hb
              rw [h, hv0] at hb; simp at hb
            have hstock : ∑ k, C i k ≠ 0 := by
              intro h; apply hdisp; simp [Inst.hideOut, h]
            have hφi : P.hideOut C φ i = φ i := by simp [Inst.hideOut, hstock]
            have hne : (univ.filter (fun k => 0 < C i k)).Nonempty := by
              by_contra hc
              rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hc
              apply hstock
              exact Finset.sum_eq_zero fun k _ => by have := hc (Finset.mem_univ k); omega
            -- the sampled FC distribution sums to one
            have hypos : 0 < ∑ k, s.y t j i k := by
              rw [h10c t j i]
              unfold Inst.thetaX
              refine div_pos (mul_pos hlpos ?_) ?_
              · have hx := x_pos_of_rho_pos P j (dec t j) φ hρ i
                have hvp : 0 < P.v i j (φ i) := hvpos i j (φ i) (by rwa [← hφi])
                calc (0:ℝ) < P.v i j (φ i) * s.x t j i (φ i) := mul_pos hvp hx
                  _ ≤ _ := Finset.single_le_sum (f := fun r => P.v i j r * s.x t j i r)
                      (fun r _ => mul_nonneg (hv _ _ _) (h10e t j i r).1) (Finset.mem_univ _)
              · have : 0 ≤ ∑ l, ∑ r, P.v l j r * s.x t j l r :=
                  Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun r _ =>
                    mul_nonneg (hv _ _ _) (h10e t j l r).1
                linarith
            have hyt_nn : ∀ k, 0 ≤ P.ytil (s.y t j) i k := fun k =>
              div_nonneg (h10f t j i k).1 hypos.le
            have hyt_sum : ∑ k, P.ytil (s.y t j) i k = 1 := by
              unfold Inst.ytil; rw [← Finset.sum_div, div_self hypos.ne']
            calc _ ≤ ∑ k, P.ytil (s.y t j) i k * Inst.finMax (univ.filter (fun k => 0 < C i k))
                  (fun k => P.optValue n (P.take C i k) - P.c i j k) := by
                  refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (hyt_nn k)
                  have hmem : P.fcChoice C j i k ∈ univ.filter (fun k => 0 < C i k) := by
                    simp only [Inst.fcChoice]
                    split_ifs with h1 h2
                    · simpa using h1
                    · exact (Finset.mem_filter.1 (Finset.min'_mem _ _)).1
                  refine le_trans ?_ (le_finMax (f := fun k => P.optValue n (P.take C i k) -
                    P.c i j k) hmem)
                  exact sub_le_sub_right (ihn _) _
              _ = _ := by rw [← Finset.sum_mul, hyt_sum, one_mul]
        _ = _ := by rw [← Finset.sum_mul, L3.1, one_mul]


abbrev Space (P : Inst) := (Fin P.T → Fin P.J → Fin P.I → Fin P.R → ℝ) ×
    (Fin P.T → Fin P.J → Fin P.I → Fin P.K → ℝ)

def feas (P : Inst) : Set (Space P) := {e |
    (∀ t j r, ∑ i, e.1 t j i r ≤ (P.Q r : ℝ)) ∧
    (∀ t j i, ∑ r, e.1 t j i r = 1) ∧
    (∀ t j i, (∑ k, e.2 t j i k) * (1 + ∑ l, ∑ r, P.v l j r * e.1 t j l r) =
        P.lam j * (∑ r, P.v i j r * e.1 t j i r)) ∧
    (∀ i k, ∑ t, ∑ j, e.2 t j i k ≤ (P.C i k : ℝ)) ∧
    (∀ t j i r, 0 ≤ e.1 t j i r ∧ e.1 t j i r ≤ 1) ∧
    (∀ t j i k, 0 ≤ e.2 t j i k ∧ e.2 t j i k ≤ 1)}

lemma feas_closed (P : Inst) : IsClosed (feas P) := by
  simp only [feas, Set.setOf_and, Set.setOf_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_
    (IsClosed.inter ?_ ?_))))
  all_goals
    repeat (first | (apply isClosed_iInter; intro _) | apply IsClosed.inter)
  all_goals
    first
    | exact isClosed_le (by fun_prop) (by fun_prop)
    | exact isClosed_eq (by fun_prop) (by fun_prop)

lemma feas_bdd (P : Inst) : Bornology.IsBounded (feas P) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨1, fun e he => ?_⟩
  obtain ⟨-, -, -, -, h5, h6⟩ := he
  rw [Metric.mem_closedBall, dist_zero_right, norm_prod_le_iff]
  constructor
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun t => ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun r => ?_
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h5 t j i r]
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun t => ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h6 t j i k]

lemma feas_cont (P : Inst) (hv : ∀ i j r, 0 ≤ P.v i j r) :
    ContinuousOn (fun e : Space P => P.detObj ⟨e.1, e.2⟩) (feas P) := by
  have hDpos : ∀ (xx : Fin P.I → Fin P.R → ℝ) (j : Fin P.J), (∀ i r, 0 ≤ xx i r) →
      0 < 1 + ∑ l, ∑ r, P.v l j r * xx l r := by
    intro xx j hx
    have : 0 ≤ ∑ l, ∑ r, P.v l j r * xx l r :=
      Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun r _ => mul_nonneg (hv _ _ _) (hx l r)
    linarith
  simp only [Inst.detObj, Inst.revX]
  refine ContinuousOn.sub ?_ (Continuous.continuousOn (by fun_prop))
  refine continuousOn_finset_sum _ fun t _ => continuousOn_finset_sum _ fun i _ =>
    continuousOn_finset_sum _ fun j _ => ?_
  refine ContinuousOn.div (Continuous.continuousOn (by fun_prop))
    (Continuous.continuousOn (by fun_prop)) fun e he => ?_
  exact (hDpos _ j (fun i r => (he.2.2.2.2.1 t j i r).1)).ne'

lemma feas_ne (P : Inst) (hv0 : ∀ i j, P.v i j P.noDisp = 0) (hQR : P.I ≤ P.Q P.noDisp) :
    (feas P).Nonempty := by
  classical
  refine ⟨(fun _ _ _ r => if r = P.noDisp then 1 else 0, fun _ _ _ _ => 0), ?_⟩
  simp only [feas, Set.mem_setOf_eq]
  refine ⟨fun t j r => ?_, fun t j i => by simp, fun t j i => ?_, fun i k => by simp,
    fun t j i r => by split_ifs <;> norm_num, fun t j i k => by simp⟩
  · by_cases hr : r = P.noDisp
    · simp only [hr, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      exact_mod_cast hQR
    · simp [hr]
  · simp only [Finset.sum_const_zero, zero_mul]
    have : ∑ r, P.v i j r * (if r = P.noDisp then (1:ℝ) else 0) = 0 := by
      simp [hv0]
    rw [this, mul_zero]

lemma feas_cpt (P : Inst) : IsCompact (feas P) :=
  Metric.isCompact_of_isClosed_isBounded (feas_closed P) (feas_bdd P)

theorem exists_DETOpt (P : Inst) (hP : P.Standing) : ∃ s, P.IsDETOpt s := by
  classical
  have hv := vnn P hP
  obtain ⟨-, -, -, -, -, -, -, hv0, -, hQR⟩ := hP
  let S : Set (Space P) := feas P
  have hDpos : ∀ (xx : Fin P.I → Fin P.R → ℝ) (j : Fin P.J), (∀ i r, 0 ≤ xx i r) →
      0 < 1 + ∑ l, ∑ r, P.v l j r * xx l r := by
    intro xx j hx
    have : 0 ≤ ∑ l, ∑ r, P.v l j r * xx l r :=
      Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun r _ => mul_nonneg (hv _ _ _) (hx l r)
    linarith
  have hiff : ∀ s : DETSol P, s ∈ P.DETFeasible ↔ ((s.x, s.y) : Space P) ∈ S := by
    intro s
    simp only [Inst.DETFeasible, Set.mem_setOf_eq, S, feas, Inst.thetaX]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      refine ⟨h1, h2, fun t j i => ?_, h4, h5, h6⟩
      rw [h3 t j i, div_mul_cancel₀ _ (hDpos _ j (fun i r => (h5 t j i r).1)).ne']
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      refine ⟨h1, h2, fun t j i => ?_, h4, h5, h6⟩
      rw [eq_div_iff (hDpos _ j (fun i r => (h5 t j i r).1)).ne', h3 t j i]
  have hclosed : IsClosed S := feas_closed P
  have hbdd : Bornology.IsBounded S := feas_bdd P
  have hcpt : IsCompact S := feas_cpt P
  have hne : S.Nonempty := feas_ne P hv0 hQR
  let f : Space P → ℝ := fun e => P.detObj ⟨e.1, e.2⟩
  have hcont : ContinuousOn f S := feas_cont P hv
  obtain ⟨e, he, hmax⟩ := hcpt.exists_isMaxOn hne hcont
  refine ⟨⟨e.1, e.2⟩, (hiff ⟨e.1, e.2⟩).2 he, fun s' hs' => ?_⟩
  rcases s' with ⟨x', y'⟩
  have h1 : ((x', y') : Space P) ∈ S := (hiff ⟨x', y'⟩).1 hs'
  have h2 : f (x', y') ≤ f e := isMaxOn_iff.1 hmax _ h1
  exact h2


lemma Bmat_nonneg {I R : ℕ} (x : Fin I → Fin R → ℝ) (hx : ∀ i r, 0 ≤ x i r) :
    ∀ n r, 0 ≤ Bmat x n r := by
  intro n r
  refine Fin.addCases (fun i => ?_) (fun k => ?_) n
  · simp [Bmat, hx]
  · simp only [Bmat, Fin.addCases_right]
    exact div_nonneg (sub_nonneg.2 (Nat.le_ceil _)) (Nat.cast_nonneg _)

end RFFAux

open RFFAux

theorem solution (P : Inst) (hP : P.Standing) :
    (∃ M : ℝ, 0 < M ∧ ∃ θ₀ : ℕ, ∀ θ : ℕ, θ₀ ≤ θ →
      (∃ s, (P.scale θ).IsDETOpt s) ∧
      ∀ s, (P.scale θ).IsDETOpt s →
        ∀ dec : ∀ (t : Fin (P.scale θ).T) (j : Fin (P.scale θ).J), FramingDecomp (s.x t j),
          0 ≤ (P.scale θ).JD - (P.scale θ).JRFF s dec ∧
          (P.scale θ).JD - (P.scale θ).JRFF s dec ≤ M * Real.sqrt (θ : ℝ)) ∧
    (0 < (P.scale 1).Jstar →
      ∃ M' : ℝ, ∃ θ₁ : ℕ, ∀ θ : ℕ, θ₁ ≤ θ →
        0 < (P.scale θ).Jstar ∧
        ∀ s, (P.scale θ).IsDETOpt s →
          ∀ dec : ∀ (t : Fin (P.scale θ).T) (j : Fin (P.scale θ).J), FramingDecomp (s.x t j),
            |1 - (P.scale θ).JRFF s dec / (P.scale θ).Jstar| ≤ M' / Real.sqrt (θ : ℝ)) := by
  classical
  have hS : ∀ θ : ℕ, (P.scale θ).Standing := fun θ => hP
  -- RFF is dominated by the optimal policy
  have hRJ : ∀ (θ : ℕ) (s : DETSol (P.scale θ)), (P.scale θ).IsDETOpt s →
      ∀ dec : ∀ (t : Fin (P.scale θ).T) (j : Fin (P.scale θ).J), FramingDecomp (s.x t j),
        (P.scale θ).JRFF s dec ≤ (P.scale θ).Jstar := fun θ s hs dec =>
    rff_le_opt (P.scale θ) (hS θ) s hs.1 dec _ le_rfl _
  have hJD : ∀ θ : ℕ, (P.scale θ).Jstar ≤ (P.scale θ).JD := fun θ =>
    FramingFulfillment.RFF.lemma_5 (P.scale θ) (hS θ)
  -- decompositions exist
  have hdec : ∀ (θ : ℕ) (s : DETSol (P.scale θ)), (P.scale θ).IsDETOpt s →
      Nonempty (∀ (t : Fin (P.scale θ).T) (j : Fin (P.scale θ).J), FramingDecomp (s.x t j)) := by
    intro θ s hs
    obtain ⟨h10a, h10b, -, -, h10e, -⟩ := hs.1
    have : ∀ t j, Nonempty (FramingDecomp (s.x t j)) := by
      intro t j
      obtain ⟨L, α, Bs, h⟩ := FramingFulfillment.RFF.framing_decomposition_exists
        (Qtil (s.x t j)) (Bmat (s.x t j)) (Bmat_nonneg _ fun i r => (h10e t j i r).1)
        (FramingFulfillment.RFF.lemma_2 (P.scale θ) (hS θ) (s.x t j) (h10a t j) (h10b t j)
          (h10e t j)).1
      exact ⟨⟨L, α, Bs, h⟩⟩
    exact ⟨fun t j => (this t j).some⟩
  obtain ⟨M, hM, θ₀, hgap⟩ := FramingFulfillment.RFF.rff_gap_upper P hP
  refine ⟨⟨M, hM, θ₀, fun θ hθ => ⟨exists_DETOpt _ (hS θ), fun s hs dec =>
    ⟨sub_nonneg.2 ((hRJ θ s hs dec).trans (hJD θ)), hgap θ hθ s hs dec⟩⟩⟩, fun hJ1 => ?_⟩
  set a := (P.scale 1).JD with ha_def
  have ha : 0 < a := lt_of_lt_of_le hJ1 (hJD 1)
  refine ⟨2 * M / a, max θ₀ (⌈(2 * M / a) ^ 2⌉₊ + 1), fun θ hθ => ?_⟩
  have hθ0 : θ₀ ≤ θ := le_trans (le_max_left _ _) hθ
  have hθ1 : ⌈(2 * M / a) ^ 2⌉₊ + 1 ≤ θ := le_trans (le_max_right _ _) hθ
  have hθreal : (2 * M / a) ^ 2 < (θ : ℝ) := by
    have h1 : (2 * M / a) ^ 2 ≤ (⌈(2 * M / a) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(2 * M / a) ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ θ := by exact_mod_cast hθ1
    push_cast at h2
    linarith
  set r := Real.sqrt (θ : ℝ) with hr
  have hθnn : (0 : ℝ) ≤ θ := Nat.cast_nonneg _
  have hr2 : r ^ 2 = θ := Real.sq_sqrt hθnn
  have hcpos : 0 < 2 * M / a := div_pos (by linarith) ha
  have hrbig : 2 * M / a < r := by
    rw [hr]; exact Real.lt_sqrt_of_sq_lt hθreal
  have hrpos : 0 < r := lt_trans hcpos hrbig
  have hMr : M * r < a * r ^ 2 / 2 := by
    have : 2 * M < a * r := by
      have := mul_lt_mul_of_pos_left hrbig ha
      rwa [mul_div_cancel₀ _ ha.ne'] at this
    nlinarith
  have hstat : (P.scale θ).JD = a * r ^ 2 := by
    rw [FramingFulfillment.RFF.det_stationary P hP θ, hr2, mul_comm]
  -- lower bound on J* via any RFF policy
  have hlow : ∀ s, (P.scale θ).IsDETOpt s →
      ∀ dec : ∀ (t : Fin (P.scale θ).T) (j : Fin (P.scale θ).J), FramingDecomp (s.x t j),
        a * r ^ 2 / 2 < (P.scale θ).JRFF s dec := by
    intro s hs dec
    have := hgap θ hθ0 s hs dec
    rw [hstat] at this
    linarith
  have hJpos : 0 < (P.scale θ).Jstar := by
    obtain ⟨s, hs⟩ := exists_DETOpt _ (hS θ)
    obtain ⟨dec⟩ := hdec θ s hs
    have := hlow s hs dec
    have := hRJ θ s hs dec
    nlinarith [sq_nonneg r]
  refine ⟨hJpos, fun s hs dec => ?_⟩
  set X := (P.scale θ).Jstar
  set Y := (P.scale θ).JRFF s dec
  have hYX : Y ≤ X := hRJ θ s hs dec
  have hXD : X ≤ a * r ^ 2 := hstat ▸ hJD θ
  have hgap' : a * r ^ 2 - Y ≤ M * r := hstat ▸ hgap θ hθ0 s hs dec
  have hYlow : a * r ^ 2 / 2 < Y := hlow s hs dec
  have hXpos : 0 < X := hJpos
  have heq : 1 - Y / X = (X - Y) / X := by field_simp
  rw [heq, abs_of_nonneg (div_nonneg (by linarith) hXpos.le)]
  have hden : 0 < a * r ^ 2 / 2 := by positivity
  calc (X - Y) / X ≤ (M * r) / (a * r ^ 2 / 2) :=
        div_le_div₀ (by positivity) (by linarith) hden (by linarith)
    _ = 2 * M / a / r := by field_simp
