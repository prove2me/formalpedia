-- Prove2me | solution 1 for ConvexRMDP.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T23:17:16.407385+00:00
-- url     : https://prove2.me/submissions/2c143983-ae71-4092-a40d-b70943ee6fbe

import Definitions.Def_ConvexRMDP_RMDP_regOp
import Definitions.Def_ConvexRMDP_RMDP_tOp
import Theorems.Thm_ConvexRMDP_lemma_3_1
import Theorems.Thm_ConvexRMDP_proposition_4_1_item_1
import Theorems.Thm_ConvexRMDP_change_of_variables
import Theorems.Thm_ConvexRMDP_fixed_point_nonneg
import Theorems.Thm_ConvexRMDP_feasible_set_convex

namespace _M7Thm41Helper

open ConvexRMDP

lemma feasible_set_isClosed {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) :
    IsClosed {x : S → ℝ | ∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s} := by
  let _ := hb
  have hcard_pos : 0 < (Fintype.card A : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have homega_pos : ∀ s a, 0 < M.omega b s a := fun s a => by
    unfold RMDP.omega expB
    exact div_pos (Real.exp_pos _) hcard_pos
  let S1 : Set (S → ℝ) := ⋂ s : S, {x : S → ℝ | 1 ≤ x s}
  let S2 : Set (S → ℝ) :=
    ⋂ (s : S) (P : ∀ a : A, M.U s a),
      {x : S → ℝ | x s ≤ ∑ a : A, M.omega b s a * ∏ s' : S, x s' ^ (M.γ * (P a).1 s')}
  have hset_eq : {x : S → ℝ | ∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s} = S1 ∩ S2 := by
    ext x
    simp only [Set.mem_inter_iff, S1, S2, Set.mem_iInter]
    constructor
    · intro hx
      refine ⟨fun s => (hx s).1, fun s P => ?_⟩
      refine ((hx s).2).trans ?_
      unfold RMDP.tOp
      refine Finset.sum_le_sum fun a _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ (homega_pos s a).le
      have hbdd : BddBelow ((fun p : S → ℝ => ∏ s', x s' ^ (M.γ * p s')) '' M.U s a) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨p, -, rfl⟩
        exact Finset.prod_nonneg fun s' _ => Real.rpow_nonneg (zero_le_one.trans (hx s').1) _
      exact csInf_le hbdd ⟨(P a).1, (P a).2, rfl⟩
    · rintro ⟨hx1, hx2⟩ s
      refine ⟨hx1 s, ?_⟩
      by_contra hnot
      push Not at hnot
      let ε : ℝ := (x s - M.tOp b x s) / 2
      have hε : 0 < ε := by dsimp [ε]; linarith
      have hex_p : ∀ a : A, ∃ p ∈ M.U s a,
          (∏ s', x s' ^ (M.γ * p s')) <
            sInf ((fun q : S → ℝ => ∏ s', x s' ^ (M.γ * q s')) '' M.U s a) +
              ε / ((Fintype.card A : ℝ) * M.omega b s a) := by
        intro a
        have hδ : 0 < ε / ((Fintype.card A : ℝ) * M.omega b s a) :=
          div_pos hε (mul_pos hcard_pos (homega_pos s a))
        obtain ⟨_, ⟨p, hpU, rfl⟩, hlt⟩ :=
          exists_lt_of_csInf_lt ((M.U_nonempty s a).image _) (lt_add_of_pos_right _ hδ)
        exact ⟨p, hpU, hlt⟩
      choose p hpU hp_lt using hex_p
      let P : ∀ a : A, M.U s a := fun a => ⟨p a, hpU a⟩
      have hP_le : x s ≤ ∑ a : A, M.omega b s a * ∏ s' : S, x s' ^ (M.γ * (P a).1 s') :=
        hx2 s P
      have hsum_le : ∑ a : A, M.omega b s a * ∏ s' : S, x s' ^ (M.γ * (P a).1 s') ≤
          M.tOp b x s + ε := by
        have hterm_le : ∀ a : A,
            M.omega b s a * (∏ s' : S, x s' ^ (M.γ * (P a).1 s')) ≤
              M.omega b s a * sInf ((fun q : S → ℝ => ∏ s', x s' ^ (M.γ * q s')) '' M.U s a) +
                ε / (Fintype.card A : ℝ) := by
          intro a
          have hm := mul_lt_mul_of_pos_left (hp_lt a) (homega_pos s a)
          have hrhs : M.omega b s a *
              (sInf ((fun q : S → ℝ => ∏ s', x s' ^ (M.γ * q s')) '' M.U s a) +
                ε / ((Fintype.card A : ℝ) * M.omega b s a)) =
              M.omega b s a * sInf ((fun q : S → ℝ => ∏ s', x s' ^ (M.γ * q s')) '' M.U s a) +
                ε / (Fintype.card A : ℝ) := by
            have hom_ne : M.omega b s a ≠ 0 := (homega_pos s a).ne'
            have hc_ne : (Fintype.card A : ℝ) ≠ 0 := hcard_pos.ne'
            field_simp [hom_ne, hc_ne]
          rw [hrhs] at hm
          exact hm.le
        calc ∑ a : A, M.omega b s a * ∏ s' : S, x s' ^ (M.γ * (P a).1 s')
            ≤ ∑ a : A, (M.omega b s a *
                  sInf ((fun q : S → ℝ => ∏ s', x s' ^ (M.γ * q s')) '' M.U s a) +
                ε / (Fintype.card A : ℝ)) :=
              Finset.sum_le_sum fun a _ => hterm_le a
          _ = M.tOp b x s + ∑ _ : A, ε / (Fintype.card A : ℝ) := by
              rw [Finset.sum_add_distrib]; rfl
          _ = M.tOp b x s + ε := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
                mul_div_cancel₀ _ hcard_pos.ne']
      dsimp [ε] at hsum_le
      linarith
  rw [hset_eq]
  have hS1 : IsClosed S1 :=
    isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  have hS2 : IsClosed S2 := by
    refine isClosed_iInter fun s => isClosed_iInter fun P => ?_
    refine isClosed_le (continuous_apply s) ?_
    refine continuous_finsetSum Finset.univ fun a _ => ?_
    refine continuous_const.mul ?_
    refine continuous_finsetProd Finset.univ fun s' _ => ?_
    have hexp_nn : 0 ≤ M.γ * (P a).1 s' :=
      mul_nonneg M.γ_pos.le ((M.U_subset s a (P a).2).1 s')
    exact (continuous_apply s').rpow_const fun _ => Or.inr hexp_nn
  exact hS1.inter hS2

end _M7Thm41Helper

open ConvexRMDP

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) :
    (∃! v : S → ℝ, M.regOp b v = v) ∧
      ∀ vt : S → ℝ, M.regOp b vt = vt →
        (IsGreatest ((fun v : S → ℝ => ∑ s, expB b (v s)) '' {v | v ≤ M.regOp b v})
            (∑ s, expB b (vt s)) ∧
          ∀ v : S → ℝ, v ≤ M.regOp b v → ∑ s, expB b (v s) = ∑ s, expB b (vt s) → v = vt) ∧
        (∃ xt : S → ℝ, (∀ s, 1 ≤ xt s ∧ xt s ≤ M.tOp b xt s) ∧
          (∀ x : S → ℝ, (∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s) → ∑ s, x s ≤ ∑ s, xt s) ∧
          (∀ x : S → ℝ, (∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s) → ∑ s, x s = ∑ s, xt s → x = xt) ∧
          vt = fun s => logB b (xt s)) ∧
        Convex ℝ {x : S → ℝ | ∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s} ∧
        IsClosed {x : S → ℝ | ∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s} := by
  obtain ⟨hmono, hcontr⟩ := proposition_4_1_item_1 M b hb
  let vStar : S → ℝ := ContractingWith.fixedPoint (M.regOp b) hcontr
  have hvStar : M.regOp b vStar = vStar := hcontr.fixedPoint_isFixedPt
  refine ⟨⟨vStar, hvStar, fun y hy => hcontr.fixedPoint_unique hy⟩, fun vt hvt => ?_⟩
  let g : (S → ℝ) → ℝ := fun v => ∑ s, expB b (v s)
  have hg_mono : Monotone g := by
    intro u w huw
    refine Finset.sum_le_sum fun s _ => ?_
    unfold expB
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (huw s) hb.le)
  have hg_strict : StrictMono g := by
    intro u w huw
    have hex_lt : ∃ s₀ : S, u s₀ < w s₀ := by
      by_contra hall
      push Not at hall
      exact huw.ne (funext fun s => le_antisymm (huw.le s) (hall s))
    obtain ⟨s₀, hs₀⟩ := hex_lt
    refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s₀, Finset.mem_univ s₀, ?_⟩
    · unfold expB
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (huw.le s) hb.le)
    · unfold expB
      exact Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hs₀ hb)
  have h31 := lemma_3_1 (M.regOp b) ⟨M.γ, M.γ_pos.le⟩ hmono hcontr g hg_mono vt hvt
  have hopt_v := h31.2.1
  have huniq_v := (h31.2.2 hg_strict).2
  refine ⟨⟨hopt_v, huniq_v⟩, ?_, feasible_set_convex M b hb,
    _M7Thm41Helper.feasible_set_isClosed M b hb⟩
  let xt : S → ℝ := fun s => expB b (vt s)
  have hvt_nn : 0 ≤ vt := (fixed_point_nonneg M b hb vt hvt).1
  have hcov := (change_of_variables M b hb).1
  have hxt_feas : ∀ s, 1 ≤ xt s ∧ xt s ≤ M.tOp b xt s := by
    have hxt_tOp : xt ≤ M.tOp b xt := (hcov vt).mp hvt.symm.le
    intro s
    refine ⟨?_, hxt_tOp s⟩
    dsimp [xt]
    unfold expB
    exact Real.one_le_exp (mul_nonneg hb.le (hvt_nn s))
  have hvt_eq : vt = fun s => logB b (xt s) := by
    ext s
    dsimp [xt]
    unfold logB expB
    rw [Real.log_exp]
    exact (mul_div_cancel_left₀ (vt s) hb.ne').symm
  refine ⟨xt, hxt_feas, ?_, ?_, hvt_eq⟩
  · intro x hx
    let vx : S → ℝ := fun s => logB b (x s)
    have hx_pos : ∀ s, 0 < x s := fun s => lt_of_lt_of_le one_pos (hx s).1
    have hexp_vx : (fun s => expB b (vx s)) = x := by
      ext s
      dsimp [vx]
      unfold expB logB
      rw [mul_div_cancel₀ _ hb.ne']
      exact Real.exp_log (hx_pos s)
    have hvx_feas : vx ≤ M.regOp b vx := by
      rw [hcov vx, hexp_vx]
      exact fun s => (hx s).2
    have hg_le : g vx ≤ g vt := hopt_v.2 ⟨vx, hvx_feas, rfl⟩
    simpa [g, hexp_vx, xt] using hg_le
  · intro x hx hsum_eq
    let vx : S → ℝ := fun s => logB b (x s)
    have hx_pos : ∀ s, 0 < x s := fun s => lt_of_lt_of_le one_pos (hx s).1
    have hexp_vx : (fun s => expB b (vx s)) = x := by
      ext s
      dsimp [vx]
      unfold expB logB
      rw [mul_div_cancel₀ _ hb.ne']
      exact Real.exp_log (hx_pos s)
    have hvx_feas : vx ≤ M.regOp b vx := by
      rw [hcov vx, hexp_vx]
      exact fun s => (hx s).2
    have hg_eq : g vx = g vt := by
      simpa [g, hexp_vx, xt] using hsum_eq
    have hvx_eq : vx = vt := huniq_v vx hvx_feas hg_eq
    calc x = fun s => expB b (vx s) := hexp_vx.symm
      _ = xt := by rw [hvx_eq]
