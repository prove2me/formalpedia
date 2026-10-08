-- Prove2me | solution 1 for DenardoDP.Contraction.theorem3
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T16:27:47.048965+00:00
-- url     : https://prove2.me/submissions/d25dbdc1-d8ea-40b7-a5cd-43532cd5e8ba

/-
Denardo, Contraction mappings in the theory underlying dynamic programming, Theorem 3: under the
contraction and monotonicity assumptions the functional equation `A w = w` has a unique solution,
and it is the optimal return `w = sup_δ v_δ`.

`A` is a contraction of the complete space of bounded functions (the pointwise supremum of the
contractions `h x d`), so Banach's theorem gives the unique fixed point. If `A w = w`, every policy
operator satisfies `H_δ w ≤ w`; by monotonicity the iterates `H_δ^n w` stay below `w` and converge to
the fixed point `v_δ`, so `v_δ ≤ w`. Conversely choosing for each state an action whose return is within
`ε(1 - c)` of `w` gives a policy with `dist w (H_δ w) ≤ ε(1 - c)`, hence `dist w v_δ ≤ ε`
by the a-priori estimate of the contraction `H_δ`. So `w` is the least upper bound of the `v_δ`.
-/
import Mathlib
import Definitions.Def_DenardoDP_Contraction_Model

set_option autoImplicit false

namespace DnLib
open DenardoDP.Contraction

variable {Ω : Type*} {D : Ω → Type*}

theorem dist_apply_le {u v : BFun Ω} (x : Ω) : |u x - v x| ≤ dist u v := by
  have := lp.norm_apply_le_norm (by simp) (u - v) x
  simpa [dist_eq_norm, Real.norm_eq_abs] using this

theorem dist_le_of_forall {u v : BFun Ω} {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, |u x - v x| ≤ C) :
    dist u v ≤ C := by
  rw [dist_eq_norm]
  refine lp.norm_le_of_forall_le hC (fun x => ?_)
  simpa [Real.norm_eq_abs] using h x

theorem max_op_contr {h : (x : Ω) → D x → BFun Ω → ℝ} {A : BFun Ω → BFun Ω} {c : ℝ}
    (hA : IsMaxOperator h A) (hc : ContractionAssumption h c) (u v : BFun Ω) :
    dist (A u) (A v) ≤ c * dist u v := by
  obtain ⟨hc0, _, hcon⟩ := hc
  refine dist_le_of_forall (by positivity) (fun x => ?_)
  have key : ∀ u v : BFun Ω, A u x ≤ A v x + c * dist u v := by
    intro u v
    refine ((isLUB_le_iff (hA u x)).2 ?_)
    intro y hy
    obtain ⟨d, rfl⟩ := hy
    have h1 := hcon u v x d
    have h2 : h x d v ≤ A v x := (hA v x).1 ⟨d, rfl⟩
    have := (abs_le.1 h1).2
    linarith
  have a1 := key u v
  have a2 := key v u
  rw [dist_comm v u] at a2
  rw [abs_le]
  constructor <;> linarith

theorem policy_contr {h : (x : Ω) → D x → BFun Ω → ℝ} {H : ((x : Ω) → D x) → BFun Ω → BFun Ω}
    {c : ℝ} (hH : IsPolicyOperator h H) (hc : ContractionAssumption h c) (δ : (x : Ω) → D x)
    (u v : BFun Ω) : dist (H δ u) (H δ v) ≤ c * dist u v := by
  obtain ⟨hc0, _, hcon⟩ := hc
  refine dist_le_of_forall (by positivity) (fun x => ?_)
  rw [hH, hH]
  exact hcon u v x (δ x)

theorem denardo_core {h : (x : Ω) → D x → BFun Ω → ℝ} {H : ((x : Ω) → D x) → BFun Ω → BFun Ω}
    {A : BFun Ω → BFun Ω} {c : ℝ} {v : ((x : Ω) → D x) → BFun Ω}
    (hH : IsPolicyOperator h H) (hA : IsMaxOperator h A) (hc : ContractionAssumption h c)
    (hmono : MonotonicityAssumption H) (hv : ∀ δ, H δ (v δ) = v δ) :
    (∃! w : BFun Ω, A w = w) ∧ ∀ w : BFun Ω, A w = w → IsOptimalReturn v w := by
  have hc' := hc
  obtain ⟨hc0, hc1, _⟩ := hc
  set K : NNReal := ⟨c, hc0⟩ with hKdef
  have hKc : (K : ℝ) = c := rfl
  have hKlt : K < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_one, hKc]; exact hc1
  have hKA : ContractingWith K A :=
    ⟨hKlt, LipschitzWith.of_dist_le_mul (fun u w => by rw [hKc]; exact max_op_contr hA hc' u w)⟩
  have hKH : ∀ δ, ContractingWith K (H δ) := fun δ =>
    ⟨hKlt, LipschitzWith.of_dist_le_mul (fun u w => by rw [hKc]; exact policy_contr hH hc' δ u w)⟩
  refine ⟨⟨ContractingWith.fixedPoint A hKA, hKA.fixedPoint_isFixedPt,
    fun y hy => hKA.fixedPoint_unique hy⟩, ?_⟩
  intro w hw
  have h1c : (0 : ℝ) < 1 - c := by linarith
  -- every policy return is below `w`
  have hup : ∀ δ x, v δ x ≤ w x := by
    intro δ x
    have hHw : ∀ y, H δ w y ≤ w y := by
      intro y
      rw [hH]
      calc h y (δ y) w ≤ A w y := (hA w y).1 ⟨δ y, rfl⟩
        _ = w y := by rw [hw]
    have hit : ∀ n : ℕ, PLe ((H δ)^[n] w) w := by
      intro n
      induction n with
      | zero => intro y; exact le_rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        intro y
        exact (hmono δ w _ ih y).trans (hHw y)
    have hfix : ContractingWith.fixedPoint (H δ) (hKH δ) = v δ :=
      (ContractingWith.fixedPoint_unique (hKH δ) (hv δ)).symm
    have hT := ContractingWith.tendsto_iterate_fixedPoint (hKH δ) w
    rw [hfix] at hT
    by_contra hlt
    push Not at hlt
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hT (v δ x - w x) (by linarith)
    have h2 := hN N le_rfl
    have h3 := dist_apply_le (u := (H δ)^[N] w) (v := v δ) x
    have h4 := hit N x
    have h5 := abs_le.1 h3
    have h6 : dist ((H δ)^[N] w) (v δ) < v δ x - w x := h2
    linarith [h5.1, h5.2]
  -- near-optimal policies
  have hlow : ∀ ε : ℝ, 0 < ε → ∃ δ : (x : Ω) → D x, ∀ x, w x - ε ≤ v δ x := by
    intro ε hε
    set ε' : ℝ := ε * (1 - c) with hε'
    have hε'pos : 0 < ε' := by positivity
    have hex : ∀ x, ∃ d : D x, w x - ε' < h x d w := by
      intro x
      have hl : w x - ε' < w x := by linarith
      have hlub : IsLUB (Set.range fun d : D x => h x d w) (w x) := by
        have := hA w x
        rwa [hw] at this
      obtain ⟨b, ⟨d, rfl⟩, hb⟩ := hlub.exists_between hl
      exact ⟨d, hb.1⟩
    choose δ hδ using hex
    refine ⟨δ, fun x => ?_⟩
    have hHw : dist w (H δ w) ≤ ε' := by
      refine dist_le_of_forall hε'pos.le (fun y => ?_)
      rw [hH]
      have h1 : h y (δ y) w ≤ A w y := (hA w y).1 ⟨δ y, rfl⟩
      rw [hw] at h1
      have := hδ y
      rw [abs_le]
      constructor <;> linarith
    have hfixp : Function.IsFixedPt (H δ) (v δ) := hv δ
    have hd := ContractingWith.dist_le_of_fixedPoint (hKH δ) w hfixp
    rw [hKc] at hd
    have hd2 : dist w (v δ) ≤ ε := by
      calc dist w (v δ) ≤ dist w (H δ w) / (1 - c) := hd
        _ ≤ ε' / (1 - c) := by gcongr
        _ = ε := by rw [hε']; field_simp
    have := dist_apply_le (u := w) (v := v δ) x
    have := abs_le.1 (this.trans hd2)
    linarith [this.1, this.2]
  intro x
  refine ⟨?_, ?_⟩
  · rintro _ ⟨δ, rfl⟩
    exact hup δ x
  · intro b hb
    by_contra hlt
    push Not at hlt
    obtain ⟨δ, hδ⟩ := hlow ((w x - b) / 2) (by linarith)
    have := hb ⟨δ, rfl⟩
    linarith [hδ x]

end DnLib

open DenardoDP.Contraction in
theorem solution {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → BFun Ω → ℝ)
    (H : ((x : Ω) → D x) → BFun Ω → BFun Ω)
    (A : BFun Ω → BFun Ω) (c : ℝ)
    (v : ((x : Ω) → D x) → BFun Ω)
    (hH : IsPolicyOperator h H) (hA : IsMaxOperator h A)
    (hc : ContractionAssumption h c) (hmono : MonotonicityAssumption H)
    (hv : ∀ δ, H δ (v δ) = v δ) :
    (∃! w : BFun Ω, A w = w) ∧
      ∀ w : BFun Ω, A w = w → IsOptimalReturn v w :=
  DnLib.denardo_core hH hA hc hmono hv
