-- Prove2me | solution 1 for DriftVarCtrl.FixedLB.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T10:01:29.445415+00:00
-- url     : https://prove2.me/submissions/54002372-3cc9-4317-b53a-fd8532f6db2b

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Theorems.Thm_DriftVarCtrl_FixedLB_lemma_12_analytic

open Set Filter Topology

namespace DriftVarCtrl.FixedLB

/-! ### Basic constants -/

lemma t1_mu_pos (p : Params) (c : Ctrl) : 0 < p.mu c := by
  cases c
  · exact p.hμ₁
  · exact p.hμ₂

lemma t1_sig_pos (p : Params) (c : Ctrl) : 0 < p.sig c := by
  cases c
  · exact p.hσ₁
  · exact p.hσ₂

lemma t1_v_pos (p : Params) (c : Ctrl) : 0 < v p c := by
  unfold v
  have := t1_mu_pos p c
  have := t1_sig_pos p c
  positivity

/-- The rest point `-hᵢ/μᵢ` of the derivative flow of control `i`. -/
noncomputable def t1A (p : Params) (c : Ctrl) : ℝ := -p.cost c / p.mu c

/-- The switching level `c*` of `V'`: the two controls are equally good when `V' = c*`. -/
noncomputable def t1cs (p : Params) : ℝ :=
  (v p .two * t1A p .two - v p .one * t1A p .one) / (v p .two - v p .one)

lemma t1_mu_eq (p : Params) (c : Ctrl) : p.mu c = p.sig c ^ 2 * v p c / 2 := by
  unfold v
  have := t1_sig_pos p c
  field_simp

lemma t1_cost_eq (p : Params) (c : Ctrl) : p.cost c = -(p.mu c) * t1A p c := by
  unfold t1A
  have := t1_mu_pos p c
  field_simp

lemma t1_cs_eq (p : Params) (hv : v p .one < v p .two) :
    t1cs p * (v p .two - v p .one) = v p .two * t1A p .two - v p .one * t1A p .one := by
  unfold t1cs
  have : v p .two - v p .one ≠ 0 := sub_ne_zero.mpr hv.ne'
  field_simp

lemma t1_other_ne (c : Ctrl) : c.other ≠ c := by cases c <;> simp [Ctrl.other]

lemma t1_other_other (c : Ctrl) : c.other.other = c := by cases c <;> rfl

lemma t1_eq_other (c d : Ctrl) (h : d ≠ c) : d = c.other := by
  cases c <;> cases d <;> simp_all [Ctrl.other]

lemma t1_ident (p : Params) (hv : v p .one < v p .two) (c : Ctrl) :
    v p c * (t1cs p - t1A p c) = v p c.other * (t1cs p - t1A p c.other) := by
  have h := t1_cs_eq p hv
  cases c
  · simp only [Ctrl.other]; linear_combination (-1 : ℝ) * h
  · simp only [Ctrl.other]; linear_combination h

/-- `Q_d` along a control-`c` derivative trajectory, for `d ≠ c`. -/
lemma t1_Q (p : Params) (hv : v p .one < v p .two) (c d : Ctrl) (hdc : d ≠ c) (g : ℝ) :
    p.cost d + p.mu d * g + p.sig d ^ 2 / 2 * (-(v p c) * (g - t1A p c)) =
      p.sig d ^ 2 / 2 * ((v p d - v p c) * (g - t1cs p)) := by
  have hd := t1_eq_other c d hdc
  subst hd
  have hid := t1_ident p hv c
  have hmu := t1_mu_eq p c.other
  have hcost := t1_cost_eq p c.other
  linear_combination hcost + (g - t1A p c.other) * hmu - (p.sig c.other ^ 2 / 2) * hid

lemma t1_Q_self (p : Params) (c : Ctrl) (g : ℝ) :
    p.cost c + p.mu c * g + p.sig c ^ 2 / 2 * (-(v p c) * (g - t1A p c)) = 0 := by
  have hmu := t1_mu_eq p c
  have hcost := t1_cost_eq p c
  linear_combination hcost + (g - t1A p c) * hmu

/-! ### Explicit trajectories -/

/-- Derivative trajectory of control `c` through `γ` at `x₀`. -/
noncomputable def gT (p : Params) (c : Ctrl) (x₀ γ x : ℝ) : ℝ :=
  t1A p c + (γ - t1A p c) * Real.exp (-(v p c) * (x - x₀))

noncomputable def gT' (p : Params) (c : Ctrl) (x₀ γ x : ℝ) : ℝ :=
  -(v p c) * ((γ - t1A p c) * Real.exp (-(v p c) * (x - x₀)))

noncomputable def GT (p : Params) (c : Ctrl) (x₀ γ x : ℝ) : ℝ :=
  t1A p c * x - (γ - t1A p c) / v p c * Real.exp (-(v p c) * (x - x₀))

lemma t1_hasDerivAt_exp (p : Params) (c : Ctrl) (x₀ x : ℝ) :
    HasDerivAt (fun x => Real.exp (-(v p c) * (x - x₀)))
      (Real.exp (-(v p c) * (x - x₀)) * (-(v p c) * 1)) x :=
  (((hasDerivAt_id x).sub_const x₀).const_mul (-(v p c))).exp

lemma t1_hasDerivAt_GT (p : Params) (c : Ctrl) (x₀ γ x : ℝ) :
    HasDerivAt (GT p c x₀ γ) (gT p c x₀ γ x) x := by
  have h := ((hasDerivAt_id' x).const_mul (t1A p c)).sub
    ((t1_hasDerivAt_exp p c x₀ x).const_mul ((γ - t1A p c) / v p c))
  have hv0 : v p c ≠ 0 := (t1_v_pos p c).ne'
  refine h.congr_deriv ?_
  simp only [gT]; field_simp; ring

lemma t1_hasDerivAt_gT (p : Params) (c : Ctrl) (x₀ γ x : ℝ) :
    HasDerivAt (gT p c x₀ γ) (gT' p c x₀ γ x) x := by
  have h := ((t1_hasDerivAt_exp p c x₀ x).const_mul (γ - t1A p c)).const_add (t1A p c)
  refine h.congr_deriv ?_
  simp only [gT']; ring

lemma t1_continuous_gT' (p : Params) (c : Ctrl) (x₀ γ : ℝ) : Continuous (gT' p c x₀ γ) := by
  unfold gT'; fun_prop

lemma t1_continuous_gT (p : Params) (c : Ctrl) (x₀ γ : ℝ) : Continuous (gT p c x₀ γ) := by
  unfold gT; fun_prop

lemma t1_gT'_eq (p : Params) (c : Ctrl) (x₀ γ x : ℝ) :
    gT' p c x₀ γ x = -(v p c) * (gT p c x₀ γ x - t1A p c) := by
  simp only [gT', gT]; ring

lemma t1_Q_gT_self (p : Params) (c : Ctrl) (x₀ γ x : ℝ) :
    p.cost c + p.mu c * gT p c x₀ γ x + p.sig c ^ 2 / 2 * gT' p c x₀ γ x = 0 := by
  rw [t1_gT'_eq]; exact t1_Q_self p c _

lemma t1_Q_gT_other (p : Params) (hv : v p .one < v p .two) (c d : Ctrl) (hdc : d ≠ c)
    (x₀ γ x : ℝ) :
    p.cost d + p.mu d * gT p c x₀ γ x + p.sig d ^ 2 / 2 * gT' p c x₀ γ x =
      p.sig d ^ 2 / 2 * ((v p d - v p c) * (gT p c x₀ γ x - t1cs p)) := by
  rw [t1_gT'_eq]; exact t1_Q p hv c d hdc _

/-! ### Supersolution packages -/

/-- `Q_c(x) = h_c + μ_c g(x) + σ_c²/2 g'(x)`. -/
noncomputable def t1Q (p : Params) (g g' : ℝ → ℝ) (c : Ctrl) (x : ℝ) : ℝ :=
  p.cost c + p.mu c * g x + p.sig c ^ 2 / 2 * g' x

def t1Good (p : Params) (π : IntervalPolicy p) (V g g' : ℝ → ℝ) : Prop :=
  (∀ x, HasDerivAt V (g x) x) ∧ (∀ x, HasDerivAt g (g' x) x) ∧ Continuous g' ∧
  V 0 = 0 ∧ V p.U = p.M ∧
  (∀ (j : Fin π.k) (x : ℝ), x ∈ Ioo (π.S j.castSucc) (π.S j.succ) →
      t1Q p g g' (π.ctrl j) x = 0) ∧
  (∀ x ∈ Ioo 0 p.U, ∀ c, 0 ≤ t1Q p g g' c x)

def t1Strict (p : Params) (g g' : ℝ → ℝ) : Prop :=
  ∃ (T : ℝ) (c0 : Ctrl), ∀ x ∈ Ioo 0 p.U,
    (x < T → 0 < t1Q p g g' c0.other x) ∧ (T < x → 0 < t1Q p g g' c0 x)

lemma t1Good.derivs {p : Params} {π : IntervalPolicy p} {V g g' : ℝ → ℝ}
    (h : t1Good p π V g g') : deriv V = g ∧ deriv (deriv V) = g' ∧ ContDiff ℝ 2 V := by
  obtain ⟨h1, h2, hc, -⟩ := h
  have hd : deriv V = g := funext fun x => (h1 x).deriv
  have hd2 : deriv g = g' := funext fun x => (h2 x).deriv
  refine ⟨hd, by rw [hd, hd2], ?_⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (h1 x).differentiableAt, by simp, ?_⟩
  rw [hd, contDiff_one_iff_deriv, hd2]
  exact ⟨fun x => (h2 x).differentiableAt, hc⟩

lemma t1Good.isValue {p : Params} {π : IntervalPolicy p} {V g g' : ℝ → ℝ}
    (h : t1Good p π V g g') : IsValue p π V := by
  obtain ⟨hd, hd2, hC⟩ := h.derivs
  obtain ⟨-, -, -, h0, hU, hode, -⟩ := h
  refine ⟨(hC.of_le (by norm_num)).contDiffOn, h0, hU, fun j x hx => ⟨hC.contDiffAt, ?_⟩⟩
  rw [hd2, hd]
  exact hode j x hx

lemma t1Good.le {p : Params} {π : IntervalPolicy p} {V g g' : ℝ → ℝ}
    (h : t1Good p π V g g') (π' : IntervalPolicy p) (W : ℝ → ℝ) (hW : IsValue p π' W) :
    ∀ x ∈ Icc 0 p.U, V x ≤ W x := by
  obtain ⟨hd, hd2, hC⟩ := h.derivs
  obtain ⟨-, -, -, h0, hU, -, hhjb⟩ := h
  refine lemma_12_analytic p V ∅ (hC.of_le (by norm_num)).contDiffOn
    (fun x _ _ => hC.contDiffAt) h0 hU (fun x hx _ c => ?_) π' W hW
  rw [hd2, hd]
  exact hhjb x hx c

/-- Uniqueness structure: a value that coincides with a strict supersolution forces `k ≤ 2`. -/
lemma t1_k_le_two {p : Params} {π0 : IntervalPolicy p} {V g g' : ℝ → ℝ}
    (h : t1Good p π0 V g g') (hs : t1Strict p g g') (π : IntervalPolicy p) (W : ℝ → ℝ)
    (hW : IsValue p π W) (heq : ∀ x ∈ Icc 0 p.U, W x = V x) : π.k ≤ 2 := by
  obtain ⟨hd, hd2, -⟩ := h.derivs
  obtain ⟨T, c0, hT⟩ := hs
  obtain ⟨-, -, -, hode⟩ := hW
  have hmono := π.S_strictMono
  have hpiece : ∀ (j : Fin π.k) (x : ℝ), x ∈ Ioo (π.S j.castSucc) (π.S j.succ) →
      x ∈ Ioo 0 p.U ∧ t1Q p g g' (π.ctrl j) x = 0 := by
    intro j x hx
    have hx0 : x ∈ Ioo 0 p.U := by
      constructor
      · have : π.S 0 ≤ π.S j.castSucc := hmono.monotone (Fin.zero_le _)
        rw [π.S_zero] at this; linarith [hx.1]
      · have : π.S j.succ ≤ π.S (Fin.last π.k) := hmono.monotone (Fin.le_last _)
        rw [π.S_last] at this; linarith [hx.2]
    refine ⟨hx0, ?_⟩
    obtain ⟨-, hW2⟩ := hode j x hx
    have hev : W =ᶠ[𝓝 x] V := by
      filter_upwards [isOpen_Ioo.mem_nhds hx0] with y hy
      exact heq y (Ioo_subset_Icc_self hy)
    rw [hev.deriv_eq, hev.deriv.deriv_eq, hd2, hd] at hW2
    exact hW2
  -- a control-`c0.other` piece lies right of `T`; a control-`c0` piece lies left of `T`
  have hright : ∀ j : Fin π.k, π.ctrl j = c0.other → T ≤ π.S j.castSucc := by
    intro j hj
    by_contra hcon
    push Not at hcon
    have hlt : π.S j.castSucc < π.S j.succ := hmono (Fin.castSucc_lt_succ)
    set x := (π.S j.castSucc + min (π.S j.succ) T) / 2
    have hm : π.S j.castSucc < min (π.S j.succ) T := lt_min hlt hcon
    have hx : x ∈ Ioo (π.S j.castSucc) (π.S j.succ) :=
      ⟨by simp only [x]; linarith, by simp only [x]; linarith [min_le_left (π.S j.succ) T]⟩
    have hxT : x < T := by simp only [x]; linarith [min_le_right (π.S j.succ) T]
    obtain ⟨hx0, hQ⟩ := hpiece j x hx
    have := (hT x hx0).1 hxT
    rw [← hj, hQ] at this
    exact lt_irrefl _ this
  have hleft : ∀ j : Fin π.k, π.ctrl j = c0 → π.S j.succ ≤ T := by
    intro j hj
    by_contra hcon
    push Not at hcon
    have hlt : π.S j.castSucc < π.S j.succ := hmono (Fin.castSucc_lt_succ)
    set x := (max (π.S j.castSucc) T + π.S j.succ) / 2
    have hm : max (π.S j.castSucc) T < π.S j.succ := max_lt hlt hcon
    have hx : x ∈ Ioo (π.S j.castSucc) (π.S j.succ) :=
      ⟨by simp only [x]; linarith [le_max_left (π.S j.castSucc) T], by simp only [x]; linarith⟩
    have hxT : T < x := by simp only [x]; linarith [le_max_right (π.S j.castSucc) T]
    obtain ⟨hx0, hQ⟩ := hpiece j x hx
    have := (hT x hx0).2 hxT
    rw [← hj, hQ] at this
    exact lt_irrefl _ this
  by_contra hk
  push Not at hk
  have h01 := π.alt 0 (by omega)
  have h12 := π.alt 1 (by omega)
  have hc : ∀ d : Ctrl, d = c0 ∨ d = c0.other := by
    intro d; by_cases hd : d = c0
    · exact Or.inl hd
    · exact Or.inr (t1_eq_other c0 d hd)
  rcases hc (π.ctrl ⟨1, by omega⟩) with h1 | h1
  · have h0 : π.ctrl ⟨0, by omega⟩ = c0.other := by
      rcases hc (π.ctrl ⟨0, by omega⟩) with h0 | h0
      · exact absurd (h0.trans h1.symm) h01
      · exact h0
    have a := hright _ h0
    have b := hleft _ h1
    have : π.S (Fin.castSucc (⟨0, by omega⟩ : Fin π.k)) < π.S (Fin.succ (⟨1, by omega⟩ : Fin π.k)) :=
      hmono (by simp [Fin.lt_def])
    linarith
  · have h2 : π.ctrl ⟨2, by omega⟩ = c0 := by
      rcases hc (π.ctrl ⟨2, by omega⟩) with h2 | h2
      · exact h2
      · exact absurd (h1.trans h2.symm) h12
    have a := hright _ h1
    have b := hleft _ h2
    have : π.S (Fin.castSucc (⟨1, by omega⟩ : Fin π.k)) < π.S (Fin.succ (⟨2, by omega⟩ : Fin π.k)) :=
      hmono (by simp [Fin.lt_def])
    linarith

/-! ### Static policies -/

lemma t1_static_good (p : Params) (hv : v p .one < v p .two) (c : Ctrl) (x₀ γ : ℝ)
    (hval : GT p c x₀ γ p.U - GT p c x₀ γ 0 = p.M)
    (hhjb : ∀ x ∈ Ioo 0 p.U, 0 ≤ (v p c.other - v p c) * (gT p c x₀ γ x - t1cs p)) :
    t1Good p (static p c) (fun x => GT p c x₀ γ x - GT p c x₀ γ 0) (gT p c x₀ γ)
      (gT' p c x₀ γ) := by
  refine ⟨fun x => (t1_hasDerivAt_GT p c x₀ γ x).sub_const _, t1_hasDerivAt_gT p c x₀ γ,
    t1_continuous_gT' p c x₀ γ, by simp, hval, ?_, ?_⟩
  · intro j x _
    exact t1_Q_gT_self p c x₀ γ x
  · intro x hx d
    by_cases hd : d = c
    · subst hd; unfold t1Q; rw [t1_Q_gT_self]
    · unfold t1Q; rw [t1_Q_gT_other p hv c d hd]
      have := t1_eq_other c d hd; subst this
      have := t1_sig_pos p c.other
      exact mul_nonneg (by positivity) (hhjb x hx)

lemma t1_static_strict (p : Params) (hv : v p .one < v p .two) (c : Ctrl) (x₀ γ : ℝ)
    (hs : ∀ x ∈ Ioo 0 p.U, 0 < (v p c.other - v p c) * (gT p c x₀ γ x - t1cs p)) :
    t1Strict p (gT p c x₀ γ) (gT' p c x₀ γ) := by
  refine ⟨p.U, c, fun x hx => ⟨fun _ => ?_, fun h => absurd h (not_lt.mpr hx.2.le)⟩⟩
  unfold t1Q; rw [t1_Q_gT_other p hv c c.other (t1_other_ne c)]
  have := t1_sig_pos p c.other
  exact mul_pos (by positivity) (hs x hx)

/-! ### Two-interval policies -/

lemma t1_glue (f1 f2 d1 d2 : ℝ → ℝ) (S : ℝ) (h1 : ∀ x, HasDerivAt f1 (d1 x) x)
    (h2 : ∀ x, HasDerivAt f2 (d2 x) x) (he : f1 S = f2 S) (hd : d1 S = d2 S) (x : ℝ) :
    HasDerivAt (fun x => if x ≤ S then f1 x else f2 x) (if x ≤ S then d1 x else d2 x) x := by
  rcases lt_trichotomy x S with h | h | h
  · have hev : (fun x => if x ≤ S then f1 x else f2 x) =ᶠ[𝓝 x] f1 := by
      filter_upwards [Iio_mem_nhds h] with y hy
      simp [le_of_lt (show y < S from hy)]
    rw [if_pos h.le]; exact (h1 x).congr_of_eventuallyEq hev
  · subst h
    rw [if_pos le_rfl]
    have hl : HasDerivWithinAt (fun y => if y ≤ x then f1 y else f2 y) (d1 x) (Iic x) x :=
      (h1 x).hasDerivWithinAt.congr (fun y hy => by simp [show y ≤ x from hy]) (by simp)
    have hr : HasDerivWithinAt (fun y => if y ≤ x then f1 y else f2 y) (d1 x) (Ici x) x := by
      rw [hd]
      refine (h2 x).hasDerivWithinAt.congr (fun y hy => ?_) (by simp [he])
      by_cases hyx : y ≤ x
      · have : y = x := le_antisymm hyx hy
        subst this; simp [he]
      · simp [hyx]
    have := hl.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · have hev : (fun x => if x ≤ S then f1 x else f2 x) =ᶠ[𝓝 x] f2 := by
      filter_upwards [Ioi_mem_nhds h] with y hy
      simp [not_le.mpr (show S < y from hy)]
    rw [if_neg (not_le.mpr h)]; exact (h2 x).congr_of_eventuallyEq hev

noncomputable def g2 (p : Params) (f : Ctrl) (S x : ℝ) : ℝ :=
  if x ≤ S then gT p f S (t1cs p) x else gT p f.other S (t1cs p) x

noncomputable def g2' (p : Params) (f : Ctrl) (S x : ℝ) : ℝ :=
  if x ≤ S then gT' p f S (t1cs p) x else gT' p f.other S (t1cs p) x

noncomputable def V2 (p : Params) (f : Ctrl) (S x : ℝ) : ℝ :=
  if x ≤ S then GT p f S (t1cs p) x - GT p f S (t1cs p) 0
  else GT p f.other S (t1cs p) x - GT p f.other S (t1cs p) S + GT p f S (t1cs p) S
    - GT p f S (t1cs p) 0

/-- Terminal value of the two-interval candidate with switch at `S`. -/
noncomputable def t1I (p : Params) (f : Ctrl) (S : ℝ) : ℝ :=
  GT p f.other S (t1cs p) p.U - GT p f.other S (t1cs p) S + GT p f S (t1cs p) S
    - GT p f S (t1cs p) 0

lemma t1_gT_sub (p : Params) (c : Ctrl) (x₀ γ x : ℝ) :
    gT p c x₀ γ x - t1cs p = (γ - t1cs p) * Real.exp (-(v p c) * (x - x₀)) +
      (t1cs p - t1A p c) * (Real.exp (-(v p c) * (x - x₀)) - 1) := by
  simp only [gT]; ring

lemma t1_other_pos (p : Params) (hv : v p .one < v p .two) (f : Ctrl)
    (hf : 0 < (v p f.other - v p f) * (t1cs p - t1A p f)) :
    0 < (v p f.other - v p f) * (t1cs p - t1A p f.other) := by
  have hid := t1_ident p hv f
  have h1 := t1_v_pos p f
  have h2 := t1_v_pos p f.other
  have : (v p f.other - v p f) * (t1cs p - t1A p f.other) * v p f.other =
      (v p f.other - v p f) * (t1cs p - t1A p f) * v p f := by
    linear_combination (-(v p f.other - v p f)) * hid
  have h3 : 0 < (v p f.other - v p f) * (t1cs p - t1A p f.other) * v p f.other := by
    rw [this]; positivity
  exact pos_of_mul_pos_left h3 h2.le

lemma t1_two (p : Params) (hv : v p .one < v p .two) (f : Ctrl) (S : ℝ) (hS : S ∈ Ioo 0 p.U)
    (hf : 0 < (v p f.other - v p f) * (t1cs p - t1A p f)) (hval : t1I p f S = p.M) :
    t1Good p (twoInt p f S hS) (V2 p f S) (g2 p f S) (g2' p f S) ∧
      t1Strict p (g2 p f S) (g2' p f S) := by
  have hf2 := t1_other_pos p hv f hf
  have hid := t1_ident p hv f
  have hgS : ∀ c, gT p c S (t1cs p) S = t1cs p := fun c => by simp [gT]
  have hg'S : gT' p f S (t1cs p) S = gT' p f.other S (t1cs p) S := by
    simp only [gT', sub_self, mul_zero, Real.exp_zero, mul_one]
    linear_combination (-1 : ℝ) * hid
  -- left branch: strict preference for `f` when `x < S`
  have hleftQ : ∀ x, x ≤ S → ∀ d, 0 ≤ t1Q p (g2 p f S) (g2' p f S) d x ∧
      (d ≠ f → x < S → 0 < t1Q p (g2 p f S) (g2' p f S) d x) := by
    intro x hx d
    simp only [t1Q, g2, g2', if_pos hx]
    by_cases hd : d = f
    · subst hd; rw [t1_Q_gT_self]; exact ⟨le_rfl, fun h => absurd rfl h⟩
    · rw [t1_Q_gT_other p hv f d hd, t1_gT_sub]
      have := t1_eq_other f d hd; subst this
      have hs := t1_sig_pos p f.other
      have he : 1 ≤ Real.exp (-(v p f) * (x - S)) := by
        apply Real.one_le_exp; have := t1_v_pos p f; nlinarith
      refine ⟨?_, fun _ hxS => ?_⟩
      · simp only [sub_self, zero_mul, zero_add]
        have : 0 ≤ (v p f.other - v p f) * ((t1cs p - t1A p f) *
            (Real.exp (-(v p f) * (x - S)) - 1)) := by
          rw [← mul_assoc]; exact mul_nonneg hf.le (by linarith)
        positivity
      · simp only [sub_self, zero_mul, zero_add]
        have he' : 1 < Real.exp (-(v p f) * (x - S)) := by
          apply Real.one_lt_exp_iff.mpr; have := t1_v_pos p f; nlinarith
        have : 0 < (v p f.other - v p f) * ((t1cs p - t1A p f) *
            (Real.exp (-(v p f) * (x - S)) - 1)) := by
          rw [← mul_assoc]; exact mul_pos hf (by linarith)
        positivity
  have hrightQ : ∀ x, S < x → ∀ d, 0 ≤ t1Q p (g2 p f S) (g2' p f S) d x ∧
      (d = f → 0 < t1Q p (g2 p f S) (g2' p f S) d x) := by
    intro x hx d
    simp only [t1Q, g2, g2', if_neg (not_le.mpr hx)]
    by_cases hd : d = f.other
    · subst hd; rw [t1_Q_gT_self]; exact ⟨le_rfl, fun h => absurd h (t1_other_ne f)⟩
    · have hdf : d = f := by
        have := t1_eq_other f.other d hd; rwa [t1_other_other] at this
      subst hdf
      rw [t1_Q_gT_other p hv d.other d (t1_other_ne d).symm, t1_gT_sub]
      have hs := t1_sig_pos p d
      have he' : Real.exp (-(v p d.other) * (x - S)) < 1 := by
        apply Real.exp_lt_one_iff.mpr; have := t1_v_pos p d.other; nlinarith
      simp only [sub_self, zero_mul, zero_add]
      have : 0 < (v p d - v p d.other) * ((t1cs p - t1A p d.other) *
          (Real.exp (-(v p d.other) * (x - S)) - 1)) := by
        have : (v p d - v p d.other) * ((t1cs p - t1A p d.other) *
            (Real.exp (-(v p d.other) * (x - S)) - 1)) =
            ((v p d.other - v p d) * (t1cs p - t1A p d.other)) *
            (1 - Real.exp (-(v p d.other) * (x - S))) := by ring
        rw [this]; exact mul_pos hf2 (by linarith)
      exact ⟨by positivity, fun _ => by positivity⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x
    exact t1_glue (fun x => GT p f S (t1cs p) x - GT p f S (t1cs p) 0)
      (fun x => GT p f.other S (t1cs p) x - GT p f.other S (t1cs p) S + GT p f S (t1cs p) S
        - GT p f S (t1cs p) 0) _ _ S
      (fun x => (t1_hasDerivAt_GT p f S _ x).sub_const _)
      (fun x => (((t1_hasDerivAt_GT p f.other S _ x).sub_const _).add_const _).sub_const _)
      (by ring) (by rw [hgS, hgS]) x
  · intro x
    exact t1_glue _ _ _ _ S (t1_hasDerivAt_gT p f S _) (t1_hasDerivAt_gT p f.other S _)
      (by rw [hgS, hgS]) hg'S x
  · exact Continuous.if_le (t1_continuous_gT' p f S _) (t1_continuous_gT' p f.other S _)
      continuous_id continuous_const (fun x hx => by rw [hx]; exact hg'S)
  · simp [V2, hS.1.le]
  · simp only [V2, if_neg (not_le.mpr hS.2)]; exact hval
  · intro j x hx
    fin_cases j
    · simp [twoInt] at hx ⊢
      simp only [t1Q, g2, g2', if_pos hx.2.le]
      exact t1_Q_gT_self p f S _ x
    · simp [twoInt] at hx ⊢
      simp only [t1Q, g2, g2', if_neg (not_le.mpr hx.1)]
      exact t1_Q_gT_self p f.other S _ x
  · intro x _ d
    by_cases hx : x ≤ S
    · exact (hleftQ x hx d).1
    · exact (hrightQ x (not_le.mp hx) d).1
  · refine ⟨S, f, fun x _ => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · exact (hleftQ x hx.le f.other).2 (t1_other_ne f) hx
    · exact (hrightQ x hx f).2 rfl

/-! ### Case analysis -/

lemma t1_kappa0_pos (p : Params) (c : Ctrl) :
    0 < (Real.exp (-(v p c) * (0 - 0)) - Real.exp (-(v p c) * (p.U - 0))) / v p c := by
  have hv := t1_v_pos p c
  have hU := p.hU
  apply div_pos _ hv
  simp only [sub_self, mul_zero, Real.exp_zero, sub_zero, sub_pos]
  apply Real.exp_lt_one_iff.mpr; nlinarith

lemma t1_kappaU_pos (p : Params) (c : Ctrl) :
    0 < (Real.exp (-(v p c) * (0 - p.U)) - Real.exp (-(v p c) * (p.U - p.U))) / v p c := by
  have hv := t1_v_pos p c
  have hU := p.hU
  apply div_pos _ hv
  simp only [sub_self, mul_zero, Real.exp_zero, sub_pos]
  apply Real.one_lt_exp_iff.mpr; nlinarith

lemma t1_val_lin (p : Params) (c : Ctrl) (x₀ γ : ℝ) :
    GT p c x₀ γ p.U - GT p c x₀ γ 0 = (GT p c x₀ (t1cs p) p.U - GT p c x₀ (t1cs p) 0) +
      (γ - t1cs p) * ((Real.exp (-(v p c) * (0 - x₀)) - Real.exp (-(v p c) * (p.U - x₀)))
        / v p c) := by
  simp only [GT]; ring

lemma t1_case (p : Params) (hv : v p .one < v p .two) (f : Ctrl)
    (hf : 0 < (v p f.other - v p f) * (t1cs p - t1A p f)) :
    ∃ (π : IntervalPolicy p) (V g g' : ℝ → ℝ), π.k ≤ 2 ∧ t1Good p π V g g' ∧
      t1Strict p g g' := by
  have hf2 := t1_other_pos p hv f hf
  set ε := v p f.other - v p f with hε
  set I0 := t1I p f 0 with hI0
  set IU := t1I p f p.U with hIU
  have hI0' : I0 = GT p f.other 0 (t1cs p) p.U - GT p f.other 0 (t1cs p) 0 := by
    simp only [hI0, t1I]; ring
  have hIU' : IU = GT p f p.U (t1cs p) p.U - GT p f p.U (t1cs p) 0 := by
    simp only [hIU, t1I]; ring
  by_cases hA : ε * (p.M - I0) ≤ 0
  · -- always `f.other`, anchored at `0`
    set κ := (Real.exp (-(v p f.other) * (0 - 0)) - Real.exp (-(v p f.other) * (p.U - 0)))
      / v p f.other with hκ
    have hκp : 0 < κ := t1_kappa0_pos p f.other
    set γ := t1cs p + (p.M - I0) / κ with hγ
    have hval : GT p f.other 0 γ p.U - GT p f.other 0 γ 0 = p.M := by
      rw [t1_val_lin, ← hI0', ← hκ, hγ]; field_simp; ring
    have hpos : ∀ x ∈ Ioo 0 p.U,
        0 < (v p f.other.other - v p f.other) * (gT p f.other 0 γ x - t1cs p) := by
      intro x hx
      rw [t1_other_other, t1_gT_sub]
      have he1 : Real.exp (-(v p f.other) * (x - 0)) < 1 := by
        apply Real.exp_lt_one_iff.mpr; have := t1_v_pos p f.other; nlinarith [hx.1]
      have he0 := Real.exp_pos (-(v p f.other) * (x - 0))
      have h1 : 0 ≤ (v p f - v p f.other) * (γ - t1cs p) := by
        have : (v p f - v p f.other) * (γ - t1cs p) = -(ε * (p.M - I0)) / κ := by
          rw [hγ, add_sub_cancel_left, hε]; ring
        rw [this]; apply div_nonneg _ hκp.le; linarith
      have : (v p f - v p f.other) * ((γ - t1cs p) * Real.exp (-(v p f.other) * (x - 0)) +
          (t1cs p - t1A p f.other) * (Real.exp (-(v p f.other) * (x - 0)) - 1)) =
          ((v p f - v p f.other) * (γ - t1cs p)) * Real.exp (-(v p f.other) * (x - 0)) +
          ((v p f.other - v p f) * (t1cs p - t1A p f.other)) *
            (1 - Real.exp (-(v p f.other) * (x - 0))) := by ring
      rw [this]
      have := mul_nonneg h1 he0.le
      have := mul_pos hf2 (sub_pos.mpr he1)
      linarith
    exact ⟨static p f.other, _, _, _, by simp [static],
      t1_static_good p hv f.other 0 γ hval (fun x hx => (hpos x hx).le),
      t1_static_strict p hv f.other 0 γ hpos⟩
  by_cases hB : 0 ≤ ε * (p.M - IU)
  · -- always `f`, anchored at `U`
    set κ := (Real.exp (-(v p f) * (0 - p.U)) - Real.exp (-(v p f) * (p.U - p.U)))
      / v p f with hκ
    have hκp : 0 < κ := t1_kappaU_pos p f
    set γ := t1cs p + (p.M - IU) / κ with hγ
    have hval : GT p f p.U γ p.U - GT p f p.U γ 0 = p.M := by
      rw [t1_val_lin, ← hIU', ← hκ, hγ]; field_simp; ring
    have hpos : ∀ x ∈ Ioo 0 p.U,
        0 < (v p f.other - v p f) * (gT p f p.U γ x - t1cs p) := by
      intro x hx
      rw [t1_gT_sub]
      have he1 : 1 < Real.exp (-(v p f) * (x - p.U)) := by
        apply Real.one_lt_exp_iff.mpr; have := t1_v_pos p f; nlinarith [hx.2]
      have he0 := Real.exp_pos (-(v p f) * (x - p.U))
      have h1 : 0 ≤ (v p f.other - v p f) * (γ - t1cs p) := by
        have : (v p f.other - v p f) * (γ - t1cs p) = (ε * (p.M - IU)) / κ := by
          rw [hγ, add_sub_cancel_left, hε]; ring
        rw [this]; exact div_nonneg hB hκp.le
      have : (v p f.other - v p f) * ((γ - t1cs p) * Real.exp (-(v p f) * (x - p.U)) +
          (t1cs p - t1A p f) * (Real.exp (-(v p f) * (x - p.U)) - 1)) =
          ((v p f.other - v p f) * (γ - t1cs p)) * Real.exp (-(v p f) * (x - p.U)) +
          ((v p f.other - v p f) * (t1cs p - t1A p f)) *
            (Real.exp (-(v p f) * (x - p.U)) - 1) := by ring
      rw [this]
      have := mul_nonneg h1 he0.le
      have := mul_pos hf (sub_pos.mpr he1)
      linarith
    exact ⟨static p f, _, _, _, by simp [static],
      t1_static_good p hv f p.U γ hval (fun x hx => (hpos x hx).le),
      t1_static_strict p hv f p.U γ hpos⟩
  · -- two intervals, by the intermediate value theorem
    push Not at hA hB
    have hcont : ContinuousOn (t1I p f) (Icc 0 p.U) := by
      apply Continuous.continuousOn
      unfold t1I GT; fun_prop
    have hex : ∃ S ∈ Ioo 0 p.U, t1I p f S = p.M := by
      rcases lt_or_gt_of_ne (show ε ≠ 0 by intro h; rw [h] at hA; simp at hA) with hneg | hpos'
      · have h1 : p.M < I0 := by nlinarith
        have h2 : IU < p.M := by nlinarith
        exact intermediate_value_Ioo' p.hU.le hcont ⟨h2, h1⟩
      · have h1 : I0 < p.M := by nlinarith
        have h2 : p.M < IU := by nlinarith
        exact intermediate_value_Ioo p.hU.le hcont ⟨h1, h2⟩
    obtain ⟨S, hS, hIS⟩ := hex
    obtain ⟨hg, hs⟩ := t1_two p hv f S hS hf hIS
    exact ⟨twoInt p f S hS, _, _, _, by simp [twoInt], hg, hs⟩

lemma t1_degenerate (p : Params) (hv : v p .one < v p .two)
    (h1 : t1cs p = t1A p .one) (h2 : t1cs p = t1A p .two) :
    ∃ (π : IntervalPolicy p) (V g g' : ℝ → ℝ), π.k ≤ 2 ∧ t1Good p π V g g' ∧
      (¬ (Δh p .one = 0 ∧ Δh p .two = 0) → t1Strict p g g') := by
  have hval0 : ∀ c : Ctrl, t1cs p = t1A p c →
      GT p c 0 (t1cs p) p.U - GT p c 0 (t1cs p) 0 = t1cs p * p.U := by
    intro c hc; simp only [GT, ← hc]; ring
  have hgsub : ∀ c : Ctrl, t1cs p = t1A p c → ∀ γ x,
      gT p c 0 γ x - t1cs p = (γ - t1cs p) * Real.exp (-(v p c) * (x - 0)) := by
    intro c hc γ x; rw [t1_gT_sub, ← hc]; ring
  have hΔ : ¬ (Δh p .one = 0 ∧ Δh p .two = 0) → p.M ≠ t1cs p * p.U := by
    intro hn hM; apply hn
    have hU := p.hU.ne'
    constructor
    · simp only [Δh, hstar]; rw [t1_cost_eq, ← h1, hM]; field_simp; ring
    · simp only [Δh, hstar]; rw [t1_cost_eq, ← h2, hM]; field_simp; ring
  have hv12 : 0 < v p .two - v p .one := sub_pos.mpr hv
  by_cases hM : t1cs p * p.U ≤ p.M
  · -- always 1
    set κ := (Real.exp (-(v p .one) * (0 - 0)) - Real.exp (-(v p .one) * (p.U - 0)))
      / v p .one with hκ
    have hκp : 0 < κ := t1_kappa0_pos p .one
    set γ := t1cs p + (p.M - t1cs p * p.U) / κ with hγ
    have hval : GT p .one 0 γ p.U - GT p .one 0 γ 0 = p.M := by
      rw [t1_val_lin, hval0 .one h1, ← hκ, hγ]; field_simp; ring
    have hexpr : ∀ x, (v p Ctrl.one.other - v p .one) * (gT p .one 0 γ x - t1cs p) =
        (v p .two - v p .one) * ((p.M - t1cs p * p.U) / κ) *
          Real.exp (-(v p .one) * (x - 0)) := by
      intro x; rw [hgsub .one h1, hγ]; simp only [Ctrl.other]; ring
    refine ⟨static p .one, _, _, _, by simp [static],
      t1_static_good p hv .one 0 γ hval (fun x _ => ?_), fun hn => ?_⟩
    · rw [hexpr]; have := div_nonneg (sub_nonneg.mpr hM) hκp.le; positivity
    · have hlt : t1cs p * p.U < p.M := lt_of_le_of_ne hM (hΔ hn).symm
      refine t1_static_strict p hv .one 0 γ (fun x _ => ?_)
      rw [hexpr]; have := div_pos (sub_pos.mpr hlt) hκp; positivity
  · -- always 2
    push Not at hM
    set κ := (Real.exp (-(v p .two) * (0 - 0)) - Real.exp (-(v p .two) * (p.U - 0)))
      / v p .two with hκ
    have hκp : 0 < κ := t1_kappa0_pos p .two
    set γ := t1cs p + (p.M - t1cs p * p.U) / κ with hγ
    have hval : GT p .two 0 γ p.U - GT p .two 0 γ 0 = p.M := by
      rw [t1_val_lin, hval0 .two h2, ← hκ, hγ]; field_simp; ring
    have hexpr : ∀ x, (v p Ctrl.two.other - v p .two) * (gT p .two 0 γ x - t1cs p) =
        (v p .two - v p .one) * ((t1cs p * p.U - p.M) / κ) *
          Real.exp (-(v p .two) * (x - 0)) := by
      intro x; rw [hgsub .two h2, hγ]; simp only [Ctrl.other]; field_simp; ring
    have hpos : ∀ x ∈ Ioo 0 p.U,
        0 < (v p Ctrl.two.other - v p .two) * (gT p .two 0 γ x - t1cs p) := by
      intro x _
      rw [hexpr]; have := div_pos (sub_pos.mpr hM) hκp; positivity
    exact ⟨static p .two, _, _, _, by simp [static],
      t1_static_good p hv .two 0 γ hval (fun x hx => (hpos x hx).le),
      fun _ => t1_static_strict p hv .two 0 γ hpos⟩

theorem t1_construct (p : Params) (hv : v p .one < v p .two) :
    ∃ (π : IntervalPolicy p) (V g g' : ℝ → ℝ), π.k ≤ 2 ∧ t1Good p π V g g' ∧
      (¬ (Δh p .one = 0 ∧ Δh p .two = 0) → t1Strict p g g') := by
  have hid := t1_ident p hv .one
  simp only [Ctrl.other] at hid
  have hv1 := t1_v_pos p .one
  have hv2 := t1_v_pos p .two
  have hv12 : 0 < v p .two - v p .one := sub_pos.mpr hv
  rcases lt_trichotomy 0 ((v p .two - v p .one) * (t1cs p - t1A p .one)) with h | h | h
  · obtain ⟨π, V, g, g', hk, hg, hs⟩ := t1_case p hv .one h
    exact ⟨π, V, g, g', hk, hg, fun _ => hs⟩
  · have h1 : t1cs p = t1A p .one := by
      rcases mul_eq_zero.mp h.symm with h' | h'
      · linarith
      · linarith
    have h2 : t1cs p = t1A p .two := by
      rw [h1, sub_self, mul_zero] at hid
      rcases mul_eq_zero.mp hid.symm with h' | h'
      · linarith
      · linarith
    exact t1_degenerate p hv h1 h2
  · have hn1 : t1cs p - t1A p .one < 0 := by
      by_contra hc; push Not at hc; nlinarith
    have hn2 : t1cs p - t1A p .two < 0 := by
      by_contra hc; push Not at hc; nlinarith
    have hf : 0 < (v p Ctrl.two.other - v p .two) * (t1cs p - t1A p .two) := by
      simp only [Ctrl.other]; nlinarith
    obtain ⟨π, V, g, g', hk, hg, hs⟩ := t1_case p hv .two hf
    exact ⟨π, V, g, g', hk, hg, fun _ => hs⟩

theorem theorem_1_proof (p : Params) (hv : v p .one < v p .two) :
    (∃ π : IntervalPolicy p, π.k ≤ 2 ∧ IsOptimal p π) ∧
    (¬ (Δh p .one = 0 ∧ Δh p .two = 0) →
      ∀ π : IntervalPolicy p, IsOptimal p π → π.k ≤ 2) := by
  obtain ⟨π0, V, g, g', hk, hg, hs⟩ := t1_construct p hv
  refine ⟨⟨π0, hk, V, hg.isValue, hg.le⟩, fun hn π ⟨W, hW, hWopt⟩ => ?_⟩
  have h1 := hWopt π0 V hg.isValue
  have h2 := hg.le π W hW
  exact t1_k_le_two hg (hs hn) π W hW (fun x hx => le_antisymm (h1 x hx) (h2 x hx))

end DriftVarCtrl.FixedLB

open DriftVarCtrl.FixedLB in
theorem solution (p : Params) (hv : v p .one < v p .two) :
    (∃ π : IntervalPolicy p, π.k ≤ 2 ∧ IsOptimal p π) ∧
    (¬ (Δh p .one = 0 ∧ Δh p .two = 0) →
      ∀ π : IntervalPolicy p, IsOptimal p π → π.k ≤ 2) :=
  theorem_1_proof p hv
