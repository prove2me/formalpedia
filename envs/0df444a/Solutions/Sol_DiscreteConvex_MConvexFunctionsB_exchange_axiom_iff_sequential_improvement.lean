-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsB.exchange_axiom_iff_sequential_improvement
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T06:35:01.666189+00:00
-- url     : https://prove2.me/submissions/b8413d54-a549-41b7-9c8a-845f14659987

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MSI
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNatSI
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ

set_option autoImplicit false

namespace DiscreteConvex.MConvexFunctionsB.P19bd

open DiscreteConvex.MConvexFunctionsB

theorem sum_abs_lt {V : Type*} [Fintype V] [DecidableEq V] (x y : V → ℤ) (u v : V)
    (hu : y u < x u) (hv : x v < y v) :
    (∑ w, |x w - (y w + CharVec u w - CharVec v w)|) < ∑ w, |x w - y w| := by
  have huv : u ≠ v := by rintro rfl; omega
  apply Finset.sum_lt_sum
  · intro w _
    have hcu : CharVec u w = if w = u then 1 else 0 := rfl
    have hcv : CharVec v w = if w = v then 1 else 0 := rfl
    have A := abs_cases (x w - (y w + CharVec u w - CharVec v w))
    have B := abs_cases (x w - y w)
    split_ifs at hcu hcv with h1 h2 h2
    · exact absurd (h1.symm.trans h2) huv
    · subst h1; omega
    · subst h2; omega
    · omega
  · refine ⟨u, Finset.mem_univ _, ?_⟩
    have hcu : CharVec u u = 1 := if_pos rfl
    have hcv : CharVec v u = 0 := if_neg huv
    have A := abs_cases (x u - (y u + CharVec u u - CharVec v u))
    have B := abs_cases (x u - y u)
    omega

/-- Prop 6.23-style descent: for an M-convex `g`, `g x > g y` gives a strict single-exchange
descent step from `x` inside the supports of `x - y`. -/
theorem descent {V : Type*} [Fintype V] [DecidableEq V] (g : (V → ℤ) → WithTop ℝ)
    (hg : MExchangeAxiom g) (x : V → ℤ) (hx : x ∈ DomZ g) :
    ∀ n : ℕ, ∀ y ∈ DomZ g, (∑ w, |x w - y w|) ≤ (n : ℤ) → g x > g y →
      g x > (SuppPos x y).inf (fun u => (SuppNeg x y).inf (fun v =>
        g (fun w => x w - CharVec u w + CharVec v w))) := by
  intro n
  induction n with
  | zero =>
    intro y _ hn hlt
    exfalso
    have hxy : x = y := by
      funext w
      have h0 : ∀ w ∈ (Finset.univ : Finset V), 0 ≤ |x w - y w| := fun w _ => abs_nonneg _
      have := (Finset.sum_eq_zero_iff_of_nonneg h0).1 (le_antisymm (by exact_mod_cast hn)
        (Finset.sum_nonneg h0)) w (Finset.mem_univ _)
      have := abs_eq_zero.1 this; omega
    subst hxy; exact lt_irrefl _ hlt
  | succ n ih =>
    intro y hy hn hlt
    -- some u in SuppPos x y
    by_cases hP : (SuppPos x y).Nonempty
    · obtain ⟨u, hu⟩ := hP
      obtain ⟨v, hv, hex⟩ := hg x hx y hy u hu
      have hu' : y u < x u := (Finset.mem_filter.1 hu).2
      have hv' : x v < y v := (Finset.mem_filter.1 hv).2
      set x' : V → ℤ := fun w => x w - CharVec u w + CharVec v w with hx'
      set y' : V → ℤ := fun w => y w + CharVec u w - CharVec v w with hy'
      have hstep : (SuppPos x y).inf (fun u => (SuppNeg x y).inf (fun v =>
          g (fun w => x w - CharVec u w + CharVec v w))) ≤ g x' :=
        (Finset.inf_le hu).trans (Finset.inf_le hv)
      by_cases hc : g x' < g x
      · exact lt_of_le_of_lt hstep hc
      · rw [not_lt] at hc
        obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hx
        obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hy
        rw [← ha] at hc hlt hex ⊢
        rw [← hb] at hlt hex
        have hx'top : g x' ≠ ⊤ := by
          intro h; rw [h] at hex; simp at hex
        have hy'top : g y' ≠ ⊤ := by
          intro h; rw [h] at hex; simp at hex
        obtain ⟨a', ha'⟩ := WithTop.ne_top_iff_exists.1 hx'top
        obtain ⟨b', hb'⟩ := WithTop.ne_top_iff_exists.1 hy'top
        rw [← ha'] at hc hex
        rw [← hb'] at hex
        have hex' : a' + b' ≤ a + b := by exact_mod_cast hex
        have hc' : a ≤ a' := by exact_mod_cast hc
        have hlt' : b < a := by exact_mod_cast hlt
        have hy'dom : y' ∈ DomZ g := hy'top
        have hlt2 : g x > g y' := by
          rw [← ha, ← hb']; exact_mod_cast (by linarith : b' < a)
        have hdist : (∑ w, |x w - y' w|) ≤ (n : ℤ) := by
          have : (∑ w, |x w - y' w|) < ∑ w, |x w - y w| := sum_abs_lt x y u v hu' hv'
          push_cast at hn; omega
        have ihy := ih y' hy'dom hdist hlt2
        rw [← ha] at ihy
        refine lt_of_le_of_lt ?_ ihy
        refine Finset.le_inf (fun c hc => ?_)
        have hcP : c ∈ SuppPos x y := by
          have h0 : y' c < x c := (Finset.mem_filter.1 hc).2
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
          have e : y' c = y c + CharVec u c - CharVec v c := rfl
          have hcu : CharVec u c = if c = u then 1 else 0 := rfl
          have hcv : CharVec v c = if c = v then 1 else 0 := rfl
          split_ifs at hcu hcv with h1 h2 h2
          · subst h1; subst h2; omega
          · subst h1; omega
          · subst h2; omega
          · omega
        refine (Finset.inf_le hcP).trans (Finset.le_inf (fun d hd => ?_))
        have hdN : d ∈ SuppNeg x y := by
          have h0 : x d < y' d := (Finset.mem_filter.1 hd).2
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
          have e : y' d = y d + CharVec u d - CharVec v d := rfl
          have hcu : CharVec u d = if d = u then 1 else 0 := rfl
          have hcv : CharVec v d = if d = v then 1 else 0 := rfl
          split_ifs at hcu hcv with h1 h2 h2
          · subst h1; subst h2; omega
          · subst h1; omega
          · subst h2; omega
          · omega
        exact Finset.inf_le hdN
    · exfalso
      rw [Finset.not_nonempty_iff_eq_empty] at hP
      by_cases hN : (SuppNeg x y).Nonempty
      · obtain ⟨u, hu⟩ := hN
        have hu2 : u ∈ SuppPos y x := by
          simp only [SuppPos, SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
          exact hu
        obtain ⟨v, hv, _⟩ := hg y hy x hx u hu2
        have : v ∈ SuppPos x y := by
          simp only [SuppPos, SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          exact hv
        rw [hP] at this; simp at this
      · rw [Finset.not_nonempty_iff_eq_empty] at hN
        have hxy : x = y := by
          funext w
          have h1 : w ∉ SuppPos x y := by rw [hP]; simp
          have h2 : w ∉ SuppNeg x y := by rw [hN]; simp
          simp only [SuppPos, SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          omega
        subst hxy; exact lt_irrefl _ hlt

theorem dom_linearWeight {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) :
    DomZ (LinearWeight f p) = DomZ f := by
  ext x
  simp only [DomZ, LinearWeight, ne_eq, WithTop.add_eq_top,
    WithTop.coe_ne_top, or_false]

theorem linearWeight_mexchange {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (p : V → ℝ) :
    MExchangeAxiom (LinearWeight f p) := by
  intro x hx y hy u hu
  rw [dom_linearWeight] at hx hy
  obtain ⟨v, hv, hex⟩ := hf x hx y hy u hu
  refine ⟨v, hv, ?_⟩
  simp only [LinearWeight]
  have hsum : (-(∑ w, p w * ((x w : ℤ) : ℝ))) + (-(∑ w, p w * ((y w : ℤ) : ℝ))) =
      (-(∑ w, p w * (((x w - CharVec u w + CharVec v w : ℤ)) : ℝ))) +
      (-(∑ w, p w * (((y w + CharVec u w - CharVec v w : ℤ)) : ℝ))) := by
    simp only [← Finset.sum_add_distrib, ← neg_add, ← mul_add]
    congr 1; apply Finset.sum_congr rfl; intro w _; push_cast; ring
  calc f (fun w => x w - CharVec u w + CharVec v w) +
        ((-(∑ w, p w * (((x w - CharVec u w + CharVec v w : ℤ)) : ℝ)) : ℝ) : WithTop ℝ) +
      (f (fun w => y w + CharVec u w - CharVec v w) +
        ((-(∑ w, p w * (((y w + CharVec u w - CharVec v w : ℤ)) : ℝ)) : ℝ) : WithTop ℝ))
      = (f (fun w => x w - CharVec u w + CharVec v w) + f (fun w => y w + CharVec u w - CharVec v w))
        + (((-(∑ w, p w * (((x w - CharVec u w + CharVec v w : ℤ)) : ℝ))) +
          (-(∑ w, p w * (((y w + CharVec u w - CharVec v w : ℤ)) : ℝ))) : ℝ) : WithTop ℝ) := by
        rw [WithTop.coe_add]; ac_rfl
    _ ≤ (f x + f y) + (((-(∑ w, p w * ((x w : ℤ) : ℝ))) + (-(∑ w, p w * ((y w : ℤ) : ℝ))) : ℝ)
          : WithTop ℝ) := by
        rw [hsum]; exact add_le_add hex le_rfl
    _ = f x + ((-(∑ w, p w * ((x w : ℤ) : ℝ)) : ℝ) : WithTop ℝ) +
        (f y + ((-(∑ w, p w * ((y w : ℤ) : ℝ)) : ℝ) : WithTop ℝ)) := by
        rw [WithTop.coe_add]; ac_rfl

theorem mexchange_msi {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) : MSI f := by
  intro p x hx y hy hlt
  have hg := linearWeight_mexchange f hf p
  rw [← dom_linearWeight f p] at hx hy
  exact descent _ hg x hx (∑ w, |x w - y w|).toNat y hy (Int.self_le_toNat _) hlt

/-! ### The M♮ half, forward direction -/

def liftPt {V : Type*} [Fintype V] (x : V → ℤ) : Option V → ℤ :=
  fun o => Option.elim o (-(∑ v, x v)) x

def liftP {V : Type*} (p : V → ℝ) : Option V → ℝ := fun o => Option.elim o 0 p

theorem lifted_eval {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (z : Option V → ℤ)
    (hz : z none = -(∑ v, z (some v))) :
    LiftedFunction f z = f (fun v => z (some v)) := by
  simp only [LiftedFunction, if_pos hz]

theorem lw_lifted {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ)
    (z : Option V → ℤ) (hz : z none = -(∑ v, z (some v))) :
    LinearWeight (LiftedFunction f) (liftP p) z = LinearWeight f p (fun v => z (some v)) := by
  simp only [LinearWeight, lifted_eval f z hz, Fintype.sum_option, liftP, Option.elim_none,
    Option.elim_some, zero_mul, zero_add]

theorem charVec_sum {V : Type*} [Fintype V] [DecidableEq V] (a : V) : ∑ o, CharVec a o = 1 := by
  simp [CharVec]

theorem move_ok {V : Type*} [Fintype V] [DecidableEq V] (x : V → ℤ) (a b : Option V) :
    (fun o => liftPt x o - CharVec a o + CharVec b o) none =
      -(∑ v, (fun o => liftPt x o - CharVec a o + CharVec b o) (some v)) := by
  have ha := charVec_sum a
  have hb := charVec_sum b
  rw [Fintype.sum_option] at ha hb
  simp only [liftPt, Option.elim_none, Option.elim_some, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  linarith

theorem charVec_some {V : Type*} [DecidableEq V] (a : Option V) (v : V) :
    CharVec a (some v) = CharVecOpt a v := by
  cases a with
  | none => simp [CharVec, CharVecOpt]
  | some u => simp [CharVec, CharVecOpt]

theorem liftPt_mem {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (x : V → ℤ)
    (hx : x ∈ DomZ f) : liftPt x ∈ DomZ (LiftedFunction f) := by
  show LiftedFunction f (liftPt x) ≠ ⊤
  rw [lifted_eval f _ (by simp [liftPt])]
  exact hx

theorem lw_liftPt {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) (x : V → ℤ) :
    LinearWeight (LiftedFunction f) (liftP p) (liftPt x) = LinearWeight f p x := by
  rw [lw_lifted f p _ (by simp [liftPt])]
  rfl

theorem mnat_mnatsi {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) : MNatSI f := by
  intro p x hx y hy hlt
  have hmsi := mexchange_msi (LiftedFunction f) hf
  have h := hmsi (liftP p) (liftPt x) (liftPt_mem f x hx) (liftPt y) (liftPt_mem f y hy)
    (by rw [lw_liftPt, lw_liftPt]; exact hlt)
  rw [lw_liftPt] at h
  refine lt_of_le_of_lt ?_ h
  refine Finset.le_inf (fun a ha => ?_)
  have ha' : a ∈ insert none ((SuppPos x y).image some) := by
    cases a with
    | none => exact Finset.mem_insert_self _ _
    | some w =>
      apply Finset.mem_insert_of_mem
      simp only [Finset.mem_image, Option.some.injEq, exists_eq_right]
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 ha).2⟩
  refine (Finset.inf_le ha').trans (Finset.le_inf (fun b hb => ?_))
  have hb' : b ∈ insert none ((SuppNeg x y).image some) := by
    cases b with
    | none => exact Finset.mem_insert_self _ _
    | some w =>
      apply Finset.mem_insert_of_mem
      simp only [Finset.mem_image, Option.some.injEq, exists_eq_right]
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hb).2⟩
  refine (Finset.inf_le hb').trans (le_of_eq ?_)
  rw [lw_lifted f p _ (move_ok x a b)]
  congr 1
  funext w
  simp only [liftPt, Option.elim_some, charVec_some]

end DiscreteConvex.MConvexFunctionsB.P19bd

namespace DiscreteConvex.MConvexFunctionsB.Q19bd

open DiscreteConvex.MConvexFunctionsB

/-- inner product `⟨p, z⟩` -/
def ip {V : Type*} [Fintype V] (p : V → ℝ) (z : V → ℤ) : ℝ := ∑ w, p w * (z w : ℝ)

theorem ip_move1 {V : Type*} [Fintype V] [DecidableEq V] (p : V → ℝ) (z : V → ℤ) (a b : V) :
    ip p (fun w => z w - CharVec a w + CharVec b w) = ip p z - p a + p b := by
  simp only [ip, CharVec]
  push_cast
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [mul_ite]

theorem ip_move2 {V : Type*} [Fintype V] [DecidableEq V] (p : V → ℝ) (z : V → ℤ) (a b : V) :
    ip p (fun w => z w + CharVec a w - CharVec b w) = ip p z + p a - p b := by
  simp only [ip, CharVec]
  push_cast
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [mul_ite]

theorem lw_coe {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) (z : V → ℤ)
    (r : ℝ) (hr : f z = r) : LinearWeight f p z = ((r - ip p z : ℝ) : WithTop ℝ) := by
  simp only [LinearWeight, hr, ip, sub_eq_add_neg, WithTop.coe_add]

theorem lw_le_of {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) (z : V → ℤ)
    (R : ℝ) (h : ∀ c : ℝ, f z = c → R ≤ c - ip p z) : (R : WithTop ℝ) ≤ LinearWeight f p z := by
  cases hz : f z with
  | top => simp [LinearWeight, hz]
  | coe c => rw [lw_coe f p z c hz]; exact_mod_cast h c hz

theorem clip (r : ℝ) (a b : WithTop ℝ) (h : (r : WithTop ℝ) < a + b) :
    ∃ a' b' : ℝ, (a' : WithTop ℝ) ≤ a ∧ (b' : WithTop ℝ) ≤ b ∧ r < a' + b' := by
  induction a using WithTop.recTopCoe with
  | top =>
    induction b using WithTop.recTopCoe with
    | top => exact ⟨r, 1, le_top, le_top, by linarith⟩
    | coe b0 => exact ⟨r - b0 + 1, b0, le_top, le_rfl, by linarith⟩
  | coe a0 =>
    induction b using WithTop.recTopCoe with
    | top => exact ⟨a0, r - a0 + 1, le_rfl, le_top, by linarith⟩
    | coe b0 =>
      refine ⟨a0, b0, le_rfl, le_rfl, ?_⟩
      rw [← WithTop.coe_add] at h; exact_mod_cast h

theorem msi_argmin {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (h : MSI f) (p : V → ℝ) (x y : V → ℤ) (hx : x ∈ DomZ f) (hy : y ∈ DomZ f)
    (hlt : LinearWeight f p x > LinearWeight f p y) :
    ∃ a ∈ SuppPos x y, ∃ b ∈ SuppNeg x y,
      LinearWeight f p (fun w => x w - CharVec a w + CharVec b w) < LinearWeight f p x ∧
      ∀ a' ∈ SuppPos x y, ∀ b' ∈ SuppNeg x y,
        LinearWeight f p (fun w => x w - CharVec a w + CharVec b w) ≤
          LinearWeight f p (fun w => x w - CharVec a' w + CharVec b' w) := by
  have H := h p x hx y hy hlt
  by_cases hs : (SuppPos x y ×ˢ SuppNeg x y).Nonempty
  · obtain ⟨⟨a, b⟩, hab, hmin⟩ := (SuppPos x y ×ˢ SuppNeg x y).exists_min_image
      (fun ab => LinearWeight f p (fun w => x w - CharVec ab.1 w + CharVec ab.2 w)) hs
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hab
    refine ⟨a, ha, b, hb, lt_of_le_of_lt ?_ H, fun a' ha' b' hb' =>
      hmin (a', b') (Finset.mem_product.2 ⟨ha', hb'⟩)⟩
    exact Finset.le_inf (fun a' ha' => Finset.le_inf (fun b' hb' =>
      hmin (a', b') (Finset.mem_product.2 ⟨ha', hb'⟩)))
  · exfalso
    have htop : (SuppPos x y).inf (fun u => (SuppNeg x y).inf (fun v =>
        LinearWeight f p (fun w => x w - CharVec u w + CharVec v w))) = ⊤ := by
      rw [Finset.inf_eq_top_iff]
      intro a ha
      rw [Finset.inf_eq_top_iff]
      intro b hb
      exact absurd ⟨(a, b), Finset.mem_product.2 ⟨ha, hb⟩⟩ hs
    rw [htop] at H
    exact not_top_lt H

theorem suppNeg_nonempty {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (h : MSI f) (x y : V → ℤ) (hx : x ∈ DomZ f) (hy : y ∈ DomZ f) (u : V)
    (hu : u ∈ SuppPos x y) : (SuppNeg x y).Nonempty := by
  by_contra hN
  rw [Finset.not_nonempty_iff_eq_empty] at hN
  obtain ⟨fx, hfx⟩ := WithTop.ne_top_iff_exists.1 hx
  obtain ⟨fy, hfy⟩ := WithTop.ne_top_iff_exists.1 hy
  have key : ∀ p : V → ℝ, fx - ip p x = fy - ip p y := by
    intro p
    have h1 : ¬ (LinearWeight f p x > LinearWeight f p y) := by
      intro hlt
      obtain ⟨a, _, b, hb, _⟩ := msi_argmin f h p x y hx hy hlt
      rw [hN] at hb; simp at hb
    have h2 : ¬ (LinearWeight f p y > LinearWeight f p x) := by
      intro hlt
      obtain ⟨a, ha, _⟩ := msi_argmin f h p y x hy hx hlt
      have : a ∈ SuppNeg x y := ha
      rw [hN] at this; simp at this
    rw [lw_coe f p x fx hfx.symm, lw_coe f p y fy hfy.symm] at h1 h2
    have h1' : ¬ (fy - ip p y < fx - ip p x) := fun hh => h1 (by exact_mod_cast hh)
    have h2' : ¬ (fx - ip p x < fy - ip p y) := fun hh => h2 (by exact_mod_cast hh)
    linarith [not_lt.1 h1', not_lt.1 h2']
  have k0 := key (fun _ => 0)
  have k1 := key (fun w => if w = u then 1 else 0)
  simp only [ip, zero_mul, Finset.sum_const_zero, ite_mul, one_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at k0 k1
  have hu' : y u < x u := (Finset.mem_filter.1 hu).2
  have : (y u : ℝ) < x u := by exact_mod_cast hu'
  linarith

theorem mem_pos {V : Type*} [Fintype V] [DecidableEq V] {x y : V → ℤ} {a : V}
    (h : a ∈ SuppPos x y) : y a < x a := (Finset.mem_filter.1 h).2

theorem mem_neg {V : Type*} [Fintype V] [DecidableEq V] {x y : V → ℤ} {a : V}
    (h : a ∈ SuppNeg x y) : x a < y a := (Finset.mem_filter.1 h).2

theorem ip_sub {V : Type*} [Fintype V] (p : V → ℝ) (x y : V → ℤ) :
    ip p x - ip p y = ∑ w, p w * ((x w : ℝ) - (y w : ℝ)) := by
  simp only [ip, ← Finset.sum_sub_distrib, mul_sub]

/-- The local case `x - y = χu + χu' - χv - χv'`. -/
theorem local_case {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (h : MSI f) (x y : V → ℤ) (hx : x ∈ DomZ f) (hy : y ∈ DomZ f) (u u' v v' : V)
    (hu : u ∈ SuppPos x y) (hu' : u' ∈ SuppPos x y) (huu : u ≠ u')
    (hv : v ∈ SuppNeg x y) (hv' : v' ∈ SuppNeg x y)
    (hxe : ∀ w, x w = y w + CharVec u w - CharVec v w + CharVec u' w - CharVec v' w)
    (F1 : f x + f y < f (fun w => x w - CharVec u w + CharVec v w) +
      f (fun w => y w + CharVec u w - CharVec v w))
    (F2 : f x + f y < f (fun w => x w - CharVec u w + CharVec v' w) +
      f (fun w => y w + CharVec u w - CharVec v' w)) : False := by
  obtain ⟨fx, hfx⟩ := WithTop.ne_top_iff_exists.1 hx
  obtain ⟨fy, hfy⟩ := WithTop.ne_top_iff_exists.1 hy
  rw [← hfx, ← hfy, ← WithTop.coe_add] at F1 F2
  obtain ⟨a1, b1, ha1, hb1, hab1⟩ := clip _ _ _ F1
  have hex2 : ∃ a2 b2 : ℝ, (a2 : WithTop ℝ) ≤ f (fun w => x w - CharVec u w + CharVec v' w) ∧
      (b2 : WithTop ℝ) ≤ f (fun w => y w + CharVec u w - CharVec v' w) ∧ fx + fy < a2 + b2 ∧
      (v = v' → a2 = a1) := by
    by_cases hvv : v = v'
    · subst hvv; exact ⟨a1, b1, ha1, hb1, hab1, fun _ => rfl⟩
    · obtain ⟨a2, b2, h1, h2, h3⟩ := clip _ _ _ F2
      exact ⟨a2, b2, h1, h2, h3, fun h => absurd h hvv⟩
  obtain ⟨a2, b2, ha2, hb2, hab2, hvv⟩ := hex2
  have hu0 := mem_pos hu
  have hu0' := mem_pos hu'
  have hv0 := mem_neg hv
  have hv0' := mem_neg hv'
  have nuv : u ≠ v := by rintro rfl; omega
  have nuv' : u ≠ v' := by rintro rfl; omega
  have nu'v : u' ≠ v := by rintro rfl; omega
  have nu'v' : u' ≠ v' := by rintro rfl; omega
  set q : ℝ := max (a1 - b2) (a2 - b1) with hq
  let p : V → ℝ := fun w => if w = u' then q else if w = v then a1 - fx else if w = v' then a2 - fx
    else 0
  have pu : p u = 0 := by simp [p, nuv, nuv', huu]
  have pu' : p u' = q := by simp [p]
  have pv : p v = a1 - fx := by simp [p, nu'v.symm]
  have pv' : p v' = a2 - fx := by
    by_cases hh : v = v'
    · subst hh; simp [p, nu'v.symm, hvv rfl]
    · simp [p, nu'v'.symm, Ne.symm hh]
  have hxf : x = fun w => (fun w => y w + CharVec u w - CharVec v w) w + CharVec u' w - CharVec v' w :=
    funext fun w => hxe w
  have hipx : ip p x = ip p y + p u - p v + p u' - p v' := by
    rw [hxf, ip_move2, ip_move2]
  have hgt : LinearWeight f p x > LinearWeight f p y := by
    rw [lw_coe f p x fx hfx.symm, lw_coe f p y fy hfy.symm, gt_iff_lt, WithTop.coe_lt_coe, hipx,
      pu, pu', pv, pv']
    have : q < a1 + a2 - fx - fy := max_lt (by linarith) (by linarith)
    linarith
  obtain ⟨a, ha, b, hb, hlt, -⟩ := msi_argmin f h p x y hx hy hgt
  have ha0 := mem_pos ha
  have hb0 := mem_neg hb
  have hxa := hxe a
  have hxb := hxe b
  have hA : a = u ∨ a = u' := by
    by_contra hc; push Not at hc
    simp only [CharVec, if_neg hc.1, if_neg hc.2] at hxa; split_ifs at hxa <;> omega
  have hB : b = v ∨ b = v' := by
    by_contra hc; push Not at hc
    simp only [CharVec, if_neg hc.1, if_neg hc.2] at hxb; split_ifs at hxb <;> omega
  refine absurd hlt (not_lt.2 ?_)
  rw [lw_coe f p x fx hfx.symm]
  apply lw_le_of
  intro c hc
  rw [ip_move1]
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
  · have : a1 ≤ c := by rw [hc] at ha1; exact_mod_cast ha1
    rw [pu, pv]; linarith
  · have : a2 ≤ c := by rw [hc] at ha2; exact_mod_cast ha2
    rw [pu, pv']; linarith
  · have e : (fun w => x w - CharVec a w + CharVec b w) =
        (fun w => y w + CharVec u w - CharVec v' w) := by
      funext w; rw [hxe w]; ring
    rw [e] at hc; rw [hc] at hb2
    have : b2 ≤ c := by exact_mod_cast hb2
    have : a1 - b2 ≤ q := le_max_left _ _
    rw [pu', pv]; linarith
  · have e : (fun w => x w - CharVec a w + CharVec b w) =
        (fun w => y w + CharVec u w - CharVec v w) := by
      funext w; rw [hxe w]; ring
    rw [e] at hc; rw [hc] at hb1
    have : b1 ≤ c := by exact_mod_cast hb1
    have : a2 - b1 ≤ q := le_max_right _ _
    rw [pu', pv']; linarith

/-- Case `supp⁺(x - y) = {u}`. -/
theorem case_one {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (h : MSI f) (x y : V → ℤ) (hx : x ∈ DomZ f) (hy : y ∈ DomZ f) (u : V)
    (hu : u ∈ SuppPos x y) (honly : ∀ a ∈ SuppPos x y, a = u)
    (hfail : ∀ v ∈ SuppNeg x y, f x + f y < f (fun w => x w - CharVec u w + CharVec v w) +
      f (fun w => y w + CharVec u w - CharVec v w)) : False := by
  obtain ⟨fx, hfx⟩ := WithTop.ne_top_iff_exists.1 hx
  obtain ⟨fy, hfy⟩ := WithTop.ne_top_iff_exists.1 hy
  have hc : ∀ v, ∃ ab : ℝ × ℝ, v ∈ SuppNeg x y →
      ((ab.1 : WithTop ℝ) ≤ f (fun w => x w - CharVec u w + CharVec v w) ∧
      (ab.2 : WithTop ℝ) ≤ f (fun w => y w + CharVec u w - CharVec v w) ∧ fx + fy < ab.1 + ab.2) := by
    intro v
    by_cases hv : v ∈ SuppNeg x y
    · have F := hfail v hv
      rw [← hfx, ← hfy, ← WithTop.coe_add] at F
      obtain ⟨a, b, h1, h2, h3⟩ := clip _ _ _ F
      exact ⟨(a, b), fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hv⟩
  choose AB hAB using hc
  have hu0 := mem_pos hu
  have key : ∀ t : V → ℝ, (∀ v ∈ SuppNeg x y, fy - (AB v).2 < t v ∧ t v < (AB v).1 - fx) →
      ip (fun w => if w ∈ SuppNeg x y then t w else 0) x -
        ip (fun w => if w ∈ SuppNeg x y then t w else 0) y = fx - fy := by
    intro t ht
    set p : V → ℝ := fun w => if w ∈ SuppNeg x y then t w else 0 with hp
    have pu : p u = 0 := by
      have : u ∉ SuppNeg x y := fun h => by have := mem_neg h; omega
      simp [p, this]
    have h1 : ¬ (LinearWeight f p x > LinearWeight f p y) := by
      intro hgt
      obtain ⟨a, ha, b, hb, hlt, -⟩ := msi_argmin f h p x y hx hy hgt
      have := honly a ha; subst this
      refine absurd hlt (not_lt.2 ?_)
      rw [lw_coe f p x fx hfx.symm]
      apply lw_le_of
      intro c hc
      rw [ip_move1, pu]
      have pb : p b = t b := by simp [p, hb]
      obtain ⟨h1, h2, h3⟩ := hAB b hb
      rw [hc] at h1
      have : (AB b).1 ≤ c := by exact_mod_cast h1
      have := (ht b hb).2
      rw [pb]; linarith
    have h2 : ¬ (LinearWeight f p y > LinearWeight f p x) := by
      intro hgt
      obtain ⟨a, ha, b, hb, hlt, -⟩ := msi_argmin f h p y x hy hx hgt
      have hb' : b ∈ SuppPos x y := hb
      have ha' : a ∈ SuppNeg x y := ha
      have := honly b hb'; subst this
      refine absurd hlt (not_lt.2 ?_)
      rw [lw_coe f p y fy hfy.symm]
      apply lw_le_of
      intro c hc
      rw [ip_move1, pu]
      have pa : p a = t a := by simp [p, ha']
      have e : (fun w => y w - CharVec a w + CharVec b w) =
          (fun w => y w + CharVec b w - CharVec a w) := by funext w; ring
      rw [e] at hc
      obtain ⟨h1, h2, h3⟩ := hAB a ha'
      rw [hc] at h2
      have : (AB a).2 ≤ c := by exact_mod_cast h2
      have := (ht a ha').1
      rw [pa]; linarith
    rw [lw_coe f p x fx hfx.symm, lw_coe f p y fy hfy.symm, gt_iff_lt, WithTop.coe_lt_coe] at h1 h2
    linarith [not_lt.1 h1, not_lt.1 h2]
  set t1 : V → ℝ := fun v => (fy - (AB v).2 + ((AB v).1 - fx)) / 2 with ht1
  set t2 : V → ℝ := fun v => (t1 v + ((AB v).1 - fx)) / 2 with ht2
  have hI : ∀ v ∈ SuppNeg x y, fy - (AB v).2 < (AB v).1 - fx := by
    intro v hv; have := (hAB v hv).2.2; linarith
  have k1 := key t1 (fun v hv => by have := hI v hv; constructor <;> simp only [t1] <;> linarith)
  have k2 := key t2 (fun v hv => by
    have := hI v hv; constructor <;> simp only [t2, t1] <;> linarith)
  rw [ip_sub] at k1 k2
  obtain ⟨v0, hv0⟩ := suppNeg_nonempty f h x y hx hy u hu
  have hlt : ∑ w, (if w ∈ SuppNeg x y then t2 w else 0) * ((x w : ℝ) - (y w : ℝ)) <
      ∑ w, (if w ∈ SuppNeg x y then t1 w else 0) * ((x w : ℝ) - (y w : ℝ)) := by
    apply Finset.sum_lt_sum
    · intro w _
      by_cases hw : w ∈ SuppNeg x y
      · rw [if_pos hw, if_pos hw]
        have h0 : (x w : ℝ) < y w := by exact_mod_cast mem_neg hw
        have := hI w hw
        have : t1 w ≤ t2 w := by simp only [t2, t1]; linarith
        nlinarith
      · rw [if_neg hw, if_neg hw]
    · refine ⟨v0, Finset.mem_univ _, ?_⟩
      rw [if_pos hv0, if_pos hv0]
      have h0 : (x v0 : ℝ) < y v0 := by exact_mod_cast mem_neg hv0
      have := hI v0 hv0
      have : t1 v0 < t2 v0 := by simp only [t2, t1]; linarith
      nlinarith
  linarith

theorem between_abs (a b c : ℤ) (h : (b ≤ a ∧ a ≤ c) ∨ (c ≤ a ∧ a ≤ b)) :
    |a - b| + |c - a| = |c - b| := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg (by omega : (0:ℤ) ≤ a - b), abs_of_nonneg (by omega : (0:ℤ) ≤ c - a),
      abs_of_nonneg (by omega : (0:ℤ) ≤ c - b)]; ring
  · rw [abs_of_nonpos (by omega : a - b ≤ (0:ℤ)), abs_of_nonpos (by omega : c - a ≤ (0:ℤ)),
      abs_of_nonpos (by omega : c - b ≤ (0:ℤ))]; ring

theorem dist_lt {V : Type*} [Fintype V] [DecidableEq V] (x y : V → ℤ) (u u' v v' : V)
    (hu : y u < x u) (hu' : y u' < x u') (huu : u ≠ u') (hv : x v < y v) (hv1 : x v' < y v')
    (hvv : v = v' → x v + 1 < y v) (nuv : u ≠ v) (nuv' : u ≠ v') (nu'v : u' ≠ v) (nu'v' : u' ≠ v')
    (hne : x ≠ fun w => y w + CharVec u' w - CharVec v w + CharVec u w - CharVec v' w) :
    ∑ w, |(y w + CharVec u' w - CharVec v w + CharVec u w - CharVec v' w) - y w| <
      ∑ w, |x w - y w| := by
  have key : ∀ w, |(y w + CharVec u' w - CharVec v w + CharVec u w - CharVec v' w) - y w| +
      |x w - (y w + CharVec u' w - CharVec v w + CharVec u w - CharVec v' w)| = |x w - y w| := by
    intro w
    apply between_abs
    by_cases h1 : w = u
    · subst h1
      simp only [CharVec, if_pos rfl, if_neg huu, if_neg nuv, if_neg nuv']
      left; omega
    by_cases h2 : w = u'
    · subst h2
      simp only [CharVec, if_pos rfl, if_neg h1, if_neg nu'v, if_neg nu'v']
      left; omega
    by_cases h3 : w = v
    · subst h3
      by_cases h4 : w = v'
      · subst h4
        simp only [CharVec, if_pos rfl, if_neg h1, if_neg h2]
        have := hvv rfl
        right; omega
      · simp only [CharVec, if_pos rfl, if_neg h1, if_neg h2, if_neg h4]
        right; omega
    by_cases h4 : w = v'
    · subst h4
      simp only [CharVec, if_pos rfl, if_neg h1, if_neg h2, if_neg h3]
      right; omega
    · simp only [CharVec, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
      by_cases h5 : y w ≤ x w
      · left; omega
      · right; omega
  obtain ⟨w0, hw0⟩ := Function.ne_iff.1 hne
  have hpos : 0 < ∑ w, |x w - (y w + CharVec u' w - CharVec v w + CharVec u w - CharVec v' w)| :=
    Finset.sum_pos' (fun w _ => abs_nonneg _) ⟨w0, Finset.mem_univ _, abs_pos.2 (sub_ne_zero.2 hw0)⟩
  have hsum := Finset.sum_congr rfl (fun w (_ : w ∈ Finset.univ) => key w)
  rw [Finset.sum_add_distrib] at hsum
  linarith

theorem sum_abs_lt {V : Type*} [Fintype V] [DecidableEq V] (x y : V → ℤ) (u v : V)
    (hu : y u < x u) (hv : x v < y v) :
    (∑ w, |x w - (y w + CharVec u w - CharVec v w)|) < ∑ w, |x w - y w| := by
  have huv : u ≠ v := by rintro rfl; omega
  apply Finset.sum_lt_sum
  · intro w _
    have hcu : CharVec u w = if w = u then 1 else 0 := rfl
    have hcv : CharVec v w = if w = v then 1 else 0 := rfl
    have A := abs_cases (x w - (y w + CharVec u w - CharVec v w))
    have B := abs_cases (x w - y w)
    split_ifs at hcu hcv with h1 h2 h2
    · exact absurd (h1.symm.trans h2) huv
    · subst h1; omega
    · subst h2; omega
    · omega
  · refine ⟨u, Finset.mem_univ _, ?_⟩
    have hcu : CharVec u u = 1 := if_pos rfl
    have hcv : CharVec v u = 0 := if_neg huv
    have A := abs_cases (x u - (y u + CharVec u u - CharVec v u))
    have B := abs_cases (x u - y u)
    omega

theorem lw_top_of {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) (z : V → ℤ)
    (hz : f z = ⊤) : LinearWeight f p z = ⊤ := by
  simp [LinearWeight, hz]

/-- (M-SI[Z]) implies (M-EXC[Z]) directly (no local exchange theorem needed). -/
theorem msi_mexchange {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (h : MSI f) : MExchangeAxiom f := by
  suffices H : ∀ n : ℕ, ∀ x y : V → ℤ, x ∈ DomZ f → y ∈ DomZ f →
      (∑ w, |x w - y w|) < (n : ℤ) → ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
        f x + f y ≥ f (fun w => x w - CharVec u w + CharVec v w) +
          f (fun w => y w + CharVec u w - CharVec v w) by
    intro x hx y hy u hu
    refine H ((∑ w, |x w - y w|).toNat + 1) x y hx hy ?_ u hu
    have := Int.self_le_toNat (∑ w, |x w - y w|)
    push_cast; omega
  intro n
  induction n with
  | zero =>
    intro x y _ _ hn
    have : 0 ≤ ∑ w, |x w - y w| := Finset.sum_nonneg (fun w _ => abs_nonneg _)
    push_cast at hn; omega
  | succ n ih =>
  intro x y hx hy hn u hu
  by_contra hcon
  have hfail : ∀ v ∈ SuppNeg x y, f x + f y < f (fun w => x w - CharVec u w + CharVec v w) +
      f (fun w => y w + CharVec u w - CharVec v w) :=
    fun v hv => lt_of_not_ge (fun hge => hcon ⟨v, hv, hge⟩)
  by_cases hA : ∃ u1 ∈ SuppPos x y, u1 ≠ u
  swap
  · push Not at hA
    exact case_one f h x y hx hy u hu hA hfail
  obtain ⟨u1, hu1, hu1u⟩ := hA
  obtain ⟨fx, hfx⟩ := WithTop.ne_top_iff_exists.1 hx
  obtain ⟨fy, hfy⟩ := WithTop.ne_top_iff_exists.1 hy
  have hc : ∀ v, ∃ ab : ℝ × ℝ, v ∈ SuppNeg x y →
      ((ab.1 : WithTop ℝ) ≤ f (fun w => x w - CharVec u w + CharVec v w) ∧
      (ab.2 : WithTop ℝ) ≤ f (fun w => y w + CharVec u w - CharVec v w) ∧ fx + fy < ab.1 + ab.2) := by
    intro v
    by_cases hv : v ∈ SuppNeg x y
    · have F := hfail v hv
      rw [← hfx, ← hfy, ← WithTop.coe_add] at F
      obtain ⟨a, b, h1, h2, h3⟩ := clip _ _ _ F
      exact ⟨(a, b), fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hv⟩
  choose AB hAB using hc
  set t : V → ℝ := fun v => (fy - (AB v).2 + ((AB v).1 - fx)) / 2 with ht_def
  have ht : ∀ v ∈ SuppNeg x y, fy - (AB v).2 < t v ∧ t v < (AB v).1 - fx := by
    intro v hv
    have := (hAB v hv).2.2
    constructor <;> simp only [t] <;> linarith
  have hu0 := mem_pos hu
  have hu10 := mem_pos hu1
  have notneg : ∀ a ∈ SuppPos x y, a ∉ SuppNeg x y := fun a ha hn => by
    have := mem_pos ha; have := mem_neg hn; omega
  set S0 : ℝ := ∑ w, (if w ∈ SuppNeg x y then t w * ((x w : ℝ) - (y w : ℝ)) else 0) with hS0
  set K : ℝ := |fx - fy - S0| + 1 with hK
  have hK1 : 1 ≤ K := by have := abs_nonneg (fx - fy - S0); linarith
  set p : V → ℝ := fun w => if w ∈ SuppNeg x y then t w else
    if w ∈ SuppPos x y ∧ w ≠ u then K else 0 with hp
  have pu : p u = 0 := by simp [p, notneg u hu]
  have pneg : ∀ v ∈ SuppNeg x y, p v = t v := fun v hv => by simp [p, hv]
  have ppos : ∀ a ∈ SuppPos x y, a ≠ u → p a = K := fun a ha hau => by
    simp [p, notneg a ha, ha, hau]
  -- g y > g x
  have hgt : LinearWeight f p y > LinearWeight f p x := by
    rw [lw_coe f p x fx hfx.symm, lw_coe f p y fy hfy.symm, gt_iff_lt, WithTop.coe_lt_coe]
    have hsum : S0 + K ≤ ip p x - ip p y := by
      rw [ip_sub]
      have : S0 + K = ∑ w, ((if w ∈ SuppNeg x y then t w * ((x w : ℝ) - (y w : ℝ)) else 0) +
          (if w = u1 then K else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
      rw [this]
      apply Finset.sum_le_sum
      intro w _
      by_cases hw : w ∈ SuppNeg x y
      · have hwu1 : w ≠ u1 := fun e => notneg u1 hu1 (e ▸ hw)
        rw [if_pos hw, if_neg hwu1, pneg w hw]; simp
      · rw [if_neg hw]
        by_cases hw2 : w ∈ SuppPos x y ∧ w ≠ u
        · rw [ppos w hw2.1 hw2.2]
          have h0 : (y w : ℝ) + 1 ≤ x w := by
            have := mem_pos hw2.1; exact_mod_cast (by omega : y w + 1 ≤ x w)
          split_ifs <;> nlinarith
        · have hwu1 : w ≠ u1 := fun e => hw2 ⟨e ▸ hu1, e ▸ hu1u⟩
          have : p w = 0 := by simp [p, hw, hw2]
          rw [if_neg hwu1, this]; simp
    have := le_abs_self (fx - fy - S0)
    linarith
  obtain ⟨a, ha, b, hb, hlt, hmin⟩ := msi_argmin f h p y x hy hx hgt
  have ha' : a ∈ SuppNeg x y := ha
  have hb' : b ∈ SuppPos x y := hb
  have ha0 := mem_neg ha'
  have hb0 := mem_pos hb'
  have hy'eq : (fun w => y w - CharVec a w + CharVec b w) =
      (fun w => y w + CharVec b w - CharVec a w) := by funext w; ring
  have hbu : b ≠ u := by
    intro hbu
    subst hbu
    refine absurd hlt (not_lt.2 ?_)
    rw [lw_coe f p y fy hfy.symm]
    apply lw_le_of
    intro c hc
    rw [ip_move1, pu, pneg a ha']
    rw [hy'eq] at hc
    have h2 := (hAB a ha').2.1
    rw [hc] at h2
    have : (AB a).2 ≤ c := by exact_mod_cast h2
    have := (ht a ha').1
    linarith
  -- the improving y-move y' = y - χa + χb
  set y' : V → ℤ := fun w => y w + CharVec b w - CharVec a w with hy'
  have hlt' : LinearWeight f p y' < LinearWeight f p y := by rw [← hy'eq]; exact hlt
  have hy'dom : y' ∈ DomZ f := by
    intro htop
    rw [lw_top_of f p y' htop] at hlt'
    exact not_top_lt hlt'
  obtain ⟨fy', hfy'⟩ := WithTop.ne_top_iff_exists.1 hy'dom
  have nab : a ≠ b := fun e => notneg b hb' (e ▸ ha')
  have nua : u ≠ a := fun e => notneg u hu (e ▸ ha')
  have hy'u : y' u = y u := by
    simp only [y', CharVec, if_neg (Ne.symm hbu), if_neg nua]; ring
  have hu' : u ∈ SuppPos x y' := Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hy'u]; exact hu0⟩
  have hd1 : (∑ w, |x w - y' w|) < ∑ w, |x w - y w| := sum_abs_lt x y b a hb0 ha0
  obtain ⟨v', hv', E1⟩ := ih x y' hx hy'dom (by push_cast at hn ⊢; omega) u hu'
  have hv'0 := mem_neg hv'
  have nbv' : b ≠ v' := by
    intro e; subst e
    simp only [y', CharVec, if_pos rfl, if_neg (Ne.symm nab)] at hv'0
    omega
  have hy'v' : y' v' = y v' - CharVec a v' := by
    simp only [y', CharVec, if_neg (Ne.symm nbv')]; ring
  have hv'S : v' ∈ SuppNeg x y := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have : 0 ≤ CharVec a v' := by simp only [CharVec]; split_ifs <;> omega
    omega
  -- y'' = y' + χu - χv'
  have hxtop1 : f (fun w => x w - CharVec u w + CharVec v' w) ≠ ⊤ := by
    intro htop; rw [htop, ← hfx, ← hfy'] at E1; simp at E1
  have hxtop2 : f (fun w => y' w + CharVec u w - CharVec v' w) ≠ ⊤ := by
    intro htop; rw [htop, ← hfx, ← hfy'] at E1; simp at E1
  obtain ⟨a1, ha1⟩ := WithTop.ne_top_iff_exists.1 hxtop1
  obtain ⟨b1, hb1⟩ := WithTop.ne_top_iff_exists.1 hxtop2
  have E1r : a1 + b1 ≤ fx + fy' := by
    rw [← ha1, ← hb1, ← hfx, ← hfy'] at E1; exact_mod_cast E1
  have hA1 : (AB v').1 ≤ a1 := by
    have := (hAB v' hv'S).1; rw [← ha1] at this; exact_mod_cast this
  have htv' := (ht v' hv'S).2
  set y'' : V → ℤ := fun w => y' w + CharVec u w - CharVec v' w with hy''
  have hg2 : LinearWeight f p y'' < LinearWeight f p y' := by
    rw [lw_coe f p y'' b1 hb1.symm, lw_coe f p y' fy' hfy'.symm, WithTop.coe_lt_coe, hy'', ip_move2,
      pu, pneg v' hv'S]
    linarith
  have hy''dom : y'' ∈ DomZ f := by
    show f y'' ≠ ⊤; rw [← hb1]; exact WithTop.coe_ne_top
  by_cases hxe : x = fun w => y w + CharVec b w - CharVec a w + CharVec u w - CharVec v' w
  · exact local_case f h x y hx hy u b a v' hu hb' (Ne.symm hbu) ha' hv'S
      (fun w => by have := congrFun hxe w; rw [this]; ring)
      (hfail a ha') (hfail v' hv'S)
  -- the non-local case
  have hvv : a = v' → x a + 1 < y a := by
    intro e; subst e
    have e2 := hy'v'
    have : CharVec a a = 1 := if_pos rfl
    omega
  have nuv' : u ≠ v' := fun e => notneg u hu (e ▸ hv'S)
  have hd2 := dist_lt x y u b a v' hu0 hb0 (Ne.symm hbu) ha0 (mem_neg hv'S) hvv nua nuv'
    (Ne.symm nab) nbv' hxe
  have hu'' : u ∈ SuppPos y'' y := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have e1 : y'' u = y' u + CharVec u u - CharVec v' u := rfl
    have : CharVec u u = 1 := if_pos rfl
    have : CharVec v' u = 0 := if_neg nuv'
    omega
  have hd2' : ∑ w, |y'' w - y w| < ∑ w, |x w - y w| := hd2
  obtain ⟨w, hw, E2⟩ := ih y'' y hy''dom hy (by push_cast at hn ⊢; omega) u hu''
  have hw0 := mem_neg hw
  have hwav : w = a ∨ w = v' := by
    by_contra hc; push Not at hc
    have e : y'' w = y w := by
      show y w + CharVec b w - CharVec a w + CharVec u w - CharVec v' w = y w
      have h1 : CharVec a w = 0 := if_neg hc.1
      have h2 : CharVec v' w = 0 := if_neg hc.2
      have h3 : 0 ≤ CharVec b w := by simp only [CharVec]; split_ifs <;> omega
      have h4 : 0 ≤ CharVec u w := by simp only [CharVec]; split_ifs <;> omega
      have : y'' w < y w := hw0
      simp only [y'', y'] at this
      omega
    exact absurd hw0 (by rw [e]; exact lt_irrefl _)
  have hwS : w ∈ SuppNeg x y := by rcases hwav with rfl | rfl <;> assumption
  have hmtop1 : f (fun z => y'' z - CharVec u z + CharVec w z) ≠ ⊤ := by
    intro htop; rw [htop, ← hb1, ← hfy] at E2; simp at E2
  have hmtop2 : f (fun z => y z + CharVec u z - CharVec w z) ≠ ⊤ := by
    intro htop; rw [htop, ← hb1, ← hfy] at E2; simp at E2
  obtain ⟨c1, hc1⟩ := WithTop.ne_top_iff_exists.1 hmtop1
  obtain ⟨c2, hc2⟩ := WithTop.ne_top_iff_exists.1 hmtop2
  have E2r : c1 + c2 ≤ b1 + fy := by
    rw [← hc1, ← hc2, ← hb1, ← hfy] at E2; exact_mod_cast E2
  have hB2 : (AB w).2 ≤ c2 := by
    have := (hAB w hwS).2.1; rw [← hc2] at this; exact_mod_cast this
  have htw := (ht w hwS).1
  have hg3 : LinearWeight f p (fun z => y'' z - CharVec u z + CharVec w z) <
      LinearWeight f p y'' := by
    rw [lw_coe f p _ c1 hc1.symm, lw_coe f p y'' b1 hb1.symm, WithTop.coe_lt_coe, ip_move1,
      pu, pneg w hwS]
    linarith
  -- m is a y-move through b, so it is at least g y'
  have hmove : ∃ a2 ∈ SuppPos y x, (fun z => y'' z - CharVec u z + CharVec w z) =
      (fun z => y z - CharVec a2 z + CharVec b z) := by
    rcases hwav with rfl | rfl
    · exact ⟨v', hv'S, by funext z; simp only [y'', y']; ring⟩
    · exact ⟨a, ha, by funext z; simp only [y'', y']; ring⟩
  obtain ⟨a2, ha2, hm⟩ := hmove
  have hge := hmin a2 ha2 b hb
  rw [hy'eq, ← hm] at hge
  exact absurd (lt_of_lt_of_le (hg3.trans hg2) hge) (lt_irrefl _)

/-! ### The M♮ half: (M♮-SI) ⇒ (M-SI) for the lift -/

theorem ip_add1 {V : Type*} [Fintype V] [DecidableEq V] (p : V → ℝ) (z : V → ℤ) (a : V) :
    ip p (fun w => z w + CharVec a w) = ip p z + p a := by
  simp only [ip, CharVec]
  push_cast
  simp only [mul_add, Finset.sum_add_distrib]
  simp [mul_ite]

theorem ip_sub1 {V : Type*} [Fintype V] [DecidableEq V] (p : V → ℝ) (z : V → ℤ) (a : V) :
    ip p (fun w => z w - CharVec a w) = ip p z - p a := by
  simp only [ip, CharVec]
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp [mul_ite]

/-- Two-point inequality from (M♮-SI). -/
theorem two_point {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (h : MNatSI f) (x : V → ℤ) (u v : V) (huv : u ≠ v)
    (hX : (fun w => x w + CharVec v w) ∈ DomZ f) (hY : (fun w => x w - CharVec u w) ∈ DomZ f) :
    f x + f (fun w => x w - CharVec u w + CharVec v w) ≤
      f (fun w => x w - CharVec u w) + f (fun w => x w + CharVec v w) := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨fX, hfX⟩ := WithTop.ne_top_iff_exists.1 hX
  obtain ⟨fY, hfY⟩ := WithTop.ne_top_iff_exists.1 hY
  rw [← hfX, ← hfY, ← WithTop.coe_add] at hcon
  obtain ⟨xh, zh, hxh, hzh, hlt⟩ := clip _ _ _ hcon
  set X : V → ℤ := fun w => x w + CharVec v w with hXd
  set Y : V → ℤ := fun w => x w - CharVec u w with hYd
  set p : V → ℝ := fun w => if w = u then fX - zh else if w = v then fX - xh else 0 with hp
  have pu : p u = fX - zh := by simp [p]
  have pv : p v = fX - xh := by simp [p, Ne.symm huv]
  have ipX : ip p X = ip p x + p v := ip_add1 p x v
  have ipY : ip p Y = ip p x - p u := ip_sub1 p x u
  have hgt : LinearWeight f p X > LinearWeight f p Y := by
    rw [lw_coe f p X fX hfX.symm, lw_coe f p Y fY hfY.symm, gt_iff_lt, WithTop.coe_lt_coe, ipX, ipY,
      pu, pv]
    linarith
  have H := h p X hX Y hY hgt
  refine absurd H (not_lt.2 (Finset.le_inf (fun a ha => Finset.le_inf (fun b hb => ?_))))
  have hbn : b = none := by
    rcases Finset.mem_insert.1 hb with hb | hb
    · exact hb
    · obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hb
      have := mem_neg hb'
      simp only [X, Y, CharVec] at this
      split_ifs at this <;> omega
  subst hbn
  rcases Finset.mem_insert.1 ha with ha | ha
  · subst ha
    have e : (fun w => X w - CharVecOpt (none : Option V) w + CharVecOpt (none : Option V) w) = X := by
      funext w; simp [CharVecOpt]
    rw [e]
  · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 ha
    have ha0 := mem_pos ha'
    have hA : a' = u ∨ a' = v := by
      by_contra hc; push Not at hc
      simp only [X, Y, CharVec, if_neg hc.1, if_neg hc.2] at ha0; omega
    rw [lw_coe f p X fX hfX.symm]
    apply lw_le_of
    intro c hc
    rcases hA with rfl | rfl
    · have e : (fun w => X w - CharVecOpt (some a') w + CharVecOpt (none : Option V) w) =
          (fun w => x w - CharVec a' w + CharVec v w) := by
        funext w; simp [CharVecOpt, X]; ring
      rw [e] at hc ⊢
      rw [hc] at hzh
      have : zh ≤ c := by exact_mod_cast hzh
      rw [ip_move1, ipX, pu]; linarith
    · have e : (fun w => X w - CharVecOpt (some a') w + CharVecOpt (none : Option V) w) = x := by
        funext w; simp [CharVecOpt, X]
      rw [e] at hc ⊢
      rw [hc] at hxh
      have : xh ≤ c := by exact_mod_cast hxh
      rw [ipX, pv]; linarith

theorem sep (A B : Finset ℝ) (h : ∀ a ∈ A, ∀ b ∈ B, a ≤ b) :
    ∃ c : ℝ, (∀ a ∈ A, a ≤ c) ∧ ∀ b ∈ B, c ≤ b := by
  by_cases hA : A.Nonempty
  · exact ⟨A.max' hA, fun a ha => A.le_max' a ha, fun b hb => A.max'_le hA b (fun a ha => h a ha b hb)⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    by_cases hB : B.Nonempty
    · exact ⟨B.min' hB, by simp [hA], fun b hb => B.min'_le b hb⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hB
      exact ⟨0, by simp [hA], by simp [hB]⟩

theorem ip_shift {V : Type*} [Fintype V] (p : V → ℝ) (c : ℝ) (z : V → ℤ) :
    ip (fun w => p w + c) z = ip p z + c * ∑ w, (z w : ℝ) := by
  simp only [ip, add_mul, Finset.sum_add_distrib, Finset.mul_sum]

/-- If no move allowed for the lift improves, (M♮-SI) is violated. -/
theorem mnatsi_allowed {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (h : MNatSI f) (p : V → ℝ) (x y : V → ℤ) (hx : x ∈ DomZ f) (hy : y ∈ DomZ f)
    (hgt : LinearWeight f p x > LinearWeight f p y)
    (H1 : ∀ u ∈ SuppPos x y, ∀ v ∈ SuppNeg x y,
      LinearWeight f p x ≤ LinearWeight f p (fun w => x w - CharVec u w + CharVec v w))
    (H2 : (∑ w, y w) < ∑ w, x w → ∀ u ∈ SuppPos x y,
      LinearWeight f p x ≤ LinearWeight f p (fun w => x w - CharVec u w))
    (H3 : (∑ w, x w) < ∑ w, y w → ∀ v ∈ SuppNeg x y,
      LinearWeight f p x ≤ LinearWeight f p (fun w => x w + CharVec v w)) : False := by
  obtain ⟨fx, hfx⟩ := WithTop.ne_top_iff_exists.1 hx
  obtain ⟨fy, hfy⟩ := WithTop.ne_top_iff_exists.1 hy
  have hR : ∀ u, ∃ r : ℝ, f (fun w => x w - CharVec u w) ≠ ⊤ → f (fun w => x w - CharVec u w) = r :=
    fun u => by
      by_cases hh : f (fun w => x w - CharVec u w) = ⊤
      · exact ⟨0, fun h' => absurd hh h'⟩
      · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hh; exact ⟨r, fun _ => hr.symm⟩
  have hQ : ∀ v, ∃ r : ℝ, f (fun w => x w + CharVec v w) ≠ ⊤ → f (fun w => x w + CharVec v w) = r :=
    fun v => by
      by_cases hh : f (fun w => x w + CharVec v w) = ⊤
      · exact ⟨0, fun h' => absurd hh h'⟩
      · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hh; exact ⟨r, fun _ => hr.symm⟩
  choose R hR using hR
  choose Q hQ using hQ
  set A : Finset ℝ := ((SuppPos x y).filter (fun u => f (fun w => x w - CharVec u w) ≠ ⊤)).image
    (fun u => fx - R u - p u) ∪ (if (∑ w, x w) < ∑ w, y w then {0} else ∅) with hA
  set B : Finset ℝ := ((SuppNeg x y).filter (fun v => f (fun w => x w + CharVec v w) ≠ ⊤)).image
    (fun v => Q v - p v - fx) ∪ (if (∑ w, y w) < ∑ w, x w then {0} else ∅) with hB
  -- real forms of H1, H2, H3
  have H1r : ∀ u ∈ SuppPos x y, ∀ v ∈ SuppNeg x y, ∀ s : ℝ,
      f (fun w => x w - CharVec u w + CharVec v w) = s → fx ≤ s + p u - p v := by
    intro u hu v hv s hs
    have := H1 u hu v hv
    rw [lw_coe f p x fx hfx.symm, lw_coe f p _ s hs, WithTop.coe_le_coe, ip_move1] at this
    linarith
  have H2r : (∑ w, y w) < ∑ w, x w → ∀ u ∈ SuppPos x y, ∀ s : ℝ,
      f (fun w => x w - CharVec u w) = s → fx ≤ s + p u := by
    intro hs0 u hu s hs
    have := H2 hs0 u hu
    rw [lw_coe f p x fx hfx.symm, lw_coe f p _ s hs, WithTop.coe_le_coe, ip_sub1] at this
    linarith
  have H3r : (∑ w, x w) < ∑ w, y w → ∀ v ∈ SuppNeg x y, ∀ s : ℝ,
      f (fun w => x w + CharVec v w) = s → fx ≤ s - p v := by
    intro hs0 v hv s hs
    have := H3 hs0 v hv
    rw [lw_coe f p x fx hfx.symm, lw_coe f p _ s hs, WithTop.coe_le_coe, ip_add1] at this
    linarith
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b := by
    intro a ha b hb
    rcases Finset.mem_union.1 ha with ha | ha <;> rcases Finset.mem_union.1 hb with hb | hb
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hb
      obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
      obtain ⟨hv1, hv2⟩ := Finset.mem_filter.1 hv
      have huv : u ≠ v := fun e => by have := mem_pos hu1; have := mem_neg (e ▸ hv1); omega
      have TP := two_point f h x u v huv hv2 hu2
      rw [hR u hu2, hQ v hv2, ← hfx, ← WithTop.coe_add] at TP
      have hz : f (fun w => x w - CharVec u w + CharVec v w) ≠ ⊤ := by
        intro htop; rw [htop] at TP; simp at TP
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hz
      rw [← hs, ← WithTop.coe_add] at TP
      have TP' : fx + s ≤ R u + Q v := by exact_mod_cast TP
      have := H1r u hu1 v hv1 s hs.symm
      linarith
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
      split_ifs at hb with hc
      · rw [Finset.mem_singleton] at hb; subst hb
        have := H2r hc u hu1 (R u) (hR u hu2)
        linarith
      · simp at hb
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hb
      obtain ⟨hv1, hv2⟩ := Finset.mem_filter.1 hv
      split_ifs at ha with hc
      · rw [Finset.mem_singleton] at ha; subst ha
        have := H3r hc v hv1 (Q v) (hQ v hv2)
        linarith
      · simp at ha
    · split_ifs at ha hb with hc1 hc2 <;> simp at ha hb
      omega
  obtain ⟨c, hcA, hcB⟩ := sep A B hAB
  set pc : V → ℝ := fun w => p w + c with hpc
  have hsign : c * ((∑ w, (x w : ℝ)) - ∑ w, (y w : ℝ)) ≤ 0 := by
    rcases lt_trichotomy (∑ w, x w) (∑ w, y w) with hl | he | hg
    · have h0 : (0:ℝ) ≤ c := hcA 0 (Finset.mem_union.2 (Or.inr (by simp [hl])))
      have : (∑ w, (x w : ℝ)) < ∑ w, (y w : ℝ) := by exact_mod_cast hl
      nlinarith
    · have : (∑ w, (x w : ℝ)) = ∑ w, (y w : ℝ) := by exact_mod_cast he
      rw [this]; simp
    · have h0 : c ≤ 0 := hcB 0 (Finset.mem_union.2 (Or.inr (by simp [hg])))
      have : (∑ w, (y w : ℝ)) < ∑ w, (x w : ℝ) := by exact_mod_cast hg
      nlinarith
  have hgtc : LinearWeight f pc x > LinearWeight f pc y := by
    rw [lw_coe f p x fx hfx.symm, lw_coe f p y fy hfy.symm, gt_iff_lt, WithTop.coe_lt_coe] at hgt
    rw [lw_coe f pc x fx hfx.symm, lw_coe f pc y fy hfy.symm, gt_iff_lt, WithTop.coe_lt_coe, ip_shift,
      ip_shift]
    nlinarith
  have Hm := h pc x hx y hy hgtc
  refine absurd Hm (not_lt.2 (Finset.le_inf (fun a ha => Finset.le_inf (fun b hb => ?_))))
  rw [lw_coe f pc x fx hfx.symm]
  apply lw_le_of
  intro s hs
  rcases Finset.mem_insert.1 ha with ha | ha <;> rcases Finset.mem_insert.1 hb with hb | hb
  · subst ha; subst hb
    have e : (fun w => x w - CharVecOpt (none : Option V) w + CharVecOpt (none : Option V) w) = x := by
      funext w; simp [CharVecOpt]
    rw [e] at hs ⊢
    rw [hs] at hfx
    have : fx = s := by exact_mod_cast hfx
    linarith
  · subst ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hb
    have e : (fun w => x w - CharVecOpt (none : Option V) w + CharVecOpt (some v) w) =
        (fun w => x w + CharVec v w) := by
      funext w; simp [CharVecOpt]
    rw [e] at hs ⊢
    have hne : f (fun w => x w + CharVec v w) ≠ ⊤ := by rw [hs]; exact WithTop.coe_ne_top
    have hmem : Q v - p v - fx ∈ B := Finset.mem_union.2 (Or.inl (Finset.mem_image.2
      ⟨v, Finset.mem_filter.2 ⟨hv, hne⟩, rfl⟩))
    have := hcB _ hmem
    have hQs : Q v = s := by have := hQ v hne; rw [hs] at this; exact_mod_cast this.symm
    rw [ip_add1]; simp only [pc]; linarith
  · subst hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ha
    have e : (fun w => x w - CharVecOpt (some u) w + CharVecOpt (none : Option V) w) =
        (fun w => x w - CharVec u w) := by
      funext w; simp [CharVecOpt]
    rw [e] at hs ⊢
    have hne : f (fun w => x w - CharVec u w) ≠ ⊤ := by rw [hs]; exact WithTop.coe_ne_top
    have hmem : fx - R u - p u ∈ A := Finset.mem_union.2 (Or.inl (Finset.mem_image.2
      ⟨u, Finset.mem_filter.2 ⟨hu, hne⟩, rfl⟩))
    have := hcA _ hmem
    have hRs : R u = s := by have := hR u hne; rw [hs] at this; exact_mod_cast this.symm
    rw [ip_sub1]; simp only [pc]; linarith
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hb
    have e : (fun w => x w - CharVecOpt (some u) w + CharVecOpt (some v) w) =
        (fun w => x w - CharVec u w + CharVec v w) := by
      funext w; simp [CharVecOpt]
    rw [e] at hs ⊢
    have := H1r u hu v hv s hs
    rw [ip_move1]; simp only [pc]; linarith

theorem lw_lift_gen {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (q : Option V → ℝ)
    (z : Option V → ℤ) (hz : z none = -(∑ v, z (some v))) :
    LinearWeight (LiftedFunction f) q z =
      LinearWeight f (fun v => q (some v) - q none) (fun v => z (some v)) := by
  have e : (-(q none * ((z none : ℤ) : ℝ) + ∑ v, q (some v) * ((z (some v) : ℤ) : ℝ))) =
      -(∑ v, (q (some v) - q none) * ((z (some v) : ℤ) : ℝ)) := by
    rw [hz]; push_cast
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
  simp only [LinearWeight, P19bd.lifted_eval f z hz, Fintype.sum_option, e]

theorem lift_hyp {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (Z : Option V → ℤ)
    (hZ : Z ∈ DomZ (LiftedFunction f)) : Z none = -(∑ v, Z (some v)) := by
  by_contra hc
  exact hZ (by simp [LiftedFunction, hc])

/-- (M♮-SI) for `f` gives (M-SI) for its lift. -/
theorem mnatsi_msi_lift {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (h : MNatSI f) : MSI (LiftedFunction f) := by
  intro q X hX Y hY hlt
  have hXe : X = P19bd.liftPt (fun v => X (some v)) := funext fun o => by
    cases o with
    | none => simp [P19bd.liftPt, lift_hyp f X hX]
    | some v => rfl
  have hYe : Y = P19bd.liftPt (fun v => Y (some v)) := funext fun o => by
    cases o with
    | none => simp [P19bd.liftPt, lift_hyp f Y hY]
    | some v => rfl
  generalize (fun v => X (some v)) = x at hXe
  generalize (fun v => Y (some v)) = y at hYe
  subst hXe hYe
  have hx : x ∈ DomZ f := by
    have := hX; simp only [DomZ, Set.mem_setOf_eq] at this ⊢
    rwa [P19bd.lifted_eval f _ (by simp [P19bd.liftPt])] at this
  have hy : y ∈ DomZ f := by
    have := hY; simp only [DomZ, Set.mem_setOf_eq] at this ⊢
    rwa [P19bd.lifted_eval f _ (by simp [P19bd.liftPt])] at this
  set p : V → ℝ := fun v => q (some v) - q none with hp
  have LWX : ∀ a b : Option V, LinearWeight (LiftedFunction f) q
      (fun o => P19bd.liftPt x o - CharVec a o + CharVec b o) =
      LinearWeight f p (fun w => x w - CharVecOpt a w + CharVecOpt b w) := by
    intro a b
    rw [lw_lift_gen f q _ (P19bd.move_ok x a b)]
    congr 1
    funext w
    simp only [P19bd.liftPt, Option.elim_some, P19bd.charVec_some]
  have LW0 : ∀ z : V → ℤ, LinearWeight (LiftedFunction f) q (P19bd.liftPt z) = LinearWeight f p z := by
    intro z; rw [lw_lift_gen f q _ (by simp [P19bd.liftPt])]; rfl
  by_contra hcon
  rw [gt_iff_lt, not_lt] at hcon
  have hgt : LinearWeight f p x > LinearWeight f p y := by rw [← LW0, ← LW0]; exact hlt
  have key : ∀ a ∈ SuppPos (P19bd.liftPt x) (P19bd.liftPt y), ∀ b ∈ SuppNeg (P19bd.liftPt x) (P19bd.liftPt y),
      LinearWeight f p x ≤ LinearWeight f p (fun w => x w - CharVecOpt a w + CharVecOpt b w) := by
    intro a ha b hb
    have := hcon.trans ((Finset.inf_le ha).trans (Finset.inf_le hb))
    rwa [LWX, LW0] at this
  apply mnatsi_allowed f h p x y hx hy hgt
  · intro u hu v hv
    have hu' : some u ∈ SuppPos (P19bd.liftPt x) (P19bd.liftPt y) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa [P19bd.liftPt] using mem_pos hu⟩
    have hv' : some v ∈ SuppNeg (P19bd.liftPt x) (P19bd.liftPt y) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa [P19bd.liftPt] using mem_neg hv⟩
    have := key _ hu' _ hv'
    have e : (fun w => x w - CharVecOpt (some u) w + CharVecOpt (some v) w) =
        (fun w => x w - CharVec u w + CharVec v w) := by funext w; simp [CharVecOpt]
    rwa [e] at this
  · intro hs u hu
    have hu' : some u ∈ SuppPos (P19bd.liftPt x) (P19bd.liftPt y) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa [P19bd.liftPt] using mem_pos hu⟩
    have hn : (none : Option V) ∈ SuppNeg (P19bd.liftPt x) (P19bd.liftPt y) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [P19bd.liftPt]; omega⟩
    have := key _ hu' _ hn
    have e : (fun w => x w - CharVecOpt (some u) w + CharVecOpt (none : Option V) w) =
        (fun w => x w - CharVec u w) := by funext w; simp [CharVecOpt]
    rwa [e] at this
  · intro hs v hv
    have hv' : some v ∈ SuppNeg (P19bd.liftPt x) (P19bd.liftPt y) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa [P19bd.liftPt] using mem_neg hv⟩
    have hn : (none : Option V) ∈ SuppPos (P19bd.liftPt x) (P19bd.liftPt y) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [P19bd.liftPt]; omega⟩
    have := key _ hn _ hv'
    have e : (fun w => x w - CharVecOpt (none : Option V) w + CharVecOpt (some v) w) =
        (fun w => x w + CharVec v w) := by funext w; simp [CharVecOpt]
    rwa [e] at this

theorem mnatsi_mnatural_convex {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (h : MNatSI f) : MNaturalConvex f :=
  msi_mexchange (LiftedFunction f) (mnatsi_msi_lift f h)

end DiscreteConvex.MConvexFunctionsB.Q19bd

open DiscreteConvex.MConvexFunctionsB in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hdom : (DomZ f).Nonempty) :
    (MExchangeAxiom f ↔ MSI f) ∧ (MNaturalConvex f ↔ MNatSI f) := by
  exact ⟨⟨P19bd.mexchange_msi f, Q19bd.msi_mexchange f⟩,
    ⟨P19bd.mnat_mnatsi f, Q19bd.mnatsi_mnatural_convex f⟩⟩
