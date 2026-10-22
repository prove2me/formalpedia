-- Prove2me | solution 1 for EVSubsidy.Marginal.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T19:57:58.713468+00:00
-- url     : https://prove2.me/submissions/5dd827a4-0587-4b39-9835-6b5dcdc257f2

import Mathlib
import Definitions.Def_EVSubsidy_Marginal_Model

set_option autoImplicit false

namespace EVPf
open EVSubsidy.Marginal Filter Topology

lemma std (P : Params) (hP : P.Standing) :
    0 < P.η ∧ P.η < 1 ∧ 0 < P.a ∧ 0 < P.T ∧ 0 < P.τ ∧ 0 < P.f ∧ 0 ≤ P.θ ∧ 0 < P.μ ∧
      0 < P.n ∧ 0 < P.s .A ∧ P.s .A ≤ P.s .B ∧ 0 < P.k .B ∧ P.k .B < P.k .A := by
  unfold Params.Standing at hP
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -, h11, h12, h13, -, -, h16, h17⟩ := hP
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h11, h12, h13, h16, h17⟩

lemma one_sub_H_pos (P : Params) (z : ℝ) : 0 < 1 - H P z := by
  unfold H
  split_ifs
  · norm_num
  · rw [sub_sub_cancel]; exact Real.exp_pos _

lemma one_sub_H_of_pos (P : Params) (z : ℝ) (hz : 0 < z) :
    1 - H P z = Real.exp (-(P.a * z)) := by
  unfold H; rw [if_neg (not_le.mpr hz)]; ring

lemma phi_pos (P : Params) (ρ : Loc → ℝ) (i : Loc) : 0 < phi P ρ i := by
  unfold phi; positivity

lemma phi_sum (P : Params) (ρ : Loc → ℝ) : phi P ρ .A + phi P ρ .B = 1 := by
  unfold phi
  rw [← add_div, div_self (ne_of_gt (by positivity))]

lemma lam_pos (P : Params) (hP : P.Standing) (ω : Policy) (ρ : Loc → ℝ) (i : Loc) :
    0 < lam P ω ρ i := by
  obtain ⟨hη0, hη1, -, hT, -⟩ := std P hP
  have h1 : 0 < 1 - P.η := by linarith
  cases i
  · simp only [lam]
    exact add_pos (mul_pos (mul_pos (div_pos h1 hT) (phi_pos P ρ .A)) (one_sub_H_pos P _))
      (mul_pos (div_pos hη0 hT) (one_sub_H_pos P _))
  · simp only [lam]
    exact mul_pos (mul_pos (div_pos h1 hT) (phi_pos P ρ .B)) (one_sub_H_pos P _)

lemma re_coef (P : Params) (ω : Policy) (ξ m : Loc → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hmax : ∀ m' : Loc → ℝ, (∀ i, 0 ≤ m' i) → spProfit P ω ξ m' ≤ spProfit P ω ξ m)
    (i : Loc) (hmi : 0 < m i) :
    (ω.β + P.f) * ξ i / P.τ - (P.k i - ω.α i) = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : Loc → ℝ,
      c = fun j => (ω.β + P.f) * ξ j / P.τ - (P.k j - ω.α j) := ⟨_, rfl⟩
  have hsp : ∀ m' : Loc → ℝ, spProfit P ω ξ m' = c .A * m' .A + c .B * m' .B := by
    intro m'; simp only [spProfit, hc]; ring
  have h1 := hmax (fun j => if j = i then 2 * m i else m j)
    (by intro j; split_ifs <;> linarith [hm i, hm j])
  have h2 := hmax (fun j => if j = i then 0 else m j)
    (by intro j; split_ifs <;> linarith [hm j])
  simp only [hsp] at h1 h2
  have key : c i = 0 := by
    cases i <;> simp at h1 h2 hmi ⊢ <;> nlinarith
  rw [hc] at key; exact key

lemma re_unique (P : Params) (hP : P.Standing) (ω : Policy) (hR : Regime P ω)
    (ξ m : Loc → ℝ) (hRE : IsRE P ω ξ m) :
    ξ = xiStar P ω ∧ ∀ i, P.n * m i * (P.k i - ω.α i) = (ω.β + P.f) * lam P ω ξ i := by
  obtain ⟨-, -, -, -, hτ, -⟩ := std P hP
  obtain ⟨hξ, hm, hmax, hbal⟩ := hRE
  have hpos : ∀ i, 0 < m i := by
    intro i
    rcases (hm i).lt_or_eq with h | h
    · exact h
    · exfalso
      have h3 := hbal i
      rw [← h] at h3
      have := lam_pos P hP ω ξ i
      nlinarith
  have hβf : ∀ i : Loc, 0 < ω.β + P.f := by
    intro i
    obtain ⟨h1, h2⟩ := hR i
    have : 0 < (P.k i - ω.α i) * P.τ := mul_pos (by linarith) hτ
    linarith
  have hc : ∀ i, (ω.β + P.f) * ξ i = (P.k i - ω.α i) * P.τ := by
    intro i
    have := re_coef P ω ξ m hm hmax i (hpos i)
    have h2 : (ω.β + P.f) * ξ i / P.τ = P.k i - ω.α i := by linarith
    rw [div_eq_iff hτ.ne'] at h2
    exact h2
  refine ⟨?_, ?_⟩
  · funext i
    simp only [xiStar]
    rw [eq_div_iff (hβf i).ne']
    linear_combination hc i
  · intro i
    have key : P.τ * (P.n * m i * (P.k i - ω.α i) - (ω.β + P.f) * lam P ω ξ i) = 0 := by
      linear_combination (-(P.n * m i)) * hc i + (ω.β + P.f) * hbal i
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hτ.ne'
    · linarith

lemma tail_facts (P : Params) (ha : 0 < P.a) (z0 : ℝ) (hz : 0 < z0) :
    MeasureTheory.IntegrableOn (fun z => (z - z0) * hDens P z) (Set.Ioi z0) ∧
    ∫ z in Set.Ioi z0, (z - z0) * hDens P z = Real.exp (-(P.a * z0)) / P.a := by
  have hEq : Set.EqOn (fun z => (z - z0) * (P.a * Real.exp (-(P.a * z))))
      (fun z => (z - z0) * hDens P z) (Set.Ioi z0) := by
    intro z hz'
    have : 0 ≤ z := le_of_lt (lt_trans hz hz')
    simp only [hDens, if_pos this]
  have h1 : ∫ z in Set.Ioi z0, (z - z0) * hDens P z =
      ∫ z in Set.Ioi z0, (z - z0) * (P.a * Real.exp (-(P.a * z))) :=
    (MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEq).symm
  have hderiv : ∀ x ∈ Set.Ioi z0, HasDerivAt
      (fun z => -(z - z0) * Real.exp (-(P.a * z)) - Real.exp (-(P.a * z)) / P.a)
      ((x - z0) * (P.a * Real.exp (-(P.a * x)))) x := by
    intro x _
    have he := (((hasDerivAt_id' x).const_mul P.a).neg).exp
    have hl := ((hasDerivAt_id' x).sub_const z0).neg
    refine ((hl.mul he).sub (he.div_const P.a)).congr_deriv ?_
    simp only [Pi.neg_apply]
    field_simp
    ring
  have hlim : Tendsto (fun z => -(z - z0) * Real.exp (-(P.a * z)) - Real.exp (-(P.a * z)) / P.a)
      atTop (𝓝 0) := by
    have hlin : Tendsto (fun z => P.a * z) atTop atTop := tendsto_id.const_mul_atTop ha
    have e1 : Tendsto (fun z => Real.exp (-(P.a * z))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
    have e2 : Tendsto (fun z => (P.a * z) ^ 1 * Real.exp (-(P.a * z))) atTop (𝓝 0) :=
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hlin
    have e3 := (e2.const_mul (-(1 / P.a))).add (e1.const_mul (z0 - 1 / P.a))
    simp only [mul_zero, add_zero] at e3
    refine e3.congr (fun z => ?_)
    simp only [pow_one]
    field_simp
    ring
  have hcont : ContinuousWithinAt
      (fun z => -(z - z0) * Real.exp (-(P.a * z)) - Real.exp (-(P.a * z)) / P.a)
      (Set.Ici z0) z0 := by
    have : Continuous
        (fun z => -(z - z0) * Real.exp (-(P.a * z)) - Real.exp (-(P.a * z)) / P.a) := by
      fun_prop
    exact this.continuousWithinAt
  have hnn : ∀ x ∈ Set.Ioi z0, 0 ≤ (x - z0) * (P.a * Real.exp (-(P.a * x))) := by
    intro x hx
    have : 0 < x - z0 := sub_pos.mpr hx
    positivity
  refine ⟨(MeasureTheory.integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnn hlim).congr_fun
    hEq measurableSet_Ioi, ?_⟩
  rw [h1, MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnn hlim]
  ring

/-- As formalized, the first integral in `driverSurplus` absorbs the second summand,
so its integrand is an integrable function plus a nonzero constant on a half-line:
it is not integrable and the Bochner integral is `0`. -/
lemma drv_zero (P : Params) (ha : 0 < P.a) (hη1 : P.η < 1) (ω : Policy) (ξ : Loc → ℝ)
    (hA : 0 < zStar P ω ξ .A) (hB : 0 < zStar P ω ξ .B) :
    driverSurplus P ω ξ = 0 := by
  simp only [driverSurplus, popShare]
  obtain ⟨hIA, -⟩ := tail_facts P ha _ hA
  obtain ⟨-, hvB⟩ := tail_facts P ha _ hB
  rw [hvB]
  have hK : (1 - P.η) * (Real.exp (-(P.a * zStar P ω ξ .B)) / P.a) ≠ 0 := by
    have : 0 < 1 - P.η := by linarith
    positivity
  have hni : ¬ MeasureTheory.Integrable
      (fun z => (z - zStar P ω ξ .A) * hDens P z +
        (1 - P.η) * (Real.exp (-(P.a * zStar P ω ξ .B)) / P.a))
      (MeasureTheory.volume.restrict (Set.Ioi (zStar P ω ξ .A))) := by
    intro h
    have h2 := MeasureTheory.Integrable.sub h hIA
    have hfun : (fun z => ((z - zStar P ω ξ .A) * hDens P z +
        (1 - P.η) * (Real.exp (-(P.a * zStar P ω ξ .B)) / P.a)) -
        (z - zStar P ω ξ .A) * hDens P z) =
        fun _ => (1 - P.η) * (Real.exp (-(P.a * zStar P ω ξ .B)) / P.a) := by
      funext z; ring
    have h3 : MeasureTheory.IntegrableOn
        (fun _ : ℝ => (1 - P.η) * (Real.exp (-(P.a * zStar P ω ξ .B)) / P.a))
        (Set.Ioi (zStar P ω ξ .A)) := by
      rw [← hfun]; exact h2
    rw [MeasureTheory.integrableOn_const_iff] at h3
    simp [Real.volume_Ioi] at h3
    rcases h3 with h3 | h3 <;> linarith
  rw [MeasureTheory.integral_undef hni]
  ring

lemma lam_sum (P : Params) (ω : Policy) (ξ : Loc → ℝ)
    (hA : 0 < zStar P ω ξ .A) (hB : 0 < zStar P ω ξ .B) :
    lam P ω ξ .A + lam P ω ξ .B = (1 - P.η) / P.T * Real.exp (-(P.a * zStar P ω ξ .B)) +
      P.η / P.T * Real.exp (-(P.a * zStar P ω ξ .A)) := by
  simp only [lam]
  rw [one_sub_H_of_pos P _ hA, one_sub_H_of_pos P _ hB]
  linear_combination ((1 - P.η) / P.T * Real.exp (-(P.a * zStar P ω ξ .B))) * phi_sum P ξ

lemma gss_closed (P : Params) (hP : P.Standing) (ω : Policy) (hR : Regime P ω)
    (ξ m : Loc → ℝ) (hRE : IsRE P ω ξ m) (hA : 0 < zStar P ω ξ .A)
    (hB : 0 < zStar P ω ξ .B) :
    GSS P ω ξ m = P.θ * (P.η * Real.exp (-(P.a * zStar P ω ξ .A)) +
      (1 - P.η) * Real.exp (-(P.a * zStar P ω ξ .B))) := by
  obtain ⟨-, hη1, ha, hT, -⟩ := std P hP
  obtain ⟨-, hb⟩ := re_unique P hP ω hR ξ m hRE
  have hsp : spSurplus P ω ξ m = 0 := by
    simp only [spSurplus]
    linear_combination (-1 : ℝ) * hb .A + (-1 : ℝ) * hb .B
  simp only [GSS]
  rw [lam_sum P ω ξ hA hB, drv_zero P ha hη1 ω ξ hA hB, hsp]
  field_simp
  ring

noncomputable def Phi (P : Params) (ω : Policy) : ℝ :=
  P.θ * (P.η * Real.exp (-(P.a * zStar P ω (xiStar P ω) .A)) +
      (1 - P.η) * Real.exp (-(P.a * zStar P ω (xiStar P ω) .B)))

lemma gssat_eq (P : Params) (hP : P.Standing) (E : Policy → (Loc → ℝ) × (Loc → ℝ))
    (hE : IsEqSelection P E) (ω : Policy) (hR : Regime P ω)
    (hA : 0 < zStar P ω (xiStar P ω) .A) (hB : 0 < zStar P ω (xiStar P ω) .B) :
    GSSat P E ω = Phi P ω := by
  have hRE := hE ω hR
  have hξ := (re_unique P hP ω hR _ _ hRE).1
  unfold GSSat Phi
  rw [gss_closed P hP ω hR _ _ hRE (by rw [hξ]; exact hA) (by rw [hξ]; exact hB), hξ]

lemma transfer (P : Params) (hP : P.Standing) (E : Policy → (Loc → ℝ) × (Loc → ℝ))
    (hE : IsEqSelection P E) (ω : ℝ → Policy) (x d : ℝ)
    (hreg : ∀ᶠ y in 𝓝 x, Regime P (ω y))
    (hcA : ContinuousAt (fun y => zStar P (ω y) (xiStar P (ω y)) .A) x)
    (hcB : ContinuousAt (fun y => zStar P (ω y) (xiStar P (ω y)) .B) x)
    (hzA : 0 < zStar P (ω x) (xiStar P (ω x)) .A)
    (hzB : 0 < zStar P (ω x) (xiStar P (ω x)) .B)
    (hd : HasDerivAt (fun y => Phi P (ω y)) d x) :
    HasDerivAt (fun y => GSSat P E (ω y)) d x := by
  apply hd.congr_of_eventuallyEq
  filter_upwards [hreg, Filter.Tendsto.eventually_const_lt hzA hcA,
    Filter.Tendsto.eventually_const_lt hzB hcB] with y hy h1 h2
  exact gssat_eq P hP E hE (ω y) hy h1 h2

lemma z_derivs (P : Params) (ω : ℝ → Policy) (x dA dB dg : ℝ)
    (hA : HasDerivAt (fun y => F P (xiStar P (ω y)) .A) dA x)
    (hB : HasDerivAt (fun y => F P (xiStar P (ω y)) .B) dB x)
    (hg : HasDerivAt (fun y => (ω y).γ) dg x) :
    HasDerivAt (fun y => zStar P (ω y) (xiStar P (ω y)) .A) (-dg + dA / P.T) x ∧
    HasDerivAt (fun y => zStar P (ω y) (xiStar P (ω y)) .B)
      (-dg + (phi P (xiStar P (ω x)) .A * dA + phi P (xiStar P (ω x)) .B * dB) / P.T) x := by
  constructor
  · exact (hg.const_sub P.p).add (hA.div_const P.T)
  · have hS := (hA.neg.exp).add (hB.neg.exp)
    have hSpos : 0 < Real.exp (-F P (xiStar P (ω x)) .A) +
        Real.exp (-F P (xiStar P (ω x)) .B) := by positivity
    have h2 := (hg.const_sub P.p).add (((hS.log hSpos.ne').neg).div_const P.T)
    refine h2.congr_deriv ?_
    simp only [phi, Pi.neg_apply, Pi.add_apply]
    ring

lemma Phi_deriv (P : Params) (ω : ℝ → Policy) (x dzA dzB : ℝ)
    (hA : HasDerivAt (fun y => zStar P (ω y) (xiStar P (ω y)) .A) dzA x)
    (hB : HasDerivAt (fun y => zStar P (ω y) (xiStar P (ω y)) .B) dzB x) :
    HasDerivAt (fun y => Phi P (ω y))
      (P.θ *
        (P.η * (Real.exp (-(P.a * zStar P (ω x) (xiStar P (ω x)) .A)) * -(P.a * dzA)) +
        (1 - P.η) * (Real.exp (-(P.a * zStar P (ω x) (xiStar P (ω x)) .B)) *
          -(P.a * dzB)))) x := by
  unfold Phi
  exact ((((hA.const_mul P.a).neg.exp).const_mul P.η).add
    (((hB.const_mul P.a).neg.exp).const_mul (1 - P.η))).const_mul P.θ

lemma const_deriv (f : ℝ → ℝ) (x c : ℝ) (h : ∀ y, f y = c) : HasDerivAt f 0 x := by
  have : f = fun _ => c := funext h
  rw [this]; exact hasDerivAt_const x c

lemma F_deriv (P : Params) (i : Loc) (ξ : ℝ → ℝ) (ξ' x : ℝ) (h : HasDerivAt ξ ξ' x)
    (hne : 1 - ξ x ≠ 0) :
    HasDerivAt (fun y => P.f + P.c i * P.τ + P.s i / (1 - ξ y))
      (P.s i * ξ' / (1 - ξ x) ^ 2) x := by
  have h3 := (((h.const_sub 1).inv hne).const_mul (P.s i)).const_add (P.f + P.c i * P.τ)
  have hfun : (fun y => P.f + P.c i * P.τ + P.s i / (1 - ξ y)) =
      (fun y => P.f + P.c i * P.τ + P.s i * (1 - ξ y)⁻¹) := by
    funext y; rw [div_eq_mul_inv]
  rw [hfun]
  exact h3.congr_deriv (by ring)

lemma F_beta (P : Params) (γ β : ℝ) (i : Loc) (hτ : 0 < P.τ) (hk : 0 < P.k i)
    (hlt : (P.k i - 0) * P.τ < β + P.f) :
    HasDerivAt (fun b => F P (xiStar P (mixBG b γ)) i)
      (-(P.k i * P.s i * P.τ / (β + P.f - P.k i * P.τ) ^ 2)) β := by
  have hkt : 0 < P.k i * P.τ := mul_pos hk hτ
  rw [sub_zero] at hlt
  have hpos : 0 < β + P.f := by linarith
  have hξ : HasDerivAt (fun b => (P.k i - 0) * P.τ / (b + P.f))
      ((P.k i - 0) * P.τ * (-1 / (β + P.f) ^ 2)) β := by
    have h0 := (((hasDerivAt_id' β).add_const P.f).inv hpos.ne').const_mul ((P.k i - 0) * P.τ)
    have hfun : (fun b => (P.k i - 0) * P.τ / (b + P.f)) =
        (fun b => (P.k i - 0) * P.τ * (b + P.f)⁻¹) := by
      funext b; rw [div_eq_mul_inv]
    rw [hfun]
    exact h0.congr_deriv (by ring)
  have hne : 1 - (P.k i - 0) * P.τ / (β + P.f) ≠ 0 := by
    rw [sub_zero, ne_eq, sub_eq_zero, eq_comm, div_eq_one_iff_eq hpos.ne']
    exact ne_of_lt hlt
  have h := F_deriv P i (fun b => (P.k i - 0) * P.τ / (b + P.f)) _ β hξ hne
  have h2 : β + P.f - P.k i * P.τ ≠ 0 := by linarith
  refine h.congr_deriv ?_
  simp only [sub_zero]
  field_simp

lemma F_alpha (P : Params) (i : Loc) (α0 d : ℝ) (hτ : 0 < P.τ) (hf : 0 < P.f)
    (hk : 0 < P.k i) (hlt : (P.k i - α0) * P.τ < 0 + P.f)
    (hd : d = (P.k i - α0) ^ 2 / (P.f * P.k i)) :
    HasDerivAt (fun t => P.f + P.c i * P.τ + P.s i / (1 - (P.k i - (α0 + t * d)) * P.τ / (0 + P.f)))
      (-((P.k i - α0) ^ 2 * P.s i * P.τ / (P.k i * (P.f - (P.k i - α0) * P.τ) ^ 2))) 0 := by
  rw [zero_add] at hlt
  have hξ : HasDerivAt (fun t => (P.k i - (α0 + t * d)) * P.τ / (0 + P.f))
      (-(d * P.τ) / (0 + P.f)) 0 := by
    have h0 := (((((hasDerivAt_id' (0:ℝ)).mul_const d).const_add α0).const_sub
      (P.k i)).mul_const P.τ).div_const (0 + P.f)
    exact h0.congr_deriv (by ring)
  have hne : 1 - (fun t => (P.k i - (α0 + t * d)) * P.τ / (0 + P.f)) 0 ≠ 0 := by
    simp only [zero_mul, add_zero, zero_add]
    rw [ne_eq, sub_eq_zero, eq_comm, div_eq_one_iff_eq hf.ne']
    exact ne_of_lt hlt
  have h := F_deriv P i (fun t => (P.k i - (α0 + t * d)) * P.τ / (0 + P.f)) _ 0 hξ hne
  have h2 : P.f - (P.k i - α0) * P.τ ≠ 0 := by linarith
  have h3 : P.k i ≠ 0 := hk.ne'
  have h4 : P.f ≠ 0 := hf.ne'
  refine h.congr_deriv ?_
  subst hd
  simp only [zero_mul, add_zero, zero_add]
  field_simp

noncomputable def Esel (P : Params) (ω : Policy) : (Loc → ℝ) × (Loc → ℝ) :=
  (xiStar P ω, fun i => P.τ * lam P ω (xiStar P ω) i / (xiStar P ω i * P.n))

lemma Esel_spec (P : Params) (hP : P.Standing) : IsEqSelection P (Esel P) := by
  obtain ⟨-, -, -, -, hτ, -, -, -, hn, -⟩ := std P hP
  intro ω hR
  have hb : 0 < ω.β + P.f := by
    obtain ⟨h1, h2⟩ := hR .A
    have : 0 < (P.k .A - ω.α .A) * P.τ := mul_pos (by linarith) hτ
    linarith
  have hxpos : ∀ i, 0 < xiStar P ω i ∧ xiStar P ω i < 1 := by
    intro i
    obtain ⟨h1, h2⟩ := hR i
    have hk : 0 < (P.k i - ω.α i) * P.τ := mul_pos (by linarith) hτ
    exact ⟨div_pos hk hb, (div_lt_one hb).mpr h2⟩
  have h0 : ∀ m : Loc → ℝ, spProfit P ω (xiStar P ω) m = 0 := by
    intro m
    simp only [spProfit, xiStar]
    field_simp
    ring
  unfold IsRE
  refine ⟨fun i => ⟨(hxpos i).1.le, (hxpos i).2⟩, fun i => ?_, fun m' _ => ?_, fun i => ?_⟩
  · simp only [Esel]
    exact div_nonneg (mul_nonneg hτ.le (lam_pos P hP ω _ i).le)
      (mul_pos (hxpos i).1 hn).le
  · simp only [Esel]
    rw [h0, h0]
  · simp only [Esel]
    have := (hxpos i).1.ne'
    have := hn.ne'
    field_simp

end EVPf

open EVSubsidy.Marginal Filter Topology in
theorem solution (P : Params) (hP : P.Standing)
    (hks : P.k .B * P.s .B ≤ P.k .A * P.s .A) :
    (∃ E, IsEqSelection P E) ∧
    ∀ E, IsEqSelection P E →
      (∀ αA αB γ : ℝ, 0 ≤ αA → 0 ≤ αB → 0 ≤ γ →
        Regime P (mixAG αA αB γ) → Balanced P E αA αB γ →
        (∀ i : Loc, 0 < zStar P (mixAG αA αB γ)
          (E (mixAG αA αB γ)).1 i) →
        max ((P.k .A - αA) ^ 2 * P.s .A * P.τ /
          (P.k .A * (P.f - (P.k .A - αA) * P.τ) ^ 2))
            ((P.k .B - αB) ^ 2 * P.s .B * P.τ /
          (P.k .B * (P.f - (P.k .B - αB) * P.τ) ^ 2)) ≤ P.μ →
        GammaMarginallyBeatsAlphaFlex P E αA αB γ) ∧
      (∀ β γ : ℝ, 0 ≤ β → 0 ≤ γ → Regime P (mixBG β γ) →
        (∀ i : Loc, 0 < zStar P (mixBG β γ)
          (E (mixBG β γ)).1 i) →
        P.μ ≤ P.k .B * P.s .B * P.τ /
          (β + P.f - P.k .B * P.τ) ^ 2 →
        BetaMarginallyBeatsGamma P E β γ) := by
  obtain ⟨hη0, hη1, ha, hT, hτ, hf, hθ, hμ, hn, hsA, hsAB, hkB, hkBA⟩ := EVPf.std P hP
  have hkA : 0 < P.k .A := lt_trans hkB hkBA
  have hsB : 0 < P.s .B := lt_of_lt_of_le hsA hsAB
  have h1η : 0 < 1 - P.η := by linarith
  refine ⟨⟨EVPf.Esel P, EVPf.Esel_spec P hP⟩, ?_⟩
  intro E hE
  refine ⟨?_, ?_⟩
  · -- part 1: purchase subsidy vs flexible pile subsidy
    intro αA αB γ _ _ _ hR _ hz hmax
    have hξ := (EVPf.re_unique P hP _ hR _ _ (hE _ hR)).1
    have hzA : 0 < zStar P (mixAG αA αB γ) (xiStar P (mixAG αA αB γ)) .A := by
      rw [← hξ]; exact hz .A
    have hzB : 0 < zStar P (mixAG αA αB γ) (xiStar P (mixAG αA αB γ)) .B := by
      rw [← hξ]; exact hz .B
    have hRA : αA < P.k .A ∧ (P.k .A - αA) * P.τ < 0 + P.f := hR .A
    have hRB : αB < P.k .B ∧ (P.k .B - αB) * P.τ < 0 + P.f := hR .B
    have hvA : (P.k .A - αA) ^ 2 * P.s .A * P.τ / (P.k .A * (P.f - (P.k .A - αA) * P.τ) ^ 2)
        ≤ P.μ := le_trans (le_max_left _ _) hmax
    have hvB : (P.k .B - αB) ^ 2 * P.s .B * P.τ / (P.k .B * (P.f - (P.k .B - αB) * P.τ) ^ 2)
        ≤ P.μ := le_trans (le_max_right _ _) hmax
    unfold GammaMarginallyBeatsAlphaFlex
    generalize hdA : alphaDir P αA αB .A = dA
    generalize hdB : alphaDir P αA αB .B = dB
    have hω0 : mixAG (αA + 0 * dA) (αB + 0 * dB) γ = mixAG αA αB γ := by simp
    -- the flexible direction
    have hFA : HasDerivAt (fun t => F P (xiStar P (mixAG (αA + t * dA) (αB + t * dB) γ)) .A)
        (-((P.k .A - αA) ^ 2 * P.s .A * P.τ / (P.k .A * (P.f - (P.k .A - αA) * P.τ) ^ 2))) 0 :=
      EVPf.F_alpha P .A αA dA hτ hf hkA hRA.2 hdA.symm
    have hFB : HasDerivAt (fun t => F P (xiStar P (mixAG (αA + t * dA) (αB + t * dB) γ)) .B)
        (-((P.k .B - αB) ^ 2 * P.s .B * P.τ / (P.k .B * (P.f - (P.k .B - αB) * P.τ) ^ 2))) 0 :=
      EVPf.F_alpha P .B αB dB hτ hf hkB hRB.2 hdB.symm
    have hgt : HasDerivAt (fun t => (mixAG (αA + t * dA) (αB + t * dB) γ).γ) 0 0 :=
      hasDerivAt_const 0 γ
    obtain ⟨hzAt, hzBt⟩ := EVPf.z_derivs P (fun t => mixAG (αA + t * dA) (αB + t * dB) γ)
      0 _ _ _ hFA hFB hgt
    have hregt : ∀ᶠ t in 𝓝 (0:ℝ), Regime P (mixAG (αA + t * dA) (αB + t * dB) γ) := by
      have c1 : Continuous (fun t : ℝ => αA + t * dA) := by fun_prop
      have c2 : Continuous (fun t : ℝ => (P.k .A - (αA + t * dA)) * P.τ) := by fun_prop
      have c3 : Continuous (fun t : ℝ => αB + t * dB) := by fun_prop
      have c4 : Continuous (fun t : ℝ => (P.k .B - (αB + t * dB)) * P.τ) := by fun_prop
      have e1 := Filter.Tendsto.eventually_lt_const (by simpa using hRA.1) (c1.continuousAt (x := 0))
      have e2 := Filter.Tendsto.eventually_lt_const (by simpa using hRA.2) (c2.continuousAt (x := 0))
      have e3 := Filter.Tendsto.eventually_lt_const (by simpa using hRB.1) (c3.continuousAt (x := 0))
      have e4 := Filter.Tendsto.eventually_lt_const (by simpa using hRB.2) (c4.continuousAt (x := 0))
      filter_upwards [e1, e2, e3, e4] with t h1 h2 h3 h4
      unfold Regime
      intro i
      cases i
      · exact ⟨h1, by simpa [mixAG] using h2⟩
      · exact ⟨h3, by simpa [mixAG] using h4⟩
    have hdα := EVPf.transfer P hP E hE (fun t => mixAG (αA + t * dA) (αB + t * dB) γ) 0 _
      hregt hzAt.continuousAt hzBt.continuousAt (by simp only [hω0]; exact hzA)
      (by simp only [hω0]; exact hzB)
      (EVPf.Phi_deriv P (fun t => mixAG (αA + t * dA) (αB + t * dB) γ) 0 _ _ hzAt hzBt)
    -- the purchase subsidy direction
    have hGA : HasDerivAt (fun g => F P (xiStar P (mixAG αA αB g)) .A) 0 γ :=
      EVPf.const_deriv _ γ (F P (xiStar P (mixAG αA αB γ)) .A) (fun g => rfl)
    have hGB : HasDerivAt (fun g => F P (xiStar P (mixAG αA αB g)) .B) 0 γ :=
      EVPf.const_deriv _ γ (F P (xiStar P (mixAG αA αB γ)) .B) (fun g => rfl)
    have hgg : HasDerivAt (fun g => (mixAG αA αB g).γ) 1 γ := hasDerivAt_id' γ
    obtain ⟨hzAg, hzBg⟩ := EVPf.z_derivs P (fun g => mixAG αA αB g) γ _ _ _ hGA hGB hgg
    have hdγ := EVPf.transfer P hP E hE (fun g => mixAG αA αB g) γ _
      (Filter.Eventually.of_forall (fun g => hR)) hzAg.continuousAt hzBg.continuousAt hzA hzB
      (EVPf.Phi_deriv P (fun g => mixAG αA αB g) γ _ _ hzAg hzBg)
    refine ⟨_, _, hdα, hdγ, ?_⟩
    simp only [hω0]
    have hsum := EVPf.phi_sum P (xiStar P (mixAG αA αB γ))
    have hφA := EVPf.phi_pos P (xiStar P (mixAG αA αB γ)) .A
    have hφB := EVPf.phi_pos P (xiStar P (mixAG αA αB γ)) .B
    generalize phi P (xiStar P (mixAG αA αB γ)) .A = φA at hsum hφA ⊢
    generalize phi P (xiStar P (mixAG αA αB γ)) .B = φB at hsum hφB ⊢
    have huA := Real.exp_pos (-(P.a * zStar P (mixAG αA αB γ) (xiStar P (mixAG αA αB γ)) .A))
    have huB := Real.exp_pos (-(P.a * zStar P (mixAG αA αB γ) (xiStar P (mixAG αA αB γ)) .B))
    generalize Real.exp (-(P.a * zStar P (mixAG αA αB γ) (xiStar P (mixAG αA αB γ)) .A)) = uA
      at huA ⊢
    generalize Real.exp (-(P.a * zStar P (mixAG αA αB γ) (xiStar P (mixAG αA αB γ)) .B)) = uB
      at huB ⊢
    generalize (P.k .A - αA) ^ 2 * P.s .A * P.τ / (P.k .A * (P.f - (P.k .A - αA) * P.τ) ^ 2)
      = vA at hvA ⊢
    generalize (P.k .B - αB) ^ 2 * P.s .B * P.τ / (P.k .B * (P.f - (P.k .B - αB) * P.τ) ^ 2)
      = vB at hvB ⊢
    rw [← sub_nonneg]
    have key : P.μ / P.T * (P.θ * (P.η * (uA * -(P.a * (-1 + 0 / P.T))) +
        (1 - P.η) * (uB * -(P.a * (-1 + (φA * 0 + φB * 0) / P.T))))) -
        P.θ * (P.η * (uA * -(P.a * (-0 + -vA / P.T))) +
        (1 - P.η) * (uB * -(P.a * (-0 + (φA * -vA + φB * -vB) / P.T)))) =
        P.θ * P.a / P.T * (P.η * uA * (P.μ - vA) +
          (1 - P.η) * uB * (φA * (P.μ - vA) + φB * (P.μ - vB))) := by
      linear_combination (-(P.θ * P.a / P.T * (1 - P.η) * uB * P.μ)) * hsum
    rw [key]
    have hvA' : 0 ≤ P.μ - vA := sub_nonneg.mpr hvA
    have hvB' : 0 ≤ P.μ - vB := sub_nonneg.mpr hvB
    exact mul_nonneg (div_nonneg (mul_nonneg hθ ha.le) hT.le)
      (add_nonneg (mul_nonneg (mul_nonneg hη0.le huA.le) hvA')
        (mul_nonneg (mul_nonneg h1η.le huB.le)
          (add_nonneg (mul_nonneg hφA.le hvA') (mul_nonneg hφB.le hvB'))))
  · -- part 2: per-session subsidy vs purchase subsidy
    intro β γ _ _ hR hz hμle
    have hξ := (EVPf.re_unique P hP _ hR _ _ (hE _ hR)).1
    have hzA : 0 < zStar P (mixBG β γ) (xiStar P (mixBG β γ)) .A := by
      rw [← hξ]; exact hz .A
    have hzB : 0 < zStar P (mixBG β γ) (xiStar P (mixBG β γ)) .B := by
      rw [← hξ]; exact hz .B
    have hRA : (P.k .A - 0) * P.τ < β + P.f := (hR .A).2
    have hRB : (P.k .B - 0) * P.τ < β + P.f := (hR .B).2
    have hFA := EVPf.F_beta P γ β .A hτ hkA hRA
    have hFB := EVPf.F_beta P γ β .B hτ hkB hRB
    have hgb : HasDerivAt (fun b => (mixBG b γ).γ) 0 β := hasDerivAt_const β γ
    obtain ⟨hzAb, hzBb⟩ := EVPf.z_derivs P (fun b => mixBG b γ) β _ _ _ hFA hFB hgb
    have hregb : ∀ᶠ b in 𝓝 β, Regime P (mixBG b γ) := by
      have c1 : Continuous (fun b : ℝ => b + P.f) := by fun_prop
      have e1 := Filter.Tendsto.eventually_const_lt hRA (c1.continuousAt (x := β))
      have e2 := Filter.Tendsto.eventually_const_lt hRB (c1.continuousAt (x := β))
      filter_upwards [e1, e2] with b h1 h2
      unfold Regime
      intro i
      cases i
      · exact ⟨(hR .A).1, h1⟩
      · exact ⟨(hR .B).1, h2⟩
    have hdβ := EVPf.transfer P hP E hE (fun b => mixBG b γ) β _
      hregb hzAb.continuousAt hzBb.continuousAt hzA hzB
      (EVPf.Phi_deriv P (fun b => mixBG b γ) β _ _ hzAb hzBb)
    have hGA : HasDerivAt (fun g => F P (xiStar P (mixBG β g)) .A) 0 γ :=
      EVPf.const_deriv _ γ (F P (xiStar P (mixBG β γ)) .A) (fun g => rfl)
    have hGB : HasDerivAt (fun g => F P (xiStar P (mixBG β g)) .B) 0 γ :=
      EVPf.const_deriv _ γ (F P (xiStar P (mixBG β γ)) .B) (fun g => rfl)
    have hgg : HasDerivAt (fun g => (mixBG β g).γ) 1 γ := hasDerivAt_id' γ
    obtain ⟨hzAg, hzBg⟩ := EVPf.z_derivs P (fun g => mixBG β g) γ _ _ _ hGA hGB hgg
    have hdγ := EVPf.transfer P hP E hE (fun g => mixBG β g) γ _
      (Filter.Eventually.of_forall (fun g => hR)) hzAg.continuousAt hzBg.continuousAt hzA hzB
      (EVPf.Phi_deriv P (fun g => mixBG β g) γ _ _ hzAg hzBg)
    refine ⟨_, _, hdβ, hdγ, ?_⟩
    -- w_B ≤ w_A
    have hDA : 0 < β + P.f - P.k .A * P.τ := by rw [sub_zero] at hRA; linarith
    have hDB : 0 < β + P.f - P.k .B * P.τ := by rw [sub_zero] at hRB; linarith
    have hwAB : P.k .B * P.s .B * P.τ / (β + P.f - P.k .B * P.τ) ^ 2 ≤
        P.k .A * P.s .A * P.τ / (β + P.f - P.k .A * P.τ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hnum : P.k .B * P.s .B * P.τ ≤ P.k .A * P.s .A * P.τ :=
        mul_le_mul_of_nonneg_right hks hτ.le
      have hden : (β + P.f - P.k .A * P.τ) ^ 2 ≤ (β + P.f - P.k .B * P.τ) ^ 2 := by
        have : P.k .B * P.τ ≤ P.k .A * P.τ := mul_le_mul_of_nonneg_right hkBA.le hτ.le
        exact pow_le_pow_left₀ hDA.le (by linarith) 2
      exact mul_le_mul hnum hden (sq_nonneg _) (mul_pos (mul_pos hkA hsA) hτ).le
    have hwA := le_trans hμle hwAB
    have hsum := EVPf.phi_sum P (xiStar P (mixBG β γ))
    have hφA := EVPf.phi_pos P (xiStar P (mixBG β γ)) .A
    have hφB := EVPf.phi_pos P (xiStar P (mixBG β γ)) .B
    generalize phi P (xiStar P (mixBG β γ)) .A = φA at hsum hφA ⊢
    generalize phi P (xiStar P (mixBG β γ)) .B = φB at hsum hφB ⊢
    have huA := Real.exp_pos (-(P.a * zStar P (mixBG β γ) (xiStar P (mixBG β γ)) .A))
    have huB := Real.exp_pos (-(P.a * zStar P (mixBG β γ) (xiStar P (mixBG β γ)) .B))
    generalize Real.exp (-(P.a * zStar P (mixBG β γ) (xiStar P (mixBG β γ)) .A)) = uA
      at huA ⊢
    generalize Real.exp (-(P.a * zStar P (mixBG β γ) (xiStar P (mixBG β γ)) .B)) = uB
      at huB ⊢
    generalize P.k .A * P.s .A * P.τ / (β + P.f - P.k .A * P.τ) ^ 2 = wA at hwA ⊢
    generalize P.k .B * P.s .B * P.τ / (β + P.f - P.k .B * P.τ) ^ 2 = wB at hμle ⊢
    rw [← sub_nonneg]
    have key : P.θ * (P.η * (uA * -(P.a * (-0 + -wA / P.T))) +
        (1 - P.η) * (uB * -(P.a * (-0 + (φA * -wA + φB * -wB) / P.T)))) -
        P.μ / P.T * (P.θ * (P.η * (uA * -(P.a * (-1 + 0 / P.T))) +
        (1 - P.η) * (uB * -(P.a * (-1 + (φA * 0 + φB * 0) / P.T))))) =
        P.θ * P.a / P.T * (P.η * uA * (wA - P.μ) +
          (1 - P.η) * uB * (φA * (wA - P.μ) + φB * (wB - P.μ))) := by
      linear_combination (P.θ * P.a / P.T * (1 - P.η) * uB * P.μ) * hsum
    rw [key]
    have hwA' : 0 ≤ wA - P.μ := sub_nonneg.mpr hwA
    have hwB' : 0 ≤ wB - P.μ := sub_nonneg.mpr hμle
    exact mul_nonneg (div_nonneg (mul_nonneg hθ ha.le) hT.le)
      (add_nonneg (mul_nonneg (mul_nonneg hη0.le huA.le) hwA')
        (mul_nonneg (mul_nonneg h1η.le huB.le)
          (add_nonneg (mul_nonneg hφA.le hwA') (mul_nonneg hφB.le hwB'))))
