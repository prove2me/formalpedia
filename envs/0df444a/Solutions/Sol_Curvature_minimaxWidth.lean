-- Prove2me | solution 1 for Curvature.minimaxWidth
-- status  : ACCEPTED   (prove)
-- author  : @ssakaue
-- created : 2026-11-24T07:39:50.103914+00:00
-- url     : https://prove2.me/submissions/88788435-0377-4fca-a5a1-d2d3f5ff2712

import Definitions.Def_Curvature_MinimaxGame

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Curvature.SignGame

variable {I : Type*} [DecidableEq I]


variable [Fintype I]


theorem two_signs (a x : ℝ) (b : Bool) :
    2 * a ≤ |x - a * sign b| + |x - a * sign (!b)| := by
  cases b <;> simp [sign] <;> grind [le_abs_self, neg_abs_le]

theorem round_loss {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : I) (a G : ℝ) (hG : 0 ≤ G) (x : (I → Bool) → Ω → ℝ)
    (hpast : ∀ σ ω, x (flip i σ) ω = x σ ω)
    (hint : ∀ σ, Integrable (fun ω => G * |x σ ω - a * sign (σ i)|) μ) :
    G*a ≤ 𝔼 σ, ∫ ω, G * |x σ ω - a * sign (σ i)| ∂μ := by
  let f := fun (σ : I → Bool) (ω : Ω) => G * |x σ ω - a * sign (σ i)|
  change G*a ≤ 𝔼 σ, ∫ ω, f σ ω ∂μ
  rw [expect_pair i]
  refine (Fintype.expect_const (ι := I → Bool) (G*a)).ge.trans ?_
  apply Finset.expect_le_expect
  intro σ _
  have hp : ∀ ω, 2*(G*a) ≤ f σ ω + f (flip i σ) ω := by
    intro ω
    simp only [f, hpast, flip_same, ← mul_add]
    nlinarith only [mul_le_mul_of_nonneg_left (two_signs a (x σ ω) (σ i)) hG]
  have hk := integral_mono (μ := μ) (integrable_const (2*(G*a)))
    ((hint σ).add (hint (flip i σ))) hp
  simp only [integral_const, probReal_univ, one_smul] at hk
  change 2 * (G*a) ≤ ∫ ω, f σ ω + f (flip i σ) ω ∂μ at hk
  rw [show (∫ ω, f σ ω + f (flip i σ) ω ∂μ) =
    (∫ ω, f σ ω ∂μ) + ∫ ω, f (flip i σ) ω ∂μ from integral_add (hint σ) (hint _)] at hk
  linarith

end Curvature.SignGame
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory
namespace Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


variable [MeasurableSpace E] [BorelSpace E]


theorem AdmissibleWidthLaw.secondMoment {μ : Measure E} (hμ : AdmissibleWidthLaw μ)
    (v : E) (hv : ‖v‖ ≤ 1) :
    Integrable (fun z : E => ⟪v,z⟫_ℝ^2) μ ∧ (∫ z, ⟪v,z⟫_ℝ^2 ∂μ) ≤ 2 := by
  let := hμ.prob
  have hs (z : E) : ⟪v,z⟫_ℝ^2 ≤ 2 * (Real.exp |⟪v,z⟫_ℝ| - 1) := by
    have hp := Real.quadratic_le_exp_of_nonneg (abs_nonneg ⟪v,z⟫_ℝ)
    rw [sq_abs] at hp
    linarith [abs_nonneg ⟪v,z⟫_ℝ]
  have hint := ((hμ.exp_integrable v hv).sub (integrable_const 1)).const_mul 2
  have hi : Integrable (fun z : E => ⟪v,z⟫_ℝ^2) μ := by
    apply hint.mono' (by fun_prop)
    apply Filter.Eventually.of_forall
    intro z
    change ‖⟪v,z⟫_ℝ^2‖ ≤ 2 * (Real.exp |⟪v,z⟫_ℝ| - 1)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ⟪v,z⟫_ℝ)]
    exact hs z
  refine ⟨hi, ?_⟩
  have h := integral_mono hi hint hs
  change (∫ z, ⟪v,z⟫_ℝ^2 ∂μ) ≤ ∫ z : E, 2 * (Real.exp |⟪v,z⟫_ℝ| - 1) ∂μ at h
  rw [integral_const_mul, integral_sub (hμ.exp_integrable v hv) (integrable_const 1),
    integral_const, probReal_univ, one_smul] at h
  linarith [hμ.exp_le v hv]


end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature.Sparse

theorem exists_blocks {d : ℕ} (hd : 2 ≤ d) {q : ℝ} (hq : 1 ≤ q) :
    ∃ k m : ℕ, 0 < k ∧ 2 ≤ m ∧ k*m ≤ d ∧
      (d:ℝ)^(1/q) * min q (Real.log ((d:ℝ)+1)) ≤ 32*(k:ℝ)^(1/q) * Real.log m := by
  let m := ⌈Real.exp q⌉₊
  have hq0 : 0 < q := by linarith
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : 0 < (d:ℝ) := by linarith
  have hmge : Real.exp q ≤ (m:ℝ) := Nat.le_ceil _
  have hExp : 2 < Real.exp q := Real.exp_one_gt_two.trans_le (Real.exp_le_exp.mpr hq)
  have hm : 2 ≤ m := by exact_mod_cast hExp.le.trans hmge
  have hm0 : 0 < (m:ℝ) := (Real.exp_pos q).trans_le hmge
  have hM : (m:ℝ) ≤ 2*Real.exp q := by
    have H := Nat.ceil_lt_add_one (Real.exp_pos q).le
    dsimp [m]
    linarith
  have hlogm : q ≤ Real.log m := by simpa using Real.log_le_log (Real.exp_pos _) hmge
  have hqinv : 1/q ≤ 1 := (div_le_iff₀ hq0).mpr (by linarith)
  have hqexp : (Real.exp q)^(1/q) = Real.exp 1 := by rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]; congr 1; field_simp
  have hBound (v : ℝ) (hv : 0 ≤ v) (h : (d:ℝ) ≤ (4*Real.exp q)*v) : (d:ℝ)^(1/q) ≤ 12*v^(1/q) := by
    have h1 := Real.rpow_le_rpow hd0.le h (by positivity : 0 ≤ 1/q)
    rw [Real.mul_rpow (by positivity) hv, Real.mul_rpow (by norm_num) (Real.exp_pos _).le, hqexp] at h1
    have h4 := Real.rpow_le_self_of_one_le (x := (4:ℝ)) (by norm_num) hqinv
    have hcoef : (4:ℝ)^(1/q)*Real.exp 1 ≤ 12 :=
      (mul_le_mul h4 Real.exp_one_lt_three.le (Real.exp_pos _).le (by norm_num)).trans_eq (by norm_num)
    exact h1.trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hv _))
  by_cases hmd : m ≤ d
  · let k := ⌊(d:ℝ)/m⌋₊
    have hdiv : 1 ≤ (d:ℝ)/m := (le_div_iff₀ hm0).mpr (by rw [one_mul]; exact_mod_cast hmd)
    have hk : 1 ≤ k := by apply Nat.le_floor; simpa using hdiv
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hkm : k*m ≤ d := by exact_mod_cast (le_div_iff₀ hm0).mp (Nat.floor_le (by positivity : 0 ≤ (d:ℝ)/m))
    have hfloor : (d:ℝ)/m ≤ 2*k := by
      have h : (d:ℝ)/m < k+1 := Nat.lt_floor_add_one _
      linarith
    have hdk : (d:ℝ) ≤ (4*Real.exp q)*k := by
      have h := (div_le_iff₀ hm0).mp hfloor
      nlinarith only [h,mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg k),show 0 ≤ (k:ℝ) by positivity]
    refine ⟨k,m,hk,hm,hkm,?_⟩
    have hl : 0 ≤ Real.log m := by linarith
    calc
      _ ≤ (d:ℝ)^(1/q) * Real.log m := mul_le_mul_of_nonneg_left ((min_le_left ..).trans hlogm) (by positivity)
      _ ≤ (12*(k:ℝ)^(1/q))*Real.log m := mul_le_mul_of_nonneg_right (hBound k (by positivity) hdk) hl
      _ ≤ _ := by nlinarith only [mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) (1/q)) hl]
  · refine ⟨1,d,by decide,hd,by simp,?_⟩
    have hD : (d:ℝ) ≤ m := by exact_mod_cast (le_of_not_ge hmd)
    have hdp := hBound 1 zero_le_one (by linarith)
    rw [Real.one_rpow, mul_one] at hdp
    have hlog : Real.log ((d:ℝ)+1) ≤ 2*Real.log d := by
      have h := Real.log_le_log (show 0 < (d:ℝ)+1 by positivity)
        (show (d:ℝ)+1 ≤ d^2 by nlinarith [(sq_nonneg ((d:ℝ)-2))])
      simpa only [Real.log_pow, Nat.cast_ofNat] using h
    have hl : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
    norm_num only [Nat.cast_one,Real.one_rpow,mul_one]
    calc
      _ ≤ (d:ℝ)^(1/q) * (2*Real.log d) := mul_le_mul_of_nonneg_left ((min_le_right ..).trans hlog) (by positivity)
      _ ≤ 12*(2*Real.log d) := mul_le_mul_of_nonneg_right hdp (by positivity)
      _ ≤ _ := by linarith

end Curvature.Sparse
end
end

section
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace NNReal
namespace Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A globally convex Lipschitz loss has a bounded subgradient at every point. -/
theorem exists_bounded_subgradient {f : E → ℝ} {G : ℝ≥0}
    (hconv : ConvexOn ℝ Set.univ f) (hlip : LipschitzWith G f) (x : E) :
    ∃ g : E, ‖g‖ ≤ G ∧ ∀ y : E, f x - f y ≤ ⟪g,x-y⟫_ℝ := by
  let A : Set (E × ℝ) := {p | f p.1 < p.2}
  have hAo : IsOpen A :=
    isOpen_lt (hlip.continuous.comp continuous_fst) continuous_snd
  have hAc : Convex ℝ A := by
    intro p hp q hq a b ha hb hab
    change f p.1 < p.2 at hp
    change f q.1 < q.2 at hq
    change f (a • p.1 + b • q.1) < a*p.2 + b*q.2
    apply (hconv.2 (Set.mem_univ p.1) (Set.mem_univ q.1) ha hb hab).trans_lt
    change a*f p.1 + b*f q.1 < _
    rcases lt_or_eq_of_le ha with ha' | hae
    · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hp ha')
        (mul_le_mul_of_nonneg_left hq.le hb)
    · have hb' : 0 < b := by linarith only [hab, hae]
      exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hp.le ha)
        (mul_lt_mul_of_pos_left hq hb')
  have hx : (x, f x) ∉ A := by
    change ¬ f x < f x
    exact lt_irrefl _
  obtain ⟨L,hL⟩ := geometric_hahn_banach_point_open hAc hAo hx
  let c := L (0,1)
  let l := L.comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hsplit (y : E) (s : ℝ) : L (y,s) = l y + c*s := by
    have he : (y,s) = (y,0) + s • ((0,1) : E × ℝ) := by ext <;> simp
    nth_rw 1 [he]
    simp only [map_add, map_smul, smul_eq_mul]
    exact congrArg (L (y,0) + ·) (mul_comm _ _)
  have hc : 0 < c := by
    have h := hL (x,f x+1) (lt_add_one (f x))
    rw [hsplit, hsplit] at h
    linarith only [h]
  have hsupp (y : E) : l x + c*f x ≤ l y + c*f y := by
    by_contra! h
    let ε := ((l x+c*f x)-(l y+c*f y))/(2*c)
    have hε : 0 < ε := div_pos (sub_pos.mpr h) (by positivity)
    have hstrict := hL (y,f y+ε) (lt_add_of_pos_right _ hε)
    rw [hsplit, hsplit] at hstrict
    have heq : c*ε = ((l x+c*f x)-(l y+c*f y))/2 := by
      unfold ε
      field_simp
    linarith only [hstrict, heq, h]
  let g := (-c⁻¹) • (InnerProductSpace.toDual ℝ E).symm l
  have hg (y : E) : f x-f y ≤ ⟪g,x-y⟫_ℝ := by
    dsimp only [g]
    rw [real_inner_smul_left,InnerProductSpace.toDual_symm_apply,map_sub,neg_mul,
      ← div_eq_inv_mul, ← neg_div, neg_sub]
    apply (le_div_iff₀ hc).mpr
    linarith only [hsupp y]
  refine ⟨g, ?_, hg⟩
  by_cases hz : g = 0
  · simp [hz]
  · have hp : 0 < ‖g‖ := norm_pos_iff.mpr hz
    have hsq : ‖g‖^2 ≤ f (x+g)-f x := by
      have h := hg (x+g)
      rw [show x-(x+g) = -g by abel, inner_neg_right, real_inner_self_eq_norm_sq] at h
      linarith only [h]
    have hdist := hlip.dist_le_mul (x+g) x
    rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at hdist
    apply le_of_mul_le_mul_right _ hp
    rw [← pow_two]
    exact hsq.trans ((le_abs_self _).trans hdist)

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Curvature.Sparse


theorem expect_succ {m t : ℕ} (f : Hist m (t+1) → ℝ) :
    (𝔼 h, f h) = 𝔼 h : Hist m t, 𝔼 i : Fin m, f (h,i) := by
  calc
    _ = 𝔼 x : Hist m t × Fin m, f (x.1,x.2) :=
      Fintype.expect_equiv (ι := Hist m (t+1)) (κ := Hist m t × Fin m) (Equiv.refl _) _ _ (fun _ => rfl)
    _ = _ := by
      simpa only [Finset.univ_product_univ] using
        (Finset.expect_product (Finset.univ : Finset (Hist m t)) (Finset.univ : Finset (Fin m))
          (fun x => f (x.1,x.2)))


variable {m : ℕ}

def ratio (δ : ℝ) (j i : Fin m) : ℝ := if i = j then 1-δ else 1+δ/(m-1)

def likelihood (δ : ℝ) (j : Fin m) : (t : ℕ) → Hist m t → ℝ
  | 0, _ => 1
  | t+1, h => likelihood δ j t h.1 * ratio δ j h.2

private theorem special_sum (j : Fin m) (u v : ℝ) :
    (∑ i : Fin m, if i = j then u else v) = u + ((m:ℝ)-1)*v := by
  have hid (i : Fin m) : (if i=j then u else v) = v + (if i=j then u-v else 0) := by split_ifs <;> ring
  simp_rw [hid, Finset.sum_add_distrib]
  simp; ring

theorem ratio_moments (hm : 2 ≤ m) (δ : ℝ) (j : Fin m) :
    (𝔼 i, ratio δ j i) = 1 ∧ (𝔼 i, (ratio δ j i)^2) = 1 + δ^2/(m-1) := by
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m:ℝ) ≠ 0 := by linarith
  have hm1 : (m:ℝ)-1 ≠ 0 := by linarith
  constructor
  · simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, ratio, special_sum]
    field_simp
    ring
  · simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, ratio, apply_ite (fun x : ℝ => x^2),
      special_sum]
    field_simp
    ring

theorem likelihood_moments (hm : 2 ≤ m) (δ : ℝ) (j : Fin m) (s : ℕ) :
    (𝔼 h, likelihood δ j s h) = 1 ∧
    (𝔼 h, (likelihood δ j s h)^2) = (1+δ^2/(m-1))^s := by
  let : NeZero m := ⟨by omega⟩
  induction s with
  | zero => simp [likelihood]
  | succ t ih =>
    constructor
    · rw [expect_succ]; simp only [likelihood, ← Finset.mul_expect, (ratio_moments hm δ j).1,
        mul_one, ih.1]
    · rw [expect_succ, pow_succ (1+δ^2/(m-1)) t]; simp only [likelihood, mul_pow, ← Finset.mul_expect, (ratio_moments hm δ j).2,
        ← Finset.expect_mul, ih.2]

theorem likelihood_nonneg (hm : 2 ≤ m) {δ : ℝ} (hd0 : 0 ≤ δ) (hd1 : δ ≤ 1)
    (j : Fin m) (s : ℕ) (h : Hist m s) : 0 ≤ likelihood δ j s h := by
  induction s with
  | zero => exact zero_le_one
  | succ s ih =>
    apply mul_nonneg (ih h.1)
    have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
    dsimp [ratio]
    split_ifs
    · linarith
    · exact add_nonneg zero_le_one (div_nonneg hd0 (by linarith))

theorem variance_bound {n s : ℕ} (hm : 2 ≤ m) (hs : s ≤ n) {δ : ℝ}
    (hδ : (n:ℝ)*δ^2 ≤ (m:ℝ)*Real.log m/64) (j : Fin m) :
    (𝔼 h, (likelihood δ j s h - 1)^2) ≤ ((m:ℝ)-1)/32 := by
  let : NeZero m := ⟨by omega⟩
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : 0 < (m:ℝ)-1 := by linarith
  have hlog := Real.log_nonneg (show 1 ≤ (m:ℝ) by linarith)
  let v := δ^2/(m-1)
  have hv : 0 ≤ v := div_nonneg (sq_nonneg _) hm1.le
  have hexp : (s:ℝ) * v ≤ Real.log m / 32 := by
    dsimp [v]
    rw [← mul_div_assoc, div_le_iff₀ hm1]
    have hs' : (s:ℝ) ≤ n := by exact_mod_cast hs
    nlinarith [mul_le_mul_of_nonneg_right hs' (sq_nonneg δ),
      mul_nonneg (sub_nonneg.mpr hm') hlog]
  have hp : (1+v)^s ≤ 1 + ((m:ℝ)-1)/32 := by
    calc
      _ ≤ (Real.exp v)^s := pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp v]) _
      _ = Real.exp ((s:ℝ)*v) := (Real.exp_nat_mul v s).symm
      _ ≤ Real.exp (Real.log m/32) := Real.exp_le_exp.mpr hexp
      _ = (m:ℝ) ^ (1/32 : ℝ) := by rw [Real.rpow_def_of_pos (by positivity)]; congr 1; ring
      _ ≤ _ := by
        have h := rpow_one_add_le_one_add_mul_self (s := (m:ℝ)-1) (p := 1/32)
          (by linarith) (by norm_num) (by norm_num)
        convert h using 1 <;> ring_nf
  have he (h : Hist m s) : (likelihood δ j s h - 1)^2 =
      (likelihood δ j s h)^2 - 2*likelihood δ j s h + 1 := by ring
  simp_rw [he]
  rw [Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.mul_expect,
    (likelihood_moments hm δ j s).1, (likelihood_moments hm δ j s).2, Fintype.expect_one]
  dsimp [v] at hp
  linarith

structure Prediction (m : ℕ) where
  p : Fin m → ℝ
  nonneg : ∀ i, 0 ≤ p i
  normalized : ∑ i, p i = 1

theorem Prediction.le_one (p : Prediction m) (i : Fin m) : p.p i ≤ 1 :=
  (Finset.single_le_sum (fun j _ => p.nonneg j) (Finset.mem_univ i)).trans_eq p.normalized

theorem identification {n s : ℕ} (hm : 2 ≤ m) (hs : s ≤ n) {δ : ℝ}
    (hδ : (n:ℝ)*δ^2 ≤ (m:ℝ)*Real.log m/64) (p : Hist m s → Prediction m) :
    (𝔼 j : Fin m, 𝔼 h : Hist m s, likelihood δ j s h * (p h).p j) ≤ 2/3 := by
  let : NeZero m := ⟨by omega⟩
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : 0 < (m:ℝ) := by linarith
  have hpoint (j : Fin m) (h : Hist m s) :
      8*m*(likelihood δ j s h * (p h).p j) ≤
      8*m*(p h).p j + 16*(likelihood δ j s h - 1)^2 + (m:ℝ)^2*(p h).p j := by
    let x := (p h).p j
    have hx : 0 ≤ x := (p h).nonneg j
    have hx1 : x ≤ 1 := (p h).le_one j
    change 8*m*(likelihood δ j s h*x) ≤ 8*m*x + 16*(likelihood δ j s h - 1)^2 + (m:ℝ)^2*x
    nlinarith only [sq_nonneg (4*(likelihood δ j s h-1) - m*x),
      mul_nonneg (sq_nonneg (m:ℝ)) (mul_nonneg hx (sub_nonneg.mpr hx1))]
  have h := Finset.expect_le_expect (s := (Finset.univ : Finset (Fin m)))
    (fun j _ => Finset.expect_le_expect (s := (Finset.univ : Finset (Hist m s))) (fun h _ => hpoint j h))
  simp_rw [Finset.expect_add_distrib, ← Finset.mul_expect] at h
  have hmass : (𝔼 j : Fin m, 𝔼 h : Hist m s, (p h).p j) = 1/(m:ℝ) := by
    rw [Finset.expect_comm]
    simp [Fintype.expect_eq_sum_div_card (ι := Fin m), Prediction.normalized]
  rw [hmass] at h
  have hv : (𝔼 j : Fin m, 𝔼 h : Hist m s, (likelihood δ j s h - 1)^2) ≤ ((m:ℝ)-1)/32 := by
    rw [← Fintype.expect_const (ι := Fin m) (((m:ℝ)-1)/32)]
    exact Finset.expect_le_expect fun j _ => variance_bound hm hs hδ j
  have hfrac : 8 * (m:ℝ) * (1/m) = 8 := by field_simp
  have hfrac' : (m:ℝ)^2 * (1/m) = m := by field_simp
  rw [hfrac,hfrac'] at h
  by_contra! hbad
  nlinarith only [h,hv,hm',mul_pos hm0 (sub_pos.mpr hbad)]

end Curvature.Sparse
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Curvature.SignGame
variable {I : Type*} [Fintype I] [DecidableEq I]

def signSum (s : Finset I) (σ : I → Bool) : ℝ := ∑ j ∈ s, sign (σ j)

omit [Fintype I] in
private theorem signSum_flip (s : Finset I) (i : I) (hi : i ∉ s) (σ : I → Bool) :
    signSum s (flip i σ) = signSum s σ := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [flip_other (by rintro rfl; exact hi hj)]

theorem signSum_moments (s : Finset I) :
    (𝔼 σ, (signSum s σ)^2) = (s.card : ℝ) ∧
    (𝔼 σ, (signSum s σ)^4) = 3*(s.card : ℝ)^2 - 2*(s.card : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp [signSum]
  | @insert i s hi ih =>
    have hsum (σ : I → Bool) : signSum (insert i s) σ = sign (σ i) + signSum s σ := by
      simp [signSum, hi]
    constructor
    · rw [expect_pair i]
      calc
        _ = 𝔼 σ, (1 + (signSum s σ)^2) := by
          apply Finset.expect_congr rfl
          intro σ _
          rw [hsum, hsum, signSum_flip s i hi, flip_same, sign_not]
          cases σ i <;> simp [sign] <;> ring
        _ = _ := by simp [Finset.expect_add_distrib, ih.1, hi, add_comm]
    · rw [expect_pair i]
      calc
        _ = 𝔼 σ, (1 + 6*(signSum s σ)^2 + (signSum s σ)^4) := by
          apply Finset.expect_congr rfl
          intro σ _
          rw [hsum, hsum, signSum_flip s i hi, flip_same, sign_not]
          cases σ i <;> simp [sign] <;> ring
        _ = _ := by
          rw [Finset.expect_add_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
            Fintype.expect_one, ih.1, ih.2]
          simp [hi]
          ring

theorem signSum_abs_lower (s : Finset I) :
    Real.sqrt (s.card : ℝ) / 8 ≤ 𝔼 σ, |signSum s σ| := by
  by_cases hn : s.card = 0
  · simp [Finset.card_eq_zero.mp hn, signSum]
  have hn' : 0 < (s.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  let c := 2 * Real.sqrt (s.card : ℝ)
  have hc : 0 < c := mul_pos (by norm_num) (Real.sqrt_pos.mpr hn')
  have hc2 : c^2 = 4 * (s.card : ℝ) := by
    dsimp [c]; rw [mul_pow, Real.sq_sqrt hn'.le]; ring
  have hpoint (x : ℝ) : c^2*x^2 ≤ c^3 * |x| + x^4 := by
    by_cases hx : |x| ≤ c
    · calc
        _ = c^2 * |x| * |x| := by rw [mul_assoc, ← sq, sq_abs]
        _ ≤ c^2 * |x| * c := mul_le_mul_of_nonneg_left hx (by positivity)
        _ ≤ _ := by nlinarith [sq_nonneg (x^2)]
    · have h : c^2 ≤ x^2 := (sq_le_sq' (by linarith [abs_nonneg x]) (le_of_not_ge hx)).trans_eq (sq_abs x)
      nlinarith only [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr h), mul_nonneg (pow_nonneg hc.le 3) (abs_nonneg x)]
  have hav := Finset.expect_le_expect (s := (Finset.univ : Finset (I → Bool)))
    (fun σ _ => hpoint (signSum s σ))
  rw [← Finset.mul_expect, Finset.expect_add_distrib, ← Finset.mul_expect,
    (signSum_moments s).1, (signSum_moments s).2] at hav
  have hsrc : (s.card : ℝ)^2 ≤ c^3 * (𝔼 σ, |signSum s σ|) := by
    rw [hc2] at hav; linarith [sq_nonneg (s.card : ℝ)]
  have hroot := Real.sq_sqrt hn'.le
  have hc3 : c^3 = 8*(s.card : ℝ)*Real.sqrt (s.card : ℝ) := by
    dsimp [c]; linear_combination 8*Real.sqrt (s.card : ℝ)*hroot
  rw [hc3] at hsrc
  have hpos := mul_pos hn' (Real.sqrt_pos.mpr hn')
  apply (le_of_mul_le_mul_left (a := (s.card : ℝ) * Real.sqrt (s.card : ℝ)) _ hpos)
  calc
    _ = (s.card : ℝ)^2 / 8 := by linear_combination (s.card : ℝ)/8 * hroot
    _ ≤ _ := by linarith only [hsrc]

end Curvature.SignGame
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace NNReal
namespace Curvature.Coordinate

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


def coord (c : E) (U : Axes r →ₗᵢ[ℝ] E) (i : Fin r) (x : E) : ℝ :=
  ⟪U (EuclideanSpace.single i 1), x - c⟫_ℝ

@[simp] theorem coord_position (c : E) (U : Axes r →ₗᵢ[ℝ] E) (i : Fin r) (z : Axes r) :
    coord c U i (position c U z) = z i := by
  simp [position, coord, U.inner_map_map, EuclideanSpace.inner_single_left]


def axesLength (a : Fin r → ℝ) : ℝ := Real.sqrt (∑ i, (a i)^2)

def inscribed (a : Fin r → ℝ) (i : Fin r) : ℝ := (a i)^2 / axesLength a

theorem length_pos [NeZero r] {a : Fin r → ℝ} (ha : ∀ i, 0 < a i) :
    0 < axesLength a := by
  apply Real.sqrt_pos.mpr
  exact Finset.sum_pos (fun i _ => sq_pos_of_pos (ha i)) Finset.univ_nonempty

theorem inscribed_sum [NeZero r] {a : Fin r → ℝ} (ha : ∀ i, 0 < a i) :
    ∑ i, inscribed a i = axesLength a := by
  simp only [inscribed, ← Finset.sum_div]
  apply (div_eq_iff (length_pos ha).ne').mpr
  rw [← sq, axesLength, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (a i)))]

theorem box_subset_ellipsoid [NeZero r] (c : E) (U : Axes r →ₗᵢ[ℝ] E)
    {a : Fin r → ℝ} (ha : ∀ i, 0 < a i) :
    box c U (inscribed a) ⊆ ellipsoid c U a := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨z, ?_, rfl⟩
  change (∑ i, (z i / a i)^2) ≤ 1
  have hL := length_pos ha
  have hsum : ∑ i, (a i / axesLength a)^2 = 1 := by
    simp only [div_pow, ← Finset.sum_div]
    rw [div_eq_one_iff_eq (pow_ne_zero _ hL.ne'), axesLength, Real.sq_sqrt]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (a i)
  rw [← hsum]
  apply Finset.sum_le_sum
  intro i _
  have habs : |z i / a i| ≤ a i / axesLength a := by
    rw [abs_div, abs_of_pos (ha i), div_le_iff₀ (ha i)]
    have hi := hz i
    unfold inscribed at hi
    exact hi.trans_eq (by ring)
  exact sq_le_sq' (by linarith [neg_abs_le (z i / a i)]) (le_trans (le_abs_self _) habs)

theorem ellipsoid_subset_box (c : E) (U : Axes r →ₗᵢ[ℝ] E)
    {a : Fin r → ℝ} (ha : ∀ i, 0 < a i) :
    ellipsoid c U a ⊆ box c U a := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨z, ?_, rfl⟩
  intro i
  have hi : (z i / a i)^2 ≤ 1 :=
    (Finset.single_le_sum (f := fun j => (z j / a j)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)).trans hz
  have hs : |z i / a i| ≤ 1 := by nlinarith [sq_abs (z i / a i)]
  rw [abs_div, abs_of_pos (ha i), div_le_iff₀ (ha i), one_mul] at hs
  exact hs

def vertex (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Fin r → ℝ) (σ : Fin r → Bool) : E :=
  position c U (WithLp.toLp 2 (fun i => a i * SignGame.sign (σ i)))

@[simp] theorem coord_vertex (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Fin r → ℝ)
    (σ : Fin r → Bool) (i : Fin r) : coord c U i (vertex c U a σ) = a i * SignGame.sign (σ i) := by
  simp [vertex]

theorem vertex_mem (c : E) (U : Axes r →ₗᵢ[ℝ] E) {a : Fin r → ℝ}
    (ha : ∀ i, 0 ≤ a i) (σ : Fin r → Bool) : vertex c U a σ ∈ box c U a := by
  refine ⟨_, ?_, rfl⟩
  intro i
  simp [abs_mul, abs_of_nonneg (ha i)]

def loss (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Fin r → ℝ) (G : ℝ) (i : Fin r)
    (b : Bool) (x : E) : ℝ := G * |coord c U i x - a i * SignGame.sign b|

theorem loss_lipschitz (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Fin r → ℝ)
    (G : ℝ≥0) (i : Fin r) (b : Bool) : LipschitzWith G (loss c U a G i b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  simp only [loss, ← mul_sub, abs_mul, abs_of_nonneg G.coe_nonneg]
  apply mul_le_mul_of_nonneg_left _ G.coe_nonneg
  apply (abs_abs_sub_abs_le_abs_sub _ _).trans
  rw [sub_sub_sub_cancel_right, coord, coord, ← inner_sub_right, sub_sub_sub_cancel_right]
  simpa using abs_real_inner_le_norm (U (EuclideanSpace.single i 1)) (x-y)

theorem loss_convex (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Fin r → ℝ)
    (G : ℝ≥0) (i : Fin r) (b : Bool) : ConvexOn ℝ Set.univ (loss c U a G i b) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t hs ht hst
  have hsplit : s • x + t • y - c = s • (x-c) + t • (y-c) := by
    rw [smul_sub, smul_sub, show s • x - s • c + (t • y - t • c) =
      s • x + t • y - (s • c + t • c) by abel, ← add_smul, hst, one_smul]
  simp only [loss, coord, hsplit, inner_add_right, real_inner_smul_right, smul_eq_mul]
  set v := a i * SignGame.sign b
  set X := ⟪U (EuclideanSpace.single i 1), x-c⟫_ℝ
  set Y := ⟪U (EuclideanSpace.single i 1), y-c⟫_ℝ
  have heq : s*X + t*Y - v = s*(X-v) + t*(Y-v) := by linear_combination v*hst
  rw [heq]
  have hu := abs_add_le (s*(X-v)) (t*(Y-v))
  rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht] at hu
  nlinarith only [mul_le_mul_of_nonneg_left hu G.coe_nonneg]

end Curvature.Coordinate
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

/-- A finite collection of directions whose convex hull contains the Euclidean half-ball. -/
theorem exists_width_directions (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ (N : ℕ) (q : Fin N → E), (∀ j, ‖q j‖ ≤ 1) ∧
      ∀ v : E, ‖v‖ ≤ 1 → (1/2 : ℝ) • v ∈ convexHull ℝ (Set.range q) := by
  classical
  let S := Metric.closedBall (0:E) 1
  have hc : IsCompact S := isCompact_closedBall _ _
  have hn : S.Nonempty := ⟨0, Metric.mem_closedBall_self (by norm_num)⟩
  obtain ⟨t, ht, hfin, hcover⟩ := hc.finite_cover_balls (by norm_num : (0:ℝ)<1/2)
  let := hfin.fintype
  let q (j : Fin (Fintype.card t)) := ((Fintype.equivFin t).symm j).val
  have hr : Set.range q = t := by
    ext x
    constructor
    · rintro ⟨j,rfl⟩; exact ((Fintype.equivFin t).symm j).property
    · intro hx; exact ⟨(Fintype.equivFin t) ⟨x,hx⟩, by simp [q]⟩
  refine ⟨_,q,fun j => ?_, ?_⟩
  · have := ht (hr ▸ Set.mem_range_self j)
    simpa [S] using this
  · intro v hv
    rw [hr]
    by_contra hnot
    obtain ⟨f,k,hf,hk⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ t)
      (hfin.isCompact_convexHull ℝ).isClosed hnot
    obtain ⟨x,hx,hmax⟩ := hc.exists_isMaxOn hn f.continuous.continuousOn
    obtain ⟨w,hw,hd⟩ := Set.mem_iUnion₂.mp (hcover hx)
    have hnorm : ‖x-w‖ < 1/2 := by simpa [Metric.mem_ball, dist_eq_norm] using hd
    have hrem : (2:ℝ) • (x-w) ∈ S := by
      simp [S,norm_smul,Metric.mem_closedBall,dist_zero_right]
      linarith
    have hp := hmax hrem
    have hq := hf w (subset_convexHull ℝ t hw)
    have hv' : v ∈ S := by simpa [S] using hv
    have hvmax := hmax hv'
    change f ((2:ℝ) • (x-w)) ≤ f x at hp
    change f v ≤ f x at hvmax
    simp only [map_smul, map_sub, smul_eq_mul] at hp hk
    linarith

end Curvature
end
end

section
set_option autoImplicit false
namespace Curvature

variable {d : ℕ}


theorem dotProduct_le_norm₂_mul (x y : Vec d) :
    dotProduct x y ≤ norm₂ x * norm₂ y := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hsq : dotProduct x y ^ 2 ≤ (norm₂ x * norm₂ y) ^ 2 := by
    rw [mul_pow, norm₂_sq, norm₂_sq]
    simpa only [pow_two, dotProduct] using h
  exact le_of_sq_le_sq hsq (mul_nonneg (norm₂_nonneg x) (norm₂_nonneg y))


end Curvature
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Curvature.Sparse

variable {m : ℕ}

abbrev Strategy (m : ℕ) := (t : ℕ) → Hist m t → Prediction m

def cumulative (p : Strategy m) : (t : ℕ) → Hist m t → ℝ
  | 0, _ => 0
  | t+1, h => cumulative p t h.1 + (p t h.1).p h.2

def count (j : Fin m) : (t : ℕ) → Hist m t → ℝ
  | 0, _ => 0
  | t+1, h => count j t h.1 + if h.2 = j then 1 else 0

theorem count_sum (t : ℕ) (h : Hist m t) : ∑ j, count j t h = t := by
  induction t with
  | zero => simp [count]
  | succ t ih =>
    simp only [count, Finset.sum_add_distrib, ih]
    simp

def bestCount [NeZero m] (t : ℕ) (h : Hist m t) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun j : Fin m => count j t h)

theorem bestCount_le [NeZero m] (t : ℕ) (h : Hist m t) (j : Fin m) :
    bestCount t h ≤ count j t h := Finset.inf'_le _ (Finset.mem_univ _)

theorem bestCount_budget [NeZero m] (t : ℕ) (h : Hist m t) : bestCount t h ≤ t/(m:ℝ) := by
  have hs := Finset.expect_le_expect (s := (Finset.univ : Finset (Fin m))) (fun j _ => bestCount_le t h j)
  rw [Finset.expect_const Finset.univ_nonempty] at hs
  simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, count_sum] using hs

theorem round_gap (hm : 2 ≤ m) (δ : ℝ) (j : Fin m) (p : Prediction m) :
    (𝔼 i : Fin m, ratio δ j i * (p.p i - (if i=j then 1 else 0))) = δ/(m-1)*(1-p.p j) := by
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m:ℝ) ≠ 0 := by linarith
  have hm1 : (m:ℝ)-1 ≠ 0 := by linarith
  have h (i : Fin m) :
      ratio δ j i * (p.p i - (if i=j then 1 else 0)) =
      (1+δ/(m-1))*p.p i + (if i=j then (1-δ)*(p.p j-1) - (1+δ/(m-1))*p.p j else 0) := by
    by_cases hi : i=j <;> simp [ratio, hi]
  simp_rw [h]
  rw [Fintype.expect_eq_sum_div_card, Finset.sum_add_distrib, ← Finset.mul_sum, p.normalized]
  simp
  field_simp
  ring

def gain (p : Strategy m) (δ : ℝ) (t : ℕ) : ℝ :=
  𝔼 j : Fin m, 𝔼 h : Hist m t, likelihood δ j t h * (cumulative p t h - count j t h)

theorem gain_succ (hm : 2 ≤ m) (p : Strategy m) (δ : ℝ) (t : ℕ) :
    gain p δ (t+1) = gain p δ t +
    δ/(m-1) * (1 - (𝔼 j : Fin m, 𝔼 h : Hist m t, likelihood δ j t h * (p t h).p j)) := by
  let : NeZero m := ⟨by omega⟩
  have hstep (j : Fin m) (h : Hist m t) :
      (𝔼 i : Fin m, likelihood δ j (t+1) (h,i) * (cumulative p (t+1) (h,i) - count j (t+1) (h,i))) =
      likelihood δ j t h * (cumulative p t h - count j t h) +
        δ/(m-1) * (likelihood δ j t h - likelihood δ j t h*(p t h).p j) := by
    have he (i : Fin m) :
        likelihood δ j (t+1) (h,i) * (cumulative p (t+1) (h,i) - count j (t+1) (h,i)) =
        (likelihood δ j t h * (cumulative p t h - count j t h))*ratio δ j i +
          likelihood δ j t h * (ratio δ j i * ((p t h).p i - (if i=j then 1 else 0))) := by
      simp only [likelihood, cumulative, count]
      ring
    simp_rw [he]
    rw [Finset.expect_add_distrib, ← Finset.mul_expect, ← Finset.mul_expect,
      (ratio_moments hm δ j).1, round_gap hm δ j (p t h)]
    ring
  unfold gain
  simp_rw [expect_succ (t := t), hstep, Finset.expect_add_distrib, ← Finset.mul_expect,
    Finset.expect_sub_distrib, (likelihood_moments hm δ _ t).1]
  simp

theorem gain_lower (hm : 2 ≤ m) (p : Strategy m) {n : ℕ} {δ : ℝ}
    (hd : 0 ≤ δ) (hδ : (n:ℝ)*δ^2 ≤ (m:ℝ)*Real.log m/64) :
    ∀ t ≤ n, (t:ℝ)* (δ/(3*(m-1))) ≤ gain p δ t := by
  let : NeZero m := ⟨by omega⟩
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have den : 0 ≤ δ / (m-1) := div_nonneg hd (by linarith)
  intro t
  induction t with
  | zero => intro _; simp [gain, cumulative, count]
  | succ t ih =>
    intro ht
    have ht' : t ≤ n := Nat.le_of_succ_le ht
    have hh := identification hm ht' hδ (p t)
    have hg := ih ht'
    rw [gain_succ hm, Nat.cast_succ]
    have he : δ/(3*((m:ℝ)-1)) = (δ/((m:ℝ)-1))/3 := by rw [div_div, mul_comm]
    rw [he] at hg ⊢
    nlinarith only [hg, mul_nonneg den (sub_nonneg.mpr hh)]

theorem exists_sequence_gap (hm : 2 ≤ m) (p : Strategy m) {n : ℕ} {δ : ℝ}
    (hd0 : 0 ≤ δ) (hd1 : δ ≤ 1) (hδ : (n:ℝ)*δ^2 ≤ (m:ℝ)*Real.log m/64) :
    letI : NeZero m := ⟨by omega⟩
    ∃ h : Hist m n, (n:ℝ)*(δ/(3*(m-1))) ≤ cumulative p n h - bestCount n h := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨w,_,hw⟩ := Finset.exists_max_image (Finset.univ : Finset (Hist m n))
    (fun h => cumulative p n h - bestCount n h) Finset.univ_nonempty
  let M := cumulative p n w - bestCount n w
  refine ⟨w, (gain_lower hm p hd0 hδ n le_rfl).trans ?_⟩
  change gain p δ n ≤ M
  have hb (j : Fin m) (h : Hist m n) :
      cumulative p n h - count j n h ≤ M :=
    (sub_le_sub_left (bestCount_le n h j) _).trans (hw h (Finset.mem_univ _))
  have hav (j : Fin m) : (𝔼 h : Hist m n, likelihood δ j n h * (cumulative p n h - count j n h)) ≤ M := by
    have h := Finset.expect_le_expect (fun h (_ : h ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hb j h) (likelihood_nonneg hm hd0 hd1 j n h))
    simpa only [← Finset.expect_mul, (likelihood_moments hm δ j n).1, one_mul] using h
  unfold gain
  calc
    _ ≤ 𝔼 _ : Fin m, M := Finset.expect_le_expect (fun j _ => hav j)
    _ = _ := Fintype.expect_const M

def gapParameter (m n : ℕ) : ℝ := Real.sqrt (m*Real.log m/(64*n))

theorem gapParameter_bounds {n : ℕ} (hm : 2 ≤ m) (hn : m*Real.log m ≤ n) :
    let δ := gapParameter m n
    0 ≤ δ ∧ δ ≤ 1 ∧ (n:ℝ)*δ^2 = m*Real.log m/64 ∧
      Real.sqrt (n*Real.log m/m)/24 ≤ (n:ℝ)*(δ/(3*(m-1))) := by
  let δ := gapParameter m n
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : 0 < (m:ℝ) := by linarith
  have hm1 : 0 < (m:ℝ)-1 := by linarith
  have hlog := Real.log_pos (show 1 < (m:ℝ) by linarith)
  have hn0 : 0 < (n:ℝ) := (mul_pos hm0 hlog).trans_le hn
  have hd : 0 ≤ δ := Real.sqrt_nonneg _
  have hsq : δ^2 = m*Real.log m/(64*n) := Real.sq_sqrt (by positivity)
  have hid : (n:ℝ)*δ^2 = m*Real.log m/64 := by rw [hsq]; field_simp
  refine ⟨hd, ?_, hid, ?_⟩
  · apply Real.sqrt_le_iff.mpr
    exact ⟨zero_le_one, (div_le_iff₀ (by positivity)).mpr (by nlinarith)⟩
  · change Real.sqrt (n*Real.log m/m)/24 ≤ (n:ℝ)*(δ/(3*(m-1)))
    have hs : Real.sqrt (n*Real.log m/m) = (8*n*δ)/m := by
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
      rw [div_pow, mul_pow, hsq]
      field_simp
      ring
    rw [hs]
    have hden := div_le_div_of_nonneg_left hd (show 0 < 3*((m:ℝ)-1) by positivity)
      (show 3*((m:ℝ)-1) ≤ 3*m by linarith)
    calc
      _ = (n:ℝ)*(δ/(3*m)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hden hn0.le

structure RandomizedStrategy (m : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  predict : (t : ℕ) → Hist m t → Ω → Prediction m
  measurable : ∀ t h j, Measurable (fun ω => (predict t h ω).p j)

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (L : RandomizedStrategy m Ω)

theorem prediction_integrable (t : ℕ) (h : Hist m t) (j : Fin m) :
    Integrable (fun ω => (L.predict t h ω).p j) μ := by
  apply (integrable_const (1 : ℝ)).mono' (L.measurable t h j).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg ((L.predict t h ω).nonneg j)]
    exact (L.predict t h ω).le_one j

def meanStrategy : Strategy m := fun t h => {
  p := fun j => ∫ ω, (L.predict t h ω).p j ∂μ
  nonneg := fun j => integral_nonneg (fun ω => (L.predict t h ω).nonneg j)
  normalized := by
    rw [← integral_finsetSum _ (fun j _ => prediction_integrable μ L t h j)]
    simp [Prediction.normalized] }

def realized (t : ℕ) (h : Hist m t) (ω : Ω) : ℝ :=
  cumulative (fun s h => L.predict s h ω) t h

theorem realized_integral (t : ℕ) (h : Hist m t) :
    Integrable (realized L t h) μ ∧ (∫ ω, realized L t h ω ∂μ) = cumulative (meanStrategy μ L) t h := by
  induction t with
  | zero => exact ⟨integrable_zero _ _ _, by simp [realized, cumulative]⟩
  | succ t ih =>
    obtain ⟨hint, he⟩ := ih h.1
    have hi := prediction_integrable μ L t h.1 h.2
    constructor
    · exact hint.add hi
    · change (∫ ω, realized L t h.1 ω + (L.predict t h.1 ω).p h.2 ∂μ) = _
      rw [integral_add hint hi, he]
      rfl

theorem experts_lower {n : ℕ} (hm : 2 ≤ m) (hn : m*Real.log m ≤ n) :
    letI : NeZero m := ⟨by omega⟩
    (∀ h : Hist m n, bestCount n h ≤ n/(m:ℝ)) ∧
    ∃ h : Hist m n, Real.sqrt (n*Real.log m/m)/24 ≤
      ∫ ω, realized L n h ω - bestCount n h ∂μ := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨hd0,hd1,hsq,hl⟩ := gapParameter_bounds hm hn
  obtain ⟨h,hh⟩ := exists_sequence_gap hm (meanStrategy μ L) hd0 hd1 hsq.le
  refine ⟨fun h => bestCount_budget n h, h, ?_⟩
  obtain ⟨hi,he⟩ := realized_integral μ L n h
  rw [integral_sub hi (integrable_const _), he, integral_const, probReal_univ, one_smul]
  exact hl.trans hh

end Curvature.Sparse
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory
namespace Curvature.Coordinate

abbrev Round (r n : ℕ) := Fin r × Fin n

def Earlier {r n : ℕ} (s t : Round r n) : Prop :=
  s.1 < t.1 ∨ s.1 = t.1 ∧ s.2 < t.2

abbrev History (E : Type*) {r n : ℕ} (t : Round r n) :=
  {s : Round r n // Earlier s t} → E → ℝ

structure Learner (E Ω : Type*) [MeasurableSpace E] [MeasurableSpace Ω] (K : Set E) (r n : ℕ) where
  predict : (t : Round r n) → History E t → Ω → E
  mem : ∀ t h ω, predict t h ω ∈ K
  measurable : ∀ t h, Measurable (predict t h)

variable {r n : ℕ} {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Fin r → ℝ) (G : ℝ≥0)

def past (σ : Round r n → Bool) (t : Round r n) : History E t :=
  fun s => loss c U a G s.val.1 (σ s.val)

theorem past_flip (σ : Round r n → Bool) (t : Round r n) :
    past c U a G (SignGame.flip t σ) t = past c U a G σ t := by
  funext s
  have hne : s.val ≠ t := by
    rintro he
    have h := s.property
    simp [he, Earlier] at h
  simp [past, SignGame.flip_other hne]

def total (σ : Round r n → Bool) (x : E) : ℝ := ∑ t, loss c U a G t.1 (σ t) x

def best (K : Set E) (σ : Round r n → Bool) : ℝ := sInf (total c U a G σ '' K)

def budget (K : Set E) (σ : Round r n → Bool) : ℝ :=
  best c U a G K σ - ∑ t, sInf (loss c U a G t.1 (σ t) '' K)

def blockSum (σ : Round r n → Bool) (i : Fin r) : ℝ := ∑ j, SignGame.sign (σ (i,j))

def majority (σ : Round r n → Bool) (i : Fin r) : Bool := decide (0 ≤ blockSum σ i)

theorem majority_mul (σ : Round r n → Bool) (i : Fin r) :
    SignGame.sign (majority σ i) * blockSum σ i = |blockSum σ i| := by
  by_cases h : 0 ≤ blockSum σ i
  · simp [majority, SignGame.sign, h, abs_of_nonneg h]
  · simp [majority, SignGame.sign, h, abs_of_neg (lt_of_not_ge h)]

private theorem loss_vertex (ha : ∀ i, 0 ≤ a i) (i : Fin r) (σ : Fin r → Bool) (b : Bool) :
    loss c U a G i b (vertex c U a σ) = G * a i * (1 - SignGame.sign (σ i)*SignGame.sign b) := by
  simp only [loss, coord_vertex, ← mul_sub, abs_mul, abs_of_nonneg (ha i)]
  cases σ i <;> cases b <;> norm_num [SignGame.sign] <;> ring

theorem total_majority (ha : ∀ i, 0 ≤ a i) (σ : Round r n → Bool) :
    total c U a G σ (vertex c U a (majority σ)) = ∑ i, (G * a i * (n - |blockSum σ i|)) := by
  unfold total
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [loss_vertex c U a G ha, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [← blockSum, majority_mul]

theorem round_min_zero {K : Set E} (ha : ∀ i, 0 ≤ a i) (hK : box c U a ⊆ K)
    (i : Fin r) (b : Bool) : sInf (loss c U a G i b '' K) = 0 := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨vertex c U a (fun _ => b), hK (vertex_mem c U ha _), by simp [loss]⟩
  · rintro _ ⟨w, _, rfl⟩
    exact mul_nonneg G.coe_nonneg (abs_nonneg _)

theorem best_le_majority {K : Set E} (ha : ∀ i, 0 ≤ a i) (hK : box c U a ⊆ K)
    (σ : Round r n → Bool) :
    best c U a G K σ ≤ ∑ i, (G * a i * (n - |blockSum σ i|)) := by
  rw [← total_majority c U a G ha σ]
  unfold best
  apply csInf_le _ (Set.mem_image_of_mem _ (hK (vertex_mem c U ha _)))
  refine ⟨0, ?_⟩
  rintro _ ⟨w, _, rfl⟩
  exact Finset.sum_nonneg fun t _ => mul_nonneg G.coe_nonneg (abs_nonneg _)

theorem budget_eq_best {K : Set E} (ha : ∀ i, 0 ≤ a i) (hK : box c U a ⊆ K)
    (σ : Round r n → Bool) : budget c U a G K σ = best c U a G K σ := by
  simp [budget, round_min_zero c U a G ha hK]

theorem budget_le {K : Set E} (ha : ∀ i, 0 ≤ a i) (hK : box c U a ⊆ K)
    (σ : Round r n → Bool) : budget c U a G K σ ≤ n * (G * ∑ i, a i) := by
  rw [budget_eq_best c U a G ha hK]
  apply (best_le_majority c U a G ha hK σ).trans
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  nlinarith only [mul_nonneg (mul_nonneg G.coe_nonneg (ha i)) (abs_nonneg (blockSum σ i))]

theorem budget_one {K : Set E} (ha : ∀ i, 0 ≤ a i) (hK : box c U a ⊆ K)
    (σ : Round r 1 → Bool) : budget c U a G K σ = 0 := by
  rw [budget_eq_best c U a G ha hK]
  apply le_antisymm
  · simpa [blockSum] using best_le_majority c U a G ha hK σ
  · apply le_csInf
    · exact ⟨_, ⟨_, hK (vertex_mem c U ha (fun _ => true)), rfl⟩⟩
    · rintro _ ⟨w, _, rfl⟩
      exact Finset.sum_nonneg fun t _ => mul_nonneg G.coe_nonneg (abs_nonneg _)

theorem blockSum_abs_lower (i : Fin r) :
    Real.sqrt n / 8 ≤ 𝔼 σ : Round r n → Bool, |blockSum σ i| := by
  let s : Finset (Round r n) := Finset.univ.image (fun j : Fin n => (i,j))
  have hinj : Function.Injective (fun j : Fin n => (i,j)) := fun _ _ h => congrArg Prod.snd h
  have hcard : s.card = n := by simp [s, Finset.card_image_of_injective _ hinj]
  have hsum (σ : Round r n → Bool) : SignGame.signSum s σ = blockSum σ i := by
    simp [s, SignGame.signSum, Finset.sum_image (f := fun t => SignGame.sign (σ t))
      (fun _ _ _ _ h => hinj h), blockSum]
  simpa only [hsum, hcard] using SignGame.signSum_abs_lower s

variable [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
variable {K : Set E} (μ : Measure Ω) [IsProbabilityMeasure μ] (L : Learner E Ω K r n)

def played (σ : Round r n → Bool) (t : Round r n) (ω : Ω) : ℝ :=
  loss c U a G t.1 (σ t) (L.predict t (past c U a G σ t) ω)

def regret (σ : Round r n → Bool) (ω : Ω) : ℝ :=
  (∑ t, played c U a G L σ t ω) - best c U a G K σ

theorem played_integrable (A : Fin r → ℝ) (hb : K ⊆ box c U A)
    (σ : Round r n → Bool) (t : Round r n) : Integrable (played c U a G L σ t) μ := by
  apply (integrable_const (G * (A t.1 + |a t.1|) : ℝ)).mono'
  · exact ((loss_lipschitz c U a G t.1 (σ t)).continuous.measurable.comp
      (L.measurable t _)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro ω
    obtain ⟨z, hz, he⟩ := hb (L.mem t (past c U a G σ t) ω)
    have hcoord := congrArg (coord c U t.1) he
    simp only [coord_position] at hcoord
    simp only [played, loss, Real.norm_eq_abs, abs_mul, abs_of_nonneg G.coe_nonneg, abs_abs,
      ← hcoord]
    apply mul_le_mul_of_nonneg_left _ G.coe_nonneg
    have ht := abs_sub (z t.1) (a t.1 * SignGame.sign (σ t))
    simp only [abs_mul, SignGame.abs_sign, mul_one] at ht
    exact ht.trans (add_le_add (hz t.1) le_rfl)

theorem played_expect_lower (A : Fin r → ℝ) (hb : K ⊆ box c U A) (t : Round r n) :
    G * a t.1 ≤ 𝔼 σ, ∫ ω, played c U a G L σ t ω ∂μ := by
  apply SignGame.round_loss μ t (a t.1) G G.coe_nonneg
    (fun σ ω => coord c U t.1 (L.predict t (past c U a G σ t) ω))
  · intro σ ω
    rw [past_flip]
  · exact fun σ => played_integrable c U a G μ L A hb σ t

theorem regret_expect_lower (A : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hK : box c U a ⊆ K) (hb : K ⊆ box c U A) :
    (∑ i, G * a i * (𝔼 σ : Round r n → Bool, |blockSum σ i|)) ≤
      𝔼 σ, ∫ ω, regret c U a G L σ ω ∂μ := by
  have hsplit (σ : Round r n → Bool) :
      (∫ ω, regret c U a G L σ ω ∂μ) =
      (∑ t, ∫ ω, played c U a G L σ t ω ∂μ) - best c U a G K σ := by
    have hint := fun t (_ : t ∈ Finset.univ) => played_integrable c U a G μ L A hb σ t
    simp only [regret, integral_sub (integrable_finsetSum Finset.univ hint) (integrable_const _),
      integral_finsetSum Finset.univ hint, integral_const, probReal_univ, one_smul]
  simp_rw [hsplit]
  rw [Finset.expect_sub_distrib, Finset.expect_sum_comm]
  have hp : (∑ t : Round r n, (G : ℝ) * a t.1) ≤
      ∑ t, 𝔼 σ, ∫ ω, played c U a G L σ t ω ∂μ :=
    Finset.sum_le_sum fun t _ => played_expect_lower c U a G μ L A hb t
  have hbest := Finset.expect_le_expect (s := (Finset.univ : Finset (Round r n → Bool)))
    (fun σ _ => best_le_majority c U a G ha hK σ)
  rw [Finset.expect_sum_comm] at hbest
  simp_rw [← Finset.mul_expect, Finset.expect_sub_distrib, Fintype.expect_const] at hbest
  rw [Fintype.sum_prod_type] at hp
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hp
  have heq :
      (∑ i, (n : ℝ) * (G * a i)) -
        (∑ i, (G * a i * (n - (𝔼 σ : Round r n → Bool, |blockSum σ i|)))) =
      ∑ i, G * a i * (𝔼 σ : Round r n → Bool, |blockSum σ i|) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← heq]
  exact sub_le_sub hp hbest

theorem exists_block_sequence (A : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hK : box c U a ⊆ K) (hb : K ⊆ box c U A) :
    ∃ σ : Round r n → Bool, budget c U a G K σ ≤ n * (G * ∑ i, a i) ∧
      (G * ∑ i, a i) * (Real.sqrt n / 8) ≤ ∫ ω, regret c U a G L σ ω ∂μ := by
  have hm : (G * ∑ i, a i) * (Real.sqrt n / 8) ≤
      ∑ i, G * a i * (𝔼 σ : Round r n → Bool, |blockSum σ i|) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (blockSum_abs_lower i) (mul_nonneg G.coe_nonneg (ha i))
  obtain ⟨σ, _, hs⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty
    (hm.trans (regret_expect_lower c U a G μ L A ha hK hb))
  exact ⟨σ, budget_le c U a G ha hK σ, hs⟩

theorem exists_clean_sequence (L₁ : Learner E Ω K r 1) (A : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hK : box c U a ⊆ K) (hb : K ⊆ box c U A) :
    ∃ σ : Round r 1 → Bool, budget c U a G K σ = 0 ∧
      G * (∑ i, a i) ≤ ∫ ω, regret c U a G L₁ σ ω ∂μ := by
  have hm := regret_expect_lower c U a G μ L₁ A ha hK hb
  simp [blockSum, ← Finset.mul_sum] at hm
  obtain ⟨σ, _, hs⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hm
  exact ⟨σ, budget_one c U a G ha hK σ, hs⟩

end Curvature.Coordinate
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory
namespace Curvature.Coordinate

variable {r : ℕ} {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]

def HasSequence (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Fin r → ℝ) (G : ℝ≥0)
    (K : Set E) (μ : Measure Ω) (L : (n : ℕ) → Learner E Ω K r n) (b R : ℝ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ (∀ σ : Round r n → Bool, budget c U a G K σ ≤ b) ∧
    ∃ σ : Round r n → Bool, R ≤ ∫ ω, regret c U a G (L n) σ ω ∂μ

theorem exists_budget_sequence [NeZero r] (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a A : Fin r → ℝ)
    (ha : ∀ i, 0 < a i) (G : ℝ≥0) (hG : 0 < G) {K : Set E}
    (hin : box c U a ⊆ K) (hout : K ⊆ box c U A)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L : (n : ℕ) → Learner E Ω K r n)
    (b : ℝ) (hb : 0 ≤ b) :
    let S := (G : ℝ) * ∑ i, a i
    HasSequence c U a G K μ L b ((S + Real.sqrt (S*b)) / 32) := by
  let S := (G : ℝ) * ∑ i, a i
  change HasSequence c U a G K μ L b ((S + Real.sqrt (S*b)) / 32)
  have hS : 0 < S := mul_pos (by exact_mod_cast hG)
    (Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty)
  by_cases hsmall : b ≤ 2*S
  · obtain ⟨σ, _, hreg⟩ := exists_clean_sequence c U a G μ (L 1) A (fun i => (ha i).le) hin hout
    refine ⟨1, by decide, fun σ => (budget_one c U a G (fun i => (ha i).le) hin σ).le.trans hb,
      σ, le_trans ?_ hreg⟩
    change (S + Real.sqrt (S*b)) / 32 ≤ S
    have hsr : Real.sqrt (S*b) ≤ 2*S := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨by positivity, by nlinarith [mul_le_mul_of_nonneg_left hsmall hS.le, sq_nonneg S]⟩
    linarith
  · let n := ⌊b/S⌋₊
    have hr : 2 ≤ b/S := (le_div_iff₀ hS).mpr (le_of_not_ge hsmall)
    have hn : 1 ≤ n := by apply Nat.le_floor; norm_num; linarith
    have hfloor : (n : ℝ)*S ≤ b :=
      (le_div_iff₀ hS).mp (Nat.floor_le (by linarith : 0 ≤ b/S))
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hd : b ≤ 2 * n * S := by
      have h : b/S < (n : ℝ) + 1 := Nat.lt_floor_add_one _
      apply (div_le_iff₀ hS).mp
      linarith
    obtain ⟨σ, _, hreg⟩ := exists_block_sequence c U a G μ (L n) A (fun i => (ha i).le) hin hout
    refine ⟨n, hn, fun σ => (budget_le c U a G (fun i => (ha i).le) hin σ).trans hfloor,
      σ, le_trans ?_ hreg⟩
    change (S + Real.sqrt (S*b)) / 32 ≤ S * (Real.sqrt n / 8)
    have hnroot : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn'
    have hrn := Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity)
    have hsr : Real.sqrt (S*b) ≤ 2*S*Real.sqrt n := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      calc
        _ ≤ S * (2*n*S) := mul_le_mul_of_nonneg_left hd hS.le
        _ ≤ _ := by
          rw [mul_pow, hrn]
          nlinarith [mul_nonneg (sq_nonneg S) (show 0 ≤ (n:ℝ) by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hnroot hS.le]

theorem box_lower [NeZero r] (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Fin r → ℝ)
    (ha : ∀ i, 0 < a i) (G : ℝ≥0) (hG : 0 < G) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L : (n : ℕ) → Learner E Ω (box c U a) r n) (b : ℝ) (hb : 0 ≤ b) :
    let S := (G : ℝ) * ∑ i, a i
    HasSequence c U a G (box c U a) μ L b ((S + Real.sqrt (S*b)) / 32) :=
  exists_budget_sequence c U a a ha G hG (Set.Subset.refl _) (Set.Subset.refl _) μ L b hb

theorem ellipsoid_lower [NeZero r] (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Fin r → ℝ)
    (ha : ∀ i, 0 < a i) (G : ℝ≥0) (hG : 0 < G) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L : (n : ℕ) → Learner E Ω (ellipsoid c U a) r n) (b : ℝ) (hb : 0 ≤ b) :
    let S := (G : ℝ) * axesLength a
    HasSequence c U (inscribed a) G (ellipsoid c U a) μ L b ((S + Real.sqrt (S*b)) / 32) := by
  have h := exists_budget_sequence c U (inscribed a) a
    (fun i => div_pos (sq_pos_of_pos (ha i)) (length_pos ha)) G hG
    (box_subset_ellipsoid c U ha) (ellipsoid_subset_box c U ha) μ L b hb
  simpa only [inscribed_sum ha] using h

end Curvature.Coordinate
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}


theorem adaptiveRate_pos (i : ℕ) : 0 < adaptiveRate i := by
  unfold adaptiveRate
  positivity

theorem adaptiveRate_le (i : ℕ) : adaptiveRate i ≤ 1 / 8 := by
  unfold adaptiveRate
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  have hpow : 1 ≤ (2 : ℝ)^i := one_le_pow₀ (by norm_num)
  linarith only [hpow]

theorem adaptiveRate_succ (i : ℕ) : adaptiveRate (i + 1) = adaptiveRate i / 2 := by
  simp only [adaptiveRate, pow_succ]
  ring

theorem adaptiveStart_lt_iff (i T : ℕ) : adaptiveStart i < T ↔ 2^i ≤ T := by
  unfold adaptiveStart
  have := Nat.one_le_two_pow (n := i)
  omega

theorem adaptiveNegative_nonneg (T : ℕ) (r : ℕ → ℝ) : 0 ≤ adaptiveNegative T r :=
  Finset.sum_nonneg fun t _ => le_max_left 0 (-r t)

theorem adaptiveNegative_le (M : ℝ) (hM : 0 ≤ M) (T : ℕ) (r : ℕ → ℝ)
    (hr : ∀ t < T, |r t| ≤ M) : adaptiveNegative T r ≤ M * T := by
  unfold adaptiveNegative
  calc
    _ ≤ ∑ _ ∈ Finset.range T, M := Finset.sum_le_sum fun t ht =>
      max_le hM ((neg_le_abs (r t)).trans (hr t (Finset.mem_range.mp ht)))
    _ = _ := by simp [mul_comm]

theorem adaptiveLoss_sum_identity (θ : ℝ) (T : ℕ) (r : ℕ → ℝ) :
    (∑ t ∈ Finset.range T, adaptiveLoss θ (r t)) =
      (1 - θ) * (∑ t ∈ Finset.range T, r t) - 2 * θ * adaptiveNegative T r := by
  unfold adaptiveNegative
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : 0 ≤ r t
  · rw [adaptiveLoss, abs_of_nonneg ht, max_eq_left (neg_nonpos.mpr ht)]
    ring
  · have hn := le_of_not_ge ht
    rw [adaptiveLoss, abs_of_nonpos hn, max_eq_right (neg_nonneg.mpr hn)]
    ring

theorem masterRatewise_of_signed {C : ℝ} (hC : 0 ≤ C) (T i : ℕ) (r : ℕ → ℝ)
    (hsigned : (∑ t ∈ Finset.range T, adaptiveLoss (2 * adaptiveRate i) (r t)) ≤
      2 * C / adaptiveRate i) :
    (∑ t ∈ Finset.range T, r t) ≤
      8 * C / (3 * adaptiveRate i) + (16/3) * adaptiveRate i * adaptiveNegative T r := by
  have hr := adaptiveRate_pos i
  have hrate := adaptiveRate_le i
  have hN := adaptiveNegative_nonneg T r
  rw [adaptiveLoss_sum_identity] at hsigned
  by_cases hp : 0 ≤ ∑ t ∈ Finset.range T, r t
  · have hcoef := mul_le_mul_of_nonneg_right
      (show (3/4 : ℝ) ≤ 1 - 2 * adaptiveRate i by linarith only [hrate]) hp
    have hdiv : 8 * C / (3 * adaptiveRate i) = (4/3) * (2 * C / adaptiveRate i) := by
      ring
    rw [hdiv]
    linarith only [hsigned, hcoef]
  · exact (le_of_not_ge hp).trans (by positivity)

private theorem exists_dyadic_neighbors {x : ℝ} (hx : 1 ≤ x) :
    ∃ i : ℕ, (2 : ℝ)^i ≤ x ∧ x < (2 : ℝ)^(i+1) := by
  have hexists : ∃ n : ℕ, x < (2 : ℝ)^n := by
    obtain ⟨n, hn⟩ := exists_nat_gt x
    exact ⟨n, hn.trans (by exact_mod_cast (Nat.lt_two_pow_self : n < 2^n))⟩
  have hfind := Nat.find_spec hexists
  cases he : Nat.find hexists with
  | zero => simp [he, not_lt_of_ge hx] at hfind
  | succ i =>
    refine ⟨i, le_of_not_gt (Nat.find_min hexists ?_), ?_⟩
    · rw [he]
      exact Nat.lt_succ_self i
    · simpa only [he] using hfind

/-- Select an awake learner and optimize the rate-dependent upper bound. -/
theorem adaptiveRegret_of_masterRatewise {C M n R : ℝ} {T : ℕ}
    (hC : 0 < C) (hMC : M ≤ C) (hT : 0 < T) (hn : 0 ≤ n)
    (hnT : n ≤ M * T)
    (hrate : ∀ i : ℕ, 2^i ≤ T →
      R ≤ 8*C / (3 * adaptiveRate i) + (16/3) * adaptiveRate i * n) :
    R ≤ 24 * (C + Real.sqrt (C * n)) := by
  by_cases ht : n < C
  · have hT1 : 1 ≤ T := by omega
    have h := hrate 0 (by simpa only [pow_zero] using hT1)
    norm_num [adaptiveRate] at h
    linarith only [h, ht, hC, Real.sqrt_nonneg (C*n)]
  · have hnC := le_of_not_gt ht
    let s := Real.sqrt (n / C)
    have hs1 : 1 ≤ s := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ((one_le_div hC).mpr hnC)
    have hs : 0 < s := zero_lt_one.trans_le hs1
    have hsSq : s^2 = n / C := Real.sq_sqrt (div_nonneg hn hC.le)
    have hCsn : C * s^2 = n := by
      rw [hsSq, mul_div_cancel₀ _ hC.ne']
    have hCsSqrt : C*s = Real.sqrt (C*n) := by
      symm
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
      calc
        C*n = C*(C*s^2) := by rw [hCsn]
        _ = (C*s)^2 := by ring
    obtain ⟨i, hlo, hhi⟩ := exists_dyadic_neighbors hs1
    have hTc : 1 ≤ (T : ℝ) := by exact_mod_cast hT
    have hsT : s ≤ (T : ℝ) := by
      apply (Real.sqrt_le_left (by positivity)).mpr
      apply (div_le_iff₀ hC).mpr
      have hCT := mul_le_mul_of_nonneg_right hMC (Nat.cast_nonneg T : 0 ≤ (T : ℝ))
      have hTT := mul_le_mul_of_nonneg_right hTc (Nat.cast_nonneg T : 0 ≤ (T : ℝ))
      have hbound := mul_le_mul_of_nonneg_right hTT hC.le
      nlinarith only [hnT, hCT, hbound]
    have hactive : 2^i ≤ T := by
      exact_mod_cast hlo.trans hsT
    have hfirst : 8 * C / (3 * adaptiveRate i) ≤ (64/3) * (C*s) := by
      rw [show 8*C / (3 * adaptiveRate i) = (64/3) * (C*(2:ℝ)^i) by
        unfold adaptiveRate
        field_simp
        ring]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlo hC.le) (by norm_num)
    have hsecond : (16/3) * adaptiveRate i * n ≤ (4/3) * (C*s) := by
      rw [← hCsn]
      unfold adaptiveRate
      field_simp
      rw [pow_succ] at hhi
      linarith only [hhi]
    have h := hrate i hactive
    rw [hCsSqrt] at hfirst hsecond
    linarith only [h, hfirst, hsecond, hC, Real.sqrt_nonneg (C*n)]

/-- Transfer linearized regret to convex loss using the observed subgradients. -/
theorem adaptiveConvexTransfer {K : Set (Vec d)} (hK : IsCompact K)
    (T : ℕ) (w g : ℕ → Vec d) (f : ℕ → Vec d → ℝ) (u : Vec d) (hu : u ∈ K)
    (hw : ∀ t < T, w t ∈ K) (hcont : ∀ t < T, ContinuousOn (f t) K)
    (hsub : ∀ t < T, ∀ v ∈ K, f t (w t) - f t v ≤ excess (g t) (w t) v) :
    (∑ t ∈ Finset.range T, (f t (w t) - f t u)) ≤
      (∑ t ∈ Finset.range T, excess (g t) (w t) u) ∧
    adaptiveNegative T (fun t => excess (g t) (w t) u) ≤
      ∑ t ∈ Finset.range T, (f t u - sInf (f t '' K)) := by
  constructor
  · exact Finset.sum_le_sum fun t ht => hsub t (Finset.mem_range.mp ht) u hu
  · apply Finset.sum_le_sum
    intro t ht
    have ht' := Finset.mem_range.mp ht
    have hbelow := (hK.image_of_continuousOn (hcont t ht')).bddBelow
    refine max_le (sub_nonneg.mpr (csInf_le hbelow ⟨u, hu, rfl⟩)) ?_
    have hminw := csInf_le hbelow ⟨w t, hw t ht', rfl⟩
    linarith only [hminw, hsub t ht' u hu]

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal InnerProductSpace
open MeasureTheory
namespace Curvature.Coordinate

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem expand (z : Axes r) :
    (∑ i, (z i) • (EuclideanSpace.single i (1:ℝ))) = z := by
  simpa using (EuclideanSpace.basisFun (Fin r) ℝ).sum_repr z

theorem box_bounded (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Fin r → ℝ) :
    Bornology.IsBounded (box c U a) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨‖c‖ + ∑ i, a i, ?_⟩
  rintro _ ⟨z,hz,rfl⟩
  apply (norm_add_le c (U z)).trans
  rw [U.norm_map]
  apply add_le_add le_rfl
  calc
    ‖z‖ = ‖∑ i, (z i) • EuclideanSpace.single i (1:ℝ)‖ := by rw [expand]
    _ ≤ _ := (norm_sum_le ..).trans (Finset.sum_le_sum fun i _ => by
      simpa [norm_smul] using hz i)

private theorem inner_position (c : E) (U : Axes r →ₗᵢ[ℝ] E) (z : Axes r) (v : E) :
    ⟪position c U z,v⟫_ℝ =
      ⟪c,v⟫_ℝ + ∑ i, z i * ⟪U (EuclideanSpace.single i 1),v⟫_ℝ := by
  rw [position, inner_add_left]
  congr 1
  conv_lhs => rw [← expand z]
  simp [map_sum, sum_inner, real_inner_smul_left]

theorem box_width_le [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i) :
    subexponentialWidth (box c U a) ≤ ∑ i, a i := by
  let K := box c U a
  have hne : K.Nonempty := ⟨_, vertex_mem c U ha (fun _ => true)⟩
  let : Nonempty K := hne.to_subtype
  let V := fun i : Fin r => U (EuclideanSpace.single i 1)
  have hV (i : Fin r) : ‖V i‖ ≤ 1 := by simp [V]
  have hs (v : E) : widthSupport K v ≤ ⟪c,v⟫_ℝ + ∑ i, a i * |⟪V i,v⟫_ℝ| := by
    apply ciSup_le
    rintro ⟨_,z,hz,rfl⟩
    rw [inner_position]
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro i _
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hz i) (abs_nonneg _))
  apply width_le_of_forall K hne
  intro μ hμ
  let := hμ.prob
  have hC := hμ.integrable.const_inner (𝕜 := ℝ) c
  have hI (i : Fin r) : Integrable (fun v : E => a i * |⟪V i,v⟫_ℝ|) μ :=
    (hμ.integrable.const_inner (𝕜 := ℝ) (V i)).abs.const_mul _
  have h := integral_mono (widthSupport_integrable K hne (box_bounded c U a) hμ)
    (hC.add (integrable_finsetSum Finset.univ fun i _ => hI i)) hs
  change (∫ v, widthSupport K v ∂μ) ≤ ∫ v : E, ⟪c,v⟫_ℝ + ∑ i, a i * |⟪V i,v⟫_ℝ| ∂μ at h
  rw [integral_add hC (integrable_finsetSum Finset.univ fun i _ => hI i),
    integral_finsetSum Finset.univ (fun i _ => hI i), integral_inner hμ.integrable, hμ.centered,
    inner_zero_right, zero_add] at h
  apply h.trans
  apply Finset.sum_le_sum
  intro i _
  rw [integral_const_mul]
  simpa using mul_le_mul_of_nonneg_left (hμ.firstMoment (V i) (hV i)) (ha i)

theorem ellipsoid_width_le [NeZero r] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Fin r → ℝ) (ha : ∀ i, 0 < a i) :
    subexponentialWidth (ellipsoid c U a) ≤ 2*axesLength a := by
  let K := ellipsoid c U a
  let L := axesLength a
  have hL : 0 < L := length_pos ha
  have hL2 : L^2 = ∑ i, (a i)^2 := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (a i)))
  have hne : K.Nonempty := ⟨_, box_subset_ellipsoid c U ha (vertex_mem c U
    (fun i => (div_pos (sq_pos_of_pos (ha i)) hL).le) (fun _ => true))⟩
  let : Nonempty K := hne.to_subtype
  let V := fun i : Fin r => U (EuclideanSpace.single i 1)
  have hV (i : Fin r) : ‖V i‖ ≤ 1 := by simp [V]
  let q := fun (i : Fin r) (v : E) => (a i)^2 * ⟪V i,v⟫_ℝ^2
  have hs (v : E) :
      widthSupport K v ≤ ⟪c,v⟫_ℝ + (L/2 + (1/(2*L)) * ∑ i, q i v) := by
    apply ciSup_le
    rintro ⟨_,z,hz,rfl⟩
    rw [inner_position]
    apply add_le_add le_rfl
    have hpoint (i : Fin r) :
        z i * ⟪V i,v⟫_ℝ ≤ (L/2)*(z i / a i)^2 + (1/(2*L))*q i v := by
      have hY (x y : ℝ) : x*y ≤ (L/2)*x^2 + (1/(2*L))*y^2 := by
        field_simp [hL]
        nlinarith only [sq_nonneg (L*x-y)]
      calc
        _ = (z i / a i) * (a i * ⟪V i,v⟫_ℝ) := by field_simp [(ha i).ne']
        _ ≤ _ := (hY _ _).trans_eq (by simp [q, mul_pow])
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
    apply h.trans (add_le_add _ le_rfl)
    simpa using mul_le_mul_of_nonneg_left hz (show 0 ≤ L/2 by positivity)
  apply width_le_of_forall K hne
  intro μ hμ
  let := hμ.prob
  have hC := hμ.integrable.const_inner (𝕜 := ℝ) c
  have hI (i : Fin r) : Integrable (q i) μ := (hμ.secondMoment (V i) (hV i)).1.const_mul _
  have hQ : Integrable (fun v => ∑ i, q i v) μ := integrable_finsetSum _ (fun i _ => hI i)
  have hM : Integrable (fun v => L/2 + (1/(2*L)) * ∑ i, q i v) μ := (integrable_const (μ := μ) (L/2)).add (hQ.const_mul (1/(2*L)))
  have h := integral_mono (widthSupport_integrable K hne
    ((box_bounded c U a).subset (ellipsoid_subset_box c U ha)) hμ) (hC.add hM) hs
  change (∫ v, widthSupport K v ∂μ) ≤ ∫ v : E, ⟪c,v⟫_ℝ + (L/2 + (1/(2*L)) * ∑ i, q i v) ∂μ at h
  rw [integral_add hC hM, integral_inner hμ.integrable, hμ.centered, inner_zero_right, zero_add,
    integral_add (integrable_const _) (hQ.const_mul _), integral_const, probReal_univ, one_smul,
    integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hI i)] at h
  have hsum : (∑ i, ∫ v, q i v ∂μ) ≤ 2*L^2 := by
    rw [hL2, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    dsimp [q]
    rw [integral_const_mul, mul_comm (2:ℝ)]
    exact mul_le_mul_of_nonneg_left (hμ.secondMoment (V i) (hV i)).2 (sq_nonneg _)
  apply h.trans
  calc
    _ ≤ L/2 + (1/(2*L))*(2*L^2) := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ ≤ 2*L := by field_simp; linarith

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

private theorem width_rate {S W b : ℝ} (hS : 0 ≤ S) (hW : W ≤ 2*S) (hb : 0 ≤ b) :
    (W + Real.sqrt (W*b)) / 64 ≤ (S + Real.sqrt (S*b)) / 32 := by
  have hs : Real.sqrt (W*b) ≤ 2 * Real.sqrt (S*b) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hS hb)]
    nlinarith only [mul_le_mul_of_nonneg_right hW hb, mul_nonneg hS hb]
  linarith

theorem box_width_lower [NeZero r] (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Fin r → ℝ)
    (ha : ∀ i, 0 < a i) (G : ℝ≥0) (hG : 0 < G) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L : (n : ℕ) → Learner E Ω (box c U a) r n) (b : ℝ) (hb : 0 ≤ b) :
    let W := (G : ℝ) * subexponentialWidth (box c U a)
    HasSequence c U a G (box c U a) μ L b ((W + Real.sqrt (W*b)) / 64) := by
  obtain ⟨n,hn,hbudget,σ,hreg⟩ := box_lower c U a ha G hG μ L b hb
  refine ⟨n,hn,hbudget,σ,(width_rate ?_ ?_ hb).trans hreg⟩
  · exact mul_nonneg G.coe_nonneg (Finset.sum_nonneg (fun i _ => (ha i).le))
  · have h := mul_le_mul_of_nonneg_left (box_width_le c U a (fun i => (ha i).le)) G.coe_nonneg
    linarith [mul_nonneg G.coe_nonneg (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (ha i).le))]

theorem ellipsoid_width_lower [NeZero r] (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Fin r → ℝ)
    (ha : ∀ i, 0 < a i) (G : ℝ≥0) (hG : 0 < G) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L : (n : ℕ) → Learner E Ω (ellipsoid c U a) r n) (b : ℝ) (hb : 0 ≤ b) :
    let W := (G : ℝ) * subexponentialWidth (ellipsoid c U a)
    HasSequence c U (inscribed a) G (ellipsoid c U a) μ L b ((W + Real.sqrt (W*b)) / 64) := by
  obtain ⟨n,hn,hbudget,σ,hreg⟩ := ellipsoid_lower c U a ha G hG μ L b hb
  refine ⟨n,hn,hbudget,σ,(width_rate (mul_nonneg G.coe_nonneg (length_pos ha).le) ?_ hb).trans hreg⟩
  nlinarith only [mul_le_mul_of_nonneg_left (ellipsoid_width_le c U a ha) G.coe_nonneg]

end Curvature.Coordinate
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}


theorem adaptiveScale_bounds {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < 1) (a : ℝ) :
    (1 - θ) / (1 + θ) ≤ adaptiveScale θ a ∧
      adaptiveScale θ a ≤ (1 + θ) / (1 - θ) := by
  have hp : 0 < 1 + θ := by positivity
  have hm : 0 < 1 - θ := sub_pos.mpr hθ'
  have hl : (1 - θ) / (1 + θ) ≤ 1 := (div_le_one hp).mpr (by linarith only [hθ])
  have hu : 1 ≤ (1 + θ) / (1 - θ) := (one_le_div hm).mpr (by linarith only [hθ])
  unfold adaptiveScale
  split <;> (try split) <;> constructor <;> first | rfl | exact hl | exact hu | exact hl.trans hu

theorem adaptiveScale_pos {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < 1) (a : ℝ) :
    0 < adaptiveScale θ a :=
  (div_pos (sub_pos.mpr hθ') (by positivity)).trans_le (adaptiveScale_bounds hθ hθ' a).1

theorem adaptiveScale_le_seventeen_fifteenths {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1/16)
    (a : ℝ) : adaptiveScale θ a ≤ 17/15 := by
  have hlt : θ < 1 := by linarith only [hθ']
  refine (adaptiveScale_bounds hθ hlt a).2.trans ((div_le_iff₀ (sub_pos.mpr hlt)).mpr ?_)
  linarith only [hθ']

theorem adaptiveScaledInput_norm {G : ℝ} (g : Vec d) (hg : norm₂ g ≤ G)
    (i : ℕ) (a : ℝ) : norm₂ (adaptiveScale (adaptiveRate i / 2) a • g) ≤ 2 * G := by
  have hθ : 0 ≤ adaptiveRate i / 2 := by have := adaptiveRate_pos i; positivity
  have hθ' : adaptiveRate i / 2 ≤ 1/16 := by linarith only [adaptiveRate_le i]
  have hp := adaptiveScale_pos hθ (by linarith only [hθ']) a
  have hmax := adaptiveScale_le_seventeen_fifteenths hθ hθ' a
  rw [norm₂_smul, abs_of_pos hp]
  exact mul_le_mul (hmax.trans (by norm_num)) hg (norm₂_nonneg _) (by norm_num)

private theorem adaptiveScale_cancel {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < 1) (a : ℝ) :
    adaptiveLoss θ a + adaptiveLoss θ (adaptiveScale θ a * (-a)) = 0 := by
  have hp : 0 < 1 + θ := by positivity
  have hm : 0 < 1 - θ := sub_pos.mpr hθ'
  rw [adaptiveLoss, adaptiveLoss, abs_mul, abs_neg,
    abs_of_pos (adaptiveScale_pos hθ hθ' a)]
  rcases lt_trichotomy 0 a with ha | rfl | ha
  · rw [abs_of_pos ha]
    simp only [adaptiveScale, if_pos ha]
    field_simp [hp.ne']
    ring
  · simp
  · rw [abs_of_neg ha]
    simp only [adaptiveScale, if_neg (not_lt_of_ge ha.le), if_pos ha]
    field_simp [hm.ne']
    ring

/-- The scalar comparison between a mixture prediction and a scaled base learner. -/
theorem adaptiveScalarBridge {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1/5) (r a : ℝ) :
    adaptiveLoss (4 * θ) r ≤ adaptiveLoss θ a +
      adaptiveLoss θ (adaptiveScale θ a * (r - a)) := by
  have hlt : θ < 1 := by linarith only [hθ']
  let s := adaptiveScale θ a
  have hs : 0 < s := adaptiveScale_pos hθ hlt a
  have hp : 0 < 1 + θ := by positivity
  have hm : 0 < 1 - θ := sub_pos.mpr hlt
  obtain ⟨hslo, hshi⟩ := adaptiveScale_bounds hθ hlt a
  have hlo : 1 - 4 * θ ≤ s * (1 - θ) := calc
    _ ≤ (1 - θ) / (1 + θ) * (1 - θ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hp]
      nlinarith only [hθ, sq_nonneg θ]
    _ ≤ _ := mul_le_mul_of_nonneg_right hslo hm.le
  have hhi : s * (1 + θ) ≤ 1 + 4 * θ := calc
    _ ≤ (1 + θ) / (1 - θ) * (1 + θ) := mul_le_mul_of_nonneg_right hshi hp.le
    _ ≤ _ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hm]
      nlinarith only [mul_nonneg hθ (show 0 ≤ 1 - 5*θ by linarith only [hθ'])]
  have habs : |r - a| - |-a| ≤ |r| := by
    simpa only [sub_neg_eq_add, sub_add_cancel] using abs_sub_abs_le_abs_sub (r-a) (-a)
  have hcancel := adaptiveScale_cancel hθ hlt a
  change adaptiveLoss θ a + adaptiveLoss θ (s * (-a)) = 0 at hcancel
  simp only [adaptiveLoss, abs_mul s, abs_of_pos hs] at hcancel
  change adaptiveLoss (4 * θ) r ≤ adaptiveLoss θ a + adaptiveLoss θ (s * (r-a))
  calc
    _ ≤ s*r - θ*s*|r| := by
      unfold adaptiveLoss
      rcases le_total 0 r with hr | hr
      · rw [abs_of_nonneg hr]
        nlinarith only [mul_le_mul_of_nonneg_right hlo hr]
      · rw [abs_of_nonpos hr]
        nlinarith only [mul_le_mul_of_nonpos_right hhi hr]
    _ ≤ s*r - θ*s*(|r-a| - |-a|) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left habs (mul_nonneg hθ hs.le)) _
    _ = _ := by
      simp only [adaptiveLoss, abs_mul s, abs_of_pos hs]
      linarith only [hcancel]

theorem adaptiveDormantBound (i : ℕ) (M : ℝ) (hM : 0 ≤ M) (r : ℕ → ℝ)
    (hr : ∀ t < adaptiveStart i, r t ≤ M) :
    (∑ t ∈ Finset.range (adaptiveStart i), adaptiveLoss (2 * adaptiveRate i) (r t)) ≤
      M / (8 * adaptiveRate i) := by
  have hs : (adaptiveStart i : ℝ) ≤ (2 : ℝ)^i := by
    exact_mod_cast (Nat.sub_le (2^i) 1)
  have hsum :
      (∑ t ∈ Finset.range (adaptiveStart i), adaptiveLoss (2 * adaptiveRate i) (r t)) ≤
      M * (adaptiveStart i : ℝ) := by
    calc
      _ ≤ ∑ _ ∈ Finset.range (adaptiveStart i), M := by
        apply Finset.sum_le_sum
        intro t ht
        have hn := mul_nonneg (show 0 ≤ 2 * adaptiveRate i by have := adaptiveRate_pos i; positivity)
          (abs_nonneg (r t))
        unfold adaptiveLoss
        linarith only [hr t (Finset.mem_range.mp ht), hn]
      _ = _ := by simp [mul_comm]
  refine hsum.trans ((mul_le_mul_of_nonneg_left hs hM).trans_eq ?_)
  unfold adaptiveRate
  field_simp

/-- Combine the mixture and scaled base learner bounds with the rounds before the learner starts. -/
theorem adaptiveMasterSigned_of_awake (T i : ℕ) (hawake : 2^i ≤ T)
    (M C₀ : ℝ) (hM : 0 ≤ M) (r a : ℕ → ℝ) (hr : ∀ t < T, r t ≤ M)
    (hmix : (∑ t ∈ Finset.Ico (adaptiveStart i) T, adaptiveLoss (adaptiveRate i / 2) (a t)) ≤
      256 * M * Real.log 2 / adaptiveRate i + (7/3) * M)
    (hbase : (∑ t ∈ Finset.Ico (adaptiveStart i) T,
      adaptiveLoss (adaptiveRate i / 2) (adaptiveScale (adaptiveRate i / 2) (a t) *
        (r t - a t))) ≤ 2 * C₀ / adaptiveRate i) :
    (∑ t ∈ Finset.range T, adaptiveLoss (2 * adaptiveRate i) (r t)) ≤
      2 * (C₀ + 256 * M) / adaptiveRate i := by
  have he : 0 < adaptiveRate i := adaptiveRate_pos i
  have he' := adaptiveRate_le i
  have hθ : 0 ≤ adaptiveRate i/2 := by positivity
  have hθ' : adaptiveRate i/2 ≤ 1/5 := by linarith only [he']
  have hstart := (adaptiveStart_lt_iff i T).mpr hawake
  have hdormant := adaptiveDormantBound i M hM r fun t ht => hr t (ht.trans hstart)
  have hbridge : (∑ t ∈ Finset.Ico (adaptiveStart i) T,
      adaptiveLoss (2 * adaptiveRate i) (r t)) ≤
      (∑ t ∈ Finset.Ico (adaptiveStart i) T, adaptiveLoss (adaptiveRate i/2) (a t)) +
      (∑ t ∈ Finset.Ico (adaptiveStart i) T,
        adaptiveLoss (adaptiveRate i/2) (adaptiveScale (adaptiveRate i/2) (a t) *
          (r t - a t))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t _
    rw [show 2 * adaptiveRate i = 4 * (adaptiveRate i/2) by ring]
    exact adaptiveScalarBridge hθ hθ' (r t) (a t)
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [h]
  have hscale : 0 ≤ M / adaptiveRate i := div_nonneg hM he.le
  have hmix' : 256*M*Real.log 2 / adaptiveRate i ≤ 256*(M / adaptiveRate i) := by
    rw [show 256*M*Real.log 2 / adaptiveRate i = (256*(M / adaptiveRate i))*Real.log 2 by ring]
    exact mul_le_of_le_one_right (by positivity) hlog
  have hconst : (7/3) * M ≤ (7/24) * (M / adaptiveRate i) := by
    have hm := mul_le_mul_of_nonneg_left he' hscale
    rw [div_mul_cancel₀ _ he.ne'] at hm
    linarith only [hm]
  rw [← Finset.sum_range_add_sum_Ico _ hstart.le]
  have hD : M / (8 * adaptiveRate i) = (1/8) * (M / adaptiveRate i) := by ring
  have hC : 2 * (C₀ + 256*M) / adaptiveRate i =
      2*C₀ / adaptiveRate i + 512*(M / adaptiveRate i) := by ring
  rw [hD] at hdormant
  rw [hC]
  linarith only [hdormant, hbridge, hmix, hbase, hmix', hconst, hscale]

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature


theorem adaptiveEta_pos {M : ℝ} (hM : 0 < M) (i : ℕ) : 0 < adaptiveEta M i :=
  div_pos (adaptiveRate_pos i) (by positivity)

theorem binaryLeftWeight_pos (η x y : ℝ) : 0 < binaryLeftWeight η x y := by
  unfold binaryLeftWeight
  positivity

theorem binaryLeftWeight_lt_one (η x y : ℝ) : binaryLeftWeight η x y < 1 := by
  unfold binaryLeftWeight
  exact (div_lt_one (by positivity)).mpr (lt_add_of_pos_right _ (Real.exp_pos _))

theorem binaryMean_mono {q x y x' y' : ℝ} (hq : q ∈ Set.Icc 0 1)
    (hx : x ≤ x') (hy : y ≤ y') : binaryMean q x y ≤ binaryMean q x' y' :=
  add_le_add (mul_le_mul_of_nonneg_left hx hq.1)
    (mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr hq.2))

@[simp] theorem binaryMean_same (q a : ℝ) : binaryMean q a a = a := by
  unfold binaryMean
  ring

private theorem binaryMean_exp_pos {η q x y : ℝ} (hq : q ∈ Set.Icc 0 1) :
    0 < binaryMean q (Real.exp (-η*x)) (Real.exp (-η*y)) := by
  unfold binaryMean
  by_cases hq0 : q = 0
  · simpa [hq0] using Real.exp_pos (-η*y)
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (lt_of_le_of_ne hq.1 (Ne.symm hq0)) (Real.exp_pos _))
      (mul_nonneg (sub_nonneg.mpr hq.2) (Real.exp_pos _).le)

theorem binaryMix_mono {η q x y x' y' : ℝ} (hη : 0 < η) (hq : q ∈ Set.Icc 0 1)
    (hx : x ≤ x') (hy : y ≤ y') : binaryMix η q x y ≤ binaryMix η q x' y' := by
  have hExp (a b : ℝ) (hab : a ≤ b) : Real.exp (-η*b) ≤ Real.exp (-η*a) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hab (neg_nonpos.mpr hη.le))
  have hmean := binaryMean_mono hq (hExp _ _ hx) (hExp _ _ hy)
  have hlog := Real.log_le_log (binaryMean_exp_pos hq) hmean
  exact div_le_div_of_nonneg_right (neg_le_neg hlog) hη.le

theorem binaryMix_translate {η q : ℝ} (hη : 0 < η) (hq : q ∈ Set.Icc 0 1)
    (x y c : ℝ) : binaryMix η q (x+c) (y+c) = binaryMix η q x y + c := by
  have hfact (a : ℝ) : Real.exp (-η*(a+c)) = Real.exp (-η*a) * Real.exp (-η*c) := by
    rw [mul_add, Real.exp_add]
  have hm : binaryMean q (Real.exp (-η*x) * Real.exp (-η*c))
      (Real.exp (-η*y) * Real.exp (-η*c)) =
    binaryMean q (Real.exp (-η*x)) (Real.exp (-η*y)) * Real.exp (-η*c) := by
    unfold binaryMean
    ring
  unfold binaryMix
  rw [hfact, hfact, hm, Real.log_mul (binaryMean_exp_pos hq).ne' (Real.exp_pos _).ne',
    Real.log_exp]
  field_simp
  ring

@[simp] theorem binaryMix_same {η : ℝ} (hη : 0 < η) (q x : ℝ) : binaryMix η q x x = x := by
  unfold binaryMix
  rw [binaryMean_same, Real.log_exp]
  field_simp

theorem binaryMix_left_le {η : ℝ} (hη : 0 < η) (x y : ℝ) :
    binaryMix η (1/2) x y ≤ x + Real.log 2 / η := by
  have hmean : Real.exp (-η*x) / 2 ≤ binaryMean (1/2) (Real.exp (-η*x))
      (Real.exp (-η*y)) := by
    unfold binaryMean
    linarith only [Real.exp_pos (-η*y)]
  have hlog := Real.log_le_log (by positivity : 0 < Real.exp (-η*x) / 2) hmean
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hlog
  unfold binaryMix
  apply (div_le_iff₀ hη).mpr
  have he : (x + Real.log 2 / η)*η = x*η + Real.log 2 := by
    rw [add_mul, div_mul_cancel₀ _ hη.ne']
  rw [he]
  linarith only [hlog]

theorem binaryMix_right_le {η : ℝ} (hη : 0 < η) (x y : ℝ) :
    binaryMix η (1/2) x y ≤ y + Real.log 2 / η := by
  have hsym : binaryMix η (1/2) x y = binaryMix η (1/2) y x := by
    unfold binaryMix
    have hmean (a b : ℝ) : binaryMean (1/2) a b = binaryMean (1/2) b a := by
      unfold binaryMean
      ring
    rw [hmean]
  rw [hsym]
  exact binaryMix_left_le hη y x

theorem binaryMix_increment (η x y v w : ℝ) :
    binaryMix η (1/2) (x+v) (y+w) - binaryMix η (1/2) x y =
      binaryMix η (binaryLeftWeight η x y) v w := by
  let X := Real.exp (-η*x)
  let Y := Real.exp (-η*y)
  let V := Real.exp (-η*v)
  let W := Real.exp (-η*w)
  have hsum : 0 < X+Y := by dsimp [X,Y]; positivity
  have hnew : 0 < (X*V+Y*W)/2 := by dsimp [X,Y,V,W]; positivity
  have hold : 0 < (X+Y)/2 := by positivity
  have hq : 1 - X/(X+Y) = Y/(X+Y) := by
    field_simp [hsum.ne']
    ring
  change -Real.log (binaryMean (1/2) (Real.exp (-η*(x+v)))
      (Real.exp (-η*(y+w))))/η -
      -Real.log (binaryMean (1/2) X Y)/η =
      -Real.log (binaryMean (X/(X+Y)) V W)/η
  rw [mul_add, mul_add, Real.exp_add, Real.exp_add]
  change -Real.log (binaryMean (1/2) (X*V) (Y*W))/η -
    -Real.log (binaryMean (1/2) X Y)/η = -Real.log (binaryMean (X/(X+Y)) V W)/η
  have hratio : binaryMean (X/(X+Y)) V W = ((X*V+Y*W)/2) / ((X+Y)/2) := by
    unfold binaryMean
    rw [hq]
    field_simp [hsum.ne']
  have havg (a b : ℝ) : binaryMean (1/2) a b = (a+b)/2 := by unfold binaryMean; ring
  rw [havg, havg, hratio, Real.log_div hnew.ne' hold.ne']
  ring


theorem adaptiveExactMean_mono (M : ℝ) (L v w : ℕ → ℝ) (k n : ℕ)
    (h : ∀ i, v i ≤ w i) : adaptiveExactMean M L v k n ≤ adaptiveExactMean M L w k n := by
  induction n generalizing k with
  | zero => exact h k
  | succ n ih =>
    simp only [adaptiveExactMean]
    exact binaryMean_mono ⟨(binaryLeftWeight_pos ..).le, (binaryLeftWeight_lt_one ..).le⟩
      (h k) (ih (k+1))

theorem adaptiveExactMean_const (M : ℝ) (L : ℕ → ℝ) (c : ℝ) (k n : ℕ) :
    adaptiveExactMean M L (fun _ => c) k n = c := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => rw [adaptiveExactMean, ih, binaryMean_same]

theorem adaptivePotential_mono {M : ℝ} (hM : 0 < M) (L L' : ℕ → ℝ) (k n : ℕ)
    (h : ∀ i, L i ≤ L' i) : adaptivePotential M L k n ≤ adaptivePotential M L' k n := by
  induction n generalizing k with
  | zero => exact h k
  | succ n ih =>
    simp only [adaptivePotential]
    exact binaryMix_mono (adaptiveEta_pos hM k) (by constructor <;> norm_num) (h k) (ih (k+1))

theorem adaptivePotential_translate {M : ℝ} (hM : 0 < M) (L : ℕ → ℝ) (c : ℝ) (k n : ℕ) :
    adaptivePotential M (fun i => L i + c) k n = adaptivePotential M L k n + c := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [adaptivePotential, adaptivePotential, ih]
    exact binaryMix_translate (adaptiveEta_pos hM k) (by constructor <;> norm_num) _ _ c

theorem adaptivePotential_shift_abs {M b : ℝ} (hM : 0 < M) (L v : ℕ → ℝ) (k n : ℕ)
    (hv : ∀ i, |v i| ≤ b) :
    |adaptivePotential M (fun i => L i + v i) k n - adaptivePotential M L k n| ≤ b := by
  have hlow := adaptivePotential_mono hM (fun i => L i - b) (fun i => L i + v i) k n
    (fun i => by linarith only [(abs_le.mp (hv i)).1])
  have hupp := adaptivePotential_mono hM (fun i => L i + v i) (fun i => L i + b) k n
    (fun i => by linarith only [(abs_le.mp (hv i)).2])
  simp only [sub_eq_add_neg, adaptivePotential_translate hM] at hlow hupp
  exact abs_le.mpr ⟨by linarith only [hlow], by linarith only [hupp]⟩

theorem adaptivePotential_path {M : ℝ} (hM : 0 < M) (L : ℕ → ℝ) (k n i : ℕ) (hi : i ≤ n) :
    adaptivePotential M L k n - L (k+i) ≤
      (Real.log 2) * (2 / adaptiveEta M (k+i) - 1 / adaptiveEta M k) := by
  induction n generalizing k i with
  | zero =>
    have hi' : i = 0 := by omega
    subst i
    simp only [adaptivePotential, add_zero, sub_self, ← sub_div, show (2:ℝ)-1=1 by norm_num]
    exact mul_nonneg (Real.log_nonneg (by norm_num)) (by have := adaptiveEta_pos hM k; positivity)
  | succ n ih =>
    have he := adaptiveEta_pos hM k
    cases i with
    | zero =>
      simp only [adaptivePotential, add_zero, ← sub_div, show (2:ℝ)-1=1 by norm_num]
      have h := binaryMix_left_le he (L k) (adaptivePotential M L (k+1) n)
      simp only [div_eq_mul_inv, one_mul] at h ⊢
      linarith only [h]
    | succ i =>
      have hS := binaryMix_right_le he (L k) (adaptivePotential M L (k+1) n)
      have hI := ih (k+1) i (by omega)
      have hshift : k + (i+1) = (k+1) + i := by omega
      have hsplit : 1 / adaptiveEta M (k+1) = 2 / adaptiveEta M k := by
        unfold adaptiveEta
        rw [adaptiveRate_succ]
        ring
      rw [hsplit, ← hshift] at hI
      simp only [adaptivePotential]
      simp only [div_eq_mul_inv, one_mul] at hS hI ⊢
      linarith only [hS, hI]


theorem adaptivePotential_congr (M : ℝ) (L L' : ℕ → ℝ) (k n : ℕ)
    (h : ∀ i, k ≤ i → i ≤ k+n → L i = L' i) :
    adaptivePotential M L k n = adaptivePotential M L' k n := by
  induction n generalizing k with
  | zero => exact h k (by omega) (by omega)
  | succ n ih =>
    have ht := ih (k+1) (fun i hlo hhi => h i (by omega) (by omega))
    simp only [adaptivePotential, ht, h k le_rfl (by omega)]

theorem adaptiveExactMean_congr (M : ℝ) (L L' v v' : ℕ → ℝ) (k n : ℕ)
    (hL : ∀ i, k ≤ i → i ≤ k+n → L i = L' i)
    (hv : ∀ i, k ≤ i → i ≤ k+n → v i = v' i) :
    adaptiveExactMean M L v k n = adaptiveExactMean M L' v' k n := by
  induction n generalizing k with
  | zero => exact hv k (by omega) (by omega)
  | succ n ih =>
    have hL' i (hlo : k+1 ≤ i) (hhi : i ≤ (k+1)+n) := hL i (by omega) (by omega)
    have hv' i (hlo : k+1 ≤ i) (hhi : i ≤ (k+1)+n) := hv i (by omega) (by omega)
    have ht := ih (k+1) hL' hv'
    simp only [adaptiveExactMean, ht, adaptivePotential_congr M L L' (k+1) n hL',
      hL k le_rfl (by omega), hv k le_rfl (by omega)]

theorem adaptivePotential_extend_zero {M : ℝ} (hM : 0 < M) (L : ℕ → ℝ) (k n : ℕ)
    (h : ∀ i ≥ k+n, L i = 0) (m : ℕ) :
    adaptivePotential M L k (n+m) = adaptivePotential M L k n := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← ih]
    clear ih
    have h' : ∀ i ≥ k+(n+m), L i = 0 := fun i hi => h i (by omega)
    clear h
    change adaptivePotential M L k ((n+m)+1) = adaptivePotential M L k (n+m)
    generalize hm : n+m = j at h' ⊢
    clear hm n m
    induction j generalizing k with
    | zero =>
      simp only [adaptivePotential]
      rw [h' k (by omega), h' (k+1) (by omega)]
      exact binaryMix_same (adaptiveEta_pos hM k) _ _
    | succ j ih =>
      have ht := ih (k+1) (fun i hi => h' i (by omega))
      change binaryMix (adaptiveEta M k) (1/2) (L k)
          (adaptivePotential M L (k+1) (j+1)) =
        binaryMix (adaptiveEta M k) (1/2) (L k) (adaptivePotential M L (k+1) j)
      rw [ht]


private theorem adaptiveExactMean_add (M : ℝ) (L v w : ℕ → ℝ) (k n : ℕ) :
    adaptiveExactMean M L (fun i => v i + w i) k n =
      adaptiveExactMean M L v k n + adaptiveExactMean M L w k n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [adaptiveExactMean, ih, binaryMean]
    ring

private theorem adaptiveExactMean_mul (M : ℝ) (L v : ℕ → ℝ) (k n : ℕ) (c : ℝ) :
    adaptiveExactMean M L (fun i => c * v i) k n =
      c * adaptiveExactMean M L v k n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [adaptiveExactMean, ih, binaryMean]
    ring

private theorem adaptiveExactMean_sum (M : ℝ) (L : ℕ → ℝ) (k n : ℕ)
    {α : Type*} (s : Finset α) (f : α → ℕ → ℝ) :
    adaptiveExactMean M L (fun i => ∑ a ∈ s, f a i) k n =
      ∑ a ∈ s, adaptiveExactMean M L (f a) k n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [adaptiveExactMean_const]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha, adaptiveExactMean_add, ih]


theorem adaptiveProbability_nonneg (M : ℝ) (L : ℕ → ℝ) (k n j : ℕ) :
    0 ≤ adaptiveProbability M L k n j := by
  have h := adaptiveExactMean_mono M L (fun _ => 0) (fun i => if i=j then 1 else 0) k n
    (fun i => by split <;> norm_num)
  simpa only [adaptiveExactMean_const, adaptiveProbability] using h

theorem adaptiveProbability_left_pos (M : ℝ) (L : ℕ → ℝ) (k n : ℕ) :
    0 < adaptiveProbability M L k n k := by
  cases n with
  | zero => simp [adaptiveProbability,adaptiveExactMean]
  | succ n =>
    unfold adaptiveProbability
    rw [adaptiveExactMean, if_pos rfl]
    let p := binaryLeftWeight (adaptiveEta M k) (L k) (adaptivePotential M L (k+1) n)
    have hp : 0 < p := binaryLeftWeight_pos _ _ _
    have hp' : 0 ≤ 1-p := sub_nonneg.mpr (binaryLeftWeight_lt_one ..).le
    change 0 < binaryMean p 1 (adaptiveProbability M L (k+1) n k)
    unfold binaryMean
    exact add_pos_of_pos_of_nonneg (by positivity)
      (mul_nonneg hp' (adaptiveProbability_nonneg ..))

theorem adaptiveExactMean_weighted_sum (M : ℝ) (L v : ℕ → ℝ) (k n : ℕ) :
    adaptiveExactMean M L v k n =
      ∑ j ∈ Finset.Icc k (k+n), adaptiveProbability M L k n j * v j := by
  have hv (i : ℕ) (hlo : k ≤ i) (hhi : i ≤ k+n) :
      v i = ∑ j ∈ Finset.Icc k (k+n), v j * (if i=j then (1:ℝ) else 0) := by
    classical
    simp only [mul_ite, mul_zero, mul_one]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji.symm]
    · intro h
      exact (h (Finset.mem_Icc.mpr ⟨hlo,hhi⟩)).elim
  rw [adaptiveExactMean_congr M L L v _ k n (by simp) hv, adaptiveExactMean_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [adaptiveExactMean_mul]
  exact mul_comm _ _

theorem adaptiveProbability_sum (M : ℝ) (L : ℕ → ℝ) (k n : ℕ) :
    (∑ j ∈ Finset.Icc k (k+n), adaptiveProbability M L k n j) = 1 := by
  simpa only [adaptiveExactMean_const, mul_one] using
    (adaptiveExactMean_weighted_sum M L (fun _ => 1) k n).symm

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory

namespace Curvature


namespace FullInfoLearner

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] {K : Set E} {T : ℕ}


private theorem rank_mono {r n : ℕ} {s t : Coordinate.Round r n}
    (h : Coordinate.Earlier s t) : finProdFinEquiv s < finProdFinEquiv t := by
  change s.2.val + n * s.1.val < t.2.val + n * t.1.val
  rcases h with h | ⟨he,h⟩
  · have hc := Nat.mul_le_mul_left n (show s.1.val + 1 ≤ t.1.val from h)
    rw [Nat.mul_add, Nat.mul_one] at hc
    have := s.2.isLt
    omega
  · rw [he]
    exact Nat.add_lt_add_right h _

private theorem earlier_of_rank {r n : ℕ} {s t : Coordinate.Round r n}
    (h : finProdFinEquiv s < finProdFinEquiv t) : Coordinate.Earlier s t := by
  rcases lt_trichotomy s.1 t.1 with hl | he | hg
  · exact Or.inl hl
  · refine Or.inr ⟨he, ?_⟩
    change s.2.val + n * s.1.val < t.2.val + n * t.1.val at h
    rw [he] at h
    exact Nat.lt_of_add_lt_add_right h
  · exact False.elim (lt_asymm h (rank_mono (Or.inl hg)))

def asBlocks (L : FullInfoLearner E Ω K) (r n : ℕ) : Coordinate.Learner E Ω K r n where
  predict t h := L.predict (finProdFinEquiv t).val fun k =>
    h ⟨finProdFinEquiv.symm ⟨k.val, lt_trans k.isLt (finProdFinEquiv t).isLt⟩,
      earlier_of_rank (by rw [Equiv.apply_symm_apply]; exact k.isLt)⟩
  mem _ _ _ := L.mem _ _ _
  measurable _ _ := L.measurable _ _

theorem of_coordinate {r : ℕ} [NeZero r] (L : FullInfoLearner E Ω K) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : ℝ≥0) (c : E) (U : Coordinate.Axes r →ₗᵢ[ℝ] E)
    (a A : Fin r → ℝ) (hout : K ⊆ Coordinate.box c U A) {b R : ℝ}
    (h : Coordinate.HasSequence c U a G K μ (L.asBlocks r) b R) : L.HasHardSequence μ G b R := by
  classical
  obtain ⟨n, hn, hb, σ, hR⟩ := h
  let e : Coordinate.Round r n ≃ Fin (r*n) := finProdFinEquiv
  let f : Fin (r*n) → E → ℝ := fun t => Coordinate.loss c U a G (e.symm t).1 (σ (e.symm t))
  have best : bestLoss K f = Coordinate.best c U a G K σ := by
    unfold bestLoss Coordinate.best Coordinate.total
    congr 1
    apply Set.image_congr
    intro x _
    exact (e.symm.sum_comp (fun t => Coordinate.loss c U a G t.1 (σ t) x))
  have budget : comparatorBudget K f = Coordinate.budget c U a G K σ := by
    unfold comparatorBudget Coordinate.budget
    rw [best, e.symm.sum_comp (fun t => sInf (Coordinate.loss c U a G t.1 (σ t) '' K))]
  have regr : L.regret f = Coordinate.regret c U a G (L.asBlocks r n) σ := by
    funext ω
    unfold regret Coordinate.regret
    rw [best]
    congr 1
    rw [← e.sum_comp (fun t => f t (L.predict t.val (pastLosses f t) ω))]
    apply Finset.sum_congr rfl
    intro t _
    simp only [f, Equiv.symm_apply_apply, Coordinate.played, asBlocks,
      Coordinate.past, e]
    rfl
  refine ⟨r*n, Nat.mul_pos (NeZero.pos r) hn, f, ?_, budget ▸ hb σ, ?_, regr ▸ hR⟩
  · exact fun t => ⟨Coordinate.loss_convex c U a G _ _, Coordinate.loss_lipschitz c U a G _ _⟩
  · rw [regr]
    exact (integrable_finsetSum _ fun t _ =>
      Coordinate.played_integrable c U a G μ (L.asBlocks r n) A hout σ t).sub (integrable_const _)

end FullInfoLearner

open Coordinate

/-- The coordinate cases of the lower bound, in chronological time, against arbitrary full feedback. -/
theorem coordinateBudgetLower {r : ℕ} [NeZero r] {E Ω : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
    (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Fin r → ℝ) (ha : ∀ i, 0 < a i)
    {K : Set E} (hK : K = box c U a ∨ K = ellipsoid c U a)
    (L : FullInfoLearner E Ω K) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : ℝ≥0) (hG : 0 < G) (b : ℝ) (hb : 0 ≤ b) :
    let W := (G : ℝ) * subexponentialWidth K
    L.HasHardSequence μ G b ((W + Real.sqrt (W*b))/64) := by
  rcases hK with rfl | rfl
  · exact L.of_coordinate μ G c U a a (Set.Subset.refl _)
      (box_width_lower c U a ha G hG μ _ b hb)
  · exact L.of_coordinate μ G c U (inscribed a) a (ellipsoid_subset_box c U ha)
      (ellipsoid_width_lower c U a ha G hG μ _ b hb)

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

/-- The two-loss exponential mix error is bounded by the weighted variance. -/
theorem binaryMix_gap {η q x y B : ℝ} (hη : 0 < η) (hq : q ∈ Set.Icc 0 1)
    (hx : |x| ≤ B) (hy : |y| ≤ B) (hsmall : 2*η*B ≤ 1) :
    binaryMean q x y - binaryMix η q x y ∈ Set.Icc 0 (η*q*(1-q)*(x-y)^2) := by
  let μ := binaryMean q x y
  let a := -η*(x-μ)
  let b := -η*(y-μ)
  let Z := binaryMean q (Real.exp a) (Real.exp b)
  have hq' : 0 ≤ 1-q := sub_nonneg.mpr hq.2
  have hx' : x-μ = (1-q)*(x-y) := by dsimp [μ, binaryMean]; ring
  have hy' : y-μ = -q*(x-y) := by dsimp [μ, binaryMean]; ring
  have hxy : |x-y| ≤ 2*B := by
    have h := abs_sub x y
    linarith only [h, hx, hy]
  have ha : |a| ≤ 1 := by
    rw [show a = -η * ((1-q)*(x-y)) by dsimp only [a]; rw [hx'], abs_mul, abs_mul, abs_neg,
      abs_of_pos hη, abs_of_nonneg hq']
    have h := mul_le_mul_of_nonneg_right (show 1-q ≤ 1 by linarith only [hq.1]) (abs_nonneg (x-y))
    have hh := mul_le_mul_of_nonneg_left ((by simpa only [one_mul] using h :
      (1-q)*|x-y| ≤ |x-y|).trans hxy) hη.le
    linarith only [hh, hsmall]
  have hb : |b| ≤ 1 := by
    rw [show b = -η * (-q*(x-y)) by dsimp only [b]; rw [hy'], abs_mul, abs_mul, abs_neg, abs_neg,
      abs_of_pos hη, abs_of_nonneg hq.1]
    have h := mul_le_mul_of_nonneg_right hq.2 (abs_nonneg (x-y))
    have hh := mul_le_mul_of_nonneg_left ((by simpa only [one_mul] using h :
      q*|x-y| ≤ |x-y|).trans hxy) hη.le
    linarith only [hh, hsmall]
  have hlin : q*a+(1-q)*b = 0 := by dsimp [a,b,μ,binaryMean]; ring
  have hsq : q*a^2+(1-q)*b^2 = η^2*q*(1-q)*(x-y)^2 := by
    dsimp only [a,b]
    rw [hx', hy']
    ring
  have hlo : 1 ≤ Z := by
    have h := binaryMean_mono hq (Real.add_one_le_exp a) (Real.add_one_le_exp b)
    change binaryMean q (a+1) (b+1) ≤ Z at h
    unfold binaryMean at h
    linarith only [h, hlin]
  have hup : Z ≤ 1 + η^2*q*(1-q)*(x-y)^2 := by
    have h₁ : Real.exp a ≤ a+1+a^2 := by
      linarith only [(le_abs_self (Real.exp a-1-a)).trans (Real.abs_exp_sub_one_sub_id_le ha)]
    have h₂ : Real.exp b ≤ b+1+b^2 := by
      linarith only [(le_abs_self (Real.exp b-1-b)).trans (Real.abs_exp_sub_one_sub_id_le hb)]
    have h := binaryMean_mono hq h₁ h₂
    change Z ≤ binaryMean q _ _ at h
    unfold binaryMean at h
    linarith only [h, hsq, hlin]
  have hcenter : μ - binaryMix η q x y = Real.log Z / η := by
    have ht := binaryMix_translate hη hq x y (-μ)
    simp only [← sub_eq_add_neg] at ht
    change -Real.log Z / η = binaryMix η q x y - μ at ht
    rw [neg_div] at ht
    linarith only [ht]
  change μ - binaryMix η q x y ∈ _
  rw [hcenter]
  constructor
  · exact div_nonneg (Real.log_nonneg hlo) hη.le
  · apply (div_le_iff₀ hη).mpr
    have hlog := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hlo)
    linarith only [hlog, hup]

def adaptiveIncrement (M : ℝ) (L v : ℕ → ℝ) (k n : ℕ) : ℝ :=
  adaptivePotential M (fun j => L j + v j) k n - adaptivePotential M L k n

def adaptiveMixError (M : ℝ) (L v : ℕ → ℝ) (k n : ℕ) : ℝ :=
  adaptiveExactMean M L v k n - adaptiveIncrement M L v k n

def adaptiveWeightedVariance (M : ℝ) (L v : ℕ → ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => 0
  | n+1 =>
    let p := binaryLeftWeight (adaptiveEta M k) (L k) (adaptivePotential M L (k+1) n)
    let m := adaptiveExactMean M L v (k+1) n
    adaptiveRate k * (p*(1-p)*(v k-m)^2) + (1-p)*adaptiveWeightedVariance M L v (k+1) n

private theorem adaptiveExactMean_abs (M : ℝ) (L v : ℕ → ℝ) (k n : ℕ) (B : ℝ)
    (hv : ∀ i, |v i| ≤ B) : |adaptiveExactMean M L v k n| ≤ B := by
  have hl := adaptiveExactMean_mono M L (fun _ => -B) v k n (fun i => (abs_le.mp (hv i)).1)
  have hh := adaptiveExactMean_mono M L v (fun _ => B) k n (fun i => (abs_le.mp (hv i)).2)
  rw [adaptiveExactMean_const] at hl hh
  exact abs_le.mpr ⟨hl, hh⟩

private theorem adaptiveIncrement_succ (M : ℝ) (L v : ℕ → ℝ) (k n : ℕ) :
    let p := binaryLeftWeight (adaptiveEta M k) (L k) (adaptivePotential M L (k+1) n)
    adaptiveIncrement M L v k (n+1) =
      binaryMix (adaptiveEta M k) p (v k) (adaptiveIncrement M L v (k+1) n) := by
  dsimp only [adaptiveIncrement, adaptivePotential]
  rw [← binaryMix_increment]
  simp

theorem adaptiveWeightedVariance_le {M : ℝ} (hM : 0 < M) (L v : ℕ → ℝ)
    (hv : ∀ i, |v i| ≤ 2*M) (k n : ℕ) :
    let m := adaptiveExactMean M L v k n
    let J := adaptiveExactMean M L (fun j => adaptiveRate j * |v j|) k n
    adaptiveWeightedVariance M L v k n ≤
      4*M*J + 2*M*adaptiveRate k*|m| - adaptiveRate k*m^2 := by
  have hsq (y : ℝ) (hy : |y| ≤ 2*M) : y^2 ≤ 2*M*|y| := by
    simpa only [← sq, sq_abs] using mul_le_mul_of_nonneg_right hy (abs_nonneg y)
  induction n generalizing k with
  | zero =>
    change 0 ≤ 4*M*(adaptiveRate k*|v k|) + 2*M*adaptiveRate k*|v k| - adaptiveRate k*(v k)^2
    have he := adaptiveRate_pos k
    have h := mul_le_mul_of_nonneg_left (hsq _ (hv k)) he.le
    have hp : 0 ≤ 4*M*(adaptiveRate k*|v k|) := by positivity
    linarith only [h,hp]
  | succ n ih =>
    let p := binaryLeftWeight (adaptiveEta M k) (L k) (adaptivePotential M L (k+1) n)
    let x := v k
    let m := adaptiveExactMean M L v (k+1) n
    let μ := binaryMean p x m
    let J := adaptiveExactMean M L (fun j => adaptiveRate j * |v j|) (k+1) n
    let S := adaptiveWeightedVariance M L v (k+1) n
    let ε := adaptiveRate k
    have hp : 0 ≤ p := (binaryLeftWeight_pos ..).le
    have hp' : 0 ≤ 1-p := sub_nonneg.mpr (binaryLeftWeight_lt_one ..).le
    have he : 0 ≤ ε := (adaptiveRate_pos k).le
    have hm := adaptiveExactMean_abs M L v (k+1) n (2*M) hv
    have hm' : (1-p)*|m| ≤ |μ|+p*|x| := by
      have heq : (1-p)*m = μ - p*x := by dsimp [μ,binaryMean]; ring
      have h := abs_sub μ (p*x)
      rwa [← heq, abs_mul (1-p), abs_mul p, abs_of_nonneg hp', abs_of_nonneg hp] at h
    have hchild : S ≤ 4*M*J + 2*M*(ε/2)*|m| - (ε/2)*m^2 := by
      simpa only [adaptiveRate_succ k] using ih (k+1)
    have hvar : p*(1-p)*(x-m)^2 = p*x^2 + (1-p)*m^2 - μ^2 := by
      dsimp [μ, binaryMean]
      ring
    change ε * (p*(1-p)*(x-m)^2) + (1-p)*S ≤
      4*M*(p*(ε*|x|)+(1-p)*J) + 2*M*ε*|μ| - ε*μ^2
    rw [hvar]
    have hx := mul_le_mul_of_nonneg_left (hsq x (hv k)) (mul_nonneg he hp)
    have hmSq := mul_le_mul_of_nonneg_left (hsq m hm) (mul_nonneg (show 0 ≤ ε/2 by positivity) hp')
    have htail := mul_le_mul_of_nonneg_left hm' (mul_nonneg (by positivity : 0 ≤ 2*M) he)
    have hI := mul_le_mul_of_nonneg_left hchild hp'
    linarith only [hx,hmSq,htail,hI]

theorem adaptiveMixError_bounds {M : ℝ} (hM : 0 < M) (L v : ℕ → ℝ)
    (hv : ∀ i, |v i| ≤ 2*M) (k n : ℕ) :
    let E := adaptiveMixError M L v k n
    0 ≤ E ∧ E ≤ 2 * adaptiveWeightedVariance M L v k n / (128*M) + 16*M*adaptiveEta M k*E := by
  induction n generalizing k with
  | zero =>
    simp only [adaptiveMixError, adaptiveExactMean, adaptiveIncrement, adaptivePotential,
      adaptiveWeightedVariance, add_sub_cancel_left, sub_self, mul_zero, zero_div, add_zero,
      le_refl, and_self]
  | succ n ih =>
    let p := binaryLeftWeight (adaptiveEta M k) (L k) (adaptivePotential M L (k+1) n)
    let x := v k
    let m := adaptiveExactMean M L v (k+1) n
    let u := adaptiveIncrement M L v (k+1) n
    let E₁ := adaptiveMixError M L v (k+1) n
    let μ := binaryMean p x m
    let E := adaptiveMixError M L v k (n+1)
    let b := binaryMean p x u - binaryMix (adaptiveEta M k) p x u
    let D := p*(1-p)*(x-m)^2
    let S := adaptiveWeightedVariance M L v (k+1) n
    let η := adaptiveEta M k
    have hp : 0 ≤ p := (binaryLeftWeight_pos ..).le
    have hp1 : p ≤ 1 := (binaryLeftWeight_lt_one ..).le
    have hp' : 0 ≤ 1-p := sub_nonneg.mpr hp1
    have hη : 0 < η := adaptiveEta_pos hM k
    have hsmall : 2*η*(2*M) ≤ 1 := by
      have heq : 2*η*(2*M) = adaptiveRate k / 32 := by
        dsimp [η,adaptiveEta]
        field_simp
        ring
      rw [heq]
      linarith only [adaptiveRate_le k]
    have hu := adaptivePotential_shift_abs hM L v (k+1) n hv
    have hm := adaptiveExactMean_abs M L v (k+1) n (2*M) hv
    change |u| ≤ 2*M at hu
    change |m| ≤ 2*M at hm
    have hb : b ∈ Set.Icc 0 (η*p*(1-p)*(x-u)^2) :=
      binaryMix_gap hη ⟨hp,hp1⟩ (hv k) hu hsmall
    obtain ⟨hE₁, hI⟩ := ih (k+1)
    change 0 ≤ E₁ at hE₁
    have hEta : adaptiveEta M (k+1) = η/2 := by simp [η, adaptiveEta, adaptiveRate_succ]; ring
    rw [hEta] at hI
    have hEsq : E₁^2 ≤ 4*M*E₁ := by
      have hE : E₁ ≤ 4*M := by
        change m-u ≤ 4*M
        linarith only [(abs_le.mp hm).2, (abs_le.mp hu).1]
      simpa only [← sq] using mul_le_mul_of_nonneg_right hE hE₁
    have hrec : E = (1-p)*E₁ + b := by
      dsimp only [E, adaptiveMixError]
      rw [adaptiveIncrement_succ]
      change binaryMean p x m - _ = (1-p)*(m-u) + b
      dsimp [b,binaryMean]
      ring
    have hEsub : (1-p)*E₁ ≤ E := by rw [hrec]; exact le_add_of_nonneg_right hb.1
    have hE : 0 ≤ E := (mul_nonneg hp' hE₁).trans hEsub
    have hdiff : (x-u)^2 ≤ 2*(x-m)^2+2*E₁^2 := by
      change (x-u)^2 ≤ 2*(x-m)^2+2*(m-u)^2
      nlinarith only [sq_nonneg ((x-m)-(m-u))]
    have hpη : 0 ≤ η*p*(1-p) := mul_nonneg (mul_nonneg hη.le hp) hp'
    have hbstep : b ≤ 2*η*D + 8*M*η*p*(1-p)*E₁ := by
      have hdiff' := mul_le_mul_of_nonneg_left hdiff hpη
      have hs' := mul_le_mul_of_nonneg_left hEsq (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hpη)
      dsimp only [D]
      linarith only [hb.2,hdiff',hs']
    have hD : 2*η*D = 2*(adaptiveRate k*D)/(128*M) := by dsimp [η,adaptiveEta]; ring
    have hchild := mul_le_mul_of_nonneg_left hI hp'
    have hptop := mul_le_mul_of_nonneg_right hp1
      (show 0 ≤ 8*M*η*((1-p)*E₁) by positivity)
    have hroot := mul_le_mul_of_nonneg_left hEsub (show 0 ≤ 16*M*η by positivity)
    change 0 ≤ E ∧ E ≤ 2 * (adaptiveRate k*D+(1-p)*S)/(128*M) + 16*M*η*E
    refine ⟨hE, ?_⟩
    dsimp only [adaptiveMixError] at hchild
    change (1-p)*E₁ ≤ (1-p)*(2*S/(128*M)+16*M*(η/2)*E₁) at hchild
    rw [hD] at hbstep
    simp only [div_eq_mul_inv] at hbstep hchild ⊢
    linarith only [hrec,hbstep,hchild,hptop,hroot]


theorem abs_adaptiveUpdate_le (i : ℕ) (r : ℝ) : |adaptiveUpdate i r| ≤ 2*|r| := by
  have he := adaptiveRate_pos i
  have h := abs_sub r (adaptiveRate i/2*|r|)
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ adaptiveRate i/2), abs_abs] at h
  have hp := mul_le_mul_of_nonneg_right (show adaptiveRate i/2 ≤ 1 by
    linarith only [adaptiveRate_le i]) (abs_nonneg r)
  unfold adaptiveUpdate adaptiveLoss
  rw [abs_neg]
  linarith only [h,hp]

private theorem weightedMean_difference {s : Finset ℕ} {p q x : ℕ → ℝ} {δ B : ℝ}
    (hδ : (∑ i ∈ s, |p i-q i|) ≤ δ) (hB : 0 ≤ B) (hx : ∀ i ∈ s, |x i| ≤ B) :
    |(∑ i ∈ s, p i*x i) - ∑ i ∈ s, q i*x i| ≤ B*δ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, |p i*x i-q i*x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, B*|p i-q i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← sub_mul, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hx i hi) (abs_nonneg _)
    _ ≤ B*δ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hδ hB

private theorem adaptiveMixError_variance_bound {M : ℝ} (hM : 0 < M) (L v : ℕ → ℝ)
    (hv : ∀ i, |v i| ≤ 2*M) (k n : ℕ) :
    let E := adaptiveMixError M L v k n
    let J := adaptiveExactMean M L (fun j => adaptiveRate j*|v j|) k n
    let m := adaptiveExactMean M L v k n
    E ≤ J/16 + adaptiveRate k*|m|/32 + E/64 := by
  let E := adaptiveMixError M L v k n
  let J := adaptiveExactMean M L (fun j => adaptiveRate j*|v j|) k n
  let m := adaptiveExactMean M L v k n
  obtain ⟨hE, he⟩ := adaptiveMixError_bounds hM L v hv k n
  have hV := adaptiveWeightedVariance_le hM L v hv k n
  have hweak : adaptiveWeightedVariance M L v k n ≤ 4*M*J + 2*M*adaptiveRate k*|m| :=
    hV.trans (sub_le_self _ (mul_nonneg (adaptiveRate_pos k).le (sq_nonneg _)))
  have hscale := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hweak (by norm_num : (0:ℝ) ≤ 2)) (by positivity : 0 ≤ 128*M)
  have hcoeff : 16*M*adaptiveEta M k = adaptiveRate k/8 := by
    unfold adaptiveEta
    field_simp
    ring
  rw [hcoeff] at he
  change 0 ≤ E at hE
  have hlast := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (adaptiveRate_le k) (by norm_num : (0:ℝ) ≤ 8)) hE
  norm_num at hlast
  have hclean : 2*(4*M*J+2*M*adaptiveRate k*|m|)/(128*M) =
      J/16+adaptiveRate k*|m|/32 := by
    field_simp
    ring
  rw [hclean] at hscale
  change E ≤ _ at he
  change E ≤ J/16+adaptiveRate k*|m|/32+E/64
  linarith only [hlast, hscale, he]

/-- One round of the recursive mixture with a bounded approximation of the weights. -/
theorem adaptiveOneRoundGap {M δ : ℝ} (hM : 0 < M) (hδ : 0 ≤ δ) (L a approx : ℕ → ℝ)
    (k n : ℕ) (ha : ∀ i, |a i| ≤ M)
    (hp : ∀ i ∈ Finset.Icc k (k+n), 0 ≤ approx i)
    (hdist : (∑ i ∈ Finset.Icc k (k+n), |adaptiveProbability M L k n i - approx i|) ≤ δ)
    (hzero : (∑ i ∈ Finset.Icc k (k+n), approx i * a i) = 0) :
    let v := fun i => adaptiveUpdate i (a i)
    let U := ∑ i ∈ Finset.Icc k (k+n), approx i * (adaptiveRate i/2) * |a i|
    adaptiveMixError M L v k n ≤ (U+M*δ)/3 ∧
      (2/3)*U-(7/3)*M*δ ≤ adaptiveIncrement M L v k n := by
  let s := Finset.Icc k (k+n)
  let v := fun i => adaptiveUpdate i (a i)
  let U := ∑ i ∈ s, approx i * (adaptiveRate i/2) * |a i|
  let m := adaptiveExactMean M L v k n
  let J := adaptiveExactMean M L (fun j => adaptiveRate j*|v j|) k n
  let E := adaptiveMixError M L v k n
  have hv (i : ℕ) : |v i| ≤ 2*M := (abs_adaptiveUpdate_le i (a i)).trans
    (mul_le_mul_of_nonneg_left (ha i) (by norm_num))
  have hU : 0 ≤ U := Finset.sum_nonneg fun i hi =>
    mul_nonneg (mul_nonneg (hp i hi) (by have := adaptiveRate_pos i; positivity)) (abs_nonneg _)
  have hMδ := mul_nonneg hM.le hδ
  have hmean := weightedMean_difference hdist (by positivity : 0 ≤ 2*M) (fun i _ => hv i)
  have hm' : (∑ i ∈ s, approx i*v i) = U := by
    change (∑ i ∈ s, approx i*a i) = 0 at hzero
    simp only [U, v, adaptiveUpdate, adaptiveLoss]
    simp only [neg_sub, mul_sub, Finset.sum_sub_distrib, hzero, sub_zero, mul_assoc]
  rw [hm', ← adaptiveExactMean_weighted_sum] at hmean
  change |m-U| ≤ 2*M*δ at hmean
  have hm : |m| ≤ U+2*M*δ := by
    have h := abs_add_le (m-U) U
    rw [sub_add_cancel, abs_of_nonneg hU] at h
    linarith only [h,hmean]
  have hjexp : (∑ i ∈ s, approx i * (adaptiveRate i*|v i|)) ≤ 4*U := by
    dsimp only [U]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left (abs_adaptiveUpdate_le i (a i))
      (mul_nonneg (hp i hi) (adaptiveRate_pos i).le)
    change (approx i*adaptiveRate i)*|v i| ≤ _ at h
    linarith only [h]
  have hjpt (i : ℕ) : |adaptiveRate i * (|v i|)| ≤ 2*M := by
    rw [abs_of_nonneg (mul_nonneg (adaptiveRate_pos i).le (abs_nonneg _))]
    exact (mul_le_of_le_one_left (abs_nonneg _) ((adaptiveRate_le i).trans (by norm_num))).trans (hv i)
  have hjabs := weightedMean_difference hdist (by positivity : 0 ≤ 2*M) (fun i _ => hjpt i)
  rw [← adaptiveExactMean_weighted_sum] at hjabs
  change |J - ∑ i ∈ s, approx i * (adaptiveRate i*|v i|)| ≤ 2*M*δ at hjabs
  have hj : J ≤ 4*U+2*M*δ := by
    linarith only [hjexp,(abs_le.mp hjabs).2]
  have heabs := adaptiveMixError_variance_bound hM L v hv k n
  have hcoef := mul_le_mul_of_nonneg_right (adaptiveRate_le k) (abs_nonneg m)
  change E ≤ J/16+adaptiveRate k*|m|/32+E/64 at heabs
  have he : E ≤ (U+M*δ)/3 := by
    linarith only [heabs, hm, hj, hcoef, hU, hMδ]
  refine ⟨he, ?_⟩
  change (2/3)*U-(7/3)*M*δ ≤ adaptiveIncrement M L v k n
  have hEq : adaptiveIncrement M L v k n = m-E := by
    dsimp only [m,E,adaptiveMixError]
    ring
  rw [hEq]
  linarith only [(abs_le.mp hmean).1, he]

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory
namespace Curvature.Sparse


variable {d : ℕ}

def adjusted (A : Finset (Fin d)) (mass : ℝ) (i : Fin d) (x : Space d) : ℝ :=
  x i + (mass - ∑ j ∈ A, x j) / A.card

def positivePart (A : Finset (Fin d)) (mass : ℝ) (i : Fin d) (x : Space d) : ℝ :=
  max 0 (adjusted A mass i x)

def sparseLoss (A : Finset (Fin d)) (mass : ℝ) (G : ℝ≥0) (i : Fin d) (x : Space d) : ℝ :=
  (G/2 : ℝ) * positivePart A mass i x

theorem adjusted_sum {A : Finset (Fin d)} (hne : A.Nonempty) (mass : ℝ) (x : Space d) :
    ∑ i ∈ A, adjusted A mass i x = mass := by
  simp only [adjusted, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr hne.card_ne_zero]
  ring

theorem positive_sum {A : Finset (Fin d)} (hne : A.Nonempty) (mass : ℝ) (x : Space d) :
    mass ≤ ∑ i ∈ A, positivePart A mass i x := by
  rw [← adjusted_sum hne mass x]
  conv_rhs => rw [adjusted_sum hne]
  exact Finset.sum_le_sum (fun i _ => le_max_right _ _)

theorem adjusted_lipschitz {A : Finset (Fin d)} (hne : A.Nonempty) (mass : ℝ) (i : Fin d) :
    LipschitzWith 2 (adjusted A mass i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hcoord (j : Fin d) : |x j - y j| ≤ ‖x-y‖ := PiLp.norm_apply_le (x-y) j
  have hsum : |∑ j ∈ A, (x j - y j)| ≤ (A.card : ℝ)*‖x-y‖ := by
    calc
      _ ≤ ∑ j ∈ A, |x j - y j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ A, ‖x-y‖ := Finset.sum_le_sum (fun j _ => hcoord j)
      _ = _ := by simp
  have hcard : 0 < (A.card : ℝ) := by exact_mod_cast hne.card_pos
  have hdiv : |(∑ j ∈ A, (x j-y j))/(A.card : ℝ)| ≤ ‖x-y‖ := by
    rw [abs_div, abs_of_pos hcard, div_le_iff₀ hcard]
    simpa [mul_comm] using hsum
  have hdiff : adjusted A mass i x - adjusted A mass i y =
      (x i-y i) - (∑ j ∈ A, (x j-y j))/(A.card:ℝ) := by
    rw [Finset.sum_sub_distrib]
    unfold adjusted
    ring
  rw [Real.dist_eq, hdiff, dist_eq_norm]
  norm_num only [NNReal.coe_ofNat]
  linarith [abs_sub (x i - y i) ((∑ j ∈ A, (x j-y j))/(A.card:ℝ)), hcoord i]

theorem positive_lipschitz {A : Finset (Fin d)} (hne : A.Nonempty) (mass : ℝ) (i : Fin d) :
    LipschitzWith 2 (positivePart A mass i) := by
  exact (adjusted_lipschitz hne mass i).const_max 0

theorem sparseLoss_lipschitz {A : Finset (Fin d)} (hne : A.Nonempty) (mass : ℝ) (G : ℝ≥0) (i : Fin d) :
    LipschitzWith G (sparseLoss A mass G i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hl := (positive_lipschitz hne mass i).dist_le_mul x y
  simp only [sparseLoss, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (G:ℝ)/2)]
  rw [Real.dist_eq, NNReal.coe_ofNat] at hl
  nlinarith only [mul_le_mul_of_nonneg_left hl G.coe_nonneg]

theorem sparseLoss_convex (A : Finset (Fin d)) (mass : ℝ) (G : ℝ≥0) (i : Fin d) :
    ConvexOn ℝ Set.univ (sparseLoss A mass G i) := by
  have hlin : ConvexOn ℝ Set.univ (adjusted A mass i) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ s t _ _ hst
    apply le_of_eq
    simp only [adjusted, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    linear_combination (mass/(A.card : ℝ)) * (Eq.symm hst)
  have hp : ConvexOn ℝ Set.univ (positivePart A mass i) := (convexOn_const _ convex_univ).sup hlin
  exact hp.smul (by positivity : 0 ≤ (G:ℝ)/2)

theorem sparseLoss_mass {A : Finset (Fin d)} (hne : A.Nonempty) (mass : ℝ) (G : ℝ≥0) (x : Space d) :
    G * mass / 2 ≤ ∑ i ∈ A, sparseLoss A mass G i x := by
  simp only [sparseLoss, ← Finset.mul_sum]
  calc
    _ = ((G:ℝ)/2)*mass := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (positive_sum hne mass x) (by positivity)

theorem sparseLoss_on_simplex {A : Finset (Fin d)} {mass : ℝ} (G : ℝ≥0)
    (i : Fin d) (x : Space d) (hs : ∑ j ∈ A, x j = mass) (hpos : 0 ≤ x i) :
    sparseLoss A mass G i x = (G:ℝ)/2*x i := by
  simp [sparseLoss, positivePart, adjusted, hs, max_eq_right hpos]

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] {K : Set E}

omit [InnerProductSpace ℝ E] in
theorem loss_integrable (μ : Measure Ω) [IsProbabilityMeasure μ] (L : FullInfoLearner E Ω K)
    (hK : Bornology.IsBounded K) {G : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith G f)
    (t : ℕ) (h : Fin t → E → ℝ) : Integrable (fun ω => f (L.predict t h ω)) μ := by
  obtain ⟨R,hR⟩ := hK.exists_norm_le
  apply (integrable_const ((G:ℝ)*R + |f 0|)).mono'
    (hf.continuous.measurable.comp (L.measurable t h)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  have hx := hR _ (L.mem t h ω)
  have hl := hf.dist_le_mul (L.predict t h ω) 0
  rw [Real.dist_eq, dist_zero_right] at hl
  rw [Real.norm_eq_abs]
  calc
    _ = |(f (L.predict t h ω)-f 0)+f 0| := by rw [sub_add_cancel]; rfl
    _ ≤ _ := (abs_add_le ..).trans (add_le_add (hl.trans (mul_le_mul_of_nonneg_left hx G.coe_nonneg)) le_rfl)

end Curvature.Sparse
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ} {K : Set (Vec d)}


theorem adaptiveAwake_iff (i t : ℕ) : i ≤ adaptiveAwake t ↔ adaptiveStart i ≤ t := by
  rw [adaptiveAwake, Nat.le_log_iff_pow_le (by decide) (Nat.succ_ne_zero t)]
  unfold adaptiveStart
  have := Nat.one_le_two_pow (n := i)
  omega

theorem adaptiveAwake_mono : Monotone adaptiveAwake := by
  intro t T ht
  exact (adaptiveAwake_iff _ _).mpr (((adaptiveAwake_iff _ _).mp le_rfl).trans ht)


def exactAdaptiveWeights (M : ℝ) : AdaptiveWeightRule M where
  prob L t i := adaptiveProbability M L 0 (adaptiveAwake t+1) i
  nonnegative L t i := adaptiveProbability_nonneg M L _ _ i
  total L t := adaptiveProbability_sum M L _ _
  awake_positive L t := Finset.sum_pos' (fun i _ => adaptiveProbability_nonneg M L _ _ i)
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _), adaptiveProbability_left_pos M L _ _⟩
  approximation L t _ _ := by
    simp only [sub_self, abs_zero, Finset.sum_const_zero]
    unfold adaptiveMixTolerance
    positivity


namespace AdaptiveBase
variable (B : AdaptiveBase K) (hcv : Convex ℝ K) {M : ℝ} (P : AdaptiveWeightRule M)


def adaptiveMixCredit (G : ℝ) (s : AdaptiveRunState d) (t : ℕ) (g : Vec d) : ℝ :=
  ∑ i ∈ Finset.Icc 0 (0+(adaptiveAwake t+1)),
    P.prob s.loss t i * (adaptiveRate i/2) * |B.adaptiveDifference hcv P G s t g i|

theorem adaptiveMixCredit_nonneg (G : ℝ) (s : AdaptiveRunState d) (t : ℕ) (g : Vec d) :
    0 ≤ B.adaptiveMixCredit hcv P G s t g := by
  unfold adaptiveMixCredit
  exact Finset.sum_nonneg fun i _ => mul_nonneg
    (mul_nonneg (P.nonnegative s.loss t i) (by have := adaptiveRate_pos i; positivity)) (abs_nonneg _)


theorem adaptivePlay_prefix (G : ℝ) (g g' : ℕ → Vec d) (t : ℕ)
    (heq : ∀ i < t, g i = g' i) :
    B.adaptivePlay hcv P G g t = B.adaptivePlay hcv P G g' t := by
  suffices B.adaptiveStateAfter hcv P G g t = B.adaptiveStateAfter hcv P G g' t
    by simp only [adaptivePlay, this]
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [adaptiveStateAfter, ih (fun i hi => heq i (by omega)), heq t (by omega)]

section Run
variable (G : ℝ) (g : ℕ → Vec d)

local notation "s" => B.adaptiveStateAfter hcv P G g
local notation "a" => B.adaptiveDifference hcv P G
local notation "w" => B.adaptiveRoundPlay hcv P G
local notation "b" => B.adaptiveBasePlay G

theorem adaptiveStateAfter_feedback_prefix (i j : ℕ) {t T : ℕ} (ht : t ≤ T) (hj : j < t) :
    (s T).feedback i j = (s t).feedback i j := by
  induction T with
  | zero => omega
  | succ T ih =>
    by_cases h : t=T+1
    · simp [h]
    · have ht' : t ≤ T := by omega
      simp only [adaptiveStateAfter, adaptiveStep, if_neg (show ¬(i ≤ adaptiveAwake T ∧ j=T)
        by omega)]
      exact ih ht'

theorem adaptiveStateAfter_feedback_norm (hG : 0 ≤ G) (hg : ∀ t, norm₂ (g t) ≤ G)
    (i j T : ℕ) : norm₂ ((s T).feedback i j) ≤ 2*G := by
  induction T with
  | zero => simpa [adaptiveStateAfter,norm₂] using (show (0:ℝ) ≤ 2*G by positivity)
  | succ T ih =>
    simp only [adaptiveStateAfter,adaptiveStep]
    split
    · exact adaptiveScaledInput_norm (g T) (hg T) i _
    · exact ih

theorem adaptiveStateAfter_feedback_current (i t T : ℕ) (ht : t < T) (hi : i ≤ adaptiveAwake t) :
    (s T).feedback i t = adaptiveScale (adaptiveRate i/2) (a (s t) t (g t) i) • g t := by
  rw [B.adaptiveStateAfter_feedback_prefix hcv P G g i t (show t+1 ≤ T by omega)
    (Nat.lt_succ_self t)]
  simp [adaptiveStateAfter,adaptiveStep,hi]

theorem adaptiveStateAfter_loss_dormant (i t : ℕ) (ht : t ≤ adaptiveStart i) :
    (s t).loss i = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hi : ¬i ≤ adaptiveAwake t := fun h => by
      have hlo := (adaptiveAwake_iff i t).mp h
      omega
    simp [adaptiveStateAfter,adaptiveStep, adaptiveDifference, hi, adaptiveUpdate, adaptiveLoss,
      ih (by omega)]

theorem adaptiveStateAfter_loss_eq (i T : ℕ) :
    (s T).loss i = ∑ t ∈ Finset.range T, adaptiveUpdate i (a (s t) t (g t) i) := by
  induction T with
  | zero => simp [adaptiveStateAfter]
  | succ T ih => simp only [adaptiveStateAfter,adaptiveStep,Finset.sum_range_succ,ih]

theorem adaptiveBasePlay_terminal (i t T : ℕ) (ht : t ≤ T) :
    b (s t) t i =
      B.play (2*G) (adaptiveRate i)
        (fun j => (s T).feedback i (j+adaptiveStart i)) (t-adaptiveStart i) := by
  apply B.play_prefix
  intro j hj
  exact (B.adaptiveStateAfter_feedback_prefix hcv P G g i _ ht (by omega)).symm

theorem adaptiveDifference_zero_mean (σ : AdaptiveRunState d) (t : ℕ) (input : Vec d) :
    (∑ i ∈ Finset.Icc 0 (0+(adaptiveAwake t+1)),
      P.prob σ.loss t i *
        a σ t input i) = 0 := by
  have hIcc : Finset.Icc 0 (0+(adaptiveAwake t+1)) = Finset.range (adaptiveAwake t+2) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hIcc, show adaptiveAwake t + 2 = (adaptiveAwake t + 1) + 1 by omega,
    Finset.sum_range_succ]
  rw [show a σ t input (adaptiveAwake t+1) = 0 by simp [adaptiveDifference], mul_zero, add_zero]
  let p := P.prob σ.loss t
  let r := adaptiveWeight P σ.loss t
  have hp (i : ℕ) : p i = adaptiveAwakeMass P σ.loss t * r i := by
    have hmass : 0 < adaptiveAwakeMass P σ.loss t := P.awake_positive σ.loss t
    change p i = adaptiveAwakeMass P σ.loss t * (p i / adaptiveAwakeMass P σ.loss t)
    rw [mul_comm, div_mul_cancel₀ _ hmass.ne']
  change (∑ i ∈ Finset.range (adaptiveAwake t+1), p i * a σ t input i) = 0
  simp_rw [hp, mul_assoc]
  rw [← Finset.mul_sum]
  suffices h : (∑ i ∈ Finset.range (adaptiveAwake t+1), r i * a σ t input i) = 0 by rw [h,mul_zero]
  have hcalc : ∀ i ∈ Finset.range (adaptiveAwake t+1), a σ t input i =
      dotProduct input (w σ t).val - dotProduct input (b σ t i).val := by
    intro i hi
    have hi' : i ≤ adaptiveAwake t := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    simp only [adaptiveDifference, if_pos hi', excess, dotProduct_sub]
  rw [Finset.sum_congr rfl (fun i hi => congrArg (fun y => r i*y) (hcalc i hi))]
  have hweights : (∑ i ∈ Finset.range (adaptiveAwake t+1), r i) = 1 :=
    adaptiveWeight_sum P σ.loss t
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hweights, one_mul]
  change dotProduct input (w σ t).val -
    (∑ i ∈ Finset.range (adaptiveAwake t+1), r i * dotProduct input (b σ t i).val) = 0
  have hsum : (∑ i ∈ Finset.range (adaptiveAwake t+1), r i * dotProduct input (b σ t i).val) =
      dotProduct input (w σ t).val := by
    change _ = dotProduct input (∑ i ∈ Finset.range (adaptiveAwake t+1), r i • (b σ t i).val)
    rw [dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul]
  rw [hsum, sub_self]

end Run
end AdaptiveBase
end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory
namespace Curvature.Sparse

abbrev Trace (E : Type*) := List (E → ℝ)

def functions {E : Type*} : (p : Trace E) → Fin p.length → E → ℝ
  | [] => Fin.elim0
  | g :: p => Fin.snoc (functions p) g

def value {E : Type*} : Trace E → E → ℝ
  | [], _ => 0
  | g :: p, x => value p x + g x

theorem value_eq {E : Type*} (p : Trace E) (x : E) : (∑ t, functions p t x) = value p x := by
  induction p with
  | nil => simp [functions,value]
  | cons g p ih =>
    refine (Fin.sum_univ_castSucc (fun t : Fin (p.length+1) => functions (g::p) t x)).trans ?_
    simpa only [functions, Fin.snoc_castSucc, Fin.snoc_last, value] using congrArg (· + g x) ih

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] {K : Set E}
    (L : FullInfoLearner E Ω K) (μ : Measure Ω) [IsProbabilityMeasure μ]

def playedValue : Trace E → Ω → ℝ
  | [], _ => 0
  | g :: p, ω => playedValue p ω + g (L.predict p.length (functions p) ω)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] in
theorem playedValue_eq (p : Trace E) (ω : Ω) :
    (∑ t, functions p t (L.predict t.val (FullInfoLearner.pastLosses (functions p) t) ω)) =
      playedValue L p ω := by
  induction p with
  | nil => simp [playedValue]
  | cons g p ih =>
    refine (Fin.sum_univ_castSucc (fun t : Fin (p.length+1) => functions (g::p) t (L.predict t.val (FullInfoLearner.pastLosses (functions (g::p)) t) ω))).trans ?_
    have h1 (t : Fin p.length) : FullInfoLearner.pastLosses (Fin.snoc (functions p) g) t.castSucc =
        FullInfoLearner.pastLosses (functions p) t := by
      funext k
      exact Fin.snoc_castSucc (n := p.length) (α := fun _ => E → ℝ) g (functions p) (⟨k.val, lt_trans k.isLt t.isLt⟩ : Fin p.length)
    have h2 : FullInfoLearner.pastLosses (Fin.snoc (functions p) g) (Fin.last p.length) = functions p := by
      funext k
      exact Fin.snoc_castSucc (n := p.length) (α := fun _ => E → ℝ) g (functions p) k
    simp only [h1,h2,functions, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last, playedValue]
    exact congrArg (· + g (L.predict p.length (functions p) ω)) ih

def Valid (G : ℝ≥0) (p : Trace E) : Prop :=
  ∀ f ∈ p, ConvexOn ℝ Set.univ f ∧ LipschitzWith G f ∧ ∀ x, 0 ≤ f x

omit [MeasurableSpace E] [BorelSpace E] in
theorem valid_at {G : ℝ≥0} {p : Trace E} (hv : Valid G p) (t : Fin p.length) :
    ConvexOn ℝ Set.univ (functions p t) ∧ LipschitzWith G (functions p t) ∧
      ∀ x, 0 ≤ functions p t x := by
  induction p with
  | nil => exact Fin.elim0 t
  | cons g p ih =>
    refine Fin.lastCases ?_ (fun k => ?_) t
    · simpa [functions] using hv g (by simp)
    · simpa [functions] using ih (fun f hf => hv f (by simp [hf])) k

theorem playedValue_integrable {G : ℝ≥0} {p : Trace E} (hv : Valid G p) (hb : Bornology.IsBounded K) :
    Integrable (playedValue L p) μ := by
  induction p with
  | nil => exact integrable_zero _ _ _
  | cons g p ih =>
    exact (ih (fun f hf => hv f (by simp [hf]))).add (loss_integrable μ L hb (hv g (by simp)).2.1 _ _)

theorem hard_of_trace {G : ℝ≥0} {p : Trace E} (hT : 0 < p.length)
    (hv : Valid G p) (hbdd : Bornology.IsBounded K) {u : E} (hu : u ∈ K)
    {b R : ℝ} (hb : value p u ≤ b) (hr : R ≤ (∫ ω, playedValue L p ω ∂μ) - value p u) :
    L.HasHardSequence μ G b R := by
  let f := functions p
  have hbest : FullInfoLearner.bestLoss K f ≤ value p u := by
    rw [← value_eq]
    exact csInf_le (s := (fun x => ∑ t, f t x) '' K)
      ⟨0, by rintro _ ⟨x,_,rfl⟩; exact Finset.sum_nonneg fun t _ => (valid_at hv t).2.2 x⟩
      (Set.mem_image_of_mem _ hu)
  have hmin (t : Fin p.length) : 0 ≤ sInf (f t '' K) := by
    apply le_csInf ⟨_,Set.mem_image_of_mem _ hu⟩
    rintro _ ⟨x,_,rfl⟩
    exact (valid_at hv t).2.2 x
  have hreg : L.regret f = fun ω => playedValue L p ω - FullInfoLearner.bestLoss K f := by
    funext ω
    exact congrArg (· - FullInfoLearner.bestLoss K f) (playedValue_eq L p ω)
  have hI := playedValue_integrable L μ hv hbdd
  refine ⟨p.length,hT,f,fun t => ⟨(valid_at hv t).1,(valid_at hv t).2.1⟩, ?_,
    hreg ▸ (hI.sub (integrable_const _)), ?_⟩
  · unfold FullInfoLearner.comparatorBudget
    linarith [Finset.sum_nonneg (fun t (_ : t ∈ Finset.univ) => hmin t)]
  · rw [hreg, integral_sub hI (integrable_const _), integral_const, probReal_univ, one_smul]
    linarith

end Curvature.Sparse
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

/-- The conjugate of the exponential penalty, evaluated at a nonnegative magnitude. -/
def expDual (t : ℝ) : ℝ := if t ≤ 1 then 0 else t*Real.log t - t + 1

theorem expDual_nonneg {t : ℝ} : 0 ≤ expDual t := by
  unfold expDual
  split_ifs with h
  · rfl
  · have ht : 0 < t := by linarith
    have hlog := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos ht) ht.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ ht.ne'] at hlog
    linarith

theorem expDual_logCost {t : ℝ} (ht : 0 ≤ t) :
    t*(1 + Real.log 2 + Real.log (max 1 t)) ≤ 4*(1 + expDual t) := by
  by_cases h : t ≤ 1
  · rw [max_eq_left h, Real.log_one, expDual, if_pos h]
    nlinarith [mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le ht]
  · have hpos : 0 < t := by linarith
    have hlog := mul_le_mul_of_nonneg_left
      (Real.one_sub_inv_le_log_of_pos (show 0 < t / (8/3) by positivity)) ht
    rw [Real.log_div hpos.ne' (by norm_num), mul_sub, mul_sub] at hlog
    have hx : t*(t/(8/3))⁻¹ = 8/3 := by field_simp
    rw [hx, mul_one] at hlog
    have h43 := Real.one_sub_inv_le_log_of_pos (by norm_num : 0 < (4:ℝ)/3)
    norm_num at h43
    have hc : 2 + Real.log 2 ≤ 3*Real.log (8/3) := by
      rw [show (8:ℝ)/3 = 2*(4/3) by ring, Real.log_mul (by norm_num) (by norm_num)]
      linarith [Real.log_two_gt_d9]
    rw [max_eq_right (by linarith), expDual, if_neg h]
    nlinarith [mul_le_mul_of_nonneg_left hc ht]

theorem exists_dyadicFloor_between {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ∃ J : ℕ, x/2 < ((2 : ℝ)^J)⁻¹ ∧ ((2 : ℝ)^J)⁻¹ ≤ x := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one hx hx1
    (by norm_num : 0 < (2:ℝ)⁻¹) (by norm_num : (2:ℝ)⁻¹ < 1)
  simp only [inv_pow] at hn hn'
  by_cases he : x = ((2:ℝ)^n)⁻¹
  · exact ⟨n, by linarith, he.ge⟩
  · refine ⟨n+1, ?_, hn.le⟩
    rw [pow_succ, mul_inv_rev]
    have hlt := lt_of_le_of_ne hn' he
    linarith

theorem dualLength_bound {c β y : ℝ} (hc : 0 ≤ c) (hβ : 0 < β)
    (hy : β*expDual (|y|/β) ≤ c) : |y| ≤ Real.exp 2*(c+β) := by
  let t := |y|/β
  have hmul : β*t = |y| := by dsimp [t]; field_simp
  have he : 1 < Real.exp 2 := (Real.one_lt_exp_iff).mpr (by norm_num)
  by_cases ht : t < Real.exp 2
  · have h1 := mul_le_mul_of_nonneg_left ht.le hβ.le
    nlinarith [mul_nonneg (Real.exp_pos 2).le hc]
  · have hlog : 2 ≤ Real.log t := (Real.le_log_iff_exp_le (he.trans_le (le_of_not_gt ht) |>.trans' zero_lt_one)).mpr (le_of_not_gt ht)
    have htt : 1 < t := he.trans_le (le_of_not_gt ht)
    have h1 : t ≤ expDual t := by
      rw [expDual, if_neg htt.not_ge]
      nlinarith [mul_le_mul_of_nonneg_left hlog (zero_lt_one.trans htt).le]
    have h2 := mul_le_mul_of_nonneg_left h1 hβ.le
    change β*expDual t ≤ c at hy
    nlinarith [mul_le_mul_of_nonneg_right he.le hc, mul_nonneg (Real.exp_pos 2).le hβ.le]

theorem dualCoordinateCost {ℓ h β y : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) (hβ : 0 < β)
    (hlo : β ≤ 2*ℓ*h) (hhi : ℓ*h ≤ β) :
    ℓ*(h + |y/ℓ| * (1 + Real.log (max 1 (|y/ℓ| / h)))) ≤
      β + 4*β*(1 + expDual (|y|/β)) := by
  let t := |y|/β
  have ht : 0 ≤ t := div_nonneg (abs_nonneg _) hβ.le
  have hyt : β*t = |y| := by dsimp [t]; field_simp
  rw [abs_div, abs_of_pos hℓ]
  have hratio : |y|/ℓ/h ≤ 2*t := by
    rw [div_le_iff₀ hh, div_le_iff₀ hℓ, ← hyt]
    nlinarith [mul_le_mul_of_nonneg_right hlo ht]
  have hmax : max 1 (|y|/ℓ/h) ≤ 2*max 1 t := by
    apply max_le _ _
    · linarith [le_max_left 1 t]
    · linarith [le_max_right 1 t]
  have hlog := Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hmax
  rw [Real.log_mul (by norm_num) (lt_of_lt_of_le zero_lt_one (le_max_left _ _)).ne'] at hlog
  have hscalar := mul_le_mul_of_nonneg_left (expDual_logCost ht) hβ.le
  have h1 := mul_le_mul_of_nonneg_left hlog (abs_nonneg y)
  have heq : ℓ*(h + |y|/ℓ*(1 + Real.log (max 1 (|y|/ℓ/h)))) =
      ℓ*h + |y| *(1 + Real.log (max 1 (|y|/ℓ/h))) := by field_simp
  rw [heq]
  change _ ≤ β + 4*β*(1+expDual t)
  rw [← mul_assoc, hyt] at hscalar
  linarith

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory
namespace Curvature.Sparse

variable {m d : ℕ}
def blockSet (e : Fin m ↪ Fin d) := Finset.univ.map e

theorem block_nonempty [NeZero m] (e : Fin m ↪ Fin d) : (blockSet e).Nonempty :=
  Finset.univ_nonempty.map

def blockMass (e : Fin m ↪ Fin d) (a : ℝ) (x : Space d) : ℝ :=
  ∑ i, positivePart (blockSet e) a (e i) x

theorem blockMass_ge [NeZero m] (e : Fin m ↪ Fin d) (a : ℝ) (x : Space d) : a ≤ blockMass e a x := by
  simpa [blockMass,blockSet] using positive_sum (block_nonempty e) a x

def blockPrediction [NeZero m] (e : Fin m ↪ Fin d) (a : ℝ) (ha : 0 < a) (x : Space d) : Prediction m where
  p i := positivePart (blockSet e) a (e i) x / blockMass e a x
  nonneg i := div_nonneg (le_max_left _ _) (ha.trans_le (blockMass_ge e a x)).le
  normalized := by rw [← Finset.sum_div]; exact div_self (ha.trans_le (blockMass_ge e a x)).ne'

theorem scaled_prediction_le [NeZero m] (e : Fin m ↪ Fin d) (a : ℝ) (ha : 0 < a) (G : ℝ≥0)
    (x : Space d) (i : Fin m) :
    ((G:ℝ)*a/2) * (blockPrediction e a ha x).p i ≤ sparseLoss (blockSet e) a G (e i) x := by
  have hM := blockMass_ge e a x
  have hscale : a * (positivePart (blockSet e) a (e i) x / blockMass e a x) ≤ positivePart (blockSet e) a (e i) x := by
    rw [← mul_div_assoc, div_le_iff₀ (ha.trans_le hM)]
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hM (show 0 ≤ positivePart (blockSet e) a (e i) x from le_max_left _ _)
  change ((G:ℝ)*a/2) * (_ / _) ≤ ((G:ℝ)/2)*_
  nlinarith only [mul_le_mul_of_nonneg_left hscale G.coe_nonneg]

def blockTrace (p : Trace (Space d)) (e : Fin m ↪ Fin d) (a : ℝ) (G : ℝ≥0) :
    (t : ℕ) → Hist m t → Trace (Space d)
  | 0, _ => p
  | t+1, h => sparseLoss (blockSet e) a G (e h.2) :: blockTrace p e a G t h.1

theorem block_valid [NeZero m] {G : ℝ≥0} {p : Trace (Space d)} (hp : Valid G p) (e : Fin m ↪ Fin d)
    (a : ℝ) (s : ℕ) (h : Hist m s) : Valid G (blockTrace p e a G s h) := by
  induction s with
  | zero => exact hp
  | succ s ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hs
    · exact ⟨sparseLoss_convex _ _ _ _, sparseLoss_lipschitz (block_nonempty e) _ _ _,
      fun _ => mul_nonneg (by positivity) (le_max_left _ _)⟩
    · exact ih h.1 f hs

theorem block_length (p : Trace (Space d)) (e : Fin m ↪ Fin d) (a : ℝ) (G : ℝ≥0)
    (s : ℕ) (h : Hist m s) : (blockTrace p e a G s h).length = p.length+s := by
  induction s with
  | zero => rfl
  | succ s ih => simp [blockTrace,ih,Nat.add_assoc]

theorem vertex_count (p : Trace (Space d)) (e : Fin m ↪ Fin d) (a : ℝ) (ha : 0 ≤ a) (G : ℝ≥0)
    (j : Fin m) (u : Space d) (hu : ∀ i, u (e i) = if i = j then a else 0) (s : ℕ) (h : Hist m s) :
    value (blockTrace p e a G s h) u = value p u + ((G:ℝ)*a/2)*count j s h := by
  have hsum : ∑ i ∈ blockSet e, u i = a := by simp [blockSet,hu]
  induction s with
  | zero => simp [blockTrace,count]
  | succ s ih =>
    have hnonneg : 0 ≤ u (e h.2) := by rw [hu]; split_ifs <;> positivity
    simp only [blockTrace,value,count,ih,sparseLoss_on_simplex G _ u hsum hnonneg,hu]
    split_ifs <;> ring

variable {Ω : Type*} [MeasurableSpace Ω] {K : Set (Space d)}
variable (L : FullInfoLearner (Space d) Ω K)

def expertInBlock [NeZero m] (p : Trace (Space d)) (e : Fin m ↪ Fin d) (a : ℝ) (ha : 0 < a)
    (G : ℝ≥0) : RandomizedStrategy m Ω where
  predict s h ω :=
    let q := blockTrace p e a G s h
    blockPrediction e a ha (L.predict q.length (functions q) ω)
  measurable s h j := by
    let q := blockTrace p e a G s h
    have hi (i : Fin m) := (positive_lipschitz (block_nonempty e) a (e i)).continuous.measurable.comp
      (L.measurable q.length (functions q))
    exact (hi j).div (Finset.measurable_fun_sum _ (fun i _ => hi i))

theorem block_played [NeZero m] (p : Trace (Space d)) (e : Fin m ↪ Fin d) (a : ℝ) (ha : 0 < a)
    (G : ℝ≥0) (s : ℕ) (h : Hist m s) (ω : Ω) :
    playedValue L p ω + ((G:ℝ)*a/2)*realized (expertInBlock L p e a ha G) s h ω ≤
      playedValue L (blockTrace p e a G s h) ω := by
  induction s with
  | zero => simp [blockTrace,realized,cumulative]
  | succ s ih =>
    let q := blockTrace p e a G s h.1
    let x := L.predict q.length (functions q) ω
    change playedValue L p ω + ((G:ℝ)*a/2) *
      (realized (expertInBlock L p e a ha G) s h.1 ω + (blockPrediction e a ha x).p h.2) ≤
      playedValue L q ω + sparseLoss (blockSet e) a G (e h.2) x
    linarith [scaled_prediction_le e a ha G x h.2, ih h.1]

theorem one_block (μ : Measure Ω) [IsProbabilityMeasure μ] (hbdd : Bornology.IsBounded K)
    {n : ℕ} (hm : 2 ≤ m) (hn : m*Real.log m ≤ n) (p : Trace (Space d)) (e : Fin m ↪ Fin d)
    (a : ℝ) (ha : 0 < a) (G : ℝ≥0) (hp : Valid G p) :
    ∃ q : Trace (Space d), ∃ j : Fin m, ∃ c : ℝ,
      Valid G q ∧ q.length = p.length+n ∧ c ≤ ((G:ℝ)*a/2)*(n/(m:ℝ)) ∧
      (∀ u : Space d, (∀ i, u (e i) = if i=j then a else 0) → value q u = value p u + c) ∧
      (∫ ω, playedValue L p ω ∂μ) + c + ((G:ℝ)*a/2)*(Real.sqrt (n*Real.log m/m)/24) ≤
        ∫ ω, playedValue L q ω ∂μ := by
  let : NeZero m := ⟨by omega⟩
  let learner := expertInBlock L p e a ha G
  let sc := (G:ℝ)*a/2
  have hsc : 0 ≤ sc := by dsimp [sc]; positivity
  obtain ⟨hb,h,hr⟩ := experts_lower μ learner hm hn
  obtain ⟨j,hj,hj'⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin m)) (fun i => count i n h)
    Finset.univ_nonempty
  have hmin : count j n h = bestCount n h := le_antisymm (Finset.le_inf' _ _ hj') (bestCount_le n h j)
  let q := blockTrace p e a G n h
  have hq := block_valid hp e a n h
  refine ⟨q,j,sc*bestCount n h,hq,block_length p e a G n h, mul_le_mul_of_nonneg_left (hb h) hsc, ?_, ?_⟩
  · intro u hu
    simpa [hmin,sc,q] using vertex_count p e a ha.le G j u hu n h
  · obtain ⟨hi,_⟩ := realized_integral μ learner n h
    rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul] at hr
    have hpI := playedValue_integrable L μ hp hbdd
    have hg := integral_mono (hpI.add (hi.const_mul sc)) (playedValue_integrable L μ hq hbdd)
      (fun ω => block_played L p e a ha G n h ω)
    change (∫ ω, playedValue L p ω + sc*realized learner n h ω ∂μ) ≤ ∫ ω, playedValue L q ω ∂μ at hg
    rw [integral_add hpI (hi.const_mul sc), integral_const_mul] at hg
    change (∫ ω, playedValue L p ω ∂μ) + sc*bestCount n h + sc*(Real.sqrt (n*Real.log m/m)/24) ≤ _
    nlinarith only [hg,mul_le_mul_of_nonneg_left hr hsc]

end Curvature.Sparse
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory
namespace Curvature.Sparse

variable {d : ℕ}

def faceVertex (a : ℝ) (B : Finset (Fin d)) : Space d :=
  WithLp.toLp 2 fun j => if j ∈ B then a else 0

theorem mass_faceVertex {A B : Finset (Fin d)} (hs : B ⊆ A) (a : ℝ) :
    ∑ j ∈ A, faceVertex a B j = B.card * a := by
  change (∑ j ∈ A, if j ∈ B then a else 0) = _
  rw [← Finset.sum_filter]
  have he : A.filter (· ∈ B) = B := by ext i; simp only [Finset.mem_filter]; exact and_iff_right_of_imp (@hs i)
  simp [he]

def harmonicTail (k : ℕ) : ℕ → ℝ
  | 0 => 0
  | t+1 => harmonicTail k t + 1/(k+t+1:ℝ)

variable {Ω : Type*} [MeasurableSpace Ω] {K : Set (Space d)} (L : FullInfoLearner (Space d) Ω K)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hK : Bornology.IsBounded K)

include hK

theorem exists_large_loss {A : Finset (Fin d)} (hne : A.Nonempty) (mass : ℝ) (G : ℝ≥0)
    (p : Trace (Space d)) :
    ∃ i ∈ A, G * mass / (2*A.card) ≤
      ∫ ω, sparseLoss A mass G i (L.predict p.length (functions p) ω) ∂μ := by
  let f := fun i ω => sparseLoss A mass G i (L.predict p.length (functions p) ω)
  have hI (i : Fin d) : Integrable (f i) μ :=
    loss_integrable μ L hK (sparseLoss_lipschitz hne mass G i) _ _
  have h := integral_mono (μ := μ) (integrable_const ((G:ℝ)*mass/2))
    (integrable_finsetSum A (fun i _ => hI i)) (fun ω => sparseLoss_mass hne mass G (L.predict p.length (functions p) ω))
  change (∫ _ : Ω, (G:ℝ)*mass/2 ∂μ) ≤ ∫ ω, ∑ i ∈ A, f i ω ∂μ at h
  rw [integral_const, probReal_univ, one_smul, integral_finsetSum A (fun i _ => hI i)] at h
  apply Finset.exists_le_of_le_expect hne
  rw [Finset.expect_eq_sum_div_card]
  have hA : 0 < (A.card:ℝ) := by exact_mod_cast hne.card_pos
  calc
    _ = ((G:ℝ)*mass/2)/A.card := by rw [div_div]
    _ ≤ _ := div_le_div_of_nonneg_right h hA.le

private theorem extend_clean (k : ℕ) (a : ℝ) (G : ℝ≥0) (s : ℕ) (A : Finset (Fin d))
    (hA : A.card = k+s) (p : Trace (Space d)) (hp : Valid G p) :
    ∃ q : Trace (Space d), ∃ B : Finset (Fin d),
      Valid G q ∧ B ⊆ A ∧ B.card = k ∧ q.length = p.length+s ∧
      value q (faceVertex a B) = value p (faceVertex a B) ∧
      (∫ ω, playedValue L p ω ∂μ) + ((G:ℝ)*(k*a)/2) * harmonicTail k s ≤
        ∫ ω, playedValue L q ω ∂μ := by
  induction s generalizing A p with
  | zero => exact ⟨p,A,hp,Finset.Subset.rfl,by simpa using hA,by simp,rfl,by simp [harmonicTail]⟩
  | succ s ih =>
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    let mass := (k:ℝ)*a
    obtain ⟨i,hi,hgain⟩ := exists_large_loss L μ hK hne mass G p
    let g := sparseLoss A mass G i
    have hgi := loss_integrable μ L hK (sparseLoss_lipschitz hne mass G i) p.length (functions p)
    have hv : Valid G (g::p) := by
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hh
      · exact ⟨sparseLoss_convex A mass G i, sparseLoss_lipschitz hne mass G i,
        fun _ => mul_nonneg (by positivity) (le_max_left _ _)⟩
      · exact hp f hh
    obtain ⟨q,B,hq,hBA,hB,hlen,hval,hreg⟩ := ih (A.erase i)
      (by rw [Finset.card_erase_of_mem hi]; omega) (g::p) hv
    have hBA' := hBA.trans (Finset.erase_subset i A)
    have hnot : i ∉ B := fun hb => (Finset.mem_erase.mp (hBA hb)).1 rfl
    have hzero : g (faceVertex a B) = 0 := by
      have hs : ∑ j ∈ A, faceVertex a B j = mass := by rw [mass_faceVertex hBA', hB]
      have hz : faceVertex a B i = 0 := by simp [faceVertex,hnot]
      simp [g,sparseLoss_on_simplex G i _ hs (by rw [hz]),hz]
    refine ⟨q,B,hq,hBA',hB,by simp at hlen; omega,by simpa [value,hzero] using hval,?_⟩
    have hrec : (∫ ω, playedValue L (g::p) ω ∂μ) =
        (∫ ω, playedValue L p ω ∂μ) + ∫ ω, g (L.predict p.length (functions p) ω) ∂μ :=
      integral_add (playedValue_integrable L μ hp hK) hgi
    rw [hrec] at hreg
    rw [hA, Nat.cast_add, Nat.cast_succ] at hgain
    change (G:ℝ)*mass/(2*((k:ℝ)+(s+1))) ≤ ∫ ω, g (L.predict p.length (functions p) ω) ∂μ at hgain
    change (∫ ω, playedValue L p ω ∂μ) + ((G:ℝ)*mass/2) * (harmonicTail k s + 1/(k+s+1:ℝ)) ≤ _
    have he : ((G:ℝ)*mass/2)*(1/(k+s+1:ℝ)) = G*mass/(2*((k:ℝ)+(s+1))) := by
      rw [← add_assoc, ← div_div, div_eq_mul_one_div ((G:ℝ)*mass/2)]
    rw [mul_add, he]
    linarith

theorem clean_lower {k : ℕ} (hk : k < d) (a : ℝ) (G : ℝ≥0)
    (hfaces : ∀ B : Finset (Fin d), B.card = k → faceVertex a B ∈ K) :
    L.HasHardSequence μ G 0 (G*(k*a)/2 * harmonicTail k (d-k)) := by
  obtain ⟨p,B,hp,_,hB,hlen,hvalue,hreg⟩ := extend_clean L μ hK k a G (d-k) Finset.univ
    (by simp; omega) [] (by simp [Valid])
  apply hard_of_trace L μ (p := p) (u := faceVertex a B) (by simp at hlen; omega) hp hK (hfaces B hB)
  · simpa [value] using hvalue.le
  · simpa [hvalue,value,playedValue] using hreg

end Curvature.Sparse
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory
namespace Curvature.Sparse

variable {d m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {K : Set (Space d)}
    (L : FullInfoLearner (Space d) Ω K) (μ : Measure Ω) [IsProbabilityMeasure μ]

private theorem assemble_blocks (hbdd : Bornology.IsBounded K) (hm : 2 ≤ m) (hn : m*Real.log m ≤ n)
    (a : ℝ) (ha : 0 < a) (G : ℝ≥0) (k : ℕ) (e : Fin k → (Fin m ↪ Fin d)) :
    let scale := (G:ℝ)*a/2
    ∃ p : Trace (Space d), ∃ j : Fin k → Fin m, ∃ c : ℝ,
      Valid G p ∧ p.length = k*n ∧ c ≤ k*(scale*(n/(m:ℝ))) ∧
      (∀ u : Space d, (∀ l i, u (e l i) = if i=j l then a else 0) → value p u = c) ∧
      c + k*(scale*(Real.sqrt (n*Real.log m/m)/24)) ≤ ∫ ω, playedValue L p ω ∂μ := by
  let sc := (G:ℝ)*a/2
  induction k with
  | zero => exact ⟨[],Fin.elim0,0,by simp [Valid],by simp,by simp,fun _ _ => rfl,by simp [playedValue]⟩
  | succ k ih =>
    obtain ⟨p,j,c,hp,hp_len,hc,hu,hgain⟩ := ih (fun i => e i.castSucc)
    obtain ⟨q,j',c',hq,hq_len,hc',hu',hgain'⟩ := one_block L μ hbdd hm hn p (e (Fin.last k)) a ha G hp
    refine ⟨q,Fin.snoc j j',c+c',hq,?_,?_,?_,?_⟩
    · rw [hq_len,hp_len,Nat.succ_mul]
    · rw [Nat.cast_succ,add_mul,one_mul]
      exact add_le_add hc hc'
    · intro u hh
      rw [hu' u (fun i => by simpa using hh (Fin.last k) i)]
      rw [hu u (fun l i => by simpa using hh l.castSucc i)]
    · rw [Nat.cast_succ,add_mul,one_mul]
      linarith

def blockEmbedding {k : ℕ} (e : Fin k × Fin m ↪ Fin d) (j : Fin k) : Fin m ↪ Fin d :=
  ⟨fun i => e (j,i), fun _ _ h => congrArg Prod.snd (e.injective h)⟩

theorem block_transfer {k : ℕ} (hk : 0 < k) (hm : 2 ≤ m) (hn : m*Real.log m ≤ n)
    (e : Fin k × Fin m ↪ Fin d) (a : ℝ) (ha : 0 < a) (G : ℝ≥0)
    (hbdd : Bornology.IsBounded K)
    (hfaces : ∀ B : Finset (Fin d), B.card = k → faceVertex a B ∈ K) :
    let sc := (G:ℝ)*a/2
    L.HasHardSequence μ G (k*(sc*(n/(m:ℝ)))) (k*(sc*(Real.sqrt (n*Real.log m/m)/24))) := by
  have hm' : 1 < (m:ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hn' : 0 < n := by
    exact_mod_cast lt_of_lt_of_le (mul_pos (lt_trans zero_lt_one hm') (Real.log_pos hm')) hn
  obtain ⟨p,j,c,hp,hlen,hbudget,hu,hr⟩ := assemble_blocks L μ hbdd hm hn a ha G k (blockEmbedding e)
  let pick : Fin k ↪ Fin d := ⟨fun l => e (l,j l), fun _ _ h => congrArg Prod.fst (e.injective h)⟩
  let B := Finset.univ.map pick
  have hB : B.card = k := by simp [B]
  have hmem (l : Fin k) (i : Fin m) : e (l,i) ∈ B ↔ i=j l := by
    constructor
    · rintro h
      obtain ⟨w,_,hw⟩ := Finset.mem_map.mp h
      have hp : (w,j w) = (l,i) := e.injective hw
      have heq : w = l := congrArg Prod.fst hp
      subst w
      exact (congrArg Prod.snd hp).symm
    · rintro rfl
      exact Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩
  have hvalue := hu (faceVertex a B) (fun l i => by
    change (if e (l,i) ∈ B then a else 0) = _
    exact if_congr (hmem l i) rfl rfl)
  apply hard_of_trace L μ (u := faceVertex a B) (p := p) (by rw [hlen]; exact Nat.mul_pos hk hn')
    hp hbdd (hfaces B hB)
  · simpa [hvalue] using hbudget
  · rw [hvalue]
    linarith

end Curvature.Sparse
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory
namespace Curvature.Sparse

theorem harmonic_log {k : ℕ} (hk : 0 < k) (s : ℕ) :
    Real.log (((k:ℝ)+s)/k) ≤ 2*harmonicTail k s := by
  have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  induction s with
  | zero => simp [harmonicTail,hk'.ne']
  | succ s ih =>
    let v := (k:ℝ)+s
    have hv : 1 ≤ v := by dsimp [v]; linarith [Nat.cast_nonneg (α := ℝ) s]
    have hv0 : 0 < v := by linarith
    have hq : 0 < (v+1)/v := by positivity
    have hlog := Real.log_le_sub_one_of_pos hq
    have he : (v+1)/v - 1 = 1/v := by field_simp; ring
    rw [he] at hlog
    have hh : 1/v ≤ 2/(v+1) := (div_le_div_iff₀ hv0 (by positivity)).mpr (by linarith)
    have he' : (((k:ℝ)+(s+1))/k) = (v/k)*((v+1)/v) := by dsimp [v]; field_simp; ring
    rw [Nat.cast_succ, he', Real.log_mul (div_ne_zero hv0.ne' hk'.ne') hq.ne', harmonicTail]
    change Real.log (v/k) + Real.log ((v+1)/v) ≤ 2*(harmonicTail k s + 1/(v+1))
    change Real.log (v/k) ≤ _ at ih
    rw [show 2/(v+1) = 2*(1/(v+1)) by ring] at hh
    linarith

private theorem hard_mono {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {K : Set (Space d)}
    {L : FullInfoLearner (Space d) Ω K} {μ : Measure Ω} {G : ℝ≥0} {b c R S : ℝ}
    (h : L.HasHardSequence μ G c S) (hb : c ≤ b) (hr : R ≤ S) : L.HasHardSequence μ G b R := by
  obtain ⟨t,ht,f,hvalid,hc,hi,hs⟩ := h
  exact ⟨t,ht,f,hvalid,hc.trans hb,hi,hr.trans hs⟩

theorem block_budget {d k m : ℕ} {Ω : Type*} [MeasurableSpace Ω] {K : Set (Space d)}
    (L : FullInfoLearner (Space d) Ω K) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hk : 0 < k) (hm : 2 ≤ m) (hkm : k*m ≤ d)
    (a : ℝ) (ha : 0 < a) (G : ℝ≥0) (hG : 0 < G) (b : ℝ) (hb : 0 ≤ b)
    (hbdd : Bornology.IsBounded K)
    (hfaces : ∀ B : Finset (Fin d), B.card = k → faceVertex a B ∈ K) :
    let W := G * (k*a) * Real.log m
    L.HasHardSequence μ G b ((W + Real.sqrt (W*b))/128) := by
  let A := (G:ℝ)*(k*a)
  let W := A * Real.log m
  change L.HasHardSequence μ G b ((W + Real.sqrt (W*b))/128)
  have hA : 0 < A := mul_pos (by exact_mod_cast hG) (mul_pos (by exact_mod_cast hk) ha)
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : 0 < (m:ℝ) := by linarith
  have hlog : 0 < Real.log m := Real.log_pos (by linarith)
  have hW : 0 < W := mul_pos hA hlog
  have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
  have hk_lt : k < d := by nlinarith only [hk,hkm,Nat.mul_le_mul_left k hm]
  by_cases hsmall : b ≤ W
  · have hmle : (m:ℝ) ≤ d/k := (le_div_iff₀ hk').mpr (by exact_mod_cast (Nat.mul_comm k m ▸ hkm))
    have hh := harmonic_log hk (d-k)
    rw [Nat.cast_sub hk_lt.le, add_sub_cancel] at hh
    have htail := (Real.log_le_log hm0 hmle).trans hh
    have hroot : Real.sqrt (W*b) ≤ W := Real.sqrt_le_iff.mpr ⟨hW.le,by nlinarith [mul_le_mul_of_nonneg_left hsmall hW.le]⟩
    apply hard_mono (clean_lower L μ hbdd hk_lt a G hfaces) hb
    change (W + Real.sqrt (W*b))/128 ≤ A/2 * harmonicTail k (d-k)
    dsimp [W] at hroot ⊢
    nlinarith only [hroot,mul_le_mul_of_nonneg_left htail hA.le, mul_nonneg hA.le hlog.le]
  · let x := b*m/A
    have hx : m*Real.log m ≤ x := by
      apply (le_div_iff₀ hA).mpr
      have hw : A*Real.log m ≤ b := (lt_of_not_ge hsmall).le
      nlinarith only [mul_le_mul_of_nonneg_right hw hm0.le]
    have hx1 : 1 ≤ x := by
      have h := Real.one_sub_inv_le_log_of_pos hm0
      have hr := mul_le_mul_of_nonneg_left h hm0.le
      rw [mul_sub, mul_one, mul_inv_cancel₀ hm0.ne'] at hr
      linarith
    let n := ⌊2*x⌋₊
    have hnlow : x ≤ n := by have h := Nat.lt_floor_add_one (2*x); change x ≤ (⌊2*x⌋₊:ℝ); linarith
    have hnhigh : (n:ℝ) ≤ 2*x := Nat.floor_le (by linarith)
    let e : Fin k × Fin m ↪ Fin d := finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb hkm)
    have hhard := block_transfer L μ hk hm (hx.trans hnlow) e a ha G hbdd hfaces
    apply hard_mono hhard
    · have h : k*((G:ℝ)*a/2*(n/(m:ℝ))) = (n:ℝ)*A/(2*m) := by dsimp [A]; ring
      rw [h, div_le_iff₀ (by positivity)]
      have hr := mul_le_mul_of_nonneg_right hnhigh hA.le
      dsimp [x] at hr
      field_simp [hA.ne'] at hr
      linarith
    · have hrootU : Real.sqrt (W*b) ≤ A*Real.sqrt (n*Real.log m/m) := by
        apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        have hnP := (div_le_iff₀ hA).mp hnlow
        dsimp only [W]
        rw [← mul_div_assoc, le_div_iff₀ hm0]
        nlinarith only [mul_le_mul_of_nonneg_right hnP (mul_nonneg hA.le hlog.le)]
      have hrootL : W ≤ Real.sqrt (W*b) := by
        apply Real.le_sqrt_of_sq_le
        nlinarith [mul_le_mul_of_nonneg_left ((lt_of_not_ge hsmall).le) hW.le]
      have heq : k*((G:ℝ)*a/2*(Real.sqrt (n*Real.log m/m)/24)) = A*Real.sqrt (n*Real.log m/m)/48 := by
        dsimp [A]; ring
      rw [heq]
      linarith [Real.sqrt_nonneg (W*b)]

end Curvature.Sparse
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace NNReal
namespace Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem subexponentialWidth_mono [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (K S : Set E) (hne : K.Nonempty) (hb : Bornology.IsBounded S) (hin : K ⊆ S) :
    subexponentialWidth K ≤ subexponentialWidth S := by
  have hneS := hne.mono hin
  let : Nonempty K := hne.to_subtype
  have hpoint (z : E) : widthSupport K z ≤ widthSupport S z := by
    obtain ⟨R, _, hR⟩ := hb.exists_pos_norm_le
    have hbd : BddAbove (Set.range fun w : S => ⟪w.val,z⟫_ℝ) := by
      refine ⟨R*‖z‖, ?_⟩
      rintro _ ⟨w,rfl⟩
      exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hR _ w.prop) (norm_nonneg _))
    exact ciSup_le fun w : K => le_ciSup (f := fun v : S => ⟪v.val,z⟫_ℝ) hbd ⟨w.val, hin w.prop⟩
  apply width_le_of_forall K hne
  intro μ hμ
  exact (integral_mono (widthSupport_integrable K hne (hb.subset hin) hμ)
    (widthSupport_integrable S hneS hb hμ) hpoint).trans
    (le_width_of_law S (widthValues_bddAbove S hneS hb) hμ)

namespace Coordinate

variable {r : ℕ} [NeZero r]

def fixedLpBody (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Vec r) (q : ℝ) : Set E :=
  position c U '' {z : Axes r | fixedUnitCoeffs q (fun i => z i / a i)}

def fixedInnerAxes (a : Vec r) (q : ℝ) (i : Fin r) : ℝ :=
  fixedAxisScale a q * (fixedAxisWeight a q i)^q

def fixedOuterAxes (a : Vec r) (q : ℝ) (i : Fin r) : ℝ :=
  fixedAxisScale a q * (fixedAxisWeight a q i)^(q/2)

omit [NeZero r] in
private theorem fixedUnitCoeffs_solid {q : ℝ} (hq : 1 ≤ q) (x y : Vec r)
    (hle : ∀ i, |x i| ≤ |y i|) (hy : fixedUnitCoeffs q y) : fixedUnitCoeffs q x := by
  by_cases h : q=1
  · exact (if_pos h).mpr fun i => (hle i).trans ((if_pos h).mp hy i)
  · simp only [fixedUnitCoeffs, if_neg h] at hy ⊢
    exact (Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow (abs_nonneg _) (hle i)
      (div_nonneg (by linarith) (by linarith)))).trans hy

theorem fixedInner_sum {a : Vec r} (ha : ∀ i, 0 < a i) {q : ℝ} (hq : 0 < q) :
    ∑ i, fixedInnerAxes a q i = fixedAxisScale a q := by
  simp only [fixedInnerAxes, ← Finset.mul_sum, fixedAxisWeight_sum ha hq, mul_one]

private theorem outerAxis_sq {a : Vec r} (ha : ∀ i, 0 < a i) (q : ℝ) (i : Fin r) :
    fixedOuterAxes a q i ^ 2 = (fixedAxisScale a q)^2*(fixedAxisWeight a q i)^q := by
  rw [fixedOuterAxes, mul_pow, ← Real.rpow_two ((fixedAxisWeight a q i)^(q/2)),
    ← Real.rpow_mul (fixedAxisWeight_pos ha q i).le]
  ring_nf

theorem fixedOuter_length {a : Vec r} (ha : ∀ i, 0 < a i) {q : ℝ} (hq : 0 < q) :
    axesLength (fixedOuterAxes a q) = fixedAxisScale a q := by
  unfold axesLength
  simp_rw [outerAxis_sq ha]
  rw [← Finset.mul_sum, fixedAxisWeight_sum ha hq, mul_one, Real.sqrt_sq (fixedAxisScale_pos ha q).le]

theorem fixedInner_subset (c : E) (U : Axes r →ₗᵢ[ℝ] E) {a : Vec r} (ha : ∀ i, 0 < a i)
    {q : ℝ} (hq : 1 ≤ q) : box c U (fixedInnerAxes a q) ⊆ fixedLpBody c U a q := by
  rintro _ ⟨z,hz,rfl⟩
  refine ⟨z, ?_, rfl⟩
  apply fixedUnitCoeffs_solid hq _ (fixedAxisComparator a q (fun _ => true)) _ (fixedAxisComparator_mem ha hq _)
  intro i
  let S := fixedAxisScale a q
  let b := fixedAxisWeight a q i
  have hS : 0 < S := fixedAxisScale_pos ha q
  have hb : 0 < b := fixedAxisWeight_pos ha q i
  have hab : a i = S*b := by dsimp [S,b,fixedAxisWeight]; field_simp [(fixedAxisScale_pos ha q).ne']
  simp only [fixedAxisComparator, SignGame.sign, if_true, mul_one, abs_of_pos (Real.rpow_pos_of_pos (fixedAxisWeight_pos ha q i) (q-1)),
    abs_div, abs_of_pos (ha i)]
  apply (div_le_iff₀ (ha i)).mpr
  refine (hz i).trans_eq ?_
  change S*b^q = b^(q-1)*a i
  rw [hab, mul_left_comm, ← Real.rpow_add_one hb.ne', sub_add_cancel]

theorem fixedBody_subset_ellipsoid (c : E) (U : Axes r →ₗᵢ[ℝ] E) {a : Vec r} (ha : ∀ i, 0 < a i)
    {q : ℝ} (hq : 1 ≤ q) (hq' : q ≤ 2) :
    fixedLpBody c U a q ⊆ ellipsoid c U (fixedOuterAxes a q) := by
  rintro _ ⟨z,hz,rfl⟩
  refine ⟨z, ?_, rfl⟩
  have h := fixedAxis_energy_le ha hq hq' (fun i => z i/a i) hz
  refine (Finset.sum_congr rfl (fun i _ => ?_)).le.trans h
  let S := fixedAxisScale a q
  let b := fixedAxisWeight a q i
  have hS : 0 < S := fixedAxisScale_pos ha q
  have hb : 0 < b := fixedAxisWeight_pos ha q i
  have hab : a i = S*b := by dsimp [S,b,fixedAxisWeight]; field_simp [(fixedAxisScale_pos ha q).ne']
  have hm : b^(2-q)*b^q=b^2 := by rw [← Real.rpow_add hb, sub_add_cancel, Real.rpow_two]
  rw [div_pow, outerAxis_sq ha]
  change z i^2/(S^2*b^q) = b^(2-q)*(z i / a i)^2
  rw [hab, div_pow, mul_pow]
  field_simp [(Real.rpow_pos_of_pos hb q).ne', hb.ne', hS.ne']
  linear_combination -(z i)^2*hm

theorem fixedLpBudgetLower [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Type*} [MeasurableSpace Ω] (c : E) (U : Axes r →ₗᵢ[ℝ] E) {a : Vec r}
    (ha : ∀ i, 0 < a i) {q : ℝ} (hq : 1 ≤ q) (hq' : q ≤ 2)
    (L : FullInfoLearner E Ω (fixedLpBody c U a q)) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : ℝ≥0) (hG : 0 < G) (b : ℝ) (hb : 0 ≤ b) :
    let W := (G:ℝ)*subexponentialWidth (fixedLpBody c U a q)
    L.HasHardSequence μ G b ((W + Real.sqrt (W*b))/64) := by
  let K := fixedLpBody c U a q
  let A := fixedOuterAxes a q
  let a₀ := fixedInnerAxes a q
  have hA : ∀ i, 0 < A i := fun i => mul_pos (fixedAxisScale_pos ha q) (Real.rpow_pos_of_pos (fixedAxisWeight_pos ha q i) _)
  have h₀ : ∀ i, 0 < a₀ i := fun i => mul_pos (fixedAxisScale_pos ha q) (Real.rpow_pos_of_pos (fixedAxisWeight_pos ha q i) _)
  have hin := fixedInner_subset c U ha hq
  have hell := fixedBody_subset_ellipsoid c U ha hq hq'
  have hout := hell.trans (ellipsoid_subset_box c U hA)
  have hn : K.Nonempty := ⟨_, hin (vertex_mem c U (fun i => (h₀ i).le) (fun _ => true))⟩
  have hqp : 0 < q := by linarith
  have hw : subexponentialWidth K ≤ 2*(∑ i, a₀ i) := by
    calc
      _ ≤ subexponentialWidth (ellipsoid c U A) := subexponentialWidth_mono K _ hn
        ((box_bounded c U A).subset (ellipsoid_subset_box c U hA)) hell
      _ ≤ 2*axesLength A := ellipsoid_width_le c U A hA
      _ = _ := by rw [fixedOuter_length ha hqp, fixedInner_sum ha hqp]
  obtain ⟨n, hn', hbudget, σ, hreg⟩ := exists_budget_sequence c U a₀ A h₀ G hG hin hout μ (L.asBlocks r) b hb
  apply L.of_coordinate μ G c U a₀ A hout
  refine ⟨n, hn', hbudget, σ, le_trans ?_ hreg⟩
  let W := (G:ℝ)*subexponentialWidth K
  let S := (G:ℝ)*∑ i, a₀ i
  have hW : W ≤ 2*S := (mul_le_mul_of_nonneg_left hw G.coe_nonneg).trans_eq (by dsimp [S]; ring)
  have hS : 0 ≤ S := mul_nonneg G.coe_nonneg (Finset.sum_nonneg fun i _ => (h₀ i).le)
  have hs : Real.sqrt (W*b) ≤ 2*Real.sqrt (S*b) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hS hb)]
    nlinarith [mul_le_mul_of_nonneg_right hW hb, mul_nonneg hS hb]
  change (W+Real.sqrt (W*b))/64 ≤ (S+Real.sqrt (S*b))/32
  linarith

omit [NeZero r] in
theorem fixedLpBody_box (c : E) (U : Axes r →ₗᵢ[ℝ] E) {a : Vec r} (ha : ∀ i, 0 < a i) :
    fixedLpBody c U a 1 = box c U a := by
  unfold fixedLpBody box
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, fixedUnitCoeffs, if_true]
  apply forall_congr'
  intro i
  rw [abs_div, abs_of_pos (ha i), div_le_one (ha i)]

omit [NeZero r] in
theorem fixedLpBody_euclidean (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Vec r) :
    fixedLpBody c U a 2 = ellipsoid c U a := by
  unfold fixedLpBody ellipsoid
  congr 1
  ext z
  norm_num [fixedUnitCoeffs, Real.rpow_two, sq_abs]


end Coordinate
end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

/-- Convert feasible dual coefficients into one fixed description for every comparator. -/
theorem description_of_dualCoefficients {d N : ℕ} (hN : 0 < N) {K : Set (Vec d)}
    (hne : K.Nonempty) (center : Vec d) (q : Matrix (Fin d) (Fin N) ℝ)
    (hq : ∀ j, norm₂ (fun i => q i j) ≤ 1) (β : Vec N) (hβ : ∀ j, 0 < β j)
    {c : ℝ} (hc : 0 ≤ c)
    (hrep : ∀ u ∈ K, ∃ y : Vec N, center + q.mulVec y = u ∧
      ∑ j, β j * expDual (|y j| / β j) ≤ c) :
    ∃ D : AdmissibleDescription K, D.N = N ∧ D.representationCost ≤ 4*c + 5*∑ j, β j := by
  classical
  let ℓ (j : Fin N) := Real.exp 2*(c+β j)
  have hl (j : Fin N) : 0 < ℓ j := mul_pos (Real.exp_pos _) (add_pos_of_nonneg_of_pos hc (hβ j))
  have hle (j : Fin N) : β j ≤ ℓ j := by
    calc
      β j ≤ c + β j := le_add_of_nonneg_left hc
      _ ≤ _ := le_mul_of_one_le_left (add_nonneg hc (hβ j).le)
        (Real.one_le_exp (by norm_num))
  have hth (j : Fin N) := exists_dyadicFloor_between (div_pos (hβ j) (hl j))
    ((div_le_one (hl j)).mpr (hle j))
  choose J hsmall hlarge using hth
  let A : Matrix (Fin d) (Fin N) ℝ := q * Matrix.diagonal ℓ
  have hcols (j : Fin N) : norm₂ (fun i => A i j) ≤ ℓ j := by
    have heq : (fun i => A i j) = ℓ j • (fun i => q i j) := by
      ext i
      simp [A, Matrix.mul_diagonal, mul_comm]
    rw [heq, norm₂_smul, abs_of_pos (hl j)]
    simpa using mul_le_mul_of_nonneg_left (hq j) (hl j).le
  have hcoeff (y : Vec N) (hy : ∑ j, β j * expDual (|y j|/β j) ≤ c) :
      (∀ j, |y j / ℓ j| ≤ 1) ∧ A.mulVec (fun j => y j/ℓ j) = q.mulVec y ∧
      coefficientCost ℓ (dyadicFloor J) (fun j => y j/ℓ j) ≤ 4*c + 5*∑ j, β j := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      rw [abs_div, abs_of_pos (hl j), div_le_one (hl j)]
      apply dualLength_bound hc (hβ j)
      exact (Finset.single_le_sum (f := fun i => β i * expDual (|y i| / β i))
        (fun i _ => mul_nonneg (hβ i).le expDual_nonneg) (Finset.mem_univ j)).trans hy
    · ext i
      simp only [A, Matrix.mulVec, dotProduct, Matrix.mul_diagonal, mul_assoc]
      apply Finset.sum_congr rfl
      intro j _
      have hcancel : ℓ j * (y j/ℓ j) = y j := by field_simp [(hl j).ne']
      rw [hcancel]
    · have hs (j : Fin N) := dualCoordinateCost (y := y j) (hl j) (dyadicFloor_pos J j) (hβ j)
        (by
          have h := (div_lt_iff₀ (hl j)).mp (show β j/ℓ j < 2*dyadicFloor J j by unfold dyadicFloor; linarith [hsmall j])
          linarith)
        (by
          have h := (le_div_iff₀ (hl j)).mp (hlarge j)
          change _ ≤ β j
          dsimp only [dyadicFloor]; linarith)
      have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hs j)
      unfold coefficientCost
      refine hsum.trans ?_
      calc
        _ = 5*(∑ j, β j) + 4*(∑ j, β j * expDual (|y j| / β j)) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun _ _ => by ring
        _ ≤ _ := by linarith
  let D : AdmissibleDescription K := {
    N := N, dimension_pos := hN, center := center, A := A, ℓ := ℓ, J := J,
    positive := hl, columns := hcols, covers := by
      intro u hu
      obtain ⟨y,he,hy⟩ := hrep u hu
      obtain ⟨hb,hA,_⟩ := hcoeff y hy
      exact ⟨_, hb, by rw [hA, he]⟩ }
  refine ⟨D,rfl, ?_⟩
  let : Nonempty K := hne.to_subtype
  apply ciSup_le
  intro u
  obtain ⟨y,he,hy⟩ := hrep u.val u.property
  obtain ⟨hb,hA,hcost⟩ := hcoeff y hy
  apply ((D.minimizingCoefficients_spec u).2.2 (fun j => y j / ℓ j) ?_).trans hcost
  exact ⟨⟨fun j => (abs_le.mp (hb j)).1, fun j => (abs_le.mp (hb j)).2⟩, by
    change center + A.mulVec _ = u.val
    rw [hA, he]⟩

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal InnerProductSpace
open MeasureTheory
namespace Curvature.Sparse

variable {d : ℕ}


def expAverage (z : Space d) : ℝ := (∑ i, Real.exp |z i|)/d

theorem expAverage_moment (hd : 0 < d) {μ : Measure (Space d)} (hμ : AdmissibleWidthLaw μ) :
    Integrable (expAverage (d := d)) μ ∧ (∫ z, expAverage z ∂μ) ≤ 2 := by
  have hex (i : Fin d) : Integrable (fun z : Space d => Real.exp |z i|) μ ∧
      (∫ z : Space d, Real.exp |z i| ∂μ) ≤ 2 := by
    let v := EuclideanSpace.single i (1:ℝ)
    have hv : ‖v‖ ≤ 1 := by simp [v]
    simpa only [v, EuclideanSpace.inner_single_left, map_one, one_mul] using
      And.intro (hμ.exp_integrable v hv) (hμ.exp_le v hv)
  refine ⟨(integrable_finsetSum _ (fun i _ => (hex i).1)).div_const _, ?_⟩
  unfold expAverage
  rw [integral_div, integral_finsetSum _ (fun i _ => (hex i).1), div_le_iff₀ (by exact_mod_cast hd)]
  simpa [mul_comm] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hex i).2)

theorem abs_le_log_add_average (hd : 0 < d) (z : Space d) (i : Fin d) :
    |z i| ≤ Real.log d + expAverage z := by
  have hd0 : 0 < (d:ℝ) := by exact_mod_cast hd
  have hs := Finset.single_le_sum (f := fun i : Fin d => Real.exp |z i|) (fun j _ => (Real.exp_pos _).le)
    (Finset.mem_univ i)
  have he := Real.add_one_le_exp (|z i| - Real.log d)
  rw [Real.exp_sub, Real.exp_log hd0] at he
  dsimp [expAverage]
  linarith [div_le_div_of_nonneg_right hs hd0.le]

private theorem coord_inner (x z : Space d) : ⟪x,z⟫_ℝ = ∑ i, x i*z i := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem bounded_of_l1 {K : Set (Space d)} {C : ℝ} (hs : ∀ x ∈ K, ∑ i, |x i| ≤ C) :
    Bornology.IsBounded K := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C,fun x hx => le_trans ?_ (hs x hx)⟩
  let B := EuclideanSpace.basisFun (Fin d) ℝ
  calc
    ‖x‖ = ‖∑ i, B.repr x i • B i‖ := by rw [B.sum_repr]
    _ ≤ _ := (norm_sum_le ..).trans_eq (by simp [B,norm_smul])

theorem width_log_bound {K : Set (Space d)} (hd : 2 ≤ d) (hne : K.Nonempty)
    {C : ℝ} (hC : 0 ≤ C) (hs : ∀ x ∈ K, ∑ i, |x i| ≤ C) :
    subexponentialWidth K ≤ 5*C*Real.log d := by
  let : Nonempty K := hne.to_subtype
  have hd0 : 0 < d := by omega
  have hd2 : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hlog : (1/2:ℝ) ≤ Real.log d := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    linarith [Real.log_le_log (by norm_num : (0:ℝ)<2) hd2]
  have hb (z : Space d) : widthSupport K z ≤ C*(Real.log d + expAverage z) := by
    apply ciSup_le
    intro w
    rw [coord_inner]
    calc
      _ ≤ ∑ i, |w.val i| *(Real.log d + expAverage z) := by
        apply Finset.sum_le_sum
        intro i _
        apply (le_abs_self _).trans
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_le_log_add_average hd0 z i) (abs_nonneg _)
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hs _ w.prop)
          ((abs_nonneg (z ⟨0,hd0⟩)).trans (abs_le_log_add_average hd0 z _))
  apply width_le_of_forall K hne
  intro μ hμ
  let := hμ.prob
  obtain ⟨hi,he⟩ := expAverage_moment hd0 hμ
  have hI : Integrable (fun z : Space d => Real.log d + expAverage z) μ := (integrable_const _).add hi
  have h := integral_mono (widthSupport_integrable _ hne (bounded_of_l1 hs) hμ) (hI.const_mul C) hb
  rw [integral_const_mul, integral_add (integrable_const _) hi, integral_const,probReal_univ,one_smul] at h
  nlinarith only [h,mul_le_mul_of_nonneg_left he hC,mul_le_mul_of_nonneg_left hlog hC]

theorem lp_l1_le {p q : ℝ} (hpq : p.HolderConjugate q) (x : Space d) (hx : x ∈ lpBall d p) :
    ∑ i, |x i| ≤ (d:ℝ)^(1/q) := by
  have h := Real.inner_le_Lp_mul_Lq Finset.univ (fun i => |x i|) (fun _ => (1:ℝ)) hpq
  simp only [mul_one,abs_abs,abs_one,Real.one_rpow,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at h
  have h1 := Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg (x i)) p))
    hx (show 0 ≤ 1/p from div_nonneg zero_le_one hpq.nonneg)
  simpa [Real.one_rpow] using h.trans (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (Nat.cast_nonneg d) _))

private theorem moment_point (q y : ℝ) (hq : 0 < q) (hy : 0 ≤ y) :
    y^q ≤ q^q*Real.exp y := by
  by_cases h : y=0
  · simp [h, Real.zero_rpow hq.ne']; positivity
  have hy' : 0 < y := hy.lt_of_ne' h
  rw [Real.rpow_def_of_pos hy',Real.rpow_def_of_pos hq,← Real.exp_add, Real.exp_le_exp]
  have hl := Real.log_le_sub_one_of_pos (div_pos hy' hq)
  rw [Real.log_div hy'.ne' hq.ne'] at hl
  have hs := mul_le_mul_of_nonneg_right hl hq.le
  field_simp [hq.ne'] at hs
  nlinarith

theorem lp_width_moment {p q : ℝ} (hpq : p.HolderConjugate q) (hd : 0 < d) :
    subexponentialWidth (lpBall d p) ≤ 2*(d:ℝ)^(1/q)*q := by
  have hq := hpq.symm.pos
  have hp := hpq.pos
  have hq1 := hpq.symm.lt
  have hI : 0 ≤ 1/q := by positivity
  let D := (d:ℝ)^(1/q)
  have hD : 0 < D := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hne : (lpBall d p).Nonempty := ⟨0,by simp [lpBall,Real.zero_rpow hp.ne']⟩
  let : Nonempty (lpBall d p) := hne.to_subtype
  have hb (z : Space d) : widthSupport (lpBall d p) z ≤ q*D*expAverage z := by
    have hsum : (∑ i, |z i|^q) ≤ q^q * ((d:ℝ)*expAverage z) := by
      dsimp [expAverage]
      rw [mul_div_cancel₀ _ (by exact_mod_cast (Nat.ne_of_gt hd)), Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => moment_point q _ hq (abs_nonneg _))
    have hz : 1 ≤ expAverage z := by
      apply (le_div_iff₀ (by exact_mod_cast hd)).mpr
      simpa using Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => Real.one_le_exp_iff.mpr (abs_nonneg (z i)))
    have hnorm := Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg (z i)) q)) hsum hI
    rw [Real.mul_rpow (Real.rpow_nonneg hq.le _) (mul_nonneg (Nat.cast_nonneg _) (by linarith)),
      ← Real.rpow_mul hq.le, mul_one_div_cancel hq.ne', Real.rpow_one, Real.mul_rpow (Nat.cast_nonneg _) (by linarith)] at hnorm
    apply ciSup_le
    intro w
    rw [coord_inner]
    have hh := Real.inner_le_Lp_mul_Lq Finset.univ (fun i => w.val i) (fun i => z i) hpq
    have h1 := Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg (w.val i)) p))
      w.prop (show 0 ≤ 1/p by positivity)
    rw [Real.one_rpow] at h1
    apply hh.trans
    calc
      _ ≤ 1*(∑ i, |z i|^q)^(1/q) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ q*(D*(expAverage z)^(1/q)) := (one_mul _).le.trans hnorm
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hz ((div_le_iff₀ hq).mpr (by linarith)))
          (mul_nonneg hq.le hD.le)
  apply width_le_of_forall _ hne
  intro μ hμ
  obtain ⟨hi, he⟩ := expAverage_moment hd hμ
  have h := integral_mono (widthSupport_integrable _ hne (bounded_of_l1 (lp_l1_le hpq)) hμ)
    (hi.const_mul (q*D)) hb
  rw [integral_const_mul] at h
  change _ ≤ 2*D*q
  nlinarith only [h,mul_le_mul_of_nonneg_left he (mul_nonneg hq.le hD.le)]

end Curvature.Sparse
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

/-- Separate a strict epigraph from an affine subspace to extend a linear minorant. -/
theorem extend_minorant {d N : ℕ} (A : Vec d →ₗ[ℝ] Vec N) (u : Vec d →ₗ[ℝ] ℝ)
    (F : Vec N → ℝ) (hcont : Continuous F) (hconv : ConvexOn ℝ Set.univ F)
    (hzero : F 0 = 0) {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ z, u z ≤ c + F (A z)) :
    ∃ g : Vec N →ₗ[ℝ] ℝ, (∀ z, g (A z) = u z) ∧ ∀ s, g s ≤ c + F s := by
  let S : Set (Vec N × ℝ) := {p | F p.1 < p.2}
  let V : Set (Vec N × ℝ) := Set.range fun z => (A z, u z - c)
  have hS : Convex ℝ S := by simpa [S] using hconv.convex_strict_epigraph
  have hV : Convex ℝ V := by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ a b _ _ hab
    refine ⟨a • x + b • y, ?_⟩
    ext1
    · simp
    · simp only [map_add, map_smul, smul_eq_mul, Prod.snd_add]
      change _ = a*(u x-c) + b*(u y-c)
      linear_combination c*hab
  have disj : Disjoint S V := by
    apply Set.disjoint_left.mpr
    rintro _ hx ⟨z,rfl⟩
    exact (not_lt.mpr (sub_le_iff_le_add'.mpr (hbound z))) hx
  obtain ⟨f,k,hlo,hhi⟩ := geometric_hahn_banach_open hS
    (isOpen_lt (hcont.comp continuous_fst) continuous_snd) hV disj
  let B := -f (0,1)
  have split (s : Vec N) (t : ℝ) : f (s,t) = f (s,0) - B*t := by
    rw [show (s,t) = (s,0) + t • ((0,1) : Vec N × ℝ) by simp, map_add, map_smul]
    simp [B, mul_comm]
  have hk : k ≤ B*c := by
    have h := hhi _ (Set.mem_range_self (f := fun z => (A z, u z-c)) 0)
    change k ≤ f (A 0, u 0-c) at h
    rw [split] at h
    simpa [show f ((0,0) : Vec N × ℝ) = 0 from map_zero f] using h
  have hB : 0 < B := by
    have h := hlo (0,1) (show F 0 < 1 by simp [hzero])
    by_contra! hneg
    have hkc : k ≤ 0 := hk.trans (mul_nonpos_of_nonpos_of_nonneg hneg hc)
    change -f (0,1) ≤ 0 at hneg
    linarith
  let g : Vec N →ₗ[ℝ] ℝ := B⁻¹ • (f.toLinearMap.comp (LinearMap.inl ℝ (Vec N) ℝ))
  have hg (s : Vec N) : B * g s = f (s,0) := by
    change B*(B⁻¹ * f (s,0)) = _
    rw [← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul]
  refine ⟨g, ?_, ?_⟩
  · intro z
    have hgraph (t : ℝ) := hhi _ (Set.mem_range_self (f := fun x => (A x, u x-c)) (t • z))
    have hmul (t : ℝ) : k ≤ B * (t*(g (A z) - u z) + c) := by
      have h := hgraph t
      rw [split, ← hg] at h
      simp only [map_smul, smul_eq_mul] at h
      linarith
    by_contra hne
    have hdiff := sub_ne_zero.mpr hne
    let t := (k/B - c - 1)/(g (A z) - u z)
    have ht : t * (g (A z) - u z) = k/B - c - 1 := div_mul_cancel₀ _ hdiff
    have h := hmul t
    rw [ht] at h
    have hcancel : B*(k/B) = k := by field_simp
    nlinarith
  · intro s
    by_contra! hbad
    let t := (g s - c + F s)/2
    have ht : F s < t := by dsimp [t]; linarith
    have h := hlo (s,t) ht
    rw [split, ← hg] at h
    have hin : c < g s-t := by dsimp [t]; linarith
    nlinarith [mul_lt_mul_of_pos_left hin hB]

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ} {K : Set (Vec d)}

private theorem adaptiveExcess_abs (g x y : Vec d) :
    |excess g x y| ≤ norm₂ g * norm₂ (x-y) := by
  have hn : norm₂ (-g) = norm₂ g := by simp [norm₂, neg_dotProduct, dotProduct_neg]
  refine abs_le.mpr ⟨?_, dotProduct_le_norm₂_mul g (x-y)⟩
  have h := dotProduct_le_norm₂_mul (-g) (x-y)
  rw [neg_dotProduct, hn] at h
  change - (norm₂ g*norm₂ (x-y)) ≤ dotProduct g (x-y)
  linarith only [h]

private theorem adaptivePotential_zero {M : ℝ} (hM : 0 < M) (k n : ℕ) :
    adaptivePotential M (fun _ => 0) k n = 0 := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [adaptivePotential, ih, binaryMix_same (adaptiveEta_pos hM k)]

private theorem adaptiveTolerance_sum_le (T : ℕ) :
    (∑ t ∈ Finset.range T, adaptiveMixTolerance t) ≤ 1 := by
  have h : ∀ n : ℕ, (∑ t ∈ Finset.range n, adaptiveMixTolerance t) ≤
      1 - 1 / ((n : ℝ)+1) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have hp : adaptiveMixTolerance n ≤ 1 / ((n : ℝ)+1) - 1 / ((n : ℝ)+2) := by
        unfold adaptiveMixTolerance
        calc
          _ ≤ 1 / (((n : ℝ)+1)*((n : ℝ)+2)) := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            rw [pow_two]
            exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = _ := by field_simp; ring
      rw [Finset.sum_range_succ, Nat.cast_succ, show (n : ℝ)+1+1=(n:ℝ)+2 by ring]
      linarith only [ih, hp]
  exact (h T).trans (sub_le_self _ (by positivity))

namespace AdaptiveBase

variable (B : AdaptiveBase K) (hcv : Convex ℝ K) {M G : ℝ}
  (P : AdaptiveWeightRule M) (g : ℕ → Vec d)

local notation "s" => B.adaptiveStateAfter hcv P G g
local notation "a" => B.adaptiveDifference hcv P G
local notation "w" => B.adaptiveRoundPlay hcv P G
local notation "b" => B.adaptiveBasePlay G

private theorem adaptiveExcess_bound (hg : ∀ t, norm₂ (g t) ≤ G)
    (hspread : ∀ u v : K, G * norm₂ (u.val-v.val) ≤ M) (t : ℕ) (u v : K) :
    |excess (g t) u.val v.val| ≤ M :=
  (adaptiveExcess_abs ..).trans ((mul_le_mul_of_nonneg_right (hg t) (norm₂_nonneg _)).trans
    (hspread u v))

theorem adaptiveRoot_bound (hM : 0 < M) (hg : ∀ t, norm₂ (g t) ≤ G)
    (hspread : ∀ u v : K, G * norm₂ (u.val-v.val) ≤ M) (T n : ℕ)
    (hdepth : ∀ t < T, adaptiveAwake t+1 ≤ n) :
    (2/3)*(∑ t ∈ Finset.range T, B.adaptiveMixCredit hcv P G (s t) t (g t)) -
      (7/3)*M*(∑ t ∈ Finset.range T, adaptiveMixTolerance t) ≤
      adaptivePotential M (s T).loss 0 n := by
  induction T with
  | zero =>
    change _ ≤ adaptivePotential M (fun _ => 0) 0 n
    simp [adaptivePotential_zero hM]
  | succ T ih =>
    have hprev := ih fun t ht => hdepth t (by omega)
    let localDepth := adaptiveAwake T+1
    let L := (s T).loss
    let L' := (s (T+1)).loss
    let Δ := fun i => adaptiveUpdate i (a (s T) T (g T) i)
    let p := P.prob L T
    have hdiff (j i : ℕ) : |a (s j) j (g j) i| ≤ M := by
      unfold adaptiveDifference
      split
      · exact adaptiveExcess_bound g hg hspread j _ _
      · simpa only [abs_zero] using hM.le
    have hLrange (i : ℕ) : |L i| ≤ 2*M*T := by
      change |(s T).loss i| ≤ _
      rw [B.adaptiveStateAfter_loss_eq hcv P G g i T]
      calc
        _ ≤ ∑ j ∈ Finset.range T, |adaptiveUpdate i (a (s j) j (g j) i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ Finset.range T, 2*M := Finset.sum_le_sum fun j _ =>
          (abs_adaptiveUpdate_le i _).trans (mul_le_mul_of_nonneg_left (hdiff j i) (by norm_num))
        _ = _ := by simp [mul_comm]
    have hdormant (i : ℕ) (hi : i ≥ localDepth) : T+1 ≤ adaptiveStart i := by
      have hi' : ¬i ≤ adaptiveAwake T := by dsimp [localDepth] at hi; omega
      have : ¬adaptiveStart i ≤ T := fun h => hi' ((adaptiveAwake_iff i T).mpr h)
      omega
    have hL (i : ℕ) (hi : i ≥ 0+localDepth) : L i = 0 :=
      B.adaptiveStateAfter_loss_dormant hcv P G g i T (by
        have := hdormant i (by omega)
        omega)
    have hround := adaptiveOneRoundGap hM (show 0 ≤ adaptiveMixTolerance T by
      unfold adaptiveMixTolerance; positivity) L (a (s T) T (g T)) p
      0 localDepth (hdiff T) (fun i _ => P.nonnegative L T i)
      (P.approximation L T hLrange (hL localDepth (by omega))) (B.adaptiveDifference_zero_mean hcv P G (s T) T (g T))
    have hstep : (2/3)*B.adaptiveMixCredit hcv P G (s T) T (g T) -
        (7/3)*M*adaptiveMixTolerance T ≤ adaptiveIncrement M L Δ 0 localDepth :=
      hround.2
    have hL' (i : ℕ) (hi : i ≥ 0+localDepth) : L' i = 0 :=
      B.adaptiveStateAfter_loss_dormant hcv P G g i (T+1) (hdormant i (by omega))
    have hn : localDepth + (n-localDepth) = n :=
      Nat.add_sub_of_le (hdepth T (by omega))
    have hb := adaptivePotential_extend_zero hM L 0 localDepth hL (n-localDepth)
    have ha := adaptivePotential_extend_zero hM L' 0 localDepth hL' (n-localDepth)
    rw [hn] at ha hb
    change _ ≤ adaptivePotential M L' 0 n
    change _ ≤ adaptivePotential M L 0 n at hprev
    change _ ≤ adaptivePotential M L' 0 localDepth - adaptivePotential M L 0 localDepth at hstep
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith only [ha,hb,hprev,hstep]

theorem adaptiveAwake_mix_comparison (hM : 0 < M) (hg : ∀ t, norm₂ (g t) ≤ G)
    (hspread : ∀ u v : K, G * norm₂ (u.val-v.val) ≤ M) (T i : ℕ) (hT : 2^i ≤ T) :
    (∑ t ∈ Finset.Ico (adaptiveStart i) T, adaptiveLoss (adaptiveRate i/2) (a (s t) t (g t) i)) ≤
      256*M*Real.log 2 / adaptiveRate i +(7/3)*M := by
  have hstart := (adaptiveStart_lt_iff i T).mpr hT
  let n := adaptiveAwake (T-1)+1
  have hn : i ≤ n := by
    have hi : adaptiveStart i ≤ T-1 := by omega
    exact ((adaptiveAwake_iff i (T-1)).mpr hi).trans (Nat.le_succ _)
  have hroot := B.adaptiveRoot_bound hcv P g hM hg hspread T n
    (fun t ht => Nat.succ_le_succ (adaptiveAwake_mono (by omega)))
  have hbudget := adaptiveTolerance_sum_le T
  have hU : 0 ≤ (2/3) * (∑ t ∈ Finset.range T, B.adaptiveMixCredit hcv P G (s t) t (g t)) :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun t _ =>
      B.adaptiveMixCredit_nonneg hcv P G (s t) t (g t))
  have hneg := mul_le_of_le_one_right (show 0 ≤ (7/3:ℝ)*M by positivity) hbudget
  have hpath := adaptivePotential_path hM (s T).loss 0 n i hn
  rw [Nat.zero_add] at hpath
  have hpenalty :
      Real.log 2 * (2/adaptiveEta M i - 1/adaptiveEta M 0) ≤
        256*M*Real.log 2 / adaptiveRate i := calc
    _ ≤ Real.log 2 * (2/adaptiveEta M i) :=
      mul_le_mul_of_nonneg_left
        (sub_le_self _ (div_nonneg (by norm_num) (adaptiveEta_pos hM 0).le))
        (Real.log_nonneg (by norm_num))
    _ = _ := by
      unfold adaptiveEta
      field_simp
      ring
  have hbefore : (∑ t ∈ Finset.range (adaptiveStart i),
      adaptiveLoss (adaptiveRate i/2) (a (s t) t (g t) i)) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    have hi : ¬i ≤ adaptiveAwake t := fun h =>
      (Nat.not_le_of_gt (Finset.mem_range.mp ht)) ((adaptiveAwake_iff i t).mp h)
    simp [adaptiveDifference, hi, adaptiveLoss]
  have hsum := B.adaptiveStateAfter_loss_eq hcv P G g i T
  simp only [adaptiveUpdate, Finset.sum_neg_distrib] at hsum
  rw [Finset.sum_Ico_eq_sub _ hstart.le, hbefore, sub_zero]
  linarith only [hpath,hpenalty,hroot,hneg,hsum,hU]

theorem adaptiveAwake_base_comparison (hG : 0 < G) (hg : ∀ t, norm₂ (g t) ≤ G)
    (T i : ℕ) (u : K) :
    let r := fun t => excess (g t) (w (s t) t).val u.val
    (∑ t ∈ Finset.Ico (adaptiveStart i) T,
      adaptiveLoss (adaptiveRate i/2)
        (adaptiveScale (adaptiveRate i/2) (a (s t) t (g t) i) * (r t-a (s t) t (g t) i))) ≤
          G * B.cost / adaptiveRate i := by
  let input := fun j => (s T).feedback i (j+adaptiveStart i)
  have hinput : ∀ j, norm₂ (input j) ≤ 2*G :=
    fun j => B.adaptiveStateAfter_feedback_norm hcv P G g hG.le hg i _ _
  have hlearner := B.playedRegret (show 0 < 2*G by positivity)
    (adaptiveRate_pos i) ((adaptiveRate_le i).trans (by norm_num)) input hinput u (T-adaptiveStart i)
  let r := fun t => excess (g t) (w (s t) t).val u.val
  let rbase := fun j => excess (input j) (B.play (2*G) (adaptiveRate i) input j).val u.val
  have hconvert : ∀ t ∈ Finset.Ico (adaptiveStart i) T,
      adaptiveScale (adaptiveRate i/2) (a (s t) t (g t) i) * (r t-a (s t) t (g t) i) =
        rbase (t-adaptiveStart i) := by
    intro t ht
    obtain ⟨hlo, hupp⟩ := Finset.mem_Ico.mp ht
    have hawake := (adaptiveAwake_iff i t).mpr hlo
    have hf := B.adaptiveStateAfter_feedback_current hcv P G g i t T hupp hawake
    have hbase := B.adaptiveBasePlay_terminal hcv P G g i t T hupp.le
    have hinput' : input (t-adaptiveStart i) =
        adaptiveScale (adaptiveRate i/2) (a (s t) t (g t) i) • g t := by
      simpa only [input, Nat.sub_add_cancel hlo] using hf
    have hdiff : r t-a (s t) t (g t) i = excess (g t) (b (s t) t i).val u.val := by
      simp only [r,adaptiveDifference,if_pos hawake,excess,dotProduct_sub]
      ring
    dsimp only [rbase]
    rw [hinput', ← hbase, hdiff, excess, excess, smul_dotProduct, smul_eq_mul]
  change (∑ t ∈ Finset.Ico (adaptiveStart i) T, adaptiveLoss (adaptiveRate i/2) _) ≤ _
  calc
    _ = ∑ t ∈ Finset.Ico (adaptiveStart i) T, adaptiveLoss (adaptiveRate i/2) (rbase (t-adaptiveStart i)) :=
      Finset.sum_congr rfl fun t ht => congrArg (adaptiveLoss (adaptiveRate i/2)) (hconvert t ht)
    _ = ∑ j ∈ Finset.range (T-adaptiveStart i), adaptiveLoss (adaptiveRate i/2) (rbase j) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp
    _ ≤ _ := by
      change 2*(∑ j ∈ Finset.range (T-adaptiveStart i), rbase j) -
        adaptiveRate i*(∑ j ∈ Finset.range (T-adaptiveStart i), |rbase j|) ≤ _ at hlearner
      simp only [adaptiveLoss, Finset.sum_sub_distrib, ← Finset.mul_sum, div_eq_mul_inv] at hlearner ⊢
      linarith only [hlearner]

/-- Linearized regret for the recursive mixture with the specified weight tolerance. -/
theorem adaptiveMixture (hM : 0 < M) (hG : 0 < G) (hg : ∀ t, norm₂ (g t) ≤ G)
    (hspread : ∀ u v : K, G * norm₂ (u.val-v.val) ≤ M) (T : ℕ) (hT : 0 < T) (u : K) :
    let r := fun t => excess (g t) (B.adaptivePlay hcv P G g t).val u.val
    let C := G*B.cost + 257*M
    (∑ t ∈ Finset.range T, r t) ≤ 24*(C+Real.sqrt (C * adaptiveNegative T r)) := by
  let r := fun t => excess (g t) (w (s t) t).val u.val
  let C₀ := G*B.cost+M
  let C := G*B.cost+257*M
  have hGC := mul_nonneg hG.le B.cost_nonneg
  have hC : 0 < C := by dsimp only [C]; positivity
  have hMC : M ≤ C := by dsimp only [C]; linarith only [hGC,hM]
  have hr (t : ℕ) : |r t| ≤ M :=
    adaptiveExcess_bound g hg hspread t _ u
  change (∑ t ∈ Finset.range T, r t) ≤ 24*(C+Real.sqrt (C*adaptiveNegative T r))
  apply adaptiveRegret_of_masterRatewise hC hMC hT (adaptiveNegative_nonneg T r)
    (adaptiveNegative_le M hM.le T r fun t _ => hr t)
  intro i hi
  apply masterRatewise_of_signed hC.le
  have hmix := B.adaptiveAwake_mix_comparison hcv P g hM hg hspread T i hi
  have hbase := B.adaptiveAwake_base_comparison hcv P g hG hg T i u
  have hbase' := hbase.trans (show G*B.cost / adaptiveRate i ≤
      2*C₀ / adaptiveRate i from div_le_div_of_nonneg_right
      (by dsimp only [C₀]; linarith only [hGC,hM]) (adaptiveRate_pos i).le)
  have h := adaptiveMasterSigned_of_awake T i hi M C₀ hM.le r
    (fun t => a (s t) t (g t) i) (fun t _ => (le_abs_self _).trans (hr t)) hmix hbase'
  exact h.trans_eq (by dsimp [C,C₀]; ring)

end AdaptiveBase
end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory
namespace Curvature.Sparse

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

private theorem compare_scale {K : Set (Space d)} {L : FullInfoLearner (Space d) Ω K}
    {μ : Measure Ω} {G : ℝ≥0} {b W S : ℝ} (hb : 0 ≤ b) (hS : 0 ≤ S) (hW : W ≤ 160*S)
    (h : L.HasHardSequence μ G b ((S + Real.sqrt (S*b))/128)) :
    L.HasHardSequence μ G b ((W + Real.sqrt (W*b))/20480) := by
  obtain ⟨T,hT,f,hf,hc,hi,hr⟩ := h
  refine ⟨T,hT,f,hf,hc,hi,le_trans ?_ hr⟩
  have hs : Real.sqrt (W*b) ≤ 160*Real.sqrt (S*b) := by
    apply Real.sqrt_le_iff.mpr ⟨by positivity,?_⟩
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hS hb)]
    nlinarith only [mul_le_mul_of_nonneg_right hW hb,mul_nonneg hS hb]
  linarith

theorem face_lp {p : ℝ} (hp : 0 < p) {k : ℕ} (hk : 0 < k) (B : Finset (Fin d)) (hB : B.card=k) :
    faceVertex ((k:ℝ)^(-1/p)) B ∈ lpBall d p := by
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast hk
  let a := (k:ℝ)^(-1/p)
  have ha : 0 < a := Real.rpow_pos_of_pos hk0 _
  change (∑ i, |faceVertex a B i|^p) ≤ 1
  have h (i : Fin d) : |faceVertex a B i|^p = if i ∈ B then a^p else 0 := by
    by_cases hi : i ∈ B <;> simp [faceVertex,hi,abs_of_pos ha,Real.zero_rpow hp.ne']
  simp_rw [h]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
    nsmul_eq_mul, hB]
  dsimp [a]
  rw [← Real.rpow_mul hk0.le, div_mul_cancel₀ _ hp.ne', Real.rpow_neg_one, mul_inv_cancel₀ hk0.ne']

theorem lp_width_lower (hd : 2 ≤ d) {p q : ℝ} (hpq : p.HolderConjugate q)
    (L : FullInfoLearner (Space d) Ω (lpBall d p)) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : ℝ≥0) (hG : 0 < G) (b : ℝ) (hb : 0 ≤ b) :
    let W := G * subexponentialWidth (lpBall d p)
    L.HasHardSequence μ G b ((W + Real.sqrt (W*b))/20480) := by
  have hd0 : 0 < d := by omega
  have hq := hpq.symm.pos
  obtain ⟨k,m,hk,hm,hkm,hopt⟩ := exists_blocks hd hpq.symm.lt.le
  let a := (k:ℝ)^(-1/p)
  let D := (d:ℝ)^(1/q)
  have hD : 0 < D := Real.rpow_pos_of_pos (by exact_mod_cast hd0) _
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast hk
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hlog := Real.log_nonneg (show 1 ≤ (m:ℝ) by linarith)
  have ha : 0 < a := Real.rpow_pos_of_pos hk0 _
  have hmass : (k:ℝ)*a = (k:ℝ)^(1/q) := by
    calc
      _ = (k:ℝ)^((1:ℝ)+(-1/p)) := by rw [Real.rpow_add hk0, Real.rpow_one]
      _ = _ := by congr 1; rw [neg_div]; linarith only [show 1/p+1/q = (1:ℝ) by simpa only [one_div] using hpq.inv_add_inv_eq_one]
  have hne : (lpBall d p).Nonempty := ⟨0,by simp [lpBall,Real.zero_rpow hpq.pos.ne']⟩
  have hs := block_budget L μ hk hm hkm a ha G hG b hb (bounded_of_l1 (lp_l1_le hpq))
    (fun B hB => face_lp hpq.pos hk B hB)
  let S := (G:ℝ)*(k*a)*Real.log m
  apply compare_scale (S := S) hb (by dsimp [S]; positivity) _ hs
  have hwidth : subexponentialWidth (lpBall d p) ≤ 5*D*(min q (Real.log ((d:ℝ)+1))) := by
    by_cases h : q ≤ Real.log ((d:ℝ)+1)
    · rw [min_eq_left h]
      have hqwidth := lp_width_moment hpq hd0
      change _ ≤ 2*D*q at hqwidth
      nlinarith only [hqwidth,mul_nonneg hD.le hq.le]
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h))]
      have hl := width_log_bound hd hne hD.le (lp_l1_le hpq)
      exact hl.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by exact_mod_cast hd0) (by linarith))
        (mul_nonneg (by norm_num) hD.le))
  have hval : subexponentialWidth (lpBall d p) ≤ 160*(((k:ℝ)*a)*Real.log m) := by
    rw [hmass]
    change D*min q (Real.log ((d:ℝ)+1)) ≤ _ at hopt
    linarith only [hwidth,hopt]
  dsimp [S]
  nlinarith only [mul_le_mul_of_nonneg_left hval G.coe_nonneg]

private theorem lower_l1_domain {K : Set (Space d)} (hd : 2 ≤ d) (hne : K.Nonempty)
    (h1 : ∀ x ∈ K, ∑ i, |x i| ≤ 1)
    (hvert : ∀ B : Finset (Fin d), B.card=1 → faceVertex 1 B ∈ K)
    (L : FullInfoLearner (Space d) Ω K) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : ℝ≥0) (hG : 0 < G) (b : ℝ) (hb : 0 ≤ b) :
    let W := G * subexponentialWidth K
    L.HasHardSequence μ G b ((W + Real.sqrt (W*b))/20480) := by
  let S := (G:ℝ)*Real.log d
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hlog := Real.log_nonneg (show 1 ≤ (d:ℝ) by linarith)
  have hs := block_budget (k := 1) (m := d) L μ (by decide) hd (by simp) 1 (by norm_num)
    G hG b hb (bounded_of_l1 h1) hvert
  simp only [Nat.cast_one,mul_one] at hs
  have hw := width_log_bound hd hne zero_le_one h1
  rw [mul_one] at hw
  apply compare_scale (S := S) hb (mul_nonneg G.coe_nonneg hlog) _ hs
  dsimp [S]
  nlinarith only [mul_le_mul_of_nonneg_left hw G.coe_nonneg,mul_nonneg G.coe_nonneg hlog]

theorem l1_width_lower (hd : 2 ≤ d) (L : FullInfoLearner (Space d) Ω (lpBall d 1))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : ℝ≥0) (hG : 0 < G) (b : ℝ) (hb : 0 ≤ b) :
    let W := G * subexponentialWidth (lpBall d 1)
    L.HasHardSequence μ G b ((W + Real.sqrt (W*b))/20480) := by
  apply lower_l1_domain hd ⟨0,by simp [lpBall]⟩ (fun x hx => by simpa [lpBall] using hx)
    (fun B hB => ?_) L μ G hG b hb
  simpa using face_lp (p := 1) (k := 1) zero_lt_one (by decide) B hB

theorem simplex_width_lower (hd : 2 ≤ d) (L : FullInfoLearner (Space d) Ω (simplex d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : ℝ≥0) (hG : 0 < G) (b : ℝ) (hb : 0 ≤ b) :
    let W := G * subexponentialWidth (simplex d)
    L.HasHardSequence μ G b ((W + Real.sqrt (W*b))/20480) := by
  have hvert (B : Finset (Fin d)) (hB : B.card = 1) : faceVertex 1 B ∈ simplex d := by
    refine ⟨fun i => ?_, ?_⟩
    · change 0 ≤ if i ∈ B then (1:ℝ) else 0
      split_ifs <;> norm_num
    · simpa [hB] using mass_faceVertex (Finset.subset_univ B) (1:ℝ)
  have hd0 : 0 < d := by omega
  have hne : (simplex d).Nonempty := ⟨_,hvert {⟨0,hd0⟩} (by simp)⟩
  apply lower_l1_domain hd hne _ hvert L μ G hG b hb
  intro x hx
  change (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 at hx
  simpa only [abs_of_nonneg (hx.1 _)] using hx.2.le

theorem lpBall_one_eq (p : ℝ) (hp : 0 < p) :
    lpBall 1 p = Coordinate.box (0 : Space 1) (LinearIsometry.id : Space 1 →ₗᵢ[ℝ] Space 1) (fun _ => 1) := by
  ext x
  have h : |x 0|^p ≤ (1:ℝ)^p ↔ |x 0| ≤ 1 := Real.rpow_le_rpow_iff (abs_nonneg _) zero_le_one hp
  simpa [lpBall, Coordinate.box, Coordinate.position] using h

theorem unitLp_width_lower (hd : 0 < d) (p : ℝ) (hp : 1 ≤ p)
    (L : FullInfoLearner (Space d) Ω (lpBall d p)) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : ℝ≥0) (hG : 0 < G) (b : ℝ) (hb : 0 ≤ b) :
    let W := G * subexponentialWidth (lpBall d p)
    L.HasHardSequence μ G b ((W + Real.sqrt (W*b))/20480) := by
  rcases eq_or_lt_of_le (show 1 ≤ d from hd) with h | hd2
  · subst d
    have hx := lpBall_one_eq p (by linarith)
    have hh := coordinateBudgetLower (0 : Space 1) (LinearIsometry.id : Space 1 →ₗᵢ[ℝ] Space 1) (fun _ => 1)
      (fun _ => zero_lt_one) (Or.inl hx) L μ G hG b hb
    obtain ⟨T,hT,f,hf,hc,hi,hr⟩ := hh
    have hne : (lpBall 1 p).Nonempty := ⟨0,by simp [lpBall, Real.zero_rpow (show p ≠ 0 by linarith)]⟩
    have hbdd : Bornology.IsBounded (lpBall 1 p) := by rw [hx]; apply Coordinate.box_bounded
    have hw : 0 ≤ subexponentialWidth (lpBall 1 p) :=
      le_csSup (widthValues_bddAbove _ hne hbdd) (zero_mem_widthValues _ hne)
    refine ⟨T,hT,f,hf,hc,hi,le_trans ?_ hr⟩
    linarith [mul_nonneg G.coe_nonneg hw, Real.sqrt_nonneg ((G:ℝ)*subexponentialWidth (lpBall 1 p)*b)]
  · rcases eq_or_lt_of_le hp with rfl | h
    · exact l1_width_lower hd2 L μ G hG b hb
    · exact lp_width_lower hd2 ((Real.holderConjugate_iff_eq_conjExponent h).mpr rfl) L μ G hG b hb

end Curvature.Sparse
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Curvature
variable {d N : ℕ} [NeZero N]

abbrev CanonicalSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)


end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

/-- Supporting prices for finite moment constraints. The zero observation supplies strict feasibility. -/
theorem moment_prices {N : ℕ} {P : Set (Vec N × ℝ)} (hP : Convex ℝ P)
    (h0 : (0,0) ∈ P) {C : ℝ} (hC : 0 ≤ C)
    (bound : ∀ p ∈ P, (∀ i, p.1 i < 1) → p.2 ≤ C) :
    ∃ c : ℝ, ∃ β : Vec N, 0 ≤ c ∧ (∀ i, 0 ≤ β i) ∧ c + ∑ i, β i = C ∧
      ∀ p ∈ P, p.2 ≤ c + ∑ i, β i * p.1 i := by
  classical
  let U : Set (Vec N × ℝ) := {p | (∀ i, p.1 i < 1) ∧ C < p.2}
  have hop : IsOpen U := by
    apply IsOpen.inter _ (isOpen_lt continuous_const continuous_snd)
    change IsOpen {p : Vec N × ℝ | ∀ i, p.1 i < 1}
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt ((continuous_apply i).comp continuous_fst) continuous_const
  have hconv : Convex ℝ U := by
    rintro x hx y hy a b ha hb hab
    have aff {v w M : ℝ} (hv : v < M) (hw : w < M) : a*v + b*w < M := by
      calc
        _ ≤ a * max v w + b * max v w :=
          add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
            (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
        _ = max v w := by rw [← add_mul, hab, one_mul]
        _ < M := max_lt hv hw
    constructor
    · intro i; exact aff (hx.1 i) (hy.1 i)
    · have h := aff (neg_lt_neg hx.2) (neg_lt_neg hy.2)
      change C < a*x.2 + b*y.2; linarith
  have hdisj : Disjoint U P := Set.disjoint_left.mpr fun p hu hp => hu.2.not_ge (bound p hp hu.1)
  obtain ⟨f,k,hlo,hhi⟩ := geometric_hahn_banach_open hconv hop hP hdisj
  let α (i : Fin N) := f (Pi.single i 1,0)
  let B := -f (0,1)
  have split (s : Vec N) (t : ℝ) : f (s,t) = (∑ i, α i*s i) - B*t := by
    let g := f.toLinearMap.comp (LinearMap.inl ℝ (Vec N) ℝ)
    have hlin : g s = ∑ i, α i * s i := by
      conv_lhs => rw [pi_eq_sum_univ' s, map_sum]
      simp [g, α, mul_comm]
    rw [show (s,t) = (s,0) + t • ((0,1) : Vec N × ℝ) by simp, map_add, map_smul]
    change g s + t * f (0,1) = _
    rw [hlin]
    dsimp [B]; ring
  have hk : k ≤ 0 := by
    simpa only [show ((0:Vec N),(0:ℝ)) = 0 from rfl, map_zero] using hhi (0,0) h0
  have ha (i : Fin N) : 0 ≤ α i := by
    by_contra! hneg
    let t := (|k| + |B*(C+1)| + 1)/(-α i)
    have ht : 0 ≤ t := div_nonneg (by positivity) (by linarith)
    let s : Vec N := Pi.single i (-t)
    have hu : (s,C+1) ∈ U := by
      refine ⟨fun j => ?_, by dsimp; linarith⟩
      by_cases he : j = i
      · subst j; simpa [s] using (show -t < 1 by linarith)
      · simp [s, Pi.single_eq_of_ne he]
    have h := hlo _ hu
    rw [split] at h
    change dotProduct α (Pi.single i (-t)) - B*(C+1) < k at h
    rw [dotProduct_single] at h
    have hcancel : (-α i)*t = |k| + |B*(C+1)| + 1 := by dsimp [t]; field_simp [hneg.ne]
    linarith [le_abs_self k, le_abs_self (B*(C+1))]
  have hB : 0 < B := by
    have h := hlo (0,C+1) (show (0,C+1) ∈ U from ⟨by simp, by dsimp; linarith⟩)
    rw [split] at h
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_sub] at h
    by_contra! hn
    linarith [mul_nonpos_of_nonpos_of_nonneg hn (show 0 ≤ C+1 by linarith)]
  let β (i : Fin N) := α i/B
  let c := C - ∑ i, β i
  have hmajor (p : Vec N × ℝ) (hp : p ∈ P) : p.2 ≤ c + ∑ i, β i * p.1 i := by
    have hs : ∑ i, α i - B*C ≤ k := by
      let D := (∑ i, α i)+B
      have hD : 0 < D := add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _ => ha i) hB
      by_contra! hbad
      let δ := ((∑ i, α i) - B*C - k)/(2*D)
      have hδ : 0 < δ := div_pos (by linarith) (by positivity)
      have h := hlo ((fun _ => 1-δ),C+δ) (show ((fun _ => 1-δ),C+δ) ∈ U by
        refine ⟨fun _ => ?_,?_⟩ <;> dsimp <;> linarith)
      rw [split, ← Finset.sum_mul] at h
      have hd : 2 * D * δ = (∑ i, α i) - B*C - k := by dsimp [δ]; field_simp
      dsimp only [D] at hd
      nlinarith
    have h := hs.trans (hhi p hp)
    rw [show f p = _ from split p.1 p.2] at h
    have hsum (s : Vec N) : B*(∑ i, β i*s i) = ∑ i, α i*s i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by dsimp [β]; field_simp
    have hone := hsum (fun _ => 1)
    simp only [mul_one] at hone
    rw [← hsum p.1, ← hone] at h
    dsimp only [c]
    exact le_of_mul_le_mul_left (by linarith : B*p.2 ≤ B*(_+_)) hB
  refine ⟨c,β, ?_, fun i => div_nonneg (ha i) hB.le, by dsimp [c]; ring, hmajor⟩
  simpa using hmajor (0,0) h0

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

def momentPenalty (s : ℝ) : ℝ := Real.exp |s| - 1

theorem penalty_convex {x y a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    momentPenalty (a*x+b*y) ≤ a * momentPenalty x + b * momentPenalty y := by
  have h := abs_add_le (a*x) (b*y)
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at h
  have hj := convexOn_exp.2 (Set.mem_univ |x|) (Set.mem_univ |y|) ha hb hab
  simp only [smul_eq_mul] at hj
  unfold momentPenalty
  linarith [Real.exp_le_exp.mpr h]

private theorem conjugate_attained (v : ℝ) :
    ∃ s : ℝ, expDual |v| = v*s - momentPenalty s := by
  by_cases h : |v| ≤ 1
  · exact ⟨0, by simp [expDual, h, momentPenalty]⟩
  · have hl := Real.log_pos (lt_of_not_ge h)
    have hp : 0 < |v| := zero_lt_one.trans (lt_of_not_ge h)
    rcases le_or_gt 0 v with hv | hv
    · refine ⟨Real.log |v|, ?_⟩
      simp only [expDual, if_neg h, momentPenalty, abs_of_nonneg hl.le, Real.exp_log hp]
      rw [abs_of_nonneg hv]
      ring
    · refine ⟨-Real.log |v|, ?_⟩
      simp only [expDual, if_neg h, momentPenalty, abs_neg, abs_of_nonneg hl.le, Real.exp_log hp]
      rw [abs_of_neg hv]
      ring

/-- Coefficients follow by separating the exponential penalty from the linear support bound. -/
theorem dualCoefficients_of_majorant {d N : ℕ} (q : Matrix (Fin d) (Fin N) ℝ)
    (β : Vec N) (hβ : ∀ j, 0 < β j) {c : ℝ} (hc : 0 ≤ c) (u : Vec d)
    (h : ∀ z, dotProduct u z ≤ c + ∑ j, β j * momentPenalty (q.transpose.mulVec z j)) :
    ∃ y : Vec N, q.mulVec y = u ∧ ∑ j, β j * expDual (|y j| / β j) ≤ c := by
  classical
  let F (s : Vec N) := ∑ j, β j * momentPenalty (s j)
  have hcon : ConvexOn ℝ Set.univ F := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    change (∑ j, β j * momentPenalty (a*x j+b*y j)) ≤
      a * (∑ j, β j * momentPenalty (x j)) + b * (∑ j, β j * momentPenalty (y j))
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have h1 := mul_le_mul_of_nonneg_left (penalty_convex (x := x j) (y := y j) ha hb hab) (hβ j).le
    linarith
  obtain ⟨g,hg,hF⟩ := extend_minorant q.transpose.mulVecLin (dotProductBilin ℝ ℝ u) F
    (by dsimp [F,momentPenalty]; fun_prop) hcon (by simp [F,momentPenalty]) hc h
  let y (j : Fin N) := g (Pi.single j 1)
  have hdot (s : Vec N) : g s = dotProduct y s := by
    conv_lhs => rw [pi_eq_sum_univ' s, map_sum]
    simp [y, dotProduct, mul_comm]
  refine ⟨y, ?_, ?_⟩
  · ext i
    have hz := hg (Pi.single i 1)
    rw [hdot] at hz
    change dotProduct y (q.transpose.mulVec (Pi.single i 1)) = dotProduct u (Pi.single i 1) at hz
    rw [Matrix.dotProduct_transpose_mulVec, single_one_dotProduct, dotProduct_single_one] at hz
    exact hz
  · choose s hs using (fun j => conjugate_attained (y j / β j))
    have h1 := hF s
    rw [hdot] at h1
    have he (j : Fin N) : β j * expDual (|y j| / β j) = y j * s j - β j * momentPenalty (s j) := by
      have h2 := hs j
      rw [abs_div, abs_of_pos (hβ j)] at h2
      rw [h2]
      field_simp [(hβ j).ne']
    simp_rw [he]
    rw [Finset.sum_sub_distrib]
    exact sub_le_iff_le_add.mpr h1

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ} {K : Set (Vec d)}


theorem adaptiveWidthConstant_pos : 0 < adaptiveWidthConstant := by
  unfold adaptiveWidthConstant adaptiveBaseWidthFactor
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- The known-width linearized regret bound for any certified initialization. -/
theorem adaptiveWidth_givenBase (B : AdaptiveBase K) (hc : IsCompact K) (hcv : Convex ℝ K)
    (hcost : B.cost ≤ adaptiveBaseWidthFactor*coordinateWidth K) {G W : ℝ} (hG : 0 < G) (hW : 0 < W)
    (hwidth : coordinateWidth K ≤ W) (P : AdaptiveWeightRule (adaptiveWidthScale G W))
    (g : ℕ → Vec d) (hg : ∀ t, norm₂ (g t) ≤ G) (T : ℕ) (hT : 0 < T) (u : K) :
    let r := fun t => excess (g t) (B.adaptivePlay hcv P G g t).val u.val
    (∑ t ∈ Finset.range T, r t) ≤
      adaptiveWidthConstant * (G*W + Real.sqrt (G*W*adaptiveNegative T r)) := by
  let M := adaptiveWidthScale G W
  let r := fun t => excess (g t) (B.adaptivePlay hcv P G g t).val u.val
  let C := G*B.cost+257*M
  let n := adaptiveNegative T r
  let κ := adaptiveBaseWidthFactor + 514 / Real.log 2
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM : 0 < M := by dsimp [M,adaptiveWidthScale]; positivity
  have hspread (x y : K) : G*norm₂ (x.val-y.val) ≤ M := calc
    _ ≤ G*(2*coordinateWidth K / Real.log 2) :=
      mul_le_mul_of_nonneg_left (coordinateWidth_pair hc x y) hG.le
    _ ≤ G*(2*W / Real.log 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hwidth (by norm_num)) hlog.le) hG.le
    _ = _ := by dsimp [M,adaptiveWidthScale]; ring
  have hm := B.adaptiveMixture hcv P g hM hG hg hspread T hT u
  change (∑ t ∈ Finset.range T, r t) ≤ 24*(C+Real.sqrt (C*n)) at hm
  have hC : C ≤ κ*(G*W) := calc
    _ ≤ G*(adaptiveBaseWidthFactor*W)+257*M := add_le_add
      (mul_le_mul_of_nonneg_left (hcost.trans
        (mul_le_mul_of_nonneg_left hwidth (by norm_num [adaptiveBaseWidthFactor]))) hG.le) le_rfl
    _ = _ := by dsimp [M,adaptiveWidthScale,κ]; ring
  have hn := adaptiveNegative_nonneg T r
  have hκ : 1 ≤ κ := by
    dsimp [κ,adaptiveBaseWidthFactor]
    have h := div_nonneg (by norm_num : (0:ℝ) ≤ 514) hlog.le
    linarith only [h]
  have hκ' : Real.sqrt κ ≤ κ := by
    apply (Real.sqrt_le_left (zero_le_one.trans hκ)).mpr
    simpa only [one_mul, pow_two] using mul_le_mul_of_nonneg_right hκ (zero_le_one.trans hκ)
  have hroot : Real.sqrt (C*n) ≤ κ*Real.sqrt (G*W*n) := calc
    _ ≤ Real.sqrt ((κ*(G*W))*n) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hC hn)
    _ = Real.sqrt κ * Real.sqrt (G*W*n) := by
      rw [mul_assoc, Real.sqrt_mul (zero_le_one.trans hκ), mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right hκ' (Real.sqrt_nonneg _)
  change (∑ t ∈ Finset.range T, r t) ≤ (24*κ)*(G*W+Real.sqrt (G*W*n))
  linarith only [hm,hC,hroot]

theorem adaptiveWidth_convex_givenBase (B : AdaptiveBase K) (hc : IsCompact K) (hcv : Convex ℝ K)
    (hcost : B.cost ≤ adaptiveBaseWidthFactor*coordinateWidth K) {G W : ℝ} (hG : 0 < G) (hW : 0 < W)
    (hwidth : coordinateWidth K ≤ W) (P : AdaptiveWeightRule (adaptiveWidthScale G W))
    (g : ℕ → Vec d) (hg : ∀ t, norm₂ (g t) ≤ G) (T : ℕ) (hT : 0 < T) (u : K)
    (f : ℕ → Vec d → ℝ) (hcont : ∀ t < T, ContinuousOn (f t) K)
    (hsub : ∀ t < T, ∀ v ∈ K, f t (B.adaptivePlay hcv P G g t).val - f t v ≤
      excess (g t) (B.adaptivePlay hcv P G g t).val v) :
    let w := fun t => (B.adaptivePlay hcv P G g t).val
    let r := fun t => excess (g t) (w t) u.val
    let n := adaptiveNegative T r
    let Δ := ∑ t ∈ Finset.range T, (f t u.val - sInf (f t '' K))
    (∑ t ∈ Finset.range T, (f t (w t) - f t u.val)) ≤ (∑ t ∈ Finset.range T, r t) ∧
      (∑ t ∈ Finset.range T, r t) ≤ adaptiveWidthConstant*(G*W+Real.sqrt (G*W*n)) ∧
      adaptiveWidthConstant*(G*W+Real.sqrt (G*W*n)) ≤
        adaptiveWidthConstant*(G*W+Real.sqrt (G*W*Δ)) := by
  let w := fun t => (B.adaptivePlay hcv P G g t).val
  have htransfer := adaptiveConvexTransfer hc T w g f u.val u.prop
    (fun t _ => (B.adaptivePlay hcv P G g t).prop) hcont hsub
  refine ⟨htransfer.1, adaptiveWidth_givenBase B hc hcv hcost hG hW hwidth P g hg T hT u, ?_⟩
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left htransfer.2 (mul_nonneg hG.le hW.le))))
    adaptiveWidthConstant_pos.le


end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory

namespace Curvature
open Coordinate


private theorem position_id (d : ℕ) :
    position 0 (LinearIsometry.id : Axes d →ₗᵢ[ℝ] Sparse.Space d) = id := by
  funext x
  simp [Coordinate.position]

theorem euclideanBall_eq_ellipsoid (d : ℕ) (R : ℝ) (hR : 0 < R) :
    Metric.closedBall (0 : Sparse.Space d) R =
      ellipsoid 0 (LinearIsometry.id : Axes d →ₗᵢ[ℝ] Sparse.Space d) (fun _ => R) := by
  rw [ellipsoid, position_id, Set.image_id]
  ext x
  simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_ofPred_eq, div_pow, ← Finset.sum_div,
    div_le_one (sq_pos_of_pos hR), ← EuclideanSpace.real_norm_sq_eq]
  exact (sq_le_sq₀ (norm_nonneg x) hR.le).symm

private theorem canonicalAxisLower {d r : ℕ} [NeZero r] {Ω : Type*} [MeasurableSpace Ω]
    (c : Sparse.Space d) (U : Axes r →ₗᵢ[ℝ] Sparse.Space d) (a : Fin r → ℝ) (ha : ∀ i, 0 < a i)
    {K : Set (Sparse.Space d)} (hK : K = box c U a ∨ K = ellipsoid c U a)
    (L : FullInfoLearner (Sparse.Space d) Ω K) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : ℝ≥0) (hG : 0 < G) (b : ℝ) (hb : 0 ≤ b) :
    let W := (G:ℝ)*subexponentialWidth K
    L.HasHardSequence μ G b ((W + Real.sqrt (W*b))/20480) := by
  have hn : K.Nonempty := by
    rcases hK with rfl | rfl
    · exact ⟨_, vertex_mem c U (fun i => (ha i).le) (fun _ => true)⟩
    · exact ⟨_, 0, by simp, rfl⟩
  have hbd : Bornology.IsBounded K := by
    rcases hK with rfl | rfl
    · exact box_bounded c U a
    · exact (box_bounded c U a).subset (ellipsoid_subset_box c U ha)
  have hw := le_csSup (widthValues_bddAbove K hn hbd) (zero_mem_widthValues K hn)
  have hh : let W := (G:ℝ)*subexponentialWidth K
            L.HasHardSequence μ G b ((W + Real.sqrt (W*b))/64) := by
    revert L
    rcases hK with rfl | rfl
    · rw [← fixedLpBody_box c U ha]
      intro L
      exact fixedLpBudgetLower c U ha (q := 1) (by norm_num) (by norm_num) L μ G hG b hb
    · rw [← fixedLpBody_euclidean c U a]
      intro L
      exact fixedLpBudgetLower c U ha (q := 2) (by norm_num) (by norm_num) L μ G hG b hb
  obtain ⟨T, hT, f, hf, hc, hi, hr⟩ := hh
  refine ⟨T, hT, f, hf, hc, hi, le_trans ?_ hr⟩
  change 0 ≤ subexponentialWidth K at hw
  linarith [mul_nonneg G.coe_nonneg hw, Real.sqrt_nonneg ((G:ℝ)*subexponentialWidth K*b)]

/-- For every full-information learner and budget, one finite deterministic sequence of
convex Lipschitz losses forces the lower bound on the expected regret. -/
theorem minimaxLower {d : ℕ} {K : Set (Sparse.Space d)} (hK : CanonicalDomain d K)
    {Ω : Type*} [MeasurableSpace Ω] (L : FullInfoLearner (Sparse.Space d) Ω K)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : ℝ≥0) (hG : 0 < G) (b : ℝ) (hb : 0 ≤ b) :
    let W := (G:ℝ)*subexponentialWidth K
    L.HasHardSequence μ G b ((W + Real.sqrt (W*b))/20480) := by
  cases hK with
  | unitLp hd p hp => exact Sparse.unitLp_width_lower hd p hp L μ G hG b hb
  | unitLinf hd =>
    let : NeZero d := ⟨Nat.ne_of_gt hd⟩
    apply canonicalAxisLower 0 (LinearIsometry.id : Axes d →ₗᵢ[ℝ] Sparse.Space d)
      (fun _ => 1) (fun _ => zero_lt_one) _ L μ G hG b hb
    exact Or.inl (by rw [box, position_id, Set.image_id])
  | euclidean hd R hR =>
    let : NeZero d := ⟨Nat.ne_of_gt hd⟩
    exact canonicalAxisLower 0 _ (fun _ => R) (fun _ => hR)
      (Or.inr (euclideanBall_eq_ellipsoid d R hR)) L μ G hG b hb
  | ellipsoid hr _ c U a ha =>
    let : NeZero _ := ⟨Nat.ne_of_gt hr⟩
    exact canonicalAxisLower c U a ha (Or.inr rfl) L μ G hG b hb
  | box hr _ c U a ha =>
    let : NeZero _ := ⟨Nat.ne_of_gt hr⟩
    exact canonicalAxisLower c U a ha (Or.inl rfl) L μ G hG b hb
  | simplex hd => exact Sparse.simplex_width_lower hd L μ G hG b hb

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory

namespace Curvature
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]

private def pairedLaw (w : ι → ℝ) (z : ι → E) : Measure E :=
  ∑ i, ENNReal.ofReal (w i/2) •
    (Measure.dirac ((1/2 : ℝ) • z i) + Measure.dirac (-((1/2 : ℝ) • z i)))

omit [BorelSpace E] [FiniteDimensional ℝ E] in
private theorem pairedLaw_prob (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (z : ι → E) : IsProbabilityMeasure (pairedLaw w z) := by
  constructor
  unfold pairedLaw
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul, mul_add, mul_one]
  simp_rw [← ENNReal.ofReal_add (div_nonneg (hw _) (by norm_num : (0:ℝ) ≤ 2)) (div_nonneg (hw _) (by norm_num : (0:ℝ) ≤ 2)), add_halves]
  rw [← ENNReal.ofReal_sum_of_nonneg (by exact fun i _ => hw i), hw1, ENNReal.ofReal_one]

private theorem paired_integrable {X : Type*} [NormedAddCommGroup X] (w : ι → ℝ) (z : ι → E)
    (g : E → X) : Integrable g (pairedLaw w z) := by
  apply integrable_finsetSum_measure.mpr
  intro i _
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  exact (integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))

private theorem paired_integral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (z : ι → E) (g : E → X) :
    (∫ s, g s ∂pairedLaw w z) = ∑ i, (w i/2) • (g ((1/2 : ℝ) • z i) + g (-((1/2 : ℝ) • z i))) := by
  unfold pairedLaw
  rw [integral_finsetSum_measure (integrable_finsetSum_measure.mp (paired_integrable w z g))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure, integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp)),
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal (div_nonneg (hw i) (by norm_num : (0:ℝ) ≤ 2))]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private theorem inner_le_support {K : Set E} (hb : Bornology.IsBounded K) (x : K) (v : E) :
    ⟪x.val,v⟫_ℝ ≤ widthSupport K v := by
  obtain ⟨R,hR⟩ := isBounded_iff_forall_norm_le.mp hb
  apply le_ciSup (f := fun y : K => ⟪y.val,v⟫_ℝ) _ x
  refine ⟨R*‖v‖, Set.forall_mem_range.mpr fun y => ?_⟩
  exact (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hR _ y.property) (norm_nonneg _)))

/-- A finite mixture tested on net directions gives an admissible centered law after symmetrizing and halving. -/
theorem finite_moment_payoff [CompleteSpace E] {N : ℕ} (q : Fin N → E)
    (hnet : ∀ v : E, ‖v‖ ≤ 1 → (1/2 : ℝ) • v ∈ convexHull ℝ (Set.range q))
    (K : Set E) (hb : Bornology.IsBounded K) (center : K)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (z : ι → E) (x : ι → K)
    (hm : ∀ j, ∑ i, w i * momentPenalty ⟪q j, z i⟫_ℝ ≤ 1) :
    (∑ i, w i * ⟪(x i).val - center.val,z i⟫_ℝ) ≤ 4*subexponentialWidth K := by
  let P (v : E) := ∑ i, w i * momentPenalty ⟪v,z i⟫_ℝ
  have hcon : Convex ℝ {v : E | P v ≤ 1} := by
    intro v hv v' hv' a b ha hh hab
    change P v ≤ 1 at hv
    change P v' ≤ 1 at hv'
    change P (a • v + b • v') ≤ 1
    have hlin : P (a • v + b • v') ≤ a*P v + b*P v' := by
      unfold P
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      have h := mul_le_mul_of_nonneg_left (penalty_convex (x := ⟪v,z i⟫_ℝ) (y := ⟪v',z i⟫_ℝ)
        ha hh hab) (hw i)
      linarith
    linarith [mul_le_mul_of_nonneg_left hv ha, mul_le_mul_of_nonneg_left hv' hh]
  have hdir (v : E) (hv : ‖v‖ ≤ 1) : P ((1/2 : ℝ) • v) ≤ 1 :=
    convexHull_min (Set.range_subset_iff.mpr hm) hcon (hnet v hv)
  have hμ : AdmissibleWidthLaw (pairedLaw w z) := by
    refine ⟨pairedLaw_prob w hw hw1 z, paired_integrable _ _ _, ?_, fun _ _ => paired_integrable _ _ _, ?_⟩
    · rw [paired_integral w hw]; simp
    · intro v hv
      rw [paired_integral w hw]
      have he (i : ι) : (w i / 2) • (Real.exp |⟪v,(1/2:ℝ) • z i⟫_ℝ| +
            Real.exp |⟪v,-((1/2:ℝ) • z i)⟫_ℝ|) =
          w i * momentPenalty ⟪(1/2:ℝ) • v,z i⟫_ℝ + w i := by
        simp only [inner_neg_right, abs_neg, real_inner_smul_right, real_inner_smul_left,
          momentPenalty, smul_eq_mul]
        ring
      simp_rw [he]
      rw [Finset.sum_add_distrib,hw1]
      linarith [hdir v hv]
  have hW := le_width_of_law K (widthValues_bddAbove K ⟨center.val,center.property⟩ hb) hμ
  rw [paired_integral w hw] at hW
  have hp (i : ι) :
      w i * ⟪(x i).val-center.val,z i⟫_ℝ ≤
        4*((w i/2) • (widthSupport K ((1/2:ℝ) • z i) + widthSupport K (-((1/2:ℝ) • z i)))) := by
    have hx := inner_le_support hb (x i) ((1/2:ℝ) • z i)
    have hc := inner_le_support hb center (-((1/2:ℝ) • z i))
    rw [real_inner_smul_right] at hx
    rw [inner_neg_right, real_inner_smul_right] at hc
    simp only [inner_sub_left, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hx hc) (hw i)]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hp i)
  rw [← Finset.mul_sum] at hsum
  linarith

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

theorem description_of_majorant {d N : ℕ} {K : Set (Vec d)} (center : K)
    (hnon : ∃ x : K, x.val ≠ center.val) (q : Matrix (Fin d) (Fin N) ℝ)
    (hq : ∀ j, norm₂ (fun i => q i j) ≤ 1) {β : Vec N} (hβ : ∀ j, 0 ≤ β j)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ x : K, ∀ z : Vec d, dotProduct (x.val-center.val) z ≤ c +
      ∑ i, β i * momentPenalty (q.transpose.mulVec z i)) :
    ∃ D : AdmissibleDescription K, D.N ≤ N ∧ D.representationCost ≤ 4*c + 5*∑ j, β j := by
  classical
  let I := {j : Fin N // 0 < β j}
  have hI : Nonempty I := by
    by_contra! he
    have hzero (i : Fin N) : β i = 0 := le_antisymm (le_of_not_gt fun hh =>
      he.elim (⟨i,hh⟩ : I)) (hβ i)
    obtain ⟨x,hx⟩ := hnon
    let v := x.val-center.val
    have hv : dotProduct v v ≠ 0 := fun h => hx (sub_eq_zero.mp (dotProduct_self_eq_zero.mp h))
    have h := hbound x (((c+1)/dotProduct v v) • v)
    change dotProduct v _ ≤ _ at h
    simp only [hzero, zero_mul, Finset.sum_const_zero, add_zero, dotProduct_smul, smul_eq_mul,
      div_mul_cancel₀ _ hv] at h
    linarith
  let := hI
  let e := (Fintype.equivFin I).symm
  let n := Fintype.card I
  let Q : Matrix (Fin d) (Fin n) ℝ := fun i j => q i (e j).val
  let B (j : Fin n) := β (e j).val
  have sum' (f : Fin N → ℝ) : ∑ j, B j*f (e j).val = ∑ i, β i*f i := by
    change ∑ j, (fun k : I => β k.val*f k.val) (e j) = _
    rw [e.sum_comp (fun k : I => β k.val*f k.val)]
    have hz (j : {i : Fin N // ¬ 0 < β i}) : β j.val*f j.val = 0 := by
      rw [le_antisymm (le_of_not_gt j.property) (hβ _), zero_mul]
    have hs := Fintype.sum_subtype_add_sum_subtype (fun j => 0 < β j) (fun j => β j*f j)
    simpa only [hz, Finset.sum_const_zero, add_zero] using hs
  have ht : ∑ j, B j = ∑ i, β i := by simpa using sum' (fun _ => 1)
  have hrep (u : Vec d) (hu : u ∈ K) : ∃ y : Vec n, center.val + Q.mulVec y = u ∧
      ∑ j, B j * expDual (|y j| / B j) ≤ c := by
    have hdom (z : Vec d) : dotProduct (u-center.val) z ≤
        c + ∑ j, B j * momentPenalty (Q.transpose.mulVec z j) := by
      change _ ≤ c + ∑ j, B j * (fun i => momentPenalty (q.transpose.mulVec z i)) (e j).val
      rw [sum' (fun i => momentPenalty (q.transpose.mulVec z i))]; exact hbound ⟨u,hu⟩ z
    obtain ⟨y,he,hy⟩ := dualCoefficients_of_majorant Q B (fun j => (e j).property) hc _ hdom
    exact ⟨y, by rw [he]; abel, hy⟩
  obtain ⟨D,hN,hcost⟩ := description_of_dualCoefficients (N := n) Fintype.card_pos
    ⟨center.val,center.property⟩ center.val Q (fun j => hq (e j).val) B (fun j => (e j).property) hc hrep
  refine ⟨D, ?_, ht ▸ hcost⟩
  rw [hN]
  simpa [n,I] using Fintype.card_subtype_le (fun j : Fin N => 0 < β j)

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Curvature

variable {d r : ℕ}


theorem canonicalUnitBall_nontrivial [NeZero r] {p : ℝ} (hp : 0 < p) : (canonicalUnitBall r p).Nontrivial := by
  let v : Vec r := Pi.single 0 1
  refine ⟨0, by simp [canonicalUnitBall, Real.zero_rpow hp.ne'],v, ?_, ?_⟩
  · change ∑ i, |v i|^p ≤ 1
    rw [Finset.sum_eq_single (0:Fin r)]
    · simp [v]
    · intro j _ hj; simp [v,hj,Real.zero_rpow hp.ne']
    · simp
  · intro h
    have := congrFun h 0
    simp [v] at this


private abbrev HasProperties {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ K.Nontrivial

private theorem props_image {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (c : F) (L : E →ₗ[ℝ] F)
    (hL : Function.Injective L) {C : Set E} (h : HasProperties C) :
    HasProperties ((fun v => c+L v) '' C) := by
  refine ⟨h.1.image (continuous_const.add L.continuous_of_finiteDimensional), ?_, h.2.2.image ?_⟩
  · simpa only [Set.image_image] using (h.2.1.linear_image L).translate c
  · intro x y hxy
    exact hL (add_left_cancel hxy)

private theorem props_toLp {C : Set (Vec r)} (h : HasProperties C) :
    HasProperties ((WithLp.toLp 2) '' C : Set (CanonicalSpace r)) := by
  let L := (EuclideanSpace.equiv (Fin r) ℝ).symm
  change HasProperties ((fun x => L.toLinearEquiv.toLinearMap x) '' C)
  simpa only [zero_add] using props_image 0 L.toLinearEquiv.toLinearMap L.injective h

private theorem props_cube [NeZero r] (a : Vec r) (ha : ∀ i, 0 < a i) :
    HasProperties {x : Vec r | ∀ i, |x i| ≤ a i} := by
  have heq : {x : Vec r | ∀ i, |x i| ≤ a i} = Set.Icc (-a) a := by
    ext x
    exact ⟨fun h => ⟨fun i => (abs_le.mp (h i)).1, fun i => (abs_le.mp (h i)).2⟩,
      fun ⟨hl,hh⟩ i => abs_le.mpr ⟨hl i,hh i⟩⟩
  rw [heq]
  have hpos : -a ≤ a := fun i => neg_le_self (ha i).le
  refine ⟨isCompact_Icc, convex_Icc _ _, -a, ⟨le_rfl,hpos⟩, a, ⟨hpos,le_rfl⟩, ?_⟩
  intro h
  have h' : -(a 0) = a 0 := congrFun h 0
  linarith [ha 0]

private theorem props_ellipsoid_axes [NeZero r] (a : Vec r) (ha : ∀ i, 0 < a i) :
    HasProperties {z : Coordinate.Axes r | ∑ i, (z i / a i)^2 ≤ 1} := by
  let L := (EuclideanSpace.equiv (Fin r) ℝ).symm.toLinearEquiv.toLinearMap.comp (Matrix.diagonal a).mulVecLin
  have hi (v : Vec r) (j : Fin r) : (L v) j = a j*v j := Matrix.mulVec_diagonal a v j
  have hinj : Function.Injective L := by
    intro v w h
    ext j
    exact mul_left_cancel₀ (ha j).ne' (by simpa only [hi] using congrArg (fun z : Coordinate.Axes r => z j) h)
  have h := props_image 0 L hinj (C:=canonicalUnitBall r 2)
    ⟨canonicalUnitBall_compact (by norm_num), canonicalUnitBall_convex (by norm_num), canonicalUnitBall_nontrivial (by norm_num)⟩
  simp only [zero_add] at h
  convert h using 1
  ext z
  constructor
  · intro hz
    refine ⟨fun i => z i / a i, ?_, ?_⟩
    · simpa [canonicalUnitBall,Real.rpow_two,sq_abs] using hz
    · ext j
      rw [hi,mul_div_cancel₀ _ (ha j).ne']
  · rintro ⟨v,hv,rfl⟩
    change ∑ i, (L v i / a i)^2 ≤ 1
    simpa [hi,fun i => (ha i).ne',canonicalUnitBall,Real.rpow_two,sq_abs] using hv

theorem CanonicalDomain.properties {K : Set (Sparse.Space d)} (hK : CanonicalDomain d K) :
    IsCompact K ∧ Convex ℝ K ∧ K.Nontrivial := by
  cases hK with
  | unitLp hd p hp =>
    let : NeZero d := ⟨hd.ne'⟩
    have hp0 : 0 < p := by linarith
    have h := props_toLp (C:=canonicalUnitBall d p)
      ⟨canonicalUnitBall_compact hp0,canonicalUnitBall_convex hp,canonicalUnitBall_nontrivial hp0⟩
    exact (show (WithLp.toLp 2 '' canonicalUnitBall d p : Set (Sparse.Space d)) = Sparse.lpBall d p by
      ext x; exact ⟨fun ⟨v,hv,h⟩ => h ▸ hv,fun hx => ⟨x.ofLp,hx,rfl⟩⟩) ▸ h
  | unitLinf hd =>
    let : NeZero d := ⟨hd.ne'⟩
    have h := props_toLp (props_cube (fun _ : Fin d => 1) (fun _ => zero_lt_one))
    exact (show (WithLp.toLp 2 '' {x : Vec d | ∀ i, |x i| ≤ 1} : Set (Sparse.Space d)) =
        {x | ∀ i, |x i| ≤ 1} by
      ext x; exact ⟨fun ⟨v,hv,h⟩ => h ▸ hv,fun hx => ⟨x.ofLp,hx,rfl⟩⟩) ▸ h
  | euclidean hd R hR =>
    let : NeZero d := ⟨hd.ne'⟩
    rw [euclideanBall_eq_ellipsoid d R hR]
    exact props_image 0 (LinearIsometry.id.toLinearMap) (LinearIsometry.id.injective)
      (props_ellipsoid_axes (fun _ : Fin d => R) (fun _ => hR))
  | ellipsoid hr _ c U a ha =>
    let : NeZero _ := ⟨hr.ne'⟩
    exact props_image c U.toLinearMap U.injective (props_ellipsoid_axes a ha)
  | box hr _ c U a ha =>
    let : NeZero _ := ⟨hr.ne'⟩
    have h := props_toLp (props_cube a ha)
    apply props_image c U.toLinearMap U.injective
    convert h using 1
    ext x; exact ⟨fun hx => ⟨x.ofLp,hx,rfl⟩,fun ⟨v,hv,h⟩ => h ▸ hv⟩
  | simplex hd =>
    let : Nontrivial (Fin d) := Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_fin]; omega)
    obtain ⟨i,j,hij⟩ := exists_pair_ne (Fin d)
    have hC : (stdSimplex ℝ (Fin d)).Nontrivial := by
      refine ⟨_,single_mem_stdSimplex _ i,_,single_mem_stdSimplex _ j,?_⟩
      intro h
      have h' := congrFun h i
      simp [hij] at h'
    have h := props_toLp (C:=stdSimplex ℝ (Fin d)) ⟨isCompact_stdSimplex _ _,convex_stdSimplex _ _,hC⟩
    exact (show (WithLp.toLp 2 '' stdSimplex ℝ (Fin d) : Set (Sparse.Space d)) = Sparse.simplex d by
      ext x; exact ⟨fun ⟨v,hv,h⟩ => h ▸ hv,fun hx => ⟨x.ofLp,hx,rfl⟩⟩) ▸ h

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Curvature

/-- A single finite moment majorant controls every point relative to the chosen center. -/
theorem net_width_majorant {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {N : ℕ}
    (q : Fin N → E) (hnet : ∀ v : E, ‖v‖ ≤ 1 → (1/2 : ℝ) • v ∈ convexHull ℝ (Set.range q))
    {K : Set E} (hb : Bornology.IsBounded K) (center : K) :
    ∃ c : ℝ, ∃ β : Vec N, 0 ≤ c ∧ (∀ j, 0 ≤ β j) ∧ c + ∑ j, β j = 4*subexponentialWidth K ∧
      ∀ x : K, ∀ z : E, ⟪x.val-center.val,z⟫_ℝ ≤ c + ∑ j, β j * momentPenalty ⟪q j,z⟫_ℝ := by
  classical
  let φ (a : E × K) : Vec N × ℝ := (fun j => momentPenalty ⟪q j,a.1⟫_ℝ, ⟪a.2.val-center.val,a.1⟫_ℝ)
  let P := convexHull ℝ (Set.range φ)
  have hin (a : E × K) : φ a ∈ P := subset_convexHull ℝ _ (Set.mem_range_self a)
  have h0 : (0,0) ∈ P := by
    change ((fun _ : Fin N => (0:ℝ)),0) ∈ P
    simpa [φ,momentPenalty] using hin (0,center)
  have bound (p : Vec N × ℝ) (hp : p ∈ P) (hcost : ∀ i, p.1 i < 1) : p.2 ≤ 4*subexponentialWidth K := by
    obtain ⟨ι, fi, w, obs, hw, hw1, hobs, heq⟩ := mem_convexHull_iff_exists_fintype.mp hp
    choose a ha using hobs
    have hfun (j : Fin N) : ∑ i, w i * momentPenalty ⟪q j,(a i).1⟫_ℝ = p.1 j := by
      have hh := congrArg (fun v : Vec N × ℝ => v.1 j) heq
      simpa only [← ha, φ, Prod.fst_sum, Prod.smul_fst, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul] using hh
    have hp' : ∑ i, w i * ⟪(a i).2.val-center.val,(a i).1⟫_ℝ = p.2 := by
      have hh := congrArg Prod.snd heq
      simpa only [← ha, φ, Prod.snd_sum, Prod.smul_snd, smul_eq_mul] using hh
    rw [← hp']
    exact finite_moment_payoff q hnet K hb center w hw hw1 (fun i => (a i).1) (fun i => (a i).2)
      (fun j => (hfun j).le.trans (hcost j).le)
  have hn : K.Nonempty := ⟨_,center.property⟩
  have hw := le_csSup (widthValues_bddAbove K hn hb) (zero_mem_widthValues K hn)
  obtain ⟨c,β,hc,hβ,hs,hp⟩ := moment_prices (convex_convexHull ℝ (Set.range φ)) h0
    (mul_nonneg (by norm_num : 0 ≤ (4:ℝ)) hw) bound
  exact ⟨c,β,hc,hβ,hs,fun x z => hp _ (hin (z,x))⟩

/-- Existence in the width-equivalence proposition, with the paper's factor twenty. -/
theorem exists_width_description {d : ℕ} {K : Set (Vec d)} (hc : IsCompact K)
    (hnon : K.Nontrivial) : ∃ D : AdmissibleDescription K, D.representationCost ≤ 20*coordinateWidth K := by
  classical
  let e := (EuclideanSpace.equiv (Fin d) ℝ).symm
  let S := e '' K
  obtain ⟨u,hu,x,hx,hne⟩ := hnon
  let center : S := ⟨e u,Set.mem_image_of_mem e hu⟩
  obtain ⟨N,q,hq,hnet⟩ := exists_width_directions (EuclideanSpace ℝ (Fin d))
  obtain ⟨c,β,hpos,hβ,hs,hbound⟩ := net_width_majorant q hnet (hc.image e.continuous).isBounded center
  let Q : Matrix (Fin d) (Fin N) ℝ := fun i j => q j i
  have hcol (j : Fin N) : norm₂ (fun i => Q i j) ≤ 1 := by
    simpa only [euclidean_norm] using hq j
  have hd (w : K) (z : Vec d) : dotProduct (w.val-u) z ≤
      c + ∑ j, β j * momentPenalty (Q.transpose.mulVec z j) := by
    have h := hbound ⟨e w.val,Set.mem_image_of_mem e w.property⟩ (e z)
    simp only [center, euclidean_inner, WithLp.ofLp_sub] at h
    convert! h using 1
  obtain ⟨D,_,hD⟩ := description_of_majorant (K := K) ⟨u,hu⟩ ⟨⟨x,hx⟩,hne.symm⟩ Q hcol hβ hpos hd
  change c + ∑ j, β j = 4*coordinateWidth K at hs
  exact ⟨D, by linarith⟩

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature
variable {d : ℕ} {K : Set (Vec d)}

/-- Choose the description before the feedback stream and all comparator choices. -/
def curvatureWidthDescription (hc : IsCompact K) (hnon : K.Nontrivial) : AdmissibleDescription K :=
  (exists_width_description hc hnon).choose

theorem curvatureWidthDescription_cost (hc : IsCompact K) (hnon : K.Nontrivial) :
    (curvatureWidthDescription hc hnon).representationCost ≤ 20*coordinateWidth K :=
  (exists_width_description hc hnon).choose_spec


end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature
variable {d : ℕ} {K : Set (Vec d)}


namespace DomainInitialization

def general (hc : IsCompact K) (hnon : K.Nontrivial) : DomainInitialization K := by
  let D := curvatureWidthDescription hc hnon
  have hd := curvatureWidthDescription_cost hc hnon
  have hw := width_le_representationCost D hnon.nonempty hc
  exact .dyadic D (by change D.representationCost ≤ 20*coordinateWidth K at hd; linarith)


theorem adaptiveBase_cost (I : DomainInitialization K) (hne : K.Nonempty) (hc : IsCompact K)
    (hcv : Convex ℝ K) : (I.adaptiveBase hne hc hcv).cost ≤ 393216*coordinateWidth K := by
  cases I with
  | dyadic D h => change 192*D.representationCost ≤ _; linarith
  | fixed center A ha hq hq' hgram hbody mode =>
    change 164*coordinateWidth K ≤ _
    have h := (AdaptiveBase.fixedAxes hne hc hcv center A ha hq hq' hgram hbody mode).cost_nonneg
    change 0 ≤ 164*coordinateWidth K at h
    linarith

end DomainInitialization


end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace NNReal
open MeasureTheory
namespace Curvature

variable {d : ℕ} {K : Set (Vec d)}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "e" => ContinuousLinearEquiv.symm (EuclideanSpace.equiv (Fin d) ℝ)

private def boundedSubgradient (G : ℝ≥0) (f : E → ℝ) (x : E) : E := by
  classical
  exact if h : ∃ g : E, ‖g‖ ≤ G ∧ ∀ y : E, f x-f y ≤ ⟪g,x-y⟫_ℝ then h.choose else 0

private theorem boundedSubgradient_norm (G : ℝ≥0) (f : E → ℝ) (x : E) :
    ‖boundedSubgradient G f x‖ ≤ G := by
  unfold boundedSubgradient
  split
  · rename_i hp
    exact hp.choose_spec.1
  · simp

private theorem boundedSubgradient_spec {G : ℝ≥0} {f : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ f) (hlip : LipschitzWith G f) (x y : E) :
    f x-f y ≤ ⟪boundedSubgradient G f x,x-y⟫_ℝ := by
  have h := exists_bounded_subgradient hconv hlip x
  unfold boundedSubgradient
  rw [dif_pos h]
  exact h.choose_spec.2 y

private def padLosses {T : ℕ} (f : Fin T → E → ℝ) (t : ℕ) (x : E) : ℝ :=
  if h : t<T then f ⟨t,h⟩ x else 0

namespace AdaptiveBase

variable (B : AdaptiveBase K) (hcv : Convex ℝ K) {M : ℝ}
  (P : AdaptiveWeightRule M) (G : ℝ≥0)

def fullAfter (f : ℕ → E → ℝ) : ℕ → AdaptiveRunState d
  | 0 => ⟨0,0⟩
  | t+1 =>
    let s := fullAfter f t
    let w := B.adaptiveRoundPlay hcv P G s t
    let g := (boundedSubgradient G (f t) (e w.val)).ofLp
    B.adaptiveStep hcv P G s t g

def fullFeedback (f : ℕ → E → ℝ) (t : ℕ) : Vec d :=
  let w := B.adaptiveRoundPlay hcv P G (B.fullAfter hcv P G f t) t
  (boundedSubgradient G (f t) (e w.val)).ofLp

theorem fullFeedback_norm (f : ℕ → E → ℝ) (t : ℕ) :
    norm₂ (B.fullFeedback hcv P G f t) ≤ G := by
  unfold fullFeedback
  simpa only [euclidean_norm] using boundedSubgradient_norm G (f t)
    (e (B.adaptiveRoundPlay hcv P G (B.fullAfter hcv P G f t) t).val)

theorem fullAfter_eq (f : ℕ → E → ℝ) (t : ℕ) :
    B.fullAfter hcv P G f t = B.adaptiveStateAfter hcv P G (B.fullFeedback hcv P G f) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change B.adaptiveStep hcv P G (B.fullAfter hcv P G f t) t (B.fullFeedback hcv P G f t) =
      B.adaptiveStep hcv P G (B.adaptiveStateAfter hcv P G (B.fullFeedback hcv P G f) t)
        t (B.fullFeedback hcv P G f t)
    rw [ih]

theorem fullAfter_prefix (f h : ℕ → E → ℝ) (t : ℕ) (heq : ∀ i < t, f i = h i) :
    B.fullAfter hcv P G f t = B.fullAfter hcv P G h t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [fullAfter, ih (fun i hi => heq i (by omega)), heq t (Nat.lt_succ_self t)]

/-- Read earlier losses in order and use one subgradient from each at the original prediction. -/
def fullInfoLearner (Ω : Type*) [MeasurableSpace Ω] : FullInfoLearner E Ω (e '' K) where
  predict t past _ :=
    e (B.adaptiveRoundPlay hcv P G (B.fullAfter hcv P G (padLosses past) t) t).val
  mem t h _ := Set.mem_image_of_mem _ (B.adaptiveRoundPlay hcv P G
    (B.fullAfter hcv P G (padLosses h) t) t).prop
  measurable _ _ := measurable_const

theorem fullInfoLearner_predict_eq {Ω : Type*} [MeasurableSpace Ω] {T : ℕ}
    (f : Fin T → E → ℝ) (t : Fin T) (ω : Ω) :
    (B.fullInfoLearner hcv P G Ω).predict t.val (FullInfoLearner.pastLosses f t) ω =
      e (B.adaptivePlay hcv P G (B.fullFeedback hcv P G (padLosses f)) t.val).val := by
  unfold fullInfoLearner adaptivePlay
  have hp : B.fullAfter hcv P G (padLosses (FullInfoLearner.pastLosses f t)) t.val =
      B.fullAfter hcv P G (padLosses f) t.val := by
    apply B.fullAfter_prefix hcv P G
    intro i hi
    funext x
    simp [padLosses, FullInfoLearner.pastLosses, hi, hi.trans t.isLt]
  change e (B.adaptiveRoundPlay hcv P G
    (B.fullAfter hcv P G (padLosses (FullInfoLearner.pastLosses f t)) t.val) t.val).val =
      e (B.adaptiveRoundPlay hcv P G
        (B.adaptiveStateAfter hcv P G (B.fullFeedback hcv P G (padLosses f)) t.val) t.val).val
  rw [hp, fullAfter_eq]

end AdaptiveBase

theorem coordinateWidth_pos_of_nontrivial (hc : IsCompact K) (hnon : K.Nontrivial) :
    0 < coordinateWidth K := by
  obtain ⟨x, hx, y, hy, hne⟩ := hnon
  have hn : 0 < norm₂ (x-y) := by
    unfold norm₂
    apply Real.sqrt_pos_of_pos
    exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg ((x-y) i))
      (Ne.symm (fun h => hne (sub_eq_zero.mp (dotProduct_self_eq_zero.mp h))))
  have h := hn.trans_le (coordinateWidth_pair hc ⟨x,hx⟩ ⟨y,hy⟩)
  have hh := (lt_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp h
  linarith only [hh]

private theorem adaptiveBudget_bound (B : AdaptiveBase K) (hc : IsCompact K)
    (hcv : Convex ℝ K) (hnon : K.Nontrivial)
    (hcost : B.cost ≤ adaptiveBaseWidthFactor * coordinateWidth K)
    {G : ℝ} (hG : 0 < G) (P : AdaptiveWeightRule (adaptiveWidthScale G (coordinateWidth K)))
    {T : ℕ} (hT : 0 < T) (f : Fin T → E → ℝ) (hf : ∀ t, Continuous (f t))
    (g : ℕ → Vec d) (hg : ∀ t, norm₂ (g t) ≤ G)
    (hsub : ∀ (t : Fin T) (x : Vec d), x ∈ K →
      let w := (B.adaptivePlay hcv P G g t.val).val
      f t (e w) - f t (e x) ≤ excess (g t.val) w x) :
    let S := e '' K
    let W := coordinateWidth K
    let w := B.adaptivePlay hcv P G g
    let Δ := FullInfoLearner.comparatorBudget S f
    (∑ t : Fin T, f t (e (w t.val).val)) - FullInfoLearner.bestLoss S f ≤
      adaptiveWidthConstant*(G*W+Real.sqrt (G*W*Δ)) := by
  let W := coordinateWidth K
  have hW : 0 < W := coordinateWidth_pos_of_nontrivial hc hnon
  let fe := padLosses f
  let w := B.adaptivePlay hcv P G g
  let fc := fun t (x : Vec d) => fe t (e x)
  let S := e '' K
  have hs : IsCompact S := hc.image (e).continuous
  let F : E → ℝ := fun x => ∑ t, f t x
  have hF : Continuous F := continuous_finsetSum _ (fun t _ => hf t)
  obtain ⟨uE, huS, hmin⟩ := hs.exists_isMinOn (hnon.nonempty.image _) hF.continuousOn
  obtain ⟨u, hu, hE⟩ := huS
  let v : K := ⟨u,hu⟩
  have huF : FullInfoLearner.bestLoss S f = ∑ t, f t (e v.val) := by
    change sInf (F '' S) = F (e v.val)
    rw [show e v.val = uE from hE]
    apply IsLeast.csInf_eq
    refine ⟨⟨uE, ⟨u, hu, hE⟩, rfl⟩, ?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact hmin hx
  have hcont (t : ℕ) (ht : t < T) : ContinuousOn (fc t) K := by
    change ContinuousOn (fun x => fe t (e x)) K
    have heq : fe t = f ⟨t,ht⟩ := by funext x; simp [fe,padLosses,ht]
    rw [heq]
    exact ((hf ⟨t,ht⟩).comp (e).continuous).continuousOn
  have hsubReal (t : ℕ) (ht : t < T) (x : Vec d) (hx : x ∈ K) :
      fc t (w t).val - fc t x ≤ excess (g t) (w t).val x := by
    have h := hsub ⟨t,ht⟩ x hx
    simpa only [fc, fe, padLosses, dif_pos ht] using h
  obtain ⟨hactual, hlin, hshift⟩ := adaptiveWidth_convex_givenBase B hc hcv
    hcost hG hW le_rfl P g hg
    T hT v fc hcont hsubReal
  let Δ := ∑ t ∈ Finset.range T, (fc t v.val - sInf (fc t '' K))
  let R := ∑ t ∈ Finset.range T, (fc t (w t).val - fc t v.val)
  have hΔ : Δ = FullInfoLearner.comparatorBudget S f := by
    dsimp only [Δ,FullInfoLearner.comparatorBudget]
    rw [huF, ← Finset.sum_sub_distrib, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have heq : fc i.val = f i ∘ e := by
      funext x
      simp [fc,fe,padLosses,i.isLt]
    have hSet : (f i ∘ e) '' K = f i '' S := by
      change (f i ∘ e) '' K = f i '' (e '' K)
      rw [Set.image_image]
      rfl
    rw [heq]
    change f i (e v.val) - sInf ((f i ∘ e) '' K) = _
    rw [hSet]
  have hR : R = (∑ t : Fin T, f t (e (w t.val).val)) - FullInfoLearner.bestLoss S f := by
    dsimp only [R]
    rw [huF, ← Finset.sum_sub_distrib, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => by simp [fc,fe,padLosses,i.isLt]
  have hrBound : R ≤ adaptiveWidthConstant*(G*W + Real.sqrt (G*W*Δ)) :=
    hactual.trans (hlin.trans hshift)
  rw [hR,hΔ] at hrBound
  exact hrBound

/-- A single deterministic strategy satisfies the expected upper bound for every budget. -/
theorem adaptiveFullInfo_upper_ofInitialization {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hc : IsCompact K) (hcv : Convex ℝ K) (hnon : K.Nontrivial)
    (I : DomainInitialization K) (G : ℝ≥0) (hG : 0 < G) :
    ∃ L : FullInfoLearner E Ω (e '' K),
      ∀ {T : ℕ}, 0 < T → ∀ (f : Fin T → E → ℝ),
        (∀ t, ConvexOn ℝ Set.univ (f t) ∧ LipschitzWith G (f t)) →
        ∀ b : ℝ, FullInfoLearner.comparatorBudget (e '' K) f ≤ b →
          Integrable (L.regret f) μ ∧
            (∫ ω, L.regret f ω ∂μ) ≤ adaptiveWidthConstant *
              ((G:ℝ)*coordinateWidth K + Real.sqrt ((G:ℝ)*coordinateWidth K*b)) := by
  let W := coordinateWidth K
  let P := exactAdaptiveWeights (adaptiveWidthScale G W)
  let B := I.adaptiveBase hnon.nonempty hc hcv
  let L := B.fullInfoLearner hcv P G Ω
  refine ⟨L, ?_⟩
  intro T hT f hf b hb
  let fe := padLosses f
  let g := B.fullFeedback hcv P G fe
  let w := B.adaptivePlay hcv P G g
  have hG' : 0 < (G:ℝ) := hG
  have hW : 0 < W := coordinateWidth_pos_of_nontrivial hc hnon
  have hsub (i : Fin T) (x : Vec d) (_ : x ∈ K) :
      f i (e (w i.val).val) - f i (e x) ≤ excess (g i.val) (w i.val).val x := by
    let t := i.val
    have heq : fe t = f i := by funext x; simp [fe,padLosses,t,i.isLt]
    have hw : B.adaptiveRoundPlay hcv P G (B.fullAfter hcv P G fe t) t = w t := by
      dsimp only [w,AdaptiveBase.adaptivePlay,g]
      rw [B.fullAfter_eq hcv P G fe t]
    have hv := boundedSubgradient_spec (hf i).1 (hf i).2 (e (w t).val) (e x)
    change f i (e (w t).val) - f i (e x) ≤ _
    rw [show g t = (boundedSubgradient G (f i) (e (w t).val)).ofLp by
      dsimp only [g,AdaptiveBase.fullFeedback]; rw [hw,heq]]
    change _ ≤ dotProduct ((boundedSubgradient G (f i) (e (w t).val)).ofLp) ((w t).val-x)
    rw [euclidean_inner,WithLp.ofLp_sub] at hv
    exact hv
  have hreg := adaptiveBudget_bound B hc hcv hnon (I.adaptiveBase_cost hnon.nonempty hc hcv)
    hG' P hT f (fun i => (hf i).2.continuous) g (B.fullFeedback_norm hcv P G fe) hsub
  let R := (∑ t : Fin T, f t (e (w t.val).val)) - FullInfoLearner.bestLoss (e '' K) f
  have hR (ω : Ω) : L.regret f ω = R := by
    dsimp only [FullInfoLearner.regret,R]
    simp only [L, AdaptiveBase.fullInfoLearner_predict_eq, w, g, fe]
  have hconst := funext hR
  rw [hconst]
  constructor
  · exact integrable_const _
  · rw [integral_const, probReal_univ, one_smul]
    exact hreg.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left hb (mul_nonneg hG'.le hW.le)))) adaptiveWidthConstant_pos.le)


private theorem coordinateDomain_spec {S : Set E} (hc : IsCompact S)
    (hcv : Convex ℝ S) (hnon : S.Nontrivial) :
    let K : Set (Vec d) := e ⁻¹' S
    IsCompact K ∧ Convex ℝ K ∧ K.Nontrivial ∧ e '' K = S := by
  let K : Set (Vec d) := e ⁻¹' S
  have hK : K = (e).symm '' S := by
    ext x
    constructor
    · intro hx
      exact ⟨e x,hx,(e).symm_apply_apply x⟩
    · rintro ⟨y,hy,rfl⟩
      change e ((e).symm y) ∈ S
      rwa [(e).apply_symm_apply]
  have hcK : IsCompact K := hK ▸ hc.image (e).symm.continuous
  have hcvK : Convex ℝ K := hcv.linear_preimage (e).toLinearMap
  have hnK : K.Nontrivial := by
    obtain ⟨x,hx,y,hy,hxy⟩ := hnon
    exact ⟨(e).symm x, hK ▸ Set.mem_image_of_mem _ hx,
      (e).symm y, hK ▸ Set.mem_image_of_mem _ hy, fun he => hxy ((e).symm.injective he)⟩
  have himage : e '' K = S := by
    rw [hK, Set.image_image]
    have hf : (fun x : E => e ((e).symm x)) = id := funext (ContinuousLinearEquiv.apply_symm_apply (e))
    rw [hf,Set.image_id]
  exact ⟨hcK, hcvK, hnK, himage⟩

/-- The same strategy, with the domain written directly in Euclidean space. -/
theorem adaptiveFullInfoUpper_ofInitialization {S : Set E} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hc : IsCompact S) (hcv : Convex ℝ S) (hnon : S.Nontrivial)
    (I : DomainInitialization (e ⁻¹' S)) (G : ℝ≥0) (hG : 0 < G) :
    ∃ L : FullInfoLearner E Ω S,
      ∀ {T : ℕ}, 0 < T → ∀ (f : Fin T → E → ℝ),
        (∀ t, ConvexOn ℝ Set.univ (f t) ∧ LipschitzWith G (f t)) →
        ∀ b : ℝ, FullInfoLearner.comparatorBudget S f ≤ b →
          Integrable (L.regret f) μ ∧
            (∫ ω, L.regret f ω ∂μ) ≤ adaptiveWidthConstant *
              ((G:ℝ)*subexponentialWidth S + Real.sqrt ((G:ℝ)*subexponentialWidth S*b)) := by
  let K : Set (Vec d) := e ⁻¹' S
  obtain ⟨hcK, hcvK, hnK, himage⟩ := coordinateDomain_spec hc hcv hnon
  have hu := adaptiveFullInfo_upper_ofInitialization μ hcK hcvK hnK I G hG
  change ∃ L : FullInfoLearner E Ω (e '' K), _ at hu
  have hwidth : coordinateWidth K = subexponentialWidth (e '' K) := rfl
  rw [hwidth, himage] at hu
  exact hu


theorem adaptiveFullInfoUpper {S : Set E} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hc : IsCompact S) (hcv : Convex ℝ S) (hnon : S.Nontrivial)
    (G : ℝ≥0) (hG : 0 < G) :
    ∃ L : FullInfoLearner E Ω S,
      ∀ {T : ℕ}, 0 < T → ∀ (f : Fin T → E → ℝ),
        (∀ t, ConvexOn ℝ Set.univ (f t) ∧ LipschitzWith G (f t)) →
        ∀ b : ℝ, FullInfoLearner.comparatorBudget S f ≤ b →
          Integrable (L.regret f) μ ∧
            (∫ ω, L.regret f ω ∂μ) ≤ adaptiveWidthConstant *
              ((G:ℝ)*subexponentialWidth S + Real.sqrt ((G:ℝ)*subexponentialWidth S*b)) := by
  obtain ⟨hcK, _, hnK, _⟩ := coordinateDomain_spec hc hcv hnon
  exact adaptiveFullInfoUpper_ofInitialization μ hc hcv hnon (DomainInitialization.general hcK hnK) G hG


private def padGradients {T : ℕ} (g : Fin T → E) (t : ℕ) : Vec d :=
  if h : t<T then (g ⟨t,h⟩).ofLp else 0


theorem adaptiveOneSubgradientOnCoords_ofInitialization (hc : IsCompact K) (hcv : Convex ℝ K)
    (hnon : K.Nontrivial) (I : DomainInitialization K) (G : ℝ≥0) (hG : 0 < G) :
    OneSubgradientUpper (e '' K) G adaptiveWidthConstant := by
  let W := coordinateWidth K
  let P := exactAdaptiveWeights (adaptiveWidthScale G W)
  let B := I.adaptiveBase hnon.nonempty hc hcv
  let S := e '' K
  let play (t : ℕ) (past : Fin t → E) : S :=
    ⟨e (B.adaptivePlay hcv P G (padGradients past) t).val,
      Set.mem_image_of_mem _ (B.adaptivePlay hcv P G (padGradients past) t).prop⟩
  refine ⟨play, ?_⟩
  intro T hT f hf gg hgg
  dsimp only
  intro hsub b hb
  let g := padGradients gg
  let w := B.adaptivePlay hcv P G g
  have hG' : 0 < (G:ℝ) := hG
  have hW : 0 < W := coordinateWidth_pos_of_nontrivial hc hnon
  have hg (i : ℕ) : norm₂ (g i) ≤ G := by
    by_cases hi : i<T
    · dsimp only [g,padGradients]
      rw [dif_pos hi, ← euclidean_norm]
      exact hgg _
    · have h0 : norm₂ (0 : Vec d) = 0 := by simp [norm₂]
      simpa only [g,padGradients,dif_neg hi,h0] using G.coe_nonneg
  have hplay (t : Fin T) : (play t.val (pastGradients gg t)).val = e (w t.val).val := by
    change e (B.adaptivePlay hcv P G (padGradients (pastGradients gg t)) t.val).val = e (w t.val).val
    apply congrArg (fun v : K => e v.val)
    apply B.adaptivePlay_prefix
    intro i hi
    simp [g,padGradients,pastGradients,hi,hi.trans t.isLt]
  have hsupport (t : Fin T) (u : Vec d) (hu : u ∈ K) :
      f t (e (w t.val).val)-f t (e u) ≤ excess (g t.val) (w t.val).val u := by
    have ht := hsub t (e u) (Set.mem_image_of_mem e hu)
    rw [hplay t, euclidean_inner,WithLp.ofLp_sub] at ht
    change _ ≤ dotProduct (g t.val) ((w t.val).val-u)
    have heq : g t.val = (gg t).ofLp := by simp [g,padGradients,t.isLt]
    rw [heq]
    exact ht
  have h := adaptiveBudget_bound B hc hcv hnon (I.adaptiveBase_cost hnon.nonempty hc hcv)
    hG' P hT f (fun t => (hf t).2.continuous) g hg hsupport
  simp_rw [hplay]
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left hb (mul_nonneg hG'.le hW.le)))) adaptiveWidthConstant_pos.le)

theorem adaptiveOneSubgradientUpper_ofInitialization {S : Set E} (hc : IsCompact S) (hcv : Convex ℝ S)
    (hnon : S.Nontrivial) (I : DomainInitialization (e ⁻¹' S)) (G : ℝ≥0) (hG : 0 < G) :
    OneSubgradientUpper S G adaptiveWidthConstant := by
  obtain ⟨hcK, hcvK, hnK, himage⟩ := coordinateDomain_spec hc hcv hnon
  have h := adaptiveOneSubgradientOnCoords_ofInitialization hcK hcvK hnK I G hG
  rwa [himage] at h

theorem adaptiveOneSubgradientUpper {S : Set E} (hc : IsCompact S) (hcv : Convex ℝ S)
    (hnon : S.Nontrivial) (G : ℝ≥0) (hG : 0 < G) :
    OneSubgradientUpper S G adaptiveWidthConstant := by
  obtain ⟨hcK, _, hnK, _⟩ := coordinateDomain_spec hc hcv hnon
  exact adaptiveOneSubgradientUpper_ofInitialization hc hcv hnon (DomainInitialization.general hcK hnK) G hG

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory
namespace Curvature
universe u v

variable {d : ℕ}


attribute [instance] MinimaxStrategy.measurable MinimaxStrategy.probability


namespace CausalLossPolicy
variable {Ξ Ω : Type*} [MeasurableSpace Ω] {K : Set (Sparse.Space d)}
    (P : CausalLossPolicy (Sparse.Space d) Ξ) (L : FullInfoLearner (Sparse.Space d) Ω K)


def oblivious {T : ℕ} (f : Fin T → (Sparse.Space d) → ℝ) : CausalLossPolicy (Sparse.Space d) Ξ :=
  fun t _ _ _ _ => if h : t<T then f ⟨t,h⟩ else 0

theorem oblivious_play {T : ℕ} (f : Fin T → (Sparse.Space d) → ℝ) (ω : Ω) (ξ : Ξ) :
    (oblivious (Ξ:=Ξ) f).play L ω ξ T = f := by
  have h (n : ℕ) (hn : n ≤ T) : (oblivious (Ξ:=Ξ) f).play L ω ξ n = fun i : Fin n => f (i.castLE hn) := by
    induction n with
    | zero => funext i; exact Fin.elim0 i
    | succ n ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [play,oblivious,show n<T by omega]; rfl
      · change Fin.snoc (α:=fun _ => Sparse.Space d → ℝ) ((oblivious f).play L ω ξ n) _ j.castSucc = _
        rw [Fin.snoc_castSucc,ih (by omega)]
        rfl
  exact h T le_rfl

end CausalLossPolicy


attribute [instance] MinimaxEnvironment.measurable MinimaxEnvironment.probability

theorem FullInfoLearner.abs_regret_le_diam {Ω : Type*} [MeasurableSpace Ω] {K : Set (Sparse.Space d)}
    (L : FullInfoLearner (Sparse.Space d) Ω K) (hc : IsCompact K) (hn : K.Nonempty)
    {T : ℕ} (f : Fin T → Sparse.Space d → ℝ) {G : ℝ≥0} (hf : ∀ t, LipschitzWith G (f t)) (ω : Ω) :
    |L.regret f ω| ≤ (T:ℝ)*((G:ℝ)*Metric.diam K) := by
  let F := fun x => ∑ t, f t x
  have hF : Continuous F := continuous_finsetSum _ (fun t _ => (hf t).continuous)
  obtain ⟨u,hu,hmin⟩ := hc.exists_isMinOn hn hF.continuousOn
  have best : FullInfoLearner.bestLoss K f = ∑ t, f t u := by
    change sInf (F '' K) = F u
    apply IsLeast.csInf_eq
    refine ⟨⟨u,hu,rfl⟩,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact hmin hx
  let w := fun t : Fin T => L.predict t.val (FullInfoLearner.pastLosses f t) ω
  have hw (t : Fin T) : w t ∈ K := L.mem ..
  have h (t : Fin T) : |f t (w t)-f t u| ≤ (G:ℝ)*Metric.diam K := by
    rw [← Real.dist_eq]
    exact ((hf t).dist_le_mul (w t) u).trans
      (mul_le_mul_of_nonneg_left (Metric.dist_le_diam_of_mem hc.isBounded (hw t) hu) G.coe_nonneg)
  change |(∑ t, f t (w t))-FullInfoLearner.bestLoss K f| ≤ _
  rw [best, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (by simpa using Finset.sum_le_sum (s:=Finset.univ) (fun t _ => h t))

theorem MinimaxEnvironment.integrable {K : Set (Sparse.Space d)} {S : MinimaxStrategy K} {G : ℝ≥0} {b : ℝ}
    (A : MinimaxEnvironment S G b) (hc : IsCompact K) (hn : K.Nonempty) :
    Integrable (fun z : S.Seed × A.Seed => S.learner.regret (A.policy.play S.learner z.1 z.2 A.T) z.1)
      (S.law.prod A.law) := by
  apply (integrable_const ((A.T:ℝ)*((G:ℝ)*Metric.diam K))).mono' A.measurablePayoff
  apply Filter.Eventually.of_forall
  intro z
  exact S.learner.abs_regret_le_diam hc hn _ (fun t => (A.losses z.1 z.2 t).2) z.1


private def obliviousEnvironment {K : Set (Sparse.Space d)} (S : MinimaxStrategy.{u} K) {G : ℝ≥0} {b : ℝ}
    {T : ℕ} (hT : 0<T) (f : Fin T → (Sparse.Space d) → ℝ) (hf : ∀ t, ConvexOn ℝ Set.univ (f t) ∧ LipschitzWith G (f t))
    (hb : FullInfoLearner.comparatorBudget K f ≤ b) (hi : Integrable (S.learner.regret f) S.law) :
    MinimaxEnvironment.{u,v} S G b where
  T := T
  horizon_pos := hT
  Seed := PUnit
  law := Measure.dirac PUnit.unit
  policy := CausalLossPolicy.oblivious f
  losses := fun ω ξ => by rw [CausalLossPolicy.oblivious_play]; exact hf
  budget := fun ω ξ => by rw [CausalLossPolicy.oblivious_play]; exact hb
  measurablePayoff := by
    simp_rw [CausalLossPolicy.oblivious_play]
    exact (hi.comp_fst _).aestronglyMeasurable

theorem minimaxValue_lower {K : Set (Sparse.Space d)} (hK : CanonicalDomain d K) (G : ℝ≥0) (hG : 0<G) (b : ℝ) (hb : 0≤b) :
    let W := (G:ℝ)*subexponentialWidth K
    ((W+Real.sqrt (W*b))/20480 : ℝ) ≤ minimaxValue.{u,v} K G b := by
  dsimp only
  apply le_iInf
  intro S
  obtain ⟨T,hT,f,hf,hb',hi,hr⟩ := minimaxLower hK S.learner S.law G hG b hb
  let A : MinimaxEnvironment.{u,v} S G b := obliviousEnvironment S hT f hf hb' hi
  have hpay : A.payoff = ∫ ω, S.learner.regret f ω ∂S.law := by
    unfold MinimaxEnvironment.payoff
    change (∫ z : S.Seed × PUnit, S.learner.regret ((CausalLossPolicy.oblivious f).play S.learner z.1 z.2 T) z.1
      ∂S.law.prod (Measure.dirac PUnit.unit)) = _
    simp only [CausalLossPolicy.oblivious_play,integral_fun_fst,probReal_univ,one_smul]
  exact (EReal.coe_le_coe (hr.trans_eq hpay.symm)).trans (le_iSup (fun A : MinimaxEnvironment.{u,v} S G b => (A.payoff:EReal)) A)


theorem minimaxValue_upper {K : Set (Sparse.Space d)} (hc : IsCompact K) (hcv : Convex ℝ K)
    (hnon : K.Nontrivial) (G : ℝ≥0) (hG : 0<G) (b : ℝ) :
    let W := (G:ℝ)*subexponentialWidth K
    minimaxValue.{u,v} K G b ≤ (adaptiveWidthConstant*(W+Real.sqrt (W*b)) : ℝ) := by
  dsimp only
  let μ := Measure.dirac (PUnit.unit : PUnit.{u+1})
  obtain ⟨L,hL⟩ := adaptiveFullInfoUpper μ hc hcv hnon G hG
  let S : MinimaxStrategy.{u} K := ⟨PUnit,μ,L⟩
  let W := (G:ℝ)*subexponentialWidth K
  let B := adaptiveWidthConstant*(W+Real.sqrt (W*b))
  have hpath {T : ℕ} (hT : 0<T) (f : Fin T → Sparse.Space d → ℝ)
      (hf : ∀ t, ConvexOn ℝ Set.univ (f t) ∧ LipschitzWith G (f t))
      (hb : FullInfoLearner.comparatorBudget K f ≤ b) (ω : S.Seed) : S.learner.regret f ω ≤ B := by
    have h := (hL hT f hf b hb).2
    rw [show μ = Measure.dirac PUnit.unit from rfl,integral_dirac] at h
    cases ω
    exact h
  apply (iInf_le (fun S : MinimaxStrategy.{u} K =>
    ⨆ A : MinimaxEnvironment.{u,v} S G b, (A.payoff:EReal)) S).trans
  apply iSup_le
  intro A
  apply EReal.coe_le_coe
  change (∫ z : S.Seed × A.Seed, S.learner.regret (A.policy.play S.learner z.1 z.2 A.T) z.1 ∂S.law.prod A.law) ≤ B
  have h := integral_mono (A.integrable hc hnon.nonempty) (integrable_const B)
    (fun z => hpath A.horizon_pos _ (A.losses z.1 z.2) (A.budget z.1 z.2) z.1)
  simpa only [integral_const,probReal_univ,one_smul] using h


end Curvature
end
end

set_option autoImplicit false
noncomputable section
open Curvature
open MeasureTheory
universe u v
open scoped BigOperators NNReal
variable {d : ℕ}

theorem solution {K : Set (Sparse.Space d)} (hK : CanonicalDomain d K) (G : ℝ≥0) (hG : 0<G)
    (b : ℝ) (hb : 0≤b) :
    let W := (G:ℝ)*subexponentialWidth K
    let rate := W+Real.sqrt (W*b)
    ((rate/20480 : ℝ) : EReal) ≤ minimaxValue.{u,v} K G b ∧
      minimaxValue.{u,v} K G b ≤ ((adaptiveWidthConstant*rate : ℝ):EReal) ∧
      OneSubgradientUpper K G adaptiveWidthConstant ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (L : FullInfoLearner (Sparse.Space d) Ω K)
        (μ : Measure Ω) [IsProbabilityMeasure μ], L.HasHardSequence μ G b (rate/20480) := by
  obtain ⟨hc,hcv,hnon⟩ := hK.properties
  exact ⟨minimaxValue_lower hK G hG b hb,minimaxValue_upper hc hcv hnon G hG b,
    adaptiveOneSubgradientUpper hc hcv hnon G hG,
    fun L μ _ => minimaxLower hK L μ G hG b hb⟩
