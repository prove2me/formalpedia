-- Prove2me | solution 1 for Curvature.contextualSearch
-- status  : ACCEPTED   (prove)
-- author  : @ssakaue
-- created : 2026-11-24T07:36:03.255997+00:00
-- url     : https://prove2.me/submissions/1bb37549-9dc8-4ae7-a9ea-0db3fd942fa8

import Definitions.Def_Curvature_ContextualSearch
import Theorems.Thm_Curvature_adaptiveWidth

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
open MeasureTheory
namespace Curvature.ContextualSearch

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω}


theorem integrable_of_abs_le {μ : @Measure Ω mΩ} {f : Ω → ℝ}
    [IsFiniteMeasure μ] (hf : @Measurable Ω ℝ mΩ _ f) (C : ℝ)
    (h : ∀ ω, |f ω| ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using h ω)

/-- A lower bound on the conditional probability of a correct comparison
implies a lower bound on the conditional mean of the signed error.
The sign may take either value when the error is zero. -/
theorem conditional_drift (hm : m ≤ mΩ) (μ : @Measure Ω mΩ) [IsProbabilityMeasure μ]
    {error bit sign : Ω → ℝ}
    (herror : @Measurable Ω ℝ m _ error)
    (hsign : @Measurable Ω ℝ m _ sign)
    (hbit : @Measurable Ω ℝ mΩ _ bit)
    (hbit_values : ∀ ω, bit ω = -1 ∨ bit ω = 1)
    (hsign_values : ∀ ω, sign ω = -1 ∨ sign ω = 1)
    (hsign_correct : ∀ ω, sign ω * error ω = |error ω|)
    (C : ℝ) (hbound : ∀ ω, |error ω| ≤ C)
    (κ : ℝ)
    (hbias : ∀ᵐ ω ∂μ, (1 + κ) / 2 ≤ μ[correctComparison bit sign | m] ω) :
    ∀ᵐ ω ∂μ, κ * |error ω| ≤ μ[fun ω => bit ω * error ω | m] ω := by
  let I := correctComparison bit sign
  have hI : @Measurable Ω ℝ mΩ _ I :=
    measurable_const.ite (g := fun _ => 0)
      (measurableSet_eq_fun hbit (hsign.mono hm le_rfl)) measurable_const
  have hI_int : Integrable I μ := integrable_of_abs_le hI 1 (fun ω => by
    simp only [I, correctComparison]
    split <;> norm_num)
  let J : Ω → ℝ := (2 : ℝ) • I - fun _ => 1
  have hJ_scale : @Measurable Ω ℝ mΩ _ ((2 : ℝ) • I) := measurable_const.mul hI
  have hJ : @Measurable Ω ℝ mΩ _ J := hJ_scale.sub measurable_const
  have hJ_abs (ω : Ω) : |J ω| = 1 := by
    simp only [J, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, I, correctComparison]
    split <;> norm_num
  have hJ_int : Integrable J μ := integrable_of_abs_le hJ 1 (fun ω => (hJ_abs ω).le)
  let A := fun ω => |error ω|
  have hA : @Measurable Ω ℝ m _ A := by
    simpa only [A, Real.norm_eq_abs] using (@Measurable.norm ℝ Ω _ _ _ m error herror)
  have hAJ : Integrable (A * J) μ := integrable_of_abs_le
    ((hA.mono hm le_rfl).mul hJ) C (fun ω => by
      simpa only [Pi.mul_apply, abs_mul, hJ_abs, mul_one, A, abs_abs] using hbound ω)
  have hprod : (fun ω => bit ω * error ω) = A * J := by
    funext ω
    change bit ω * error ω = |error ω| * (2 * I ω - 1)
    have he := hsign_correct ω
    rcases hbit_values ω with hb | hb <;> rcases hsign_values ω with hs | hs <;>
      norm_num [I, correctComparison, hb, hs] at he ⊢ <;> linarith only [he]
  have hsub := condExp_sub (hI_int.smul (2 : ℝ)) (integrable_const (μ := μ) (1 : ℝ)) m
  have hscale := condExp_smul (μ := μ) (2 : ℝ) I m
  have hpull := condExp_mul_of_stronglyMeasurable_left hA.stronglyMeasurable hAJ hJ_int
  rw [hprod]
  filter_upwards [hbias, hsub, hscale, hpull] with ω hprob hsubω hscaleω hpullω
  change (1 + κ) / 2 ≤ μ[I | m] ω at hprob
  rw [hpullω]
  change κ * |error ω| ≤ |error ω| * μ[J | m] ω
  change μ[J | m] ω = μ[(2 : ℝ) • I | m] ω - μ[fun _ => (1 : ℝ) | m] ω at hsubω
  rw [hsubω, hscaleω, condExp_const hm]
  change κ * |error ω| ≤ |error ω| * (2 * μ[I | m] ω - 1)
  rw [mul_comm κ]
  exact mul_le_mul_of_nonneg_left (by linarith only [hprob]) (abs_nonneg _)

end Curvature.ContextualSearch
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature.ContextualSearch


def target (a : ℝ) (b : Bool) : ℝ := if b then a else -a


/-- The history has its most recent observation first. Each step draws a fresh flip. -/
def after (k y : ℝ) (p : Strategy) (F : History → ℝ) : ℕ → History → ℝ
  | 0, h => F h
  | t+1, h => branch k (truthBit (p h) y)
      (after k y p F t (false :: h)) (after k y p F t (true :: h))

def blockError (k a : ℝ) (p : Strategy) (b : Bool) (n : ℕ) (h : History) : ℝ :=
  ∑ t ∈ Finset.range n, after k (target a b) p (fun v => |p v - target a b|) t h

theorem branch_const (k : ℝ) (truth : Bool) (c : ℝ) : branch k truth c c = c := by
  unfold branch
  ring

theorem branch_mono {k : ℝ} (hk : |k| ≤ 1) (truth : Bool) {x y x' y' : ℝ}
    (hx : x ≤ x') (hy : y ≤ y') : branch k truth x y ≤ branch k truth x' y' := by
  have hk' := abs_le.mp hk
  cases truth <;> simp only [branch, Bool.false_eq_true, if_false, if_true] <;> gcongr <;> linarith

theorem after_const (k y : ℝ) (p : Strategy) (c : ℝ) (t : ℕ) (h : History) :
    after k y p (fun _ => c) t h = c := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih => simp only [after, ih, branch_const]

theorem after_mono {k : ℝ} (hk : |k| ≤ 1) (y : ℝ) (p : Strategy)
    {F G : History → ℝ} (hFG : ∀ h, F h ≤ G h) (t : ℕ) (h : History) :
    after k y p F t h ≤ after k y p G t h := by
  induction t generalizing h with
  | zero => exact hFG h
  | succ t ih => exact branch_mono hk _ (ih _) (ih _)

private def potential (u v M : ℝ) : ℝ := -5/4 + 2*(u+v) - M*(u^2+v^2)

private theorem terminal_lower (a x u v : ℝ) (ha : 0 ≤ a) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    a * potential u v 1 ≤ (u * |x-a| + v * |x-(-a)|)/2 := by
  have hmin : potential u v 1 ≤ min u v := by
    unfold potential
    apply le_min <;> nlinarith only [sq_nonneg (u-1/2), sq_nonneg (v-1),
      sq_nonneg (u-1), sq_nonneg (v-1/2)]
  have hdist : 2*a ≤ |x-a| + |x-(-a)| := by grind [neg_abs_le, le_abs_self]
  have hw := mul_le_mul_of_nonneg_left hdist (le_min hu hv)
  have h₁ := mul_le_mul_of_nonneg_right (min_le_left u v) (abs_nonneg (x-a))
  have h₂ := mul_le_mul_of_nonneg_right (min_le_right u v) (abs_nonneg (x-(-a)))
  nlinarith only [hw,h₁,h₂,mul_le_mul_of_nonneg_left hmin ha]

private theorem two_laws (a k : ℝ) (ha : 0 ≤ a) (hk : |k| ≤ 1) (p : Strategy)
    (t : ℕ) (h : History) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    a * potential u v ((1+k^2)^t) ≤
    (u * after k a p (fun l => |p l-a|) t h +
     v * after k (-a) p (fun l => |p l-(-a)|) t h)/2 := by
  induction t generalizing h u v with
  | zero => simpa only [pow_zero, after] using terminal_lower a (p h) u v ha hu hv
  | succ t ih =>
    let s := if truthBit (p h) a then k else -k
    let r := if truthBit (p h) (-a) then k else -k
    have hs : |s| ≤ 1 := by dsimp [s]; split <;> simpa using hk
    have hr : |r| ≤ 1 := by dsimp [r]; split <;> simpa using hk
    have hs₂ : s^2=k^2 := by dsimp [s]; split <;> ring
    have hr₂ : r^2=k^2 := by dsimp [r]; split <;> ring
    have lf := ih (false :: h) (u*(1-s)) (v*(1-r))
      (mul_nonneg hu (by linarith [(abs_le.mp hs).2]))
      (mul_nonneg hv (by linarith [(abs_le.mp hr).2]))
    have rt := ih (true :: h) (u*(1+s)) (v*(1+r))
      (mul_nonneg hu (by linarith [(abs_le.mp hs).1]))
      (mul_nonneg hv (by linarith [(abs_le.mp hr).1]))
    have he : potential (u*(1-s)) (v*(1-r)) ((1+k^2)^t) +
        potential (u*(1+s)) (v*(1+r)) ((1+k^2)^t) =
        2 * potential u v ((1+k^2)^(t+1)) := by
      unfold potential
      rw [pow_succ (1+k^2)]
      ring_nf
      simp only [hs₂, hr₂]
    simp only [after, branch]
    change _ ≤ (u * (((1-s)*_ + (1+s)*_)/2) + v * (((1-r)*_ + (1+r)*_)/2))/2
    linarith only [lf,rt,congrArg (fun z : ℝ => a*z) he]

private theorem moment_le {k : ℝ} {t : ℕ} (h : (t : ℝ)*k^2 ≤ 1/16) :
    (1+k^2)^t ≤ 9/8 := by
  have hb : ∀ n : ℕ, (n : ℝ)*k^2 ≤ 1/16 →
      (1+k^2)^n*(1-(n : ℝ)*k^2) ≤ 1 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      intro hn
      push_cast at hn ⊢
      have hn' : (n : ℝ)*k^2 ≤ 1/16 := by nlinarith [sq_nonneg k]
      have hs : (1+k^2)*(1-(n+1)*k^2) ≤ 1-n*k^2 := by
        nlinarith only [mul_nonneg (by positivity : 0 ≤ (n:ℝ)+1) (sq_nonneg (k^2))]
      rw [pow_succ, mul_assoc]
      exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans (ih hn')
  have hz := hb t h
  have hnon : 0 ≤ (1+k^2)^t := by positivity
  nlinarith only [hz,mul_nonneg hnon (sub_nonneg.mpr h)]

theorem round_lower {k a : ℝ} (ha : 0 ≤ a) (hk : |k| ≤ 1) (p : Strategy) (t : ℕ)
    (ht : (t : ℝ)*k^2 ≤ 1/16) (h : History) :
    a/2 ≤ (after k a p (fun l => |p l - a|) t h +
      after k (-a) p (fun l => |p l - (-a)|) t h)/2 := by
  have hl := two_laws a k ha hk p t h 1 1 zero_le_one zero_le_one
  simp only [one_mul, potential, one_pow] at hl
  nlinarith only [hl, mul_le_mul_of_nonneg_left (moment_le ht) ha]

theorem block_lower {k a : ℝ} (ha : 0 ≤ a) (hk : |k| ≤ 1) (p : Strategy) (n : ℕ)
    (hn : ∀ t < n, (t : ℝ)*k^2 ≤ 1/16) (h : History) :
    n*a/2 ≤ (blockError k a p true n h + blockError k a p false n h)/2 := by
  have hsum := Finset.sum_le_sum (s := Finset.range n)
    (fun t ht => round_lower ha hk p t (hn t (Finset.mem_range.mp ht)) h)
  simp only [← Finset.sum_div, Finset.sum_add_distrib] at hsum
  simpa [blockError, target, mul_div_assoc] using hsum

end Curvature.ContextualSearch
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace NNReal
namespace Curvature.Coordinate

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


def axesLength (a : Fin r → ℝ) : ℝ := Real.sqrt (∑ i, (a i)^2)

def inscribed (a : Fin r → ℝ) (i : Fin r) : ℝ := (a i)^2 / axesLength a

theorem length_pos [NeZero r] {a : Fin r → ℝ} (ha : ∀ i, 0 < a i) :
    0 < axesLength a := by
  apply Real.sqrt_pos.mpr
  exact Finset.sum_pos (fun i _ => sq_pos_of_pos (ha i)) Finset.univ_nonempty


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


theorem vertex_mem (c : E) (U : Axes r →ₗᵢ[ℝ] E) {a : Fin r → ℝ}
    (ha : ∀ i, 0 ≤ a i) (σ : Fin r → Bool) : vertex c U a σ ∈ box c U a := by
  refine ⟨_, ?_, rfl⟩
  intro i
  simp [abs_mul, abs_of_nonneg (ha i)]


end Curvature.Coordinate
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
namespace Curvature.ContextualSearch

/-- Expected total absolute error conditional on all target signs and on the strategy's seed.
    Coordinate 0 is presented first, and each coordinate is presented for n rounds. -/
def totalError (k a : ℝ) (p : Strategy) (n : ℕ) : (d : ℕ) → (Fin d → Bool) → History → ℝ
  | 0, _, _ => 0
  | d+1, σ, h =>
    blockError k a p (σ 0) n h +
    after k (target a (σ 0)) p (totalError k a p n d (Fin.tail σ)) n h

private theorem after_expect {I : Type*} [Fintype I] (k y : ℝ) (p : Strategy)
    (f : I → History → ℝ) (t : ℕ) (h : History) :
    (𝔼 i, after k y p (f i) t h) = after k y p (fun v => 𝔼 i, f i v) t h := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    simp only [after, branch, ← Finset.expect_div, Finset.expect_add_distrib, ← Finset.mul_expect, ih]

private theorem expect_signs {d : ℕ} (f : (Fin (d+1) → Bool) → ℝ) :
    (𝔼 σ, f σ) = ((𝔼 τ, f (Fin.cons true τ)) + 𝔼 τ, f (Fin.cons false τ))/2 := by
  let e := Fin.consEquiv (fun _ : Fin (d+1) => Bool)
  have he := Fintype.expect_equiv e (fun x => f (e x)) f (fun _ => rfl)
  have hp := Finset.expect_product (Finset.univ : Finset Bool)
    (Finset.univ : Finset (Fin d → Bool)) (fun x => f (e x))
  rw [Finset.univ_product_univ] at hp
  rw [← he,hp]
  rw [Fintype.expect_eq_sum_div_card (ι := Bool)]
  simp only [Fintype.sum_bool, Fintype.card_bool, Nat.cast_ofNat]
  rfl

theorem average_total_lower {k a : ℝ} (ha : 0 ≤ a) (hk : |k| ≤ 1) (p : Strategy)
    (n : ℕ) (hn : ∀ t < n, (t : ℝ)*k^2 ≤ 1/16) (d : ℕ) (h : History) :
    d*(n*a/2) ≤ 𝔼 σ, totalError k a p n d σ h := by
  induction d generalizing h with
  | zero => simp [totalError]
  | succ d ih =>
    rw [expect_signs]
    have hrec (b : Bool) :
        d*(n*a/2) ≤ after k (target a b) p (fun v => 𝔼 τ, totalError k a p n d τ v) n h := by
      rw [← after_const k (target a b) p (d*(n*a/2)) n h]
      exact after_mono hk _ p ih n h
    simp only [totalError, Fin.cons_zero, Fin.tail_cons, Finset.expect_add_distrib,
      Fintype.expect_const, after_expect]
    push_cast
    linarith only [hrec true, hrec false, block_lower ha hk p n hn h]

variable {Ω : Type*} [MeasurableSpace Ω]


private theorem after_integrable (μ : Measure Ω) (L : Learner Ω) (k y : ℝ)
    (f : Ω → History → ℝ) (hf : ∀ h, Integrable (fun w => f w h) μ) (n : ℕ) (h : History) :
    Integrable (fun w => after k y (L.query w) (f w) n h) μ := by
  induction n generalizing h with
  | zero => exact hf h
  | succ n ih =>
    let A := fun w => after k y (L.query w) (f w) n (false::h)
    let B := fun w => after k y (L.query w) (f w) n (true::h)
    let D := fun s : ℝ => fun w => ((1-s)*A w+(1+s)*B w)/2
    have hi (s : ℝ) : Integrable (D s) μ :=
      (((ih (false::h)).const_mul (1-s)).add ((ih (true::h)).const_mul (1+s))).div_const 2
    let S : Set Ω := {w | y ≤ L.query w h}
    have hS : MeasurableSet S := measurableSet_le measurable_const (L.measurable h)
    have he (w : Ω) : after k y (L.query w) (f w) (n+1) h = S.piecewise (D k) (D (-k)) w := by
      by_cases hw : y ≤ L.query w h <;> simp [after, branch, truthBit, Set.piecewise, D, A, B, S, hw]
    simpa only [he] using Integrable.piecewise hS (hi k).integrableOn (hi (-k)).integrableOn

private theorem total_integrable (μ : Measure Ω) [IsProbabilityMeasure μ] (L : Learner Ω)
    (k a : ℝ) (n d : ℕ) (σ : Fin d → Bool) (h : History) :
    Integrable (fun w => totalError k a (L.query w) n d σ h) μ := by
  induction d generalizing h with
  | zero => exact integrable_zero _ _ _
  | succ d ih =>
    let y := target a (σ 0)
    have hp (v : History) : Integrable (fun w => L.query w v - y) μ := by
      apply Integrable.sub _ (integrable_const y)
      apply (integrable_const (1 : ℝ)).mono' (L.measurable v).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun w => L.bounded w v
    have he : Integrable (fun w => blockError k a (L.query w) (σ 0) n h) μ :=
      integrable_finsetSum _ fun t _ => after_integrable μ L k y _ (fun v => (hp v).abs) t h
    exact he.add (after_integrable μ L k y _ (ih (Fin.tail σ)) n h)

/-- Every seeded causal learner has a single fixed target vector whose expected error
    is large. Integration over the seed occurs after the target signs have been fixed. -/
theorem exists_fixed_target_lower (μ : Measure Ω) [IsProbabilityMeasure μ] (L : Learner Ω)
    {k a : ℝ} (ha : 0 ≤ a) (hk : |k| ≤ 1) (n : ℕ)
    (hn : ∀ t < n, (t : ℝ)*k^2 ≤ 1/16) (d : ℕ) :
    ∃ σ : Fin d → Bool, d*(n*a/2) ≤ ∫ w, totalError k a (L.query w) n d σ [] ∂μ := by
  let f := fun (w : Ω) (σ : Fin d → Bool) => totalError k a (L.query w) n d σ []
  have hi (σ : Fin d → Bool) : Integrable (fun w => f w σ) μ :=
    total_integrable μ L k a n d σ []
  have hm (w : Ω) : d*(n*a/2) ≤ 𝔼 σ, f w σ := average_total_lower ha hk (L.query w) n hn d []
  simp only [Fintype.expect_eq_sum_div_card] at hm
  have ht := integral_mono (μ := μ) (integrable_const (d*(n*a/2)))
    ((integrable_finsetSum _ fun σ _ => hi σ).div_const _) hm
  simp only [integral_const, probReal_univ, one_smul, integral_div, integral_finsetSum _ (fun σ _ => hi σ)] at ht
  rw [← Fintype.expect_eq_sum_div_card] at ht
  obtain ⟨σ, _, hσ⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty ht
  exact ⟨σ,hσ⟩

end Curvature.ContextualSearch
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature.ContextualSearch


def targetSequence {d : ℕ} (a : ℝ) (n : ℕ) (σ : Fin d → Bool) : List ℝ :=
  (List.ofFn σ).flatMap (fun b => List.replicate n (target a b))

private theorem branch_add (k : ℝ) (b : Bool) (x y u v : ℝ) :
    branch k b (x+u) (y+v) = branch k b x y + branch k b u v := by
  unfold branch
  ring

private theorem flip_add_const (k c : ℝ) (n : ℕ) (f : (Fin n → Bool) → ℝ) :
    flipExpectation k n (fun b => c+f b) = c + flipExpectation k n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [flipExpectation, ih, branch_add, branch_const]

private theorem flip_mean_observation (k : ℝ) (x y : ℝ) (f : Bool → ℝ) :
    branch k true (f (observedBit x y false)) (f (observedBit x y true)) =
    branch k (truthBit x y) (f false) (f true) := by
  cases hh : truthBit x y <;> simp [observedBit, hh, branch]
  ring

private def play (k : ℝ) (p : Strategy) : List ℝ → History → ℝ
  | [], _ => 0
  | y::ys, h => |p h-y| + branch k (truthBit (p h) y)
    (play k p ys (false::h)) (play k p ys (true::h))

private theorem play_eq_tape (k : ℝ) (p : Strategy) (ys : List ℝ) (h : History) :
    play k p ys h = flipExpectation k ys.length (fun b => realizedError p ys b h) := by
  induction ys generalizing h with
  | nil => rfl
  | cons y ys ih =>
    simp only [play, List.length_cons, flipExpectation, realizedError, Fin.tail_cons, Fin.cons_zero,
      flip_add_const]
    rw [← ih, ← ih]
    congr 1
    exact (flip_mean_observation k (p h) y (fun bit => play k p ys (bit::h))).symm

private theorem after_sum (k : ℝ) (b : Bool) (n : ℕ) (X Y : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, branch k b (X i) (Y i)) =
    branch k b (∑ i ∈ Finset.range n, X i) (∑ i ∈ Finset.range n, Y i) := by
  simp only [branch, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem play_block (k a : ℝ) (p : Strategy) (b : Bool) (ys : List ℝ) (n : ℕ) (h : History) :
    play k p (List.replicate n (target a b) ++ ys) h =
    blockError k a p b n h + after k (target a b) p (play k p ys) n h := by
  induction n generalizing h with
  | zero => simp [blockError, after]
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, play, ih, branch_add, after]
    rw [← add_assoc]
    congr 1
    unfold blockError
    rw [Finset.sum_range_succ']
    simp only [after]
    rw [after_sum]
    ring

theorem totalError_eq_flipExpectation (k a : ℝ) (p : Strategy) (n d : ℕ)
    (σ : Fin d → Bool) (h : History) :
    totalError k a p n d σ h =
    flipExpectation k (targetSequence a n σ).length
      (fun b => realizedError p (targetSequence a n σ) b h) := by
  rw [← play_eq_tape]
  induction d generalizing h with
  | zero => simp [targetSequence, totalError, play]
  | succ d ih =>
    simp only [totalError, targetSequence, List.ofFn_succ, List.flatMap_cons, play_block]
    change _ + after _ _ _ (fun h' => totalError k a p n d (Fin.tail σ) h') n h =
      _ + after _ _ _ (fun h' => play k p (targetSequence a n (Fin.tail σ)) h') n h
    simp only [ih]

end Curvature.ContextualSearch
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


end Curvature.Coordinate
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


end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature


theorem searchUnitBall_width {d : ℕ} (hd : 0 < d) :
    coordinateWidth (searchUnitBall d) ≤ 2 * Real.sqrt d := by
  let : NeZero d := ⟨hd.ne'⟩
  have hset : (WithLp.toLp 2 '' searchUnitBall d : Set (Sparse.Space d)) = Metric.closedBall 0 1 := by
    ext x
    rw [Metric.mem_closedBall,dist_zero_right,euclidean_norm]
    exact ⟨fun ⟨_,h,rfl⟩ => h,fun h => ⟨x.ofLp,h,rfl⟩⟩
  rw [coordinateWidth,hset,euclideanBall_eq_ellipsoid d 1 zero_lt_one]
  simpa [Coordinate.axesLength] using
    Coordinate.ellipsoid_width_le (0 : Sparse.Space d) LinearIsometry.id (fun _ : Fin d => (1:ℝ))
      (fun _ => zero_lt_one)


end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}

def searchTarget (σ : Fin d → Bool) : Vec d :=
  fun i => (Real.sqrt d)⁻¹ * SignGame.sign (σ i)


theorem searchTarget_mem (hd : 0 < d) (σ : Fin d → Bool) :
    searchTarget σ ∈ searchUnitBall d := by
  have hpos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hsquare (i : Fin d) : SignGame.sign (σ i) ^ 2 = 1 := by
    cases h : σ i <;> norm_num [SignGame.sign]
  change Real.sqrt (∑ i, searchTarget σ i * searchTarget σ i) ≤ 1
  rw [Real.sqrt_le_left zero_le_one]
  simp_rw [← pow_two, searchTarget, mul_pow, hsquare]
  simp [inv_pow, Nat.ne_of_gt hd]

@[simp] theorem searchContext_dot (i : Fin d) (x : Vec d) :
    dotProduct (searchContext i) x = x i := by
  simp [searchContext,dotProduct,Pi.single_apply,ite_mul]

theorem searchContext_mem (i : Fin d) : searchContext i ∈ searchUnitBall d := by
  simp [searchUnitBall,norm₂,searchContext]

theorem searchContext_target (σ : Fin d → Bool) (i : Fin d) :
    dotProduct (searchContext i) (searchTarget σ) =
      (if σ i then 1 / Real.sqrt d else -(1 / Real.sqrt d)) := by
  cases h : σ i <;> simp [searchTarget,SignGame.sign,h]


theorem searchBlockLength_pos (κ : ℝ) : 0 < searchBlockLength κ :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem searchBlockLength_exposure {κ : ℝ} (hk : 0 < κ) {t : ℕ}
    (ht : t < searchBlockLength κ) : (t : ℝ) * κ^2 ≤ 1 / 16 := by
  unfold searchBlockLength at ht
  rcases lt_max_iff.mp ht with ht | ht
  · have : t = 0 := by omega
    simp [this]
  · have h := Nat.floor_le (show 0 ≤ 1 / (16 * κ^2) by positivity)
    have ht' : (t : ℝ) ≤ (⌊1 / (16 * κ^2)⌋₊ : ℕ) := by exact_mod_cast ht.le
    have ht'' := (le_div_iff₀ (show 0 < 16 * κ^2 by positivity)).mp (ht'.trans h)
    linarith

theorem searchBlockLength_lower {κ : ℝ} (hk : 0 < κ) :
    1 / (32 * κ^2) ≤ (searchBlockLength κ : ℝ) := by
  have hf := Nat.lt_floor_add_one (1 / (16 * κ^2))
  have hn0 : 1 ≤ searchBlockLength κ := searchBlockLength_pos κ
  have hn : (1 : ℝ) ≤ (searchBlockLength κ : ℝ) := by exact_mod_cast hn0
  have hfloor0 : ⌊1 / (16 * κ^2)⌋₊ ≤ searchBlockLength κ := le_max_right _ _
  have hfloor : ((⌊1 / (16 * κ^2)⌋₊ : ℕ) : ℝ) ≤ (searchBlockLength κ : ℝ) := by exact_mod_cast hfloor0
  have htwo : 1 / (16 * κ^2) ≤ 2 * (searchBlockLength κ : ℝ) := by linarith
  have h := (div_le_iff₀ (show 0 < 16 * κ^2 by positivity)).mp htwo
  apply (div_le_iff₀ (show 0 < 32 * κ^2 by positivity)).mpr
  linarith

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Curvature.ContextualSearch

variable {d : ℕ}


private theorem abs_unitDot_le_one (x y : searchUnitBall d) :
    |dotProduct x.val y.val| ≤ 1 := by
  have hnorm : norm₂ x.val * norm₂ y.val ≤ 1 := by
    simpa only [one_mul] using
      mul_le_mul x.prop y.prop (norm₂_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hneg := (dotProduct_le_norm₂_mul (-x.val) y.val)
  rw [neg_dotProduct, show norm₂ (-x.val) = norm₂ x.val by
    simp [norm₂, neg_dotProduct, dotProduct_neg]] at hneg
  exact abs_le.mpr ⟨by linarith only [hneg, hnorm],
    (dotProduct_le_norm₂_mul x.val y.val).trans hnorm⟩

theorem predictedResponse_abs_le_one (I : DomainInitialization (searchUnitBall d)) {W : ℝ}
    (P : AdaptiveWeightRule (adaptiveWidthScale 1 W))
    (φ : ℕ → searchUnitBall d) (Y : ℕ → ℝ) (t : ℕ) :
    |predictedResponse I P φ Y t| ≤ 1 := by
  unfold predictedResponse
  exact abs_unitDot_le_one _ _

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]


omit mΩ in
private theorem measurable_target (φ : ℕ → Ω → searchUnitBall d) (u : searchUnitBall d)
    (t : ℕ) (m : MeasurableSpace Ω)
    (hφ : @Measurable Ω (searchUnitBall d) m _ (φ t)) :
    @Measurable Ω ℝ m _ (fun ω => dotProduct (φ t ω).val u.val) := by
  unfold dotProduct
  apply Finset.measurable_sum
  intro i _
  exact (Measurable.comp (measurable_pi_apply i) hφ.subtype_coe).mul measurable_const

private theorem linearized_le_young {C W A κ : ℝ}
    (hW : 0 < W) (hA : 0 ≤ A) (hκ : 0 < κ) :
    C * (W + Real.sqrt (W*A)) ≤ κ/2*A + (C*W+C^2*W/(2*κ)) := by
  let s := Real.sqrt (W*A)
  have hs : s^2 = W*A := Real.sq_sqrt (mul_nonneg hW.le hA)
  have hsq : 0 ≤ W * (κ^2*A + C^2*W - 2*κ*C*s) := by
    have heq : W * (κ^2*A + C^2*W - 2*κ*C*s) = (κ*s-C*W)^2 := calc
      _ = κ^2 * (W*A) + C^2*W^2 - 2*κ*C*W*s := by ring
      _ = _ := by nth_rw 1 [← hs]; ring
    rw [heq]
    exact sq_nonneg _
  have hy := nonneg_of_mul_nonneg_right hsq hW
  change C * (W + s) ≤ κ/2*A + (C*W+C^2*W/(2*κ))
  have hκ2 : 0 < 2 * κ := by positivity
  apply (le_of_mul_le_mul_right · hκ2)
  field_simp [hκ.ne']
  nlinarith only [hy]

/-- On any finite horizon, expected absolute prediction error of the adaptive predictor
under the conditional comparison bias in (22). -/
theorem expectedError_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : DomainInitialization (searchUnitBall d)) {W κ : ℝ}
    (hW : 0 < W) (hwidth : coordinateWidth (searchUnitBall d) ≤ W)
    (P : AdaptiveWeightRule (adaptiveWidthScale 1 W))
    (u : searchUnitBall d) (φ : ℕ → Ω → searchUnitBall d) (Y : ℕ → Ω → ℝ)
    (hκ : 0 < κ) (hκ₁ : κ ≤ 1)
    (noise : ComparisonNoise μ κ u φ Y
      (fun t ω => predictedResponse I P (fun s => φ s ω) (fun s => Y s ω) t))
    (T : ℕ) :
    let absError := fun ω => ∑ t ∈ Finset.range T,
      |predictedResponse I P (fun s => φ s ω) (fun s => Y s ω) t -
        dotProduct (φ t ω).val u.val|
    Integrable absError μ ∧
      (∫ ω, absError ω ∂μ) ≤ (2*adaptiveWidthConstant + adaptiveWidthConstant^2)*W/κ^2 := by
  let C := adaptiveWidthConstant
  let error := fun t ω => predictedResponse I P (fun s => φ s ω) (fun s => Y s ω) t -
    dotProduct (φ t ω).val u.val
  let excessLoss := fun t ω => Y t ω * error t ω
  let A := fun ω => ∑ t ∈ Finset.range T, |error t ω|
  let R := fun ω => ∑ t ∈ Finset.range T, excessLoss t ω
  have herror (t : ℕ) : @Measurable Ω ℝ (noise.beforeBit t) _ (error t) :=
    (noise.prediction_measurable t).sub
      (measurable_target φ u t (noise.beforeBit t) (noise.context_measurable t))
  have hbit (t : ℕ) : Measurable (Y t) :=
    (noise.bit_measurable t).mono (noise.beforeBit.le (t+1)) le_rfl
  have habit (t : ℕ) (ω : Ω) : |Y t ω| = 1 := by
    rcases noise.bit_values t ω with h | h <;> rw [h] <;> norm_num
  have hbounded (t : ℕ) (ω : Ω) : |error t ω| ≤ 2 := by
    exact (abs_sub _ _).trans (by
      linarith only [predictedResponse_abs_le_one I P (fun s => φ s ω) (fun s => Y s ω) t,
        abs_unitDot_le_one (φ t ω) u])
  have herrorAmbient (t : ℕ) : Measurable (error t) :=
    (herror t).mono (noise.beforeBit.le t) le_rfl
  have hE_int (t : ℕ) : Integrable (error t) μ :=
    integrable_of_abs_le (herrorAmbient t) 2 (hbounded t)
  have hR_int (t : ℕ) : Integrable (excessLoss t) μ :=
    integrable_of_abs_le ((hbit t).mul (herrorAmbient t)) 2
      (fun ω => by simpa only [excessLoss, abs_mul, habit, one_mul] using hbounded t ω)
  have hA_int : Integrable A μ :=
    integrable_finsetSum _ fun t _ => (hE_int t).abs
  refine ⟨hA_int, ?_⟩
  have hRtotal_int : Integrable R μ := integrable_finsetSum _ fun t _ => hR_int t
  have hmean (t : ℕ) :
      κ * (∫ ω, |error t ω| ∂μ) ≤ ∫ ω, excessLoss t ω ∂μ := by
    have hf := noise.beforeBit.le t
    let _ : IsFiniteMeasure (μ.trim hf) := isFiniteMeasure_trim hf
    have h := conditional_drift hf μ (herror t) (noise.sign_measurable t) (hbit t)
      (noise.bit_values t) (noise.sign_values t) (noise.sign_correct t)
      2 (hbounded t) κ (noise.bias t)
    have hint := integral_mono_ae ((hE_int t).abs.const_mul κ)
      integrable_condExp h
    rw [integral_const_mul, integral_condExp hf] at hint
    exact hint
  have hlow : κ * (∫ ω, A ω ∂μ) ≤ ∫ ω, R ω ∂μ := by
    dsimp only [A, R]
    rw [integral_finsetSum _ (fun t _ => (hE_int t).abs),
      integral_finsetSum _ (fun t _ => hR_int t), Finset.mul_sum]
    exact Finset.sum_le_sum fun t _ => hmean t
  have hA_nonneg (ω : Ω) : 0 ≤ A ω := Finset.sum_nonneg fun t _ => abs_nonneg _
  have hpath (ω : Ω) : R ω ≤ C * (W + Real.sqrt (W*A ω)) := by
    by_cases hT : 0 < T
    · let g := feedback (fun s => φ s ω) (fun s => Y s ω)
      have hg (t : ℕ) : norm₂ (g t) ≤ 1 := by
        simpa only [g, feedback, norm₂_smul, habit, one_mul, searchUnitBall, Set.mem_ofPred_eq]
          using (φ t ω).prop
      let B := I.adaptiveBase (searchUnitBall_nonempty d) (searchUnitBall_compact d)
        (searchUnitBall_convex d)
      let r := fun t => excess (g t) (B.adaptivePlay (searchUnitBall_convex d) P 1 g t).val u.val
      have hr (t : ℕ) : r t = excessLoss t ω := by
        simp only [r, excess, g, feedback, smul_dotProduct, smul_eq_mul, dotProduct_sub,
          excessLoss, error, predictedResponse, B, mul_sub]
      have hn : adaptiveNegative T r ≤ A ω := by
        apply Finset.sum_le_sum
        intro t _
        rw [hr]
        apply max_le
        · exact abs_nonneg _
        · have hh := neg_le_abs (excessLoss t ω)
          simpa only [excessLoss, abs_mul, habit, one_mul] using hh
      have hreg := (adaptiveWidth I (searchUnitBall_compact d) (searchUnitBall_convex d)
        (searchUnitBall_nonempty d) zero_lt_one hW hwidth P g hg T hT u).1
      simp only [one_mul] at hreg
      change (∑ t ∈ Finset.range T, r t) ≤
        C * (W + Real.sqrt (W * adaptiveNegative T r)) at hreg
      simpa only [R, hr] using hreg.trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hn hW.le)))
        adaptiveWidthConstant_pos.le)
    · have hzero : T = 0 := by omega
      simp only [hzero, R, A, Finset.range_zero, Finset.sum_empty, mul_zero, Real.sqrt_zero,
        add_zero]
      exact mul_nonneg adaptiveWidthConstant_pos.le hW.le
  let Bnd := C*W+C^2*W/(2*κ)
  have hupper (ω : Ω) : R ω ≤ κ/2*A ω + Bnd :=
    (hpath ω).trans (linearized_le_young hW (hA_nonneg ω) hκ)
  have hhigh := integral_mono hRtotal_int
    ((hA_int.const_mul (κ/2)).add (integrable_const Bnd)) hupper
  change (∫ ω, R ω ∂μ) ≤ ∫ ω, κ/2*A ω + Bnd ∂μ at hhigh
  rw [integral_add (hA_int.const_mul (κ/2)) (integrable_const Bnd), integral_const_mul,
    integral_const, probReal_univ, one_smul] at hhigh
  change (∫ ω, A ω ∂μ) ≤ (2*C+C^2)*W/κ^2
  apply (le_div_iff₀ (sq_pos_of_pos hκ)).mpr
  have hmid : κ/2 * (∫ ω, A ω ∂μ) ≤ Bnd := by linarith only [hlow, hhigh]
  have hscaled := mul_le_mul_of_nonneg_left hmid (show 0 ≤ 2*κ by positivity)
  dsimp only [Bnd] at hscaled
  field_simp [hκ.ne'] at hscaled
  have hCWκ := mul_le_mul_of_nonneg_left hκ₁
    (show 0 ≤ 2*C*W by
      exact mul_nonneg (mul_nonneg (by norm_num) adaptiveWidthConstant_pos.le) hW.le)
  nlinarith only [hscaled, hCWκ]


end Curvature.ContextualSearch
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Curvature.ContextualSearch

variable {d : ℕ}


variable {Ω : Type*} [MeasurableSpace Ω]


theorem coordinateSchedule_length (d n : ℕ) : (coordinateSchedule d n).length = d*n := by
  simp [coordinateSchedule,List.length_flatMap]

theorem coordinateSchedule_mem {n : ℕ} {x : Vec d} (hx : x ∈ coordinateSchedule d n) :
    x ∈ searchUnitBall d := by
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hx
  exact (List.mem_replicate.mp hi).2 ▸ searchContext_mem i

theorem coordinateSchedule_responses (n : ℕ) (σ : Fin d → Bool) :
    (coordinateSchedule d n).map (fun x => dotProduct x (searchTarget σ)) =
      targetSequence (1/Real.sqrt d) n σ := by
  have he : List.ofFn σ = (List.finRange d).map σ := by simp [List.finRange, List.map_ofFn,Function.comp_def]
  simp only [coordinateSchedule,List.map_flatMap,List.map_replicate,searchContext_target,
    targetSequence,he,List.flatMap_map,target]

/-- For every randomized contextual learner the same fixed schedule admits a fixed hard target. -/
theorem contextualSearchLower (μ : Measure Ω) [IsProbabilityMeasure μ] (L : ContextLearner d Ω)
    (hd : 0 < d) {κ : ℝ} (hk : 0 < κ) (hk' : κ ≤ 1) :
    let n := searchBlockLength κ
    let ctx := coordinateSchedule d n
    0 < ctx.length ∧ (∀ x ∈ ctx, x ∈ searchUnitBall d) ∧
      ∃ u ∈ searchUnitBall d, Real.sqrt d / (64*κ^2) ≤ expectedError μ L κ ctx u := by
  let n := searchBlockLength κ
  let ctx := coordinateSchedule d n
  let a := 1 / Real.sqrt (d : ℝ)
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg d)
  obtain ⟨σ,hσ⟩ := exists_fixed_target_lower μ (L.onSchedule ctx)
    (a:=a) (by dsimp [a]; positivity) (by rwa [abs_of_pos hk]) n
    (fun _ ht => searchBlockLength_exposure hk ht) d
  refine ⟨?_,fun _ h => coordinateSchedule_mem h, searchTarget σ, searchTarget_mem hd σ, ?_⟩
  · rw [coordinateSchedule_length]
    exact Nat.mul_pos hd (searchBlockLength_pos κ)
  · change _ ≤ expectedError μ L κ ctx (searchTarget σ)
    unfold expectedError
    rw [show ctx.map (fun x => dotProduct x (searchTarget σ)) = targetSequence a n σ from
      coordinateSchedule_responses n σ]
    simp_rw [← totalError_eq_flipExpectation]
    apply le_trans ?_ hσ
    have hn : 1/(32*κ^2) ≤ (n : ℝ) := searchBlockLength_lower hk
    dsimp only [a]
    calc
      _ = Real.sqrt d * (1/(32*κ^2)) / 2 := by ring
      _ ≤ Real.sqrt d * n / 2 := by gcongr
      _ = (d : ℝ) * (n * (1 / Real.sqrt d) / 2) := by field_simp; nlinarith [hs2]

end Curvature.ContextualSearch
end
end

set_option autoImplicit false
noncomputable section
open Curvature
open MeasureTheory
universe u v
open Curvature.ContextualSearch

theorem solution {d : ℕ} (hd : 0 < d) {κ : ℝ} (hk : 0 < κ) (hk' : κ ≤ 1) :
    coordinateWidth (searchUnitBall d) ≤ 2*Real.sqrt d ∧
    (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      {W A : ℝ} (_ : 0 < W) (_ : coordinateWidth (searchUnitBall d) ≤ W)
      (_ : W ≤ A*Real.sqrt d) (P : AdaptiveWeightRule (adaptiveWidthScale 1 W))
      (u : searchUnitBall d) (φ : ℕ → Ω → searchUnitBall d) (Y : ℕ → Ω → ℝ),
      let yhat := fun t ω => predictedResponse (searchUnitBall_initialization hd) P
        (fun s => φ s ω) (fun s => Y s ω) t
      ComparisonNoise μ κ u φ Y yhat →
      let err := fun T ω => ∑ t ∈ Finset.range T, |yhat t ω - dotProduct (φ t ω).val u.val|
      let B := (2*adaptiveWidthConstant + adaptiveWidthConstant^2) * A * Real.sqrt d / κ^2
      (∀ T, Integrable (err T) μ ∧ (∫ ω, err T ω ∂μ) ≤ B) ∧ (⨆ T : ℕ, ∫ ω, err T ω ∂μ) ≤ B) ∧
    (∀ {Ω : Type v} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (L : ContextLearner d Ω),
      let ctx := coordinateSchedule d (searchBlockLength κ)
      0 < ctx.length ∧ (∀ x ∈ ctx, x ∈ searchUnitBall d) ∧
        ∃ u ∈ searchUnitBall d, Real.sqrt d / (64*κ^2) ≤ expectedError μ L κ ctx u) := by
  refine ⟨searchUnitBall_width hd, ?_, fun μ _ L => contextualSearchLower μ L hd hk hk'⟩
  intro Ω _ μ _ W A hW hw hA P u φ Y yhat noise
  dsimp only
  have h (T : ℕ) := expectedError_le μ (searchUnitBall_initialization hd) hW hw P u φ Y hk hk' noise T
  have hscale : (2*adaptiveWidthConstant + adaptiveWidthConstant^2)*W/κ^2 ≤
      (2*adaptiveWidthConstant + adaptiveWidthConstant^2)*A*Real.sqrt d/κ^2 := by
    rw [mul_assoc (2*adaptiveWidthConstant + adaptiveWidthConstant^2) A]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left hA (add_nonneg
      (mul_nonneg (by norm_num) adaptiveWidthConstant_pos.le) (sq_nonneg _))
  exact ⟨fun T => ⟨(h T).1, (h T).2.trans hscale⟩, ciSup_le fun T => (h T).2.trans hscale⟩
