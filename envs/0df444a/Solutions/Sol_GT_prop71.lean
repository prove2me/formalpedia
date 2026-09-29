-- Prove2me | solution 1 for GT.prop71
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T11:06:50.765875+00:00
-- url     : https://prove2.me/submissions/0fdba5dd-8260-4f37-b5cb-13e6db917e15

import Mathlib
import Definitions.Def_GreenTaoFourCore
import Theorems.Thm_GT_large_quad
import Theorems.Thm_GT_loc_to_glob
import Theorems.Thm_GT_poor_d2

section File_KM_Bohr
/-!
# Bohr sets in `ZMod N`

We define the circle distance `cn`, Bohr sets `bohr Γ ρ`, prove the basic covering bound
`|bohr Γ ρ| ≤ (4ρ/ρ')^d |bohr Γ ρ'|`, the absolute lower bound `|bohr Γ ρ| ≥ N (ρ/2)^d`, and the
existence of regular radii.
-/

open Finset

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N]

lemma cn_nonneg (z : ZMod N) : 0 ≤ cn z := norm_nonneg _

@[simp] lemma cn_zero : cn (0 : ZMod N) = 0 := by simp [cn]

lemma cn_add_le (a b : ZMod N) : cn (a + b) ≤ cn a + cn b := by
  simp only [cn, map_add]; exact norm_add_le _ _

lemma cn_natCast_mul_le (n : ℕ) (z : ZMod N) : cn ((n : ZMod N) * z) ≤ n * cn z := by
  simp only [cn]
  rw [← nsmul_eq_mul, map_nsmul]
  exact norm_nsmul_le

variable {Γ Γ' : Finset (ZMod N)} {ρ ρ' : ℝ} {x y : ZMod N}

@[simp] lemma mem_bohr : x ∈ bohr Γ ρ ↔ ∀ γ ∈ Γ, cn (γ * x) ≤ ρ := by simp [bohr]

lemma zero_mem_bohr (hρ : 0 ≤ ρ) : (0 : ZMod N) ∈ bohr Γ ρ := by simp [hρ]

lemma bohr_mono (h : ρ ≤ ρ') : bohr Γ ρ ⊆ bohr Γ ρ' := by
  intro x hx
  rw [mem_bohr] at *
  exact fun γ hγ => (hx γ hγ).trans h

lemma bohr_nonempty (hρ : 0 ≤ ρ) : (bohr Γ ρ).Nonempty := ⟨0, zero_mem_bohr hρ⟩

/-! ### The covering bound -/

/-! ### Regularity -/

/-! ### Dilation by a unit -/

end

end KM
end File_KM_Bohr

section File_KM_Conv
/-!
# Convolutions and normalised indicator functions on a finite abelian group
-/

open Finset

namespace KM

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Indicator function of a finset. -/
def ind (S : Finset G) : G → ℝ := fun x => if x ∈ S then 1 else 0

variable {S T A B : Finset G} {f g h : G → ℝ} {x y t : G}

lemma mu_nonneg (S : Finset G) (x : G) : 0 ≤ mu S x := by
  unfold mu; split_ifs <;> positivity

lemma mu_le (S : Finset G) (x : G) : mu S x ≤ (S.card : ℝ)⁻¹ := by
  unfold mu; split_ifs
  · exact le_rfl
  · positivity

lemma mu_eq_inv_mul_ind (S : Finset G) : mu S = fun x => (S.card : ℝ)⁻¹ * ind S x := by
  ext x; unfold mu ind; split_ifs <;> simp

lemma sum_ind (S : Finset G) : ∑ x, ind S x = S.card := by
  unfold ind; rw [sum_ite_mem, univ_inter]; simp

lemma sum_mu (hS : S.Nonempty) : ∑ x, mu S x = 1 := by
  rw [mu_eq_inv_mul_ind]; simp only; rw [← mul_sum, sum_ind]
  have : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  field_simp

/-! ### Reindexing -/

/-! ### Basic properties of convolutions -/

/-! ### Translates of indicator functions -/

end

end KM
end File_KM_Conv

section File_GT_Bohr
/-!
# Regular probability distributions on Bohr sets (Green–Tao §4)

`regP Γ ρ a = 2 ∫_{1/2}^1 μ_{B(Γ, tρ)}(a) dt`, and the approximate translation invariance
(Lemma 4.4): translating by an element of `B(Γ', ρ')`, `Γ ⊆ Γ'`, changes `regP Γ ρ` by at most
`O(|Γ| ρ'/ρ)` in total variation.
-/

open Finset MeasureTheory KM

namespace GT

noncomputable section

variable {N : ℕ} [NeZero N]

/-- A bounded measurable real function is interval integrable. -/
lemma intervalIntegrable_of_bdd {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ t, |f t| ≤ M) (a b : ℝ) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := M) (by simp) hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hM t

variable (Γ : Finset (ZMod N)) {ρ : ℝ}

lemma bohr_mul_mono (hρ : 0 ≤ ρ) : Monotone fun t : ℝ => bohr Γ (t * ρ) :=
  fun _ _ h => bohr_mono (mul_le_mul_of_nonneg_right h hρ)

lemma card_bohr_mul_mono (hρ : 0 ≤ ρ) :
    Monotone fun t : ℝ => ((bohr Γ (t * ρ)).card : ℝ) :=
  fun s t h => by
    try simp only
    exact_mod_cast card_le_card (bohr_mul_mono Γ hρ h)

lemma measurable_mu_bohr (hρ : 0 ≤ ρ) (a : ZMod N) :
    Measurable fun t : ℝ => mu (bohr Γ (t * ρ)) a := by
  have h1 : Measurable fun t : ℝ => ((bohr Γ (t * ρ)).card : ℝ)⁻¹ :=
    (card_bohr_mul_mono Γ hρ).measurable.inv
  have h2 : Measurable fun t : ℝ => KM.ind (bohr Γ (t * ρ)) a := by
    apply Monotone.measurable
    intro s t hst
    simp only [KM.ind]
    by_cases hs : a ∈ bohr Γ (s * ρ)
    · rw [if_pos hs, if_pos (bohr_mul_mono Γ hρ hst hs)]
    · rw [if_neg hs]; split_ifs <;> norm_num
  have e : (fun t : ℝ => mu (bohr Γ (t * ρ)) a) =
      fun t => ((bohr Γ (t * ρ)).card : ℝ)⁻¹ * KM.ind (bohr Γ (t * ρ)) a := by
    funext t; rw [mu_eq_inv_mul_ind]
  rw [e]; exact h1.mul h2

lemma abs_mu_le_one (S : Finset (ZMod N)) (a : ZMod N) : |mu S a| ≤ 1 := by
  rw [abs_of_nonneg (mu_nonneg S a)]
  refine (mu_le S a).trans ?_
  rcases Nat.eq_zero_or_pos S.card with h | h
  · simp [h]
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast h)

lemma intervalIntegrable_mu_bohr (hρ : 0 ≤ ρ) (a : ZMod N) (x y : ℝ) :
    IntervalIntegrable (fun t : ℝ => mu (bohr Γ (t * ρ)) a) volume x y :=
  intervalIntegrable_of_bdd (measurable_mu_bohr Γ hρ a) (fun _ => abs_mu_le_one _ a) x y

lemma regP_nonneg (a : ZMod N) : 0 ≤ regP Γ ρ a := by
  unfold regP
  have := intervalIntegral.integral_nonneg (a := (1 / 2 : ℝ)) (b := 1) (μ := volume)
    (f := fun t => mu (bohr Γ (t * ρ)) a) (by norm_num) (fun t _ => mu_nonneg _ a)
  linarith

lemma sum_regP (hρ : 0 ≤ ρ) : ∑ a, regP Γ ρ a = 1 := by
  unfold regP
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finset_sum
    (fun a _ => intervalIntegrable_mu_bohr Γ hρ a _ _)]
  have : ∀ t ∈ Set.uIcc (1 / 2 : ℝ) 1, ∑ a, mu (bohr Γ (t * ρ)) a = 1 := by
    intro t ht
    have ht0 : 0 ≤ t := by
      rw [Set.uIcc_of_le (by norm_num)] at ht; linarith [ht.1]
    exact sum_mu (bohr_nonempty (mul_nonneg ht0 hρ))
  rw [intervalIntegral.integral_congr this]
  simp; norm_num

end

end GT
end File_GT_Bohr

section File_GT_LocU2
/-!
# The local inverse `U²` theorem (Green–Tao, Theorem 4.10)

We prove the local inverse theorem for the Gowers `U²` norm in the general form: if `P₀, P₁` are
probability distributions on `ZMod N` such that `P₀` is almost invariant under translation by
elements of the support of `P₁` (in total variation, up to `ε`), and a `1`-bounded `f` has
local `U²`-type average at least `η` with `144 ε ≤ η²`, then `f` correlates with a linear phase
on translates of `P₁`.  The proof (due to F. Shao) replaces `P₀` by products of square roots
and then uses Fourier analysis on `ZMod N`.
-/

open Finset ComplexConjugate KM

namespace GT

noncomputable section

variable {N : ℕ} [NeZero N]

/-! ### Fourier identities -/

lemma ofReal_norm_sq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-! ### Elementary estimates -/

/-- Weighted Jensen: `(∑ pᵢ aᵢ)² ≤ ∑ pᵢ aᵢ²` for a probability vector `p`. -/
lemma sq_wavg_le {ι : Type*} [Fintype ι] {p : ι → ℝ} (a : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) : (∑ i, p i * a i) ^ 2 ≤ ∑ i, p i * a i ^ 2 := by
  have := sum_mul_sq_le_sq_mul_sq univ (fun i => √(p i)) (fun i => √(p i) * a i)
  have e1 : ∀ i, √(p i) * (√(p i) * a i) = p i * a i := fun i => by
    rw [← mul_assoc, Real.mul_self_sqrt (hp i)]
  have e2 : ∀ i, √(p i) ^ 2 = p i := fun i => Real.sq_sqrt (hp i)
  have e3 : ∀ i, (√(p i) * a i) ^ 2 = p i * a i ^ 2 := fun i => by rw [mul_pow, e2]
  simp only [e1, e2, e3, hp1, one_mul] at this
  exact this

section dist

variable {P : ZMod N → ℝ} (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1)
include hP hP1

end dist

/-! ### The main estimates -/

section main

end main

end

end GT
end File_GT_LocU2

section File_GT_Prob
/-!
# Common toolkit for the Green–Tao argument

* the exponential `e(x)` of a point of `ℝ/ℤ`, with the bounds `4‖x‖ ≤ |e(x) - 1| ≤ 2π‖x‖`;
* the dual norm `‖h‖_{S^⊥}` (`snorm`) and its relation with Bohr sets;
* support and translation properties of the regular distributions `regP`;
* the local inverse `U²` theorem for regular distributions on Bohr sets.
-/

open Finset ComplexConjugate KM

namespace GT

noncomputable section

/-! ### The exponential on `ℝ/ℤ` -/

lemma ec_add (x y : UnitAddCircle) : ec (x + y) = ec x * ec y := by
  simp [ec, AddCircle.toCircle_add]

lemma ec_neg (x : UnitAddCircle) : ec (-x) = conj (ec x) := by
  rw [ec, ec, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]

@[simp] lemma norm_ec (x : UnitAddCircle) : ‖ec x‖ = 1 := Circle.norm_coe _

variable {N : ℕ} [NeZero N]

/-! ### The dual norm `‖h‖_{S^⊥}` -/

variable {S : Finset (ZMod N)}

lemma snorm_nonneg (h : ZMod N) : 0 ≤ snorm S h := by
  unfold snorm
  split_ifs with hS
  · obtain ⟨s, hs⟩ := hS
    exact (cn_nonneg _).trans (Finset.le_sup' (fun s => cn (s * h)) hs)
  · exact le_rfl

lemma cn_le_snorm {s : ZMod N} (hs : s ∈ S) (h : ZMod N) : cn (s * h) ≤ snorm S h := by
  unfold snorm
  rw [dif_pos ⟨s, hs⟩]
  exact Finset.le_sup' (fun s => cn (s * h)) hs

lemma snorm_le_iff {h : ZMod N} {ρ : ℝ} (hρ : 0 ≤ ρ) : snorm S h ≤ ρ ↔ ∀ s ∈ S, cn (s * h) ≤ ρ := by
  constructor
  · intro H s hs; exact (cn_le_snorm hs h).trans H
  · intro H
    unfold snorm
    split_ifs with hS
    · exact Finset.sup'_le hS _ H
    · exact hρ

lemma mem_bohr_iff_snorm {h : ZMod N} {ρ : ℝ} (hρ : 0 ≤ ρ) : h ∈ bohr S ρ ↔ snorm S h ≤ ρ := by
  rw [mem_bohr, snorm_le_iff hρ]

lemma snorm_le_of_mem {h : ZMod N} {ρ : ℝ} (hh : h ∈ bohr S ρ) (hρ : 0 ≤ ρ) : snorm S h ≤ ρ :=
  (mem_bohr_iff_snorm hρ).mp hh

lemma snorm_add_le (h k : ZMod N) : snorm S (h + k) ≤ snorm S h + snorm S k := by
  rw [snorm_le_iff (add_nonneg (snorm_nonneg _) (snorm_nonneg _))]
  intro s hs
  rw [mul_add]
  exact (cn_add_le _ _).trans (add_le_add (cn_le_snorm hs h) (cn_le_snorm hs k))

@[simp] lemma snorm_zero : snorm S (0 : ZMod N) = 0 := by
  unfold snorm; split_ifs <;> simp

lemma snorm_nsmul_le (n : ℕ) (h : ZMod N) : snorm S ((n : ZMod N) * h) ≤ n * snorm S h := by
  rw [snorm_le_iff (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (snorm_nonneg h))]
  intro s hs
  rw [mul_left_comm]
  exact (cn_natCast_mul_le n _).trans
    (mul_le_mul_of_nonneg_left (cn_le_snorm hs h) (Nat.cast_nonneg (α := ℝ) n))

lemma snorm_mono {S' : Finset (ZMod N)} (hSS : S ⊆ S') (h : ZMod N) : snorm S h ≤ snorm S' h := by
  rw [snorm_le_iff (snorm_nonneg _)]
  exact fun s hs => cn_le_snorm (hSS hs) h

/-! ### Regular distributions -/

lemma regP_eq_zero_of_not_mem {Γ : Finset (ZMod N)} {ρ : ℝ} (hρ : 0 ≤ ρ) {a : ZMod N}
    (ha : a ∉ bohr Γ ρ) : regP Γ ρ a = 0 := by
  unfold regP
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero,
    mul_zero]
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
  try simp only
  have : a ∉ bohr Γ (t * ρ) := fun h' =>
    ha (bohr_mono (by nlinarith [ht.2] : t * ρ ≤ ρ) h')
  simp [mu, this]

lemma mem_bohr_of_regP_ne_zero {Γ : Finset (ZMod N)} {ρ : ℝ} (hρ : 0 ≤ ρ) {a : ZMod N}
    (ha : regP Γ ρ a ≠ 0) : a ∈ bohr Γ ρ := by
  by_contra h; exact ha (regP_eq_zero_of_not_mem hρ h)

lemma regP_isDist (Γ : Finset (ZMod N)) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∀ x, 0 ≤ regP Γ ρ x) ∧ ∑ x, regP Γ ρ x = 1 :=
  ⟨fun x => regP_nonneg Γ x, sum_regP Γ hρ⟩

/-! ### Averages against probability vectors -/

section avg

variable {α : Type*} [Fintype α] {P : α → ℝ}

/-- Pigeonhole: a weighted average is attained or exceeded at a point of positive weight. -/
lemma exists_pos_ge (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1) (F : α → ℝ) {c : ℝ}
    (h : c ≤ ∑ x, P x * F x) : ∃ x, P x ≠ 0 ∧ c ≤ F x := by
  by_contra hc
  push_neg at hc
  obtain ⟨x0, hx0⟩ : ∃ x, P x ≠ 0 := by
    by_contra h'; push_neg at h'; simp [h'] at hP1
  have hlt : ∑ x, P x * F x < ∑ x, P x * c := by
    apply sum_lt_sum
    · intro x _
      by_cases hx : P x = 0
      · rw [hx, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (hc x hx).le (hP x)
    · exact ⟨x0, mem_univ _, mul_lt_mul_of_pos_left (hc x0 hx0)
        (lt_of_le_of_ne (hP x0) (Ne.symm hx0))⟩
  rw [← sum_mul, hP1, one_mul] at hlt
  linarith

end avg

end

end GT
end File_GT_Prob

section File_GT_AddOn
/-!
# Local additivity on Bohr sets

`AddOn S R f` says that `f (x + y) = f x + f y` whenever `‖x‖_{S^⊥} + ‖y‖_{S^⊥} ≤ R`.
Locally linear maps on Bohr sets (and the partial maps of locally bilinear maps) are of this
form; we record how they act on integer combinations.
-/

open Finset KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p] {S : Finset (ZMod p)} {M : Type*} [AddCommGroup M]

namespace AddOn

variable {R : ℝ} {f : ZMod p → M}

lemma mono (h : AddOn S R f) {R' : ℝ} (hR : R' ≤ R) : AddOn S R' f :=
  fun x y hxy => h x y (hxy.trans hR)

lemma neg (h : AddOn S R f) : AddOn S R (fun x => -f x) := fun x y hxy => by
  simp only; rw [h x y hxy, neg_add]

end AddOn

end

end GT
end File_GT_AddOn

section File_GT_LocQ
/-!
# Calculus of locally quadratic maps on shifted Bohr sets

For `Ξ` locally quadratic on `n₀ + B(S, ρ)` we study the second difference
`D2 Ξ a h k = Ξ(a+h+k) - Ξ(a+h) - Ξ(a+k) + Ξ(a)`: it does not depend on the base point and is
additive in each variable (under `S^⊥`-norm budgets).
-/

open Finset KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p] {S : Finset (ZMod p)} {M : Type*} [AddCommGroup M]

lemma mem_sBohr {n0 x : ZMod p} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    x ∈ sBohr S n0 ρ ↔ snorm S (x - n0) ≤ ρ := by
  rw [sBohr, Set.mem_setOf_eq, mem_bohr_iff_snorm hρ]

lemma D2_comm (Ξ : ZMod p → M) (a h k : ZMod p) : D2 Ξ a h k = D2 Ξ a k h := by
  unfold D2; rw [add_right_comm a h k]; abel

lemma LocQuad.comp {B : Set (ZMod p)} {Ξ : ZMod p → M} (hL : LocQuad B Ξ)
    {M' : Type*} [AddCommGroup M'] (f : M →+ M') : LocQuad B (fun x => f (Ξ x)) := by
  intro n h1 h2 h3 m0 m1 m2 m3 m12 m13 m23 m123
  have := hL n h1 h2 h3 m0 m1 m2 m3 m12 m13 m23 m123
  have e := congrArg f this
  simp only [map_add, map_sub, map_zero] at e
  exact e

variable {n0 : ZMod p} {ρ : ℝ} {Ξ : ZMod p → M}

lemma lq_third (hL : LocQuad (sBohr S n0 ρ) Ξ) (hρ : 0 ≤ ρ) {a h1 h2 h3 : ZMod p}
    (hs : snorm S (a - n0) + snorm S h1 + snorm S h2 + snorm S h3 ≤ ρ) :
    Ξ (a + h1 + h2 + h3) - Ξ (a + h1 + h2) - Ξ (a + h1 + h3) - Ξ (a + h2 + h3)
      + Ξ (a + h1) + Ξ (a + h2) + Ξ (a + h3) - Ξ a = 0 := by
  have n1 := snorm_nonneg (S := S) h1
  have n2 := snorm_nonneg (S := S) h2
  have n3 := snorm_nonneg (S := S) h3
  have n0' := snorm_nonneg (S := S) (a - n0)
  have mem : ∀ x : ZMod p, snorm S (x - n0) ≤ ρ → x ∈ sBohr S n0 ρ :=
    fun x hx => (mem_sBohr hρ).2 hx
  have t2 : ∀ u v : ZMod p, snorm S (a + u + v - n0) ≤ snorm S (a - n0) + snorm S u + snorm S v :=
    fun u v => by
      rw [show a + u + v - n0 = (a - n0) + u + v by abel]
      exact (snorm_add_le _ _).trans (add_le_add (snorm_add_le _ _) le_rfl)
  have t1 : ∀ u : ZMod p, snorm S (a + u - n0) ≤ snorm S (a - n0) + snorm S u := fun u => by
    rw [show a + u - n0 = (a - n0) + u by abel]; exact snorm_add_le _ _
  have t3 : snorm S (a + h1 + h2 + h3 - n0) ≤
      snorm S (a - n0) + snorm S h1 + snorm S h2 + snorm S h3 := by
    rw [show a + h1 + h2 + h3 - n0 = (a - n0) + h1 + h2 + h3 by abel]
    exact (snorm_add_le _ _).trans (add_le_add
      ((snorm_add_le _ _).trans (add_le_add (snorm_add_le _ _) le_rfl)) le_rfl)
  refine hL a h1 h2 h3 (mem _ (by linarith)) (mem _ (by linarith [t1 h1]))
    (mem _ (by linarith [t1 h2])) (mem _ (by linarith [t1 h3])) (mem _ (by linarith [t2 h1 h2]))
    (mem _ (by linarith [t2 h1 h3])) (mem _ (by linarith [t2 h2 h3])) (mem _ (by linarith [t3]))

/-- Base-point independence of the second difference. -/
lemma D2_base (hL : LocQuad (sBohr S n0 ρ) Ξ) (hρ : 0 ≤ ρ) {a t h k : ZMod p}
    (hs : snorm S (a - n0) + snorm S t + snorm S h + snorm S k ≤ ρ) :
    D2 Ξ (a + t) h k = D2 Ξ a h k := by
  have := lq_third hL hρ hs
  unfold D2
  rw [← sub_eq_zero, ← this]
  abel

/-- Additivity of the second difference in its first variable. -/
lemma D2_add_left (hL : LocQuad (sBohr S n0 ρ) Ξ) (hρ : 0 ≤ ρ) {a h h' k : ZMod p}
    (hs : snorm S (a - n0) + snorm S h + snorm S h' + snorm S k ≤ ρ) :
    D2 Ξ a (h + h') k = D2 Ξ a h k + D2 Ξ a h' k := by
  have e : D2 Ξ a (h + h') k = D2 Ξ a h k + D2 Ξ (a + h) h' k := by
    unfold D2; rw [← add_assoc a h h']; abel
  rw [e, D2_base hL hρ hs]

lemma D2_add_right (hL : LocQuad (sBohr S n0 ρ) Ξ) (hρ : 0 ≤ ρ) {a h k k' : ZMod p}
    (hs : snorm S (a - n0) + snorm S h + snorm S k + snorm S k' ≤ ρ) :
    D2 Ξ a h (k + k') = D2 Ξ a h k + D2 Ξ a h k' := by
  rw [D2_comm, D2_add_left hL hρ (by linarith), D2_comm Ξ a k, D2_comm Ξ a k']

/-- The partial maps of `D2 Ξ a` are locally additive. -/
lemma addOn_D2_left (hL : LocQuad (sBohr S n0 ρ) Ξ) (hρ : 0 ≤ ρ) (a k : ZMod p) :
    AddOn S (ρ - snorm S (a - n0) - snorm S k) (fun h => D2 Ξ a h k) :=
  fun h h' hs => D2_add_left hL hρ (by linarith)

lemma addOn_D2_right (hL : LocQuad (sBohr S n0 ρ) Ξ) (hρ : 0 ≤ ρ) (a h : ZMod p) :
    AddOn S (ρ - snorm S (a - n0) - snorm S h) (fun k => D2 Ξ a h k) :=
  fun k k' hs => D2_add_right hL hρ (by linarith)

/-- Along a short progression a locally quadratic map is a quadratic polynomial. -/
lemma lq_prog (hL : LocQuad (sBohr S n0 ρ) Ξ) (hρ : 0 ≤ ρ) {a h : ZMod p} (j : ℕ)
    (hs : snorm S (a - n0) + j * snorm S h ≤ ρ) :
    Ξ (a + (j : ZMod p) * h) - Ξ a = j • (Ξ (a + h) - Ξ a) + (j.choose 2) • D2 Ξ a h h := by
  have hsh := snorm_nonneg (S := S) h
  -- consecutive differences
  have hstep : ∀ i : ℕ, i + 2 ≤ j →
      Ξ (a + ((i + 1 : ℕ) : ZMod p) * h) - Ξ (a + (i : ZMod p) * h) =
        (Ξ (a + h) - Ξ a) + i • D2 Ξ a h h := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      have hb : D2 Ξ (a + (i : ZMod p) * h) h h = D2 Ξ a h h := by
        refine D2_base hL hρ (le_trans ?_ hs)
        have : snorm S ((i : ZMod p) * h) ≤ i * snorm S h := snorm_nsmul_le i h
        have hij : (i : ℝ) + 2 ≤ j := by exact_mod_cast (by omega : i + 2 ≤ j)
        nlinarith
      have e : Ξ (a + ((i + 1 + 1 : ℕ) : ZMod p) * h) - Ξ (a + ((i + 1 : ℕ) : ZMod p) * h) =
          (Ξ (a + ((i + 1 : ℕ) : ZMod p) * h) - Ξ (a + (i : ZMod p) * h)) +
            D2 Ξ (a + (i : ZMod p) * h) h h := by
        unfold D2
        have e1 : a + ((i + 1 + 1 : ℕ) : ZMod p) * h = a + (i : ZMod p) * h + h + h := by
          push_cast; ring
        have e2 : a + ((i + 1 : ℕ) : ZMod p) * h = a + (i : ZMod p) * h + h := by push_cast; ring
        rw [e1, e2]; abel
      rw [e, ih', hb, succ_nsmul]
      abel
  induction j with
  | zero => simp
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; simp
    · have hs' : snorm S (a - n0) + j * snorm S h ≤ ρ := by
        have : (j : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.le_succ j
        nlinarith
      have ih' := ih hs' (fun i hi => hstep i (by omega))
      have hlast := hstep (j - 1) (by omega)
      rw [show j - 1 + 1 = j from Nat.sub_add_cancel hpos] at hlast
      have ecast : ((j - 1 : ℕ) : ZMod p) = (j : ZMod p) - 1 := by
        rw [Nat.cast_sub hpos]; simp
      have e : Ξ (a + ((j + 1 : ℕ) : ZMod p) * h) - Ξ a =
          (Ξ (a + ((j + 1 : ℕ) : ZMod p) * h) - Ξ (a + (j : ZMod p) * h)) +
          (Ξ (a + (j : ZMod p) * h) - Ξ a) := by abel
      have hnext := hstep j
      -- use the step from `j` to `j + 1` via the step from `j - 1` to `j`
      have hb : D2 Ξ (a + ((j - 1 : ℕ) : ZMod p) * h) h h = D2 Ξ a h h := by
        refine D2_base hL hρ (le_trans ?_ hs)
        have : snorm S (((j - 1 : ℕ) : ZMod p) * h) ≤ (j - 1 : ℕ) * snorm S h :=
          snorm_nsmul_le _ h
        have hij : ((j - 1 : ℕ) : ℝ) + 2 ≤ (j + 1 : ℕ) := by
          push_cast [Nat.cast_sub hpos]; linarith
        nlinarith
      have estep : Ξ (a + ((j + 1 : ℕ) : ZMod p) * h) - Ξ (a + (j : ZMod p) * h) =
          (Ξ (a + (j : ZMod p) * h) - Ξ (a + ((j - 1 : ℕ) : ZMod p) * h)) +
            D2 Ξ (a + ((j - 1 : ℕ) : ZMod p) * h) h h := by
        unfold D2
        have e1 : a + ((j + 1 : ℕ) : ZMod p) * h = a + ((j - 1 : ℕ) : ZMod p) * h + h + h := by
          rw [ecast]; push_cast; ring
        have e2 : a + (j : ZMod p) * h = a + ((j - 1 : ℕ) : ZMod p) * h + h := by
          rw [ecast]; ring
        rw [e1, e2]; abel
      have hc : (j + 1).choose 2 = j.choose 2 + j := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
      have hj : (j - 1) • D2 Ξ a h h + D2 Ξ a h h = j • D2 Ξ a h h := by
        rw [← succ_nsmul, Nat.sub_add_cancel hpos]
      rw [e, estep, hlast, hb, ih', hc, add_nsmul, succ_nsmul,
        add_assoc (Ξ (a + h) - Ξ a), hj]
      generalize Ξ (a + h) - Ξ a = Δ
      generalize D2 Ξ a h h = D
      rw [add_nsmul]
      abel

end

end GT
end File_GT_LocQ

section File_GT_CS
/-!
# The double Cauchy–Schwarz inequality used in Weyl differencing
-/

open Finset
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

lemma conj_ec (x : UnitAddCircle) : conj (ec x) = ec (-x) := (ec_neg x).symm

lemma ofReal_norm_sq_wsum (c : α → ℝ) (u : α → ℂ) :
    ((‖∑ i, (c i : ℂ) * u i‖ ^ 2 : ℝ) : ℂ) = ∑ i, ∑ j, ((c i * c j : ℝ) : ℂ) * (u i * conj (u j)) := by
  rw [ofReal_norm_sq, map_sum, sum_mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  simp only [map_mul, Complex.conj_ofReal]; push_cast; ring

/-- **Double Cauchy–Schwarz.** -/
theorem cs2 {P : α → ℝ} {Q : β → ℝ} (hP : ∀ r, 0 ≤ P r) (hP1 : ∑ r, P r = 1)
    (hQ : ∀ h, 0 ≤ Q h) (hQ1 : ∑ h, Q h = 1) (b1 : α → ℂ) (b2 : β → ℂ)
    (hb1 : ∀ r, ‖b1 r‖ ≤ 1) (hb2 : ∀ h, ‖b2 h‖ ≤ 1) (X : α → β → UnitAddCircle) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (h : δ ≤ ‖∑ r, ∑ h, (P r : ℂ) * (Q h : ℂ) * (b1 r * b2 h * ec (X r h))‖) :
    δ ^ 4 ≤ ‖∑ r, ∑ r', ∑ h, ∑ h', ((P r * P r' * Q h * Q h' : ℝ) : ℂ) *
      ec (X r h - X r h' - X r' h + X r' h')‖ := by
  obtain ⟨T, hT⟩ : ∃ T : α → ℂ, ∀ r, T r = ∑ h, (Q h : ℂ) * (b2 h * ec (X r h)) :=
    ⟨_, fun _ => rfl⟩
  have e0 : ∑ r, ∑ h, (P r : ℂ) * (Q h : ℂ) * (b1 r * b2 h * ec (X r h)) =
      ∑ r, (P r : ℂ) * (b1 r * T r) := by
    refine sum_congr rfl fun r _ => ?_
    rw [hT, mul_sum, mul_sum]; exact sum_congr rfl fun h _ => by ring
  have h1 : δ ≤ ∑ r, P r * ‖T r‖ := by
    refine h.trans ?_
    rw [e0]
    refine (norm_sum_le _ _).trans (sum_le_sum fun r _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP r)]
    refine mul_le_mul_of_nonneg_left ?_ (hP r)
    calc ‖b1 r‖ * ‖T r‖ ≤ 1 * ‖T r‖ := mul_le_mul_of_nonneg_right (hb1 r) (norm_nonneg _)
      _ = ‖T r‖ := one_mul _
  have h2 : δ ^ 2 ≤ ∑ r, P r * ‖T r‖ ^ 2 :=
    le_trans (pow_le_pow_left₀ hδ h1 2) (sq_wavg_le _ hP hP1)
  obtain ⟨U, hU⟩ : ∃ U : β → β → ℂ, ∀ h h', U h h' = ∑ r, (P r : ℂ) * ec (X r h - X r h') :=
    ⟨_, fun _ _ => rfl⟩
  have h3 : ((∑ r, P r * ‖T r‖ ^ 2 : ℝ) : ℂ) =
      ∑ h, ∑ h', ((Q h * Q h' : ℝ) : ℂ) * (b2 h * conj (b2 h') * U h h') := by
    push_cast
    have : ∀ r, (P r : ℂ) * ((‖T r‖ ^ 2 : ℝ) : ℂ) = ∑ h, ∑ h', (P r : ℂ) *
        (((Q h * Q h' : ℝ) : ℂ) * (b2 h * conj (b2 h') * ec (X r h - X r h'))) := by
      intro r
      rw [hT, ofReal_norm_sq_wsum, mul_sum]
      refine sum_congr rfl fun h _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun h' _ => ?_
      rw [map_mul, conj_ec, sub_eq_add_neg, ec_add]
      ring
    push_cast at this
    rw [sum_congr rfl fun r _ => this r, sum_comm]
    refine sum_congr rfl fun h _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun h' _ => ?_
    rw [hU, mul_sum, mul_sum]
    exact sum_congr rfl fun r _ => by ring
  have h4 : δ ^ 2 ≤ ∑ h, ∑ h', Q h * Q h' * ‖U h h'‖ := by
    refine h2.trans ?_
    have e := congrArg norm h3
    rw [Complex.norm_real, Real.norm_eq_abs] at e
    refine (le_abs_self _).trans (e ▸ ?_)
    refine (norm_sum_le _ _).trans (sum_le_sum fun h _ => (norm_sum_le _ _).trans
      (sum_le_sum fun h' _ => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hQ h) (hQ h')), norm_mul, norm_mul, Complex.norm_conj]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hQ h) (hQ h'))
    have := mul_le_mul (hb2 h) (hb2 h') (norm_nonneg _) zero_le_one
    calc ‖b2 h‖ * ‖b2 h'‖ * ‖U h h'‖ ≤ 1 * 1 * ‖U h h'‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = ‖U h h'‖ := by ring
  -- second application
  have hQQ : ∀ z : β × β, 0 ≤ Q z.1 * Q z.2 := fun z => mul_nonneg (hQ _) (hQ _)
  have hQQ1 : ∑ z : β × β, Q z.1 * Q z.2 = 1 := by
    simp only [Fintype.sum_prod_type, ← mul_sum, hQ1, mul_one]
  have h5 : δ ^ 4 ≤ ∑ h, ∑ h', Q h * Q h' * ‖U h h'‖ ^ 2 := by
    have := sq_wavg_le (fun z : β × β => ‖U z.1 z.2‖) hQQ hQQ1
    simp only [Fintype.sum_prod_type] at this
    calc δ ^ 4 = (δ ^ 2) ^ 2 := by ring
      _ ≤ (∑ h, ∑ h', Q h * Q h' * ‖U h h'‖) ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
      _ ≤ _ := this
  have h6 : ((∑ h, ∑ h', Q h * Q h' * ‖U h h'‖ ^ 2 : ℝ) : ℂ) =
      ∑ r, ∑ r', ∑ h, ∑ h', ((P r * P r' * Q h * Q h' : ℝ) : ℂ) *
        ec (X r h - X r h' - X r' h + X r' h') := by
    push_cast
    have : ∀ h h', (Q h : ℂ) * (Q h' : ℂ) * ((‖U h h'‖ ^ 2 : ℝ) : ℂ) = ∑ r, ∑ r',
        ((P r * P r' * Q h * Q h' : ℝ) : ℂ) * ec (X r h - X r h' - X r' h + X r' h') := by
      intro h h'
      rw [hU, ofReal_norm_sq_wsum, mul_sum]
      refine sum_congr rfl fun r _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun r' _ => ?_
      rw [conj_ec, ← ec_add]
      push_cast
      rw [show X r h - X r h' + -(X r' h - X r' h') = X r h - X r h' - X r' h + X r' h' by abel]
      ring
    push_cast at this
    rw [sum_congr rfl fun h _ => sum_congr rfl fun h' _ => this h h']
    obtain ⟨G, hG⟩ : ∃ G : α → α → β → β → ℂ, ∀ r r' h h', G r r' h h' =
        (P r : ℂ) * (P r' : ℂ) * (Q h : ℂ) * (Q h' : ℂ) * ec (X r h - X r h' - X r' h + X r' h') :=
      ⟨_, fun _ _ _ _ => rfl⟩
    simp only [← hG]
    calc ∑ h, ∑ h', ∑ r, ∑ r', G r r' h h' = ∑ h, ∑ r, ∑ r', ∑ h', G r r' h h' :=
          sum_congr rfl fun h _ => by
            rw [sum_comm]; exact sum_congr rfl fun r _ => sum_comm
      _ = ∑ r, ∑ r', ∑ h, ∑ h', G r r' h h' := by
            rw [sum_comm]; refine sum_congr rfl fun r _ => ?_
            rw [sum_comm]
  rw [← h6, Complex.norm_real, Real.norm_eq_abs]
  exact h5.trans (le_abs_self _)

end

end GT
end File_GT_CS

section File_GT_LargeQuad
/-!
# Large local quadratic exponential sums (Green–Tao, Proposition 4.9)
-/

open Finset KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- Pigeonhole for a double average. -/
lemma exists_pair_ge {Γ : Finset (ZMod p)} {ρ1 ρ : ℝ} (hρ1 : 0 ≤ ρ1) (hρ : 0 ≤ ρ)
    (G : ZMod p → ZMod p → ℝ) {c : ℝ}
    (h : c ≤ ∑ x, ∑ y, regP Γ ρ1 x * regP Γ ρ y * G x y) :
    ∃ x y, regP Γ ρ1 x ≠ 0 ∧ regP Γ ρ y ≠ 0 ∧ c ≤ G x y := by
  have hD := regP_isDist Γ hρ
  have hD1 := regP_isDist Γ hρ1
  have hP : ∀ z : ZMod p × ZMod p, 0 ≤ regP Γ ρ1 z.1 * regP Γ ρ z.2 :=
    fun z => mul_nonneg (hD1.1 _) (hD.1 _)
  have hP1 : ∑ z : ZMod p × ZMod p, regP Γ ρ1 z.1 * regP Γ ρ z.2 = 1 := by
    simp only [Fintype.sum_prod_type, ← mul_sum, hD.2, mul_one, hD1.2]
  obtain ⟨z, hz, hcz⟩ := exists_pos_ge hP hP1 (fun z => G z.1 z.2) (c := c) (by
    rw [Fintype.sum_prod_type]; exact h)
  exact ⟨z.1, z.2, left_ne_zero_of_mul hz, right_ne_zero_of_mul hz, hcz⟩

end

end GT
end File_GT_LargeQuad

section File_GT_WD
/-!
# Weyl differencing for locally quadratic phases (Green–Tao §7)
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

set_option maxHeartbeats 2000000 in
/-- The tail of the Weyl differencing argument: a large correlation of the second difference
`D2 ψ a₀` against arbitrary bounded functions of each variable forces `q · D2 ψ a₀` to be small
on a small Bohr set, for some bounded `q ≥ 1`. -/
theorem wd_tail (hp : p.Prime) {S : Finset (ZMod p)} (hS : ∃ s ∈ S, s ≠ 0) {n0 : ZMod p}
    {ρ : ℝ} (hρ : 0 < ρ) {ψ : ZMod p → UnitAddCircle} (hL : LocQuad (sBohr S n0 ρ) ψ)
    {a0 : ZMod p} (ha0 : snorm S (a0 - n0) ≤ ρ / 2) {ρr ρh : ℝ} (hρh : 0 < ρh)
    (hhr : ρh ≤ ρr) (hr8 : ρr ≤ ρ / 8) (b1 b2 : ZMod p → ℂ) (hb1 : ∀ r, ‖b1 r‖ ≤ 1)
    (hb2 : ∀ h, ‖b2 h‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : δ ≤ ‖∑ r, ∑ h, (regP S ρr r : ℂ) * (regP S ρh h : ℂ) *
      (b1 r * b2 h * ec (D2 ψ a0 r h))‖) :
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (32 / δ ^ 4) ^ (S.card ^ 2) ∧
      ∀ n m, snorm S n ≤ lqR S.card (δ ^ 4) ρh → snorm S m ≤ lqR S.card (δ ^ 4) ρh →
        ‖q • D2 ψ a0 n m‖ ≤ lqK S.card (δ ^ 4) ρh * snorm S n * snorm S m := by
  have hρr : 0 < ρr := lt_of_lt_of_le hρh hhr
  have hDr := regP_isDist S hρr.le
  have hDh := regP_isDist S hρh.le
  obtain ⟨X, hX⟩ : ∃ X : ZMod p → ZMod p → UnitAddCircle, X = D2 ψ a0 := ⟨_, rfl⟩
  rw [← hX] at h
  have hcs := cs2 hDr.1 hDr.2 hDh.1 hDh.2 b1 b2 hb1 hb2 X hδ.le h
  -- pigeonhole in `(r', h')`
  obtain ⟨W, hW⟩ : ∃ W : ZMod p → ZMod p → ℂ, ∀ r' h', W r' h' = ∑ r, ∑ h,
      (regP S ρr r : ℂ) * (regP S ρh h : ℂ) * ec (X r h - X r h' - X r' h + X r' h') :=
    ⟨_, fun _ _ => rfl⟩
  have hre : ∑ r, ∑ r', ∑ h, ∑ h', ((regP S ρr r * regP S ρr r' * regP S ρh h *
      regP S ρh h' : ℝ) : ℂ) * ec (X r h - X r h' - X r' h + X r' h') =
      ∑ r', ∑ h', (regP S ρr r' : ℂ) * (regP S ρh h' : ℂ) * W r' h' := by
    obtain ⟨G, hG⟩ : ∃ G : ZMod p → ZMod p → ZMod p → ZMod p → ℂ, ∀ r r' h h', G r r' h h' =
        (regP S ρr r' : ℂ) * (regP S ρh h' : ℂ) * ((regP S ρr r : ℂ) * (regP S ρh h : ℂ) *
          ec (X r h - X r h' - X r' h + X r' h')) := ⟨_, fun _ _ _ _ => rfl⟩
    have e1 : ∀ r r' h h', ((regP S ρr r * regP S ρr r' * regP S ρh h *
        regP S ρh h' : ℝ) : ℂ) * ec (X r h - X r h' - X r' h + X r' h') = G r r' h h' := by
      intro r r' h h'; rw [hG]; push_cast; ring
    have rhs : ∑ r', ∑ h', (regP S ρr r' : ℂ) * (regP S ρh h' : ℂ) * W r' h' =
        ∑ r', ∑ h', ∑ r, ∑ h, G r r' h h' := by
      refine sum_congr rfl fun r' _ => sum_congr rfl fun h' _ => ?_
      rw [hW, mul_sum]; refine sum_congr rfl fun r _ => ?_
      rw [mul_sum]; refine sum_congr rfl fun h _ => ?_
      rw [hG]
    rw [rhs]
    simp only [e1]
    calc ∑ r, ∑ r', ∑ h, ∑ h', G r r' h h' = ∑ r', ∑ r, ∑ h, ∑ h', G r r' h h' := sum_comm
      _ = ∑ r', ∑ r, ∑ h', ∑ h, G r r' h h' :=
          sum_congr rfl fun r' _ => sum_congr rfl fun r _ => sum_comm
      _ = ∑ r', ∑ h', ∑ r, ∑ h, G r r' h h' := sum_congr rfl fun r' _ => sum_comm
  rw [hre] at hcs
  have hcs' : δ ^ 4 ≤ ∑ r', ∑ h', regP S ρr r' * regP S ρh h' * ‖W r' h'‖ := by
    refine hcs.trans ((norm_sum_le _ _).trans (sum_le_sum fun r' _ => (norm_sum_le _ _).trans
      (sum_le_sum fun h' _ => le_of_eq ?_)))
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (regP_nonneg S r'), abs_of_nonneg (regP_nonneg S h')]
  obtain ⟨r', h', hr', hh', hW'⟩ := exists_pair_ge hρr.le hρh.le _ hcs'
  have hsr' : snorm S r' ≤ ρr := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρr.le hr') hρr.le
  have hsh' : snorm S h' ≤ ρh := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρh.le hh') hρh.le
  -- the phase in the form of Proposition 4.9
  have hW2 : δ ^ 4 ≤ ‖∑ r, ∑ h, (regP S ρr r : ℂ) * (regP S ρh h : ℂ) *
      ec (X r h + (fun r => -X r h') r + (fun h => -X r' h) h)‖ := by
    refine hW'.trans (le_of_eq ?_)
    rw [hW]
    have e : ∑ r, ∑ h, (regP S ρr r : ℂ) * (regP S ρh h : ℂ) *
        ec (X r h - X r h' - X r' h + X r' h') = ec (X r' h') * ∑ r, ∑ h,
        (regP S ρr r : ℂ) * (regP S ρh h : ℂ) *
          ec (X r h + (fun r => -X r h') r + (fun h => -X r' h) h) := by
      rw [mul_sum]; refine sum_congr rfl fun r _ => ?_
      rw [mul_sum]; refine sum_congr rfl fun h _ => ?_
      try simp only
      rw [show X r h - X r h' - X r' h + X r' h' = X r' h' + (X r h + -X r h' + -X r' h) by abel,
        ec_add]
      ring
    rw [e, norm_mul, norm_ec, one_mul]
  have H1 : ∀ m, snorm S m ≤ 2 * ρr → AddOn S (2 * ρr) (fun n => X n m) := by
    intro m hm
    rw [hX]
    exact (addOn_D2_left hL hρ.le a0 m).mono (by linarith)
  have H2 : ∀ n, snorm S n ≤ 2 * ρr → AddOn S (2 * ρr) (fun m => X n m) := by
    intro n hn
    rw [hX]
    exact (addOn_D2_right hL hρ.le a0 n).mono (by linarith)
  have H3 : AddOn S (2 * ρr) (fun r => -X r h') := by
    rw [hX]
    exact ((addOn_D2_left hL hρ.le a0 h').mono (by linarith)).neg
  have H4 : AddOn S (2 * ρr) (fun h => -X r' h) := by
    rw [hX]
    exact ((addOn_D2_right hL hρ.le a0 r').mono (by linarith)).neg
  obtain ⟨q, hq1, hq2, hq3⟩ := large_quad (φ := X) (lam := fun r => -X r h')
    (mu := fun h => -X r' h) hp hS hρh hhr (pow_pos hδ 4) (pow_le_one₀ hδ.le hδ1) H1 H2 H3 H4 hW2
  refine ⟨q, hq1, hq2, fun n m hn hm => ?_⟩
  rw [← hX]
  exact hq3 n m hn hm

end

end GT
end File_GT_WD

section File_GT_WeylStep
/-!
# The Weyl step of Proposition 7.1 (Green–Tao, Lemmas 3.2 and 7.2)

A poorly distributed label produces a non-zero frequency `k = (k₀, k₁, k₂)` with coordinates
`|k_{j,i}| ≲ (d/η)‖v_i‖` such that `E e(k₀·Ξ(a) + k₁·Ξ(a+r) + k₂·Ξ(a+2r))` is large.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

lemma kdot_apply {ι : Type*} [Fintype ι] (k : ι → ℤ) (x : ι → UnitAddCircle) :
    kdot k x = ∑ i, k i • x i := rfl

namespace DTorus

lemma Good.one_le_norm {G : DTorus} (hG : G.Good) (i : Fin G.d) : 1 ≤ ‖G.v i‖ := by
  classical
  have h := hG.2.1 (Pi.single i 1 : Fin G.d → ℤ) (by simp)
  have e : G.emb (fun j => (((Pi.single i 1 : Fin G.d → ℤ) j : ℤ) : ℝ)) = G.v i := by
    unfold emb
    rw [sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  rwa [e] at h

end DTorus

end

end GT
end File_GT_WeylStep

section File_GT_Prop71
/-!
# Proposition 7.1 of Green–Tao

A poorly distributed label gives a primitive dual frequency `k'`, a multiplier `m`, and for each
base point `a` of the Bohr set a frequency `ξ_a`, such that `k'·(Ξ(a + 2mh) − Ξ(a))` is small
for `h` in a small Bohr set with frequencies `S ∪ {ξ_a}`.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma kdot_smul_left {ι : Type*} [Fintype ι] (c : ℤ) (k : ι → ℤ) (y : ι → UnitAddCircle) :
    kdot (c • k) y = c • kdot k y := by
  simp only [kdot_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, SemigroupAction.mul_smul]

variable {S : Finset (ZMod p)} {M : Type*} [AddCommGroup M] {n0 : ZMod p} {ρ : ℝ}
  {Ξ : ZMod p → M}

lemma one_le_wM {G : DTorus} (hG : G.Good) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (i : Fin G.d) :
    1 ≤ wM G η i := by
  have h1 := hG.one_le_norm i
  have h2 : (1 : ℝ) ≤ 1000 * (G.d + 1) / η * ‖G.v i‖ := by
    have : (1 : ℝ) ≤ 1000 * (G.d + 1) / η := by
      rw [le_div_iff₀ hη]; have : (0 : ℝ) ≤ G.d := Nat.cast_nonneg _; nlinarith
    nlinarith
  have := h2.trans (Nat.le_ceil _)
  unfold wM
  exact_mod_cast this

lemma one_le_wP {G : DTorus} (hG : G.Good) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) : 1 ≤ wP G η := by
  unfold wP
  refine one_le_pow₀ ?_
  calc (1 : ℝ) = ∏ _i : Fin G.d, (1 : ℝ) := by simp
    _ ≤ ∏ i, (2 * wM G η i : ℝ) := Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => by
        have := one_le_wM hG hη hη1 i
        have : (1 : ℝ) ≤ wM G η i := by exact_mod_cast this
        linarith

lemma wδ_pos {G : DTorus} (hG : G.Good) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) : 0 < wδ G η := by
  unfold wδ; have := one_le_wP hG hη hη1; positivity

lemma wδ_le {G : DTorus} (hG : G.Good) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) : wδ G η ≤ η / 256 := by
  unfold wδ
  have := one_le_wP hG hη hη1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Factoring a non-zero integer vector as `g • k'` with `k'` primitive. -/
lemma exists_prim_factor {d : ℕ} {k : Fin d → ℤ} (hk : k ≠ 0) :
    ∃ (g : ℕ) (k' : Fin d → ℤ), 1 ≤ g ∧ Prim k' ∧ (∀ i, k i = g * k' i) ∧
      (g : ℝ) ≤ ∑ i, |(k i : ℝ)| := by
  classical
  obtain ⟨i0, hi0⟩ : ∃ i0, k i0 ≠ 0 := by
    by_contra h; push_neg at h; exact hk (funext h)
  obtain ⟨k', hk', hg1⟩ := Finset.extract_gcd k (s := univ) ⟨i0, mem_univ _⟩
  set G0 := univ.gcd k with hG0
  have hG0nn : 0 ≤ G0 := by
    have : normalize G0 = G0 := Finset.normalize_gcd
    rw [← this, ← Int.abs_eq_normalize]; exact abs_nonneg _
  have hG0ne : G0 ≠ 0 := by
    intro h0; apply hi0; rw [hk' i0 (mem_univ _), h0, zero_mul]
  refine ⟨G0.toNat, k', ?_, ?_, fun i => ?_, ?_⟩
  · have : 0 < G0 := lt_of_le_of_ne hG0nn (Ne.symm hG0ne)
    omega
  · intro e he
    exact isUnit_of_dvd_one (hg1 ▸ Finset.dvd_gcd fun i _ => he i)
  · rw [hk' i (mem_univ _), Int.toNat_of_nonneg hG0nn]
  · have hk'0 : k' i0 ≠ 0 := by
      intro h0; apply hi0; rw [hk' i0 (mem_univ _), h0, mul_zero]
    have h1 : (G0.toNat : ℝ) ≤ |(k i0 : ℝ)| := by
      rw [hk' i0 (mem_univ _)]
      push_cast
      rw [abs_mul, show ((G0.toNat : ℕ) : ℝ) = (G0 : ℝ) by exact_mod_cast Int.toNat_of_nonneg hG0nn,
        abs_of_nonneg (by exact_mod_cast hG0nn)]
      have : (1 : ℝ) ≤ |(k' i0 : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk'0
      nlinarith [(by exact_mod_cast hG0nn : (0 : ℝ) ≤ G0)]
    exact h1.trans (single_le_sum (f := fun i => |(k i : ℝ)|) (fun i _ => abs_nonneg _)
      (mem_univ i0))

/-- Second differences of a locally quadratic map are independent of the base point, as long as
all cube vertices stay inside the Bohr set. -/
lemma D2_base_gen {S : Finset (ZMod p)} {M : Type*} [AddCommGroup M] {n0 : ZMod p} {ρ : ℝ}
    {Ξ : ZMod p → M} (hL : LocQuad (sBohr S n0 ρ) Ξ) (hρ : 0 ≤ ρ) {a a' h k : ZMod p}
    (ha : snorm S (a - n0) + (snorm S h + snorm S k) ≤ ρ)
    (ha' : snorm S (a' - n0) + (snorm S h + snorm S k) ≤ ρ) : D2 Ξ a h k = D2 Ξ a' h k := by
  have hh := snorm_nonneg (S := S) h
  have hk := snorm_nonneg (S := S) k
  have hmem : ∀ b y, snorm S (b - n0) + snorm S y ≤ ρ → b + y ∈ sBohr S n0 ρ := by
    intro b y hb
    rw [mem_sBohr hρ, show b + y - n0 = (b - n0) + y by abel]
    exact (snorm_add_le _ _).trans hb
  have hhk' : snorm S (h + k) ≤ snorm S h + snorm S k := snorm_add_le _ _
  have e : a' + (a - a') = a := by abel
  have H := hL a' (a - a') h k (by simpa using hmem a' 0 (by simp; linarith))
    (by rw [e]; simpa using hmem a 0 (by simp; linarith))
    (hmem a' h (by linarith)) (hmem a' k (by linarith))
    (by rw [e]; exact hmem a h (by linarith)) (by rw [e]; exact hmem a k (by linarith))
    (by rw [add_assoc]; exact hmem a' (h + k) (by linarith))
    (by rw [e, add_assoc]; exact hmem a (h + k) (by linarith))
  rw [e] at H
  rw [← sub_eq_zero, ← H]
  unfold D2
  abel

lemma p71δ_pos {G : DTorus} (hG : G.Good) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) : 0 < p71δ G η := by
  unfold p71δ; have := wδ_pos hG hη hη1; positivity

lemma p71δ_le {G : DTorus} (hG : G.Good) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) : p71δ G η ≤ 1 := by
  unfold p71δ; have := wδ_le hG hη hη1; linarith

set_option maxHeartbeats 4000000 in
/-- **Proposition 7.1** (with per-base-point frequency): a poorly distributed label gives a
primitive `k`, a multiplier `m ≥ 1`, and for every base point `a` of the half Bohr set a
frequency `ξ` such that `k · (Ξ(a + 2mh) − Ξ(a))` is linearly small in `‖h‖_{(S ∪ {ξ})^⊥}`. -/
theorem prop71 (hp : p.Prime) {S : Finset (ZMod p)} (hS : ∃ s ∈ S, s ≠ 0) {n0 : ZMod p} {ρ : ℝ}
    (hρ : 0 < ρ) {ε4 : ℝ} (hε0 : 0 < ε4) (hε8 : ε4 ≤ 1 / 8)
    {G : DTorus} (hG : G.Good) {F : G.Pt → ℝ} (hF : G.IsLip F) (hF1 : ∀ x, |F x| ≤ 1)
    {Ξ : ZMod p → G.Pt} (hL : LocQuad (sBohr S n0 ρ) Ξ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hsmall : 100 * S.card * ε4 ≤ wδ G η / 2)
    (hpoor : ∑ z : ZMod p × ZMod p, regP S (ρ / 2) (z.1 - n0) * regP S (ε4 * ρ) z.2 *
        (F (Ξ z.1) * F (Ξ (z.1 + z.2)) * F (Ξ (z.1 + 2 * z.2)) * F (Ξ (z.1 + 3 * z.2))) <
      (∑ z : ZMod p × ZMod p, regP S (ρ / 2) (z.1 - n0) * regP S (ε4 * ρ) z.2 *
        F (Ξ z.1)) ^ 4 - η / 2) :
    ∃ k : Fin G.d → ℤ, Prim k ∧ (∀ i, |k i| < 4 * wM G η i) ∧
      ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ p71m S G η ∧
        ∀ a, snorm S (a - n0) ≤ ρ / 2 → ∃ ξ : ZMod p, ∀ b h : ZMod p,
          snorm S (b - a) ≤ p71R S G η ε4 ρ →
          snorm (insert ξ S) h ≤ p71R S G η ε4 ρ → 8 * m * snorm (insert ξ S) h ≤ ρ →
          ‖kdot k (Ξ (b + ((2 * m : ℕ) : ZMod p) * h) - Ξ b)‖ ≤
            (2 + 2 * p71E S G η ε4 ρ + 4 * m * p71K S G η ε4 ρ * p71R S G η ε4 ρ) *
              snorm (insert ξ S) h := by
  classical
  obtain ⟨kφ, hkφ0, hkφb, a0, ha0, b1, b2, hb1, hb2, hbig⟩ :=
    poor_d2 hρ hε0 hε8 hG hF hF1 hL hη hη1 hsmall hpoor
  have hδ0 := p71δ_pos hG hη hη1
  have hδ1 := p71δ_le hG hη hη1
  have hρr : 0 < ε4 * ρ := mul_pos hε0 hρ
  have hwδ0 := wδ_pos hG hη hη1
  have hwδ1 := wδ_le hG hη hη1
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hρh0 : 0 < wρh S G η ε4 ρ := by unfold wρh; positivity
  have hρhr : wρh S G η ε4 ρ ≤ ε4 * ρ := by
    unfold wρh
    rw [div_le_iff₀ (by positivity)]
    have : wδ G η * (ε4 * ρ) ≤ 1 * (ε4 * ρ) := by
      apply mul_le_mul_of_nonneg_right _ hρr.le; linarith
    nlinarith
  have hbig' : p71δ G η ≤ ‖∑ r, ∑ h, (regP S (ε4 * ρ) r : ℂ) *
      (regP S (wρh S G η ε4 ρ) h : ℂ) *
      (b1 r * b2 h * ec (D2 (fun x => kdot kφ (Ξ x)) a0 r h))‖ := by
    unfold p71δ; linarith
  obtain ⟨q, hq1, hqb, hqD⟩ := wd_tail hp hS hρ (hL.comp (kdot kφ)) ha0 hρh0 hρhr
    (by nlinarith) b1 b2 hb1 hb2 hδ0 hδ1 hbig'
  obtain ⟨g, k', hg1, hk', hkk, hgs⟩ := exists_prim_factor hkφ0
  set R := p71R S G η ε4 ρ with hR
  set K := p71K S G η ε4 ρ with hK
  set E := p71E S G η ε4 ρ with hE
  set A := p71A S G η ε4 ρ with hA
  -- positivity and size facts
  have hSne : S.Nonempty := by obtain ⟨s, hs, _⟩ := hS; exact ⟨s, hs⟩
  have hScard : (1 : ℝ) ≤ S.card := by exact_mod_cast hSne.card_pos
  have hR0 : 0 < R := by
    rw [hR, p71R, lqR, lqτ]; positivity
  have hRρh : R ≤ wρh S G η ε4 ρ := by
    rw [hR, p71R, lqR, lqτ]
    have hτ : p71δ G η ^ 4 * wρh S G η ε4 ρ / (200 * S.card) ≤ wρh S G η ε4 ρ := by
      rw [div_le_iff₀ (by positivity)]
      have : p71δ G η ^ 4 ≤ 1 := pow_le_one₀ hδ0.le hδ1
      nlinarith
    refine le_trans (div_le_self (by positivity) ?_) hτ
    have h2 : (1 : ℝ) ≤ 2 ^ (S.card ^ 2) := one_le_pow₀ (by norm_num)
    have h3 : (1 : ℝ) ≤ 65536 / (p71δ G η ^ 4) ^ 3 + 1 := by
      have : (0 : ℝ) ≤ 65536 / (p71δ G η ^ 4) ^ 3 := by positivity
      linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h2 hScard) h3
  have hRρ : R ≤ ρ / 4 := by
    refine hRρh.trans (hρhr.trans ?_); nlinarith
  have hK0 : 0 ≤ K := by rw [hK, p71K, lqK]; positivity
  have hA1 : 1 ≤ A := by rw [hA, p71A]; nlinarith [sq_nonneg (2 * R)]
  refine ⟨k', hk', fun i => ?_, q * g, ?_, ?_, ?_⟩
  · have h1 := hkφb i
    rw [hkk i] at h1
    have hk'i : |k' i| ≤ |(g : ℤ) * k' i| := by
      rw [abs_mul]; have : (1 : ℤ) ≤ |(g : ℤ)| := by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hg1
      nlinarith [abs_nonneg (k' i)]
    omega
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · rw [p71m]
    push_cast
    have hsum : ∑ i, |(kφ i : ℝ)| ≤ 4 * ∑ i, (wM G η i : ℝ) := by
      rw [mul_sum]
      refine sum_le_sum fun i _ => ?_
      have := hkφb i
      have : ((|kφ i| : ℤ) : ℝ) < ((4 * (wM G η i : ℤ) : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at this ⊢; linarith
    exact mul_le_mul hqb (hgs.trans hsum) (by positivity) (by positivity)
  · intro a ha
    have hR8 : R ≤ ρ / 8 := hRρh.trans (hρhr.trans (by nlinarith))
    set ψ : ZMod p → UnitAddCircle := fun x => kdot k' (Ξ x) with hψ
    have hψk : ∀ x, (q : ℤ) • kdot kφ x = ((q * g : ℕ) : ℤ) • kdot k' x := by
      intro x
      have : kφ = ((g : ℤ)) • k' := funext fun i => by rw [hkk i]; simp
      rw [this, kdot_smul_left, smul_smul]; push_cast; ring_nf
    have hD2 : ∀ n n', D2 (fun x => kdot kφ (Ξ x)) a0 n n' =
        kdot kφ (Ξ (a0 + n + n') - Ξ (a0 + n) - Ξ (a0 + n') + Ξ a0) := by
      intro n n'; simp [D2, map_sub, map_add]
    have hD2' : ∀ b n n', D2 ψ b n n' =
        kdot k' (Ξ (b + n + n') - Ξ (b + n) - Ξ (b + n') + Ξ b) := by
      intro b n n'; simp [hψ, D2, map_sub, map_add]
    -- the bilinear bound at any base `b` with `‖b - n₀‖ ≤ 3ρ/4`
    have hbil : ∀ b, snorm S (b - n0) ≤ 3 * ρ / 4 → ∀ n n', snorm S n ≤ R → snorm S n' ≤ R →
        ‖(q * g) • D2 ψ b n n'‖ ≤ K * snorm S n * snorm S n' := by
      intro b hb n n' hn hn'
      have hfar : D2 Ξ b n n' = D2 Ξ a0 n n' :=
        D2_base_gen hL hρ.le (by linarith) (by linarith)
      have := hqD n n' hn hn'
      rw [hD2] at this
      rw [hD2']
      have hfar' : Ξ (b + n + n') - Ξ (b + n) - Ξ (b + n') + Ξ b =
          Ξ (a0 + n + n') - Ξ (a0 + n) - Ξ (a0 + n') + Ξ a0 := hfar
      have e := hψk (Ξ (a0 + n + n') - Ξ (a0 + n) - Ξ (a0 + n') + Ξ a0)
      simp only [natCast_zsmul] at e
      rw [hfar', ← e]
      exact this
    obtain ⟨ξ, hξ⟩ := loc_to_glob hSne (ρ := 2 * R) (A := A) (by positivity) hA1
      (fun x => (q * g) • ψ x) a (by
        intro h k hh hk
        have hh' := snorm_le_of_mem hh (by positivity)
        have hk' := snorm_le_of_mem hk (by positivity)
        have hb := hbil a (by linarith) h k (by linarith) (by linarith)
        have e : (q * g) • ψ (a + h + k) - (q * g) • ψ (a + h) - (q * g) • ψ (a + k) +
            (q * g) • ψ a = (q * g) • D2 ψ a h k := by simp [D2, smul_sub, smul_add]
        rw [e]
        refine hb.trans ?_
        rw [le_div_iff₀ (by positivity), hA, p71A]
        have := mul_nonneg (snorm_nonneg (S := S) h) (snorm_nonneg (S := S) k)
        nlinarith [sq_nonneg (2 * R)])
    refine ⟨ξ, fun b h hbR hhR hhρ => ?_⟩
    obtain ⟨t, rfl⟩ : ∃ t, b = a + t := ⟨b - a, by abel⟩
    have htR : snorm S t ≤ R := by simpa using hbR
    have hb : snorm S (a + t - n0) ≤ ρ / 2 + R := by
      rw [show a + t - n0 = (a - n0) + t by abel]
      exact (snorm_add_le _ _).trans (by linarith)
    set σ := snorm (insert ξ S) h with hσ
    have hσS : snorm S h ≤ σ := snorm_mono (subset_insert _ _) h
    have hξh : ‖ZMod.toAddCircle (ξ * h)‖ ≤ σ := cn_le_snorm (mem_insert_self _ _) h
    have hs0 := snorm_nonneg (S := S) h
    have ht0 := snorm_nonneg (S := S) t
    have hm1 : (1 : ℝ) ≤ (q * g : ℕ) := by
      have : 1 ≤ q * g := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      exact_mod_cast this
    have hmσ : ((q * g : ℕ) : ℝ) * snorm S h ≤ ((q * g : ℕ) : ℝ) * σ :=
      mul_le_mul_of_nonneg_left hσS (by positivity)
    have hprog := lq_prog hL hρ.le (a := a + t) (h := h) (2 * (q * g)) (by
      have e : ((2 * (q * g) : ℕ) : ℝ) = 2 * ((q * g : ℕ) : ℝ) := by push_cast; ring
      rw [e]; linarith)
    have hkey : kdot k' (Ξ (a + t + ((2 * (q * g) : ℕ) : ZMod p) * h) - Ξ (a + t)) =
        2 • (((q * g) • ψ (a + h) - (q * g) • ψ a) + (q * g) • D2 ψ a t h) +
          (2 * (q * g) - 1) • ((q * g) • D2 ψ (a + t) h h) := by
      rw [hprog, map_add, map_nsmul, map_nsmul, map_sub]
      rw [show (2 * (q * g)).choose 2 = (2 * (q * g) - 1) * (q * g) by
        rw [Nat.choose_two_right]
        have : 2 * (q * g) * (2 * (q * g) - 1) / 2 = (q * g) * (2 * (q * g) - 1) := by
          rw [mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
        rw [this, mul_comm]]
      have eD : kdot k' (D2 Ξ (a + t) h h) = D2 ψ (a + t) h h := by
        simp [hψ, D2, map_sub, map_add]
      have eS : ψ (a + t + h) - ψ (a + t) = (ψ (a + h) - ψ a) + D2 ψ a t h := by
        simp only [D2]; abel
      have eS' : kdot k' (Ξ (a + t + h)) - kdot k' (Ξ (a + t)) =
          (ψ (a + h) - ψ a) + D2 ψ a t h := eS
      rw [eD, eS']
      simp only [smul_add, smul_sub, smul_smul, mul_comm 2 (q * g)]
    rw [hkey]
    have h1 := hξ h ((mem_bohr_iff_snorm (by positivity)).mpr (by linarith))
    have h2 := hbil (a + t) (by linarith) h h (by linarith) (by linarith)
    have h3 := hbil a (by linarith) t h htR (by linarith)
    have e1 : (q * g) • ψ (a + h) - (q * g) • ψ a =
        ((q * g) • ψ (a + h) - (q * g) • ψ a - ZMod.toAddCircle (ξ * h)) +
          ZMod.toAddCircle (ξ * h) := by abel
    have hE0 : 0 ≤ E := by
      have e : E = 10 ^ 9 * √A * (S.card : ℝ) ^ 4 / (2 * R) := rfl
      rw [e]
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (pow_nonneg hS0 _)) (by linarith)
    have hσ0 : 0 ≤ σ := snorm_nonneg _
    have hn1 : ‖(q * g) • ψ (a + h) - (q * g) • ψ a‖ ≤ E * σ + σ := by
      rw [e1]
      refine (norm_add_le _ _).trans (add_le_add ?_ hξh)
      refine h1.trans ?_
      have : (0 : ℝ) ≤ 10 ^ 9 * √A * (S.card : ℝ) ^ 4 / (2 * R) := by
        have e : E = 10 ^ 9 * √A * (S.card : ℝ) ^ 4 / (2 * R) := rfl
        rw [← e]; exact hE0
      calc 10 ^ 9 * √A * (S.card : ℝ) ^ 4 * snorm S h / (2 * R)
          = 10 ^ 9 * √A * (S.card : ℝ) ^ 4 / (2 * R) * snorm S h := by ring
        _ ≤ E * σ := mul_le_mul_of_nonneg_left hσS this
    have hn2 : ‖(q * g) • D2 ψ (a + t) h h‖ ≤ K * R * σ := by
      refine h2.trans ?_
      have : snorm S h * snorm S h ≤ R * σ := mul_le_mul (by linarith) hσS hs0 hR0.le
      nlinarith
    have hn3 : ‖(q * g) • D2 ψ a t h‖ ≤ K * R * σ := by
      refine h3.trans ?_
      have : snorm S t * snorm S h ≤ R * σ := mul_le_mul htR hσS hs0 hR0.le
      nlinarith
    have hKRσ : 0 ≤ K * R * σ := by positivity
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add norm_nsmul_le norm_nsmul_le).trans ?_
    have hn13 := (norm_add_le ((q * g) • ψ (a + h) - (q * g) • ψ a) ((q * g) • D2 ψ a t h)).trans
      (add_le_add hn1 hn3)
    have hc : ((2 * (q * g) - 1 : ℕ) : ℝ) ≤ 2 * (q * g : ℕ) := by
      have : 2 * (q * g) - 1 ≤ 2 * (q * g) := Nat.sub_le _ _
      exact_mod_cast this
    push_cast at hc hm1 ⊢
    nlinarith

end

end GT
end File_GT_Prop71

open Finset KM
open scoped ComplexConjugate
open GT in
theorem solution {p : ℕ} [NeZero p] (hp : p.Prime) {S : Finset (ZMod p)} (hS : ∃ s ∈ S, s ≠ 0) {n0 : ZMod p} {ρ : ℝ}
    (hρ : 0 < ρ) {ε4 : ℝ} (hε0 : 0 < ε4) (hε8 : ε4 ≤ 1 / 8)
    {G : DTorus} (hG : G.Good) {F : G.Pt → ℝ} (hF : G.IsLip F) (hF1 : ∀ x, |F x| ≤ 1)
    {Ξ : ZMod p → G.Pt} (hL : LocQuad (sBohr S n0 ρ) Ξ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hsmall : 100 * S.card * ε4 ≤ wδ G η / 2)
    (hpoor : ∑ z : ZMod p × ZMod p, regP S (ρ / 2) (z.1 - n0) * regP S (ε4 * ρ) z.2 *
        (F (Ξ z.1) * F (Ξ (z.1 + z.2)) * F (Ξ (z.1 + 2 * z.2)) * F (Ξ (z.1 + 3 * z.2))) <
      (∑ z : ZMod p × ZMod p, regP S (ρ / 2) (z.1 - n0) * regP S (ε4 * ρ) z.2 *
        F (Ξ z.1)) ^ 4 - η / 2) :
    ∃ k : Fin G.d → ℤ, Prim k ∧ (∀ i, |k i| < 4 * wM G η i) ∧
      ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ p71m S G η ∧
        ∀ a, snorm S (a - n0) ≤ ρ / 2 → ∃ ξ : ZMod p, ∀ b h : ZMod p,
          snorm S (b - a) ≤ p71R S G η ε4 ρ →
          snorm (insert ξ S) h ≤ p71R S G η ε4 ρ → 8 * m * snorm (insert ξ S) h ≤ ρ →
          ‖kdot k (Ξ (b + ((2 * m : ℕ) : ZMod p) * h) - Ξ b)‖ ≤
            (2 + 2 * p71E S G η ε4 ρ + 4 * m * p71K S G η ε4 ρ * p71R S G η ε4 ρ) *
              snorm (insert ξ S) h :=
  @GT.prop71 p _ hp S hS n0 ρ hρ ε4 hε0 hε8 G hG F hF hF1 Ξ hL η hη hη1 hsmall hpoor

