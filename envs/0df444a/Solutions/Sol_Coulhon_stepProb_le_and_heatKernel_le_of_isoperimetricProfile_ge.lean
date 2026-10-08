-- Prove2me | solution 1 for Coulhon.stepProb_le_and_heatKernel_le_of_isoperimetricProfile_ge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-04T11:42:10.262083+00:00
-- url     : https://prove2.me/submissions/076ea7b7-5f80-441d-9d48-18c254d6c357

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels
universe u

section
/-!
# Kernel library for the Markov heat-kernel package

Substochastic kernels on a type `X` (no countability needed): non-negative entries, summable rows
with sums at most one. Their powers `stepProb`, Chapman–Kolmogorov, symmetry of powers, column
sums, and Poisson series facts used by the heat kernel.
-/

open DurrettProbability MarkovChain

namespace MarkovHK

variable {X : Type*}

/-- A substochastic kernel. -/
def IsSub (p : X → X → ℝ) : Prop :=
  (∀ x y, 0 ≤ p x y) ∧ (∀ x, Summable (p x)) ∧ ∀ x, ∑' y, p x y ≤ 1

lemma isSub_of_isTransition {p : X → X → ℝ} (h : IsTransition p) : IsSub p :=
  ⟨h.1, h.2.1, fun x => (h.2.2 x).le⟩

lemma IsSub.le_one {p : X → X → ℝ} (h : IsSub p) (x y : X) : p x y ≤ 1 :=
  le_trans ((h.2.1 x).le_tsum y fun z _ => h.1 x z) (h.2.2 x)

/-- Fubini for `a(w) q(w, z) r(z)`, `a ≥ 0` summable, `q` substochastic, `0 ≤ r ≤ 1`. -/
lemma summable_triple {a : X → ℝ} (ha0 : ∀ w, 0 ≤ a w) (has : Summable a) {q : X → X → ℝ}
    (hq : IsSub q) {r : X → ℝ} (hr0 : ∀ z, 0 ≤ r z) (hr1 : ∀ z, r z ≤ 1) :
    Summable (fun p : X × X => a p.1 * q p.1 p.2 * r p.2) := by
  have h0 : 0 ≤ (fun p : X × X => a p.1 * q p.1 p.2 * r p.2) := fun p =>
    mul_nonneg (mul_nonneg (ha0 _) (hq.1 _ _)) (hr0 _)
  have hrow : ∀ w, Summable (fun z => a w * q w z * r z) := fun w =>
    Summable.of_nonneg_of_le (fun z => h0 (w, z))
      (fun z => by
        have := mul_le_mul_of_nonneg_left (hr1 z) (mul_nonneg (ha0 w) (hq.1 w z))
        simpa using this)
      ((hq.2.1 w).mul_left (a w))
  refine (summable_prod_of_nonneg h0).mpr ⟨hrow, ?_⟩
  refine Summable.of_nonneg_of_le (fun w => tsum_nonneg fun z => h0 (w, z)) (fun w => ?_) has
  calc ∑' z, a w * q w z * r z ≤ ∑' z, a w * q w z :=
        Summable.tsum_le_tsum (fun z => by
          have := mul_le_mul_of_nonneg_left (hr1 z) (mul_nonneg (ha0 w) (hq.1 w z))
          simpa using this) (hrow w) ((hq.2.1 w).mul_left (a w))
    _ = a w * ∑' z, q w z := tsum_mul_left
    _ ≤ a w * 1 := mul_le_mul_of_nonneg_left (hq.2.2 w) (ha0 w)
    _ = a w := mul_one _

/-- Exchange of the order of summation for `a(w) q(w, z) r(z)`. -/
lemma tsum_comm_triple {a : X → ℝ} (ha0 : ∀ w, 0 ≤ a w) (has : Summable a) {q : X → X → ℝ}
    (hq : IsSub q) {r : X → ℝ} (hr0 : ∀ z, 0 ≤ r z) (hr1 : ∀ z, r z ≤ 1) :
    ∑' w, a w * ∑' z, q w z * r z = ∑' z, (∑' w, a w * q w z) * r z := by
  have hs := summable_triple ha0 has hq hr0 hr1
  have hcomm := Summable.tsum_comm (f := fun w z => a w * q w z * r z) hs
  have hcol : ∀ z, Summable (fun w => a w * q w z * r z) :=
    fun z => hs.prod_symm.prod_factor z
  calc ∑' w, a w * ∑' z, q w z * r z = ∑' w, ∑' z, a w * q w z * r z := by
        refine tsum_congr fun w => ?_
        rw [← tsum_mul_left]; exact tsum_congr fun z => by ring
    _ = ∑' z, ∑' w, a w * q w z * r z := hcomm.symm
    _ = ∑' z, (∑' w, a w * q w z) * r z := by
        refine tsum_congr fun z => ?_
        rw [← tsum_mul_right]

/-- The weighted column sums `z ↦ ∑_w a(w) q(w, z)` are summable with total `≤ ∑ a`. -/
lemma summable_col {a : X → ℝ} (ha0 : ∀ w, 0 ≤ a w) (has : Summable a) {q : X → X → ℝ}
    (hq : IsSub q) :
    Summable (fun z => ∑' w, a w * q w z) ∧ (∀ z, Summable (fun w => a w * q w z)) ∧
      ∑' z, ∑' w, a w * q w z ≤ ∑' w, a w := by
  have hs := summable_triple ha0 has hq (r := fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl)
  simp only [mul_one] at hs
  refine ⟨?_, fun z => ?_, ?_⟩
  · have := hs.prod_symm.prod
    simpa using this
  · have := hs.prod_symm.prod_factor z
    simpa using this
  · have h := tsum_comm_triple ha0 has hq (r := fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl)
    simp only [mul_one] at h
    rw [← h]
    refine Summable.tsum_le_tsum (fun w => ?_) ?_ has
    · calc a w * ∑' z, q w z ≤ a w * 1 := mul_le_mul_of_nonneg_left (hq.2.2 w) (ha0 w)
        _ = a w := mul_one _
    · refine Summable.of_nonneg_of_le (fun w => mul_nonneg (ha0 w) (tsum_nonneg (hq.1 w)))
        (fun w => ?_) has
      calc a w * ∑' z, q w z ≤ a w * 1 := mul_le_mul_of_nonneg_left (hq.2.2 w) (ha0 w)
        _ = a w := mul_one _

variable [DecidableEq X]

lemma stepProb_zero (p : X → X → ℝ) (x y : X) :
    stepProb p 0 x y = if x = y then 1 else 0 := rfl

lemma stepProb_succ (p : X → X → ℝ) (n : ℕ) (x y : X) :
    stepProb p (n + 1) x y = ∑' z, p x z * stepProb p n z y := rfl

lemma isSub_stepProb {p : X → X → ℝ} (hp : IsSub p) : ∀ n, IsSub (stepProb p n) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun x y => by simp only [stepProb_zero]; split_ifs <;> norm_num, fun x => ?_,
      fun x => ?_⟩
    · exact (hasSum_ite_eq x (1 : ℝ)).summable.congr fun y => by
        simp only [stepProb_zero]; split_ifs <;> simp_all [eq_comm]
    · have : (fun y => stepProb p 0 x y) = fun y => if y = x then 1 else 0 := by
        funext y; simp only [stepProb_zero]; split_ifs <;> simp_all [eq_comm]
      rw [this, tsum_ite_eq]
  | succ n ih =>
    refine ⟨fun x y => tsum_nonneg fun z => mul_nonneg (hp.1 x z) (ih.1 z y), fun x => ?_,
      fun x => ?_⟩
    · exact (summable_col (hp.1 x) (hp.2.1 x) ih).1
    · exact le_trans (summable_col (hp.1 x) (hp.2.1 x) ih).2.2 (hp.2.2 x)

lemma stepProb_nonneg {p : X → X → ℝ} (hp : IsSub p) (n : ℕ) (x y : X) :
    0 ≤ stepProb p n x y := (isSub_stepProb hp n).1 x y

lemma stepProb_le_one {p : X → X → ℝ} (hp : IsSub p) (n : ℕ) (x y : X) :
    stepProb p n x y ≤ 1 := (isSub_stepProb hp n).le_one x y

/-- Rows of powers of a transition kernel sum to one. -/
lemma tsum_stepProb {p : X → X → ℝ} (hp : IsTransition p) (n : ℕ) (x : X) :
    ∑' y, stepProb p n x y = 1 := by
  induction n generalizing x with
  | zero =>
    have : (fun y => stepProb p 0 x y) = fun y => if y = x then 1 else 0 := by
      funext y; simp only [stepProb_zero]; split_ifs <;> simp_all [eq_comm]
    rw [this, tsum_ite_eq]
  | succ n ih =>
    have hs := isSub_of_isTransition hp
    have h := tsum_comm_triple (hs.1 x) (hs.2.1 x) (isSub_stepProb hs n) (r := fun _ => 1)
      (fun _ => zero_le_one) (fun _ => le_rfl)
    simp only [mul_one, ih] at h
    simp only [stepProb_succ]
    rw [← h, hp.2.2 x]

/-- Chapman–Kolmogorov. -/
lemma stepProb_add {p : X → X → ℝ} (hp : IsSub p) (m n : ℕ) (x y : X) :
    stepProb p (m + n) x y = ∑' z, stepProb p m x z * stepProb p n z y := by
  induction m generalizing x with
  | zero =>
    simp only [zero_add, stepProb_zero]
    have : (fun z => (if x = z then (1 : ℝ) else 0) * stepProb p n z y) =
        fun z => if z = x then stepProb p n x y else 0 := by
      funext z; split_ifs <;> simp_all [eq_comm]
    rw [this, tsum_ite_eq]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, stepProb_succ]
    simp only [ih]
    have := tsum_comm_triple (hp.1 x) (hp.2.1 x) (isSub_stepProb hp m)
      (r := fun z => stepProb p n z y) (fun z => stepProb_nonneg hp n z y)
      (fun z => stepProb_le_one hp n z y)
    rw [this]
    rfl

lemma stepProb_one {p : X → X → ℝ} (x y : X) : stepProb p 1 x y = p x y := by
  simp only [stepProb_succ, stepProb_zero]
  have : (fun z => p x z * (if z = y then (1 : ℝ) else 0)) = fun z => if z = y then p x y else 0 := by
    funext z; split_ifs with h <;> simp [h]
  rw [this, tsum_ite_eq]

/-- Right peeling: `pⁿ⁺¹(x, y) = ∑_z pⁿ(x, z) p(z, y)`. -/
lemma stepProb_succ' {p : X → X → ℝ} (hp : IsSub p) (n : ℕ) (x y : X) :
    stepProb p (n + 1) x y = ∑' z, stepProb p n x z * p z y := by
  rw [stepProb_add hp n 1]
  simp only [stepProb_one]

/-- Powers of a symmetric kernel are symmetric. -/
lemma stepProb_symm {p : X → X → ℝ} (hp : IsSub p) (hs : IsSymmetric p) (n : ℕ) (x y : X) :
    stepProb p n x y = stepProb p n y x := by
  induction n generalizing x y with
  | zero => simp only [stepProb_zero]; split_ifs <;> simp_all [eq_comm]
  | succ n ih =>
    rw [stepProb_succ, stepProb_succ' hp]
    refine tsum_congr fun z => ?_
    rw [hs x z, ih z y, mul_comm]

/-- Column sums of powers of a symmetric transition kernel are one. -/
lemma tsum_stepProb_col {p : X → X → ℝ} (hp : IsTransition p) (hs : IsSymmetric p) (n : ℕ)
    (y : X) : ∑' z, stepProb p n z y = 1 := by
  rw [← tsum_stepProb hp n y]
  exact tsum_congr fun z => stepProb_symm (isSub_of_isTransition hp) hs n z y

lemma summable_stepProb_col {p : X → X → ℝ} (hp : IsTransition p) (hs : IsSymmetric p) (n : ℕ)
    (y : X) : Summable (fun z => stepProb p n z y) :=
  ((isSub_stepProb (isSub_of_isTransition hp) n).2.1 y).congr fun z =>
    stepProb_symm (isSub_of_isTransition hp) hs n y z

/-! ## The heat kernel -/

lemma uniformize_eq_self {J : X → X → ℝ} (hJ : IsTransition J) : uniformize J = J := by
  funext a b; simp [uniformize, hJ.2.2 a]

/-- The Poisson weights. -/
noncomputable def poi (t : ℝ) (n : ℕ) : ℝ := Real.exp (-t) * t ^ n / n.factorial

lemma poi_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ poi t n := by
  unfold poi; positivity

lemma hasSum_poi (t : ℝ) : HasSum (poi t) 1 := by
  have h := NormedSpace.expSeries_div_hasSum_exp t
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-t))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  have e : poi t = fun i => Real.exp (-t) * (t ^ i / ↑i.factorial) := by
    funext n; unfold poi; ring
  rw [e]; exact h2

lemma summable_poi (t : ℝ) : Summable (poi t) := (hasSum_poi t).summable

lemma tsum_poi (t : ℝ) : ∑' n, poi t n = 1 := (hasSum_poi t).tsum_eq

lemma heatKernel_eq {J : X → X → ℝ} (t : ℝ) (x y : X) :
    heatKernel J t x y = ∑' n, poi t n * stepProb (uniformize J) n x y := rfl

lemma summable_heat {p : X → X → ℝ} (hp : IsSub p) {t : ℝ} (ht : 0 ≤ t) (x y : X) :
    Summable (fun n => poi t n * stepProb p n x y) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (poi_nonneg ht n) (stepProb_nonneg hp n x y))
    (fun n => by
      have := mul_le_mul_of_nonneg_left (stepProb_le_one hp n x y) (poi_nonneg ht n)
      simpa using this)
    (summable_poi t)

end MarkovHK
end

section
/-!
# Binomial and shifted-exponential identities (shared by H9 and H8)
-/

open DurrettProbability MarkovChain

namespace MarkovHK

/-- One Pascal step of the binomial theorem, for a sequence `b`. -/
lemma binom_step (a : ℝ) (b : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : ℝ) * a ^ (n + 1 - k) * b k =
      a * ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ (n - k) * b k +
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ (n - k) * b (k + 1) := by
  rw [Finset.sum_range_succ' _ (n + 1)]
  have h1 : ∀ k ∈ Finset.range (n + 1),
      ((n + 1).choose (k + 1) : ℝ) * a ^ (n + 1 - (k + 1)) * b (k + 1) =
        (n.choose k : ℝ) * a ^ (n - k) * b (k + 1) +
          (n.choose (k + 1) : ℝ) * a ^ (n - k) * b (k + 1) := by
    intro k _
    rw [Nat.choose_succ_succ', Nat.succ_sub_succ]; push_cast; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun k => (n.choose k : ℝ) * a ^ (n - k) * b k) n]
  rw [Finset.sum_range_succ (fun k => (n.choose (k + 1) : ℝ) * a ^ (n - k) * b (k + 1)) n]
  simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right,
    Nat.cast_one, one_mul, Nat.sub_zero]
  rw [mul_add, Finset.mul_sum]
  have h2 : ∀ k ∈ Finset.range n, a * ((n.choose (k + 1) : ℝ) * a ^ (n - (k + 1)) * b (k + 1)) =
      (n.choose (k + 1) : ℝ) * a ^ (n - k) * b (k + 1) := by
    intro k hk
    have : n - k = (n - (k + 1)) + 1 := by have := Finset.mem_range.mp hk; omega
    rw [this, pow_succ]; ring
  rw [Finset.sum_congr rfl h2]
  ring

/-- The shifted exponential series: `∑_j poi(t, j) C(j, k) α^{j−k} = poi(t, k) e^{αt}`. -/
lemma hasSum_shift (t α : ℝ) (k : ℕ) :
    HasSum (fun j => poi t j * (j.choose k : ℝ) * α ^ (j - k)) (poi t k * Real.exp (α * t)) := by
  have hexp := NormedSpace.expSeries_div_hasSum_exp (α * t)
  rw [← Real.exp_eq_exp_ℝ] at hexp
  have h := hexp.mul_left (poi t k)
  rw [← hasSum_nat_add_iff' k]
  have hz : ∑ i ∈ Finset.range k, poi t i * (i.choose k : ℝ) * α ^ (i - k) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi)]; simp
  rw [hz, sub_zero]
  have e : (fun m => poi t (m + k) * ((m + k).choose k : ℝ) * α ^ (m + k - k)) =
      fun m => poi t k * ((α * t) ^ m / m.factorial) := by
    funext m
    have hc : ((m + k).choose k : ℝ) * m.factorial * k.factorial = (m + k).factorial := by
      exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial m k
    have hmf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    have hkf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hmkf : ((m + k).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hch : ((m + k).choose k : ℝ) = (m + k).factorial / (m.factorial * k.factorial) := by
      rw [← hc]; field_simp
    unfold poi
    rw [Nat.add_sub_cancel, hch, mul_pow, pow_add]
    field_simp
  rw [e]; exact h

variable {X : Type*} [DecidableEq X]

lemma summable_ite (x : X) (c : ℝ) : Summable (fun z : X => if x = z then c else 0) :=
  (hasSum_ite_eq x c).summable.congr fun z => by split_ifs <;> simp_all [eq_comm]

lemma tsum_ite (x : X) (c : ℝ) : ∑' z : X, (if x = z then c else 0) = c := by
  rw [show (fun z : X => if x = z then c else 0) = fun z => if z = x then c else 0 by
    funext z; split_ifs <;> simp_all [eq_comm]]
  exact tsum_ite_eq x (fun _ => c)

/-- `q = J − αI`. -/
def qk (J : X → X → ℝ) (α : ℝ) : X → X → ℝ := fun x y => J x y - if x = y then α else 0

lemma isSub_qk {J : X → X → ℝ} (hJ : IsTransition J) {α : ℝ} (hα : 0 ≤ α)
    (hdiag : ∀ x, α ≤ J x x) : IsSub (qk J α) := by
  refine ⟨fun x y => ?_, fun x => ?_, fun x => ?_⟩
  · unfold qk; split_ifs with h
    · subst h; linarith [hdiag x]
    · linarith [hJ.1 x y]
  · exact (hJ.2.1 x).sub (summable_ite x α)
  · unfold qk
    rw [(hJ.2.1 x).tsum_sub (summable_ite x α), hJ.2.2 x, tsum_ite]
    linarith

/-- The binomial expansion `Jⁿ = ∑_{k ≤ n} C(n, k) α^{n−k} qᵏ`. -/
lemma stepProb_binom {J : X → X → ℝ} (hJ : IsTransition J) {α : ℝ} (hα : 0 ≤ α)
    (hdiag : ∀ x, α ≤ J x x) (n : ℕ) :
    ∀ x y, stepProb J n x y =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * α ^ (n - k) * stepProb (qk J α) k x y := by
  have hq := isSub_qk hJ hα hdiag
  have hJS := isSub_of_isTransition hJ
  induction n with
  | zero => intro x y; simp [stepProb_zero]
  | succ n ih =>
    intro x y
    have hsplit : ∀ z, J x z * stepProb J n z y =
        qk J α x z * stepProb J n z y + (if x = z then α * stepProb J n x y else 0) := by
      intro z; unfold qk; split_ifs with h
      · subst h; ring
      · ring
    have hs1 : Summable (fun z => qk J α x z * stepProb J n z y) :=
      Summable.of_nonneg_of_le (fun z => mul_nonneg (hq.1 x z) (stepProb_nonneg hJS n z y))
        (fun z => by
          have := mul_le_mul_of_nonneg_left (stepProb_le_one hJS n z y) (hq.1 x z)
          simpa using this) (hq.2.1 x)
    have hs2 : ∀ k, Summable (fun z => qk J α x z * stepProb (qk J α) k z y) := fun k =>
      Summable.of_nonneg_of_le (fun z => mul_nonneg (hq.1 x z) (stepProb_nonneg hq k z y))
        (fun z => by
          have := mul_le_mul_of_nonneg_left (stepProb_le_one hq k z y) (hq.1 x z)
          simpa using this) (hq.2.1 x)
    rw [stepProb_succ]
    simp only [hsplit]
    rw [hs1.tsum_add (summable_ite x _), tsum_ite]
    have hmid : ∑' z, qk J α x z * stepProb J n z y =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * α ^ (n - k) *
          stepProb (qk J α) (k + 1) x y := by
      simp only [ih]
      simp_rw [Finset.mul_sum]
      rw [Summable.tsum_finsetSum fun k _ => ?_]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [stepProb_succ, ← tsum_mul_left]
        exact tsum_congr fun z => by ring
      · exact ((hs2 k).mul_left ((n.choose k : ℝ) * α ^ (n - k))).congr fun z => by ring
    rw [hmid, ih x y, binom_step α (fun k => stepProb (qk J α) k x y) n]
    ring

end MarkovHK
end

section
/-!
# Heat kernels of transition kernels: semigroup law, off-diagonal bound, comparison

* `heat_semigroup`: `∑_w p(s, u, w) p(s', w, v) = p(s + s', u, v)`;
* `heat_le_avg_diag`: for symmetric `J`, `p(t, u, v) ≤ (p(t, u, u) + p(t, v, v)) / 2`;
* `heat_le_exp_mul_heat`: if `A ≤ B + δ I` entrywise (both transition kernels), then
  `p_A(t) ≤ e^{δt} p_B(t)` entrywise.
-/

open DurrettProbability MarkovChain

namespace MarkovHK

/-! ## Fubini across two index types -/

section Gen

variable {α β : Type*}

lemma summable_triple_gen {a : α → ℝ} (ha0 : ∀ i, 0 ≤ a i) (has : Summable a) {q : α → β → ℝ}
    (hq0 : ∀ i w, 0 ≤ q i w) (hqs : ∀ i, Summable (q i)) (hq1 : ∀ i, ∑' w, q i w ≤ 1)
    {r : β → ℝ} (hr0 : ∀ w, 0 ≤ r w) (hr1 : ∀ w, r w ≤ 1) :
    Summable (fun p : α × β => a p.1 * q p.1 p.2 * r p.2) := by
  have h0 : 0 ≤ (fun p : α × β => a p.1 * q p.1 p.2 * r p.2) := fun p =>
    mul_nonneg (mul_nonneg (ha0 _) (hq0 _ _)) (hr0 _)
  have hle : ∀ i w, a i * q i w * r w ≤ a i * q i w := fun i w => by
    have := mul_le_mul_of_nonneg_left (hr1 w) (mul_nonneg (ha0 i) (hq0 i w))
    simpa using this
  have hrow : ∀ i, Summable (fun w => a i * q i w * r w) := fun i =>
    Summable.of_nonneg_of_le (fun w => h0 (i, w)) (hle i) ((hqs i).mul_left (a i))
  refine (summable_prod_of_nonneg h0).mpr ⟨hrow, ?_⟩
  refine Summable.of_nonneg_of_le (fun i => tsum_nonneg fun w => h0 (i, w)) (fun i => ?_) has
  calc ∑' w, a i * q i w * r w ≤ ∑' w, a i * q i w :=
        Summable.tsum_le_tsum (hle i) (hrow i) ((hqs i).mul_left (a i))
    _ = a i * ∑' w, q i w := tsum_mul_left
    _ ≤ a i * 1 := mul_le_mul_of_nonneg_left (hq1 i) (ha0 i)
    _ = a i := mul_one _

lemma tsum_comm_gen {a : α → ℝ} (ha0 : ∀ i, 0 ≤ a i) (has : Summable a) {q : α → β → ℝ}
    (hq0 : ∀ i w, 0 ≤ q i w) (hqs : ∀ i, Summable (q i)) (hq1 : ∀ i, ∑' w, q i w ≤ 1)
    {r : β → ℝ} (hr0 : ∀ w, 0 ≤ r w) (hr1 : ∀ w, r w ≤ 1) :
    ∑' i, a i * ∑' w, q i w * r w = ∑' w, (∑' i, a i * q i w) * r w := by
  have hs := summable_triple_gen ha0 has hq0 hqs hq1 hr0 hr1
  have hcomm := Summable.tsum_comm (f := fun i w => a i * q i w * r w) hs
  calc ∑' i, a i * ∑' w, q i w * r w = ∑' i, ∑' w, a i * q i w * r w := by
        refine tsum_congr fun i => ?_
        rw [← tsum_mul_left]; exact tsum_congr fun w => by ring
    _ = ∑' w, ∑' i, a i * q i w * r w := hcomm.symm
    _ = ∑' w, (∑' i, a i * q i w) * r w := by
        refine tsum_congr fun w => ?_
        rw [← tsum_mul_right]

lemma summable_col_gen {a : α → ℝ} (ha0 : ∀ i, 0 ≤ a i) (has : Summable a) {q : α → β → ℝ}
    (hq0 : ∀ i w, 0 ≤ q i w) (hqs : ∀ i, Summable (q i)) (hq1 : ∀ i, ∑' w, q i w ≤ 1) :
    Summable (fun w => ∑' i, a i * q i w) := by
  have hs := summable_triple_gen ha0 has hq0 hqs hq1 (r := fun _ => 1) (fun _ => zero_le_one)
    (fun _ => le_rfl)
  simp only [mul_one] at hs
  simpa using hs.prod_symm.prod

end Gen

/-- A summable function on `ℕ × ℕ` sums along antidiagonals. -/
lemma tsum_prod_antidiagonal {F : ℕ × ℕ → ℝ} (hF : Summable F) :
    ∑' p, F p = ∑' n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, F kl := by
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq F]
  have hs : Summable (F ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) :=
    (Equiv.summable_iff _).mpr hF
  have h2 := hs.tsum_sigma' (fun n => (hasSum_fintype _).summable)
  simp only [Function.comp_apply] at h2
  rw [h2]
  refine tsum_congr fun n => ?_
  rw [tsum_fintype]
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  exact Finset.sum_coe_sort _ _

/-- The Poisson convolution `∑_{a+b=n} poi(s, a) poi(s', b) = poi(s + s', n)`. -/
lemma poi_conv (s s' : ℝ) (n : ℕ) :
    ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, poi s kl.1 * poi s' kl.2 = poi (s + s') n := by
  unfold poi
  rw [(Commute.all s s').add_pow', Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have hkl' : kl.1 + kl.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
  have hc : (n.choose kl.1 : ℝ) * kl.1.factorial * kl.2.factorial = n.factorial := by
    have h0 := Nat.add_choose_mul_factorial_mul_factorial kl.2 kl.1
    rw [add_comm kl.2 kl.1, hkl'] at h0
    have h0' : n.choose kl.1 * kl.1.factorial * kl.2.factorial = n.factorial := by
      rw [← h0]; ring
    exact_mod_cast h0'
  have h4 : (n.choose kl.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have h1 : (kl.1.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (kl.2.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h3 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [nsmul_eq_mul, ← hc, neg_add, Real.exp_add]
  field_simp

variable {X : Type*} [DecidableEq X]

lemma heat_nonneg {J : X → X → ℝ} (hJ : IsTransition J) {t : ℝ} (ht : 0 ≤ t) (u v : X) :
    0 ≤ heatKernel J t u v := by
  rw [heatKernel_eq, uniformize_eq_self hJ]
  exact tsum_nonneg fun n => mul_nonneg (poi_nonneg ht n)
    (stepProb_nonneg (isSub_of_isTransition hJ) n u v)

lemma heat_le_one {J : X → X → ℝ} (hJ : IsTransition J) {t : ℝ} (ht : 0 ≤ t) (u v : X) :
    heatKernel J t u v ≤ 1 := by
  rw [heatKernel_eq, uniformize_eq_self hJ, ← tsum_poi t]
  have hS := isSub_of_isTransition hJ
  exact Summable.tsum_le_tsum (fun n => by
    have := mul_le_mul_of_nonneg_left (stepProb_le_one hS n u v) (poi_nonneg ht n)
    simpa using this) (summable_heat hS ht u v) (summable_poi t)

lemma heat_symm {J : X → X → ℝ} (hJ : IsTransition J) (hJs : IsSymmetric J) (t : ℝ) (u v : X) :
    heatKernel J t u v = heatKernel J t v u := by
  rw [heatKernel_eq, heatKernel_eq, uniformize_eq_self hJ]
  exact tsum_congr fun n => by rw [stepProb_symm (isSub_of_isTransition hJ) hJs]

/-- Rows of the heat kernel are summable (with sum one). -/
lemma summable_heat_row {J : X → X → ℝ} (hJ : IsTransition J) {t : ℝ} (ht : 0 ≤ t) (u : X) :
    Summable (fun w => heatKernel J t u w) := by
  have hS := isSub_of_isTransition hJ
  have := summable_col_gen (poi_nonneg ht) (summable_poi t) (q := fun n w => stepProb J n u w)
    (fun n w => stepProb_nonneg hS n u w) (fun n => (isSub_stepProb hS n).2.1 u)
    (fun n => (isSub_stepProb hS n).2.2 u)
  refine this.congr fun w => ?_
  rw [heatKernel_eq, uniformize_eq_self hJ]

/-- The semigroup law. -/
lemma heat_semigroup {J : X → X → ℝ} (hJ : IsTransition J) {s s' : ℝ} (hs : 0 ≤ s)
    (hs' : 0 ≤ s') (u v : X) :
    ∑' w, heatKernel J s u w * heatKernel J s' w v = heatKernel J (s + s') u v := by
  have hS := isSub_of_isTransition hJ
  simp only [heatKernel_eq, uniformize_eq_self hJ]
  -- step 1: pull the sum over `a` out
  have step1 := tsum_comm_gen (poi_nonneg hs) (summable_poi s)
    (q := fun a w => stepProb J a u w) (fun a w => stepProb_nonneg hS a u w)
    (fun a => (isSub_stepProb hS a).2.1 u) (fun a => (isSub_stepProb hS a).2.2 u)
    (r := fun w => ∑' b, poi s' b * stepProb J b w v)
    (fun w => by have := heat_nonneg hJ hs' w v; rwa [heatKernel_eq, uniformize_eq_self hJ] at this)
    (fun w => by have := heat_le_one hJ hs' w v; rwa [heatKernel_eq, uniformize_eq_self hJ] at this)
  rw [← step1]
  -- step 2: inside, pull the sum over `b` out
  have step2 : ∀ a, ∑' w, stepProb J a u w * ∑' b, poi s' b * stepProb J b w v =
      ∑' b, poi s' b * stepProb J (a + b) u v := by
    intro a
    have h := tsum_comm_gen (fun w => stepProb_nonneg hS a u w) ((isSub_stepProb hS a).2.1 u)
      (q := fun w b => poi s' b * stepProb J b w v)
      (fun w b => mul_nonneg (poi_nonneg hs' b) (stepProb_nonneg hS b w v))
      (fun w => summable_heat hS hs' w v)
      (fun w => by have := heat_le_one hJ hs' w v; rwa [heatKernel_eq, uniformize_eq_self hJ] at this)
      (r := fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl)
    simp only [mul_one] at h
    rw [h]
    refine tsum_congr fun b => ?_
    rw [stepProb_add hS a b u v, ← tsum_mul_left]
    exact tsum_congr fun w => by ring
  simp only [step2]
  -- step 3: the double series over `ℕ × ℕ`
  have hrow' : ∀ a, Summable (fun b => poi s' b * stepProb J (a + b) u v) := fun a =>
    Summable.of_nonneg_of_le (fun b => mul_nonneg (poi_nonneg hs' b) (stepProb_nonneg hS _ u v))
      (fun b => by
        have := mul_le_mul_of_nonneg_left (stepProb_le_one hS (a + b) u v) (poi_nonneg hs' b)
        simpa using this) (summable_poi s')
  set G : ℕ × ℕ → ℝ := fun p => poi s p.1 * (poi s' p.2 * stepProb J (p.1 + p.2) u v) with hG
  have hG0 : 0 ≤ G := fun p => mul_nonneg (poi_nonneg hs _)
    (mul_nonneg (poi_nonneg hs' _) (stepProb_nonneg hS _ u v))
  have hGrow : ∀ a, Summable (fun b => G (a, b)) := fun a => (hrow' a).mul_left (poi s a)
  have hGs : Summable G := by
    refine (summable_prod_of_nonneg hG0).mpr ⟨hGrow, ?_⟩
    refine Summable.of_nonneg_of_le (fun a => tsum_nonneg fun b => hG0 (a, b)) (fun a => ?_)
      (summable_poi s)
    calc ∑' b, G (a, b) = poi s a * ∑' b, poi s' b * stepProb J (a + b) u v := by
          rw [← tsum_mul_left]
      _ ≤ poi s a * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (poi_nonneg hs a)
          rw [← tsum_poi s']
          refine Summable.tsum_le_tsum (fun b => ?_) (hrow' a) (summable_poi s')
          have := mul_le_mul_of_nonneg_left (stepProb_le_one hS (a + b) u v) (poi_nonneg hs' b)
          simpa using this
      _ = poi s a := mul_one _
  calc ∑' a, poi s a * ∑' b, poi s' b * stepProb J (a + b) u v
      = ∑' a, ∑' b, G (a, b) := tsum_congr fun a => by rw [← tsum_mul_left]
    _ = ∑' p, G p := hGs.tsum_prod.symm
    _ = ∑' n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, G kl := tsum_prod_antidiagonal hGs
    _ = ∑' n, poi (s + s') n * stepProb J n u v := by
        refine tsum_congr fun n => ?_
        rw [← poi_conv, Finset.sum_mul]
        refine Finset.sum_congr rfl fun kl hkl => ?_
        have hkl' : kl.1 + kl.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
        simp only [hG, hkl']
        ring

lemma tsum_mul_le_avg {a b : X → ℝ} (ha0 : ∀ w, 0 ≤ a w) (hb0 : ∀ w, 0 ≤ b w)
    (ha1 : ∀ w, a w ≤ 1) (hb1 : ∀ w, b w ≤ 1) (has : Summable a) (hbs : Summable b) :
    ∑' w, a w * b w ≤ (∑' w, a w * a w + ∑' w, b w * b w) / 2 := by
  have hsq : ∀ (c : X → ℝ), (∀ w, 0 ≤ c w) → (∀ w, c w ≤ 1) → Summable c →
      Summable (fun w => c w * c w) := fun c h0 h1 hs =>
    Summable.of_nonneg_of_le (fun w => mul_nonneg (h0 w) (h0 w))
      (fun w => by have := mul_le_mul_of_nonneg_left (h1 w) (h0 w); simpa using this) hs
  have hab : Summable (fun w => a w * b w) :=
    Summable.of_nonneg_of_le (fun w => mul_nonneg (ha0 w) (hb0 w))
      (fun w => by have := mul_le_mul_of_nonneg_left (hb1 w) (ha0 w); simpa using this) has
  rw [← (hsq a ha0 ha1 has).tsum_add (hsq b hb0 hb1 hbs), ← tsum_div_const]
  refine Summable.tsum_le_tsum (fun w => ?_) hab
    (((hsq a ha0 ha1 has).add (hsq b hb0 hb1 hbs)).div_const 2)
  nlinarith [sq_nonneg (a w - b w)]

/-- Off the diagonal, by the semigroup law at `t/2`, symmetry and `ab ≤ (a² + b²)/2`. -/
lemma heat_le_avg_diag {J : X → X → ℝ} (hJ : IsTransition J) (hJs : IsSymmetric J) {t : ℝ}
    (ht : 0 ≤ t) (u v : X) :
    heatKernel J t u v ≤ (heatKernel J t u u + heatKernel J t v v) / 2 := by
  have h2 : 0 ≤ t / 2 := by linarith
  have htt : t / 2 + t / 2 = t := by ring
  have hsg := fun a b => heat_semigroup hJ h2 h2 a b
  rw [htt] at hsg
  rw [← hsg u v, ← hsg u u, ← hsg v v]
  have e1 : ∀ c d : X, (fun w => heatKernel J (t / 2) c w * heatKernel J (t / 2) w d) =
      fun w => heatKernel J (t / 2) c w * heatKernel J (t / 2) d w :=
    fun c d => funext fun w => by rw [heat_symm hJ hJs _ w d]
  rw [e1 u v, e1 u u, e1 v v]
  exact tsum_mul_le_avg (fun w => heat_nonneg hJ h2 u w) (fun w => heat_nonneg hJ h2 v w)
    (fun w => heat_le_one hJ h2 u w) (fun w => heat_le_one hJ h2 v w)
    (summable_heat_row hJ h2 u) (summable_heat_row hJ h2 v)

end MarkovHK
end

section
/-!
# Moments `⟨Uⁿ f, f⟩` of a symmetric transition kernel, without the spectral theorem

For `f` supported in a finite set `S`: `gₐ = Uᵃ f` and `mₙ = ⟨Uⁿ f, f⟩`.
* `mom_add`: `m_{a+b} = ⟨gₐ, g_b⟩`;
* `gv_succ`: `g_{a+1} = U gₐ`;
* `contraction`: `‖U h‖₂ ≤ ‖h‖₂` (Jensen and unit column sums);
* `mom_sub_le`: `m₀ − mₙ ≤ n (m₀ − m₁)`, from `m_i − m_{i+1} ≤ m₀ − m₁`.
-/

open DurrettProbability MarkovChain

namespace MarkovHK

variable {X : Type*}

/-- Jensen for sub-probability weights: `(∑ u v)² ≤ ∑ u v²` when `∑ u ≤ 1`. -/
lemma sq_tsum_le {u v : X → ℝ} (hu0 : ∀ w, 0 ≤ u w) (hus : Summable u) (hu1 : ∑' w, u w ≤ 1)
    (huv : Summable (fun w => u w * v w)) (huv2 : Summable (fun w => u w * v w ^ 2)) :
    (∑' w, u w * v w) ^ 2 ≤ ∑' w, u w * v w ^ 2 := by
  set c := ∑' w, u w * v w with hc
  have hexp : ∀ w, u w * (v w - c) ^ 2 = u w * v w ^ 2 - 2 * c * (u w * v w) + c ^ 2 * u w := by
    intro w; ring
  have hs : Summable (fun w => u w * v w ^ 2 - 2 * c * (u w * v w) + c ^ 2 * u w) :=
    (huv2.sub (huv.mul_left (2 * c))).add (hus.mul_left (c ^ 2))
  have h0 : 0 ≤ ∑' w, (u w * v w ^ 2 - 2 * c * (u w * v w) + c ^ 2 * u w) :=
    tsum_nonneg fun w => by rw [← hexp]; exact mul_nonneg (hu0 w) (sq_nonneg _)
  rw [(huv2.sub (huv.mul_left (2 * c))).tsum_add (hus.mul_left (c ^ 2)),
    huv2.tsum_sub (huv.mul_left (2 * c)), tsum_mul_left, tsum_mul_left, ← hc] at h0
  have : c ^ 2 * ∑' w, u w ≤ c ^ 2 := by
    calc c ^ 2 * ∑' w, u w ≤ c ^ 2 * 1 := mul_le_mul_of_nonneg_left hu1 (sq_nonneg c)
      _ = c ^ 2 := mul_one _
  nlinarith

variable [DecidableEq X]

/-- `‖U h‖₂² ≤ ‖h‖₂²` for a symmetric transition kernel `U`. -/
lemma contraction {U : X → X → ℝ} (hU : IsTransition U) (hUs : IsSymmetric U) {h : X → ℝ}
    (hh : Summable (fun w => h w ^ 2)) :
    (∀ z, Summable (fun w => U z w * h w)) ∧ Summable (fun z => (∑' w, U z w * h w) ^ 2) ∧
      ∑' z, (∑' w, U z w * h w) ^ 2 ≤ ∑' w, h w ^ 2 := by
  have hUS := isSub_of_isTransition hU
  have hrow1 : ∀ z, Summable (fun w => U z w * h w) := fun z =>
    Summable.of_norm_bounded (g := fun w => (U z w + h w ^ 2) / 2)
      (((hU.2.1 z).add hh).div_const 2) (fun w => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hU.1 z w)]
        have h1 := hU.1 z w
        have h2 := hUS.le_one z w
        nlinarith [sq_nonneg (|h w| - 1), sq_abs (h w), abs_nonneg (h w)])
  have hrow2 : ∀ z, Summable (fun w => U z w * h w ^ 2) := fun z =>
    Summable.of_nonneg_of_le (fun w => mul_nonneg (hU.1 z w) (sq_nonneg _))
      (fun w => by
        have := mul_le_mul_of_nonneg_right (hUS.le_one z w) (sq_nonneg (h w))
        simpa using this) hh
  -- `∑_z ∑_w U(z,w) h(w)² = ∑_w h(w)²`
  have hcol := summable_col (fun w => sq_nonneg (h w)) hh hUS
  have hfub := tsum_comm_triple (fun w => sq_nonneg (h w)) hh hUS (r := fun _ => 1)
    (fun _ => zero_le_one) (fun _ => le_rfl)
  simp only [mul_one, hU.2.2] at hfub
  have hswap : ∀ z, ∑' w, h w ^ 2 * U w z = ∑' w, U z w * h w ^ 2 := fun z =>
    tsum_congr fun w => by rw [hUs w z]; ring
  have hjen : ∀ z, (∑' w, U z w * h w) ^ 2 ≤ ∑' w, U z w * h w ^ 2 := fun z =>
    sq_tsum_le (hU.1 z) (hU.2.1 z) (hU.2.2 z).le (hrow1 z) (hrow2 z)
  have hsum2 : Summable (fun z => ∑' w, U z w * h w ^ 2) := hcol.1.congr hswap
  refine ⟨hrow1, Summable.of_nonneg_of_le (fun z => sq_nonneg _) hjen hsum2, ?_⟩
  calc ∑' z, (∑' w, U z w * h w) ^ 2 ≤ ∑' z, ∑' w, U z w * h w ^ 2 :=
        Summable.tsum_le_tsum hjen (Summable.of_nonneg_of_le (fun z => sq_nonneg _) hjen hsum2)
          hsum2
    _ = ∑' w, h w ^ 2 := by
        rw [← tsum_congr hswap, ← hfub]

/-- `mₙ = ⟨Uⁿ f, f⟩` for `f` supported in `S`. -/
noncomputable def mom (U : X → X → ℝ) (S : Finset X) (f : X → ℝ) (n : ℕ) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ S, f x * stepProb U n x y * f y

/-- `gₐ = Uᵃ f`. -/
noncomputable def gv (U : X → X → ℝ) (S : Finset X) (f : X → ℝ) (a : ℕ) (z : X) : ℝ :=
  ∑ x ∈ S, stepProb U a z x * f x

section Moments

variable {U : X → X → ℝ} (hU : IsTransition U) (hUs : IsSymmetric U) (S : Finset X) (f : X → ℝ)
include hU hUs

lemma abs_gv_le_sum (a : ℕ) (z : X) : |gv U S f a z| ≤ ∑ x ∈ S, stepProb U a z x * |f x| := by
  have hUS := isSub_of_isTransition hU
  unfold gv
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul, abs_of_nonneg (stepProb_nonneg hUS a z x)]

lemma abs_gv_le (a : ℕ) (z : X) : |gv U S f a z| ≤ ∑ x ∈ S, |f x| := by
  have hUS := isSub_of_isTransition hU
  refine (abs_gv_le_sum hU hUs S f a z).trans (Finset.sum_le_sum fun x _ => ?_)
  have := mul_le_mul_of_nonneg_right (stepProb_le_one hUS a z x) (abs_nonneg (f x))
  simpa using this

lemma summable_abs_gv (a : ℕ) : Summable (fun z => |gv U S f a z|) := by
  refine Summable.of_nonneg_of_le (fun z => abs_nonneg _) (abs_gv_le_sum hU hUs S f a) ?_
  exact summable_sum fun x _ => (summable_stepProb_col hU hUs a x).mul_right _

lemma summable_gv (a : ℕ) : Summable (gv U S f a) :=
  (summable_abs_gv hU hUs S f a).of_abs

lemma summable_gv_mul (a b : ℕ) : Summable (fun z => gv U S f a z * gv U S f b z) := by
  refine Summable.of_norm_bounded (g := fun z => (∑ x ∈ S, |f x|) * |gv U S f b z|)
    ((summable_abs_gv hU hUs S f b).mul_left _) (fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_gv_le hU hUs S f a z) (abs_nonneg _)

lemma summable_gv_sq (a : ℕ) : Summable (fun z => gv U S f a z ^ 2) :=
  (summable_gv_mul hU hUs S f a a).congr fun z => by ring

/-- `m_{a+b} = ⟨gₐ, g_b⟩`. -/
lemma mom_add (a b : ℕ) : mom U S f (a + b) = ∑' z, gv U S f a z * gv U S f b z := by
  have hUS := isSub_of_isTransition hU
  have hsum : ∀ x y, Summable (fun z => stepProb U a x z * stepProb U b z y) := fun x y =>
    Summable.of_nonneg_of_le (fun z => mul_nonneg (stepProb_nonneg hUS a x z)
      (stepProb_nonneg hUS b z y)) (fun z => by
        have := mul_le_mul_of_nonneg_left (stepProb_le_one hUS b z y) (stepProb_nonneg hUS a x z)
        simpa using this) ((isSub_stepProb hUS a).2.1 x)
  unfold mom gv
  simp only [stepProb_add hUS a b]
  have e1 : ∀ x y, f x * (∑' z, stepProb U a x z * stepProb U b z y) * f y =
      ∑' z, f x * (stepProb U a x z * stepProb U b z y) * f y := by
    intro x y; rw [← tsum_mul_left, ← tsum_mul_right]
  simp only [e1]
  rw [Finset.sum_congr rfl fun x _ => (Summable.tsum_finsetSum fun y _ =>
    ((hsum x y).mul_left (f x)).mul_right (f y)).symm]
  rw [(Summable.tsum_finsetSum fun x _ => summable_sum fun y _ =>
    ((hsum x y).mul_left (f x)).mul_right (f y)).symm]
  refine tsum_congr fun z => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [stepProb_symm hUS hUs a x z]; ring

/-- `g_{a+1} = U gₐ`. -/
lemma gv_succ (a : ℕ) (z : X) : gv U S f (a + 1) z = ∑' w, U z w * gv U S f a w := by
  have hUS := isSub_of_isTransition hU
  unfold gv
  simp only [stepProb_succ]
  have hs : ∀ x, Summable (fun w => U z w * stepProb U a w x * f x) := fun x =>
    (Summable.of_nonneg_of_le (fun w => mul_nonneg (hU.1 z w) (stepProb_nonneg hUS a w x))
      (fun w => by
        have := mul_le_mul_of_nonneg_left (stepProb_le_one hUS a w x) (hU.1 z w)
        simpa using this) (hU.2.1 z)).mul_right (f x)
  rw [Finset.sum_congr rfl fun x _ => (tsum_mul_right (f := fun w => U z w * stepProb U a w x)
    (a := f x)).symm, (Summable.tsum_finsetSum fun x _ => hs x).symm]
  refine tsum_congr fun w => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

end Moments

end MarkovHK
end

section
/-!
# H2, part 1: Faber–Krahn and the Nash inequality (counting measure)

* `fk`: `Λ_P(v) ≥ c v^{−β}` (`v ≥ 1`) gives `ℰ(g) ≥ c |Ω|^{−β} ‖g‖²` for `g` supported in `Ω`;
* `nash_fin`: for `f ≥ 0` finitely supported, `‖f‖₂^{2(1+β)} ≤ K ℰ(f) ‖f‖₁^{2β}`, `K = 2·4^β/c`
  (truncation `(f − s)₊`, `s = ‖f‖₂²/(4‖f‖₁)`, Coulhon's "Application" / Grigor'yan's Lemma 2.1);
* `nash_ext`: the same for `0 ≤ g ≤ 1` summable (Tannery's theorem along finite truncations).
-/

open DurrettProbability MarkovChain MarkovHK
open Filter Topology

namespace Coulhon

namespace H2

variable {X : Type*}

lemma dirichletForm_nonneg {P : X → X → ℝ} (hP : ∀ x y, 0 ≤ P x y) (f : X → ℝ) :
    0 ≤ dirichletForm P (fun _ => 1) f := by
  unfold dirichletForm
  exact mul_nonneg (by norm_num) (tsum_nonneg fun p =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (hP _ _)) zero_le_one)

lemma dirichletEigenvalue_nonneg' {P : X → X → ℝ} (hP : ∀ x y, 0 ≤ P x y) (Ω : Finset X) :
    0 ≤ dirichletEigenvalue P (fun _ => 1) Ω := by
  unfold dirichletEigenvalue
  rcases Set.eq_empty_or_nonempty
    {e | ∃ f : X → ℝ, (∀ x ∉ Ω, f x = 0) ∧ normSq (fun _ => 1) f = 1 ∧
      dirichletForm P (fun _ => 1) f = e} with h | h
  · rw [h, Real.sInf_empty]
  · exact le_csInf h fun e ⟨f, _, _, hf⟩ => hf ▸ dirichletForm_nonneg hP f

lemma dirichletForm_smul {P : X → X → ℝ} (f : X → ℝ) (a : ℝ) :
    dirichletForm P (fun _ => 1) (fun x => a * f x) = a ^ 2 * dirichletForm P (fun _ => 1) f := by
  unfold dirichletForm
  rw [← tsum_mul_left]
  have : ∀ p : X × X, (a * f p.1 - a * f p.2) ^ 2 * P p.1 p.2 * 1 =
      a ^ 2 * ((f p.1 - f p.2) ^ 2 * P p.1 p.2 * 1) := fun p => by ring
  simp only [this]
  rw [tsum_mul_left, tsum_mul_left]; ring

lemma normSq_smul (f : X → ℝ) (a : ℝ) :
    normSq (fun _ => 1) (fun x => a * f x) = a ^ 2 * normSq (fun _ => 1) f := by
  unfold normSq
  rw [← tsum_mul_left]
  exact tsum_congr fun x => by ring

/-- Faber–Krahn from the profile. -/
lemma fk {P : X → X → ℝ} (hP : ∀ x y, 0 ≤ P x y) {c β : ℝ}
    (hΛ : ∀ v : ℝ, 1 ≤ v → c * v ^ (-β) ≤ isoperimetricProfile P (fun _ => 1) v)
    (Ω : Finset X) (hΩ : Ω.Nonempty) (g : X → ℝ) (hg : ∀ x ∉ Ω, g x = 0) :
    c * (Ω.card : ℝ) ^ (-β) * normSq (fun _ => 1) g ≤ dirichletForm P (fun _ => 1) g := by
  set a := normSq (fun _ => 1) g with ha
  have ha0 : 0 ≤ a := tsum_nonneg fun x => by positivity
  rcases ha0.lt_or_eq with hapos | hazero
  swap
  · rw [← hazero, mul_zero]; exact dirichletForm_nonneg hP g
  have hcard : (1 : ℝ) ≤ Ω.card := by exact_mod_cast Finset.card_pos.mpr hΩ
  -- `λ₁(Ω) ≤ ℰ(g)/a`
  set f : X → ℝ := fun x => (Real.sqrt a)⁻¹ * g x with hf
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0
  have hsa0 : 0 < Real.sqrt a := Real.sqrt_pos.mpr hapos
  have hfn : normSq (fun _ => 1) f = 1 := by
    rw [hf, normSq_smul, inv_pow, hsa, ← ha, inv_mul_cancel₀ hapos.ne']
  have hfe : dirichletForm P (fun _ => 1) f = dirichletForm P (fun _ => 1) g / a := by
    rw [hf, dirichletForm_smul, inv_pow, hsa]; field_simp
  have hlam1 : dirichletEigenvalue P (fun _ => 1) Ω ≤ dirichletForm P (fun _ => 1) g / a := by
    unfold dirichletEigenvalue
    refine csInf_le ⟨0, fun e ⟨f', _, _, hf'⟩ => hf' ▸ dirichletForm_nonneg hP f'⟩ ?_
    exact ⟨f, fun x hx => by simp [hf, hg x hx], hfn, hfe⟩
  have hΛ1 : isoperimetricProfile P (fun _ => 1) Ω.card ≤ dirichletEigenvalue P (fun _ => 1) Ω := by
    unfold isoperimetricProfile
    refine csInf_le ⟨0, fun e ⟨Ω', _, _, hΩ'⟩ => hΩ' ▸ dirichletEigenvalue_nonneg' hP Ω'⟩ ?_
    exact ⟨Ω, hΩ, by simp, rfl⟩
  have h := (hΛ _ hcard).trans (hΛ1.trans hlam1)
  rw [le_div_iff₀ hapos] at h
  exact h

lemma summable_dirichlet' {P : X → X → ℝ} (hP : IsTransition P) (hPs : IsSymmetric P)
    {g : X → ℝ} (hg2 : Summable (fun x => g x ^ 2)) :
    Summable (fun p : X × X => (g p.1 - g p.2) ^ 2 * P p.1 p.2 * 1) := by
  set G : X × X → ℝ := fun p => g p.1 ^ 2 * P p.1 p.2 with hG
  have hG0 : 0 ≤ G := fun p => mul_nonneg (sq_nonneg _) (hP.1 _ _)
  have hrowG : ∀ x, ∑' y, G (x, y) = g x ^ 2 := fun x => by
    show ∑' y, g x ^ 2 * P x y = g x ^ 2
    rw [tsum_mul_left, hP.2.2 x, mul_one]
  have hGs : Summable G := by
    refine (summable_prod_of_nonneg hG0).mpr ⟨fun x => (hP.2.1 x).mul_left (g x ^ 2), ?_⟩
    exact hg2.congr fun x => (hrowG x).symm
  have hGs' : Summable (G ∘ Prod.swap) := (Equiv.summable_iff (Equiv.prodComm X X)).mpr hGs
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) ((hGs.add hGs').mul_left 2)
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (hP.1 _ _)) zero_le_one
  · have e : (G ∘ Prod.swap) p = g p.2 ^ 2 * P p.1 p.2 := by
      show g p.2 ^ 2 * P p.2 p.1 = g p.2 ^ 2 * P p.1 p.2
      rw [hPs p.2 p.1]
    have e1 : G p = g p.1 ^ 2 * P p.1 p.2 := rfl
    show (g p.1 - g p.2) ^ 2 * P p.1 p.2 * 1 ≤ 2 * (G p + (G ∘ Prod.swap) p)
    rw [e, e1]
    have h1 : (g p.1 - g p.2) ^ 2 ≤ 2 * g p.1 ^ 2 + 2 * g p.2 ^ 2 := by
      nlinarith [sq_nonneg (g p.1 + g p.2)]
    have h2 := hP.1 p.1 p.2
    calc (g p.1 - g p.2) ^ 2 * P p.1 p.2 * 1 = (g p.1 - g p.2) ^ 2 * P p.1 p.2 := by ring
      _ ≤ (2 * g p.1 ^ 2 + 2 * g p.2 ^ 2) * P p.1 p.2 := mul_le_mul_of_nonneg_right h1 h2
      _ = 2 * (g p.1 ^ 2 * P p.1 p.2 + g p.2 ^ 2 * P p.1 p.2) := by ring

/-- Nash for non-negative finitely supported `f`. -/
lemma nash_fin {P : X → X → ℝ} (hP : IsTransition P) (hPs : IsSymmetric P) {c β : ℝ} (hc : 0 < c)
    (hβ : 0 < β)
    (hΛ : ∀ v : ℝ, 1 ≤ v → c * v ^ (-β) ≤ isoperimetricProfile P (fun _ => 1) v)
    (f : X → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfin : (Function.support f).Finite) :
    normSq (fun _ => 1) f ^ (1 + β) ≤
      2 * 4 ^ β / c * dirichletForm P (fun _ => 1) f * (∑' x, f x) ^ (2 * β) := by
  classical
  set S := hfin.toFinset with hS
  have hf : ∀ x ∉ S, f x = 0 := fun x hx => by
    simpa [hS, Set.Finite.mem_toFinset, Function.mem_support] using hx
  set N := normSq (fun _ => 1) f with hN
  set L := ∑' x, f x with hL
  have hNS : N = ∑ x ∈ S, f x ^ 2 := by
    rw [hN]; unfold normSq
    rw [tsum_eq_sum (s := S) (fun x hx => by simp [hf x hx])]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hLS : L = ∑ x ∈ S, f x := tsum_eq_sum fun x hx => hf x hx
  have hN0 : 0 ≤ N := by rw [hNS]; exact Finset.sum_nonneg fun x _ => sq_nonneg _
  have hE0 := dirichletForm_nonneg hP.1 f
  rcases hN0.lt_or_eq with hNpos | hNz
  swap
  · rw [← hNz, Real.zero_rpow (by linarith)]
    exact mul_nonneg (mul_nonneg (by positivity) hE0) (Real.rpow_nonneg (tsum_nonneg hf0) _)
  have hL0 : 0 < L := by
    rw [hLS]
    by_contra hcon
    have hz : ∀ x ∈ S, f x = 0 := fun x hx =>
      (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hf0 x).mp
        (le_antisymm (not_lt.mp hcon) (Finset.sum_nonneg fun x _ => hf0 x)) x hx
    rw [hNS, Finset.sum_eq_zero fun x hx => by simp [hz x hx]] at hNpos
    exact lt_irrefl _ hNpos
  set s := N / (4 * L) with hs
  have hs0 : 0 < s := by positivity
  set h : X → ℝ := fun x => max (f x - s) 0 with hh
  set Ω := S.filter (fun x => s < f x) with hΩ
  have hhΩ : ∀ x ∉ Ω, h x = 0 := by
    intro x hx
    simp only [hh]
    by_cases hxS : x ∈ S
    · have : ¬ s < f x := fun hlt => hx (Finset.mem_filter.mpr ⟨hxS, hlt⟩)
      exact max_eq_right (by linarith [not_lt.mp this])
    · rw [hf x hxS]; exact max_eq_right (by linarith)
  -- `‖h‖² ≥ N/2`
  have hpt : ∀ x, f x ^ 2 ≤ h x ^ 2 + 2 * s * f x := by
    intro x; simp only [hh]
    rcases le_total (f x) s with hle | hle
    · rw [max_eq_right (by linarith)]; nlinarith [hf0 x]
    · rw [max_eq_left (by linarith)]; nlinarith
  have hhn : N / 2 ≤ normSq (fun _ => 1) h := by
    have hhS : normSq (fun _ => 1) h = ∑ x ∈ S, h x ^ 2 := by
      unfold normSq
      rw [tsum_eq_sum (s := S) (fun x hx => by
        have := hhΩ x (fun h' => hx (Finset.mem_filter.mp h').1); simp [this])]
      exact Finset.sum_congr rfl fun x _ => by ring
    have : N ≤ normSq (fun _ => 1) h + 2 * s * L := by
      rw [hNS, hhS, hLS, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun x _ => hpt x
    have e : 2 * s * L = N / 2 := by rw [hs]; field_simp; ring
    linarith
  have hΩne : Ω.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : normSq (fun _ => 1) h = 0 := by
      unfold normSq
      exact (tsum_congr fun x => by rw [hhΩ x (by simp [hne])]; ring).trans tsum_zero
    linarith
  -- `|Ω| ≤ L/s`
  have hcard : (Ω.card : ℝ) ≤ L / s := by
    rw [le_div_iff₀ hs0, hLS]
    calc (Ω.card : ℝ) * s = ∑ x ∈ Ω, s := by simp [mul_comm]
      _ ≤ ∑ x ∈ Ω, f x := Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2.le
      _ ≤ ∑ x ∈ S, f x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun x _ _ => hf0 x
  have hcard1 : (1 : ℝ) ≤ Ω.card := by exact_mod_cast Finset.card_pos.mpr hΩne
  -- `ℰ(h) ≤ ℰ(f)`
  have hf2 : Summable (fun x => f x ^ 2) :=
    summable_of_ne_finset_zero (s := S) fun x hx => by simp [hf x hx]
  have hh2 : Summable (fun x => h x ^ 2) :=
    summable_of_ne_finset_zero (s := S) fun x hx => by
      have := hhΩ x (fun h' => hx (Finset.mem_filter.mp h').1); simp [this]
  have hEh : dirichletForm P (fun _ => 1) h ≤ dirichletForm P (fun _ => 1) f := by
    unfold dirichletForm
    refine mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum (fun p => ?_)
      (summable_dirichlet' hP hPs hh2) (summable_dirichlet' hP hPs hf2)) (by norm_num)
    have hl : (h p.1 - h p.2) ^ 2 ≤ (f p.1 - f p.2) ^ 2 := by
      have := abs_max_sub_max_le_abs (f p.1 - s) (f p.2 - s) 0
      rw [show f p.1 - s - (f p.2 - s) = f p.1 - f p.2 by ring] at this
      rw [← sq_abs, ← sq_abs (f p.1 - f p.2)]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have := hP.1 p.1 p.2
    nlinarith
  -- Faber–Krahn on `Ω`
  have hFK := fk hP.1 hΛ Ω hΩne h hhΩ
  have hpow : (L / s) ^ (-β) ≤ (Ω.card : ℝ) ^ (-β) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hcard (by linarith)
  have hmain : c * (L / s) ^ (-β) * (N / 2) ≤ dirichletForm P (fun _ => 1) f := by
    calc c * (L / s) ^ (-β) * (N / 2) ≤ c * (Ω.card : ℝ) ^ (-β) * normSq (fun _ => 1) h := by
          gcongr
      _ ≤ _ := hFK.trans hEh
  -- algebra
  have hLs : (L / s) ^ (-β) = N ^ β * (4 ^ β)⁻¹ * (L ^ (2 * β))⁻¹ := by
    rw [hs, show L / (N / (4 * L)) = 4 * L ^ 2 / N by field_simp, Real.rpow_neg (by positivity),
      Real.div_rpow (by positivity) hN0, Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_natCast L 2, ← Real.rpow_mul hL0.le]
    push_cast
    field_simp
  rw [hLs] at hmain
  rw [Real.rpow_add hNpos, Real.rpow_one]
  have h4 : 0 < (4 : ℝ) ^ β := by positivity
  have hL2 : 0 < L ^ (2 * β) := by positivity
  have hNb : 0 < N ^ β := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hc]
  have e : c * (N ^ β * (4 ^ β)⁻¹ * (L ^ (2 * β))⁻¹) * (N / 2) * (2 * 4 ^ β * L ^ (2 * β)) =
      N * N ^ β * c := by field_simp
  have := mul_le_mul_of_nonneg_right hmain (by positivity : (0 : ℝ) ≤ 2 * 4 ^ β * L ^ (2 * β))
  rw [e] at this
  linarith

/-- The domination for the Dirichlet summand of `0 ≤ g`, `g² summable`. -/
lemma summable_bound {P : X → X → ℝ} (hP : IsTransition P) (hPs : IsSymmetric P) {g : X → ℝ}
    (hg2 : Summable (fun x => g x ^ 2)) :
    Summable (fun p : X × X => 2 * (g p.1 ^ 2 * P p.1 p.2 + g p.2 ^ 2 * P p.1 p.2)) := by
  set G : X × X → ℝ := fun p => g p.1 ^ 2 * P p.1 p.2 with hG
  have hG0 : 0 ≤ G := fun p => mul_nonneg (sq_nonneg _) (hP.1 _ _)
  have hrowG : ∀ x, ∑' y, G (x, y) = g x ^ 2 := fun x => by
    show ∑' y, g x ^ 2 * P x y = g x ^ 2
    rw [tsum_mul_left, hP.2.2 x, mul_one]
  have hGs : Summable G := by
    refine (summable_prod_of_nonneg hG0).mpr ⟨fun x => (hP.2.1 x).mul_left (g x ^ 2), ?_⟩
    exact hg2.congr fun x => (hrowG x).symm
  have hGs' : Summable (G ∘ Prod.swap) := (Equiv.summable_iff (Equiv.prodComm X X)).mpr hGs
  refine ((hGs.add hGs').mul_left 2).congr fun p => ?_
  show 2 * (g p.1 ^ 2 * P p.1 p.2 + g p.2 ^ 2 * P p.2 p.1) = _
  rw [hPs p.2 p.1]

/-- Nash for `0 ≤ g ≤ 1` summable, by finite truncations (Tannery). -/
lemma nash_ext {P : X → X → ℝ} (hP : IsTransition P) (hPs : IsSymmetric P) {K β : ℝ} (hβ : 0 < β)
    (hnash : ∀ f : X → ℝ, (∀ x, 0 ≤ f x) → (Function.support f).Finite →
      normSq (fun _ => 1) f ^ (1 + β) ≤ K * dirichletForm P (fun _ => 1) f * (∑' x, f x) ^ (2 * β))
    (g : X → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) (hgs : Summable g) :
    normSq (fun _ => 1) g ^ (1 + β) ≤ K * dirichletForm P (fun _ => 1) g * (∑' x, g x) ^ (2 * β) := by
  classical
  set gF : Finset X → X → ℝ := fun F x => if x ∈ F then g x else 0 with hgF
  have hg2 : Summable (fun x => g x ^ 2) :=
    Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => by nlinarith [hg0 x, hg1 x]) hgs
  have hN : Tendsto (fun F => normSq (fun _ => 1) (gF F)) atTop (𝓝 (normSq (fun _ => 1) g)) := by
    have h := (hg2.mul_right 1).hasSum
    unfold normSq
    have e : ∀ F, ∑' x, gF F x ^ 2 * 1 = ∑ x ∈ F, g x ^ 2 * 1 := fun F => by
      rw [tsum_eq_sum (s := F) (fun x hx => by simp [hgF, hx])]
      exact Finset.sum_congr rfl fun x hx => by simp [hgF, hx]
    simp only [e]
    exact h
  have hL : Tendsto (fun F => ∑' x, gF F x) atTop (𝓝 (∑' x, g x)) := by
    have h := hgs.hasSum
    have e : ∀ F, ∑' x, gF F x = ∑ x ∈ F, g x := fun F => by
      rw [tsum_eq_sum (s := F) (fun x hx => by simp [hgF, hx])]
      exact Finset.sum_congr rfl fun x hx => by simp [hgF, hx]
    simp only [e]
    exact h
  have hE : Tendsto (fun F => dirichletForm P (fun _ => 1) (gF F)) atTop
      (𝓝 (dirichletForm P (fun _ => 1) g)) := by
    unfold dirichletForm
    refine Tendsto.const_mul _ ?_
    refine tendsto_tsum_of_dominated_convergence (summable_bound hP hPs hg2) (fun p => ?_) ?_
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop ({p.1, p.2} : Finset X)] with F hF
      have h1 : p.1 ∈ F := hF (by simp)
      have h2 : p.2 ∈ F := hF (by simp)
      simp [hgF, h1, h2]
    · refine Filter.Eventually.of_forall fun F p => ?_
      have ha : 0 ≤ gF F p.1 ∧ gF F p.1 ≤ g p.1 := by
        simp only [hgF]; split_ifs
        · exact ⟨hg0 _, le_rfl⟩
        · exact ⟨le_rfl, hg0 _⟩
      have hb : 0 ≤ gF F p.2 ∧ gF F p.2 ≤ g p.2 := by
        simp only [hgF]; split_ifs
        · exact ⟨hg0 _, le_rfl⟩
        · exact ⟨le_rfl, hg0 _⟩
      have hP0 := hP.1 p.1 p.2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hP0) zero_le_one)]
      have h1 : (gF F p.1 - gF F p.2) ^ 2 ≤ 2 * g p.1 ^ 2 + 2 * g p.2 ^ 2 := by
        nlinarith [sq_nonneg (gF F p.1 + gF F p.2)]
      nlinarith
  have hlhs := hN.rpow_const (Or.inr (by linarith : (0 : ℝ) ≤ 1 + β))
  have hrhs := (hE.const_mul K).mul (hL.rpow_const (Or.inr (by linarith : (0 : ℝ) ≤ 2 * β)))
  refine le_of_tendsto_of_tendsto' hlhs hrhs fun F => ?_
  refine hnash (gF F) (fun x => ?_) ?_
  · simp only [hgF]; split_ifs
    · exact hg0 x
    · exact le_rfl
  · refine (F.finite_toSet).subset fun x hx => ?_
    by_contra hxF
    have hxF' : x ∉ F := fun h => hxF (Finset.mem_coe.mpr h)
    exact hx (by simp [hgF, hxF'])

end H2

end Coulhon
end

section
/-!
# H2, part 2: the lazy chain `W = (I + P)/2` and its return probabilities

With `mₖ = Wᵏ(x, x)` and `gₙ = Wⁿ δₓ`: `m_{2n} = ‖gₙ‖²`, `‖gₙ‖₁ = 1`,
`m_{2n} − m_{2n+1} = ℰ_W(gₙ) = ℰ_P(gₙ)/2`, `m_{2n+1} ≥ m_{2n+2}` (contraction of `P`), so the Nash
inequality gives `m_{2n} − m_{2n+2} ≥ m_{2n}^{1+β}/(2K)` and `m_{2n} ≤ (βn/(2K))^{−1/β}`.
-/

open DurrettProbability MarkovChain MarkovHK

namespace Coulhon

namespace H2

/-- The discrete comparison lemma: `a uₙ^{1+β} ≤ uₙ − u_{n+1}` gives `βan ≤ uₙ^{−β}` (or `uₙ = 0`). -/
lemma ode_discrete {u : ℕ → ℝ} {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (hu0 : ∀ n, 0 ≤ u n)
    (hstep : ∀ n, a * u n ^ (1 + β) ≤ u n - u (n + 1)) :
    ∀ n : ℕ, u n = 0 ∨ β * a * n ≤ u n ^ (-β) := by
  intro n
  induction n with
  | zero => right; simp only [Nat.cast_zero, mul_zero]; exact Real.rpow_nonneg (hu0 0) _
  | succ n ih =>
    rcases (hu0 (n + 1)).lt_or_eq with hpos | hz
    swap
    · left; exact hz.symm
    right
    have hs := hstep n
    have hun : 0 < u n := by
      have : 0 ≤ a * u n ^ (1 + β) := mul_nonneg ha.le (Real.rpow_nonneg (hu0 n) _)
      linarith
    have ih' : β * a * n ≤ u n ^ (-β) := ih.resolve_left hun.ne'
    set y := a * u n ^ β with hy
    have hy0 : 0 ≤ y := mul_nonneg ha.le (Real.rpow_nonneg hun.le _)
    have hsplit : u n ^ (1 + β) = u n * u n ^ β := by
      rw [Real.rpow_add hun, Real.rpow_one]
    have hle : u (n + 1) ≤ u n * (1 - y) := by
      rw [hsplit] at hs; rw [hy]; nlinarith
    have hy1 : 0 < 1 - y := by
      by_contra hc
      have : u n * (1 - y) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hun.le (not_lt.mp hc)
      linarith
    have h1 : (u n * (1 - y)) ^ (-β) ≤ u (n + 1) ^ (-β) :=
      Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
    rw [Real.mul_rpow hun.le hy1.le] at h1
    have h2 : 1 + β * y ≤ (1 - y) ^ (-β) := by
      rw [Real.rpow_def_of_pos hy1]
      have hlog : Real.log (1 - y) ≤ -y := by
        have := Real.log_le_sub_one_of_pos hy1; linarith
      have := Real.add_one_le_exp (Real.log (1 - y) * -β)
      nlinarith
    have h3 : u n ^ (-β) * u n ^ β = 1 := by
      rw [← Real.rpow_add hun]; simp
    have h4 : u n ^ (-β) * (1 + β * y) = u n ^ (-β) + β * a := by
      rw [hy]; linear_combination (β * a) * h3
    have h5 : u n ^ (-β) * (1 + β * y) ≤ u n ^ (-β) * (1 - y) ^ (-β) :=
      mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hun.le _)
    push_cast
    nlinarith

/-- The decay `uₙ ≤ (βan)^{−1/β}` for `n ≥ 1`. -/
lemma ode_decay {u : ℕ → ℝ} {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (hu0 : ∀ n, 0 ≤ u n)
    (hstep : ∀ n, a * u n ^ (1 + β) ≤ u n - u (n + 1)) (n : ℕ) (hn : 1 ≤ n) :
    u n ≤ (β * a * n) ^ (-1 / β) := by
  have hpos : 0 < β * a * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  rcases ode_discrete ha hβ hu0 hstep n with hz | h
  · rw [hz]; exact Real.rpow_nonneg hpos.le _
  · rcases (hu0 n).lt_or_eq with hun | hz
    · have hz : -1 / β ≤ 0 := by
        have : 0 < 1 / β := by positivity
        rw [neg_div]; linarith
      have := Real.rpow_le_rpow_of_nonpos (z := -1 / β) hpos h hz
      rw [← Real.rpow_mul hun.le, show -β * (-1 / β) = 1 by field_simp, Real.rpow_one] at this
      exact this
    · rw [← hz]; exact Real.rpow_nonneg hpos.le _

variable {X : Type*} [DecidableEq X]

/-- The lazy kernel. -/
noncomputable def lazy (P : X → X → ℝ) : X → X → ℝ := fun x y => (P x y + if x = y then 1 else 0) / 2

lemma isTransition_lazy {P : X → X → ℝ} (hP : IsTransition P) : IsTransition (lazy P) := by
  refine ⟨fun x y => ?_, fun x => ?_, fun x => ?_⟩
  · unfold lazy; have := hP.1 x y; split_ifs <;> linarith
  · exact ((hP.2.1 x).add (summable_ite x 1)).div_const 2
  · unfold lazy
    rw [tsum_div_const, (hP.2.1 x).tsum_add (summable_ite x 1), hP.2.2 x, tsum_ite]; norm_num

lemma isSymmetric_lazy {P : X → X → ℝ} (hPs : IsSymmetric P) : IsSymmetric (lazy P) := by
  intro x y; unfold lazy; rw [hPs x y]
  by_cases h : x = y
  · subst h; rfl
  · simp [h, Ne.symm h]

lemma dirichletForm_lazy (P : X → X → ℝ) (g : X → ℝ) :
    dirichletForm (lazy P) (fun _ => 1) g = dirichletForm P (fun _ => 1) g / 2 := by
  unfold dirichletForm lazy
  have : ∀ p : X × X, (g p.1 - g p.2) ^ 2 * ((P p.1 p.2 + if p.1 = p.2 then 1 else 0) / 2) * 1 =
      ((g p.1 - g p.2) ^ 2 * P p.1 p.2 * 1) / 2 := by
    intro p; split_ifs with h
    · rw [h]; ring
    · ring
  simp only [this]
  rw [tsum_div_const]; ring

/-- The `ℓ²` Dirichlet identity `ℰ_U(g) = ‖g‖² − ⟨g, U g⟩` for `0 ≤ g ≤ 1` summable. -/
lemma dirichlet_eq_inner {U : X → X → ℝ} (hU : IsTransition U) (hUs : IsSymmetric U) {g : X → ℝ}
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) (hgs : Summable g) :
    dirichletForm U (fun _ => 1) g = ∑' x, g x ^ 2 - ∑' x, g x * ∑' y, U x y * g y := by
  have hg2 : Summable (fun x => g x ^ 2) :=
    Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => by nlinarith [hg0 x, hg1 x]) hgs
  set A : X × X → ℝ := fun p => g p.1 ^ 2 * U p.1 p.2 with hA
  set C : X × X → ℝ := fun p => g p.1 * (U p.1 p.2 * g p.2) with hC
  have hA0 : 0 ≤ A := fun p => mul_nonneg (sq_nonneg _) (hU.1 _ _)
  have hrowA : ∀ x, ∑' y, A (x, y) = g x ^ 2 := fun x => by
    show ∑' y, g x ^ 2 * U x y = g x ^ 2
    rw [tsum_mul_left, hU.2.2 x, mul_one]
  have hAs : Summable A :=
    (summable_prod_of_nonneg hA0).mpr ⟨fun x => (hU.2.1 x).mul_left (g x ^ 2), hg2.congr fun x =>
      (hrowA x).symm⟩
  have hBs : Summable (A ∘ Prod.swap) := (Equiv.summable_iff (Equiv.prodComm X X)).mpr hAs
  have hC0 : 0 ≤ C := fun p => mul_nonneg (hg0 _) (mul_nonneg (hU.1 _ _) (hg0 _))
  have hCs : Summable C := by
    refine Summable.of_nonneg_of_le hC0 (fun p => ?_) ((hAs.add hBs).div_const 2)
    show g p.1 * (U p.1 p.2 * g p.2) ≤ (g p.1 ^ 2 * U p.1 p.2 + g p.2 ^ 2 * U p.2 p.1) / 2
    rw [hUs p.2 p.1]
    have h1 := mul_nonneg (hU.1 p.1 p.2) (sq_nonneg (g p.1 - g p.2))
    have key : (g p.1 ^ 2 * U p.1 p.2 + g p.2 ^ 2 * U p.1 p.2) / 2 - g p.1 * (U p.1 p.2 * g p.2) =
        U p.1 p.2 * (g p.1 - g p.2) ^ 2 / 2 := by ring
    linarith
  have hsplit : (fun p : X × X => (g p.1 - g p.2) ^ 2 * U p.1 p.2 * 1) =
      fun p => A p + (A ∘ Prod.swap) p - 2 * C p := by
    funext p
    show (g p.1 - g p.2) ^ 2 * U p.1 p.2 * 1 =
      g p.1 ^ 2 * U p.1 p.2 + g p.2 ^ 2 * U p.2 p.1 - 2 * (g p.1 * (U p.1 p.2 * g p.2))
    rw [hUs p.2 p.1]; ring
  have hBt : ∑' p, (A ∘ Prod.swap) p = ∑' p, A p := (Equiv.prodComm X X).tsum_eq A
  unfold dirichletForm
  rw [hsplit, (hAs.add hBs).tsum_sub (hCs.mul_left 2), hAs.tsum_add hBs,
    hBt, tsum_mul_left, hAs.tsum_prod, hCs.tsum_prod]
  simp only [hrowA]
  have e : ∀ x, ∑' y, C (x, y) = g x * ∑' y, U x y * g y := fun x => by
    show ∑' y, g x * (U x y * g y) = _
    rw [tsum_mul_left]
  simp only [e]
  ring

/-- The point mass. -/
def dl (x : X) : X → ℝ := fun y => if y = x then 1 else 0

lemma gv_dl (U : X → X → ℝ) (x : X) (n : ℕ) (z : X) : gv U {x} (dl x) n z = stepProb U n z x := by
  simp [gv, dl]

lemma mom_dl (U : X → X → ℝ) (x : X) (k : ℕ) : mom U {x} (dl x) k = stepProb U k x x := by
  simp [mom, dl]

section Decay

variable {P : X → X → ℝ} (hP : IsTransition P) (hPs : IsSymmetric P)
include hP hPs

/-- `‖gⱼ‖² − ⟨gⱼ, W gⱼ⟩ = ℰ_W(gⱼ)`, i.e. `m_{2j} − m_{2j+1} = ℰ_W(gⱼ)`. -/
lemma lazy_dirichlet (x : X) (j : ℕ) :
    dirichletForm (lazy P) (fun _ => 1) (gv (lazy P) {x} (dl x) j) =
      mom (lazy P) {x} (dl x) (j + j) - mom (lazy P) {x} (dl x) (j + (j + 1)) := by
  have hW := isTransition_lazy hP
  have hWs := isSymmetric_lazy hPs
  have hWS := isSub_of_isTransition hW
  set g := gv (lazy P) {x} (dl x) j with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z => by rw [hg, gv_dl]; exact stepProb_nonneg hWS j z x
  have hg1 : ∀ z, g z ≤ 1 := fun z => by rw [hg, gv_dl]; exact stepProb_le_one hWS j z x
  rw [dirichlet_eq_inner hW hWs hg0 hg1 (summable_gv hW hWs _ _ j), mom_add hW hWs,
    mom_add hW hWs]
  congr 1
  · exact tsum_congr fun z => by ring
  · exact tsum_congr fun z => by rw [gv_succ hW hWs]

/-- `m_{2j+1} ≤ m_{2j}`. -/
lemma lazy_odd_le (x : X) (j : ℕ) :
    stepProb (lazy P) (2 * j + 1) x x ≤ stepProb (lazy P) (2 * j) x x := by
  have h := lazy_dirichlet hP hPs x j
  have h0 := dirichletForm_nonneg (isTransition_lazy hP).1 (gv (lazy P) {x} (dl x) j)
  rw [mom_dl, mom_dl] at h
  rw [show 2 * j = j + j by ring, show j + j + 1 = j + (j + 1) by ring]
  linarith

/-- `m_{2j+2} ≤ m_{2j+1}`: the contraction of `P` on `gⱼ`, `P gⱼ = 2 g_{j+1} − gⱼ`. -/
lemma lazy_even_le (x : X) (j : ℕ) :
    stepProb (lazy P) (2 * j + 2) x x ≤ stepProb (lazy P) (2 * j + 1) x x := by
  have hW := isTransition_lazy hP
  have hWs := isSymmetric_lazy hPs
  set g := gv (lazy P) {x} (dl x) j with hg
  set g' := gv (lazy P) {x} (dl x) (j + 1) with hg'
  have hg2 : Summable (fun z => g z ^ 2) := summable_gv_sq hW hWs {x} (dl x) j
  obtain ⟨hrow, hsum, hle⟩ := contraction hP hPs (h := g) hg2
  have hPg : ∀ z, ∑' w, P z w * g w = 2 * g' z - g z := by
    intro z
    have h1 := gv_succ hW hWs {x} (dl x) j z
    rw [← hg, ← hg'] at h1
    have h2 : ∑' w, lazy P z w * g w = (∑' w, P z w * g w + g z) / 2 := by
      unfold lazy
      have e : ∀ w, (P z w + if z = w then 1 else 0) / 2 * g w =
          (P z w * g w + if z = w then g z else 0) / 2 := fun w => by
        split_ifs with h
        · rw [h]; ring
        · ring
      simp only [e]
      rw [tsum_div_const, (hrow z).tsum_add (summable_ite z (g z)), tsum_ite]
    linarith
  simp only [hPg] at hle
  -- expand `‖2 g' − g‖²`
  have hgg := summable_gv_mul hW hWs {x} (dl x) j j
  have hg'g' := summable_gv_mul hW hWs {x} (dl x) (j + 1) (j + 1)
  have hg'g := summable_gv_mul hW hWs {x} (dl x) (j + 1) j
  have hexp : ∑' z, (2 * g' z - g z) ^ 2 = 4 * ∑' z, g' z * g' z - 4 * ∑' z, g' z * g z +
      ∑' z, g z * g z := by
    have e : ∀ z, (2 * g' z - g z) ^ 2 = 4 * (g' z * g' z) - 4 * (g' z * g z) + g z * g z :=
      fun z => by ring
    simp only [e]
    rw [((hg'g'.mul_left 4).sub (hg'g.mul_left 4)).tsum_add hgg,
      (hg'g'.mul_left 4).tsum_sub (hg'g.mul_left 4), tsum_mul_left, tsum_mul_left]
  have hsq : ∑' w, g w ^ 2 = ∑' z, g z * g z := tsum_congr fun z => by ring
  rw [hexp, hsq] at hle
  rw [← mom_add hW hWs, ← mom_add hW hWs, ← mom_add hW hWs, mom_dl, mom_dl, mom_dl] at hle
  rw [show j + 1 + (j + 1) = 2 * j + 2 by ring, show j + 1 + j = 2 * j + 1 by ring] at hle
  linarith

/-- The return probabilities of the lazy chain decrease. -/
lemma lazy_antitone (x : X) (k : ℕ) : stepProb (lazy P) (k + 1) x x ≤ stepProb (lazy P) k x x := by
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show j + j = 2 * j by ring]; exact lazy_odd_le hP hPs x j
  · rw [show 2 * j + 1 + 1 = 2 * j + 2 by ring]; exact lazy_even_le hP hPs x j

lemma lazy_antitone' (x : X) {k l : ℕ} (hkl : k ≤ l) :
    stepProb (lazy P) l x x ≤ stepProb (lazy P) k x x := by
  induction hkl with
  | refl => exact le_rfl
  | step _ ih => exact (lazy_antitone hP hPs x _).trans ih

/-- The Nash step `m_{2n}^{1+β} ≤ 2K (m_{2n} − m_{2n+2})`. -/
lemma lazy_nash_step {K β : ℝ} (hβ : 0 < β)
    (hnash : ∀ f : X → ℝ, (∀ x, 0 ≤ f x) → (Function.support f).Finite →
      normSq (fun _ => 1) f ^ (1 + β) ≤ K * dirichletForm P (fun _ => 1) f * (∑' x, f x) ^ (2 * β))
    (hK : 0 ≤ K) (x : X) (n : ℕ) :
    stepProb (lazy P) (2 * n) x x ^ (1 + β) ≤
      2 * K * (stepProb (lazy P) (2 * n) x x - stepProb (lazy P) (2 * n + 2) x x) := by
  have hW := isTransition_lazy hP
  have hWs := isSymmetric_lazy hPs
  have hWS := isSub_of_isTransition hW
  set g := gv (lazy P) {x} (dl x) n with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z => by rw [hg, gv_dl]; exact stepProb_nonneg hWS n z x
  have hg1 : ∀ z, g z ≤ 1 := fun z => by rw [hg, gv_dl]; exact stepProb_le_one hWS n z x
  have hgs := summable_gv hW hWs {x} (dl x) n
  have hN := nash_ext hP hPs hβ hnash g hg0 hg1 hgs
  have hL : ∑' z, g z = 1 := by
    rw [hg]; simp only [gv_dl]; exact tsum_stepProb_col hW hWs n x
  have hNg : normSq (fun _ => 1) g = stepProb (lazy P) (2 * n) x x := by
    unfold normSq
    rw [← mom_dl, show 2 * n = n + n by ring, mom_add hW hWs]
    exact tsum_congr fun z => by ring
  have hE : dirichletForm P (fun _ => 1) g =
      2 * (stepProb (lazy P) (2 * n) x x - stepProb (lazy P) (2 * n + 1) x x) := by
    have h1 := lazy_dirichlet hP hPs x n
    rw [dirichletForm_lazy, mom_dl, mom_dl] at h1
    rw [show 2 * n = n + n by ring, show n + n + 1 = n + (n + 1) by ring]
    linarith
  rw [hL, Real.one_rpow, mul_one, hNg, hE] at hN
  have := lazy_even_le hP hPs x n
  nlinarith

end Decay

end H2

end Coulhon
end

section
/-!
# H2, part 3: continuous time

`p_P(t) = ∑ₖ poi(2t, k) Wᵏ` (`e^{−t(I−P)} = e^{−2t(I−W)}`), the Poisson lower tail
`∑_{k < t} poi(2t, k) ≤ e^{−3t/10}`, and `p_P(t, x, y) ≤ C t^{−1/β}`.
-/

open DurrettProbability MarkovChain MarkovHK

namespace Coulhon

namespace H2

variable {X : Type*} [DecidableEq X]

lemma stepProb_smul (P : X → X → ℝ) (c : ℝ) (n : ℕ) (x y : X) :
    stepProb (fun a b => c * P a b) n x y = c ^ n * stepProb P n x y := by
  induction n generalizing x with
  | zero => simp [stepProb_zero]
  | succ n ih =>
    simp only [stepProb_succ, ih]
    rw [← tsum_mul_left]
    exact tsum_congr fun z => by ring

lemma qk_lazy (P : X → X → ℝ) : qk (lazy P) (1 / 2) = fun a b => (1 / 2) * P a b := by
  funext a b; unfold qk lazy; split_ifs <;> ring

lemma poi_two_mul_half (t : ℝ) (k : ℕ) :
    poi (2 * t) k * (1 / 2) ^ k = Real.exp (-t) * poi t k := by
  unfold poi
  rw [mul_pow, show -(2 * t) = -t + -t by ring, Real.exp_add]
  have h2 : (2 : ℝ) ^ k * (1 / 2) ^ k = 1 := by rw [← mul_pow]; norm_num
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp
  linear_combination t ^ k * h2

/-- `p_P(t) = ∑ₖ poi(2t, k) Wᵏ`. -/
lemma heat_eq_lazy {P : X → X → ℝ} (hP : IsTransition P) {t : ℝ} (ht : 0 ≤ t) (x y : X) :
    heatKernel P t x y = ∑' k, poi (2 * t) k * stepProb (lazy P) k x y := by
  have hW := isTransition_lazy hP
  have hPS := isSub_of_isTransition hP
  have hdiag : ∀ z, (1 / 2 : ℝ) ≤ lazy P z z := fun z => by
    unfold lazy; simp only [if_true]; linarith [hP.1 z z]
  have hbin : ∀ k, stepProb (lazy P) k x y = ∑ j ∈ Finset.range (k + 1),
      (k.choose j : ℝ) * (1 / 2) ^ k * stepProb P j x y := by
    intro k
    rw [stepProb_binom hW (by norm_num) hdiag k x y, qk_lazy]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [stepProb_smul]
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show (1 / 2 : ℝ) ^ k = (1 / 2) ^ (k - j) * (1 / 2) ^ j by
      rw [← pow_add, Nat.sub_add_cancel hjk]]
    ring
  set F : ℕ → ℕ → ℝ := fun j k => poi (2 * t) k * (k.choose j : ℝ) * (1 / 2) ^ k * stepProb P j x y
    with hF
  have h2t : 0 ≤ 2 * t := by linarith
  have hF0 : ∀ j k, 0 ≤ F j k := fun j k => mul_nonneg (mul_nonneg (mul_nonneg
    (poi_nonneg h2t k) (Nat.cast_nonneg _)) (by positivity)) (stepProb_nonneg hPS j x y)
  have hrow : ∀ j, HasSum (fun k => F j k) (poi t j * stepProb P j x y) := by
    intro j
    have h := ((hasSum_shift t 1 j).mul_left (Real.exp (-t))).mul_right (stepProb P j x y)
    have e1 : Real.exp (-t) * (poi t j * Real.exp (1 * t)) * stepProb P j x y =
        poi t j * stepProb P j x y := by
      rw [one_mul, show Real.exp (-t) * (poi t j * Real.exp t) = poi t j *
        (Real.exp (-t) * Real.exp t) by ring, ← Real.exp_add]; simp
    rw [e1] at h
    refine h.congr_fun fun k => ?_
    simp only [hF, one_pow, mul_one]
    rw [show poi (2 * t) k * (k.choose j : ℝ) * (1 / 2) ^ k = poi (2 * t) k * (1 / 2) ^ k *
      (k.choose j : ℝ) by ring, poi_two_mul_half]
    ring
  have hFs : Summable (fun p : ℕ × ℕ => F p.1 p.2) := by
    refine (summable_prod_of_nonneg fun p => hF0 p.1 p.2).mpr ⟨fun j => (hrow j).summable, ?_⟩
    simp only [fun j => (hrow j).tsum_eq]
    exact Summable.of_nonneg_of_le (fun j => mul_nonneg (poi_nonneg ht j)
      (stepProb_nonneg hPS j x y)) (fun j => by
        have := mul_le_mul_of_nonneg_left (stepProb_le_one hPS j x y) (poi_nonneg ht j)
        simpa using this) (summable_poi t)
  have hcol : ∀ k, ∑' j, F j k = poi (2 * t) k * stepProb (lazy P) k x y := by
    intro k
    rw [tsum_eq_sum (s := Finset.range (k + 1)) fun j hj => ?_, hbin k, Finset.mul_sum]
    · exact Finset.sum_congr rfl fun j _ => by simp only [hF]; ring
    · rw [Finset.mem_range, not_lt] at hj
      simp only [hF, Nat.choose_eq_zero_of_lt (by omega : k < j)]; simp
  rw [heatKernel_eq, uniformize_eq_self hP]
  calc ∑' j, poi t j * stepProb P j x y = ∑' j, ∑' k, F j k :=
        tsum_congr fun j => (hrow j).tsum_eq.symm
    _ = ∑' k, ∑' j, F j k := (Summable.tsum_comm (f := F) hFs).symm
    _ = ∑' k, poi (2 * t) k * stepProb (lazy P) k x y := tsum_congr hcol

/-- The Poisson lower tail. -/
lemma poisson_tail {t : ℝ} (ht : 0 ≤ t) :
    ∑' k : ℕ, poi (2 * t) k * (if (k : ℝ) < t then 1 else 0) ≤ Real.exp (-(3 / 10 * t)) := by
  have h2t : 0 ≤ 2 * t := by linarith
  have hhalf : HasSum (fun k => poi (2 * t) k * (1 / 2) ^ k) (Real.exp (-t)) := by
    have h := (hasSum_poi t).mul_left (Real.exp (-t))
    rw [mul_one] at h
    exact h.congr_fun fun k => poi_two_mul_half t k
  have hle : ∀ k : ℕ, poi (2 * t) k * (if (k : ℝ) < t then 1 else 0) ≤
      (2 : ℝ) ^ t * (poi (2 * t) k * (1 / 2) ^ k) := by
    intro k
    split_ifs with hk
    · rw [mul_one]
      have h1 : (2 : ℝ) ^ (k : ℝ) ≤ (2 : ℝ) ^ t :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hk.le
      rw [Real.rpow_natCast] at h1
      have h2 : (2 : ℝ) ^ k * (1 / 2) ^ k = 1 := by rw [← mul_pow]; norm_num
      have h3 := poi_nonneg h2t k
      have h4 : 1 ≤ (2 : ℝ) ^ t * (1 / 2) ^ k := by
        calc (1 : ℝ) = 2 ^ k * (1 / 2) ^ k := h2.symm
          _ ≤ 2 ^ t * (1 / 2) ^ k := mul_le_mul_of_nonneg_right h1 (by positivity)
      calc poi (2 * t) k = poi (2 * t) k * 1 := (mul_one _).symm
        _ ≤ poi (2 * t) k * ((2 : ℝ) ^ t * (1 / 2) ^ k) := mul_le_mul_of_nonneg_left h4 h3
        _ = (2 : ℝ) ^ t * (poi (2 * t) k * (1 / 2) ^ k) := by ring
    · rw [mul_zero]; exact mul_nonneg (by positivity) (mul_nonneg (poi_nonneg h2t k) (by positivity))
  calc ∑' k : ℕ, poi (2 * t) k * (if (k : ℝ) < t then 1 else 0)
      ≤ ∑' k : ℕ, (2 : ℝ) ^ t * (poi (2 * t) k * (1 / 2) ^ k) :=
        Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun k => mul_nonneg (poi_nonneg h2t k)
          (by split_ifs <;> norm_num)) (fun k => by
            have := mul_le_mul_of_nonneg_left (show (if (k : ℝ) < t then (1 : ℝ) else 0) ≤ 1 by
              split_ifs <;> norm_num) (poi_nonneg h2t k)
            simpa using this) (summable_poi (2 * t))) (hhalf.summable.mul_left _)
    _ = (2 : ℝ) ^ t * Real.exp (-t) := by rw [tsum_mul_left, hhalf.tsum_eq]
    _ ≤ Real.exp (-(3 / 10 * t)) := by
        rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hl2 : Real.log 2 < 7 / 10 := by
          have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
        nlinarith

/-- `e^{−3t/10} ≤ C_e / t^{1/β}`. -/
lemma exp_le_rpow {β : ℝ} (hβ : 0 < β) {t : ℝ} (ht : 0 < t) :
    Real.exp (-(3 / 10 * t)) ≤
      (1 + (⌈1 / β⌉₊).factorial * (10 / 3) ^ ⌈1 / β⌉₊) / t ^ (1 / β) := by
  set m := ⌈1 / β⌉₊ with hm
  have htb : 0 < t ^ (1 / β) := Real.rpow_pos_of_pos ht _
  rw [le_div_iff₀ htb]
  have he1 : Real.exp (-(3 / 10 * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hepos := Real.exp_pos (-(3 / 10 * t))
  have hB : 0 ≤ (m.factorial : ℝ) * (10 / 3) ^ m := by positivity
  rcases le_or_gt t 1 with ht1 | ht1
  · have : t ^ (1 / β) ≤ 1 := Real.rpow_le_one ht.le ht1 (by positivity)
    nlinarith
  · have hpow : t ^ (1 / β) ≤ t ^ m := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le ht1.le (Nat.le_ceil _)
    have hexp := Real.pow_div_factorial_le_exp (3 / 10 * t) (by positivity) m
    have hmf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    rw [div_le_iff₀ hmf, mul_pow] at hexp
    have h1 : t ^ m * Real.exp (-(3 / 10 * t)) ≤ m.factorial * (10 / 3) ^ m := by
      have e1 : Real.exp (3 / 10 * t) * Real.exp (-(3 / 10 * t)) = 1 := by
        rw [← Real.exp_add]; simp
      have e2 : (3 / 10 : ℝ) ^ m * (10 / 3) ^ m = 1 := by rw [← mul_pow]; norm_num
      have h3 : (3 / 10 : ℝ) ^ m * t ^ m * Real.exp (-(3 / 10 * t)) ≤ m.factorial :=
        by nlinarith
      calc t ^ m * Real.exp (-(3 / 10 * t)) = ((3 / 10 : ℝ) ^ m * t ^ m *
            Real.exp (-(3 / 10 * t))) * (10 / 3) ^ m := by
            rw [show ((3 / 10 : ℝ) ^ m * t ^ m * Real.exp (-(3 / 10 * t))) * (10 / 3) ^ m =
              t ^ m * Real.exp (-(3 / 10 * t)) * ((3 / 10 : ℝ) ^ m * (10 / 3) ^ m) by ring, e2]
            ring
        _ ≤ m.factorial * (10 / 3) ^ m := mul_le_mul_of_nonneg_right h3 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hpow hepos.le]

end H2

end Coulhon
end

section
/-!
# H2: Faber–Krahn gives on-diagonal heat-kernel decay (Coulhon II.1 / Grigor'yan 1.1)

Continuous time (`cont_bound`): Nash (`H2FK`) for the lazy chain `W = (I + P)/2` gives
`W^{2n}(x, x) ≤ (βn/(2K))^{−1/β}` (`H2Lazy`); `p(t) = ∑ₖ poi(2t, k) Wᵏ` with `Wᵏ(x, x)` decreasing and
the Poisson lower tail (`H2Heat`) give `p(t, x, x) ≤ C_d t^{−1/β}`.

Discrete time: the even moments `aⱼ = P^{2j}(x, x) = ‖Pʲ δₓ‖²` are decreasing and log-convex
(Cauchy–Schwarz), so `aₙ rʲ ≤ aⱼ rⁿ` with `r = aₙ/a_{n−1}`, and
`p(2n, x, x) ≥ ∑ⱼ poi(2n, 2j) aⱼ ≥ aₙ r^{−n} e^{−2n} cosh(2n√r) ≥ aₙ/2` (QUOTES §H2.4: no laziness).
-/


open DurrettProbability MarkovChain MarkovHK

namespace Coulhon

namespace H2

variable {X : Type*} [DecidableEq X]

/-- The constant of the continuous-time bound. -/
noncomputable def Cd (c β : ℝ) : ℝ :=
  max (4 ^ (1 / β)) ((β * (1 / (2 * (2 * 4 ^ β / c))) / 4) ^ (-1 / β) +
    (1 + (⌈1 / β⌉₊).factorial * (10 / 3) ^ ⌈1 / β⌉₊))

lemma one_le_Cd {c β : ℝ} (hβ : 0 < β) : 1 ≤ Cd c β :=
  le_trans (Real.one_le_rpow (by norm_num) (by positivity)) (le_max_left _ _)

/-- The on-diagonal continuous-time bound. -/
lemma cont_bound {P : X → X → ℝ} (hP : IsTransition P) (hPs : IsSymmetric P) {c β : ℝ}
    (hc : 0 < c) (hβ : 0 < β)
    (hΛ : ∀ v : ℝ, 1 ≤ v → c * v ^ (-β) ≤ isoperimetricProfile P (fun _ => 1) v)
    (x : X) {t : ℝ} (ht : 0 < t) : heatKernel P t x x ≤ Cd c β / t ^ (1 / β) := by
  have htb : 0 < t ^ (1 / β) := Real.rpow_pos_of_pos ht _
  have hW := isTransition_lazy hP
  have hWS := isSub_of_isTransition hW
  set K := 2 * 4 ^ β / c with hK
  have hK0 : 0 < K := by positivity
  set a := 1 / (2 * K) with ha
  have ha0 : 0 < a := by positivity
  set u : ℕ → ℝ := fun n => stepProb (lazy P) (2 * n) x x with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => stepProb_nonneg hWS _ x x
  have hstep : ∀ n, a * u n ^ (1 + β) ≤ u n - u (n + 1) := by
    intro n
    have h := lazy_nash_step hP hPs hβ (nash_fin hP hPs hc hβ hΛ) hK0.le x n
    simp only [hu]
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, ha]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  rcases lt_or_ge t 4 with ht4 | ht4
  · -- small times
    have h1 := heat_le_one hP ht.le x x
    have h2 : t ^ (1 / β) ≤ 4 ^ (1 / β) := Real.rpow_le_rpow ht.le ht4.le (by positivity)
    rw [le_div_iff₀ htb]
    calc heatKernel P t x x * t ^ (1 / β) ≤ 1 * 4 ^ (1 / β) :=
          mul_le_mul h1 h2 htb.le zero_le_one
      _ ≤ Cd c β := by rw [one_mul]; exact le_max_left _ _
  · -- large times
    set n₀ := ⌊t / 2⌋₊ with hn₀
    have hn₀t : (2 * n₀ : ℝ) ≤ t := by
      have := Nat.floor_le (by positivity : (0 : ℝ) ≤ t / 2); rw [← hn₀] at this; linarith
    have hn₀4 : t / 4 ≤ (n₀ : ℝ) := by
      have := Nat.lt_floor_add_one (t / 2); rw [← hn₀] at this; linarith
    have hn₀1 : 1 ≤ n₀ := by
      have : (1 : ℝ) ≤ n₀ := by linarith
      exact_mod_cast this
    have hdec := ode_decay ha0 hβ hu0 hstep n₀ hn₀1
    have hpt : ∀ k : ℕ, stepProb (lazy P) k x x ≤ (if (k : ℝ) < t then 1 else 0) + u n₀ := by
      intro k
      split_ifs with hk
      · linarith [stepProb_le_one hWS k x x, hu0 n₀]
      · have hk' : 2 * n₀ ≤ k := by
          have : (2 * n₀ : ℝ) ≤ k := hn₀t.trans (not_lt.mp hk)
          exact_mod_cast this
        rw [zero_add]; exact lazy_antitone' hP hPs x hk'
    have h2t : (0 : ℝ) ≤ 2 * t := by linarith
    have hsum1 : Summable (fun k : ℕ => poi (2 * t) k * (if (k : ℝ) < t then 1 else 0)) :=
      Summable.of_nonneg_of_le (fun k => mul_nonneg (poi_nonneg h2t k) (by split_ifs <;> norm_num))
        (fun k => by
          have := mul_le_mul_of_nonneg_left (show (if (k : ℝ) < t then (1 : ℝ) else 0) ≤ 1 by
            split_ifs <;> norm_num) (poi_nonneg h2t k)
          simpa using this) (summable_poi (2 * t))
    have hle1 : heatKernel P t x x ≤ Real.exp (-(3 / 10 * t)) + u n₀ := by
      rw [heat_eq_lazy hP ht.le]
      calc ∑' k, poi (2 * t) k * stepProb (lazy P) k x x
          ≤ ∑' k, (poi (2 * t) k * (if (k : ℝ) < t then 1 else 0) + poi (2 * t) k * u n₀) := by
            refine Summable.tsum_le_tsum (fun k => ?_) (summable_heat hWS h2t x x)
              (hsum1.add ((summable_poi _).mul_right _))
            rw [← mul_add]; exact mul_le_mul_of_nonneg_left (hpt k) (poi_nonneg h2t k)
        _ = ∑' k, poi (2 * t) k * (if (k : ℝ) < t then 1 else 0) + u n₀ := by
            rw [hsum1.tsum_add ((summable_poi _).mul_right _), tsum_mul_right, tsum_poi, one_mul]
        _ ≤ Real.exp (-(3 / 10 * t)) + u n₀ := by linarith [poisson_tail ht.le]
    have hu_le : u n₀ ≤ (β * a / 4) ^ (-1 / β) / t ^ (1 / β) := by
      have hpos : 0 < β * a * t / 4 := by positivity
      have h1 : (β * a * n₀) ^ (-1 / β) ≤ (β * a * t / 4) ^ (-1 / β) :=
        Real.rpow_le_rpow_of_nonpos hpos (by nlinarith [mul_pos hβ ha0])
          (by rw [neg_div]; have h' : 0 < 1 / β := (by positivity); linarith)
      have h2 : (β * a * t / 4) ^ (-1 / β) = (β * a / 4) ^ (-1 / β) / t ^ (1 / β) := by
        rw [show β * a * t / 4 = (β * a / 4) * t by ring, Real.mul_rpow (by positivity) ht.le,
          neg_div, Real.rpow_neg ht.le]; ring
      linarith
    have he := exp_le_rpow hβ ht
    calc heatKernel P t x x ≤ Real.exp (-(3 / 10 * t)) + u n₀ := hle1
      _ ≤ (1 + (⌈1 / β⌉₊).factorial * (10 / 3) ^ ⌈1 / β⌉₊) / t ^ (1 / β) +
            (β * a / 4) ^ (-1 / β) / t ^ (1 / β) := add_le_add he hu_le
      _ = ((β * a / 4) ^ (-1 / β) + (1 + (⌈1 / β⌉₊).factorial * (10 / 3) ^ ⌈1 / β⌉₊)) /
            t ^ (1 / β) := by ring
      _ ≤ Cd c β / t ^ (1 / β) := by
          apply div_le_div_of_nonneg_right _ htb.le
          rw [Cd, ha, hK]; exact le_max_right _ _

/-- Cauchy–Schwarz for series. -/
lemma sq_tsum_mul_le {u v : X → ℝ} (hu : Summable (fun z => u z ^ 2))
    (hv : Summable (fun z => v z ^ 2)) (huv : Summable (fun z => u z * v z)) :
    (∑' z, u z * v z) ^ 2 ≤ (∑' z, u z ^ 2) * ∑' z, v z ^ 2 := by
  set A := ∑' z, u z ^ 2
  set B := ∑' z, u z * v z
  set C := ∑' z, v z ^ 2
  have hq : ∀ l : ℝ, 0 ≤ A - 2 * l * B + l ^ 2 * C := by
    intro l
    have e : ∀ z, (u z - l * v z) ^ 2 = u z ^ 2 - 2 * l * (u z * v z) + l ^ 2 * v z ^ 2 :=
      fun z => by ring
    have hs := (hu.sub (huv.mul_left (2 * l))).add (hv.mul_left (l ^ 2))
    have h0 : 0 ≤ ∑' z, (u z - l * v z) ^ 2 := tsum_nonneg fun z => sq_nonneg _
    simp only [e] at h0
    rwa [(hu.sub (huv.mul_left (2 * l))).tsum_add (hv.mul_left (l ^ 2)),
      hu.tsum_sub (huv.mul_left (2 * l)), tsum_mul_left, tsum_mul_left] at h0
  have hC0 : 0 ≤ C := tsum_nonneg fun z => sq_nonneg _
  rcases hC0.lt_or_eq with hCpos | hCz
  · have := hq (B / C)
    have e : A - 2 * (B / C) * B + (B / C) ^ 2 * C = A - B ^ 2 / C := by field_simp; ring
    rw [e] at this
    rw [sub_nonneg, div_le_iff₀ hCpos] at this
    linarith
  · -- `C = 0`: then `B = 0`
    rw [← hCz, mul_zero]
    by_contra hcon
    push_neg at hcon
    have hB : B ≠ 0 := by intro h; rw [h] at hcon; simp at hcon
    have h1 := hq ((A + 1) / B)
    rw [← hCz] at h1
    have e : A - 2 * ((A + 1) / B) * B + ((A + 1) / B) ^ 2 * 0 = A - 2 * (A + 1) := by
      field_simp; ring
    rw [e] at h1
    have hA0 : 0 ≤ A := tsum_nonneg fun z => sq_nonneg _
    linarith

/-- `P^{2n}(x, x) ≤ 2 p(2n, x, x)`, with no laziness. -/
lemma even_le_two_heat {P : X → X → ℝ} (hP : IsTransition P) (hPs : IsSymmetric P) (x : X)
    (n : ℕ) (hn : 1 ≤ n) : stepProb P (2 * n) x x ≤ 2 * heatKernel P (2 * n) x x := by
  have hPS := isSub_of_isTransition hP
  set a : ℕ → ℝ := fun j => stepProb P (2 * j) x x with ha
  set g : ℕ → X → ℝ := fun j => gv P {x} (dl x) j with hg
  have ha_gram : ∀ i j, stepProb P (i + j) x x = ∑' z, g i z * g j z := by
    intro i j; rw [← mom_dl, mom_add hP hPs]
  have ha_sq : ∀ j, a j = ∑' z, g j z ^ 2 := by
    intro j; simp only [ha]; rw [two_mul, ha_gram]; exact tsum_congr fun z => by ring
  have hg2 : ∀ j, Summable (fun z => g j z ^ 2) := fun j => summable_gv_sq hP hPs {x} (dl x) j
  have hgg : ∀ i j, Summable (fun z => g i z * g j z) := fun i j =>
    summable_gv_mul hP hPs {x} (dl x) i j
  have ha0 : ∀ j, 0 ≤ a j := fun j => stepProb_nonneg hPS _ x x
  -- decreasing
  have hdec : ∀ j, a (j + 1) ≤ a j := by
    intro j
    obtain ⟨_, _, hle⟩ := contraction hP hPs (h := g j) (hg2 j)
    have e : ∀ z, ∑' w, P z w * g j w = g (j + 1) z := fun z => by
      simp only [hg]; rw [gv_succ hP hPs]
    simp only [e] at hle
    rw [ha_sq, ha_sq]; exact hle
  -- log-convex
  have hlc : ∀ j, a (j + 1) ^ 2 ≤ a j * a (j + 2) := by
    intro j
    have h := sq_tsum_mul_le (hg2 j) (hg2 (j + 2)) (hgg j (j + 2))
    rw [← ha_gram, ← ha_sq, ← ha_sq] at h
    rwa [show j + (j + 2) = 2 * (j + 1) by ring] at h
  rcases (ha0 n).lt_or_eq with hpos | hz
  swap
  · have : stepProb P (2 * n) x x = 0 := hz.symm
    rw [this]
    have := heat_nonneg hP (by positivity : (0 : ℝ) ≤ 2 * n) x x
    linarith
  have hanti : Antitone a := antitone_nat_of_succ_le hdec
  -- positivity of all `aⱼ`
  have hapos : ∀ j, 0 < a j := by
    have hfwd : ∀ k, 0 < a (n + k) := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        rcases k with _ | _ | k
        · simpa using hpos
        · by_contra hc
          have hz1 : a (n + 1) = 0 := le_antisymm (not_lt.mp hc) (ha0 _)
          have := hlc (n - 1)
          have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
          rw [hn1, show n - 1 + 2 = n + 1 by omega, hz1, mul_zero] at this
          nlinarith
        · by_contra hc
          have hz1 : a (n + (k + 2)) = 0 := le_antisymm (not_lt.mp hc) (ha0 _)
          have := hlc (n + k)
          rw [show n + k + 2 = n + (k + 2) by ring, hz1, mul_zero,
            show n + k + 1 = n + (k + 1) by ring] at this
          have := ih (k + 1) (by omega)
          nlinarith
    intro j
    rcases le_total j n with hj | hj
    · exact lt_of_lt_of_le hpos (hanti hj)
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj; exact hfwd k
  -- the ratio `r = aₙ / a_{n−1}`
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set r := a (m + 1) / a m with hr
  have hr0 : 0 < r := div_pos (hapos _) (hapos _)
  have hr1 : r ≤ 1 := by rw [div_le_one (hapos m)]; exact hdec m
  have hrm : r * a m = a (m + 1) := by rw [hr, div_mul_cancel₀ _ (hapos m).ne']
  -- ratios increase
  have hup : ∀ k, r * a (m + k) ≤ a (m + k + 1) := by
    intro k
    induction k with
    | zero => simp only [add_zero]; rw [hrm]
    | succ k ih =>
      have h := hlc (m + k)
      have hpk := hapos (m + k)
      have hpk1 := hapos (m + k + 1)
      rw [show m + (k + 1) = m + k + 1 by ring]
      rw [show m + k + 2 = m + k + 1 + 1 by ring] at h
      by_contra hc
      push_neg at hc
      nlinarith
  have hdown : ∀ k, k ≤ m → a (m - k + 1) ≤ r * a (m - k) := by
    intro k hk
    induction k with
    | zero => rw [Nat.sub_zero, hrm]
    | succ k ih =>
      have ih' := ih (by omega)
      have h := hlc (m - (k + 1))
      rw [show m - (k + 1) + 2 = m - k + 1 by omega, show m - (k + 1) + 1 = m - k by omega] at h
      have hp1 := hapos (m - (k + 1))
      have hp2 := hapos (m - k)
      rw [show m - (k + 1) + 1 = m - k by omega]
      by_contra hc
      push_neg at hc
      nlinarith
  -- the supporting line `a_{m+1} rʲ ≤ aⱼ r^{m+1}`
  have hhi : ∀ k, r ^ k * a (m + 1) ≤ a (m + 1 + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hup (k + 1)
      rw [show m + (k + 1) = m + 1 + k by ring, show m + 1 + k + 1 = m + 1 + (k + 1) by ring]
        at this
      calc r ^ (k + 1) * a (m + 1) = r * (r ^ k * a (m + 1)) := by ring
        _ ≤ r * a (m + 1 + k) := mul_le_mul_of_nonneg_left ih hr0.le
        _ ≤ a (m + 1 + (k + 1)) := this
  have hlo : ∀ k, k ≤ m + 1 → a (m + 1) ≤ r ^ k * a (m + 1 - k) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have ih' := ih (by omega)
      have hd := hdown k (by omega)
      rw [show m + 1 - k = m - k + 1 by omega] at ih'
      rw [show m + 1 - (k + 1) = m - k by omega]
      calc a (m + 1) ≤ r ^ k * a (m - k + 1) := ih'
        _ ≤ r ^ k * (r * a (m - k)) := mul_le_mul_of_nonneg_left hd (pow_nonneg hr0.le _)
        _ = r ^ (k + 1) * a (m - k) := by ring
  have hsupp : ∀ j, a (m + 1) * r ^ j ≤ a j * r ^ (m + 1) := by
    intro j
    rcases le_total j (m + 1) with hj | hj
    · have h := hlo (m + 1 - j) (by omega)
      rw [show m + 1 - (m + 1 - j) = j by omega] at h
      calc a (m + 1) * r ^ j ≤ r ^ (m + 1 - j) * a j * r ^ j :=
            mul_le_mul_of_nonneg_right h (pow_nonneg hr0.le _)
        _ = a j * (r ^ (m + 1 - j) * r ^ j) := by ring
        _ = a j * r ^ (m + 1) := by rw [← pow_add, Nat.sub_add_cancel hj]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
      calc a (m + 1) * r ^ (m + 1 + k) = r ^ (m + 1) * (r ^ k * a (m + 1)) := by ring
        _ ≤ r ^ (m + 1) * a (m + 1 + k) := mul_le_mul_of_nonneg_left (hhi k) (pow_nonneg hr0.le _)
        _ = a (m + 1 + k) * r ^ (m + 1) := by ring
  -- the heat kernel at time `2n`
  set T : ℝ := 2 * ((m + 1 : ℕ) : ℝ) with hT
  have hT0 : 0 ≤ T := by positivity
  have hinj : Function.Injective (fun j : ℕ => 2 * j) := fun i j h => by simpa using h
  have hheat : heatKernel P T x x = ∑' k, poi T k * stepProb P k x x := by
    rw [heatKernel_eq, uniformize_eq_self hP]
  have hsk := summable_heat hPS hT0 x x
  have heven : ∑' j, poi T (2 * j) * a j ≤ heatKernel P T x x := by
    rw [hheat]
    exact tsum_comp_le_tsum_of_inj hsk (fun k => mul_nonneg (poi_nonneg hT0 k)
      (stepProb_nonneg hPS k x x)) hinj
  have hpe : Summable (fun j => poi T (2 * j)) := (summable_poi T).comp_injective hinj
  -- `∑ⱼ poi(T, 2j) rʲ = e^{−T} cosh(T √r)`
  have hcosh : HasSum (fun j => poi T (2 * j) * r ^ j) (Real.exp (-T) * Real.cosh (T * Real.sqrt r)) := by
    have h := (Real.hasSum_cosh (T * Real.sqrt r)).mul_left (Real.exp (-T))
    refine h.congr_fun fun j => ?_
    have e1 : (T * Real.sqrt r) ^ (2 * j) = T ^ (2 * j) * r ^ j := by
      rw [mul_pow, pow_mul (Real.sqrt r), Real.sq_sqrt hr0.le]
    rw [e1]; unfold poi; ring
  have hfin_sum : a (m + 1) / r ^ (m + 1) * (Real.exp (-T) * Real.cosh (T * Real.sqrt r)) ≤
      heatKernel P T x x := by
    refine le_trans ?_ heven
    rw [← hcosh.tsum_eq, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun j => ?_) (hcosh.summable.mul_left _) ?_
    · have h := hsupp j
      have hrp : 0 < r ^ (m + 1) := pow_pos hr0 _
      have h' : a (m + 1) / r ^ (m + 1) * r ^ j ≤ a j := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hrp]; linarith
      calc a (m + 1) / r ^ (m + 1) * (poi T (2 * j) * r ^ j)
          = poi T (2 * j) * (a (m + 1) / r ^ (m + 1) * r ^ j) := by ring
        _ ≤ poi T (2 * j) * a j := mul_le_mul_of_nonneg_left h' (poi_nonneg hT0 _)
    · exact Summable.of_nonneg_of_le (fun j => mul_nonneg (poi_nonneg hT0 _) (ha0 j)) (fun j => by
        have := mul_le_mul_of_nonneg_left (stepProb_le_one hPS (2 * j) x x) (poi_nonneg hT0 (2 * j))
        simpa using this) hpe
  have hkey : r ^ (m + 1) ≤ 2 * (Real.exp (-T) * Real.cosh (T * Real.sqrt r)) := by
    rw [Real.cosh_eq]
    have hs : Real.sqrt r ≤ Real.exp (Real.sqrt r - 1) := by
      linarith [Real.add_one_le_exp (Real.sqrt r - 1)]
    have hs0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
    have h1 : r ^ (m + 1) = Real.sqrt r ^ (2 * (m + 1)) := by rw [pow_mul, Real.sq_sqrt hr0.le]
    have h2 : Real.sqrt r ^ (2 * (m + 1)) ≤ Real.exp (Real.sqrt r - 1) ^ (2 * (m + 1)) :=
      pow_le_pow_left₀ hs0 hs _
    have h3 : Real.exp (Real.sqrt r - 1) ^ (2 * (m + 1)) =
        Real.exp (-T) * Real.exp (T * Real.sqrt r) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, hT]; congr 1; push_cast; ring
    have h4 : 0 ≤ Real.exp (-T) * Real.exp (-(T * Real.sqrt r)) := by positivity
    nlinarith
  have hrp : 0 < r ^ (m + 1) := pow_pos hr0 _
  have hfin := mul_le_mul_of_nonneg_left hkey (div_nonneg (ha0 (m + 1)) hrp.le)
  rw [div_mul_cancel₀ _ hrp.ne'] at hfin
  show a (m + 1) ≤ 2 * heatKernel P T x x
  linarith

end H2

end Coulhon
end

section
open DurrettProbability MarkovChain MarkovHK
open Coulhon
open H2 in
theorem solution (c β : ℝ) (hc : 0 < c)
    (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type u) [Countable X] [DecidableEq X] (P : X → X → ℝ),
      IsTransition P → IsSymmetric P →
      (∀ v : ℝ, 1 ≤ v → c * v ^ (-β) ≤ isoperimetricProfile P (fun _ => 1) v) →
      (∀ t : ℕ, 1 ≤ t → ∀ x y, stepProb P t x y ≤ C / (t : ℝ) ^ (1 / β)) ∧
        ∀ t : ℝ, 0 < t → ∀ x y, heatKernel P t x y ≤ C / t ^ (1 / β) := by
  have hCd := one_le_Cd (c := c) hβ
  have h32 : 1 ≤ (3 / 2 : ℝ) ^ (1 / β) := Real.one_le_rpow (by norm_num) (by positivity)
  refine ⟨2 * (3 / 2 : ℝ) ^ (1 / β) * Cd c β, by positivity, ?_⟩
  intro X _ _ P hP hPs hΛ
  have hPS := isSub_of_isTransition hP
  have hCle : Cd c β ≤ 2 * (3 / 2 : ℝ) ^ (1 / β) * Cd c β := by nlinarith
  -- continuous time, all `x, y`
  have hcont : ∀ t : ℝ, 0 < t → ∀ x y, heatKernel P t x y ≤ Cd c β / t ^ (1 / β) := by
    intro t ht x y
    have h := heat_le_avg_diag hP hPs ht.le x y
    have hx := cont_bound hP hPs hc hβ hΛ x ht
    have hy := cont_bound hP hPs hc hβ hΛ y ht
    linarith
  refine ⟨fun t ht x y => ?_, fun t ht x y => ?_⟩
  swap
  · have htb : 0 < t ^ (1 / β) := Real.rpow_pos_of_pos ht _
    exact (hcont t ht x y).trans (div_le_div_of_nonneg_right hCle htb.le)
  -- discrete time: the even bound `P^{2n}(z, w) ≤ 2 C_d / (2n)^{1/β}`
  have heven : ∀ n : ℕ, 1 ≤ n → ∀ z w,
      stepProb P (2 * n) z w ≤ 2 * Cd c β / ((2 * n : ℕ) : ℝ) ^ (1 / β) := by
    intro n hn z w
    have hT : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast; linarith
    have hdiag : ∀ v, stepProb P (2 * n) v v ≤ 2 * Cd c β / ((2 * n : ℕ) : ℝ) ^ (1 / β) := by
      intro v
      have h1 := even_le_two_heat hP hPs v n hn
      have h2 := cont_bound hP hPs hc hβ hΛ v hT
      push_cast at h2 ⊢
      rw [mul_div_assoc]
      linarith
    -- `P^{2n}(z, w) ≤ (P^{2n}(z, z) + P^{2n}(w, w))/2`
    have hsg : ∀ a b, stepProb P (2 * n) a b = ∑' v, stepProb P n a v * stepProb P n v b := by
      intro a b; rw [two_mul, stepProb_add hPS]
    have hoff : stepProb P (2 * n) z w ≤
        (stepProb P (2 * n) z z + stepProb P (2 * n) w w) / 2 := by
      rw [hsg, hsg, hsg]
      have e : ∀ a b, (fun v => stepProb P n a v * stepProb P n v b) =
          fun v => stepProb P n a v * stepProb P n b v :=
        fun a b => funext fun v => by rw [stepProb_symm hPS hPs n v b]
      rw [e z w, e z z, e w w]
      exact tsum_mul_le_avg (fun v => stepProb_nonneg hPS n z v) (fun v => stepProb_nonneg hPS n w v)
        (fun v => stepProb_le_one hPS n z v) (fun v => stepProb_le_one hPS n w v)
        ((isSub_stepProb hPS n).2.1 z) ((isSub_stepProb hPS n).2.1 w)
    linarith [hdiag z, hdiag w]
  have htb : 0 < (t : ℝ) ^ (1 / β) := Real.rpow_pos_of_pos (by exact_mod_cast ht) _
  rcases Nat.even_or_odd t with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · -- `t = 2n`
    have hn : 1 ≤ n := by omega
    have h := heven n hn x y
    rw [show n + n = 2 * n by ring] at htb ⊢
    refine h.trans (div_le_div_of_nonneg_right ?_ htb.le)
    nlinarith
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- `t = 1`
      simp only [mul_zero, zero_add, Nat.cast_one, Real.one_rpow, div_one]
      rw [stepProb_one]
      have h1 := hPS.le_one x y
      have : (1 : ℝ) ≤ 2 * (3 / 2 : ℝ) ^ (1 / β) * Cd c β := by nlinarith
      linarith
    · -- `t = 2n + 1`
      have hM := heven n hn
      set M := 2 * Cd c β / ((2 * n : ℕ) : ℝ) ^ (1 / β) with hMdef
      have hodd : stepProb P (2 * n + 1) x y ≤ M := by
        rw [stepProb_succ]
        calc ∑' z, P x z * stepProb P (2 * n) z y ≤ ∑' z, P x z * M :=
              Summable.tsum_le_tsum (fun z => mul_le_mul_of_nonneg_left (hM z y) (hP.1 x z))
                (Summable.of_nonneg_of_le (fun z => mul_nonneg (hP.1 x z)
                  (stepProb_nonneg hPS _ z y)) (fun z => by
                    have := mul_le_mul_of_nonneg_left (stepProb_le_one hPS (2 * n) z y) (hP.1 x z)
                    simpa using this) (hP.2.1 x)) ((hP.2.1 x).mul_right M)
          _ = M := by rw [tsum_mul_right, hP.2.2 x, one_mul]
      refine hodd.trans ?_
      -- `(2n+1)^{1/β} ≤ (3/2)^{1/β} (2n)^{1/β}`
      have h2n : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        push_cast; linarith
      have hle : ((2 * n + 1 : ℕ) : ℝ) ≤ 3 / 2 * ((2 * n : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        push_cast; linarith
      have hp : ((2 * n + 1 : ℕ) : ℝ) ^ (1 / β) ≤ (3 / 2 : ℝ) ^ (1 / β) * ((2 * n : ℕ) : ℝ) ^ (1 / β) := by
        rw [← Real.mul_rpow (by norm_num) h2n.le]
        exact Real.rpow_le_rpow (by positivity) hle (by positivity)
      have h2nb : 0 < ((2 * n : ℕ) : ℝ) ^ (1 / β) := Real.rpow_pos_of_pos h2n _
      rw [hMdef, div_le_div_iff₀ h2nb htb]
      have hCd0 : 0 ≤ Cd c β := by linarith
      calc 2 * Cd c β * ((2 * n + 1 : ℕ) : ℝ) ^ (1 / β)
          ≤ 2 * Cd c β * ((3 / 2 : ℝ) ^ (1 / β) * ((2 * n : ℕ) : ℝ) ^ (1 / β)) :=
            mul_le_mul_of_nonneg_left hp (by positivity)
        _ = 2 * (3 / 2 : ℝ) ^ (1 / β) * Cd c β * ((2 * n : ℕ) : ℝ) ^ (1 / β) := by ring
end
