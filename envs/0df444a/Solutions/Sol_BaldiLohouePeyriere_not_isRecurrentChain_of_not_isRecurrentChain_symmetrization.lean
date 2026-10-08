-- Prove2me | solution 1 for BaldiLohouePeyriere.not_isRecurrentChain_of_not_isRecurrentChain_symmetrization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T13:46:57.600278+00:00
-- url     : https://prove2.me/submissions/4506b4ac-17c5-4a46-9b2c-00a42bebaef2

import Mathlib
import Definitions.Def_IntervalExchange

section

/-!
# Baldi–Lohoué–Peyrière (JMMS Lemma 5.5): transience passes from the symmetrization

For a probability `μ` on `G` acting on `X`, let `P = walkKernel μ` and
`Q = walkKernel ((μ + μ̌)/2) = (P + Pᵀ)/2`. Counting measure is invariant for `P` (the action is
by bijections), so `P` is doubly stochastic and `Q` is a symmetric stochastic kernel.

Route (Green functions, no path space):
* **Renewal** (for any stochastic kernel): transience at `o` gives bounded truncated Green
  functions `green K o N = ∑_{n<N} K^n(o,o)`; recurrence makes them unbounded.
* **Hardy inequality for `Q`** (transience of `Q` at `o`): for bounded summable `f`,
  `f(o) ≤ (2 t G_Q + E_Q(f)/t)/4`, where `E_Q(f) = ∑_{x,y} Q(x,y)(f x - f y)²`.
* **Energy of the `P`-Green function.** For `U = ∑_{n<N} p_n` (`p_n` the `P`-law at time `n`),
  `U - U P = δ_o - p_N`, and since `Q = (P + Pᵀ)/2` with `P` doubly stochastic,
  `E_Q(U) = 2 ⟨U, U - U P⟩ = 2 (U(o) - ⟨U, p_N⟩) ≤ 2 U(o)`.
* With `t = 1`: `U(o) ≤ G_Q/2 + U(o)/2`, so `green P o N = U(o) ≤ G_Q`, and `P` is transient.
-/

open IntervalExchange

set_option linter.unusedSectionVars false

namespace BaldiLohouePeyriere.IETB

open Classical

/-! ## Summation helpers -/

section Sums

variable {V W : Type*}

lemma prod_summable {F : V → W → ℝ} (h0 : ∀ x y, 0 ≤ F x y) (h1 : ∀ x, Summable (F x))
    (h2 : Summable fun x => ∑' y, F x y) : Summable (fun q : V × W => F q.1 q.2) :=
  (summable_prod_of_nonneg (f := fun q : V × W => F q.1 q.2) (fun q => h0 q.1 q.2)).2 ⟨h1, h2⟩

lemma dom_summable {ι : Type*} {F G : ι → ℝ} (hF : Summable F) (h : ∀ q, |G q| ≤ F q) :
    Summable G :=
  Summable.of_norm_bounded hF (fun q => by rw [Real.norm_eq_abs]; exact h q)

lemma swap_summable {G : V × W → ℝ} (h : Summable G) : Summable (fun q : W × V => G q.swap) :=
  (Equiv.prodComm W V).summable_iff.2 h

lemma tsum_swap_eq (G : V × W → ℝ) : ∑' q : W × V, G q.swap = ∑' q, G q :=
  (Equiv.prodComm W V).tsum_eq G

lemma col_summable {G : V → W → ℝ} (h : Summable (fun q : V × W => G q.1 q.2)) :
    Summable fun y => ∑' x, G x y :=
  (swap_summable h).prod

lemma tsum_comm_of {G : V → W → ℝ} (h : Summable (fun q : V × W => G q.1 q.2)) :
    ∑' x, ∑' y, G x y = ∑' y, ∑' x, G x y :=
  (Summable.tsum_comm (f := G) h).symm

end Sums

/-! ## Stochastic kernels: renewal and Green functions -/

section Stoch

variable {V : Type*} {K : V → V → ℝ}

/-- `K` is a stochastic kernel. -/
def IsStoch (K : V → V → ℝ) : Prop := (∀ x y, 0 ≤ K x y) ∧ ∀ x, HasSum (K x) 1

lemma K_nn (hc : IsStoch K) (x y : V) : 0 ≤ K x y := hc.1 x y

lemma K_sum (hc : IsStoch K) (x : V) : Summable (K x) := (hc.2 x).summable

lemma K_tsum (hc : IsStoch K) (x : V) : ∑' y, K x y = 1 := (hc.2 x).tsum_eq

lemma K_le (hc : IsStoch K) (x y : V) : K x y ≤ 1 := by
  rw [← K_tsum hc x]; exact (K_sum hc x).le_tsum y (fun z _ => K_nn hc x z)

/-- The transition operator acting on measures. -/
noncomputable def T (K : V → V → ℝ) (f : V → ℝ) (y : V) : ℝ := ∑' x, f x * K x y

lemma T_row (hc : IsStoch K) {f : V → ℝ} (hf : Summable f) (y : V) :
    Summable fun x => f x * K x y :=
  dom_summable hf.abs fun x => by
    rw [abs_mul, abs_of_nonneg (K_nn hc x y)]
    exact mul_le_of_le_one_right (abs_nonneg _) (K_le hc x y)

lemma T_prod (hc : IsStoch K) {f : V → ℝ} (hf : Summable f) :
    Summable (fun q : V × V => f q.1 * K q.1 q.2) := by
  have hF := prod_summable (F := fun x y => |f x| * K x y)
    (fun x y => mul_nonneg (abs_nonneg _) (K_nn hc x y)) (fun x => (K_sum hc x).mul_left _)
    (by simp_rw [tsum_mul_left, K_tsum hc, mul_one]; exact hf.abs)
  exact dom_summable hF fun q => by rw [abs_mul, abs_of_nonneg (K_nn hc _ _)]

lemma T_summable (hc : IsStoch K) {f : V → ℝ} (hf : Summable f) : Summable (T K f) :=
  col_summable (G := fun x y => f x * K x y) (T_prod hc hf)

lemma T_tsum (hc : IsStoch K) {f : V → ℝ} (hf : Summable f) : ∑' y, T K f y = ∑' x, f x := by
  unfold T
  rw [← tsum_comm_of (G := fun x y => f x * K x y) (T_prod hc hf)]
  simp_rw [tsum_mul_left, K_tsum hc, mul_one]

lemma T_add (hc : IsStoch K) {f g : V → ℝ} (hf : Summable f) (hg : Summable g) (y : V) :
    T K (fun x => f x + g x) y = T K f y + T K g y := by
  unfold T; simp_rw [add_mul]; exact (T_row hc hf y).tsum_add (T_row hc hg y)

lemma T_smul (r : ℝ) (f : V → ℝ) (y : V) : T K (fun x => r * f x) y = r * T K f y := by
  unfold T; simp_rw [mul_assoc]; exact tsum_mul_left

lemma T_sum (hc : IsStoch K) {ι : Type*} (s : Finset ι) (F : ι → V → ℝ)
    (hF : ∀ i, Summable (F i)) (y : V) :
    T K (fun x => ∑ i ∈ s, F i x) y = ∑ i ∈ s, T K (F i) y := by
  unfold T; simp_rw [Finset.sum_mul]; exact Summable.tsum_finsetSum fun i _ => T_row hc (hF i) y

lemma T_nn (hc : IsStoch K) {f : V → ℝ} (hf : ∀ x, 0 ≤ f x) (y : V) : 0 ≤ T K f y :=
  tsum_nonneg fun x => mul_nonneg (hf x) (K_nn hc x y)

lemma T_delta (o y : V) : T K (fun z => if z = o then 1 else 0) y = K o y := by
  unfold T; simp only [ite_mul, one_mul, zero_mul]; exact tsum_ite_eq o _

/-- The law of the chain at time `n`, started at `o`. -/
noncomputable def p (K : V → V → ℝ) (o : V) : ℕ → V → ℝ
  | 0 => fun z => if z = o then 1 else 0
  | n + 1 => T K (p K o n)

/-- The law at time `n` of the chain killed at its first return to `o`. -/
noncomputable def ak (K : V → V → ℝ) (o : V) : ℕ → V → ℝ
  | 0 => fun z => if z = o then 1 else 0
  | n + 1 => fun z => if z = o then 0 else T K (ak K o n) z

noncomputable def fr (K : V → V → ℝ) (o : V) (n : ℕ) : ℝ := T K (ak K o n) o

noncomputable def green (K : V → V → ℝ) (o : V) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, p K o n o

lemma p_summable (hc : IsStoch K) (o : V) : ∀ n, Summable (p K o n)
  | 0 => (hasSum_ite_eq o (1 : ℝ)).summable
  | n + 1 => T_summable hc (p_summable hc o n)

lemma p_nn (hc : IsStoch K) (o : V) : ∀ n z, 0 ≤ p K o n z
  | 0, z => by simp only [p]; split_ifs <;> norm_num
  | n + 1, z => T_nn hc (p_nn hc o n) z

lemma p_tsum (hc : IsStoch K) (o : V) : ∀ n, ∑' z, p K o n z = 1
  | 0 => by simp only [p]; exact tsum_ite_eq o (fun _ => (1 : ℝ))
  | n + 1 => by
    show ∑' z, T K (p K o n) z = 1
    rw [T_tsum hc (p_summable hc o n), p_tsum hc o n]

lemma p_le (hc : IsStoch K) (o : V) (n : ℕ) (z : V) : p K o n z ≤ 1 := by
  rw [← p_tsum hc o n]
  exact (p_summable hc o n).le_tsum z (fun w _ => p_nn hc o n w)

lemma ak_nn (hc : IsStoch K) (o : V) : ∀ n z, 0 ≤ ak K o n z
  | 0, z => by simp only [ak]; split_ifs <;> norm_num
  | n + 1, z => by
    simp only [ak]; split_ifs
    · exact le_rfl
    · exact T_nn hc (ak_nn hc o n) z

lemma ak_summable (hc : IsStoch K) (o : V) : ∀ n, Summable (ak K o n)
  | 0 => (hasSum_ite_eq o (1 : ℝ)).summable
  | n + 1 => Summable.of_nonneg_of_le (ak_nn hc o (n + 1)) (fun z => by
      simp only [ak]; split_ifs
      · exact T_nn hc (ak_nn hc o n) z
      · exact le_rfl) (T_summable hc (ak_summable hc o n))

lemma fr_nn (hc : IsStoch K) (o : V) (n : ℕ) : 0 ≤ fr K o n := T_nn hc (ak_nn hc o n) o

lemma avoidProb_eq (o : V) (n : ℕ) :
    avoidProb K o (n + 1) = ak K o (n + 1) := by
  induction n with
  | zero =>
    funext y
    simp only [avoidProb, ak]
    rw [T_delta]
  | succ n ih =>
    funext y
    simp only [avoidProb]
    rw [ih]
    rfl

lemma firstReturnProb_eq (o : V) (n : ℕ) :
    firstReturnProb K o n = fr K o n := by
  cases n with
  | zero =>
    simp only [firstReturnProb, fr, ak]
    rw [T_delta]
  | succ n =>
    simp only [firstReturnProb, fr]
    rw [avoidProb_eq]
    rfl

lemma fr_partial (hc : IsStoch K) (o : V) (n : ℕ) :
    ∑ k ∈ Finset.range n, fr K o k + ∑' z, ak K o n z = 1 := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, ak]
    exact tsum_ite_eq o (fun _ => (1 : ℝ))
  | succ n ih =>
    have hs := T_summable hc (ak_summable hc o n)
    have e : ∑' z, ak K o (n + 1) z = ∑' z, ak K o n z - fr K o n := by
      rw [← T_tsum hc (ak_summable hc o n), hs.tsum_eq_add_tsum_ite o]
      simp only [ak, fr]
      ring
    rw [Finset.sum_range_succ, e]
    linarith

lemma fr_sum_le (hc : IsStoch K) (o : V) (n : ℕ) : ∑ k ∈ Finset.range n, fr K o k ≤ 1 := by
  have := fr_partial hc o n
  have : 0 ≤ ∑' z, ak K o n z := tsum_nonneg (ak_nn hc o n)
  linarith

lemma fr_summable (hc : IsStoch K) (o : V) : Summable (fr K o) :=
  summable_of_sum_range_le (fr_nn hc o) (fr_sum_le hc o)

lemma renewal (hc : IsStoch K) (o : V) (n : ℕ) (z : V) :
    p K o (n + 1) z = ak K o (n + 1) z +
      ∑ k ∈ Finset.range (n + 1), fr K o k * p K o (n - k) z := by
  induction n generalizing z with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero]
    show T K (p K o 0) z = (if z = o then 0 else T K (ak K o 0) z) + T K (ak K o 0) o * p K o 0 z
    have h0 : ak K o 0 = p K o 0 := rfl
    rw [h0]
    by_cases hz : z = o
    · subst hz; simp [p]
    · simp [p, hz]
  | succ n ih =>
    have hfun : p K o (n + 1) = fun w => ak K o (n + 1) w +
        ∑ k ∈ Finset.range (n + 1), fr K o k * p K o (n - k) w := funext ih
    have step : p K o (n + 2) z = T K (ak K o (n + 1)) z +
        ∑ k ∈ Finset.range (n + 1), fr K o k * p K o (n + 1 - k) z := by
      show T K (p K o (n + 1)) z = _
      rw [hfun, T_add hc (ak_summable hc o (n + 1))
        (summable_sum fun k _ => (p_summable hc o (n - k)).mul_left _),
        T_sum hc _ _ (fun k => (p_summable hc o (n - k)).mul_left _)]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < n + 1 := Finset.mem_range.1 hk
      rw [T_smul, show n + 1 - k = (n - k) + 1 by omega]
      rfl
    rw [step, Finset.sum_range_succ _ (n + 1), Nat.sub_self]
    by_cases hz : z = o
    · subst hz
      simp only [ak, p, fr, if_true]
      ring
    · simp only [ak, p, hz, if_false]
      ring

lemma green_succ (hc : IsStoch K) (o : V) (N : ℕ) :
    green K o (N + 1) = 1 + ∑ k ∈ Finset.range N, fr K o k * green K o (N - k) := by
  unfold green
  rw [Finset.sum_range_succ']
  have h0 : p K o 0 o = 1 := by simp [p]
  rw [h0, add_comm]
  congr 1
  have : ∀ n, p K o (n + 1) o = ∑ k ∈ Finset.range (n + 1), fr K o k * p K o (n - k) o := by
    intro n
    rw [renewal hc]
    simp [ak]
  simp_rw [this]
  rw [Finset.sum_range_diag_flip N (fun k m => fr K o k * p K o m o)]
  simp_rw [Finset.mul_sum]

lemma green_nn (hc : IsStoch K) (o : V) (N : ℕ) : 0 ≤ green K o N :=
  Finset.sum_nonneg fun n _ => p_nn hc o n o

lemma green_mono (hc : IsStoch K) (o : V) : Monotone (green K o) := by
  refine monotone_nat_of_le_succ fun N => ?_
  unfold green
  rw [Finset.sum_range_succ]
  linarith [p_nn hc o N o]

lemma green_bdd (hc : IsStoch K) (o : V) (hF : ∑' k, fr K o k < 1) (N : ℕ) :
    green K o N ≤ 1 / (1 - ∑' k, fr K o k) := by
  set F := ∑' k, fr K o k
  set M := 1 / (1 - F)
  have hne : 1 - F ≠ 0 := by linarith
  have hM : 1 + F * M = M := by
    simp only [M]; field_simp; ring
  have hM0 : 0 ≤ M := by simp only [M]; exact div_nonneg zero_le_one (by linarith)
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    cases N with
    | zero => simp [green, hM0]
    | succ N =>
      rw [green_succ hc]
      have h1 : ∑ k ∈ Finset.range N, fr K o k * green K o (N - k) ≤
          ∑ k ∈ Finset.range N, fr K o k * M :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (ih _ (by omega)) (fr_nn hc o k)
      have h2 : ∑ k ∈ Finset.range N, fr K o k ≤ F :=
        (fr_summable hc o).sum_le_tsum _ (fun k _ => fr_nn hc o k)
      rw [← Finset.sum_mul] at h1
      nlinarith

lemma not_bdd (hc : IsStoch K) (o : V) (hrec : HasSum (fr K o) 1) (M : ℝ)
    (hM : ∀ N, green K o N ≤ M) : False := by
  have hbdd : BddAbove (Set.range fun N => green K o N) := ⟨M, by rintro _ ⟨N, rfl⟩; exact hM N⟩
  set S := ⨆ N, green K o N
  have hle : ∀ N, green K o N ≤ S := fun N => le_ciSup hbdd N
  have hS1 : 1 ≤ S := by
    have := hle 1
    simp [green, p] at this
    exact this
  have hK : ∀ k, 1 + (∑ j ∈ Finset.range k, fr K o j) * S ≤ S := by
    intro k
    set FK := ∑ j ∈ Finset.range k, fr K o j
    have hFK : 0 ≤ FK := Finset.sum_nonneg fun j _ => fr_nn hc o j
    have hJ : ∀ J, FK * green K o J ≤ S - 1 := by
      intro J
      have e := green_succ hc o (J + k)
      have h1 : FK * green K o J ≤ ∑ j ∈ Finset.range k, fr K o j * green K o (J + k - j) := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
          (green_mono hc o (by have := Finset.mem_range.1 hj; omega)) (fr_nn hc o j)
      have h2 : ∑ j ∈ Finset.range k, fr K o j * green K o (J + k - j) ≤
          ∑ j ∈ Finset.range (J + k), fr K o j * green K o (J + k - j) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun j _ _ => mul_nonneg (fr_nn hc o j) (green_nn hc o _))
      have h3 := hle (J + k + 1)
      linarith
    have : FK * S ≤ S - 1 := by
      rw [Real.mul_iSup_of_nonneg hFK]
      exact ciSup_le hJ
    linarith
  have ht : Filter.Tendsto (fun k => 1 + (∑ j ∈ Finset.range k, fr K o j) * S) Filter.atTop
      (nhds (1 + 1 * S)) :=
    tendsto_const_nhds.add (hrec.tendsto_sum_nat.mul tendsto_const_nhds)
  have := le_of_tendsto' ht hK
  linarith

lemma bdd_of_not_rec (hc : IsStoch K) (o : V) (h : ¬ IsRecurrentChain K o) :
    ∃ G, ∀ N, green K o N ≤ G := by
  unfold IsRecurrentChain at h
  have efr : firstReturnProb K o = fr K o := funext (firstReturnProb_eq o)
  rw [efr] at h
  have hle1 : ∑' k, fr K o k ≤ 1 :=
    Real.tsum_le_of_sum_range_le (fr_nn hc o) (fr_sum_le hc o)
  have hlt : ∑' k, fr K o k < 1 := by
    rcases hle1.lt_or_eq with h' | h'
    · exact h'
    · exact absurd (h' ▸ (fr_summable hc o).hasSum) h
  exact ⟨_, green_bdd hc o hlt⟩

lemma not_bdd_of_rec (hc : IsStoch K) (o : V) (h : IsRecurrentChain K o)
    (M : ℝ) (hM : ∀ N, green K o N ≤ M) : False := by
  unfold IsRecurrentChain at h
  have efr : firstReturnProb K o = fr K o := funext (firstReturnProb_eq o)
  rw [efr] at h
  exact not_bdd hc o h M hM

/-- The truncated Green function `U_N = ∑_{n<N} p_n`. -/
noncomputable def U (K : V → V → ℝ) (o : V) (N : ℕ) (x : V) : ℝ :=
  ∑ n ∈ Finset.range N, p K o n x

lemma U_nn (hc : IsStoch K) (o : V) (N : ℕ) (x : V) : 0 ≤ U K o N x :=
  Finset.sum_nonneg fun n _ => p_nn hc o n x

lemma U_le (hc : IsStoch K) (o : V) (N : ℕ) (x : V) : U K o N x ≤ N := by
  unfold U
  calc ∑ n ∈ Finset.range N, p K o n x ≤ ∑ n ∈ Finset.range N, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => p_le hc o n x
    _ = N := by simp

lemma U_summable (hc : IsStoch K) (o : V) (N : ℕ) : Summable (U K o N) :=
  summable_sum fun n _ => p_summable hc o n

lemma U_abs_le (hc : IsStoch K) (o : V) (N : ℕ) (x : V) : |U K o N x| ≤ N := by
  rw [abs_of_nonneg (U_nn hc o N x)]; exact U_le hc o N x

lemma green_eq (o : V) (N : ℕ) : green K o N = U K o N o := rfl

/-- `T U_N = ∑_{n<N} p_{n+1}`. -/
lemma T_U (hc : IsStoch K) (o : V) (N : ℕ) (y : V) :
    T K (U K o N) y = ∑ n ∈ Finset.range N, p K o (n + 1) y := by
  unfold U
  rw [T_sum hc _ _ (p_summable hc o)]
  rfl

lemma U_sub_T (hc : IsStoch K) (o : V) (N : ℕ) (y : V) :
    U K o N y - T K (U K o N) y = p K o 0 y - p K o N y := by
  rw [T_U hc]; unfold U
  rw [← Finset.sum_sub_distrib, Finset.sum_range_sub' (fun n => p K o n y)]

end Stoch

/-! ## Symmetric stochastic kernels: the Hardy inequality -/

section Sym

variable {V : Type*} {c : V → V → ℝ}

/-- `c` is a symmetric stochastic kernel. -/
def IsSymStoch (c : V → V → ℝ) : Prop := IsStoch c ∧ ∀ x y, c x y = c y x

lemma cp_eq (hc : IsSymStoch c) (o : V) (n : ℕ) (x : V) :
    (Summable fun y => c x y * p c o n y) ∧ ∑' y, c x y * p c o n y = p c o (n + 1) x := by
  have e : (fun y => c x y * p c o n y) = fun y => p c o n y * c y x := by
    funext y; rw [hc.2 x y]; ring
  rw [e]; exact ⟨T_row hc.1 (p_summable hc.1 o n) x, rfl⟩

lemma cu (hc : IsSymStoch c) (o : V) (N : ℕ) (x : V) :
    (Summable fun y => c x y * U c o N y) ∧
      ∑' y, c x y * U c o N y = ∑ n ∈ Finset.range N, p c o (n + 1) x := by
  unfold U
  simp_rw [Finset.mul_sum]
  refine ⟨summable_sum fun n _ => (cp_eq hc o n x).1, ?_⟩
  rw [Summable.tsum_finsetSum fun n _ => (cp_eq hc o n x).1]
  exact Finset.sum_congr rfl fun n _ => (cp_eq hc o n x).2

lemma dom1 {ι : Type*} {f g : ι → ℝ} (hg : Summable g) (H : ℝ) (hf : ∀ x, |f x| ≤ H)
    (hg0 : ∀ x, 0 ≤ g x) : Summable fun x => f x * g x :=
  dom_summable (hg.mul_left H) fun x => by
    rw [abs_mul, abs_of_nonneg (hg0 x)]; exact mul_le_mul_of_nonneg_right (hf x) (hg0 x)

/-- Summation by parts against the truncated Green function. -/
lemma ibp (hc : IsSymStoch c) (o : V) (N : ℕ) (h : V → ℝ) (H : ℝ) (hH : ∀ x, |h x| ≤ H) :
    Summable (fun q : V × V => c q.1 q.2 * (U c o N q.1 - U c o N q.2) * (h q.1 - h q.2)) ∧
    ∑' q : V × V, c q.1 q.2 * (U c o N q.1 - U c o N q.2) * (h q.1 - h q.2) =
      2 * (h o - ∑' x, h x * p c o N x) := by
  have hs := hc.1
  set W := U c o N with hWdef
  have B1 : Summable (fun q : V × V => c q.1 q.2 * W q.1) :=
    prod_summable (F := fun x y => c x y * W x)
      (fun x y => mul_nonneg (K_nn hs x y) (U_nn hs o N x))
      (fun x => (K_sum hs x).mul_right _)
      (by simp_rw [tsum_mul_right, K_tsum hs, one_mul]; exact U_summable hs o N)
  have B2 : Summable (fun q : V × V => c q.1 q.2 * W q.2) := by
    refine (swap_summable B1).congr fun q => ?_
    simp only [Prod.fst_swap, Prod.snd_swap]; rw [hc.2]
  set A : V × V → ℝ := fun q => c q.1 q.2 * (W q.1 - W q.2) * h q.1 with hA
  have SA : Summable A := dom_summable ((B1.add B2).mul_left H) fun q => by
    simp only [A]
    rw [abs_mul, abs_mul, abs_of_nonneg (K_nn hs _ _)]
    have h1 := U_nn hs o N q.1
    have h2 := U_nn hs o N q.2
    have hΔ : |W q.1 - W q.2| ≤ W q.1 + W q.2 := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    have hc0 := K_nn hs q.1 q.2
    calc c q.1 q.2 * |W q.1 - W q.2| * |h q.1| ≤ c q.1 q.2 * (W q.1 + W q.2) * H :=
          mul_le_mul (mul_le_mul_of_nonneg_left hΔ hc0) (hH _) (abs_nonneg _)
            (mul_nonneg hc0 (by linarith))
      _ = H * (c q.1 q.2 * W q.1 + c q.1 q.2 * W q.2) := by ring
  have SAs : Summable (fun q : V × V => A q.swap) := swap_summable SA
  have term : ∀ q : V × V, c q.1 q.2 * (W q.1 - W q.2) * (h q.1 - h q.2) = A q + A q.swap := by
    intro q; simp only [A, Prod.fst_swap, Prod.snd_swap]; rw [hc.2 q.2 q.1]; ring
  refine ⟨(SA.add SAs).congr fun q => (term q).symm, ?_⟩
  simp_rw [term]
  rw [SA.tsum_add SAs, tsum_swap_eq A, SA.tsum_prod]
  have inner : ∀ x, ∑' y, A (x, y) = h x * (p c o 0 x - p c o N x) := by
    intro x
    have e : (fun y => A (x, y)) = fun y => h x * (c x y * W x - c x y * W y) := by
      funext y; simp only [A]; ring
    rw [e, tsum_mul_left, Summable.tsum_sub ((K_sum hs x).mul_right _) (cu hc o N x).1,
      tsum_mul_right, (cu hc o N x).2, K_tsum hs, one_mul]
    simp only [W, U]
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub' (fun n => p c o n x)]
  simp_rw [inner, mul_sub]
  have hb : ∀ n, Summable fun x => h x * p c o n x :=
    fun n => dom1 (p_summable hs o n) H hH (p_nn hs o n)
  rw [Summable.tsum_sub (hb 0) (hb N)]
  have : ∑' x, h x * p c o 0 x = h o := by
    simp only [p, mul_ite, mul_one, mul_zero]; exact tsum_ite_eq o h
  rw [this]; ring

lemma energy_u (hc : IsSymStoch c) (o : V) (N : ℕ) :
    Summable (fun q : V × V => c q.1 q.2 * (U c o N q.1 - U c o N q.2) ^ 2) ∧
    ∑' q : V × V, c q.1 q.2 * (U c o N q.1 - U c o N q.2) ^ 2 ≤ 2 * U c o N o := by
  obtain ⟨hs, he⟩ := ibp hc o N (U c o N) _ (U_abs_le hc.1 o N)
  have eq : (fun q : V × V => c q.1 q.2 * (U c o N q.1 - U c o N q.2) ^ 2) =
      fun q => c q.1 q.2 * (U c o N q.1 - U c o N q.2) * (U c o N q.1 - U c o N q.2) := by
    funext q; ring
  rw [eq]
  refine ⟨hs, ?_⟩
  rw [he]
  have : 0 ≤ ∑' x, U c o N x * p c o N x :=
    tsum_nonneg fun x => mul_nonneg (U_nn hc.1 o N x) (p_nn hc.1 o N x)
  linarith

lemma ip_p (hc : IsSymStoch c) (o : V) : ∀ m n,
    ∑' y, p c o m y * p c o n y = p c o (m + n) o
  | 0, n => by
    simp only [p, ite_mul, one_mul, zero_mul, zero_add]
    exact tsum_ite_eq o _
  | m + 1, n => by
    have hs := hc.1
    have hS : Summable (fun q : V × V => c q.1 q.2 * p c o m q.2 * p c o n q.1) := by
      have hF := prod_summable (F := fun y x => c y x * p c o n y)
        (fun y x => mul_nonneg (K_nn hs y x) (p_nn hs o n y))
        (fun y => (K_sum hs y).mul_right _)
        (by simp_rw [tsum_mul_right, K_tsum hs, one_mul]; exact p_summable hs o n)
      refine dom_summable hF fun q => ?_
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (K_nn hs _ _) (p_nn hs o m _)) (p_nn hs o n _))]
      have := p_le hs o m q.2
      have h0 := mul_nonneg (K_nn hs q.1 q.2) (p_nn hs o n q.1)
      calc c q.1 q.2 * p c o m q.2 * p c o n q.1 = c q.1 q.2 * p c o n q.1 * p c o m q.2 := by
            ring
        _ ≤ c q.1 q.2 * p c o n q.1 * 1 := mul_le_mul_of_nonneg_left this h0
        _ = _ := mul_one _
    calc ∑' y, p c o (m + 1) y * p c o n y
        = ∑' y, ∑' x, c y x * p c o m x * p c o n y := by
          refine tsum_congr fun y => ?_
          rw [← (cp_eq hc o m y).2, ← tsum_mul_right]
      _ = ∑' x, ∑' y, c y x * p c o m x * p c o n y :=
          tsum_comm_of (G := fun y x => c y x * p c o m x * p c o n y) hS
      _ = ∑' x, p c o m x * p c o (n + 1) x := by
          refine tsum_congr fun x => ?_
          rw [← (cp_eq hc o n x).2, ← tsum_mul_left]
          refine tsum_congr fun y => ?_
          rw [hc.2 y x]; ring
      _ = p c o (m + 1 + n) o := by rw [ip_p hc o m (n + 1)]; congr 1; omega

lemma p_tendsto (hc : IsSymStoch c) (o : V) (G : ℝ) (hG : ∀ N, green c o N ≤ G) (x : V) :
    Filter.Tendsto (fun N => p c o N x) Filter.atTop (nhds 0) := by
  have hs := hc.1
  have hsum : Summable fun n => p c o n o :=
    summable_of_sum_range_le (fun n => p_nn hs o n o) hG
  have hlim : Filter.Tendsto (fun N => p c o (N + N) o) Filter.atTop (nhds 0) :=
    hsum.tendsto_atTop_zero.comp
      (Filter.tendsto_atTop_mono (fun n => Nat.le_add_right n n) Filter.tendsto_id)
  have hbound : ∀ N, p c o N x ≤ Real.sqrt (p c o (N + N) o) := by
    intro N
    have hS : Summable fun y => p c o N y * p c o N y :=
      Summable.of_nonneg_of_le (fun y => mul_nonneg (p_nn hs o N y) (p_nn hs o N y))
        (fun y => mul_le_of_le_one_right (p_nn hs o N y) (p_le hs o N y)) (p_summable hs o N)
    have h1 : p c o N x * p c o N x ≤ p c o (N + N) o := by
      rw [← ip_p hc o N N]
      exact hS.le_tsum x (fun y _ => mul_nonneg (p_nn hs o N y) (p_nn hs o N y))
    calc p c o N x = Real.sqrt (p c o N x ^ 2) := (Real.sqrt_sq (p_nn hs o N x)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
  have hlim2 : Filter.Tendsto (fun N => Real.sqrt (p c o (N + N) o)) Filter.atTop (nhds 0) := by
    simpa using hlim.sqrt
  exact squeeze_zero (fun N => p_nn hs o N x) hbound hlim2

/-- The one-sided Hardy inequality, for bounded summable `f`. -/
lemma hardy (hc : IsSymStoch c) (o : V) (G : ℝ) (hG : ∀ N, green c o N ≤ G) (f : V → ℝ)
    (hf : Summable f) (H : ℝ) (hH : ∀ x, |f x| ≤ H) (t : ℝ) (ht : 0 < t) :
    f o ≤ (2 * t * G + (∑' q : V × V, c q.1 q.2 * (f q.1 - f q.2) ^ 2) / t) / 4 := by
  have hs := hc.1
  have C1 : Summable (fun q : V × V => c q.1 q.2 * f q.1 ^ 2) := by
    refine prod_summable (F := fun x y => c x y * f x ^ 2)
      (fun x y => mul_nonneg (K_nn hs x y) (sq_nonneg _))
      (fun x => (K_sum hs x).mul_right _) ?_
    simp_rw [tsum_mul_right, K_tsum hs, one_mul]
    refine dom_summable (hf.abs.mul_left H) fun x => ?_
    rw [abs_of_nonneg (sq_nonneg _), sq, ← abs_mul_abs_self]
    exact mul_le_mul_of_nonneg_right (hH x) (abs_nonneg _)
  have C2 : Summable (fun q : V × V => c q.1 q.2 * f q.2 ^ 2) := by
    refine (swap_summable C1).congr fun q => ?_
    simp only [Prod.fst_swap, Prod.snd_swap]; rw [hc.2]
  have Ef : Summable (fun q : V × V => c q.1 q.2 * (f q.1 - f q.2) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun q => mul_nonneg (K_nn hs _ _) (sq_nonneg _))
      (fun q => ?_) ((C1.add C2).mul_left 2)
    have hc0 := K_nn hs q.1 q.2
    have : (f q.1 - f q.2) ^ 2 ≤ 2 * (f q.1 ^ 2 + f q.2 ^ 2) := by
      nlinarith [sq_nonneg (f q.1 + f q.2)]
    calc c q.1 q.2 * (f q.1 - f q.2) ^ 2 ≤ c q.1 q.2 * (2 * (f q.1 ^ 2 + f q.2 ^ 2)) :=
          mul_le_mul_of_nonneg_left this hc0
      _ = 2 * (c q.1 q.2 * f q.1 ^ 2 + c q.1 q.2 * f q.2 ^ 2) := by ring
  set EF := ∑' q : V × V, c q.1 q.2 * (f q.1 - f q.2) ^ 2
  have hN : ∀ N, f o ≤ ∑' x, f x * p c o N x + (2 * t * G + EF / t) / 4 := by
    intro N
    obtain ⟨sU, eU⟩ := energy_u hc o N
    obtain ⟨sUf, eUf⟩ := ibp hc o N f H hH
    have hUo : U c o N o ≤ G := hG N
    set W := U c o N
    have key : ∀ q : V × V, c q.1 q.2 * (W q.1 - W q.2) * (f q.1 - f q.2) ≤
        (t * (c q.1 q.2 * (W q.1 - W q.2) ^ 2) + c q.1 q.2 * (f q.1 - f q.2) ^ 2 / t) / 2 := by
      intro q
      set a := W q.1 - W q.2
      set b := f q.1 - f q.2
      have hab : a * b ≤ (t * a ^ 2 + b ^ 2 / t) / 2 := by
        have e : (t * a ^ 2 + b ^ 2 / t) / 2 - a * b = (t * a - b) ^ 2 / (2 * t) := by
          field_simp; ring
        have : 0 ≤ (t * a - b) ^ 2 / (2 * t) := by positivity
        linarith
      have hc0 := K_nn hs q.1 q.2
      calc c q.1 q.2 * a * b = c q.1 q.2 * (a * b) := by ring
        _ ≤ c q.1 q.2 * ((t * a ^ 2 + b ^ 2 / t) / 2) := mul_le_mul_of_nonneg_left hab hc0
        _ = _ := by ring
    have hle := Summable.tsum_le_tsum key sUf
      (((sU.mul_left t).add (Ef.div_const t)).div_const 2)
    rw [eUf, tsum_div_const, Summable.tsum_add (sU.mul_left t) (Ef.div_const t), tsum_mul_left,
      tsum_div_const] at hle
    have h1 : t * ∑' q : V × V, c q.1 q.2 * (W q.1 - W q.2) ^ 2 ≤ t * (2 * G) :=
      mul_le_mul_of_nonneg_left (by linarith) ht.le
    linarith
  have hT : Filter.Tendsto (fun N => ∑' x, f x * p c o N x + (2 * t * G + EF / t) / 4)
      Filter.atTop (nhds (0 + (2 * t * G + EF / t) / 4)) := by
    refine Filter.Tendsto.add ?_ tendsto_const_nhds
    have := tendsto_tsum_of_dominated_convergence (f := fun N x => f x * p c o N x)
      (g := fun _ => (0 : ℝ)) (bound := fun x => |f x|) (𝓕 := Filter.atTop) hf.abs
      (fun x => by simpa using (p_tendsto hc o G hG x).const_mul (f x))
      (Filter.Eventually.of_forall fun N x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (p_nn hs o N x)]
        exact mul_le_of_le_one_right (abs_nonneg _) (p_le hs o N x))
    simpa using this
  have := ge_of_tendsto' hT hN
  linarith

end Sym

/-! ## The comparison: a doubly stochastic kernel and its symmetrization -/

section Comp

variable {V : Type*} {P : V → V → ℝ}

lemma isSymStoch_symm (hP : IsStoch P) (hcol : ∀ y, HasSum (fun x => P x y) 1) :
    IsSymStoch (fun x y => (P x y + P y x) / 2) := by
  refine ⟨⟨fun x y => by have := K_nn hP x y; have := K_nn hP y x; positivity, fun x => ?_⟩,
    fun x y => by ring⟩
  have := ((hP.2 x).add (hcol x)).div_const 2
  simpa using this

/-- The energy identity: `E_Q(U) = 2 (U(o) - ⟨U, p_N⟩) ≤ 2 U(o)` for the `P`-Green function. -/
lemma energy_P (hP : IsStoch P) (hcol : ∀ y, HasSum (fun x => P x y) 1) (o : V) (N : ℕ) :
    ∑' q : V × V, (P q.1 q.2 + P q.2 q.1) / 2 * (U P o N q.1 - U P o N q.2) ^ 2 ≤
      2 * U P o N o := by
  set W := U P o N with hWdef
  have hW0 := U_nn hP o N
  have hWH := U_le hP o N
  have hWs : Summable W := U_summable hP o N
  have hW2 : Summable fun x => W x ^ 2 := by
    refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_) (hWs.mul_left (N : ℝ))
    rw [sq]; exact mul_le_mul_of_nonneg_right (hWH x) (hW0 x)
  have hPn := K_nn hP
  -- the three pieces
  have S1 : Summable (fun q : V × V => P q.1 q.2 * W q.1 ^ 2) :=
    prod_summable (F := fun x y => P x y * W x ^ 2)
      (fun x y => mul_nonneg (hPn x y) (sq_nonneg _)) (fun x => (K_sum hP x).mul_right _)
      (by simp_rw [tsum_mul_right, K_tsum hP, one_mul]; exact hW2)
  have S2' : Summable (fun q : V × V => P q.2 q.1 * W q.1 ^ 2) :=
    prod_summable (F := fun y x => P x y * W y ^ 2)
      (fun y x => mul_nonneg (hPn x y) (sq_nonneg _)) (fun y => (hcol y).summable.mul_right _)
      (by simp_rw [tsum_mul_right, (hcol _).tsum_eq, one_mul]; exact hW2)
  have S2 : Summable (fun q : V × V => P q.1 q.2 * W q.2 ^ 2) := swap_summable S2'
  have S0 : Summable (fun q : V × V => P q.1 q.2 * W q.1) :=
    prod_summable (F := fun x y => P x y * W x)
      (fun x y => mul_nonneg (hPn x y) (hW0 x)) (fun x => (K_sum hP x).mul_right _)
      (by simp_rw [tsum_mul_right, K_tsum hP, one_mul]; exact hWs)
  have S3 : Summable (fun q : V × V => P q.1 q.2 * W q.1 * W q.2) := by
    refine dom_summable (S0.mul_left (N : ℝ)) fun q => ?_
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (hPn _ _) (hW0 _)) (hW0 _))]
    calc P q.1 q.2 * W q.1 * W q.2 ≤ P q.1 q.2 * W q.1 * N :=
          mul_le_mul_of_nonneg_left (hWH _) (mul_nonneg (hPn _ _) (hW0 _))
      _ = N * (P q.1 q.2 * W q.1) := by ring
  set F : V × V → ℝ := fun q => P q.1 q.2 * (W q.1 - W q.2) ^ 2 with hF
  have eF : ∀ q, F q = P q.1 q.2 * W q.1 ^ 2 + P q.1 q.2 * W q.2 ^ 2 -
      2 * (P q.1 q.2 * W q.1 * W q.2) := fun q => by simp only [F]; ring
  have SF : Summable F := ((S1.add S2).sub (S3.mul_left 2)).congr fun q => (eF q).symm
  have SFs : Summable fun q : V × V => F q.swap := swap_summable SF
  -- reduce to `F`
  have e1 : ∑' q : V × V, (P q.1 q.2 + P q.2 q.1) / 2 * (W q.1 - W q.2) ^ 2 = ∑' q, F q := by
    have : ∀ q : V × V, (P q.1 q.2 + P q.2 q.1) / 2 * (W q.1 - W q.2) ^ 2 = (F q + F q.swap) / 2 :=
      fun q => by simp only [F, Prod.fst_swap, Prod.snd_swap]; ring
    simp_rw [this]
    rw [tsum_div_const, SF.tsum_add SFs, tsum_swap_eq F]; ring
  rw [e1]
  -- compute the three pieces
  have t1 : ∑' q : V × V, P q.1 q.2 * W q.1 ^ 2 = ∑' x, W x ^ 2 := by
    rw [S1.tsum_prod]; simp_rw [tsum_mul_right, K_tsum hP, one_mul]
  have t2 : ∑' q : V × V, P q.1 q.2 * W q.2 ^ 2 = ∑' x, W x ^ 2 := by
    rw [← tsum_swap_eq (fun q : V × V => P q.1 q.2 * W q.2 ^ 2)]
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [S2'.tsum_prod]; simp_rw [tsum_mul_right, (hcol _).tsum_eq, one_mul]
  have S3' : Summable (fun q : V × V => P q.2 q.1 * W q.2 * W q.1) := by
    have := swap_summable S3; simpa using this
  have t3 : ∑' q : V × V, P q.1 q.2 * W q.1 * W q.2 = ∑' y, T P W y * W y := by
    rw [← tsum_swap_eq (fun q : V × V => P q.1 q.2 * W q.1 * W q.2)]
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [S3'.tsum_prod]
    refine tsum_congr fun y => ?_
    unfold T; rw [← tsum_mul_right]
    exact tsum_congr fun x => by ring
  have hTW : Summable fun y => T P W y * W y := by
    refine Summable.of_nonneg_of_le (fun y => mul_nonneg (T_nn hP hW0 y) (hW0 y))
      (fun y => ?_) ((T_summable hP hWs).mul_right (N : ℝ))
    exact mul_le_mul_of_nonneg_left (hWH y) (T_nn hP hW0 y)
  have hWp : Summable fun y => W y * p P o N y :=
    dom1 (p_summable hP o N) N (U_abs_le hP o N) (p_nn hP o N)
  have t4 : ∑' y, W y ^ 2 - ∑' y, T P W y * W y = W o - ∑' y, W y * p P o N y := by
    rw [← hW2.tsum_sub hTW]
    have : ∀ y, W y ^ 2 - T P W y * W y = W y * p P o 0 y - W y * p P o N y := by
      intro y
      have := U_sub_T hP o N y
      rw [← hWdef] at this
      calc W y ^ 2 - T P W y * W y = W y * (W y - T P W y) := by ring
        _ = _ := by rw [this]; ring
    simp_rw [this]
    have h0 : Summable fun y => W y * p P o 0 y :=
      dom1 (p_summable hP o 0) N (U_abs_le hP o N) (p_nn hP o 0)
    rw [h0.tsum_sub hWp]
    congr 1
    simp only [p, mul_ite, mul_one, mul_zero]; exact tsum_ite_eq o W
  have ht : ∑' q, F q = 2 * (W o - ∑' y, W y * p P o N y) := by
    simp_rw [eF]
    rw [Summable.tsum_sub (S1.add S2) (S3.mul_left 2), S1.tsum_add S2, tsum_mul_left, t1, t2, t3,
      ← t4]
    ring
  rw [ht]
  have : 0 ≤ ∑' y, W y * p P o N y := tsum_nonneg fun y => mul_nonneg (hW0 y) (p_nn hP o N y)
  linarith

/-- **Comparison.** If the symmetrization of a doubly stochastic `P` is transient at `o`, so
is `P`. -/
theorem not_rec_of_not_rec_symm (hP : IsStoch P) (hcol : ∀ y, HasSum (fun x => P x y) 1)
    (o : V) (h : ¬ IsRecurrentChain (fun x y => (P x y + P y x) / 2) o) :
    ¬ IsRecurrentChain P o := by
  intro hrec
  have hc := isSymStoch_symm hP hcol
  obtain ⟨G, hG⟩ := bdd_of_not_rec hc.1 o h
  refine not_bdd_of_rec hP o hrec G fun N => ?_
  rw [green_eq]
  have h1 := hardy hc o G hG (U P o N) (U_summable hP o N) N (U_abs_le hP o N) 1 one_pos
  have h2 := energy_P hP hcol o N
  rw [div_one] at h1
  linarith

end Comp

/-! ## The walk kernel of a probability on `G` -/

section Walk

variable {G X : Type*} [Group G] [MulAction G X]

lemma hasSum_aux (μ : G → ℝ) (hμ0 : ∀ g, 0 ≤ μ g) (hμ : HasSum μ 1) (R : G → X → Prop)
    (pt : G → X) (hR : ∀ g z, R g z ↔ z = pt g) :
    HasSum (fun z => ∑' g, if R g z then μ g else 0) 1 := by
  have row : ∀ g, HasSum (fun z => if R g z then μ g else 0) (μ g) := by
    intro g
    have : (fun z => if R g z then μ g else 0) = fun z => if z = pt g then μ g else 0 := by
      funext z; simp only [hR]
    rw [this]; exact hasSum_ite_eq (pt g) (μ g)
  have hS : Summable (fun q : G × X => if R q.1 q.2 then μ q.1 else 0) :=
    prod_summable (F := fun g z => if R g z then μ g else 0)
      (fun g z => by split_ifs <;> simp [hμ0 g]) (fun g => (row g).summable)
      (by simp_rw [fun g => (row g).tsum_eq]; exact hμ.summable)
  refine (col_summable (G := fun g z => if R g z then μ g else 0) hS).hasSum_iff.2 ?_
  rw [← tsum_comm_of (G := fun g z => if R g z then μ g else 0) hS]
  simp_rw [fun g => (row g).tsum_eq]
  exact hμ.tsum_eq

lemma walkKernel_isStoch (μ : G → ℝ) (hμ0 : ∀ g, 0 ≤ μ g) (hμ : HasSum μ 1) :
    IsStoch (walkKernel μ : X → X → ℝ) := by
  refine ⟨fun x y => tsum_nonneg fun g => by split_ifs <;> simp [hμ0 g], fun x => ?_⟩
  exact hasSum_aux μ hμ0 hμ (fun g y => g • x = y) (fun g => g • x) (fun g z => eq_comm)

lemma walkKernel_col (μ : G → ℝ) (hμ0 : ∀ g, 0 ≤ μ g) (hμ : HasSum μ 1) (y : X) :
    HasSum (fun x => (walkKernel μ : X → X → ℝ) x y) 1 :=
  hasSum_aux μ hμ0 hμ (fun g x => g • x = y) (fun g => g⁻¹ • y)
    (fun _ _ => eq_inv_smul_iff.symm)

lemma walkKernel_symm (μ : G → ℝ) (hμ0 : ∀ g, 0 ≤ μ g) (hμ : HasSum μ 1) (x y : X) :
    walkKernel (fun g => (μ g + μ g⁻¹) / 2) x y =
      (walkKernel μ x y + walkKernel μ y x) / 2 := by
  unfold walkKernel
  have hinv : Summable fun g : G => μ g⁻¹ :=
    (Equiv.inv G).summable_iff.2 hμ.summable
  have s1 : Summable (fun g : G => if g • x = y then μ g else 0) :=
    Summable.of_nonneg_of_le (fun g => by split_ifs <;> simp [hμ0 g])
      (fun g => by split_ifs <;> simp [hμ0 g]) hμ.summable
  have s2 : Summable (fun g : G => if g • x = y then μ g⁻¹ else 0) :=
    Summable.of_nonneg_of_le (fun g => by split_ifs <;> simp [hμ0 g⁻¹])
      (fun g => by split_ifs <;> simp [hμ0 g⁻¹]) hinv
  have e2 : ∑' g : G, (if g • x = y then μ g⁻¹ else 0) =
      ∑' g : G, (if g • y = x then μ g else 0) := by
    rw [← (Equiv.inv G).tsum_eq]
    refine tsum_congr fun g => ?_
    simp only [Equiv.inv_apply, inv_inv, inv_smul_eq_iff]
    by_cases h : g • y = x
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun h' => h h'.symm), if_neg h]
  rw [← e2, ← s1.tsum_add s2, ← tsum_div_const]
  refine tsum_congr fun g => ?_
  split_ifs <;> ring

end Walk

end BaldiLohouePeyriere.IETB

namespace BaldiLohouePeyriere

open BaldiLohouePeyriere.IETB

theorem chk_not_isRecurrentChain_of_not_isRecurrentChain_symmetrization {G X : Type*} [Group G]
    [Countable G] [MulAction G X] [MulAction.IsPretransitive G X] (μ : G → ℝ)
    (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1)
    (hν : ∀ x₀ : X, ¬ IsRecurrentChain (walkKernel fun g => (μ g + μ g⁻¹) / 2) x₀) :
    ∀ x₀ : X, ¬ IsRecurrentChain (walkKernel μ) x₀ := by
  intro x₀
  have e : (walkKernel (fun g => (μ g + μ g⁻¹) / 2) : X → X → ℝ) =
      fun x y => (walkKernel μ x y + walkKernel μ y x) / 2 := by
    funext x y; exact walkKernel_symm μ hμ.1 hμ.2 x y
  have h := hν x₀
  rw [e] at h
  exact not_rec_of_not_rec_symm (walkKernel_isStoch μ hμ.1 hμ.2)
    (walkKernel_col μ hμ.1 hμ.2) x₀ h

end BaldiLohouePeyriere

end

open IntervalExchange
theorem solution {G X : Type*} [Group G]
    [Countable G] [MulAction G X] [MulAction.IsPretransitive G X] (μ : G → ℝ)
    (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1)
    (hν : ∀ x₀ : X, ¬ IsRecurrentChain (walkKernel fun g => (μ g + μ g⁻¹) / 2) x₀) :
    ∀ x₀ : X, ¬ IsRecurrentChain (walkKernel μ) x₀ :=
  BaldiLohouePeyriere.chk_not_isRecurrentChain_of_not_isRecurrentChain_symmetrization μ hμ hν
