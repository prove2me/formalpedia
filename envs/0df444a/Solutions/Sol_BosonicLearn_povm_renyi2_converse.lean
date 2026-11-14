-- Prove2me | solution 1 for BosonicLearn.povm_renyi2_converse
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-14T02:14:45.909253+00:00
-- url     : https://prove2.me/submissions/c4863eae-b32c-4f47-b7ac-176ac4e6a695

import Mathlib
import Definitions.Def_BosonicLearn_FockPOVM
import Theorems.Thm_BosonicLearn_isDensity_of_posSemidef

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open MeasureTheory
open scoped ENNReal Matrix

open BosonicLearn

noncomputable section

/-! ### Finite quadratic forms of an effect matrix -/

/-- The hypothesis `FockPOVM.effect_form` at a measurable set. -/
private abbrev EffB {I : Type} (E : Matrix I I ℂ) : Prop :=
  ∀ (s : Finset I) (z : I → ℂ),
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0 ∧
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ∧
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2

private lemma eff_diag {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E) (i : I) :
    (E i i).im = 0 ∧ 0 ≤ (E i i).re ∧ (E i i).re ≤ 1 := by
  have h := hE {i} (Pi.single i 1)
  simpa using h

/-- `E` is Hermitian: polarize the reality of the quadratic forms on `{i, j}`. -/
private lemma eff_herm {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E) (i j : I) :
    E j i = star (E i j) := by
  by_cases hij : i = j
  · subst hij
    exact (Complex.conj_eq_iff_im.mpr (eff_diag hE i).1).symm
  · have hji : j ≠ i := fun h => hij h.symm
    have hii := (eff_diag hE i).1
    have hjj := (eff_diag hE j).1
    have h1 := (hE {i, j} (fun k => if k = i then 1 else if k = j then 1 else 0)).1
    have h2 := (hE {i, j} (fun k => if k = i then 1 else if k = j then Complex.I else 0)).1
    simp [Finset.sum_pair hij, hji] at h1 h2
    apply Complex.ext
    · simp
      linarith
    · simp
      linarith

/-- Cauchy–Schwarz for finite complex vectors, in `dotProduct` form. -/
private lemma cs_dot {ι : Type} [Fintype ι] (u v : ι → ℂ) :
    ‖star u ⬝ᵥ v‖ ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * (∑ i, ‖v i‖ ^ 2) := by
  have h1 : ‖star u ⬝ᵥ v‖ ≤ ∑ i, ‖u i‖ * ‖v i‖ := by
    unfold dotProduct
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖u i‖) (fun i => ‖v i‖)
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

open scoped MatrixOrder ComplexOrder in
/-- Cauchy–Schwarz for the positive form of `E` on a finite set: the block is `Bᴴ B`, so the form is an inner
product of `B w` and `B z`, and `‖B z‖² = ⟨z, E z⟩`. -/
private lemma eff_cs_sharp {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E) (s : Finset I)
    (w z : I → ℂ) :
    ‖∑ i ∈ s, ∑ j ∈ s, star (w i) * E i j * z j‖ ^ 2 ≤
      (∑ i ∈ s, ∑ j ∈ s, star (w i) * E i j * w j).re *
        (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re := by
  let M : Matrix s s ℂ := fun a b => E a b
  have form : ∀ x y : I → ℂ, star (fun a : s => x a) ⬝ᵥ M.mulVec (fun a : s => y a) =
      ∑ i ∈ s, ∑ j ∈ s, star (x i) * E i j * y j := by
    intro x y
    rw [← Finset.sum_coe_sort s]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [M, mul_assoc]
  have hM : M.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext a b
      simp only [Matrix.conjTranspose_apply]
      exact (eff_herm hE b a).symm
    · let x' : I → ℂ := fun i => if h : i ∈ s then x ⟨i, h⟩ else 0
      have hx : (fun a : s => x' a) = x := by
        funext a
        simp [x']
      have h := hE s x'
      rw [← hx, form x' x', Complex.nonneg_iff]
      exact ⟨h.2.1, h.1.symm⟩
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  have key : ∀ x y : s → ℂ, star x ⬝ᵥ M.mulVec y = star (B.mulVec x) ⬝ᵥ B.mulVec y := by
    intro x y
    rw [hB, Matrix.star_eq_conjTranspose, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.star_mulVec]
  have hq : ∀ x : s → ℂ, ∑ c, ‖B.mulVec x c‖ ^ 2 = (star x ⬝ᵥ M.mulVec x).re := by
    intro x
    rw [key x x]
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have h1 := cs_dot (B.mulVec fun a : s => w a) (B.mulVec fun a : s => z a)
  rw [← form w z, key]
  refine h1.trans ?_
  rw [hq, hq, form w w, form z z]

/-- `E² ≤ E` on the diagonal: `∑ⱼ |Eᵢⱼ|² ≤ Eᵢᵢ`. -/
private lemma row_sq_le {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E) (i : I)
    (s : Finset I) : ∑ j ∈ s, ‖E i j‖ ^ 2 ≤ (E i i).re := by
  have hi : i ∈ insert i s := Finset.mem_insert_self i s
  have hsub : ∑ j ∈ s, ‖E i j‖ ^ 2 ≤ ∑ j ∈ insert i s, ‖E i j‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert i s) fun j _ _ => by positivity
  generalize insert i s = s' at hi hsub
  set T : ℝ := ∑ j ∈ s', ‖E i j‖ ^ 2 with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j _ => by positivity
  have h := eff_cs_sharp hE s' (fun k => if k = i then 1 else 0) (fun j => star (E i j))
  beta_reduce at h
  have e1 : ∑ k ∈ s', ∑ j ∈ s', star (if k = i then (1 : ℂ) else 0) * E k j * star (E i j) =
      ((T : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single i]
    · simp only [if_true, star_one, one_mul]
      rw [hT]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.star_def, Complex.mul_conj']
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd hi h
  have e2 : ∑ k ∈ s', ∑ j ∈ s', star (if k = i then (1 : ℂ) else 0) * E k j *
      (if j = i then (1 : ℂ) else 0) = E i i := by
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · intro h
        exact absurd hi h
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd hi h
  have h3 := (hE s' (fun j => star (E i j))).2.2
  simp only [norm_star] at h3
  have hii : 0 ≤ (E i i).re := (eff_diag hE i).2.1
  rw [e1, e2, Complex.norm_real, Real.norm_of_nonneg hT0] at h
  have h4 : T ^ 2 ≤ (E i i).re * T := h.trans (mul_le_mul_of_nonneg_left h3 hii)
  rcases hT0.eq_or_lt with h0 | hpos
  · linarith
  · have h5 : T * T ≤ (E i i).re * T := by simpa [sq] using h4
    have := le_of_mul_le_mul_right h5 hpos
    linarith

/-! ### The diagonal state -/

private lemma diag_density {I : Type} [DecidableEq I] [Countable I] (p : I → ℝ) (hp : ∀ i, 0 < p i)
    (hp1 : HasSum p 1) : IsDensity (Matrix.diagonal fun i => ((p i : ℝ) : ℂ)) := by
  refine isDensity_of_posSemidef _ ?_ ?_ ?_
  · intro s z
    have e : ∑ i ∈ s, ∑ j ∈ s, star (z i) * (Matrix.diagonal fun i => ((p i : ℝ) : ℂ)) i j * z j =
        ((∑ i ∈ s, p i * ‖z i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_eq_single i]
      · rw [Matrix.diagonal_apply_eq, Complex.star_def, mul_right_comm, Complex.conj_mul']
        ring
      · intro j _ hj
        rw [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
        simp
      · intro h
        exact absurd hi h
    rw [e]
    exact ⟨Complex.ofReal_im _, by
      rw [Complex.ofReal_re]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i).le (by positivity)⟩
  · simpa using hp1.summable
  · simpa using hp1.tsum_eq

/-! ### The weighted Hilbert–Schmidt bound -/

private lemma sqrt_mul_le_half (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ a / 2 + b / 2 := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_nonneg (a - b)]

private lemma weighted_term (x a b r : ℝ) (hx : 0 ≤ x) (hr : r ≤ a / 2 + b / 2) :
    x * r ≤ a / 2 * x + b / 2 * x := by
  nlinarith

/-- `∑_{i,j ∈ t} |Eᵢⱼ|² √(pᵢ pⱼ) ≤ ∑_{i ∈ t} pᵢ Eᵢᵢ`. -/
private lemma weighted_fin {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E) (p : I → ℝ)
    (hp : ∀ i, 0 < p i) (t : Finset I) :
    ∑ i ∈ t, ∑ j ∈ t, ‖E i j‖ ^ 2 * Real.sqrt (p i * p j) ≤ ∑ i ∈ t, p i * (E i i).re := by
  have hsym : ∀ i j, ‖E j i‖ = ‖E i j‖ := fun i j => by rw [eff_herm hE i j, norm_star]
  have h1 : ∑ i ∈ t, ∑ j ∈ t, ‖E i j‖ ^ 2 * Real.sqrt (p i * p j) ≤
      ∑ i ∈ t, ∑ j ∈ t, (p i / 2 * ‖E i j‖ ^ 2 + p j / 2 * ‖E j i‖ ^ 2) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    rw [hsym i j]
    exact weighted_term _ _ _ _ (by positivity) (sqrt_mul_le_half (p i) (p j) (hp i).le (hp j).le)
  have h2 : ∑ i ∈ t, ∑ j ∈ t, (p i / 2 * ‖E i j‖ ^ 2 + p j / 2 * ‖E j i‖ ^ 2) =
      ∑ i ∈ t, p i * ∑ j ∈ t, ‖E i j‖ ^ 2 := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => p j / 2 * ‖E j i‖ ^ 2), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h2] at h1
  exact h1.trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (row_sq_le hE i t) (hp i).le)

/-! ### Symmetry of density operators -/

private lemma dens_diag {A : Type} {X : Matrix A A ℂ} (hX : IsDensity X) (i : A) :
    (X i i).im = 0 ∧ 0 ≤ (X i i).re := by
  classical
  have h := hX.2.1 {i} (Pi.single i 1)
  simpa using h

private lemma dens_herm {A : Type} {X : Matrix A A ℂ} (hX : IsDensity X) (i j : A) :
    X j i = star (X i j) := by
  classical
  by_cases hij : i = j
  · subst hij
    exact (Complex.conj_eq_iff_im.mpr (dens_diag hX i).1).symm
  · have hji : j ≠ i := fun h => hij h.symm
    have hii := (dens_diag hX i).1
    have hjj := (dens_diag hX j).1
    have h1 := (hX.2.1 {i, j} (fun k => if k = i then 1 else if k = j then 1 else 0)).1
    have h2 := (hX.2.1 {i, j} (fun k => if k = i then 1 else if k = j then Complex.I else 0)).1
    simp [Finset.sum_pair hij, hji] at h1 h2
    apply Complex.ext
    · simp
      linarith
    · simp
      linarith

/-! ### The Born sum of the diagonal state -/

private lemma born_diag {I : Type} [DecidableEq I] {F : Matrix I I ℂ} (hF : EffB F) (p : I → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : HasSum p 1) :
    Summable (fun i => p i * (F i i).re) ∧
    (∑' i, ∑' j, F i j * (Matrix.diagonal fun i => ((p i : ℝ) : ℂ)) j i).re =
      ∑' i, p i * (F i i).re := by
  have hs : Summable (fun i => p i * (F i i).re) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hp i).le (eff_diag hF i).2.1)
      (fun i => by nlinarith [(eff_diag hF i).2.2, hp i]) hp1.summable
  refine ⟨hs, ?_⟩
  have e : ∀ i, ∑' j, F i j * (Matrix.diagonal fun i => ((p i : ℝ) : ℂ)) j i =
      ((p i * (F i i).re : ℝ) : ℂ) := by
    intro i
    rw [tsum_eq_single i]
    · rw [Matrix.diagonal_apply_eq]
      apply Complex.ext
      · simp [mul_comm]
      · simp [(eff_diag hF i).1]
    · intro j hj
      rw [Matrix.diagonal_apply_ne _ hj, mul_zero]
  simp only [e]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]

/-! ### Cauchy–Schwarz on `I × I` -/

private lemma cs_fin {I : Type} [DecidableEq I] {F : Matrix I I ℂ} (hF : EffB F)
    (ρ : Matrix I I ℂ) (hρ : IsDensity ρ) (p : I → ℝ) (hp : ∀ i, 0 < p i)
    (s : ℝ) (hs : ∀ t : Finset I, ∑ i ∈ t, p i * (F i i).re ≤ s)
    (q : ℝ) (hq : HasSum (fun x : I × I => ‖ρ x.1 x.2‖ ^ 2 / Real.sqrt (p x.1 * p x.2)) q)
    (u : Finset (I × I)) :
    ∑ x ∈ u, ‖F x.1 x.2 * ρ x.2 x.1‖ ≤ Real.sqrt s * Real.sqrt q := by
  set r : I × I → ℝ := fun x => Real.sqrt (Real.sqrt (p x.1 * p x.2)) with hr
  have hrpos : ∀ x, 0 < r x := fun x =>
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (mul_pos (hp x.1) (hp x.2)))
  have hr2 : ∀ x, r x ^ 2 = Real.sqrt (p x.1 * p x.2) := fun x => Real.sq_sqrt (Real.sqrt_nonneg _)
  have h1 : ∑ x ∈ u, ‖F x.1 x.2 * ρ x.2 x.1‖ =
      ∑ x ∈ u, (‖F x.1 x.2‖ * r x) * (‖ρ x.1 x.2‖ / r x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_mul, dens_herm hρ x.1 x.2, norm_star]
    have := (hrpos x).ne'
    field_simp
  rw [h1]
  refine (Real.sum_mul_le_sqrt_mul_sqrt u _ _).trans ?_
  have hA : ∑ x ∈ u, (‖F x.1 x.2‖ * r x) ^ 2 ≤ s := by
    set t : Finset I := u.image Prod.fst ∪ u.image Prod.snd with ht
    have hsub : u ⊆ t ×ˢ t := by
      intro x hx
      rw [Finset.mem_product]
      exact ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx),
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)⟩
    calc ∑ x ∈ u, (‖F x.1 x.2‖ * r x) ^ 2 ≤ ∑ x ∈ t ×ˢ t, (‖F x.1 x.2‖ * r x) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => by positivity
      _ = ∑ i ∈ t, ∑ j ∈ t, ‖F i j‖ ^ 2 * Real.sqrt (p i * p j) := by
          rw [Finset.sum_product]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [mul_pow, hr2]
      _ ≤ ∑ i ∈ t, p i * (F i i).re := weighted_fin hF p hp t
      _ ≤ s := hs t
  have hB : ∑ x ∈ u, (‖ρ x.1 x.2‖ / r x) ^ 2 ≤ q := by
    have e : ∀ x, (‖ρ x.1 x.2‖ / r x) ^ 2 = ‖ρ x.1 x.2‖ ^ 2 / Real.sqrt (p x.1 * p x.2) :=
      fun x => by rw [div_pow, hr2]
    simp only [e]
    exact sum_le_hasSum u (fun x _ => by positivity) hq
  exact mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

/-- The inequality for the Born sums. -/
private lemma born_bound {I : Type} [DecidableEq I] {F : Matrix I I ℂ} (hF : EffB F)
    (ρ : Matrix I I ℂ) (hρ : IsDensity ρ) (p : I → ℝ) (hp : ∀ i, 0 < p i) (hp1 : HasSum p 1)
    (q : ℝ) (hq : HasSum (fun x : I × I => ‖ρ x.1 x.2‖ ^ 2 / Real.sqrt (p x.1 * p x.2)) q) :
    (∑' i, ∑' j, F i j * ρ j i).re ^ 2 ≤
      (∑' i, ∑' j, F i j * (Matrix.diagonal fun i => ((p i : ℝ) : ℂ)) j i).re * q := by
  obtain ⟨hsum, hs⟩ := born_diag hF p hp hp1
  rw [hs]
  have hterm : ∀ i, 0 ≤ p i * (F i i).re := fun i => mul_nonneg (hp i).le (eff_diag hF i).2.1
  have hs0 : 0 ≤ ∑' i, p i * (F i i).re := tsum_nonneg hterm
  have hq0 : 0 ≤ q := hq.nonneg fun x => by positivity
  have hfin := cs_fin hF ρ hρ p hp _ (fun t => hsum.sum_le_tsum t fun i _ => hterm i) q hq
  have hnorm : Summable (fun x : I × I => ‖F x.1 x.2 * ρ x.2 x.1‖) :=
    summable_of_sum_le (fun x => norm_nonneg _) hfin
  have hS : Summable (fun x : I × I => F x.1 x.2 * ρ x.2 x.1) := hnorm.of_norm
  have e : ∑' i, ∑' j, F i j * ρ j i = ∑' x : I × I, F x.1 x.2 * ρ x.2 x.1 := hS.tsum_prod.symm
  rw [e]
  have h1 : |(∑' x : I × I, F x.1 x.2 * ρ x.2 x.1).re| ≤
      Real.sqrt (∑' i, p i * (F i i).re) * Real.sqrt q :=
    (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm hnorm).trans
      (Real.tsum_le_of_sum_le (fun x => norm_nonneg _) hfin))
  calc (∑' x : I × I, F x.1 x.2 * ρ x.2 x.1).re ^ 2
      = |(∑' x : I × I, F x.1 x.2 * ρ x.2 x.1).re| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt (∑' i, p i * (F i i).re) * Real.sqrt q) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = (∑' i, p i * (F i i).re) * q := by rw [mul_pow, Real.sq_sqrt hs0, Real.sq_sqrt hq0]

private lemma max_sq_le (t s q : ℝ) (hq : 0 ≤ q) (h : t ^ 2 ≤ s * q) :
    (max t 0) ^ 2 ≤ max s 0 * q := by
  have h2 : s * q ≤ max s 0 * q := mul_le_mul_of_nonneg_right (le_max_left _ _) hq
  rcases le_total t 0 with ht | ht
  · rw [max_eq_right ht]
    have : 0 ≤ max s 0 * q := mul_nonneg (le_max_right _ _) hq
    simpa using this
  · rw [max_eq_left ht]
    exact h.trans h2

/-! ### The statement -/

theorem solution {I O : Type} [DecidableEq I] [Countable I] [MeasurableSpace O]
    (E : FockPOVM I O) (ρ : Matrix I I ℂ) (hρ : IsDensity ρ)
    (p : I → ℝ) (hp : ∀ i, 0 < p i) (hp1 : HasSum p 1)
    (q : ℝ) (hq : HasSum (fun x : I × I => ‖ρ x.1 x.2‖ ^ 2 / Real.sqrt (p x.1 * p x.2)) q)
    (B : Set O) (hB : MeasurableSet B) :
    IsDensity (Matrix.diagonal fun i => ((p i : ℝ) : ℂ)) ∧
    (E.law ρ B).toReal ^ 2 ≤ (E.law (Matrix.diagonal fun i => ((p i : ℝ) : ℂ)) B).toReal * q := by
  have hσ := diag_density p hp hp1
  refine ⟨hσ, ?_⟩
  have hF : EffB (E.effect B) := E.effect_form B hB
  have hq0 : 0 ≤ q := hq.nonneg fun x => by positivity
  rw [E.law_born ρ hρ B hB, E.law_born _ hσ B hB, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  exact max_sq_le _ _ _ hq0 (born_bound hF ρ hρ p hp hp1 q hq)
