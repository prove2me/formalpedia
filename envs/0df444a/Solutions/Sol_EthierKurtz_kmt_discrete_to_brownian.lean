-- Prove2me | solution 1 for EthierKurtz.kmt_discrete_to_brownian
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T10:20:04.041094+00:00
-- url     : https://prove2.me/submissions/fb92cab8-c127-401d-a31b-14ad82db6590

import Mathlib
import Definitions.Def_EthierKurtz_kmtApproximation
import Definitions.Def_EthierKurtz_kmtDiscreteApproximation

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Peac1b43d

/-! ## Piece 3a: the Schauder kernel identity (elementary real analysis) -/

/-- tent on `[0,1]`, peak `1/2` at `1/2`, zero outside. -/
noncomputable def Lam (x : ℝ) : ℝ := max 0 (min x (1 - x))

lemma Lam_nonneg (x : ℝ) : 0 ≤ Lam x := le_max_left _ _

lemma Lam_le (x : ℝ) : Lam x ≤ 1 / 2 := by
  unfold Lam; simp only [min_def, max_def]; split_ifs <;> linarith

lemma Lam_of_nonpos {x : ℝ} (h : x ≤ 0) : Lam x = 0 := by
  unfold Lam; simp only [min_def, max_def]; split_ifs <;> linarith

lemma Lam_of_one_le {x : ℝ} (h : 1 ≤ x) : Lam x = 0 := by
  unfold Lam; simp only [min_def, max_def]; split_ifs <;> linarith

lemma Lam_continuous : Continuous Lam := by
  unfold Lam; fun_prop

noncomputable def lev (n : ℕ) (x y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), Lam (2 ^ n * x - k) * Lam (2 ^ n * y - k)

lemma lev_succ (n : ℕ) (x y : ℝ) :
    lev (n + 1) x y = lev n (2 * x) (2 * y) + lev n (2 * x - 1) (2 * y - 1) := by
  unfold lev
  rw [pow_succ, mul_two, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring_nf
  · refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring_nf

lemma lev_zero (x y : ℝ) : lev 0 x y = Lam x * Lam y := by
  simp [lev]

lemma lev_left_out {n : ℕ} {x : ℝ} (hx : x ≤ 0 ∨ 1 ≤ x) (y : ℝ) : lev n x y = 0 := by
  unfold lev
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' : (k : ℝ) + 1 ≤ 2 ^ n := by
    have := Finset.mem_range.1 hk
    exact_mod_cast this
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rcases hx with hx | hx
  · rw [Lam_of_nonpos (by nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]), zero_mul]
  · rw [Lam_of_one_le (by nlinarith), zero_mul]

lemma lev_symm (n : ℕ) (x y : ℝ) : lev n x y = lev n y x := by
  unfold lev; exact Finset.sum_congr rfl fun k _ => mul_comm _ _

lemma lev_right_out {n : ℕ} {y : ℝ} (hy : y ≤ 0 ∨ 1 ≤ y) (x : ℝ) : lev n x y = 0 := by
  rw [lev_symm]; exact lev_left_out hy x

noncomputable def Kn (N : ℕ) (x y : ℝ) : ℝ := ∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n * lev n x y

lemma Kn_succ (N : ℕ) (x y : ℝ) :
    Kn (N + 1) x y = Lam x * Lam y + 1 / 2 * Kn N (2 * x) (2 * y) +
      1 / 2 * Kn N (2 * x - 1) (2 * y - 1) := by
  unfold Kn
  rw [Finset.sum_range_succ', pow_zero, one_mul, lev_zero, Finset.mul_sum, Finset.mul_sum]
  have : ∀ n ∈ Finset.range N, (1 / 2 : ℝ) ^ (n + 1) * lev (n + 1) x y =
      1 / 2 * ((1 / 2) ^ n * lev n (2 * x) (2 * y)) +
        1 / 2 * ((1 / 2) ^ n * lev n (2 * x - 1) (2 * y - 1)) := by
    intro n _; rw [lev_succ, pow_succ]; ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]; ring

lemma Kn_left_out {N : ℕ} {x : ℝ} (hx : x ≤ 0 ∨ 1 ≤ x) (y : ℝ) : Kn N x y = 0 := by
  unfold Kn; exact Finset.sum_eq_zero fun n _ => by rw [lev_left_out hx, mul_zero]

/-- Brownian bridge covariance on `[0,1]^2`, zero outside. -/
noncomputable def Gb (x y : ℝ) : ℝ :=
  if 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 then min x y - x * y else 0

lemma Gb_left_out {x : ℝ} (hx : x ≤ 0 ∨ 1 ≤ x) (y : ℝ) : Gb x y = 0 := by
  unfold Gb
  split_ifs with h
  · obtain ⟨h1, h2, h3, h4⟩ := h
    rcases hx with hx | hx
    · have : x = 0 := le_antisymm hx h1
      subst this; simp [min_eq_left h3]
    · have : x = 1 := le_antisymm h2 hx
      subst this; simp [min_eq_right h4]
  · rfl

lemma Gb_bound (x y : ℝ) : |Gb x y| ≤ 1 := by
  unfold Gb
  split_ifs with h
  · obtain ⟨h1, h2, h3, h4⟩ := h
    rw [abs_le]; simp only [min_def]; split_ifs <;> constructor <;> nlinarith
  · simp

lemma Gb_symm (x y : ℝ) : Gb x y = Gb y x := by
  unfold Gb
  by_cases h : 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1
  · rw [if_pos h, if_pos ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩, min_comm, mul_comm]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.2.1, h'.2.2.2, h'.1, h'.2.1⟩)]

lemma Gb_right_out {y : ℝ} (hy : y ≤ 0 ∨ 1 ≤ y) (x : ℝ) : Gb x y = 0 := by
  rw [Gb_symm]; exact Gb_left_out hy x

lemma Gb_in {x y : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) (h3 : 0 ≤ y) (h4 : y ≤ 1) :
    Gb x y = min x y - x * y := if_pos ⟨h1, h2, h3, h4⟩

lemma Lam_lo {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1 / 2) : Lam x = x := by
  unfold Lam; rw [min_eq_left (by linarith), max_eq_right h1]

lemma Lam_hi {x : ℝ} (h1 : 1 / 2 ≤ x) (h2 : x ≤ 1) : Lam x = 1 - x := by
  unfold Lam; rw [min_eq_right (by linarith), max_eq_right (by linarith)]

lemma Gb_rec (x y : ℝ) :
    Gb x y = Lam x * Lam y + 1 / 2 * Gb (2 * x) (2 * y) + 1 / 2 * Gb (2 * x - 1) (2 * y - 1) := by
  by_cases hx : x ≤ 0 ∨ 1 ≤ x
  · rw [Gb_left_out hx, Gb_left_out (x := 2 * x) (by rcases hx with h | h <;> [left; right] <;> linarith),
      Gb_left_out (x := 2 * x - 1) (by rcases hx with h | h <;> [left; right] <;> linarith)]
    rcases hx with h | h
    · rw [Lam_of_nonpos h]; ring
    · rw [Lam_of_one_le h]; ring
  by_cases hy : y ≤ 0 ∨ 1 ≤ y
  · rw [Gb_right_out hy, Gb_right_out (y := 2 * y) (by rcases hy with h | h <;> [left; right] <;> linarith),
      Gb_right_out (y := 2 * y - 1) (by rcases hy with h | h <;> [left; right] <;> linarith)]
    rcases hy with h | h
    · rw [Lam_of_nonpos h]; ring
    · rw [Lam_of_one_le h]; ring
  push_neg at hx hy
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  rw [Gb_in hx0.le hx1.le hy0.le hy1.le]
  rcases le_total x (1 / 2) with hxh | hxh <;> rcases le_total y (1 / 2) with hyh | hyh
  · rw [Gb_left_out (x := 2 * x - 1) (Or.inl (by linarith)), Lam_lo hx0.le hxh, Lam_lo hy0.le hyh,
      Gb_in (by linarith) (by linarith) (by linarith) (by linarith)]
    rcases le_total x y with h | h
    · rw [min_eq_left h, min_eq_left (by linarith)]; ring
    · rw [min_eq_right h, min_eq_right (by linarith)]; ring
  · rw [Gb_left_out (x := 2 * x - 1) (Or.inl (by linarith)), Gb_right_out (y := 2 * y) (Or.inr (by linarith)),
      Lam_lo hx0.le hxh, Lam_hi hyh hy1.le, min_eq_left (by linarith)]; ring
  · rw [Gb_right_out (y := 2 * y - 1) (Or.inl (by linarith)), Gb_left_out (x := 2 * x) (Or.inr (by linarith)),
      Lam_hi hxh hx1.le, Lam_lo hy0.le hyh, min_eq_right (by linarith)]; ring
  · rw [Gb_left_out (x := 2 * x) (Or.inr (by linarith)), Lam_hi hxh hx1.le, Lam_hi hyh hy1.le,
      Gb_in (by linarith) (by linarith) (by linarith) (by linarith)]
    rcases le_total x y with h | h
    · rw [min_eq_left h, min_eq_left (by linarith)]; ring
    · rw [min_eq_right h, min_eq_right (by linarith)]; ring

lemma Kn_approx (N : ℕ) (x y : ℝ) : |Gb x y - Kn N x y| ≤ (1 / 2 : ℝ) ^ N := by
  induction N generalizing x y with
  | zero => simpa [Kn] using Gb_bound x y
  | succ N ih =>
    have e : Gb x y - Kn (N + 1) x y =
        1 / 2 * (Gb (2 * x) (2 * y) - Kn N (2 * x) (2 * y)) +
          1 / 2 * (Gb (2 * x - 1) (2 * y - 1) - Kn N (2 * x - 1) (2 * y - 1)) := by
      rw [Kn_succ, Gb_rec x y]; ring
    rw [e, pow_succ]
    rcases le_total x (1 / 2) with hx | hx
    · rw [Gb_left_out (x := 2 * x - 1) (Or.inl (by linarith)),
        Kn_left_out (x := 2 * x - 1) (Or.inl (by linarith))]
      have := ih (2 * x) (2 * y)
      rw [abs_le] at this ⊢; constructor <;> nlinarith [this.1, this.2]
    · rw [Gb_left_out (x := 2 * x) (Or.inr (by linarith)),
        Kn_left_out (x := 2 * x) (Or.inr (by linarith))]
      have := ih (2 * x - 1) (2 * y - 1)
      rw [abs_le] at this ⊢; constructor <;> nlinarith [this.1, this.2]

/-! ## Piece 3b: integer gluing identity -/

noncomputable def cl (j : ℕ) (t : ℝ≥0) : ℝ := min (max ((t : ℝ) - j) 0) 1

lemma cl_of_le {j : ℕ} {t : ℝ≥0} (h : (t : ℝ) ≤ j) : cl j t = 0 := by
  unfold cl
  rw [max_eq_right (by linarith)]
  norm_num

lemma cl_of_ge {j : ℕ} {t : ℝ≥0} (h : (j : ℝ) + 1 ≤ t) : cl j t = 1 := by
  unfold cl
  rw [max_eq_left (by linarith), min_eq_right (by linarith)]

lemma cl_of_mem {j : ℕ} {t : ℝ≥0} (h1 : (j : ℝ) ≤ t) (h2 : (t : ℝ) ≤ j + 1) :
    cl j t = (t : ℝ) - j := by
  unfold cl
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]

lemma cl_continuous (j : ℕ) : Continuous (cl j) := by
  unfold cl
  exact ((NNReal.continuous_coe.sub continuous_const).max continuous_const).min continuous_const

lemma min_sub_cl (a : ℝ≥0) (j : ℕ) : min (a : ℝ) ((j : ℝ) + 1) - min (a : ℝ) (j : ℝ) = cl j a := by
  unfold cl
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma sum_cl (a : ℝ≥0) (M : ℕ) : ∑ j ∈ Finset.range M, cl j a = min (a : ℝ) M := by
  have : ∀ j ∈ Finset.range M, cl j a = min (a : ℝ) ((j + 1 : ℕ) : ℝ) - min (a : ℝ) (j : ℝ) := by
    intro j _; rw [← min_sub_cl]; push_cast; ring
  rw [Finset.sum_congr rfl this, Finset.sum_range_sub (fun j : ℕ => min (a : ℝ) (j : ℝ))]
  simp [min_eq_right (NNReal.coe_nonneg a)]

lemma cl_mul_add_Gb_le (j : ℕ) {s t : ℝ≥0} (hst : s ≤ t) :
    cl j s * cl j t + Gb ((s : ℝ) - j) ((t : ℝ) - j) = cl j s := by
  have hst' : (s : ℝ) ≤ t := hst
  rcases le_total (s : ℝ) j with h0 | h0
  · rw [cl_of_le h0, Gb_left_out (Or.inl (by linarith))]; ring
  rcases le_total ((j : ℝ) + 1) s with h1 | h1
  · rw [cl_of_ge h1, cl_of_ge (by linarith), Gb_left_out (Or.inr (by linarith))]; ring
  rw [cl_of_mem h0 h1]
  rcases le_total ((j : ℝ) + 1) t with h2 | h2
  · rw [cl_of_ge h2, Gb_right_out (Or.inr (by linarith))]; ring
  · rw [cl_of_mem (by linarith) h2, Gb_in (by linarith) (by linarith) (by linarith) (by linarith),
      min_eq_left (by linarith)]; ring

lemma cl_mul_add_Gb (j : ℕ) (s t : ℝ≥0) :
    cl j s * cl j t + Gb ((s : ℝ) - j) ((t : ℝ) - j) = cl j (min s t) := by
  rcases le_total s t with h | h
  · rw [min_eq_left h, cl_mul_add_Gb_le j h]
  · rw [min_eq_right h, mul_comm, Gb_symm, cl_mul_add_Gb_le j h]

lemma glue_identity {M : ℕ} {s t : ℝ≥0} (hs : (s : ℝ) ≤ M) (ht : (t : ℝ) ≤ M) :
    ∑ j ∈ Finset.range M, (cl j s * cl j t + Gb ((s : ℝ) - j) ((t : ℝ) - j)) = min (s : ℝ) t := by
  simp_rw [cl_mul_add_Gb]
  rw [sum_cl, NNReal.coe_min, min_eq_left (le_trans (min_le_left _ _) hs)]

/-! ## Piece 3c: the Gaussian family and the partial-sum processes -/

abbrev IX := ℕ × Option (ℕ × ℕ)
abbrev OM := IX → ℝ

noncomputable def mu : Measure OM := Measure.infinitePi (fun _ : IX => gaussianReal 0 1)

instance : IsProbabilityMeasure mu := by unfold mu; infer_instance

lemma xi_indep : iIndepFun (fun (i : IX) (ω : OM) => ω i) mu :=
  iIndepFun_infinitePi (P := fun _ : IX => gaussianReal 0 1) (X := fun _ => id)
    (fun _ => measurable_id)

lemma xi_law (i : IX) : HasLaw (fun ω : OM => ω i) (gaussianReal 0 1) mu :=
  ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩

lemma xi_gp : IsGaussianProcess (fun (i : IX) (ω : OM) => ω i) mu := by
  refine ⟨fun I => ?_⟩
  have hind := xi_indep.precomp (Subtype.val_injective (p := fun i => i ∈ I))
  exact iIndepFun.hasGaussianLaw (fun i => (xi_law i.1).hasGaussianLaw) hind

lemma xi_memLp (i : IX) : MemLp (fun ω : OM => ω i) 2 mu := (xi_law i).hasGaussianLaw.memLp_two

lemma xi_cov (i i' : IX) :
    cov[fun ω : OM => ω i, fun ω : OM => ω i'; mu] = if i = i' then 1 else 0 := by
  split_ifs with h
  · subst h
    rw [covariance_self (xi_memLp i).aemeasurable, (xi_law i).variance_eq, variance_id_gaussianReal]
    simp
  · exact (xi_indep.indepFun h).covariance_eq_zero (xi_memLp i) (xi_memLp i')

lemma lin_cov (S : Finset IX) (a b : IX → ℝ) :
    cov[fun ω : OM => ∑ i ∈ S, a i * ω i, fun ω : OM => ∑ i ∈ S, b i * ω i; mu] =
      ∑ i ∈ S, a i * b i := by
  rw [covariance_fun_sum_fun_sum' (X := fun i (ω : OM) => a i * ω i) (Y := fun i (ω : OM) => b i * ω i)
    (fun i _ => (xi_memLp i).const_mul _) (fun i _ => (xi_memLp i).const_mul _)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, xi_cov]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [if_neg (Ne.symm hji)]; ring)
    (fun h => absurd hi h), if_pos rfl]
  ring

lemma lin_integral (S : Finset IX) (a : IX → ℝ) : ∫ ω, ∑ i ∈ S, a i * ω i ∂mu = 0 := by
  rw [integral_finsetSum _ fun i _ => ((xi_memLp i).integrable one_le_two).const_mul _]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul, (xi_law i).integral_eq, integral_id_gaussianReal, mul_zero]

lemma lin_law (S : Finset IX) (a : IX → ℝ) :
    HasLaw (fun ω : OM => ∑ i ∈ S, a i * ω i) (gaussianReal 0 (∑ i ∈ S, a i * a i).toNNReal) mu := by
  have hG : HasGaussianLaw (fun ω : OM => ∑ i ∈ S, a i * ω i) mu :=
    (xi_gp.smul a).hasGaussianLaw_fun_sum (I := S)
  refine ⟨hG.aemeasurable, ?_⟩
  rw [hG.map_eq_gaussianReal, lin_integral, ← covariance_self hG.aemeasurable, lin_cov]

noncomputable def sq (n : ℕ) : ℝ := Real.sqrt (1 / 2 : ℝ) ^ n

lemma sq_mul_sq (n : ℕ) : sq n * sq n = (1 / 2 : ℝ) ^ n := by
  unfold sq; rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]

lemma sq_nonneg' (n : ℕ) : 0 ≤ sq n := by unfold sq; positivity

noncomputable def coef (i : IX) (t : ℝ≥0) : ℝ :=
  match i.2 with
  | none => cl i.1 t
  | some p => sq p.1 * Lam (2 ^ p.1 * ((t : ℝ) - i.1) - p.2)

def Tn (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range N ×ˢ Finset.range (2 ^ N)).filter (fun p => p.2 < 2 ^ p.1)

lemma mem_Tn {N : ℕ} (p : ℕ × ℕ) :
    p ∈ Tn N ↔ p.1 ∈ Finset.range N ∧ p.2 ∈ Finset.range (2 ^ p.1) := by
  simp only [Tn, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨⟨h1, lt_of_lt_of_le h3 (Nat.pow_le_pow_right (by norm_num) h1.le)⟩, h3⟩

def Sn (N M : ℕ) : Finset IX := Finset.range M ×ˢ insert none ((Tn N).image some)

lemma sum_Sn (N M : ℕ) (f : IX → ℝ) :
    ∑ i ∈ Sn N M, f i = ∑ j ∈ Finset.range M,
      (f (j, none) + ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (2 ^ n), f (j, some (n, k))) := by
  unfold Sn
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_insert (by simp), Finset.sum_image (fun _ _ _ _ h => Option.some_injective _ h),
    Finset.sum_finset_product (Tn N) (Finset.range N) (fun n => Finset.range (2 ^ n)) mem_Tn]

/-- partial-sum process -/
noncomputable def Bp (N M : ℕ) (t : ℝ≥0) (ω : OM) : ℝ := ∑ i ∈ Sn N M, coef i t * ω i

lemma tent_sum (N j : ℕ) (s t : ℝ≥0) :
    ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (2 ^ n),
      coef (j, some (n, k)) s * coef (j, some (n, k)) t = Kn N ((s : ℝ) - j) ((t : ℝ) - j) := by
  unfold Kn lev
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum, ← sq_mul_sq]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [coef]
  ring

lemma Bp_cov (N M : ℕ) (s t : ℝ≥0) :
    cov[Bp N M s, Bp N M t; mu] =
      ∑ j ∈ Finset.range M, (cl j s * cl j t + Kn N ((s : ℝ) - j) ((t : ℝ) - j)) := by
  unfold Bp
  rw [lin_cov, sum_Sn]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tent_sum]
  rfl

lemma Kn_tendsto (x y : ℝ) : Filter.Tendsto (fun N => Kn N x y) Filter.atTop (nhds (Gb x y)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact Kn_approx N x y

lemma Bp_cov_tendsto {M : ℕ} {s t : ℝ≥0} (hs : (s : ℝ) ≤ M) (ht : (t : ℝ) ≤ M) :
    Filter.Tendsto (fun N => cov[Bp N M s, Bp N M t; mu]) Filter.atTop (nhds (min (s : ℝ) t)) := by
  simp_rw [Bp_cov]
  rw [← glue_identity hs ht]
  exact tendsto_finset_sum _ fun j _ => tendsto_const_nhds.add (Kn_tendsto _ _)

/-! ## Piece 3d: the good set has full measure -/

lemma gauss_tail (a : ℝ) :
    gaussianReal 0 1 {x : ℝ | a < |x|} ≤ ENNReal.ofReal (2 * Real.exp (1 / 2) * Real.exp (-a)) := by
  have hm1 : mgf (fun x : ℝ => x) (gaussianReal 0 1) 1 = Real.exp (1 / 2) := by
    rw [mgf_fun_id_gaussianReal]; norm_num
  have hm2 : mgf (fun x : ℝ => x) (gaussianReal 0 1) (-1) = Real.exp (1 / 2) := by
    rw [mgf_fun_id_gaussianReal]; norm_num
  have hA := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := fun x : ℝ => x) (t := 1) a
    zero_le_one (integrable_exp_mul_gaussianReal 1)
  have hB := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := fun x : ℝ => x) (t := -1) (-a)
    (by norm_num) (integrable_exp_mul_gaussianReal (-1))
  rw [hm1] at hA
  rw [hm2] at hB
  have hsub : {x : ℝ | a < |x|} ⊆ {x | a ≤ x} ∪ {x | x ≤ -a} := by
    intro x (hx : a < |x|)
    rcases lt_abs.1 hx with h | h
    · left; exact h.le
    · right; show x ≤ -a; linarith
  calc gaussianReal 0 1 {x : ℝ | a < |x|}
      ≤ gaussianReal 0 1 {x | a ≤ x} + gaussianReal 0 1 {x | x ≤ -a} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = ENNReal.ofReal ((gaussianReal 0 1).real {x | a ≤ x}) +
          ENNReal.ofReal ((gaussianReal 0 1).real {x | x ≤ -a}) := by
        simp only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (Real.exp (-1 * a) * Real.exp (1 / 2)) +
          ENNReal.ofReal (Real.exp (-(-1) * (-a)) * Real.exp (1 / 2)) :=
        add_le_add (ENNReal.ofReal_le_ofReal hA) (ENNReal.ofReal_le_ofReal hB)
    _ = ENNReal.ofReal (2 * Real.exp (1 / 2) * Real.exp (-a)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring_nf

lemma coord_tail (i : IX) (a : ℝ) :
    mu {ω : OM | a < |ω i|} ≤ ENNReal.ofReal (2 * Real.exp (1 / 2) * Real.exp (-a)) := by
  have hS : MeasurableSet {x : ℝ | a < |x|} := measurableSet_lt measurable_const continuous_abs.measurable
  have : mu {ω : OM | a < |ω i|} = gaussianReal 0 1 {x : ℝ | a < |x|} := by
    rw [← (xi_law i).map_eq, Measure.map_apply (measurable_pi_apply i) hS]; rfl
  rw [this]; exact gauss_tail a

/-- bad event at block `j`, level `n` -/
def Ev (j n : ℕ) : Set OM :=
  ⋃ k ∈ Finset.range (2 ^ n), {ω : OM | (n : ℝ) + 1 < |ω (j, some (n, k))|}

noncomputable def bnd (n : ℕ) : ℝ := 2 ^ n * (2 * Real.exp (1 / 2) * Real.exp (-((n : ℝ) + 1)))

lemma bnd_nonneg (n : ℕ) : 0 ≤ bnd n := by unfold bnd; positivity

lemma bnd_eq (n : ℕ) : bnd n = (2 * Real.exp (1 / 2) * Real.exp (-1)) * (2 * Real.exp (-1)) ^ n := by
  unfold bnd
  rw [show -((n : ℝ) + 1) = -1 + n * (-1) by ring, Real.exp_add, Real.exp_nat_mul, mul_pow]
  ring

lemma bnd_summable : Summable bnd := by
  have h1 : 2 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hr : 2 * Real.exp (-1) < 1 := by
    rw [Real.exp_neg]
    calc 2 * (Real.exp 1)⁻¹ < Real.exp 1 * (Real.exp 1)⁻¹ := by
          gcongr
      _ = 1 := mul_inv_cancel₀ (Real.exp_pos 1).ne'
  have := (summable_geometric_of_lt_one (by positivity) hr).mul_left
    (2 * Real.exp (1 / 2) * Real.exp (-1))
  simpa only [← bnd_eq] using this

lemma Ev_le (j n : ℕ) : mu (Ev j n) ≤ ENNReal.ofReal (bnd n) := by
  unfold Ev
  calc mu (⋃ k ∈ Finset.range (2 ^ n), {ω : OM | (n : ℝ) + 1 < |ω (j, some (n, k))|})
      ≤ ∑ k ∈ Finset.range (2 ^ n), mu {ω : OM | (n : ℝ) + 1 < |ω (j, some (n, k))|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.range (2 ^ n),
          ENNReal.ofReal (2 * Real.exp (1 / 2) * Real.exp (-((n : ℝ) + 1))) :=
        Finset.sum_le_sum fun k _ => coord_tail _ _
    _ = ENNReal.ofReal (∑ k ∈ Finset.range (2 ^ n),
          (2 * Real.exp (1 / 2) * Real.exp (-((n : ℝ) + 1)))) :=
        (ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity).symm
    _ = ENNReal.ofReal (bnd n) := by simp [bnd]

lemma Ev_tsum_ne_top (j : ℕ) : ∑' n, mu (Ev j n) ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n => Ev_le j n)
  rw [← ENNReal.ofReal_tsum_of_nonneg bnd_nonneg bnd_summable]
  exact ENNReal.ofReal_ne_top

def good (ω : OM) : Prop :=
  ∀ j : ℕ, ∃ C : ℕ, ∀ n k : ℕ, k < 2 ^ n → |ω (j, some (n, k))| ≤ C * ((n : ℝ) + 1)

lemma measurableSet_good : MeasurableSet {ω : OM | good ω} := by
  simp only [good, Set.setOf_forall, Set.setOf_exists]
  refine MeasurableSet.iInter fun j => MeasurableSet.iUnion fun C => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply _)) measurable_const

lemma ae_good : ∀ᵐ ω ∂mu, good ω := by
  have h : ∀ᵐ ω ∂mu, ∀ j : ℕ, ∀ᶠ n in Filter.atTop, ω ∉ Ev j n :=
    ae_all_iff.2 fun j => ae_eventually_notMem (Ev_tsum_ne_top j)
  filter_upwards [h] with ω hω
  intro j
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 (hω j)
  set T : ℝ := ∑ n ∈ Finset.range N0, ∑ k ∈ Finset.range (2 ^ n), |ω (j, some (n, k))| with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨⌈1 + T⌉₊, fun n k hk => ?_⟩
  have hC : 1 + T ≤ (⌈1 + T⌉₊ : ℝ) := Nat.le_ceil _
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rcases lt_or_ge n N0 with hn | hn
  · have h1 : |ω (j, some (n, k))| ≤ ∑ k' ∈ Finset.range (2 ^ n), |ω (j, some (n, k'))| :=
      Finset.single_le_sum (f := fun k' => |ω (j, some (n, k'))|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 hk)
    have h2 : ∑ k' ∈ Finset.range (2 ^ n), |ω (j, some (n, k'))| ≤ T :=
      Finset.single_le_sum (f := fun n' => ∑ k' ∈ Finset.range (2 ^ n'), |ω (j, some (n', k'))|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_range.2 hn)
    nlinarith
  · have hnot := hN0 n hn
    simp only [Ev, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt] at hnot
    have := hnot k (Finset.mem_range.2 hk)
    nlinarith

/-! ## Piece 3e: the limit process `Bf` -/

noncomputable def Fl (j n : ℕ) (ω : OM) (t : ℝ≥0) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), coef (j, some (n, k)) t * ω (j, some (n, k))

lemma Lam_ne_zero {z : ℝ} (h : Lam z ≠ 0) : 0 < z ∧ z < 1 := by
  by_contra hc
  rw [not_and_or, not_lt, not_lt] at hc
  rcases hc with hc | hc
  · exact h (Lam_of_nonpos hc)
  · exact h (Lam_of_one_le hc)

lemma Fl_bound (j n : ℕ) (ω : OM) (C : ℝ) (hC : ∀ k, k < 2 ^ n → |ω (j, some (n, k))| ≤ C)
    (t : ℝ≥0) : |Fl j n ω t| ≤ sq n * (1 / 2) * C := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 (by positivity))
  have hsq := sq_nonneg' n
  by_cases hex : ∃ k ∈ Finset.range (2 ^ n), Lam (2 ^ n * ((t : ℝ) - j) - k) ≠ 0
  · obtain ⟨k0, hk0, hne⟩ := hex
    unfold Fl
    rw [Finset.sum_eq_single k0]
    · simp only [coef]
      rw [abs_mul, abs_mul, abs_of_nonneg hsq, abs_of_nonneg (Lam_nonneg _)]
      have := hC k0 (Finset.mem_range.1 hk0)
      have hL := Lam_le (2 ^ n * ((t : ℝ) - j) - k0)
      have hL0 := Lam_nonneg (2 ^ n * ((t : ℝ) - j) - k0)
      calc sq n * Lam (2 ^ n * ((t : ℝ) - j) - k0) * |ω (j, some (n, k0))|
          ≤ sq n * (1 / 2) * |ω (j, some (n, k0))| := by gcongr
        _ ≤ sq n * (1 / 2) * C := by gcongr
    · intro k _ hk
      simp only [coef]
      by_cases hz : Lam (2 ^ n * ((t : ℝ) - j) - k) = 0
      · rw [hz]; ring
      · exfalso
        obtain ⟨a1, a2⟩ := Lam_ne_zero hz
        obtain ⟨b1, b2⟩ := Lam_ne_zero hne
        have e1 : (k : ℝ) < k0 + 1 := by linarith
        have e2 : (k0 : ℝ) < k + 1 := by linarith
        have e1' : k < k0 + 1 := by exact_mod_cast e1
        have e2' : k0 < k + 1 := by exact_mod_cast e2
        exact hk (by omega)
    · intro h; exact absurd hk0 h
  · push_neg at hex
    have : Fl j n ω t = 0 := by
      unfold Fl
      refine Finset.sum_eq_zero fun k hk => ?_
      simp only [coef]; rw [hex k hk]; ring
    rw [this, abs_zero]; positivity

lemma Fl_continuous (j n : ℕ) (ω : OM) : Continuous (Fl j n ω) := by
  unfold Fl coef
  refine continuous_finsetSum _ fun k _ => ?_
  exact (continuous_const.mul (Lam_continuous.comp (by fun_prop))).mul continuous_const

lemma Fl_of_le {j : ℕ} {t : ℝ≥0} (h : (t : ℝ) ≤ j) (n : ℕ) (ω : OM) : Fl j n ω t = 0 := by
  unfold Fl
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [coef]
  rw [Lam_of_nonpos (by
    have : (2 : ℝ) ^ n * ((t : ℝ) - j) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])]
  ring

noncomputable def ubd (C : ℝ) (n : ℕ) : ℝ := sq n * (1 / 2) * (C * ((n : ℝ) + 1))

lemma ubd_summable (C : ℝ) : Summable (ubd C) := by
  have hr : ‖Real.sqrt (1 / 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_lt' one_pos]; norm_num
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h0 := summable_geometric_of_norm_lt_one hr
  have := (h1.add h0).mul_left (C / 2)
  refine this.congr fun n => ?_
  simp only [ubd, sq, pow_one]
  ring

lemma Fl_summable_bound {ω : OM} (hω : good ω) (j : ℕ) :
    ∃ C : ℝ, ∀ n t, ‖Fl j n ω t‖ ≤ ubd C n := by
  obtain ⟨C, hC⟩ := hω j
  exact ⟨C, fun n t => by
    rw [Real.norm_eq_abs]
    exact Fl_bound j n ω _ (fun k hk => hC n k hk) t⟩

lemma Fl_summable {ω : OM} (hω : good ω) (j : ℕ) (t : ℝ≥0) : Summable (fun n => Fl j n ω t) := by
  obtain ⟨C, hC⟩ := Fl_summable_bound hω j
  exact Summable.of_norm_bounded (ubd_summable C) fun n => hC n t

noncomputable def Bfin (ω : OM) (M : ℕ) (t : ℝ≥0) : ℝ :=
  ∑ j ∈ Finset.range M, (cl j t * ω (j, none) + ∑' n, Fl j n ω t)

open Classical in
noncomputable def Bf (t : ℝ≥0) (ω : OM) : ℝ := if good ω then Bfin ω (⌊t⌋₊ + 1) t else 0

lemma Bfin_mono (ω : OM) {N M : ℕ} {t : ℝ≥0} (ht : (t : ℝ) ≤ N) (hNM : N ≤ M) :
    Bfin ω N t = Bfin ω M t := by
  unfold Bfin
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro j _ hjN
  have hj : (t : ℝ) ≤ j := by
    have : N ≤ j := by simpa using hjN
    have : (N : ℝ) ≤ j := by exact_mod_cast this
    linarith
  simp only [cl_of_le hj, Fl_of_le hj, zero_mul, tsum_zero, add_zero]

lemma floor_le_succ' (t : ℝ≥0) : (t : ℝ) ≤ ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by
  have := Nat.lt_floor_add_one t
  have : (t : ℝ) < ((⌊t⌋₊ : ℝ≥0) : ℝ) + 1 := by exact_mod_cast this
  push_cast
  simpa using this.le

lemma Bfin_eq (ω : OM) {M : ℕ} {t : ℝ≥0} (ht : (t : ℝ) ≤ M) :
    Bfin ω (⌊t⌋₊ + 1) t = Bfin ω M t := by
  rw [Bfin_mono ω (floor_le_succ' t) (le_max_left _ M), ← Bfin_mono ω ht (le_max_right _ M)]

lemma Bfin_continuous {ω : OM} (hω : good ω) (M : ℕ) : Continuous (Bfin ω M) := by
  unfold Bfin
  refine continuous_finsetSum _ fun j _ => ?_
  refine ((cl_continuous j).mul continuous_const).add ?_
  obtain ⟨C, hC⟩ := Fl_summable_bound hω j
  exact continuous_tsum (fun n => Fl_continuous j n ω) (ubd_summable C) hC

lemma Bf_continuous (ω : OM) : Continuous (fun t => Bf t ω) := by
  by_cases hω : good ω
  · simp only [Bf, if_pos hω]
    rw [continuous_iff_continuousAt]
    intro t0
    set N : ℕ := ⌊t0⌋₊ + 1
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ) < N} := isOpen_lt NNReal.continuous_coe continuous_const
    have hmem : t0 ∈ {t : ℝ≥0 | (t : ℝ) < N} := by
      have := Nat.lt_floor_add_one t0
      show (t0 : ℝ) < ((⌊t0⌋₊ + 1 : ℕ) : ℝ)
      push_cast
      exact_mod_cast this
    refine ((Bfin_continuous hω N).continuousAt).congr ?_
    filter_upwards [hopen.mem_nhds hmem] with t ht
    exact (Bfin_eq ω (le_of_lt ht)).symm
  · simp only [Bf, if_neg hω]
    exact continuous_const

lemma Bp_eq (N M : ℕ) (t : ℝ≥0) (ω : OM) :
    Bp N M t ω = ∑ j ∈ Finset.range M,
      (cl j t * ω (j, none) + ∑ n ∈ Finset.range N, Fl j n ω t) := by
  unfold Bp
  rw [sum_Sn]
  rfl

lemma Bp_tendsto {ω : OM} (hω : good ω) (M : ℕ) (t : ℝ≥0) :
    Filter.Tendsto (fun N => Bp N M t ω) Filter.atTop (nhds (Bfin ω M t)) := by
  simp_rw [Bp_eq]
  exact tendsto_finset_sum _ fun j _ =>
    tendsto_const_nhds.add (Fl_summable hω j t).hasSum.tendsto_sum_nat

lemma measurable_Bp (N M : ℕ) (t : ℝ≥0) : Measurable (Bp N M t) := by
  unfold Bp
  exact Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)

open Classical in
lemma measurable_Bf (t : ℝ≥0) : Measurable (Bf t) := by
  refine measurable_of_tendsto_metrizable (f := fun N ω => if good ω then Bp N (⌊t⌋₊ + 1) t ω else 0)
    (fun N => Measurable.ite measurableSet_good (measurable_Bp _ _ _) measurable_const) ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : good ω
  · simp only [Bf, if_pos hω]
    exact Bp_tendsto hω _ t
  · simp only [Bf, if_neg hω]
    exact tendsto_const_nhds

/-! ## Piece 3f: Gaussian limits and the Brownian law of `Bf` -/

lemma gauss_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} {v : ℕ → ℝ≥0} {w : ℝ≥0}
    (hX : ∀ N, HasLaw (X N) (gaussianReal 0 (v N)) P) (hY : AEMeasurable Y P)
    (hlim : ∀ᵐ ω ∂P, Filter.Tendsto (fun N => X N ω) Filter.atTop (nhds (Y ω)))
    (hv : Filter.Tendsto v Filter.atTop (nhds w)) :
    HasLaw Y (gaussianReal 0 w) P := by
  refine ⟨hY, ?_⟩
  have : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY
  refine Measure.ext_of_charFun (funext fun u => ?_)
  have hf : Continuous (fun x : ℝ => Complex.exp ((inner ℝ x u : ℝ) * Complex.I)) := by fun_prop
  have hc : ∀ Z : Ω → ℝ, AEMeasurable Z P →
      charFun (P.map Z) u = ∫ ω, Complex.exp ((inner ℝ (Z ω) u : ℝ) * Complex.I) ∂P := by
    intro Z hZ
    rw [charFun_apply, integral_map hZ hf.aestronglyMeasurable]
  have h1 : Filter.Tendsto (fun N => charFun (P.map (X N)) u) Filter.atTop
      (nhds (charFun (P.map Y) u)) := by
    rw [hc Y hY]
    have e : (fun N => charFun (P.map (X N)) u) =
        fun N => ∫ ω, Complex.exp ((inner ℝ (X N ω) u : ℝ) * Complex.I) ∂P :=
      funext fun N => hc _ (hX N).aemeasurable
    rw [e]
    refine tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun N => (hf.measurable.comp_aemeasurable (hX N).aemeasurable).aestronglyMeasurable)
      (integrable_const 1) (fun N => ae_of_all _ fun ω => (Complex.norm_exp_ofReal_mul_I _).le) ?_
    filter_upwards [hlim] with ω hω
    exact (hf.tendsto _).comp hω
  have h2 : Filter.Tendsto (fun N => charFun (P.map (X N)) u) Filter.atTop
      (nhds (charFun (gaussianReal 0 w) u)) := by
    have e : (fun N => charFun (P.map (X N)) u) = fun N => charFun (gaussianReal 0 (v N)) u :=
      funext fun N => by rw [(hX N).map_eq]
    rw [e]
    have hg : Continuous (fun r : ℝ≥0 => charFun (gaussianReal 0 r) u) := by
      simp only [charFun_gaussianReal]
      fun_prop
    exact (hg.tendsto w).comp hv
  exact tendsto_nhds_unique h1 h2

lemma cov_raw (N M : ℕ) (s t : ℝ≥0) :
    cov[Bp N M s, Bp N M t; mu] = ∑ i ∈ Sn N M, coef i s * coef i t := by
  unfold Bp; exact lin_cov _ _ _

lemma CL {κ : Type*} [Fintype κ] (τ : κ → ℝ≥0) (u : κ → ℝ) :
    HasLaw (fun ω => ∑ a, u a * Bf (τ a) ω)
      (gaussianReal 0 (∑ a, ∑ b, u a * u b * min (τ a : ℝ) (τ b)).toNNReal) mu := by
  set M : ℕ := ⌊∑ a, τ a⌋₊ + 1 with hM
  have hτM : ∀ a, (τ a : ℝ) ≤ M := by
    intro a
    have h1 : τ a ≤ ∑ b, τ b := Finset.single_le_sum (fun b _ => zero_le) (Finset.mem_univ a)
    have h2 : ((τ a : ℝ≥0) : ℝ) ≤ ((∑ b, τ b : ℝ≥0) : ℝ) := by exact_mod_cast h1
    exact le_trans h2 (floor_le_succ' _)
  set c : IX → ℝ := fun i => ∑ a, u a * coef i (τ a) with hc
  have hX : ∀ N, (fun ω => ∑ a, u a * Bp N M (τ a) ω) = fun ω => ∑ i ∈ Sn N M, c i * ω i := by
    intro N; funext ω
    simp only [Bp, hc, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  have hquad : ∀ N, ∑ i ∈ Sn N M, c i * c i =
      ∑ a, ∑ b, u a * u b * cov[Bp N M (τ a), Bp N M (τ b); mu] := by
    intro N
    simp only [hc, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [cov_raw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hlimv : Filter.Tendsto (fun N => ∑ i ∈ Sn N M, c i * c i) Filter.atTop
      (nhds (∑ a, ∑ b, u a * u b * min (τ a : ℝ) (τ b))) := by
    simp_rw [hquad]
    exact tendsto_finset_sum _ fun a _ => tendsto_finset_sum _ fun b _ =>
      (Bp_cov_tendsto (hτM a) (hτM b)).const_mul _
  refine gauss_limit (X := fun N ω => ∑ a, u a * Bp N M (τ a) ω)
    (v := fun N => (∑ i ∈ Sn N M, c i * c i).toNNReal) (fun N => ?_)
    (Finset.measurable_sum _ fun a _ => measurable_const.mul (measurable_Bf _)).aemeasurable ?_
    ((continuous_real_toNNReal.tendsto _).comp hlimv)
  · rw [hX N]; exact lin_law _ _
  · filter_upwards [ae_good] with ω hω
    have hB : ∀ a, Bf (τ a) ω = Bfin ω M (τ a) := fun a => by
      simp only [Bf, if_pos hω]; exact Bfin_eq ω (hτM a)
    have e : (∑ a, u a * Bf (τ a) ω) = ∑ a, u a * Bfin ω M (τ a) :=
      Finset.sum_congr rfl fun a _ => by rw [hB a]
    rw [e]
    exact tendsto_finset_sum _ fun a _ => (Bp_tendsto hω M (τ a)).const_mul (u a)

lemma Bf_law1 (t : ℝ≥0) : HasLaw (Bf t) (gaussianReal 0 (t : ℝ).toNNReal) mu := by
  have h := CL (κ := Unit) (fun _ => t) (fun _ => 1)
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, min_self] at h
  exact h

lemma Bf_law2 (s t : ℝ≥0) :
    HasLaw (Bf s + Bf t) (gaussianReal 0 ((s : ℝ) + t + 2 * min (s : ℝ) t).toNNReal) mu := by
  have h := CL (κ := Fin 2) ![s, t] ![1, 1]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
    min_self] at h
  have e : (s : ℝ) + min (s : ℝ) t + (min (t : ℝ) s + t) = (s : ℝ) + t + 2 * min (s : ℝ) t := by
    rw [min_comm (t : ℝ) s]; ring
  rw [e] at h
  exact h

lemma Bf_memLp (t : ℝ≥0) : MemLp (Bf t) 2 mu := (Bf_law1 t).hasGaussianLaw.memLp_two

lemma Bf_var1 (t : ℝ≥0) : Var[Bf t; mu] = t := by
  rw [(Bf_law1 t).variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ (NNReal.coe_nonneg t)]

lemma Bf_brownian : IsBrownianReal Bf mu := by
  refine ⟨IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t => ?_) (fun s t hst => ?_),
    ae_of_all _ fun ω => Bf_continuous ω⟩
  · refine ⟨fun I => ⟨?_⟩⟩
    have hBI : Measurable (fun ω => I.restrict (fun t => Bf t ω)) :=
      measurable_pi_lambda _ fun a => measurable_Bf a
    refine isGaussian_of_map_eq_gaussianReal fun L => ⟨0, (∑ a : I, ∑ b : I,
      L (fun j => if a = j then 1 else 0) * L (fun j => if b = j then 1 else 0) *
        min ((a : ℝ≥0) : ℝ) ((b : ℝ≥0) : ℝ)).toNNReal, ?_⟩
    rw [Measure.map_map L.continuous.measurable hBI]
    have e : (L ∘ fun ω => I.restrict (fun t => Bf t ω)) =
        fun ω => ∑ a : I, L (fun j => if a = j then 1 else 0) * Bf a.1 ω := by
      funext ω
      simp only [Function.comp_apply]
      rw [show L (I.restrict (fun t => Bf t ω)) = L.toLinearMap (I.restrict (fun t => Bf t ω)) from rfl,
        LinearMap.pi_apply_eq_sum_univ]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Finset.restrict, smul_eq_mul, ContinuousLinearMap.coe_coe]
      ring
    rw [e]
    exact (CL (κ := I) (fun a => a.1) (fun a => L (fun j => if a = j then 1 else 0))).map_eq
  · rw [(Bf_law1 t).integral_eq, integral_id_gaussianReal]
  · have h2 := Bf_law2 s t
    have hv2 : Var[Bf s + Bf t; mu] = (s : ℝ) + t + 2 * min (s : ℝ) t := by
      rw [h2.variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ (by positivity)]
    rw [variance_add (Bf_memLp s) (Bf_memLp t), Bf_var1, Bf_var1] at hv2
    have hmin : min (s : ℝ) t = s := min_eq_left (by exact_mod_cast hst)
    linarith

abbrev CP := {b : ℝ≥0 → ℝ // Continuous b}

noncomputable def Bmap (ω : OM) : CP := ⟨fun t => Bf t ω, Bf_continuous ω⟩

lemma measurable_Bmap : Measurable Bmap :=
  Measurable.subtype_mk (measurable_pi_lambda _ fun t => measurable_Bf t)

theorem brownian_exists :
    ∃ P : Measure CP, IsProbabilityMeasure P ∧ IsBrownianReal (fun t (b : CP) => b.val t) P := by
  refine ⟨mu.map Bmap, Measure.isProbabilityMeasure_map measurable_Bmap.aemeasurable,
    ⟨⟨fun I => ?_⟩, ae_of_all _ fun b => b.2⟩⟩
  have hm : Measurable (fun b : CP => I.restrict (fun t => b.val t)) :=
    measurable_pi_lambda _ fun t => (measurable_pi_apply (t : ℝ≥0)).comp measurable_subtype_coe
  refine ⟨hm.aemeasurable, ?_⟩
  rw [Measure.map_map hm measurable_Bmap]
  exact (Bf_brownian.hasLaw I).map_eq


/-! ## Pieces 1 and 2 -/

lemma cl_nat_of_lt {j k : ℕ} (h : j < k) : cl j (k : ℝ≥0) = 1 := by
  unfold cl
  have : (1 : ℝ) ≤ (k : ℝ) - j := by
    have : ((j : ℝ) + 1) ≤ k := by exact_mod_cast h
    linarith
  simp only [NNReal.coe_natCast]
  rw [max_eq_left (by linarith), min_eq_right this]

/-- Piecewise-linear correction of a path `w` so that its integer values are the partial sums of `g`. -/
noncomputable def glue (g : ℕ → ℝ) (w : CP) (N : ℕ) (t : ℝ≥0) : ℝ :=
  w.val t - w.val 0 +
    ∑ j ∈ Finset.range N, (g j - (w.val ((j + 1 : ℕ) : ℝ≥0) - w.val (j : ℝ≥0))) * cl j t

noncomputable def bpath (g : ℕ → ℝ) (w : CP) (t : ℝ≥0) : ℝ := glue g w (⌊t⌋₊ + 1) t

lemma glue_mono (g : ℕ → ℝ) (w : CP) {N M : ℕ} {t : ℝ≥0} (ht : (t : ℝ) ≤ N) (hNM : N ≤ M) :
    glue g w N t = glue g w M t := by
  unfold glue
  congr 1
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro j hjM hjN
  have : N ≤ j := by simpa using hjN
  rw [cl_of_le (by have : (N : ℝ) ≤ j := by exact_mod_cast this
                   linarith), mul_zero]

lemma bpath_eq (g : ℕ → ℝ) (w : CP) {N : ℕ} {t : ℝ≥0} (ht : (t : ℝ) ≤ N) :
    bpath g w t = glue g w N t := by
  unfold bpath
  have hK : (t : ℝ) ≤ ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one t
    have : (t : ℝ) < ((⌊t⌋₊ : ℝ≥0) : ℝ) + 1 := by exact_mod_cast this
    push_cast
    simpa using this.le
  rw [glue_mono g w hK (le_max_left _ N), ← glue_mono g w ht (le_max_right _ N)]

lemma glue_continuous (g : ℕ → ℝ) (w : CP) (N : ℕ) : Continuous (glue g w N) := by
  unfold glue
  refine (w.2.sub continuous_const).add ?_
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (cl_continuous j)

lemma bpath_continuous (g : ℕ → ℝ) (w : CP) : Continuous (bpath g w) := by
  rw [continuous_iff_continuousAt]
  intro t0
  set N : ℕ := ⌊t0⌋₊ + 1 with hN
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ) < N} := isOpen_lt NNReal.continuous_coe continuous_const
  have hmem : t0 ∈ {t : ℝ≥0 | (t : ℝ) < N} := by
    have := Nat.lt_floor_add_one t0
    show (t0 : ℝ) < ((⌊t0⌋₊ + 1 : ℕ) : ℝ)
    push_cast
    exact_mod_cast this
  refine ((glue_continuous g w N).continuousAt).congr ?_
  filter_upwards [hopen.mem_nhds hmem] with t ht
  exact (bpath_eq g w (le_of_lt ht)).symm

lemma bpath_nat (g : ℕ → ℝ) (w : CP) (k : ℕ) :
    bpath g w (k : ℝ≥0) = ∑ i ∈ Finset.range k, g i := by
  rw [bpath_eq g w (N := k) (by simp)]
  unfold glue
  have : ∀ j ∈ Finset.range k,
      (g j - (w.val ((j + 1 : ℕ) : ℝ≥0) - w.val (j : ℝ≥0))) * cl j (k : ℝ≥0) =
        g j - (w.val ((j + 1 : ℕ) : ℝ≥0) - w.val (j : ℝ≥0)) := by
    intro j hj
    rw [cl_nat_of_lt (Finset.mem_range.1 hj), mul_one]
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib,
    Finset.sum_range_sub (fun j : ℕ => w.val (j : ℝ≥0))]
  simp

lemma measurable_eval_CP (t : ℝ≥0) : Measurable (fun w : CP => w.val t) :=
  (measurable_pi_apply t).comp measurable_subtype_coe

abbrev XX := (ℕ → ℝ) × (ℕ → ℝ)

lemma measurable_bpath_t (t : ℝ≥0) :
    Measurable (fun ω : XX × CP => bpath ω.1.2 ω.2 t) := by
  unfold bpath glue
  refine Measurable.add ?_ ?_
  · exact ((measurable_eval_CP t).comp measurable_snd).sub ((measurable_eval_CP 0).comp measurable_snd)
  · refine Finset.measurable_sum _ fun j _ => ?_
    refine Measurable.mul ?_ measurable_const
    refine Measurable.sub ((measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)) ?_
    exact ((measurable_eval_CP _).comp measurable_snd).sub ((measurable_eval_CP _).comp measurable_snd)

/-- The coupling map. -/
noncomputable def F (ω : XX × CP) : (ℕ → ℝ) × CP :=
  (ω.1.1, ⟨bpath ω.1.2 ω.2, bpath_continuous _ _⟩)

lemma measurable_F : Measurable F := by
  refine Measurable.prodMk (measurable_fst.comp measurable_fst) ?_
  refine Measurable.subtype_mk ?_
  exact measurable_pi_lambda _ fun t => measurable_bpath_t t

lemma map_F_comp_fst (Q : Measure XX) [IsProbabilityMeasure Q] (P : Measure CP)
    [IsProbabilityMeasure P] {β : Type*} [MeasurableSpace β] {φ : (ℕ → ℝ) → β}
    (hφ : Measurable φ) :
    ((Q.prod P).map F).map (fun z => φ z.1) = Q.map (fun x => φ x.1) := by
  rw [Measure.map_map (show Measurable (fun z : (ℕ → ℝ) × CP => φ z.1) from
    hφ.comp measurable_fst) measurable_F]
  have : (fun z : (ℕ → ℝ) × CP => φ z.1) ∘ F = (fun x : XX => φ x.1) ∘ Prod.fst := rfl
  rw [this, ← Measure.map_map (show Measurable (fun x : XX => φ x.1) from hφ.comp measurable_fst)
    measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]

/-- Assembly: a Brownian `bpath` on the product space yields the KMT approximation. -/
theorem assemble (μ : ProbabilityMeasure ℝ)
    (hmean : ∫ x : ℝ, x ∂(μ : Measure ℝ) = 0)
    (hvariance : variance (fun x : ℝ => x) (μ : Measure ℝ) = 1)
    (Q : Measure XX) [IsProbabilityMeasure Q]
    (h1 : iIndepFun (fun (i : ℕ) (z : XX) => z.1 i) Q)
    (h2 : ∀ i : ℕ, HasLaw (fun (z : XX) => z.1 i) (μ : Measure ℝ) Q)
    (C K lam : ℝ) (hC : 0 < C) (hK : 0 < K) (hlam : 0 < lam)
    (hb : ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
        Q {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
            C * Real.log (n : ℝ) + x <
              |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} <
          ENNReal.ofReal (K * Real.exp (-lam * x)))
    (P : Measure CP) [IsProbabilityMeasure P]
    (hB : IsBrownianReal (fun t (ω : XX × CP) => bpath ω.1.2 ω.2 t) (Q.prod P)) :
    EthierKurtz.kmtApproximation μ := by
  have hprob : IsProbabilityMeasure ((Q.prod P).map F) :=
    Measure.isProbabilityMeasure_map measurable_F.aemeasurable
  refine ⟨⟨(Q.prod P).map F, hprob⟩, ?_, ?_, ?_, C, K, lam, hC, hK, hlam, ?_⟩
  · -- independence of the first coordinates
    show iIndepFun (fun (i : ℕ) (z : (ℕ → ℝ) × CP) => z.1 i) ((Q.prod P).map F)
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun i => by fun_prop)]
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun i => by fun_prop)] at h1
    rw [map_F_comp_fst Q P (φ := fun x i => x i) measurable_id, h1]
    congr 1
    funext i
    exact (map_F_comp_fst Q P (φ := fun x => x i) (measurable_pi_apply i)).symm
  · intro i
    refine ⟨((measurable_pi_apply i).comp measurable_fst).aemeasurable, ?_⟩
    show ((Q.prod P).map F).map (fun z => z.1 i) = (μ : Measure ℝ)
    rw [map_F_comp_fst Q P (φ := fun x => x i) (measurable_pi_apply i)]
    exact (h2 i).map_eq
  · refine ⟨⟨fun I => ?_⟩, ae_of_all _ fun z => z.2.2⟩
    have hm : Measurable (fun z : (ℕ → ℝ) × CP => I.restrict (fun t => z.2.val t)) :=
      measurable_pi_lambda _ fun t => (measurable_eval_CP t).comp measurable_snd
    refine ⟨hm.aemeasurable, ?_⟩
    show ((Q.prod P).map F).map _ = _
    rw [Measure.map_map hm measurable_F]
    exact (hB.hasLaw I).map_eq
  · intro m σ W n hn x hx
    have hm0 : m = 0 := hmean
    have hσ1 : σ = 1 := by
      show Real.sqrt (variance (fun x : ℝ => x) (μ : Measure ℝ)) = 1
      rw [hvariance, Real.sqrt_one]
    have hW : ∀ (k : ℕ) (z : (ℕ → ℝ) × CP), W (k : ℝ≥0) z = z.2.val k := by
      intro k z
      show m * ((k : ℝ≥0) : ℝ) + σ * z.2.val k = z.2.val k
      rw [hm0, hσ1]; ring
    simp only [hW]
    set S : Set ((ℕ → ℝ) × CP) := {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
        C * Real.log (n : ℝ) + x < |(∑ i ∈ Finset.range k, z.1 i) - z.2.val k|} with hS
    have hSm : MeasurableSet S := by
      have : S = ⋃ k : ℕ, {z | 1 ≤ k ∧ k ≤ n ∧
          C * Real.log (n : ℝ) + x < |(∑ i ∈ Finset.range k, z.1 i) - z.2.val k|} := by
        ext z; simp [hS]
      rw [this]
      refine MeasurableSet.iUnion fun k => ?_
      by_cases hk : 1 ≤ k ∧ k ≤ n
      · simp only [hk, true_and]
        refine measurableSet_lt measurable_const ?_
        refine Measurable.abs (Measurable.sub ?_ ((measurable_eval_CP _).comp measurable_snd))
        exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp measurable_fst
      · have : {z : (ℕ → ℝ) × CP | 1 ≤ k ∧ k ≤ n ∧
            C * Real.log (n : ℝ) + x < |(∑ i ∈ Finset.range k, z.1 i) - z.2.val k|} = ∅ := by
          ext z; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h => hk ⟨h.1, h.2.1⟩
        rw [this]; exact MeasurableSet.empty
    show ((Q.prod P).map F) S < _
    rw [Measure.map_apply measurable_F hSm]
    have hpre : F ⁻¹' S = {z : XX | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
            C * Real.log (n : ℝ) + x <
              |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} ×ˢ Set.univ := by
      ext ω
      simp only [hS, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true, F]
      simp only [bpath_nat]
    rw [hpre, Measure.prod_prod, measure_univ, mul_one]
    exact hb n hn x hx

/-! ## Piece 2: `bpath` is Brownian under `Q.prod P` -/

noncomputable def Ug (M : ℕ) (t : ℝ≥0) (ω : XX × CP) : ℝ :=
  ∑ j ∈ Finset.range M, cl j t * ω.1.2 j

noncomputable def Yg (M : ℕ) (t : ℝ≥0) (ω : XX × CP) : ℝ :=
  ω.2.val t - ω.2.val 0 -
    ∑ j ∈ Finset.range M, cl j t * (ω.2.val ((j + 1 : ℕ) : ℝ≥0) - ω.2.val (j : ℝ≥0))

lemma bpath_UY (ω : XX × CP) {M : ℕ} {t : ℝ≥0} (ht : (t : ℝ) ≤ M) :
    bpath ω.1.2 ω.2 t = Ug M t ω + Yg M t ω := by
  rw [bpath_eq _ _ ht]
  unfold glue Ug Yg
  have : ∀ j ∈ Finset.range M,
      (ω.1.2 j - (ω.2.val ((j + 1 : ℕ) : ℝ≥0) - ω.2.val (j : ℝ≥0))) * cl j t =
        cl j t * ω.1.2 j - cl j t * (ω.2.val ((j + 1 : ℕ) : ℝ≥0) - ω.2.val (j : ℝ≥0)) := by
    intro j _; ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib]
  ring

section Transport
variable (Q : Measure XX) [IsProbabilityMeasure Q] (P : Measure CP) [IsProbabilityMeasure P]

lemma map_prod_fst {β : Type*} [MeasurableSpace β] {φ : XX → β} (hφ : Measurable φ) :
    (Q.prod P).map (fun ω => φ ω.1) = Q.map φ := by
  rw [show (fun ω : XX × CP => φ ω.1) = φ ∘ Prod.fst from rfl,
    ← Measure.map_map hφ measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]

lemma map_prod_snd {β : Type*} [MeasurableSpace β] {φ : CP → β} (hφ : Measurable φ) :
    (Q.prod P).map (fun ω => φ ω.2) = P.map φ := by
  rw [show (fun ω : XX × CP => φ ω.2) = φ ∘ Prod.snd from rfl,
    ← Measure.map_map hφ measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]

lemma W_brownian (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) :
    IsBrownianReal (fun t (ω : XX × CP) => ω.2.val t) (Q.prod P) := by
  refine ⟨⟨fun I => ?_⟩, ae_of_all _ fun ω => ω.2.2⟩
  have hm : Measurable (fun b : CP => I.restrict (fun t => b.val t)) :=
    measurable_pi_lambda _ fun t => measurable_eval_CP t
  refine ⟨(hm.comp measurable_snd).aemeasurable, ?_⟩
  rw [map_prod_snd Q P hm]
  exact (hP.hasLaw I).map_eq

lemma g_indep (h3 : iIndepFun (fun (i : ℕ) (z : XX) => z.2 i) Q) :
    iIndepFun (fun (i : ℕ) (ω : XX × CP) => ω.1.2 i) (Q.prod P) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun i => by fun_prop)]
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun i => by fun_prop)] at h3
  rw [map_prod_fst Q P (φ := fun z i => z.2 i) (by fun_prop), h3]
  congr 1
  funext i
  exact (map_prod_fst Q P (φ := fun z => z.2 i) (by fun_prop)).symm

lemma g_law (h4 : ∀ i : ℕ, HasLaw (fun (z : XX) => z.2 i) (gaussianReal 0 1) Q) (i : ℕ) :
    HasLaw (fun (ω : XX × CP) => ω.1.2 i) (gaussianReal 0 1) (Q.prod P) := by
  refine ⟨(by fun_prop : Measurable (fun (ω : XX × CP) => ω.1.2 i)).aemeasurable, ?_⟩
  rw [map_prod_fst Q P (φ := fun z => z.2 i) (by fun_prop)]
  exact (h4 i).map_eq

lemma g_gaussProc (h3 : iIndepFun (fun (i : ℕ) (z : XX) => z.2 i) Q)
    (h4 : ∀ i : ℕ, HasLaw (fun (z : XX) => z.2 i) (gaussianReal 0 1) Q) :
    IsGaussianProcess (fun (i : ℕ) (ω : XX × CP) => ω.1.2 i) (Q.prod P) := by
  refine ⟨fun I => ?_⟩
  have hind := (g_indep Q P h3).precomp (Subtype.val_injective (p := fun i => i ∈ I))
  exact iIndepFun.hasGaussianLaw (fun i => (g_law Q P h4 i.1).hasGaussianLaw) hind

end Transport

lemma floor_le_succ (t : ℝ≥0) : (t : ℝ) ≤ ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by
  have := Nat.lt_floor_add_one t
  have : (t : ℝ) < ((⌊t⌋₊ : ℝ≥0) : ℝ) + 1 := by exact_mod_cast this
  push_cast
  simpa using this.le

section GP
variable (Q : Measure XX) [IsProbabilityMeasure Q] (P : Measure CP) [IsProbabilityMeasure P]

lemma U_gaussProc (h3 : iIndepFun (fun (i : ℕ) (z : XX) => z.2 i) Q)
    (h4 : ∀ i : ℕ, HasLaw (fun (z : XX) => z.2 i) (gaussianReal 0 1) Q) :
    IsGaussianProcess (fun t (ω : XX × CP) => Ug (⌊t⌋₊ + 1) t ω) (Q.prod P) := by
  refine (g_gaussProc Q P h3 h4).of_isGaussianProcess fun t => ?_
  refine ⟨Finset.range (⌊t⌋₊ + 1),
    ∑ j ∈ (Finset.range (⌊t⌋₊ + 1)).attach, cl j t • ContinuousLinearMap.proj j, fun ω => ?_⟩
  simp only [Ug, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.coe_proj, smul_eq_mul, Finset.restrict]
  exact (Finset.sum_attach (Finset.range (⌊t⌋₊ + 1)) (fun j => cl j t * ω.1.2 j)).symm

/-- the finite set of times that `Yg` at time `t` uses -/
noncomputable def Jt (t : ℝ≥0) : Finset ℝ≥0 :=
  insert t ((Finset.range (⌊t⌋₊ + 2)).image (fun k : ℕ => (k : ℝ≥0)))

lemma mem_Jt_nat (t : ℝ≥0) {k : ℕ} (hk : k ≤ ⌊t⌋₊ + 1) : ((k : ℕ) : ℝ≥0) ∈ Jt t :=
  Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega)))

lemma Y_gaussProc (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) :
    IsGaussianProcess (fun t (ω : XX × CP) => Yg (⌊t⌋₊ + 1) t ω) (Q.prod P) := by
  refine (W_brownian Q P hP).isGaussianProcess.of_isGaussianProcess fun t => ?_
  have h0 : ((0 : ℕ) : ℝ≥0) ∈ Jt t := mem_Jt_nat t (by omega)
  refine ⟨Jt t,
    ContinuousLinearMap.proj ⟨t, Finset.mem_insert_self _ _⟩ -
      ContinuousLinearMap.proj ⟨((0 : ℕ) : ℝ≥0), h0⟩ -
      ∑ j ∈ (Finset.range (⌊t⌋₊ + 1)).attach, cl j t •
        (ContinuousLinearMap.proj ⟨((j.1 + 1 : ℕ) : ℝ≥0),
            mem_Jt_nat t (by have := Finset.mem_range.1 j.2; omega)⟩ -
          ContinuousLinearMap.proj ⟨((j.1 : ℕ) : ℝ≥0),
            mem_Jt_nat t (by have := Finset.mem_range.1 j.2; omega)⟩), fun ω => ?_⟩
  simp only [Yg, ContinuousLinearMap.coe_sub', FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, Pi.sub_apply, ContinuousLinearMap.coe_proj,
    smul_eq_mul, Finset.restrict, Nat.cast_zero]
  congr 1
  exact (Finset.sum_attach (Finset.range (⌊t⌋₊ + 1))
    (fun j => cl j t * (ω.2.val ((j + 1 : ℕ) : ℝ≥0) - ω.2.val (j : ℝ≥0)))).symm

lemma B_gaussProc (h3 : iIndepFun (fun (i : ℕ) (z : XX) => z.2 i) Q)
    (h4 : ∀ i : ℕ, HasLaw (fun (z : XX) => z.2 i) (gaussianReal 0 1) Q)
    (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) :
    IsGaussianProcess (fun t (ω : XX × CP) => bpath ω.1.2 ω.2 t) (Q.prod P) := by
  refine ⟨fun I => ?_⟩
  have hU := (U_gaussProc Q P h3 h4).hasGaussianLaw I
  have hY := (Y_gaussProc Q P hP).hasGaussianLaw I
  have mX : Measurable (fun x : XX => I.restrict (fun t => ∑ j ∈ Finset.range (⌊t⌋₊ + 1),
      cl j t * x.2 j)) := by
    refine measurable_pi_lambda _ fun t => ?_
    exact Finset.measurable_sum _ fun j _ => measurable_const.mul ((measurable_pi_apply j).comp measurable_snd)
  have mY : Measurable (fun w : CP => I.restrict (fun t => w.val t - w.val 0 -
      ∑ j ∈ Finset.range (⌊t⌋₊ + 1),
        cl j t * (w.val ((j + 1 : ℕ) : ℝ≥0) - w.val (j : ℝ≥0)))) := by
    refine measurable_pi_lambda _ fun t => ?_
    refine ((measurable_eval_CP _).sub (measurable_eval_CP _)).sub ?_
    exact Finset.measurable_sum _ fun j _ =>
      measurable_const.mul ((measurable_eval_CP _).sub (measurable_eval_CP _))
  have hind := indepFun_prod (μ := Q) (ν := P) mX mY
  have hsum := (IndepFun.hasGaussianLaw hU hY hind).fun_add
  have heq : (fun ω : XX × CP => I.restrict (fun t => bpath ω.1.2 ω.2 t)) =
      (fun ω => I.restrict (fun x => Ug (⌊x⌋₊ + 1) x ω) +
        I.restrict (fun x => Yg (⌊x⌋₊ + 1) x ω)) := by
    funext ω t
    simp only [Finset.restrict, Pi.add_apply]
    exact bpath_UY ω (floor_le_succ t)
  rw [heq]
  exact hsum

end GP

section Moments
variable (Q : Measure XX) [IsProbabilityMeasure Q] (P : Measure CP) [IsProbabilityMeasure P]

lemma Ug_integral (h4 : ∀ i : ℕ, HasLaw (fun (z : XX) => z.2 i) (gaussianReal 0 1) Q)
    (M : ℕ) (t : ℝ≥0) : ∫ ω, Ug M t ω ∂(Q.prod P) = 0 := by
  unfold Ug
  rw [integral_finset_sum]
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul, (g_law Q P h4 j).integral_eq, integral_id_gaussianReal, mul_zero]
  · intro j _
    exact ((g_law Q P h4 j).hasGaussianLaw.integrable).const_mul _

lemma Yg_integral (hP : IsBrownianReal (fun t (b : CP) => b.val t) P)
    (M : ℕ) (t : ℝ≥0) : ∫ ω, Yg M t ω ∂(Q.prod P) = 0 := by
  have hW := W_brownian Q P hP
  have hi : ∀ a : ℝ≥0, Integrable (fun ω : XX × CP => ω.2.val a) (Q.prod P) :=
    fun a => hW.integrable_eval a
  have h0 : ∀ a : ℝ≥0, ∫ ω, ω.2.val a ∂(Q.prod P) = 0 := fun a => hW.integral_eval a
  have hD : ∀ j : ℕ, Integrable (fun ω : XX × CP =>
      cl j t * (ω.2.val ((j + 1 : ℕ) : ℝ≥0) - ω.2.val (j : ℝ≥0))) (Q.prod P) :=
    fun j => ((hi _).sub (hi _)).const_mul _
  have hD0 : ∀ j : ℕ, ∫ ω, cl j t * (ω.2.val ((j + 1 : ℕ) : ℝ≥0) - ω.2.val (j : ℝ≥0))
      ∂(Q.prod P) = 0 := by
    intro j
    rw [integral_const_mul, integral_sub (hi _) (hi _), h0, h0, sub_zero, mul_zero]
  have hA : Integrable (fun ω : XX × CP => ω.2.val t - ω.2.val 0) (Q.prod P) := (hi t).sub (hi 0)
  have hS : Integrable (fun ω : XX × CP => ∑ j ∈ Finset.range M,
      cl j t * (ω.2.val ((j + 1 : ℕ) : ℝ≥0) - ω.2.val (j : ℝ≥0))) (Q.prod P) :=
    integrable_finset_sum _ fun j _ => hD j
  unfold Yg
  rw [integral_sub hA hS, integral_sub (hi t) (hi 0), h0, h0,
    integral_finset_sum _ fun j _ => hD j, Finset.sum_eq_zero fun j _ => hD0 j]
  simp

lemma B_integral (h4 : ∀ i : ℕ, HasLaw (fun (z : XX) => z.2 i) (gaussianReal 0 1) Q)
    (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) (t : ℝ≥0) :
    ∫ ω, bpath ω.1.2 ω.2 t ∂(Q.prod P) = 0 := by
  have hW := W_brownian Q P hP
  have hi : ∀ a : ℝ≥0, Integrable (fun ω : XX × CP => ω.2.val a) (Q.prod P) :=
    fun a => hW.integrable_eval a
  have hU : Integrable (Ug (⌊t⌋₊ + 1) t) (Q.prod P) :=
    integrable_finset_sum _ fun j _ => ((g_law Q P h4 j).hasGaussianLaw.integrable).const_mul _
  have hY : Integrable (Yg (⌊t⌋₊ + 1) t) (Q.prod P) :=
    ((hi t).sub (hi 0)).sub (integrable_finset_sum _ fun j _ => ((hi _).sub (hi _)).const_mul _)
  simp_rw [bpath_UY _ (floor_le_succ t)]
  rw [integral_add hU hY, Ug_integral Q P h4, Yg_integral Q P hP, add_zero]

end Moments

section Cov
variable (Q : Measure XX) [IsProbabilityMeasure Q] (P : Measure CP) [IsProbabilityMeasure P]

noncomputable def Wf (a : ℝ≥0) : XX × CP → ℝ := fun ω => ω.2.val a
noncomputable def Df (j : ℕ) : XX × CP → ℝ := Wf ((j + 1 : ℕ) : ℝ≥0) - Wf (j : ℝ≥0)
noncomputable def Gf (j : ℕ) : XX × CP → ℝ := fun ω => ω.1.2 j
noncomputable def Sf (M : ℕ) (a : ℝ≥0) : XX × CP → ℝ := ∑ j ∈ Finset.range M, cl j a • Df j

lemma Ug_eq (M : ℕ) (a : ℝ≥0) : Ug M a = ∑ j ∈ Finset.range M, cl j a • Gf j := by
  funext ω; simp [Ug, Gf, Finset.sum_apply]

lemma Yg_eq (M : ℕ) (a : ℝ≥0) : Yg M a = Wf a - Wf 0 - Sf M a := by
  funext ω; simp [Yg, Wf, Sf, Df, Finset.sum_apply]

lemma cl_succ_sub (i j : ℕ) :
    cl j ((i + 1 : ℕ) : ℝ≥0) - cl j (i : ℝ≥0) = if i = j then 1 else 0 := by
  unfold cl
  simp only [NNReal.coe_natCast]
  push_cast
  split_ifs with h
  · subst h; simp only [min_def, max_def]; split_ifs <;> linarith
  · have h' : (i : ℝ) + 1 ≤ j ∨ (j : ℝ) + 1 ≤ i := by
      rcases (show i + 1 ≤ j ∨ j + 1 ≤ i by omega) with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    simp only [min_def, max_def]
    rcases h' with h' | h' <;> split_ifs <;> linarith

variable {Q P}

lemma memLp_Wf (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) (a : ℝ≥0) :
    MemLp (Wf a) 2 (Q.prod P) :=
  ((W_brownian Q P hP).isGaussianProcess.hasGaussianLaw_eval a).memLp_two

lemma memLp_Df (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) (j : ℕ) :
    MemLp (Df j) 2 (Q.prod P) := (memLp_Wf (Q := Q) hP _).sub (memLp_Wf hP _)

lemma memLp_Sf (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) (M : ℕ) (a : ℝ≥0) :
    MemLp (Sf M a) 2 (Q.prod P) :=
  memLp_finsetSum' _ fun j _ => (memLp_Df (Q := Q) hP j).const_smul (cl j a)

lemma memLp_A (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) (a : ℝ≥0) :
    MemLp (Wf a - Wf 0) 2 (Q.prod P) := (memLp_Wf (Q := Q) hP _).sub (memLp_Wf hP _)

lemma memLp_Gf (h4 : ∀ i : ℕ, HasLaw (fun (z : XX) => z.2 i) (gaussianReal 0 1) Q) (j : ℕ) :
    MemLp (Gf j) 2 (Q.prod P) := (g_law Q P h4 j).hasGaussianLaw.memLp_two

lemma memLp_Ug (h4 : ∀ i : ℕ, HasLaw (fun (z : XX) => z.2 i) (gaussianReal 0 1) Q)
    (M : ℕ) (a : ℝ≥0) : MemLp (Ug M a) 2 (Q.prod P) := by
  rw [Ug_eq]; exact memLp_finsetSum' _ fun j _ => (memLp_Gf (P := P) h4 j).const_smul (cl j a)

lemma memLp_Yg (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) (M : ℕ) (a : ℝ≥0) :
    MemLp (Yg M a) 2 (Q.prod P) := by
  rw [Yg_eq]; exact (memLp_A hP a).sub (memLp_Sf hP M a)

lemma cov_Wf (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) (a b : ℝ≥0) :
    cov[Wf a, Wf b; Q.prod P] = min (a : ℝ) (b : ℝ) := by
  have h := (W_brownian Q P hP).covariance_eval a b
  exact h

lemma cov_Wf_Df (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) (a : ℝ≥0) (j : ℕ) :
    cov[Wf a, Df j; Q.prod P] = cl j a := by
  rw [show Df j = Wf ((j + 1 : ℕ) : ℝ≥0) - Wf (j : ℝ≥0) from rfl,
    covariance_sub_right (memLp_Wf hP _) (memLp_Wf hP _) (memLp_Wf hP _),
    cov_Wf hP, cov_Wf hP]
  push_cast
  exact min_sub_cl a j

lemma cov_Df_Df (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) (i j : ℕ) :
    cov[Df i, Df j; Q.prod P] = if i = j then 1 else 0 := by
  rw [show Df i = Wf ((i + 1 : ℕ) : ℝ≥0) - Wf (i : ℝ≥0) from rfl,
    covariance_sub_left (memLp_Wf hP _) (memLp_Wf hP _) (memLp_Df hP _),
    cov_Wf_Df hP, cov_Wf_Df hP, cl_succ_sub]

lemma cov_A_A (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) (a b : ℝ≥0) :
    cov[Wf a - Wf 0, Wf b - Wf 0; Q.prod P] = min (a : ℝ) (b : ℝ) := by
  rw [covariance_sub_sub (memLp_Wf hP _) (memLp_Wf hP _) (memLp_Wf hP _) (memLp_Wf hP _),
    cov_Wf hP, cov_Wf hP, cov_Wf hP, cov_Wf hP, NNReal.coe_zero,
    min_eq_right (NNReal.coe_nonneg a), min_eq_left (NNReal.coe_nonneg b), min_self]
  ring

lemma cov_A_S (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) (M : ℕ) (a b : ℝ≥0) :
    cov[Wf a - Wf 0, Sf M b; Q.prod P] = ∑ j ∈ Finset.range M, cl j a * cl j b := by
  unfold Sf
  rw [covariance_sum_right' (fun j _ => (memLp_Df hP j).const_smul _) (memLp_A hP a)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [covariance_smul_right, covariance_sub_left (memLp_Wf hP _) (memLp_Wf hP _) (memLp_Df hP _),
    cov_Wf_Df hP, cov_Wf_Df hP, cl_of_le (j := j) (t := 0) (by simp)]
  ring

lemma cov_S_A (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) (M : ℕ) (a b : ℝ≥0) :
    cov[Sf M a, Wf b - Wf 0; Q.prod P] = ∑ j ∈ Finset.range M, cl j a * cl j b := by
  rw [covariance_comm, cov_A_S hP]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

lemma cov_S_S (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) (M : ℕ) (a b : ℝ≥0) :
    cov[Sf M a, Sf M b; Q.prod P] = ∑ j ∈ Finset.range M, cl j a * cl j b := by
  unfold Sf
  rw [covariance_sum_sum' (fun j _ => (memLp_Df hP j).const_smul _)
    (fun j _ => (memLp_Df hP j).const_smul _)]
  simp_rw [covariance_smul_left, covariance_smul_right, cov_Df_Df hP]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [if_neg (Ne.symm hji)]; ring)
    (fun h => absurd hi h), if_pos rfl]
  ring

lemma cov_Yg (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) (M : ℕ) (a b : ℝ≥0) :
    cov[Yg M a, Yg M b; Q.prod P] =
      min (a : ℝ) (b : ℝ) - ∑ j ∈ Finset.range M, cl j a * cl j b := by
  rw [Yg_eq, Yg_eq, covariance_sub_sub (memLp_A hP a) (memLp_Sf hP M a) (memLp_A hP b)
    (memLp_Sf hP M b), cov_A_A hP, cov_A_S hP, cov_S_A hP, cov_S_S hP]
  ring

lemma cov_Gf (h3 : iIndepFun (fun (i : ℕ) (z : XX) => z.2 i) Q)
    (h4 : ∀ i : ℕ, HasLaw (fun (z : XX) => z.2 i) (gaussianReal 0 1) Q) (i j : ℕ) :
    cov[Gf i, Gf j; Q.prod P] = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h
    rw [covariance_self (memLp_Gf (P := P) h4 i).aemeasurable]
    change Var[fun ω : XX × CP => ω.1.2 i; Q.prod P] = 1
    rw [(g_law Q P h4 i).variance_eq,
      variance_id_gaussianReal]
    simp
  · exact ((g_indep Q P h3).indepFun h).covariance_eq_zero (memLp_Gf h4 i) (memLp_Gf h4 j)

lemma cov_Ug (h3 : iIndepFun (fun (i : ℕ) (z : XX) => z.2 i) Q)
    (h4 : ∀ i : ℕ, HasLaw (fun (z : XX) => z.2 i) (gaussianReal 0 1) Q) (M : ℕ) (a b : ℝ≥0) :
    cov[Ug M a, Ug M b; Q.prod P] = ∑ j ∈ Finset.range M, cl j a * cl j b := by
  rw [Ug_eq, Ug_eq, covariance_sum_sum' (fun j _ => (memLp_Gf h4 j).const_smul _)
    (fun j _ => (memLp_Gf h4 j).const_smul _)]
  simp_rw [covariance_smul_left, covariance_smul_right, cov_Gf h3 h4]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [if_neg (Ne.symm hji)]; ring)
    (fun h => absurd hi h), if_pos rfl]
  ring

lemma cov_U_Y (h4 : ∀ i : ℕ, HasLaw (fun (z : XX) => z.2 i) (gaussianReal 0 1) Q)
    (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) (M : ℕ) (a b : ℝ≥0) :
    cov[Ug M a, Yg M b; Q.prod P] = 0 := by
  have hE : ∀ c : ℝ≥0, MemLp (fun w : CP => w.val c) 2 P := fun c =>
    (hP.isGaussianProcess.hasGaussianLaw_eval c).memLp_two
  have hX : MemLp (fun x : XX => ∑ j ∈ Finset.range M, cl j a * x.2 j) 2 Q :=
    memLp_finsetSum _ fun j _ => ((h4 j).hasGaussianLaw.memLp_two).const_mul _
  have hY : MemLp (fun w : CP => w.val b - w.val 0 - ∑ j ∈ Finset.range M,
      cl j b * (w.val ((j + 1 : ℕ) : ℝ≥0) - w.val (j : ℝ≥0))) 2 P :=
    ((hE b).sub (hE 0)).sub (memLp_finsetSum _ fun j _ => ((hE _).sub (hE _)).const_mul _)
  exact covariance_fst_snd_prod hX hY

lemma B_cov (h3 : iIndepFun (fun (i : ℕ) (z : XX) => z.2 i) Q)
    (h4 : ∀ i : ℕ, HasLaw (fun (z : XX) => z.2 i) (gaussianReal 0 1) Q)
    (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) (s t : ℝ≥0) (hst : s ≤ t) :
    cov[fun ω : XX × CP => bpath ω.1.2 ω.2 s, fun ω => bpath ω.1.2 ω.2 t; Q.prod P] = s := by
  have htM := floor_le_succ t
  have hsM : (s : ℝ) ≤ ((⌊t⌋₊ + 1 : ℕ) : ℝ) := le_trans (by exact_mod_cast hst) htM
  have e1 : (fun ω : XX × CP => bpath ω.1.2 ω.2 s) = Ug (⌊t⌋₊ + 1) s + Yg (⌊t⌋₊ + 1) s :=
    funext fun ω => bpath_UY ω hsM
  have e2 : (fun ω : XX × CP => bpath ω.1.2 ω.2 t) = Ug (⌊t⌋₊ + 1) t + Yg (⌊t⌋₊ + 1) t :=
    funext fun ω => bpath_UY ω htM
  rw [e1, e2, covariance_add_left (memLp_Ug h4 _ _) (memLp_Yg hP _ _)
      ((memLp_Ug h4 _ _).add (memLp_Yg hP _ _)),
    covariance_add_right (memLp_Ug h4 _ _) (memLp_Ug h4 _ _) (memLp_Yg hP _ _),
    covariance_add_right (memLp_Yg hP _ _) (memLp_Ug h4 _ _) (memLp_Yg hP _ _),
    cov_U_Y h4 hP, covariance_comm (Yg _ s), cov_U_Y h4 hP, cov_Ug h3 h4, cov_Yg hP,
    min_eq_left (by exact_mod_cast hst)]
  ring

theorem glue_isBrownian (h3 : iIndepFun (fun (i : ℕ) (z : XX) => z.2 i) Q)
    (h4 : ∀ i : ℕ, HasLaw (fun (z : XX) => z.2 i) (gaussianReal 0 1) Q)
    (hP : IsBrownianReal (fun t (b : CP) => b.val t) P) :
    IsBrownianReal (fun t (ω : XX × CP) => bpath ω.1.2 ω.2 t) (Q.prod P) :=
  ⟨(B_gaussProc Q P h3 h4 hP).isPreBrownianReal_of_covariance (B_integral Q P h4 hP)
    (fun s t hst => B_cov h3 h4 hP s t hst), ae_of_all _ fun ω => bpath_continuous _ _⟩

end Cov

end Peac1b43d

open MeasureTheory ProbabilityTheory EthierKurtz in
theorem solution
    (μ : ProbabilityMeasure ℝ)
    (hmean : ∫ x : ℝ, x ∂(μ : Measure ℝ) = 0)
    (hvariance : variance (fun x : ℝ => x) (μ : Measure ℝ) = 1)
    (hdisc : kmtDiscreteApproximation μ) :
    kmtApproximation μ := by
  obtain ⟨Q, h1, h2, h3, h4, C, K, lam, hC, hK, hlam, hb⟩ := hdisc
  obtain ⟨P, hPprob, hP⟩ := Peac1b43d.brownian_exists
  exact Peac1b43d.assemble μ hmean hvariance (Q : Measure ((ℕ → ℝ) × (ℕ → ℝ))) h1 h2 C K lam
    hC hK hlam hb P (Peac1b43d.glue_isBrownian h3 h4 hP)
