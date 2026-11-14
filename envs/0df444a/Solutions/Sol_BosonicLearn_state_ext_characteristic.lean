-- Prove2me | solution 1 for BosonicLearn.state_ext_characteristic
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T20:57:22.976514+00:00
-- url     : https://prove2.me/submissions/43faad9c-e43c-4131-a641-29608131edf8

import Mathlib
import Definitions.Def_BosonicLearn_husimiQ
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Theorems.Thm_BosonicLearn_husimi_fourier

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize IsDensity NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory
open scoped ENNReal

open BosonicLearn

/-!
# A state on the Fock space is determined by its Weyl characteristic function

Route.

1. `husimi_ae_eq`: by `husimi_fourier`, the finite measures `Q_ρ dβ` and `Q_σ dβ` have the same
   characteristic function, hence coincide (`Measure.ext_of_charFun`), hence `Q_ρ = Q_σ` almost
   everywhere (`withDensity_eq_iff`).
2. `husimi_continuous`: the entries of a trace-class array are bounded (`entry_bound`), so the double
   series defining `Q` converges locally uniformly (`term_bound`, `maj_summable`) and `Q` is
   continuous; two continuous functions that agree almost everywhere agree everywhere.
3. A density is Hermitian (`density_herm`), so the double series is real (`G_real`) and the complex
   series `∑_{u,v} conj c(β)_u (ρ - σ)_{uv} c(β)_v` vanishes for every `β`. By `term_factor` this is,
   up to a non-vanishing Gaussian factor, a power series in `γ̄ⱼ, γⱼ` (`γⱼ = β_{q,j} + i β_{p,j}`) with
   coefficients `(ρ - σ)_{uv} wgt u wgt v`.
4. `PU_all`: such a power series vanishing on all of `ℂⁿ` has zero coefficients. One mode
   (`one_mode`): put `γ = t z` with `t` real; the coefficient of `t^N` (`ps_unique`) is a polynomial
   in `z` up to the factor `z^{-N}` on the unit circle, which has infinitely many points
   (`circle_infinite`). Several modes: induction on the set of modes (`PU_option`), summing over
   the other modes first.
-/

noncomputable section

/-! ### Uniqueness of power series in `γ̄, γ` -/

/-- A power series in one real variable that vanishes identically has vanishing coefficients. -/
private lemma ps_unique (c : ℕ → ℂ) (h : ∀ t : ℝ, HasSum (fun N => c N * (t : ℂ) ^ N) 0) :
    ∀ N, c N = 0 := by
  have hs : Summable fun N => ‖c N‖ := by
    have := (h 1).summable.norm
    simpa using this
  intro N
  induction N using Nat.strong_induction_on with
  | _ m ih =>
    have key : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖c m‖ ≤ t * ∑' N, ‖c N‖ := by
      intro t ht ht1
      have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      have h1 : HasSum (fun N => c (N + m) * (t : ℂ) ^ (N + m)) 0 := by
        have := (hasSum_nat_add_iff' m).mpr (h t)
        rw [Finset.sum_eq_zero (fun i hi => by rw [ih i (Finset.mem_range.mp hi), zero_mul]),
          sub_zero] at this
        exact this
      have h2 : HasSum (fun N => c (N + m) * (t : ℂ) ^ N) 0 := by
        have := h1.mul_right (((t : ℂ) ^ m)⁻¹)
        simp only [zero_mul] at this
        have e : (fun N => c (N + m) * (t : ℂ) ^ N) =
            fun N => c (N + m) * (t : ℂ) ^ (N + m) * ((t : ℂ) ^ m)⁻¹ := by
          funext N
          rw [pow_add]
          field_simp
        rw [e]
        exact this
      have h3 : HasSum (fun N => c (N + 1 + m) * (t : ℂ) ^ (N + 1)) (0 - c m) := by
        have := (hasSum_nat_add_iff' 1).mpr h2
        simpa using this
      have h4 : ‖c m‖ = ‖∑' N, c (N + 1 + m) * (t : ℂ) ^ (N + 1)‖ := by
        rw [h3.tsum_eq]; simp
      have hsn : Summable fun N => ‖c (N + 1 + m)‖ := by
        have := (summable_nat_add_iff (1 + m)).mpr hs
        simpa [add_assoc] using this
      have hle : ∀ N, ‖c (N + 1 + m) * (t : ℂ) ^ (N + 1)‖ ≤ t * ‖c (N + 1 + m)‖ := by
        intro N
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le, mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        calc t ^ (N + 1) = t ^ N * t := pow_succ t N
          _ ≤ 1 * t := mul_le_mul_of_nonneg_right (pow_le_one₀ ht.le ht1) ht.le
          _ = t := one_mul t
      have hsn2 : Summable fun N => ‖c (N + 1 + m) * (t : ℂ) ^ (N + 1)‖ :=
        Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle (hsn.mul_left t)
      rw [h4]
      calc ‖∑' N, c (N + 1 + m) * (t : ℂ) ^ (N + 1)‖
          ≤ ∑' N, ‖c (N + 1 + m) * (t : ℂ) ^ (N + 1)‖ := norm_tsum_le_tsum_norm hsn2
        _ ≤ ∑' N, t * ‖c (N + 1 + m)‖ := hsn2.tsum_le_tsum hle (hsn.mul_left t)
        _ = t * ∑' N, ‖c (N + 1 + m)‖ := tsum_mul_left
        _ ≤ t * ∑' N, ‖c N‖ := by
          refine mul_le_mul_of_nonneg_left ?_ ht.le
          have hinj : Function.Injective fun N : ℕ => N + 1 + m := fun a b hab => by
            simp only at hab; omega
          exact tsum_comp_le_tsum_of_inj hs (fun _ => norm_nonneg _) hinj
    by_contra hne
    have hpos : 0 < ‖c m‖ := norm_pos_iff.mpr hne
    have hS : ‖c m‖ ≤ ∑' N, ‖c N‖ := hs.le_tsum m (fun _ _ => norm_nonneg _)
    have hSpos : 0 < ∑' N, ‖c N‖ := lt_of_lt_of_le hpos hS
    have h := key (‖c m‖ / (2 * ∑' N, ‖c N‖)) (by positivity)
      (by rw [div_le_one (by positivity)]; linarith)
    have e : ‖c m‖ / (2 * ∑' N, ‖c N‖) * ∑' N, ‖c N‖ = ‖c m‖ / 2 := by
      field_simp
    rw [e] at h
    linarith

private lemma circle_infinite : {z : ℂ | ‖z‖ = 1}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun x : ℝ => (1 + (x : ℂ) * Complex.I) / (1 - (x : ℂ) * Complex.I)) ?_ ?_
  · intro x y hxy
    have hx : (1 - (x : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
    have hy : (1 - (y : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
    simp only at hxy
    rw [div_eq_div_iff hx hy] at hxy
    have := congrArg Complex.im hxy
    simp at this
    linarith
  · intro x
    show ‖(1 + (x : ℂ) * Complex.I) / (1 - (x : ℂ) * Complex.I)‖ = 1
    have hx : (1 - (x : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
    have hc : (1 - (x : ℂ) * Complex.I) = (starRingEnd ℂ) (1 + (x : ℂ) * Complex.I) := by
      simp
      ring
    rw [norm_div, hc, Complex.norm_conj, div_self]
    rw [← Complex.norm_conj, ← hc]
    exact norm_ne_zero_iff.mpr hx

/-- One mode: a series `∑ b k l γ̄^k γ^l` vanishing for every complex `γ` has `b = 0`. -/
private lemma one_mode (b : ℕ → ℕ → ℂ)
    (h : ∀ γ : ℂ, HasSum (fun p : ℕ × ℕ => b p.1 p.2 * ((starRingEnd ℂ) γ ^ p.1 * γ ^ p.2)) 0) :
    ∀ k l, b k l = 0 := by
  have hA : ∀ (z : ℂ) (N : ℕ),
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal N, b p.1 p.2 * ((starRingEnd ℂ) z ^ p.1 * z ^ p.2) = 0 := by
    intro z
    apply ps_unique
    intro t
    have h1 := h ((t : ℂ) * z)
    have h2 := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff).mpr h1
    have h3 := h2.sigma (fun N => hasSum_fintype _)
    convert h3 using 1
    funext N
    rw [Finset.sum_mul, ← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp : (p : ℕ × ℕ).1 + (p : ℕ × ℕ).2 = N := Finset.HasAntidiagonal.mem_antidiagonal.mp p.2
    simp only [Function.comp_apply, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply, map_mul,
      Complex.conj_ofReal, mul_pow]
    have ht : (t : ℂ) ^ N = (t : ℂ) ^ (p : ℕ × ℕ).1 * (t : ℂ) ^ (p : ℕ × ℕ).2 := by
      rw [← pow_add, hp]
    rw [ht]
    ring
  intro k l
  let Q : Polynomial ℂ := ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k + l),
    Polynomial.C (b p.1 p.2) * Polynomial.X ^ (2 * p.2)
  have hQ : Q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot Q (circle_infinite.mono fun z hz => ?_)
    have hz1 : (starRingEnd ℂ) z * z = 1 := by
      rw [Complex.conj_mul', hz]; simp
    show Q.eval z = 0
    have e : Q.eval z = z ^ (k + l) *
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k + l), b p.1 p.2 * ((starRingEnd ℂ) z ^ p.1 * z ^ p.2) := by
      simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : p.1 + p.2 = k + l := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [← hp', pow_add]
      calc b p.1 p.2 * z ^ (2 * p.2)
          = b p.1 p.2 * (((starRingEnd ℂ) z * z) ^ p.1 * z ^ (2 * p.2)) := by
            rw [hz1, one_pow, one_mul]
        _ = z ^ p.1 * z ^ p.2 * (b p.1 p.2 * ((starRingEnd ℂ) z ^ p.1 * z ^ p.2)) := by
            rw [mul_pow, two_mul, pow_add]; ring
    rw [e, hA z, mul_zero]
  have hc : Q.coeff (2 * l) = b k l := by
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (k, l)]
    · simp
    · intro p hp hne
      have hp' : p.1 + p.2 = k + l := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [if_neg]
      intro h2
      apply hne
      ext <;> simp <;> omega
    · intro hn
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (rfl : (k, l).1 + (k, l).2 = k + l)) hn
  rw [← hc, hQ, Polynomial.coeff_zero]

/-- `PU ι`: a power series in `γ̄ᵢ, γᵢ` (`i : ι`) vanishing identically has zero coefficients. -/
private def PU (ι : Type) [Fintype ι] : Prop :=
  ∀ a : (ι → ℕ) → (ι → ℕ) → ℂ,
    (∀ γ : ι → ℂ, HasSum (fun p : (ι → ℕ) × (ι → ℕ) =>
      a p.1 p.2 * ∏ i, ((starRingEnd ℂ) (γ i) ^ p.1 i * γ i ^ p.2 i)) 0) →
    ∀ u v, a u v = 0

private lemma PU_empty : PU PEmpty := by
  intro a h u v
  have h1 := h (fun _ => 0)
  have h2 := h1.unique (hasSum_single (u, v) (fun p hp => absurd
    (Prod.ext (funext fun i => i.elim) (funext fun i => i.elim) : p = (u, v)) hp))
  simpa using h2.symm

private lemma PU_equiv (α β : Type) [Fintype α] [Fintype β] (e : α ≃ β) (ih : PU α) : PU β := by
  intro a h u v
  let E : (α → ℕ) ≃ (β → ℕ) := Equiv.arrowCongr e (Equiv.refl ℕ)
  have key := ih (fun u v => a (E u) (E v)) (fun γ => ?_) (E.symm u) (E.symm v)
  · simpa using key
  · have h1 := h (fun j => γ (e.symm j))
    have h2 := (Equiv.hasSum_iff (E.prodCongr E)).mpr h1
    have e2 : (fun p : (α → ℕ) × (α → ℕ) =>
        a (E p.1) (E p.2) * ∏ i, ((starRingEnd ℂ) (γ i) ^ p.1 i * γ i ^ p.2 i)) =
        (fun p : (β → ℕ) × (β → ℕ) => a p.1 p.2 *
          ∏ i, ((starRingEnd ℂ) (γ (e.symm i)) ^ p.1 i * γ (e.symm i) ^ p.2 i)) ∘
            (E.prodCongr E) := by
      funext p
      simp only [Function.comp_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
      congr 1
      exact (Equiv.prod_comp e.symm
        (fun i => (starRingEnd ℂ) (γ i) ^ p.1 i * γ i ^ p.2 i)).symm
    rw [e2]
    exact h2

private lemma PU_option (α : Type) [Fintype α] (ih : PU α) : PU (Option α) := by
  intro a h
  let cons : ℕ → (α → ℕ) → (Option α → ℕ) := fun k w =>
    (Equiv.piOptionEquivProd (β := fun _ => ℕ)).symm (k, w)
  let E : ((Option α → ℕ) × (Option α → ℕ)) ≃ (ℕ × ℕ) × ((α → ℕ) × (α → ℕ)) :=
    ((Equiv.piOptionEquivProd (β := fun _ => ℕ)).prodCongr
      (Equiv.piOptionEquivProd (β := fun _ => ℕ))).trans
        (Equiv.prodProdProdComm ℕ (α → ℕ) ℕ (α → ℕ))
  have hF : ∀ (γ₀ : ℂ) (γ' : α → ℂ), HasSum (fun x : (ℕ × ℕ) × ((α → ℕ) × (α → ℕ)) =>
      a (cons x.1.1 x.2.1) (cons x.1.2 x.2.2) * (((starRingEnd ℂ) γ₀ ^ x.1.1 * γ₀ ^ x.1.2) *
        ∏ i, ((starRingEnd ℂ) (γ' i) ^ x.2.1 i * γ' i ^ x.2.2 i))) 0 := by
    intro γ₀ γ'
    have h1 := h (fun o => Option.elim o γ₀ γ')
    have h2 := (Equiv.hasSum_iff E.symm).mpr h1
    have e : (fun x : (ℕ × ℕ) × ((α → ℕ) × (α → ℕ)) =>
        a (cons x.1.1 x.2.1) (cons x.1.2 x.2.2) * (((starRingEnd ℂ) γ₀ ^ x.1.1 * γ₀ ^ x.1.2) *
          ∏ i, ((starRingEnd ℂ) (γ' i) ^ x.2.1 i * γ' i ^ x.2.2 i))) =
        (fun p : (Option α → ℕ) × (Option α → ℕ) => a p.1 p.2 *
          ∏ i, ((starRingEnd ℂ) ((fun o => Option.elim o γ₀ γ') i) ^ p.1 i *
            (fun o => Option.elim o γ₀ γ') i ^ p.2 i)) ∘ E.symm := by
      funext x
      simp only [Function.comp_apply]
      rw [Fintype.prod_option]
      rfl
    rw [e]
    exact h2
  have hB : ∀ (γ' : α → ℂ) (k l : ℕ), HasSum (fun p' : (α → ℕ) × (α → ℕ) =>
      a (cons k p'.1) (cons l p'.2) *
        ∏ i, ((starRingEnd ℂ) (γ' i) ^ p'.1 i * γ' i ^ p'.2 i)) 0 := by
    intro γ'
    have hfib : ∀ q : ℕ × ℕ, Summable (fun p' : (α → ℕ) × (α → ℕ) =>
        a (cons q.1 p'.1) (cons q.2 p'.2) *
          ∏ i, ((starRingEnd ℂ) (γ' i) ^ p'.1 i * γ' i ^ p'.2 i)) := by
      intro q
      have := (hF 1 γ').summable.prod_factor q
      simpa using this
    have h1 : ∀ γ₀ : ℂ, HasSum (fun q : ℕ × ℕ =>
        (∑' p' : (α → ℕ) × (α → ℕ), a (cons q.1 p'.1) (cons q.2 p'.2) *
          ∏ i, ((starRingEnd ℂ) (γ' i) ^ p'.1 i * γ' i ^ p'.2 i)) *
            ((starRingEnd ℂ) γ₀ ^ q.1 * γ₀ ^ q.2)) 0 := by
      intro γ₀
      refine (hF γ₀ γ').prod_fiberwise (fun q => ?_)
      have := (hfib q).hasSum.mul_right ((starRingEnd ℂ) γ₀ ^ q.1 * γ₀ ^ q.2)
      have e : (fun c : (α → ℕ) × (α → ℕ) =>
          a (cons (q, c).1.1 (q, c).2.1) (cons (q, c).1.2 (q, c).2.2) *
            (((starRingEnd ℂ) γ₀ ^ (q, c).1.1 * γ₀ ^ (q, c).1.2) *
              ∏ i, ((starRingEnd ℂ) (γ' i) ^ (q, c).2.1 i * γ' i ^ (q, c).2.2 i))) =
          fun p' : (α → ℕ) × (α → ℕ) => (a (cons q.1 p'.1) (cons q.2 p'.2) *
            ∏ i, ((starRingEnd ℂ) (γ' i) ^ p'.1 i * γ' i ^ p'.2 i)) *
              ((starRingEnd ℂ) γ₀ ^ q.1 * γ₀ ^ q.2) := by
        funext c
        ring
      rw [e]
      exact this
    have h2 := one_mode (fun k l => ∑' p' : (α → ℕ) × (α → ℕ), a (cons k p'.1) (cons l p'.2) *
          ∏ i, ((starRingEnd ℂ) (γ' i) ^ p'.1 i * γ' i ^ p'.2 i)) h1
    intro k l
    have h3 := (hfib (k, l)).hasSum
    have h4 : (∑' p' : (α → ℕ) × (α → ℕ), a (cons k p'.1) (cons l p'.2) *
          ∏ i, ((starRingEnd ℂ) (γ' i) ^ p'.1 i * γ' i ^ p'.2 i)) = 0 := h2 k l
    rw [h4] at h3
    exact h3
  intro u v
  have key := ih (fun u' v' => a (cons (u none) u') (cons (v none) v'))
    (fun γ' => hB γ' (u none) (v none)) (fun i => u (some i)) (fun i => v (some i))
  have hu : cons (u none) (fun i => u (some i)) = u := by
    funext o; cases o <;> rfl
  have hv : cons (v none) (fun i => v (some i)) = v := by
    funext o; cases o <;> rfl
  simp only [hu, hv] at key
  exact key

private lemma PU_all (I : Type) [Fintype I] : PU I := by
  refine Fintype.induction_empty_option (P := fun (α : Type) [Fintype α] => PU α) ?_ ?_ ?_ I
  · intro α β _ e ih
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    exact PU_equiv α β e ih
  · exact PU_empty
  · intro α _ ih
    exact PU_option α ih

/-! ### Products of series over multi-indices -/

/-- `PP α`: a product over the finite type `α` of absolutely convergent series over `ℕ` is an
absolutely convergent series over the multi-indices `α → ℕ`, with sum the product of the sums. -/
private def PP (α : Type) [Fintype α] : Prop :=
  ∀ (f : α → ℕ → ℂ) (s : α → ℂ),
      (∀ i, Summable fun k => ‖f i k‖) → (∀ i, HasSum (f i) (s i)) →
      Summable (fun w : α → ℕ => ‖∏ i, f i (w i)‖) ∧
      HasSum (fun w : α → ℕ => ∏ i, f i (w i)) (∏ i, s i)

private lemma PP_equiv (α β : Type) [Fintype α] [Fintype β] (e : α ≃ β) (ih : PP α) : PP β := by
  intro f s hn hs
  obtain ⟨h1, h2⟩ := ih (fun i => f (e i)) (fun i => s (e i)) (fun i => hn (e i))
    (fun i => hs (e i))
  let E : (β → ℕ) ≃ (α → ℕ) := Equiv.arrowCongr e.symm (Equiv.refl ℕ)
  have hE : ∀ w : β → ℕ, ∏ i, f (e i) (E w i) = ∏ j, f j (w j) := by
    intro w
    exact Equiv.prod_comp e (fun j => f j (w j))
  have hsE : ∏ i, s (e i) = ∏ j, s j := Equiv.prod_comp e s
  refine ⟨?_, ?_⟩
  · have := (Equiv.summable_iff E).mpr h1
    have hfun : ((fun w : α → ℕ => ‖∏ i, f (e i) (w i)‖) ∘ E) =
        fun w : β → ℕ => ‖∏ j, f j (w j)‖ := by
      funext w
      show ‖∏ i, f (e i) (E w i)‖ = _
      rw [hE]
    rw [hfun] at this
    exact this
  · have := (Equiv.hasSum_iff E).mpr h2
    have hfun : ((fun w : α → ℕ => ∏ i, f (e i) (w i)) ∘ E) =
        fun w : β → ℕ => ∏ j, f j (w j) := by
      funext w
      show ∏ i, f (e i) (E w i) = _
      rw [hE]
    rw [hfun, hsE] at this
    exact this

private lemma PP_empty : PP PEmpty := by
  intro f s _ _
  have h := hasSum_unique (fun w : PEmpty → ℕ => ∏ i, f i (w i))
  have hn := hasSum_unique (fun w : PEmpty → ℕ => ‖∏ i, f i (w i)‖)
  refine ⟨hn.summable, ?_⟩
  convert h using 1
  simp

private lemma PP_option (α : Type) [Fintype α] (ih : PP α) : PP (Option α) := by
  intro f s hn hs
  obtain ⟨h1, h2⟩ := ih (fun i => f (some i)) (fun i => s (some i)) (fun i => hn (some i))
    (fun i => hs (some i))
  let E : (Option α → ℕ) ≃ ℕ × (α → ℕ) := Equiv.piOptionEquivProd (β := fun _ => ℕ)
  have hmulN : Summable fun x : ℕ × (α → ℕ) => ‖f none x.1 * ∏ i, f (some i) (x.2 i)‖ :=
    Summable.mul_norm (f := f none) (g := fun w : α → ℕ => ∏ i, f (some i) (w i)) (hn none) h1
  have hmulS : Summable fun x : ℕ × (α → ℕ) => f none x.1 * ∏ i, f (some i) (x.2 i) :=
    hmulN.of_norm
  have hmul : HasSum (fun x : ℕ × (α → ℕ) => f none x.1 * ∏ i, f (some i) (x.2 i))
      (s none * ∏ i, s (some i)) :=
    HasSum.mul (f := f none) (g := fun w : α → ℕ => ∏ i, f (some i) (w i)) (hs none) h2 hmulS
  have hEw : ∀ w : Option α → ℕ, E w = (w none, fun i => w (some i)) := fun w => rfl
  refine ⟨?_, ?_⟩
  · have h3 := (Equiv.summable_iff E).mpr hmulN
    have hfun : ((fun x : ℕ × (α → ℕ) => ‖f none x.1 * ∏ i, f (some i) (x.2 i)‖) ∘ E) =
        fun w : Option α → ℕ => ‖∏ j, f j (w j)‖ := by
      funext w
      rw [Function.comp_apply, hEw, Fintype.prod_option (fun j => f j (w j))]
    rw [hfun] at h3
    exact h3
  · have h3 := (Equiv.hasSum_iff E).mpr hmul
    have hfun : ((fun x : ℕ × (α → ℕ) => f none x.1 * ∏ i, f (some i) (x.2 i)) ∘ E) =
        fun w : Option α → ℕ => ∏ j, f j (w j) := by
      funext w
      rw [Function.comp_apply, hEw, Fintype.prod_option (fun j => f j (w j))]
    rw [hfun, ← Fintype.prod_option s] at h3
    exact h3

private lemma hasSum_pi_prod (I : Type) [Fintype I] : PP I := by
  refine Fintype.induction_empty_option (P := fun (α : Type) [Fintype α] => PP α) ?_ ?_ ?_ I
  · intro α β _ e ih
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    exact PP_equiv α β e ih
  · exact PP_empty
  · intro α _ ih
    exact PP_option α ih

/-! ### The coherent vector: factorisation, bounds, continuity -/

/-- The normalisation weight `∏ⱼ 1/(√2^{mⱼ} √(mⱼ!))`. -/
private def wgt {n : ℕ} (m : Occupation (Fin n)) : ℂ :=
  ∏ j, ((Real.sqrt 2 : ℂ) ^ (m j) * (Real.sqrt (Nat.factorial (m j)) : ℂ))⁻¹

/-- The complex amplitude `γⱼ = β_{q,j} + i β_{p,j}`. -/
private def gam {n : ℕ} (β : Fin n ⊕ Fin n → ℝ) (j : Fin n) : ℂ :=
  (β (Sum.inl j) : ℂ) + Complex.I * (β (Sum.inr j) : ℂ)

/-- The Gaussian factor `∏ⱼ exp(-(β_{q,j}² + β_{p,j}²)/4)`. -/
private def gau {n : ℕ} (β : Fin n ⊕ Fin n → ℝ) : ℂ :=
  ∏ j : Fin n, ((Real.exp (-(β (Sum.inl j) ^ 2 + β (Sum.inr j) ^ 2) / 4) : ℝ) : ℂ)

private lemma wgt_ne_zero {n : ℕ} (m : Occupation (Fin n)) : wgt m ≠ 0 := by
  unfold wgt
  refine Finset.prod_ne_zero_iff.mpr fun j _ => inv_ne_zero (mul_ne_zero (pow_ne_zero _ ?_) ?_)
  · exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  · exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))

private lemma gau_ne_zero {n : ℕ} (β : Fin n ⊕ Fin n → ℝ) : gau β ≠ 0 := by
  unfold gau
  exact Finset.prod_ne_zero_iff.mpr fun j _ => Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'

private lemma coherent_factor {n : ℕ} (β : Fin n ⊕ Fin n → ℝ) (m : Occupation (Fin n)) :
    coherentVector β m = gau β * wgt m * ∏ j, gam β j ^ (m j) := by
  unfold coherentVector gau wgt gam
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [div_eq_mul_inv]
  ring

private lemma coherent_factor_star {n : ℕ} (β : Fin n ⊕ Fin n → ℝ) (m : Occupation (Fin n)) :
    star (coherentVector β m) = gau β * wgt m * ∏ j, (starRingEnd ℂ) (gam β j) ^ (m j) := by
  rw [coherent_factor, ← starRingEnd_apply, map_mul, map_mul, map_prod]
  have h1 : (starRingEnd ℂ) (gau β) = gau β := by
    unfold gau
    rw [map_prod]
    exact Finset.prod_congr rfl fun j _ => Complex.conj_ofReal _
  have h2 : (starRingEnd ℂ) (wgt m) = wgt m := by
    unfold wgt
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_inv₀, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_ofReal]
  rw [h1, h2]
  congr 1
  exact Finset.prod_congr rfl fun j _ => map_pow _ _ _

/-- The summand of the Husimi double series, factorised. -/
private lemma term_factor {n : ℕ} (D : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (β : Fin n ⊕ Fin n → ℝ) (u v : Occupation (Fin n)) :
    star (coherentVector β u) * D u v * coherentVector β v =
      gau β ^ 2 * ((D u v * wgt u * wgt v) *
        ∏ j, ((starRingEnd ℂ) (gam β j) ^ (u j) * gam β j ^ (v j))) := by
  rw [coherent_factor_star, coherent_factor, Finset.prod_mul_distrib]
  ring

/-- The majorant `∏ⱼ R^{mⱼ}/√(mⱼ!)`. -/
private def maj {n : ℕ} (R : ℝ) (m : Occupation (Fin n)) : ℝ :=
  ∏ j, R ^ (m j) / Real.sqrt (Nat.factorial (m j))

private lemma maj_nonneg {n : ℕ} {R : ℝ} (hR : 0 ≤ R) (m : Occupation (Fin n)) : 0 ≤ maj R m :=
  Finset.prod_nonneg fun _ _ => div_nonneg (pow_nonneg hR _) (Real.sqrt_nonneg _)

private lemma summable_pow_div_sqrt_factorial (R : ℝ) (hR : 0 ≤ R) :
    Summable fun k : ℕ => R ^ k / Real.sqrt (Nat.factorial k) := by
  have h1 := Real.summable_pow_div_factorial (4 * R ^ 2)
  have h2 : Summable fun k : ℕ => ((1 : ℝ) / 4) ^ k :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine Summable.of_nonneg_of_le (fun k => div_nonneg (pow_nonneg hR _) (Real.sqrt_nonneg _))
    (fun k => ?_) (h1.add h2)
  have hs : 0 < Real.sqrt (Nat.factorial k) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : Real.sqrt (Nat.factorial k) ^ 2 = (Nat.factorial k : ℝ) :=
    Real.sq_sqrt (by positivity)
  set s := Real.sqrt (Nat.factorial k) with hsdef
  have e1 : R ^ k / s = ((2 * R) ^ k / s) * ((1 : ℝ) / 2) ^ k := by
    rw [mul_pow, one_div, inv_pow]
    field_simp
  have e2 : (4 * R ^ 2) ^ k / (Nat.factorial k : ℝ) = ((2 * R) ^ k / s) ^ 2 := by
    rw [div_pow, hs2, ← pow_mul, mul_comm k 2, pow_mul]
    congr 2
    ring
  have e3 : ((1 : ℝ) / 4) ^ k = (((1 : ℝ) / 2) ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  rw [e1, e2, e3]
  nlinarith [sq_nonneg ((2 * R) ^ k / s - ((1 : ℝ) / 2) ^ k), sq_nonneg ((2 * R) ^ k / s),
    sq_nonneg (((1 : ℝ) / 2) ^ k)]

private lemma maj_summable {n : ℕ} (R : ℝ) (hR : 0 ≤ R) :
    Summable (maj (n := n) R) := by
  have hn : ∀ j : Fin n, Summable fun k : ℕ =>
      ‖(((R ^ k / Real.sqrt (Nat.factorial k) : ℝ)) : ℂ)‖ := by
    intro _
    refine (summable_pow_div_sqrt_factorial R hR).congr fun k => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (div_nonneg (pow_nonneg hR _) (Real.sqrt_nonneg _))]
  have key := (hasSum_pi_prod (Fin n)
    (fun _ k => (((R ^ k / Real.sqrt (Nat.factorial k) : ℝ)) : ℂ))
    (fun j => ∑' k, (((R ^ k / Real.sqrt (Nat.factorial k) : ℝ)) : ℂ)) hn
    (fun j => (hn j).of_norm.hasSum)).1
  refine key.congr fun m => ?_
  rw [norm_prod]
  unfold maj
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (div_nonneg (pow_nonneg hR _) (Real.sqrt_nonneg _))]

private lemma coherent_norm_le {n : ℕ} (β : Fin n ⊕ Fin n → ℝ) (R : ℝ)
    (hβ : ∀ j, ‖gam β j‖ ≤ R) (m : Occupation (Fin n)) :
    ‖coherentVector β m‖ ≤ maj R m := by
  unfold coherentVector maj
  rw [norm_prod]
  refine Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => ?_)
  have hg := hβ j
  unfold gam at hg
  have hs : 0 < Real.sqrt (Nat.factorial (m j)) := Real.sqrt_pos.mpr (by positivity)
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.one_le_sqrt]; norm_num
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  refine div_le_div₀ (pow_nonneg ((norm_nonneg _).trans hg) _) ?_ hs ?_
  · calc Real.exp (-(β (Sum.inl j) ^ 2 + β (Sum.inr j) ^ 2) / 4) *
          ‖(β (Sum.inl j) : ℂ) + Complex.I * (β (Sum.inr j) : ℂ)‖ ^ (m j)
        ≤ 1 * R ^ (m j) := by
          refine mul_le_mul ?_ (pow_le_pow_left₀ (norm_nonneg _) hg _)
            (pow_nonneg (norm_nonneg _) _) zero_le_one
          rw [Real.exp_le_one_iff]
          have : 0 ≤ β (Sum.inl j) ^ 2 + β (Sum.inr j) ^ 2 := by positivity
          linarith
      _ = R ^ (m j) := one_mul _
  · calc Real.sqrt (Nat.factorial (m j)) = 1 * Real.sqrt (Nat.factorial (m j)) := (one_mul _).symm
      _ ≤ Real.sqrt 2 ^ (m j) * Real.sqrt (Nat.factorial (m j)) :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ h2) hs.le

private lemma term_bound {n : ℕ} (D : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (C : ℝ) (hD : ∀ u v, ‖D u v‖ ≤ C) (β : Fin n ⊕ Fin n → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hβ : ∀ j, ‖gam β j‖ ≤ R) (p : Occupation (Fin n) × Occupation (Fin n)) :
    ‖star (coherentVector β p.1) * D p.1 p.2 * coherentVector β p.2‖ ≤
      C * (maj R p.1 * maj R p.2) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hD p.1 p.2)
  rw [norm_mul, norm_mul, norm_star]
  calc ‖coherentVector β p.1‖ * ‖D p.1 p.2‖ * ‖coherentVector β p.2‖
      ≤ maj R p.1 * C * maj R p.2 :=
        mul_le_mul (mul_le_mul (coherent_norm_le β R hβ p.1) (hD _ _) (norm_nonneg _)
          (maj_nonneg hR _)) (coherent_norm_le β R hβ p.2) (norm_nonneg _)
          (mul_nonneg (maj_nonneg hR _) hC)
    _ = C * (maj R p.1 * maj R p.2) := by ring

private lemma maj2_summable {n : ℕ} (C R : ℝ) (hR : 0 ≤ R) :
    Summable fun p : Occupation (Fin n) × Occupation (Fin n) => C * (maj R p.1 * maj R p.2) :=
  ((maj_summable R hR).mul_of_nonneg (maj_summable R hR) (maj_nonneg hR)
    (maj_nonneg hR)).mul_left C

private lemma gam_norm_le {n : ℕ} (β : Fin n ⊕ Fin n → ℝ) (j : Fin n) : ‖gam β j‖ ≤ 2 * ‖β‖ := by
  unfold gam
  calc ‖(β (Sum.inl j) : ℂ) + Complex.I * (β (Sum.inr j) : ℂ)‖
      ≤ ‖(β (Sum.inl j) : ℂ)‖ + ‖Complex.I * (β (Sum.inr j) : ℂ)‖ := norm_add_le _ _
    _ = ‖β (Sum.inl j)‖ + ‖β (Sum.inr j)‖ := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real]
    _ ≤ ‖β‖ + ‖β‖ := add_le_add (norm_le_pi_norm β _) (norm_le_pi_norm β _)
    _ = 2 * ‖β‖ := by ring

private lemma term_summable {n : ℕ} (D : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (C : ℝ) (hD : ∀ u v, ‖D u v‖ ≤ C) (β : Fin n ⊕ Fin n → ℝ) :
    Summable fun p : Occupation (Fin n) × Occupation (Fin n) =>
      star (coherentVector β p.1) * D p.1 p.2 * coherentVector β p.2 :=
  Summable.of_norm_bounded (maj2_summable C (2 * ‖β‖) (by positivity))
    (term_bound D C hD β _ (by positivity) (gam_norm_le β))

private lemma coherent_continuous {n : ℕ} (u : Occupation (Fin n)) :
    Continuous fun β : Fin n ⊕ Fin n → ℝ => coherentVector β u := by
  unfold coherentVector
  fun_prop

private lemma G_continuous {n : ℕ} (D : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (C : ℝ) (hD : ∀ u v, ‖D u v‖ ≤ C) :
    Continuous fun β : Fin n ⊕ Fin n → ℝ => ∑' p : Occupation (Fin n) × Occupation (Fin n),
      star (coherentVector β p.1) * D p.1 p.2 * coherentVector β p.2 := by
  refine continuous_iff_continuousAt.mpr fun β₀ => ?_
  have hR : 0 ≤ 2 * (‖β₀‖ + 1) := by positivity
  have hon : ContinuousOn (fun β : Fin n ⊕ Fin n → ℝ =>
      ∑' p : Occupation (Fin n) × Occupation (Fin n),
        star (coherentVector β p.1) * D p.1 p.2 * coherentVector β p.2) (Metric.ball β₀ 1) := by
    refine continuousOn_tsum (fun p => ?_) (maj2_summable C (2 * (‖β₀‖ + 1)) hR)
      (fun p β hβ => ?_)
    · exact (((continuous_star.comp (coherent_continuous p.1)).mul continuous_const).mul
        (coherent_continuous p.2)).continuousOn
    · refine term_bound D C hD β _ hR (fun j => (gam_norm_le β j).trans ?_) p
      have h1 : ‖β - β₀‖ < 1 := by rwa [mem_ball_iff_norm] at hβ
      have h2 : ‖β‖ ≤ ‖β₀‖ + ‖β - β₀‖ := by
        calc ‖β‖ = ‖β₀ + (β - β₀)‖ := by rw [add_sub_cancel]
          _ ≤ ‖β₀‖ + ‖β - β₀‖ := norm_add_le _ _
      linarith
  exact hon.continuousAt (Metric.ball_mem_nhds β₀ one_pos)

private lemma husimi_eq {n : ℕ} (D : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (C : ℝ) (hD : ∀ u v, ‖D u v‖ ≤ C) (β : Fin n ⊕ Fin n → ℝ) :
    husimiQ D β = (2 * Real.pi) ^ (-(n : ℝ)) *
      (∑' p : Occupation (Fin n) × Occupation (Fin n),
        star (coherentVector β p.1) * D p.1 p.2 * coherentVector β p.2).re := by
  unfold husimiQ
  rw [(term_summable D C hD β).tsum_prod]

private lemma husimi_continuous {n : ℕ} (D : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (C : ℝ) (hD : ∀ u v, ‖D u v‖ ≤ C) : Continuous (husimiQ D) := by
  have e : husimiQ D = fun β : Fin n ⊕ Fin n → ℝ => (2 * Real.pi) ^ (-(n : ℝ)) *
      (∑' p : Occupation (Fin n) × Occupation (Fin n),
        star (coherentVector β p.1) * D p.1 p.2 * coherentVector β p.2).re :=
    funext (husimi_eq D C hD)
  rw [e]
  exact continuous_const.mul (Complex.continuous_re.comp (G_continuous D C hD))

/-- For a Hermitian array the double series is real. -/
private lemma G_real {n : ℕ} (D : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (hherm : ∀ u v, D v u = star (D u v)) (β : Fin n ⊕ Fin n → ℝ) :
    (∑' p : Occupation (Fin n) × Occupation (Fin n),
      star (coherentVector β p.1) * D p.1 p.2 * coherentVector β p.2).im = 0 := by
  rw [← Complex.conj_eq_iff_im, Complex.conj_tsum, ← (Equiv.prodComm _ _).tsum_eq]
  refine tsum_congr fun p => ?_
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, map_mul]
  rw [hherm p.1 p.2]
  simp only [← starRingEnd_apply, Complex.conj_conj]
  ring

/-! ### Density operators: Hermitian symmetry and bounded entries -/

private lemma density_diag {I : Type} {X : Matrix I I ℂ} (hX : IsDensity X) (i : I) :
    (X i i).im = 0 ∧ 0 ≤ (X i i).re := by
  classical
  have h := hX.2.1 {i} (Pi.single i 1)
  simpa using h

private lemma density_herm {I : Type} {X : Matrix I I ℂ} (hX : IsDensity X) (i j : I) :
    X j i = star (X i j) := by
  classical
  by_cases hij : i = j
  · subst hij
    exact (Complex.conj_eq_iff_im.mpr (density_diag hX i).1).symm
  · have hji : j ≠ i := fun h => hij h.symm
    have hii := (density_diag hX i).1
    have hjj := (density_diag hX j).1
    have h1 := (hX.2.1 {i, j} (fun k => if k = i then 1 else if k = j then 1 else 0)).1
    have h2 := (hX.2.1 {i, j} (fun k => if k = i then 1 else if k = j then Complex.I else 0)).1
    simp [Finset.sum_pair hij, hji] at h1 h2
    apply Complex.ext
    · simp
      linarith
    · simp
      linarith

private lemma entry_bound {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) (i j : I) :
    ‖X i j‖ ≤ ∑' k, ‖e.left k‖ * ‖e.right k‖ := by
  rw [e.coefficients i j]
  have hle : ∀ k, ‖e.left k i * star (e.right k j)‖ ≤ ‖e.left k‖ * ‖e.right k‖ := by
    intro k
    rw [norm_mul, norm_star]
    exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) _ _)
      (lp.norm_apply_le_norm (by norm_num) _ _) (norm_nonneg _) (norm_nonneg _)
  have hs : Summable fun k => ‖e.left k i * star (e.right k j)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle e.summable
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hle e.summable)

/-! ### Equal characteristic functions give equal Husimi functions -/

private lemma charFun_density {ι : Type*} [Fintype ι] (Q : (ι → ℝ) → ℝ) (hQ0 : ∀ β, 0 ≤ Q β)
    (hQm : Measurable Q) (x : EuclideanSpace ℝ ι) :
    charFun ((volume : Measure (EuclideanSpace ℝ ι)).withDensity
        (fun β => ENNReal.ofReal (Q (WithLp.ofLp β)))) x =
      ∫ β : ι → ℝ, Complex.exp (Complex.I * ((∑ a, x a * β a : ℝ) : ℂ)) * ((Q β : ℝ) : ℂ) := by
  rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
  rw [← (PiLp.volume_preserving_ofLp ι).integral_comp
    (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
  simp [ENNReal.toReal_ofReal (hQ0 _), PiLp.inner_apply, mul_comm]

private lemma integrable_density {ι : Type*} [Fintype ι] (Q : (ι → ℝ) → ℝ) (hQi : Integrable Q) :
    Integrable (fun β : EuclideanSpace ℝ ι => Q (WithLp.ofLp β)) :=
  ((PiLp.volume_preserving_ofLp ι).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurableEmbedding).2 hQi

private lemma husimi_ae_eq {n : ℕ} (ρ σ : State (Occupation (Fin n)))
    (h : ∀ ξ : Fin n × Fin 2 → ℝ,
      oscillatorCharacteristic ρ.coefficients ξ = oscillatorCharacteristic σ.coefficients ξ) :
    (fun x : EuclideanSpace ℝ (Fin n ⊕ Fin n) => husimiQ ρ.coefficients (WithLp.ofLp x))
      =ᵐ[volume] fun x => husimiQ σ.coefficients (WithLp.ofLp x) := by
  obtain ⟨-, hQ0, hQm, hQi, hF⟩ := husimi_fourier ρ
  obtain ⟨-, hQ0', hQm', hQi', hF'⟩ := husimi_fourier σ
  have hfin : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin n))).withDensity
      (fun β => ENNReal.ofReal (husimiQ ρ.coefficients (WithLp.ofLp β)))) :=
    isFiniteMeasure_withDensity_ofReal (integrable_density _ hQi).2
  have hfin' : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin n))).withDensity
      (fun β => ENNReal.ofReal (husimiQ σ.coefficients (WithLp.ofLp β)))) :=
    isFiniteMeasure_withDensity_ofReal (integrable_density _ hQi').2
  have hμ : (volume : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin n))).withDensity
      (fun β => ENNReal.ofReal (husimiQ ρ.coefficients (WithLp.ofLp β))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin n))).withDensity
      (fun β => ENNReal.ofReal (husimiQ σ.coefficients (WithLp.ofLp β))) := by
    refine Measure.ext_of_charFun (funext fun x => ?_)
    rw [charFun_density _ hQ0 hQm x, charFun_density _ hQ0' hQm' x, hF, hF', h]
  have hae := (withDensity_eq_iff (by fun_prop) (by fun_prop)
    (integrable_density _ hQi).lintegral_lt_top.ne).mp hμ
  filter_upwards [hae] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (hQ0 _) (hQ0' _)).mp hx

end

/-! ### The theorem -/

theorem solution {n : ℕ} (ρ σ : State (Occupation (Fin n)))
    (h : ∀ ξ : Fin n × Fin 2 → ℝ,
      oscillatorCharacteristic ρ.coefficients ξ = oscillatorCharacteristic σ.coefficients ξ) :
    ρ.coefficients = σ.coefficients := by
  obtain ⟨eρ⟩ := ρ.density.1
  obtain ⟨eσ⟩ := σ.density.1
  have hbρ := entry_bound eρ
  have hbσ := entry_bound eσ
  -- the Husimi functions agree everywhere
  have hQ : ∀ β : Fin n ⊕ Fin n → ℝ, husimiQ ρ.coefficients β = husimiQ σ.coefficients β := by
    have hc1 : Continuous fun x : EuclideanSpace ℝ (Fin n ⊕ Fin n) =>
        husimiQ ρ.coefficients (WithLp.ofLp x) :=
      (husimi_continuous _ _ hbρ).comp (PiLp.continuous_ofLp 2 _)
    have hc2 : Continuous fun x : EuclideanSpace ℝ (Fin n ⊕ Fin n) =>
        husimiQ σ.coefficients (WithLp.ofLp x) :=
      (husimi_continuous _ _ hbσ).comp (PiLp.continuous_ofLp 2 _)
    have heq := (Continuous.ae_eq_iff_eq volume hc1 hc2).mp (husimi_ae_eq ρ σ h)
    intro β
    exact congrFun heq (WithLp.toLp 2 β)
  -- the complex double series agree
  have hG : ∀ β : Fin n ⊕ Fin n → ℝ,
      (∑' p : Occupation (Fin n) × Occupation (Fin n),
        star (coherentVector β p.1) * ρ.coefficients p.1 p.2 * coherentVector β p.2) =
      ∑' p : Occupation (Fin n) × Occupation (Fin n),
        star (coherentVector β p.1) * σ.coefficients p.1 p.2 * coherentVector β p.2 := by
    intro β
    have h1 := hQ β
    rw [husimi_eq _ _ hbρ, husimi_eq _ _ hbσ] at h1
    have hpos : (2 * Real.pi) ^ (-(n : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
    apply Complex.ext
    · exact mul_left_cancel₀ hpos h1
    · rw [G_real _ (density_herm ρ.density) β, G_real _ (density_herm σ.density) β]
  -- the series of the difference vanishes
  have hH : ∀ β : Fin n ⊕ Fin n → ℝ,
      HasSum (fun p : Occupation (Fin n) × Occupation (Fin n) =>
        star (coherentVector β p.1) * (ρ.coefficients p.1 p.2 - σ.coefficients p.1 p.2) *
          coherentVector β p.2) 0 := by
    intro β
    have h1 := (term_summable _ _ hbρ β).hasSum.sub (term_summable _ _ hbσ β).hasSum
    rw [hG β, sub_self] at h1
    have e : (fun p : Occupation (Fin n) × Occupation (Fin n) =>
        star (coherentVector β p.1) * (ρ.coefficients p.1 p.2 - σ.coefficients p.1 p.2) *
          coherentVector β p.2) = fun p =>
        star (coherentVector β p.1) * ρ.coefficients p.1 p.2 * coherentVector β p.2 -
          star (coherentVector β p.1) * σ.coefficients p.1 p.2 * coherentVector β p.2 := by
      funext p
      ring
    rw [e]
    exact h1
  -- uniqueness of the power series
  have key := PU_all (Fin n)
    (fun u v => (ρ.coefficients u v - σ.coefficients u v) * wgt u * wgt v) (fun γ => ?_)
  · funext u v
    have h1 := key u v
    simp only [mul_eq_zero, wgt_ne_zero, or_false] at h1
    exact sub_eq_zero.mp h1
  · let β : Fin n ⊕ Fin n → ℝ := Sum.elim (fun j => (γ j).re) (fun j => (γ j).im)
    have hγ : ∀ j, gam β j = γ j := by
      intro j
      show ((γ j).re : ℂ) + Complex.I * ((γ j).im : ℂ) = γ j
      rw [mul_comm]
      exact Complex.re_add_im (γ j)
    have h1 := (hH β).mul_left ((gau β ^ 2)⁻¹)
    rw [mul_zero] at h1
    have e : (fun p : Occupation (Fin n) × Occupation (Fin n) =>
        (ρ.coefficients p.1 p.2 - σ.coefficients p.1 p.2) * wgt p.1 * wgt p.2 *
          ∏ i, ((starRingEnd ℂ) (γ i) ^ p.1 i * γ i ^ p.2 i)) = fun p =>
        (gau β ^ 2)⁻¹ * (star (coherentVector β p.1) *
          (ρ.coefficients p.1 p.2 - σ.coefficients p.1 p.2) * coherentVector β p.2) := by
      funext p
      have ht := term_factor (ρ.coefficients - σ.coefficients) β p.1 p.2
      simp only [Matrix.sub_apply] at ht
      rw [ht, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (gau_ne_zero β)), one_mul]
      simp only [hγ]
    rw [e]
    exact h1
