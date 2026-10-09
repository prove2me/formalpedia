-- Prove2me | solution 1 for BarvinokCount.ShortFormula.latticeCount_eq_short_signed_sum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T16:27:47.4478+00:00
-- url     : https://prove2.me/submissions/ce0124f3-6f0c-46a0-b11e-08245f531556
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BarvinokCount_ShortFormula_sigma
import Definitions.Def_BarvinokCount_ShortFormula_integralSimplex
import Definitions.Def_BarvinokCount_ShortFormula_iterCount
import Theorems.Thm_BarvinokCount_ShortFormula_brion_simplex
import Theorems.Thm_BarvinokCount_ShortFormula_exists_primitive_signed_decomposition
import Theorems.Thm_BarvinokCount_ShortFormula_constTerm_primitive_eq_poly
import Theorems.Thm_BarvinokCount_ShortFormula_exists_moment_vector_not_orthogonal
set_option autoImplicit false
open scoped Topology
open Filter

namespace BarvinokCount.ShortFormula

/-- Laurent constant term with a fixed exponent. -/
def LCTAt (f : ℝ → ℝ) (a : ℝ) (K : ℕ) : Prop :=
  ∃ φ : ℝ → ℝ, AnalyticAt ℝ φ 0 ∧ (∀ᶠ t in 𝓝[≠] (0 : ℝ), φ t = t ^ K * f t) ∧
    a = iteratedDeriv K φ 0 / (K.factorial : ℝ)

lemma lct_shift (φ : ℝ → ℝ) (hφ : AnalyticAt ℝ φ 0) (N M : ℕ) :
    iteratedDeriv (N + M) (fun t => t ^ M * φ t) 0 / ((N + M).factorial : ℝ) =
      iteratedDeriv N φ 0 / (N.factorial : ℝ) := by
  have h1 : ContDiffAt ℝ (N + M) (fun t : ℝ => t ^ M) 0 := by fun_prop
  have h2 : ContDiffAt ℝ (N + M) φ 0 := hφ.contDiffAt
  rw [iteratedDeriv_fun_mul h1 h2]
  rw [Finset.sum_eq_single M]
  · rw [iteratedDeriv_fun_pow_zero]
    simp only [if_true, Nat.add_sub_cancel]
    have hc : ((N + M).choose M : ℝ) * (M.factorial : ℝ) * (N.factorial : ℝ) = ((N + M).factorial : ℝ) := by
      have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left M N)
      rw [Nat.add_sub_cancel] at this
      exact_mod_cast this
    have hN : (N.factorial : ℝ) ≠ 0 := by positivity
    have hNM : ((N + M).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    rw [← hc]; ring
  · intro b _ hb
    rw [iteratedDeriv_fun_pow_zero, if_neg hb]; ring
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_add_left M N))) h

lemma LCTAt.raise {f : ℝ → ℝ} {a : ℝ} {N : ℕ} (h : LCTAt f a N) (K : ℕ) (hK : N ≤ K) :
    LCTAt f a K := by
  obtain ⟨φ, hφ, he, ha⟩ := h
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hK
  refine ⟨fun t => t ^ M * φ t, (analyticAt_id.pow M).mul hφ, ?_, ?_⟩
  · filter_upwards [he] with t ht
    rw [ht, pow_add]; ring
  · rw [lct_shift φ hφ N M, ha]

lemma LCTAt.unique {f : ℝ → ℝ} {a b : ℝ} {K : ℕ} (ha : LCTAt f a K) (hb : LCTAt f b K) :
    a = b := by
  obtain ⟨φ, hφ, he, rfl⟩ := ha
  obtain ⟨ψ, hψ, he', rfl⟩ := hb
  have hpe : φ =ᶠ[𝓝[≠] (0 : ℝ)] ψ := by
    filter_upwards [he, he'] with t h1 h2
    rw [h1, h2]
  have h0 : φ 0 = ψ 0 := by
    have t1 : Tendsto φ (𝓝[≠] (0 : ℝ)) (𝓝 (φ 0)) :=
      hφ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have t2 : Tendsto ψ (𝓝[≠] (0 : ℝ)) (𝓝 (ψ 0)) :=
      hψ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (t1.congr' hpe) t2
  have hn : φ =ᶠ[𝓝 (0 : ℝ)] ψ := by
    have := eventually_nhdsWithin_iff.mp hpe
    filter_upwards [this] with t ht
    by_cases h : t = 0
    · subst h; exact h0
    · exact ht h
  rw [hn.iteratedDeriv_eq]

lemma LCTAt.congr {f g : ℝ → ℝ} {a : ℝ} {K : ℕ} (h : LCTAt f a K)
    (hfg : ∀ᶠ t in 𝓝[≠] (0 : ℝ), f t = g t) : LCTAt g a K := by
  obtain ⟨φ, hφ, he, ha⟩ := h
  refine ⟨φ, hφ, ?_, ha⟩
  filter_upwards [he, hfg] with t h1 h2
  rw [h1, h2]

lemma LCTAt.const_mul {f : ℝ → ℝ} {a : ℝ} {K : ℕ} (h : LCTAt f a K) (c : ℝ) :
    LCTAt (fun t => c * f t) (c * a) K := by
  obtain ⟨φ, hφ, he, ha⟩ := h
  refine ⟨fun t => c * φ t, analyticAt_const.mul hφ, ?_, ?_⟩
  · filter_upwards [he] with t ht
    rw [ht]; ring
  · rw [iteratedDeriv_const_mul_field, ha]; ring

lemma LCTAt.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (a : ι → ℝ) {K : ℕ}
    (h : ∀ i ∈ s, LCTAt (f i) (a i) K) :
    LCTAt (fun t => ∑ i ∈ s, f i t) (∑ i ∈ s, a i) K := by
  classical
  choose φ hφ he ha using h
  let Φ : ι → ℝ → ℝ := fun i => if hi : i ∈ s then φ i hi else 0
  have hΦa : ∀ i ∈ s, AnalyticAt ℝ (Φ i) 0 := by
    intro i hi; simp only [Φ, dif_pos hi]; exact hφ i hi
  refine ⟨fun t => ∑ i ∈ s, Φ i t, Finset.analyticAt_fun_sum _ hΦa, ?_, ?_⟩
  · have : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ i ∈ s, Φ i t = t ^ K * f i t := by
      rw [Finset.eventually_all]
      intro i hi
      simp only [Φ, dif_pos hi]
      exact he i hi
    filter_upwards [this] with t ht
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl ht
  · rw [iteratedDeriv_fun_sum (fun i hi => (hΦa i hi).contDiffAt), Finset.sum_div]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [Φ, dif_pos hi]
    exact ha i hi

lemma LCTAt.toLaurent {f : ℝ → ℝ} {a : ℝ} {K : ℕ} (h : LCTAt f a K) : IsLaurentConstTerm f a :=
  ⟨K, h⟩

lemma LCTAt.ofLaurent {f : ℝ → ℝ} {a : ℝ} (h : IsLaurentConstTerm f a) : ∃ N, LCTAt f a N := h

lemma LCTAt.ofAnalytic {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) : LCTAt f (f 0) 0 := by
  refine ⟨f, hf, ?_, ?_⟩
  · exact Eventually.of_forall (fun t => by simp)
  · simp


lemma castVec_sub' {d : ℕ} (a b : Fin d → ℤ) : castVec (a - b) = castVec a - castVec b := by
  funext l; simp [castVec]

theorem supportingCone_simplex_eq_cone' {d k : ℕ} (v : Fin (k + 1) → Fin d → ℤ)
    (j : Fin (k + 1)) :
    supportingCone (simplex v) (castVec (v j)) = cone (edgeGens v j) := by
  classical
  set x : Fin (k + 1) → (Fin d → ℝ) := fun l => castVec (v l) with hxdef
  have hedge : ∀ a, castVec (edgeGens v j a) = x (j.succAbove a) - x j :=
    fun a => castVec_sub' _ _
  have hS : simplex v = convexHull ℝ (Set.range x) := rfl
  ext u
  constructor
  · rintro ⟨δ, hδ, hmem⟩
    have hx := hmem δ hδ le_rfl
    rw [hS, convexHull_range_eq_exists_affineCombination] at hx
    obtain ⟨s, w, hw0, hw1, hcomb⟩ := hx
    let μ : Fin (k + 1) → ℝ := fun i => if i ∈ s then w i else 0
    have hμ0 : ∀ i, 0 ≤ μ i := fun i => by
      by_cases hi : i ∈ s
      · simp only [μ, if_pos hi]; exact hw0 i hi
      · simp only [μ, if_neg hi]; exact le_rfl
    have hμ1 : ∑ i, μ i = 1 := by
      rw [← hw1]; simp only [μ]; rw [Finset.sum_ite_mem, Finset.univ_inter]
    have hsum : x j + δ • u = ∑ i, μ i • x i := by
      rw [← hcomb, Finset.affineCombination_eq_linear_combination s _ _ hw1]
      simp only [μ, ite_smul, zero_smul]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have e1 : ∑ i, μ i • x i = μ j • x j + ∑ a, μ (j.succAbove a) • x (j.succAbove a) :=
      Fin.sum_univ_succAbove _ j
    have e2 : ∑ i, μ i = μ j + ∑ a, μ (j.succAbove a) := Fin.sum_univ_succAbove _ j
    have key : δ • u = ∑ a, μ (j.succAbove a) • (x (j.succAbove a) - x j) := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
      have h3 : ∑ a, μ (j.succAbove a) = 1 - μ j := by linarith
      rw [h3]
      rw [e1] at hsum
      linear_combination (norm := module) hsum
    refine ⟨fun a => μ (j.succAbove a) / δ, fun a => div_nonneg (hμ0 _) hδ.le, ?_⟩
    calc u = δ⁻¹ • (δ • u) := by rw [smul_smul, inv_mul_cancel₀ hδ.ne', one_smul]
      _ = _ := by
        rw [key, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [hedge, smul_smul]
        simp only [div_eq_inv_mul]
  · rintro ⟨lam, hlam, rfl⟩
    set L := ∑ a, lam a with hLdef
    have hL : 0 ≤ L := Finset.sum_nonneg (fun a _ => hlam a)
    refine ⟨1 / (1 + L), by positivity, fun δ hδ hδle => ?_⟩
    have hδL : δ * L ≤ 1 := by
      have h1 : δ * (1 + L) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hδle
      nlinarith
    let μ : Fin (k + 1) → ℝ := j.insertNth (1 - δ * L) (fun a => δ * lam a)
    have hμ0 : ∀ i, 0 ≤ μ i := by
      refine Fin.succAboveCases j ?_ ?_
      · simp only [μ, Fin.insertNth_apply_same]; linarith
      · intro a; simp only [μ, Fin.insertNth_apply_succAbove]; exact mul_nonneg hδ.le (hlam a)
    have hμ1 : ∑ i, μ i = 1 := by
      rw [Fin.sum_univ_succAbove _ j]
      simp only [μ, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      rw [← Finset.mul_sum]; ring
    have hx : x j + δ • ∑ a, lam a • castVec (edgeGens v j a) = ∑ i, μ i • x i := by
      rw [Fin.sum_univ_succAbove _ j]
      simp only [μ, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, hedge]
      have h4 : δ • ∑ a, lam a • (x (j.succAbove a) - x j) =
          ∑ a, (δ * lam a) • x (j.succAbove a) - (δ * L) • x j := by
        rw [Finset.smul_sum, hLdef, Finset.mul_sum, Finset.sum_smul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        first | module
      rw [h4]
      first | module
    show x j + δ • ∑ a, lam a • castVec (edgeGens v j a) ∈ simplex v
    rw [hx, hS]
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => hμ0 i) hμ1
      (fun i _ => subset_convexHull ℝ _ (Set.mem_range_self i))

lemma finsum_exp_eq {d : ℕ} (S : Set (Fin d → ℤ)) :
    ∃ T : Finset (Fin d → ℤ), S.ncard = T.card ∧ ∀ c : Fin d → ℝ,
      ∑ᶠ z ∈ S, Real.exp (c ⬝ᵥ castVec z) = ∑ z ∈ T, Real.exp (c ⬝ᵥ castVec z) := by
  by_cases hS : S.Finite
  · exact ⟨hS.toFinset, Set.ncard_eq_toFinset_card S hS,
      fun c => finsum_mem_eq_finite_toFinset_sum _ hS⟩
  · refine ⟨∅, by simp [Set.Infinite.ncard hS], fun c => ?_⟩
    rw [Finset.sum_empty]
    apply finsum_mem_eq_zero_of_infinite
    have : Function.support (fun z : Fin d → ℤ => Real.exp (c ⬝ᵥ castVec z)) = Set.univ := by
      ext z; simp [(Real.exp_pos _).ne']
    rw [this, Set.inter_univ]; exact hS

lemma contAt_finsum_exp {d : ℕ} (S : Set (Fin d → ℤ)) (P : ℝ → Fin d → ℝ) (hP : Continuous P) :
    Continuous (fun s => ∑ᶠ z ∈ S, Real.exp (P s ⬝ᵥ castVec z)) := by
  obtain ⟨T, -, hT⟩ := finsum_exp_eq S
  simp only [hT]
  exact continuous_finsetSum _ (fun z _ =>
    Real.continuous_exp.comp (hP.dotProduct continuous_const))

lemma sigma_contAt {d n : ℕ} (u : Fin n → Fin d → ℤ) (P : ℝ → Fin d → ℝ) (hP : Continuous P)
    (hc0 : IsRegular u (P 0)) : ContinuousAt (fun s => sigma u (P s)) 0 := by
  unfold sigma
  apply ContinuousAt.mul
  · exact (contAt_finsum_exp _ P hP).continuousAt
  · apply tendsto_finsetProd
    intro i _
    apply ContinuousAt.div continuousAt_const
    · exact (continuousAt_const.sub (Real.continuous_exp.comp
        (hP.dotProduct continuous_const)).continuousAt)
    · intro h
      apply hc0 i
      have h' : Real.exp (P 0 ⬝ᵥ castVec (u i)) = 1 := by linarith
      exact Real.exp_eq_one_iff _ |>.mp h'

end BarvinokCount.ShortFormula

open BarvinokCount.ShortFormula in
theorem solution {d k : ℕ} (hd : 2 ≤ d)
    (v : Fin (k + 1) → Fin d → ℤ) (hv : AffineIndependent ℝ fun j => castVec (v j)) :
    ∃ (N : Fin (k + 1) → ℕ) (m : (j : Fin (k + 1)) → Fin (N j) → ℕ)
      (g : (j : Fin (k + 1)) → (i : Fin (N j)) → Fin (m j i) → Fin d → ℤ)
      (ε : (j : Fin (k + 1)) → Fin (N j) → ℤ),
      (∀ j i, IsPrimitiveGens (g j i)) ∧
      (∀ j, N j ≤ (2 ^ d) ^ iterCount d (coneIndex (edgeGens v j))) ∧
      (∀ j, IsSignedConeDecomp (supportingCone (simplex v) (castVec (v j))) (g j) (ε j)) ∧
      ∀ c : Fin d → ℝ, (∀ j i, IsRegular (g j i) c) →
        ∃ R : (j : Fin (k + 1)) → Fin (N j) → ℝ,
          (∀ j i, IsLaurentConstTerm
            (fun t => Real.exp (t * (c ⬝ᵥ castVec (v j))) * sigma (g j i) (t • c)) (R j i)) ∧
          (latticeCount (simplex v) : ℝ) = ∑ j, ∑ i, (ε j i : ℝ) * R j i := by
  classical
  set x : Fin (k + 1) → (Fin d → ℝ) := fun l => castVec (v l) with hxdef
  have hedge : ∀ j a, castVec (edgeGens v j a) = x (j.succAbove a) - x j :=
    fun j a => castVec_sub' _ _
  have hinj : Function.Injective x := hv.injective
  have hedge0 : ∀ j a, castVec (edgeGens v j a) ≠ 0 := by
    intro j a h
    rw [hedge, sub_eq_zero] at h
    exact Fin.succAbove_ne j a (hinj h)
  -- simplicity of the edge generators
  have hsimple : ∀ j, IsSimpleGens (edgeGens v j) := by
    intro j
    have hli := (affineIndependent_iff_linearIndependent_vsub ℝ x j).mp hv
    have hcomp := hli.comp (fun a : Fin k => (⟨j.succAbove a, Fin.succAbove_ne j a⟩ : {y // y ≠ j}))
      (fun a b hab => Fin.succAbove_right_injective (congrArg Subtype.val hab))
    have hfun : (fun a => castVec (edgeGens v j a)) =
        ((fun i : {y // y ≠ j} => x ↑i -ᵥ x j) ∘
          fun a : Fin k => (⟨j.succAbove a, Fin.succAbove_ne j a⟩ : {y // y ≠ j})) := by
      funext a
      simp only [Function.comp_apply, vsub_eq_sub]
      exact hedge j a
    unfold IsSimpleGens
    rw [hfun]
    exact hcomp
  -- a direction orthogonal to no edge
  obtain ⟨w, hw⟩ : ∃ w : Fin d → ℝ, ∀ j a, w ⬝ᵥ castVec (edgeGens v j a) ≠ 0 := by
    let uq : Fin ((k + 1) * k) → Fin d → ℚ := fun n l =>
      ((edgeGens v (finProdFinEquiv.symm n).1 (finProdFinEquiv.symm n).2 l : ℤ) : ℚ)
    have huq : ∀ n, uq n ≠ 0 := by
      intro n h
      apply hedge0 (finProdFinEquiv.symm n).1 (finProdFinEquiv.symm n).2
      funext l
      have := congrFun h l
      simp only [uq, Pi.zero_apply, Int.cast_eq_zero] at this
      simp only [castVec, Pi.zero_apply, this, Int.cast_zero]
    obtain ⟨t, -, ht⟩ := exists_moment_vector_not_orthogonal d ((k + 1) * k) uq huq
    refine ⟨fun l => (t : ℝ) ^ (l : ℕ), fun j a h => ht (finProdFinEquiv (j, a)) ?_⟩
    have hq : (((fun l : Fin d => (t : ℚ) ^ (l : ℕ)) ⬝ᵥ uq (finProdFinEquiv (j, a)) : ℚ) : ℝ) =
        (fun l : Fin d => (t : ℝ) ^ (l : ℕ)) ⬝ᵥ castVec (edgeGens v j a) := by
      simp only [uq, Equiv.symm_apply_apply]
      simp [dotProduct, castVec]
    rw [h] at hq
    exact_mod_cast hq
  choose N m g ε hN hprim hdec hsig using
    fun j => exists_primitive_signed_decomposition hd (edgeGens v j) (hsimple j)
  refine ⟨N, m, g, ε, fun j i => hprim j i, hN, fun j => ?_, ?_⟩
  · rw [supportingCone_simplex_eq_cone']; exact hdec j
  intro c hc
  have hR : ∀ j i, ∃ r, IsLaurentConstTerm
      (fun t => Real.exp (t * (c ⬝ᵥ castVec (v j))) * sigma (g j i) (t • c)) r := by
    intro j i
    obtain ⟨Q, -, hQ⟩ := constTerm_primitive_eq_poly (m j i)
    exact ⟨_, hQ d (g j i) (hprim j i) (v j) c (hc j i)⟩
  choose R hRl using hR
  refine ⟨R, hRl, ?_⟩
  set S : Set (Fin d → ℤ) := {z | castVec z ∈ simplex v} with hSdef
  -- the identity at every point regular for all the g j i
  have ident : ∀ c0 : Fin d → ℝ, (∀ j i, IsRegular (g j i) c0) →
      ∑ᶠ z ∈ S, Real.exp (c0 ⬝ᵥ castVec z) =
        ∑ j, Real.exp (c0 ⬝ᵥ x j) * ∑ i, (ε j i : ℝ) * sigma (g j i) c0 := by
    intro c0 hc0
    let P : ℝ → Fin d → ℝ := fun s => c0 + s • w
    have hPc : Continuous P := by fun_prop
    have hP0 : P 0 = c0 := by simp [P]
    have hdotP : ∀ (e : Fin d → ℝ) (s : ℝ), P s ⬝ᵥ e = c0 ⬝ᵥ e + s * (w ⬝ᵥ e) := by
      intro e s; simp [P, add_dotProduct, smul_dotProduct]
    have hE : ∀ᶠ s in 𝓝[≠] (0 : ℝ), ∀ j, IsRegular (edgeGens v j) (P s) := by
      simp only [BarvinokCount.ShortFormula.IsRegular, Filter.eventually_all]
      intro j a
      by_cases h0 : c0 ⬝ᵥ castVec (edgeGens v j a) = 0
      · filter_upwards [self_mem_nhdsWithin] with s hs
        rw [hdotP, h0, zero_add]; exact mul_ne_zero hs (hw j a)
      · have hcont : ContinuousAt (fun s => P s ⬝ᵥ castVec (edgeGens v j a)) 0 :=
          (hPc.dotProduct continuous_const).continuousAt
        have := hcont.eventually_ne (by simpa [hP0] using h0)
        exact nhdsWithin_le_nhds this
    have hG : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ j i, IsRegular (g j i) (P s) := by
      simp only [BarvinokCount.ShortFormula.IsRegular, Filter.eventually_all]
      intro j i l
      have hcont : ContinuousAt (fun s => P s ⬝ᵥ castVec (g j i l)) 0 :=
        (hPc.dotProduct continuous_const).continuousAt
      exact hcont.eventually_ne (by simpa [hP0] using hc0 j i l)
    have heq : ∀ᶠ s in 𝓝[≠] (0 : ℝ), ∑ᶠ z ∈ S, Real.exp (P s ⬝ᵥ castVec z) =
        ∑ j, Real.exp (P s ⬝ᵥ x j) * ∑ i, (ε j i : ℝ) * sigma (g j i) (P s) := by
      filter_upwards [hE, nhdsWithin_le_nhds hG] with s h1 h2
      rw [brion_simplex v hv (P s) h1]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hsig j (P s) (h1 j) (h2 j)]
    have hLc : ContinuousAt (fun s => ∑ᶠ z ∈ S, Real.exp (P s ⬝ᵥ castVec z)) 0 :=
      (contAt_finsum_exp S P hPc).continuousAt
    have hRc : ContinuousAt (fun s => ∑ j, Real.exp (P s ⬝ᵥ x j) *
        ∑ i, (ε j i : ℝ) * sigma (g j i) (P s)) 0 := by
      apply tendsto_finsetSum
      intro j _
      apply ContinuousAt.mul
      · exact (Real.continuous_exp.comp (hPc.dotProduct continuous_const)).continuousAt
      · apply tendsto_finsetSum
        intro i _
        exact continuousAt_const.mul (sigma_contAt (g j i) P hPc (by rw [hP0]; exact hc0 j i))
    have := tendsto_nhds_unique ((hLc.tendsto.mono_left nhdsWithin_le_nhds).congr' heq)
      (hRc.tendsto.mono_left nhdsWithin_le_nhds)
    simpa [hP0] using this
  -- the Laurent bookkeeping
  let f : ℝ → ℝ := fun t => ∑ᶠ z ∈ S, Real.exp ((t • c) ⬝ᵥ castVec z)
  obtain ⟨T, hTcard, hT⟩ := finsum_exp_eq S
  have hf : AnalyticAt ℝ f 0 := by
    have : f = fun t => ∑ z ∈ T, Real.exp (t * (c ⬝ᵥ castVec z)) := by
      funext t; simp only [f]; rw [hT]; simp only [smul_dotProduct, smul_eq_mul]
    rw [this]
    apply Finset.analyticAt_fun_sum
    intro z _
    fun_prop
  have hf0 : f 0 = (latticeCount (simplex v) : ℝ) := by
    simp only [f, hT, zero_smul, zero_dotProduct, Real.exp_zero, Finset.sum_const, nsmul_eq_mul,
      mul_one]
    rw [← hTcard]
    rfl
  choose K' hK' using fun j i => LCTAt.ofLaurent (hRl j i)
  set K := ∑ j, ∑ i, K' j i with hKdef
  have hle : ∀ j i, K' j i ≤ K := by
    intro j i
    exact (Finset.single_le_sum (f := fun i => K' j i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun j => ∑ i, K' j i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j))
  have h1 : LCTAt f (f 0) K := (LCTAt.ofAnalytic hf).raise K (Nat.zero_le _)
  have h2 : LCTAt (fun t => ∑ j, ∑ i, (ε j i : ℝ) *
      (Real.exp (t * (c ⬝ᵥ castVec (v j))) * sigma (g j i) (t • c)))
      (∑ j, ∑ i, (ε j i : ℝ) * R j i) K :=
    LCTAt.sum _ _ _ (fun j _ => LCTAt.sum _ _ _ (fun i _ =>
      ((hK' j i).raise K (hle j i)).const_mul _))
  have h3 : LCTAt f (∑ j, ∑ i, (ε j i : ℝ) * R j i) K := by
    refine h2.congr ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hreg : ∀ j i, IsRegular (g j i) (t • c) := by
      intro j i l
      rw [smul_dotProduct, smul_eq_mul]
      exact mul_ne_zero ht (hc j i l)
    simp only [f]
    rw [ident (t • c) hreg]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [x, smul_dotProduct, smul_eq_mul]
    ring
  rw [← hf0]
  exact h1.unique h3

