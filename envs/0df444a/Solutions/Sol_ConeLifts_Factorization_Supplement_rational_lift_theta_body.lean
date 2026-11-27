-- Prove2me | solution 1 for ConeLifts.Factorization.Supplement.rational_lift_theta_body
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:28:03.791194+00:00
-- url     : https://prove2.me/submissions/ac7a69e2-e80c-4d34-933d-5fa463f93b23

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Factorization_Supplement_IsConvexRadical
import Definitions.Def_ConeLifts_Factorization_Supplement_thetaBody
import Definitions.Def_ConeLifts_Factorization_Supplement_HasRationalFactorization

open ConeLifts
open ConeLifts.Factorization
open ConeLifts.Factorization.Supplement

/-- **Theorem 5.6** of Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 21. Let `I` be a convex
radical ideal and `Z = 𝒱_ℝ(I)` with `conv(Z)` compact and containing the origin (in its interior,
the paper's standing convex-body assumption, restated on pp. 21–22). Then

1. the slack operator of `conv(Z)` has a rational factorization with
   `A(x) = (1/p(x)²) w(x) w(x)ᵀ ∈ Sᵏ₊` iff for every linear polynomial `ℓ` nonnegative over `Z`,
   `p² ℓ` is a sum of squares modulo `I` of linear combinations of the entries of `w`;
2. the slack operator of `conv(Z)` has a polynomial factorization `A(x) = w(x) w(x)ᵀ` with every
   entry of `w` of degree at most `k` iff `TH_k(I) = conv(Z)`.

Recorded repair in (1): `p(x) ≠ 0` for every `x ∈ ext(conv Z)`, which the form `1/p(x)²` of `A`
presupposes. In (2) the size `r` of the matrices is free; `k` is the degree bound. "Linear
polynomial" means total degree at most one. -/
theorem solution {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℝ))
    (hI : IsConvexRadical I)
    (hC : ConeLifts.Factorization.IsConvexBody (convexHull ℝ (realZeroSet I))) :
    (∀ (k : ℕ) (p : MvPolynomial (Fin n) ℝ) (w : Fin k → MvPolynomial (Fin n) ℝ),
      (∀ x ∈ Set.extremePoints ℝ (convexHull ℝ (realZeroSet I)), polyEval x p ≠ 0) →
      (HasRationalFactorization (convexHull ℝ (realZeroSet I)) p w ↔
        ∀ ℓ : MvPolynomial (Fin n) ℝ, ℓ.totalDegree ≤ 1 →
          (∀ z ∈ realZeroSet I, 0 ≤ polyEval z ℓ) →
            IsSosModulo I (Submodule.span ℝ (Set.range w) : Set (MvPolynomial (Fin n) ℝ))
              (p ^ 2 * ℓ))) ∧
    (∀ k : ℕ,
      (∃ (r : ℕ) (w : Fin r → MvPolynomial (Fin n) ℝ), (∀ i, (w i).totalDegree ≤ k) ∧
          HasRationalFactorization (convexHull ℝ (realZeroSet I)) 1 w) ↔
        thetaBody I k = convexHull ℝ (realZeroSet I)) := by
          classical
          have hEZ : Set.extremePoints ℝ (convexHull ℝ (realZeroSet I)) ⊆ realZeroSet I :=
            extremePoints_convexHull_subset
          have hmemI : ∀ f, f ∈ I ↔ ∀ x ∈ Set.extremePoints ℝ (convexHull ℝ (realZeroSet I)),
              polyEval x f = 0 := by
            intro f
            rw [← SetLike.mem_coe, hI]
            simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
            exact ⟨fun h x hx => h x ⟨hEZ hx, hx⟩, fun h x hx => h x hx.2⟩
          -- trace of a rank one times a sum of rank ones
          have htr : ∀ (k : ℕ) (c : ℝ) (u : Fin k → ℝ) (m : ℕ) (v : Fin m → Fin k → ℝ),
              ((c • Matrix.vecMulVec u u) * ∑ t, Matrix.vecMulVec (v t) (star (v t))).trace
                = c * ∑ t, (∑ j, v t j * u j) ^ 2 := by
            intro k c u m v
            simp only [Matrix.trace, Matrix.mul_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
              Matrix.sum_apply, star_trivial, smul_eq_mul, Matrix.diag_apply, sq, Finset.mul_sum,
              Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
          have hev : ∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℕ) (h : Fin s → MvPolynomial (Fin n) ℝ)
              (f : MvPolynomial (Fin n) ℝ), polyEval x (f - ∑ i, h i ^ 2) = polyEval x f - ∑ i, polyEval x (h i) ^ 2 := by
            intro x s h f
            simp [polyEval, map_sum]
          have hdeg1 : ∀ (a : ℝ) (b : Fin n → ℝ),
              (MvPolynomial.C a + ∑ i, MvPolynomial.C (b i) * MvPolynomial.X i :
                MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 := by
            intro a b
            refine (MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) ?_)
            refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
            refine (MvPolynomial.totalDegree_mul _ _).trans ?_
            simp
          have hev1 : ∀ (a : ℝ) (b : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)),
              polyEval x (MvPolynomial.C a + ∑ i, MvPolynomial.C (b i) * MvPolynomial.X i) =
                a + ∑ i, b i * x i := by
            intro a b x
            simp [polyEval, map_sum]
          have hlin : ∀ ℓ : MvPolynomial (Fin n) ℝ, ℓ.totalDegree ≤ 1 →
              ℓ = MvPolynomial.C (ℓ.coeff 0) + ∑ i, MvPolynomial.C (ℓ.coeff (Finsupp.single i 1)) * MvPolynomial.X i := by
            intro ℓ hℓ
            ext m
            simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C, MvPolynomial.coeff_sum,
              MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', mul_ite, mul_one, mul_zero]
            by_cases hm0 : m = 0
            · subst hm0
              simp
            · rw [if_neg (Ne.symm hm0), zero_add]
              by_cases hdeg : m.degree ≤ 1
              · obtain ⟨j, hj⟩ : ∃ j, m = Finsupp.single j 1 := by
                  have h1 : m.degree = 1 := by
                    have : m.degree ≠ 0 := by
                      intro h; exact hm0 ((Finsupp.degree_eq_zero_iff m).1 h)
                    omega
                  exact (Finsupp.sum_eq_one_iff m).mp h1
                subst hj
                rw [Finset.sum_eq_single j]
                · simp
                · intro b _ hb
                  rw [if_neg]
                  intro h
                  exact hb (Finsupp.single_left_injective one_ne_zero h)
                · simp
              · rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt (by
                  have : Finsupp.degree m = ∑ i ∈ m.support, m i := rfl
                  omega)]
                symm
                apply Finset.sum_eq_zero
                intro i _
                rw [if_neg]
                rintro rfl
                simp at hdeg
          have hlin' : ∀ ℓ : MvPolynomial (Fin n) ℝ, ℓ.totalDegree ≤ 1 → ∀ x : EuclideanSpace ℝ (Fin n),
              polyEval x ℓ = ℓ.coeff 0 + ∑ i, ℓ.coeff (Finsupp.single i 1) * x i := by
            intro ℓ hℓ x
            conv_lhs => rw [hlin ℓ hℓ]
            exact hev1 _ _ x
          have hinner : ∀ x y : EuclideanSpace ℝ (Fin n), inner ℝ x y = ∑ i, y i * x i := by
            intro x y
            simp [PiLp.inner_apply, mul_comm]
          open Matrix in
          have hcl : ∀ (k : ℕ) (S : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → Fin k → ℝ),
              IsClosed {q : ℝ × EuclideanSpace ℝ (Fin n) | ∃ B : Matrix (Fin k) (Fin k) ℝ, B.PosSemidef ∧
                ∀ x ∈ S, q.1 - inner ℝ x q.2 = f x ⬝ᵥ (B *ᵥ f x)} := by
            intro k S f
            -- bilinear bound
            have hbil : ∀ (B : Matrix (Fin k) (Fin k) ℝ), B.PosSemidef → ∀ u v : Fin k → ℝ,
                |u ⬝ᵥ (B *ᵥ v)| ≤ (u ⬝ᵥ (B *ᵥ u) + v ⬝ᵥ (B *ᵥ v)) / 2 := by
              intro B hB u v
              have h1 := hB.dotProduct_mulVec_nonneg (u + v)
              have h2 := hB.dotProduct_mulVec_nonneg (u - v)
              have hs : v ⬝ᵥ (B *ᵥ u) = u ⬝ᵥ (B *ᵥ v) := by
                rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
                congr 2
                have := hB.1
                rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
                rw [this]
              simp only [star_trivial, mulVec_add, mulVec_sub, add_dotProduct, dotProduct_add,
                sub_dotProduct, dotProduct_sub, hs] at h1 h2
              rw [abs_le]; constructor <;> linarith
            have hsumq : ∀ (B : Matrix (Fin k) (Fin k) ℝ), B.PosSemidef → ∀ (K : ℝ) (N N' : ℕ)
                (g : Fin N → Fin k → ℝ) (g' : Fin N' → Fin k → ℝ) (c : Fin N → ℝ) (d : Fin N' → ℝ),
                (∀ l, g l ⬝ᵥ (B *ᵥ g l) ≤ K) → (∀ l, g' l ⬝ᵥ (B *ᵥ g' l) ≤ K) →
                |(∑ l, c l • g l) ⬝ᵥ (B *ᵥ ∑ l, d l • g' l)| ≤ (∑ l, |c l|) * (∑ l, |d l|) * K := by
              intro B hB K N N' g g' c d hg hg'
              simp only [mulVec_sum, mulVec_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct,
                dotProduct_smul, smul_eq_mul]
              have hK : ∀ l l', |g l ⬝ᵥ (B *ᵥ g' l')| ≤ K := by
                intro l l'
                have := hbil B hB (g l) (g' l')
                have := hg l; have := hg' l'
                linarith
              calc _ ≤ ∑ l', ∑ l, |d l'| * |c l| * K := by
                    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l' _ => ?_)
                    rw [abs_mul]
                    refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)).trans ?_
                    rw [Finset.mul_sum]
                    refine Finset.sum_le_sum fun l _ => ?_
                    rw [abs_mul, ← mul_assoc]
                    exact mul_le_mul_of_nonneg_left (hK l l') (by positivity)
                _ = (∑ l, |c l|) * (∑ l, |d l|) * K := by
                    rw [Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_comm]
                    refine Finset.sum_congr rfl fun l _ => ?_
                    rw [Finset.sum_mul]
                    exact Finset.sum_congr rfl fun l' _ => by ring
            apply isClosed_of_closure_subset
            intro q hq
            obtain ⟨qs, hqs, hlim⟩ := mem_closure_iff_seq_limit.1 hq
            choose B hBpsd hBeq using hqs
            set W := Submodule.span ℝ (f '' S) with hWdef
            obtain ⟨W', hW'⟩ := W.exists_isCompl
            let Ql : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ) := W.subtype ∘ₗ W.projectionOnto W' hW'
            have hQf : ∀ x ∈ S, Ql (f x) = f x := by
              intro x hx
              have := Submodule.projectionOnto_apply_left hW' ⟨f x, Submodule.subset_span ⟨x, hx, rfl⟩⟩
              simp only [Ql, LinearMap.comp_apply, Submodule.coe_subtype]
              rw [this]
            let Q := LinearMap.toMatrix' Ql
            have hQv : ∀ v, Q *ᵥ v = Ql v := fun v => LinearMap.toMatrix'_mulVec Ql v
            have hcol : ∀ j, Q *ᵥ Pi.single j 1 ∈ W := by
              intro j; rw [hQv]; exact (W.projectionOnto W' hW' _).2
            choose N c g hcg using fun j => Submodule.mem_span_set'.1 (hcol j)
            choose xs hxsS hxs using fun (p : Σ j, Fin (N j)) => (g p.1 p.2).2
            have hFt : Filter.Tendsto (fun m (p : Σ j, Fin (N j)) => (qs m).1 - inner ℝ (xs p) (qs m).2)
                Filter.atTop (nhds (fun p => q.1 - inner ℝ (xs p) q.2)) := by
              rw [tendsto_pi_nhds]; intro p
              exact ((continuous_fst.sub (continuous_const.inner continuous_snd)).tendsto q).comp hlim
            obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hFt)
            have hRb : ∀ m j i, (g j i : Fin k → ℝ) ⬝ᵥ (B m *ᵥ (g j i : Fin k → ℝ)) ≤ |R| := by
              intro m j i
              have h1 := hR _ ⟨m, rfl⟩
              have h2 := (norm_le_pi_norm (fun (p : Σ j, Fin (N j)) => (qs m).1 - inner ℝ (xs p) (qs m).2) ⟨j, i⟩).trans h1
              rw [← hxs ⟨j, i⟩, ← hBeq m _ (hxsS ⟨j, i⟩)]
              rw [Real.norm_eq_abs] at h2
              exact (le_abs_self _).trans (h2.trans (le_abs_self R))
            let B' : ℕ → Matrix (Fin k) (Fin k) ℝ := fun m => Qᴴ * B m * Q
            have hB'psd : ∀ m, (B' m).PosSemidef := fun m => (hBpsd m).conjTranspose_mul_mul_same Q
            have hent : ∀ (M : Matrix (Fin k) (Fin k) ℝ) i j, (Qᴴ * M * Q) i j =
                (Q *ᵥ Pi.single i 1) ⬝ᵥ (M *ᵥ (Q *ᵥ Pi.single j 1)) := by
              intro M i j
              simp only [Matrix.mul_apply, dotProduct, mulVec, Pi.single_apply, conjTranspose_apply,
                star_trivial, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
                Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
            set K : ℝ := ∑ i, ∑ j, (∑ l, |c i l|) * (∑ l, |c j l|) * |R| with hK
            have hB'b : ∀ m i j, |B' m i j| ≤ K := by
              intro m i j
              have h1 : |B' m i j| ≤ (∑ l, |c i l|) * (∑ l, |c j l|) * |R| := by
                show |(Qᴴ * B m * Q) i j| ≤ _
                rw [hent, ← hcg i, ← hcg j]
                exact hsumq (B m) (hBpsd m) |R| _ _ _ _ _ _ (fun l => hRb m i l) (fun l => hRb m j l)
              refine h1.trans ?_
              have hnn : ∀ i j, 0 ≤ (∑ l, |c i l|) * (∑ l, |c j l|) * |R| := fun i j => by positivity
              refine (Finset.single_le_sum (fun j _ => hnn i j) (Finset.mem_univ j)).trans ?_
              exact Finset.single_le_sum (f := fun i => ∑ j, (∑ l, |c i l|) * (∑ l, |c j l|) * |R|)
                (fun i _ => Finset.sum_nonneg fun j _ => hnn i j) (Finset.mem_univ i)
            have hK0 : 0 ≤ K := by positivity
            let B'' : ℕ → (Fin k → Fin k → ℝ) := fun m i j => B' m i j
            obtain ⟨L, -, φ, hφ, hL⟩ := tendsto_subseq_of_bounded (x := B'')
              (Metric.isBounded_closedBall (x := (0 : Fin k → Fin k → ℝ)) (r := K)) (fun m => by
                refine (mem_closedBall_zero_iff (E := Fin k → Fin k → ℝ)).2 ?_
                refine (pi_norm_le_iff_of_nonneg hK0).2 fun i => (pi_norm_le_iff_of_nonneg hK0).2 fun j => ?_
                exact (Real.norm_eq_abs _).le.trans (hB'b m i j))
            have hLij : ∀ i j, Filter.Tendsto (fun m => B' (φ m) i j) Filter.atTop (nhds (L i j)) := by
              intro i j
              exact (((continuous_apply j).comp (continuous_apply i)).tendsto L).comp hL
            have hqf : ∀ (v : Fin k → ℝ), Filter.Tendsto (fun m => v ⬝ᵥ (B' (φ m) *ᵥ v)) Filter.atTop
                (nhds (v ⬝ᵥ ((L : Matrix (Fin k) (Fin k) ℝ) *ᵥ v))) := by
              intro v
              simp only [dotProduct, mulVec]
              exact tendsto_finsetSum _ fun i _ => (tendsto_finsetSum _ fun j _ =>
                (hLij i j).mul tendsto_const_nhds).const_mul _
            refine ⟨L, ?_, ?_⟩
            · refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
              · refine Matrix.IsHermitian.ext fun i j => ?_
                rw [star_trivial]
                refine tendsto_nhds_unique ?_ (hLij i j)
                refine (hLij j i).congr fun m => ?_
                have := (hB'psd (φ m)).1
                exact congrFun (congrFun this i) j ▸ (by rw [conjTranspose_apply, star_trivial])
              · simp only [star_trivial]
                exact ge_of_tendsto' (hqf v) fun m => by
                  have := (hB'psd (φ m)).dotProduct_mulVec_nonneg v
                  simpa using this
            · intro x hx
              refine tendsto_nhds_unique ?_ (hqf (f x))
              have hc : Continuous fun r : ℝ × EuclideanSpace ℝ (Fin n) => r.1 - inner ℝ x r.2 :=
                continuous_fst.sub (continuous_const.inner continuous_snd)
              have h1 : Filter.Tendsto (fun m => (qs (φ m)).1 - inner ℝ x (qs (φ m)).2) Filter.atTop
                  (nhds (q.1 - inner ℝ x q.2)) := (hc.tendsto q).comp (hlim.comp hφ.tendsto_atTop)
              refine h1.congr fun m => ?_
              rw [hBeq (φ m) x hx]
              show _ = f x ⬝ᵥ ((Qᴴ * B (φ m) * Q) *ᵥ f x)
              rw [← mulVec_mulVec, ← mulVec_mulVec, conjTranspose_eq_transpose_of_trivial,
                dotProduct_mulVec (f x) Qᵀ, vecMul_transpose, hQv, hQf x hx]
          have part1 : ∀ (k : ℕ) (p : MvPolynomial (Fin n) ℝ) (w : Fin k → MvPolynomial (Fin n) ℝ),
              (∀ x ∈ Set.extremePoints ℝ (convexHull ℝ (realZeroSet I)), polyEval x p ≠ 0) →
              (HasRationalFactorization (convexHull ℝ (realZeroSet I)) p w ↔
                ∀ ℓ : MvPolynomial (Fin n) ℝ, ℓ.totalDegree ≤ 1 →
                  (∀ z ∈ realZeroSet I, 0 ≤ polyEval z ℓ) →
                    IsSosModulo I (Submodule.span ℝ (Set.range w) : Set (MvPolynomial (Fin n) ℝ))
                      (p ^ 2 * ℓ)) := by
            intro k p w hp
            constructor
            · intro hfac ℓ hℓ hℓZ
              obtain ⟨-, B, hB, heq⟩ := hfac
              set C := convexHull ℝ (realZeroSet I) with hCdef
              set f : EuclideanSpace ℝ (Fin n) → Fin k → ℝ := fun x j => polyEval x (w j) / polyEval x p
                with hfdef
              have hD := hcl k (Set.extremePoints ℝ C) f
              set T := {y : EuclideanSpace ℝ (Fin n) | ((1 : ℝ), y) ∈ {q : ℝ × EuclideanSpace ℝ (Fin n) |
                ∃ B : Matrix (Fin k) (Fin k) ℝ, B.PosSemidef ∧ ∀ x ∈ Set.extremePoints ℝ C,
                  q.1 - inner ℝ x q.2 = f x ⬝ᵥ (B.mulVec (f x))}} with hTdef
              have hTc : IsClosed T := hD.preimage (continuous_const.prodMk continuous_id)
              have hTv : Convex ℝ T := by
                rintro y1 ⟨B1, hB1, he1⟩ y2 ⟨B2, hB2, he2⟩ a b ha hb hab
                refine ⟨a • B1 + b • B2, (hB1.smul ha).add (hB2.smul hb), fun x hx => ?_⟩
                have e1 := he1 x hx; have e2 := he2 x hx
                simp only at e1 e2 ⊢
                rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add,
                  dotProduct_smul, dotProduct_smul, ← e1, ← e2, inner_add_right, inner_smul_right,
                  inner_smul_right, smul_eq_mul, smul_eq_mul]
                linear_combination (-1 : ℝ) * hab
              have hextT : Set.extremePoints ℝ (ConeLifts.Shared.polar C) ⊆ T := by
                intro y hy
                refine ⟨B y, hB y hy, fun x hx => ?_⟩
                simp only
                rw [heq x hx y hy, rationalMap]
                simp only [Matrix.trace, Matrix.mul_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
                  smul_eq_mul, Matrix.diag_apply, dotProduct, Matrix.mulVec, hfdef, Finset.mul_sum]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
                ring
              obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hC.2.2)
              have hpolc : IsCompact (ConeLifts.Shared.polar C) := by
                refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
                · have : ConeLifts.Shared.polar C = ⋂ x ∈ C, {y | inner ℝ x y ≤ (1 : ℝ)} := by
                    ext y; simp [ConeLifts.Shared.polar]
                  rw [this]
                  exact isClosed_biInter fun x _ =>
                    isClosed_le (continuous_const.inner continuous_id) continuous_const
                · refine isBounded_iff_forall_norm_le.2 ⟨2 / ε, fun y hy => ?_⟩
                  by_cases hy0 : y = 0
                  · rw [hy0, norm_zero]; positivity
                  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
                  have hmem : (ε / 2 / ‖y‖) • y ∈ C := hball (by
                    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
                      abs_of_pos (by positivity), div_mul_cancel₀ _ hyn.ne']
                    linarith)
                  have := hy _ hmem
                  rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at this
                  rw [le_div_iff₀ hε]
                  have h2 : ε / 2 / ‖y‖ * ‖y‖ ^ 2 = ε / 2 * ‖y‖ := by field_simp
                  nlinarith
              have hpolv : Convex ℝ (ConeLifts.Shared.polar C) := by
                intro y1 h1 y2 h2 a b ha hb hab x hx
                rw [inner_add_right, inner_smul_right, inner_smul_right]
                have := h1 x hx; have := h2 x hx
                nlinarith
              have hpolT : ConeLifts.Shared.polar C ⊆ T := by
                rw [← closure_convexHull_extremePoints hpolc hpolv]
                exact closure_minimal (convexHull_min hextT hTv) hTc
              have hℓC : ∀ x ∈ C, 0 ≤ polyEval x ℓ := by
                refine fun x hx => (convexHull_min (t := {x | 0 ≤ polyEval x ℓ}) (fun z hz => hℓZ z hz) ?_) hx
                intro x hx y hy a b ha hb hab
                have h1 : 0 ≤ polyEval x ℓ := hx
                have h2 : 0 ≤ polyEval y ℓ := hy
                show 0 ≤ polyEval (a • x + b • y) ℓ
                rw [hlin' ℓ hℓ] at h1 h2 ⊢
                simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
                have hs : ∑ i, ℓ.coeff (Finsupp.single i 1) * (a * x i + b * y i) =
                    a * ∑ i, ℓ.coeff (Finsupp.single i 1) * x i + b * ∑ i, ℓ.coeff (Finsupp.single i 1) * y i := by
                  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                  exact Finset.sum_congr rfl (fun i _ => by ring)
                rw [hs]
                have : ℓ.coeff 0 + (a * ∑ i, ℓ.coeff (Finsupp.single i 1) * x i +
                    b * ∑ i, ℓ.coeff (Finsupp.single i 1) * y i) =
                    a * (ℓ.coeff 0 + ∑ i, ℓ.coeff (Finsupp.single i 1) * x i) +
                    b * (ℓ.coeff 0 + ∑ i, ℓ.coeff (Finsupp.single i 1) * y i) := by
                  linear_combination (-(ℓ.coeff 0)) * hab
                rw [this]
                positivity
              set a := ℓ.coeff 0 with ha
              set b : Fin n → ℝ := fun i => ℓ.coeff (Finsupp.single i 1) with hb
              have hℓx : ∀ x, polyEval x ℓ = a + ∑ i, b i * x i := fun x => hlin' ℓ hℓ x
              have ha0 : 0 ≤ a := by
                have := hℓC 0 (interior_subset hC.2.2)
                rw [hℓx] at this; simpa using this
              rcases ha0.lt_or_eq with hapos | ha0
              · let y : EuclideanSpace ℝ (Fin n) := (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i => - b i / a)
                have hy : ∀ i, y i = - b i / a := fun i => by simp [y]
                have hyx : ∀ x, a * (1 - inner ℝ x y) = polyEval x ℓ := by
                  intro x
                  rw [hℓx, hinner, mul_sub, Finset.mul_sum]
                  simp only [hy]
                  have : ∀ i, a * (-b i / a * x i) = - (b i * x i) := fun i => by field_simp
                  simp only [this, Finset.sum_neg_distrib]
                  ring
                have hyT : y ∈ T := hpolT (fun x hx => by
                  have h1 := hℓC x hx
                  rw [← hyx] at h1
                  have := (mul_nonneg_iff_of_pos_left hapos).1 h1
                  show inner ℝ x y ≤ 1
                  linarith)
                obtain ⟨Bm, hBm, hBe⟩ := hyT
                obtain ⟨s, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 hBm
                refine ⟨s, fun t => Real.sqrt a • ∑ j, v t j • w j, fun t => ?_, ?_⟩
                · exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
                    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
                rw [hmemI]
                intro x hx
                have e := hBe x hx
                simp only at e
                have hq : f x ⬝ᵥ ((∑ t, Matrix.vecMulVec (v t) (star (v t))).mulVec (f x)) =
                    ∑ t, (∑ j, v t j * f x j) ^ 2 := by
                  simp only [Matrix.sum_mulVec, dotProduct_sum, star_trivial]
                  refine Finset.sum_congr rfl fun t _ => ?_
                  simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, sq, Finset.sum_mul,
                    Finset.mul_sum]
                  rw [Finset.sum_comm]
                  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
                rw [hq] at e
                have hpx := hp x hx
                rw [hev]
                have hpe : polyEval x (p ^ 2 * ℓ) = polyEval x p ^ 2 * polyEval x ℓ := by simp [polyEval]
                have hhe : ∀ t, polyEval x (Real.sqrt a • ∑ j, v t j • w j) =
                    Real.sqrt a * (polyEval x p * ∑ j, v t j * f x j) := by
                  intro t
                  simp only [polyEval, MvPolynomial.smul_eval, map_sum, hfdef]
                  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  have hpx' : (MvPolynomial.eval fun i => x i) p ≠ 0 := hpx
                  field_simp
                rw [hpe, ← hyx, e]
                simp only [hhe, mul_pow, Real.sq_sqrt ha0, ← Finset.mul_sum]
                ring
              · have hz : ∀ x ∈ C, ∑ i, b i * x i = 0 := by
                  intro x hx
                  have h1 := hℓC x hx
                  rw [hℓx, ← ha0, zero_add] at h1
                  set t : ℝ := ε / 2 / (‖x‖ + 1)
                  have ht : 0 < t := by positivity
                  have hmem : (-t) • x ∈ C := hball (by
                    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_neg,
                      abs_of_pos ht]
                    have : t * ‖x‖ < ε := by
                      have h3 : t * (‖x‖ + 1) = ε / 2 := by simp only [t]; field_simp
                      nlinarith [norm_nonneg x]
                    exact this)
                  have h2 := hℓC _ hmem
                  rw [hℓx, ← ha0, zero_add] at h2
                  simp only [PiLp.smul_apply, smul_eq_mul] at h2
                  have : ∑ i, b i * (-t * x i) = -t * ∑ i, b i * x i := by
                    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
                  rw [this] at h2
                  nlinarith
                refine ⟨0, Fin.elim0, fun i => i.elim0, ?_⟩
                rw [hmemI]
                intro x hx
                rw [hev]
                simp [polyEval]
                right
                have := hz x (hEZ hx |> subset_convexHull ℝ _)
                have h4 := hℓx x
                rw [this, ← ha0, add_zero] at h4
                simpa [polyEval] using h4
            · intro hsos
              refine ⟨fun x _ => ?_, ?_⟩
              · unfold rationalMap
                have := Matrix.posSemidef_vecMulVec_self_star (fun i => polyEval x (w i))
                simp only [star_trivial] at this
                exact this.smul (by positivity)
              have key : ∀ y, ∃ Bm : Matrix (Fin k) (Fin k) ℝ,
                  y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar (convexHull ℝ (realZeroSet I))) →
                  Bm.PosSemidef ∧ ∀ x ∈ Set.extremePoints ℝ (convexHull ℝ (realZeroSet I)),
                    1 - inner ℝ x y = (rationalMap p w x * Bm).trace := by
                intro y
                by_cases hy : y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar (convexHull ℝ (realZeroSet I)))
                · have hℓdeg := hdeg1 1 (fun i => - y i)
                  have hℓev : ∀ x, polyEval x (MvPolynomial.C 1 + ∑ i, MvPolynomial.C (-y i) * MvPolynomial.X i) = 1 - inner ℝ x y := by
                    intro x; rw [hev1, hinner]; simp [Finset.sum_neg_distrib, sub_eq_add_neg]
                  obtain ⟨s, h, hhw, hhI⟩ := hsos _ hℓdeg (fun z hz => by
                    rw [hℓev]; have := hy.1 z (subset_convexHull ℝ _ hz); linarith)
                  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hhw i)
                  refine ⟨∑ t, Matrix.vecMulVec (fun j => c t j) (star fun j => c t j), fun _ =>
                    ⟨Matrix.posSemidef_iff_eq_sum_vecMulVec.2 ⟨s, _, rfl⟩, ?_⟩⟩
                  intro x hx
                  rw [rationalMap, htr]
                  have h1 := (hmemI _).1 hhI x hx
                  rw [hev] at h1
                  have h2 : ∀ t, polyEval x (h t) = ∑ j, c t j * polyEval x (w j) := by
                    intro t; rw [← hc t]; simp [polyEval, map_sum]
                  simp only [← h2]
                  have hpx := hp x hx
                  have h3 : polyEval x (p ^ 2 * (MvPolynomial.C 1 + ∑ i, MvPolynomial.C (-y i) * MvPolynomial.X i)) = polyEval x p ^ 2 * (1 - inner ℝ x y) := by
                    rw [← hℓev]; simp [polyEval]
                  rw [h3] at h1
                  field_simp
                  linarith
                · exact ⟨0, fun h => absurd h hy⟩
              choose B hB using key
              exact ⟨B, fun y hy => (hB y hy).1, fun x hx y hy => (hB y hy).2 x hx⟩
          refine ⟨part1, fun k => ?_⟩
          have hsub : convexHull ℝ (realZeroSet I) ⊆ thetaBody I k := by
            refine convexHull_min ?_ ?_
            · rintro z hz ℓ hℓ ⟨s, h, _, hhI⟩
              have h1 : polyEval z (ℓ - ∑ i, h i ^ 2) = 0 := hz _ hhI
              rw [hev] at h1
              have : 0 ≤ ∑ i, polyEval z (h i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
              show 0 ≤ polyEval z ℓ
              linarith
            · intro x hx y hy a b ha hb hab ℓ hℓ hsos
              have h1 := hx ℓ hℓ hsos
              have h2 := hy ℓ hℓ hsos
              show 0 ≤ polyEval (a • x + b • y) ℓ
              rw [hlin' ℓ hℓ] at h1 h2 ⊢
              simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
              have : ℓ.coeff 0 + ∑ i, ℓ.coeff (Finsupp.single i 1) * (a * x i + b * y i) =
                  a * (ℓ.coeff 0 + ∑ i, ℓ.coeff (Finsupp.single i 1) * x i) +
                  b * (ℓ.coeff 0 + ∑ i, ℓ.coeff (Finsupp.single i 1) * y i) := by
                have hs : ∑ i, ℓ.coeff (Finsupp.single i 1) * (a * x i + b * y i) =
                    a * ∑ i, ℓ.coeff (Finsupp.single i 1) * x i + b * ∑ i, ℓ.coeff (Finsupp.single i 1) * y i := by
                  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                  exact Finset.sum_congr rfl (fun i _ => by ring)
                rw [hs]
                linear_combination (-(ℓ.coeff 0)) * hab
              rw [this]
              positivity
          constructor
          · rintro ⟨r, w, hwdeg, hfac⟩
            refine Set.Subset.antisymm ?_ hsub
            intro x hx
            by_contra hxC
            obtain ⟨f, u, hfx, hfC⟩ := geometric_hahn_banach_point_closed hC.2.1 hC.1.isClosed hxC
            have hf : ∀ z : EuclideanSpace ℝ (Fin n), f z = ∑ i, f (EuclideanSpace.single i 1) * z i := by
              intro z
              conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr z]
              simp [map_sum, mul_comm]
            have hℓdeg := hdeg1 (-u) (fun i => f (EuclideanSpace.single i 1))
            have hℓev : ∀ z, polyEval z (MvPolynomial.C (-u) + ∑ i, MvPolynomial.C (f (EuclideanSpace.single i 1)) * MvPolynomial.X i) = f z - u := by
              intro z; rw [hev1, hf]; ring
            have hsos := ((part1 r 1 w (fun _ _ => by simp [polyEval])).1 hfac) _ hℓdeg (fun z hz => by
              rw [hℓev]; have := hfC z (subset_convexHull ℝ _ hz); linarith)
            rw [one_pow, one_mul] at hsos
            obtain ⟨s, h, hh, hhI⟩ := hsos
            have hspan : Submodule.span ℝ (Set.range w) ≤ MvPolynomial.restrictTotalDegree (Fin n) ℝ k :=
              Submodule.span_le.2 (by
                rintro _ ⟨i, rfl⟩
                exact (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (hwdeg i))
            have := hx _ hℓdeg ⟨s, h, fun i => (MvPolynomial.mem_restrictTotalDegree _ _ _).1 (hspan (hh i)), hhI⟩
            rw [hℓev] at this
            linarith
          · intro hTH
            obtain ⟨r, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.1
              (Module.Finite.iff_fg.1 (inferInstance :
                Module.Finite ℝ (MvPolynomial.restrictTotalDegree (Fin n) ℝ k)))
            have hwdeg : ∀ i, (w i).totalDegree ≤ k := fun i =>
              (MvPolynomial.mem_restrictTotalDegree _ _ _).1 (hw ▸ Submodule.subset_span ⟨i, rfl⟩)
            refine ⟨r, w, hwdeg, ?_⟩
            rw [part1 r 1 w (fun _ _ => by simp [polyEval])]
            intro ℓ hℓ hℓZ
            rw [one_pow, one_mul]
            set C := convexHull ℝ (realZeroSet I) with hCdef
            set E := Set.extremePoints ℝ C with hEdef
            set F : EuclideanSpace ℝ (Fin n) → Fin r → ℝ := fun x j => polyEval x (w j) with hFdef
            set K := {q : ℝ × EuclideanSpace ℝ (Fin n) | ∃ B : Matrix (Fin r) (Fin r) ℝ, B.PosSemidef ∧
                ∀ x ∈ E, q.1 - inner ℝ x q.2 = F x ⬝ᵥ (B.mulVec (F x))} with hKdef
            have hKc : IsClosed K := hcl r E F
            have hKv : Convex ℝ K := by
              rintro y1 ⟨B1, hB1, he1⟩ y2 ⟨B2, hB2, he2⟩ a b ha hb hab
              refine ⟨a • B1 + b • B2, (hB1.smul ha).add (hB2.smul hb), fun x hx => ?_⟩
              have e1 := he1 x hx; have e2 := he2 x hx
              simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
              rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add,
                dotProduct_smul, dotProduct_smul, ← e1, ← e2, inner_add_right, inner_smul_right,
                inner_smul_right, smul_eq_mul, smul_eq_mul]
              ring
            have hKs : ∀ q ∈ K, ∀ c : ℝ, 0 ≤ c → c • q ∈ K := by
              rintro q ⟨B1, hB1, he1⟩ c hc
              refine ⟨c • B1, hB1.smul hc, fun x hx => ?_⟩
              have e1 := he1 x hx
              simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
              rw [Matrix.smul_mulVec, dotProduct_smul, ← e1, inner_smul_right, smul_eq_mul]
              ring
            have hq : ∀ (s : ℕ) (v : Fin s → Fin r → ℝ) (x : EuclideanSpace ℝ (Fin n)),
                F x ⬝ᵥ ((∑ t, Matrix.vecMulVec (v t) (star (v t))).mulVec (F x)) =
                  ∑ t, (∑ j, v t j * F x j) ^ 2 := by
              intro s v x
              simp only [Matrix.sum_mulVec, dotProduct_sum, star_trivial]
              refine Finset.sum_congr rfl fun t _ => ?_
              simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, sq, Finset.sum_mul,
                Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
            -- vector of a linear polynomial
            let vec : MvPolynomial (Fin n) ℝ → ℝ × EuclideanSpace ℝ (Fin n) := fun ℓ' =>
              (ℓ'.coeff 0, (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i => - ℓ'.coeff (Finsupp.single i 1)))
            have hvec : ∀ ℓ' : MvPolynomial (Fin n) ℝ, ℓ'.totalDegree ≤ 1 → ∀ x,
                polyEval x ℓ' = (vec ℓ').1 - inner ℝ x (vec ℓ').2 := by
              intro ℓ' h' x
              rw [hlin' ℓ' h', hinner]
              simp [vec, Finset.sum_neg_distrib, sub_eq_add_neg]
            -- sos → K
            have hsosK : ∀ ℓ' : MvPolynomial (Fin n) ℝ, ℓ'.totalDegree ≤ 1 →
                IsSosModulo I {h | h.totalDegree ≤ k} ℓ' → vec ℓ' ∈ K := by
              rintro ℓ' h' ⟨s, h, hh, hhI⟩
              have hhw : ∀ i, h i ∈ Submodule.span ℝ (Set.range w) := fun i => by
                rw [hw]; exact (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (hh i)
              choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hhw i)
              refine ⟨∑ t, Matrix.vecMulVec (fun j => c t j) (star fun j => c t j),
                Matrix.posSemidef_iff_eq_sum_vecMulVec.2 ⟨s, _, rfl⟩, fun x hx => ?_⟩
              rw [hq, ← hvec ℓ' h' x]
              have h1 := (hmemI _).1 hhI x hx
              rw [hev] at h1
              have h2 : ∀ t, polyEval x (h t) = ∑ j, c t j * F x j := by
                intro t; rw [← hc t]; simp [polyEval, map_sum, hFdef]
              simp only [h2] at h1
              linarith
            -- K → sos
            have hKsos : vec ℓ ∈ K → IsSosModulo I (Submodule.span ℝ (Set.range w) :
                Set (MvPolynomial (Fin n) ℝ)) ℓ := by
              rintro ⟨Bm, hBm, hBe⟩
              obtain ⟨s, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 hBm
              refine ⟨s, fun t => ∑ j, v t j • w j, fun t => ?_, ?_⟩
              · exact Submodule.sum_mem _ fun j _ =>
                    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
              rw [hmemI]
              intro x hx
              have e := hBe x hx
              rw [hq, ← hvec ℓ hℓ x] at e
              rw [hev, e]
              have hhe : ∀ t, polyEval x (∑ j, v t j • w j) = ∑ j, v t j * F x j := by
                intro t
                simp [polyEval, MvPolynomial.smul_eval, map_sum, hFdef]
              simp only [hhe, sub_self]
            have hℓC : ∀ x ∈ C, 0 ≤ polyEval x ℓ := by
              refine fun x hx => (convexHull_min (t := {x | 0 ≤ polyEval x ℓ}) (fun z hz => hℓZ z hz) ?_) hx
              intro x hx y hy a b ha hb hab
              have h1 : 0 ≤ polyEval x ℓ := hx
              have h2 : 0 ≤ polyEval y ℓ := hy
              show 0 ≤ polyEval (a • x + b • y) ℓ
              rw [hvec ℓ hℓ] at h1 h2 ⊢
              rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
              have : (vec ℓ).1 - (a * inner ℝ x (vec ℓ).2 + b * inner ℝ y (vec ℓ).2) =
                  a * ((vec ℓ).1 - inner ℝ x (vec ℓ).2) + b * ((vec ℓ).1 - inner ℝ y (vec ℓ).2) := by
                linear_combination (-((vec ℓ).1)) * hab
              rw [this]
              positivity
            apply hKsos
            by_contra hnot
            obtain ⟨f, u, hfK, hfq⟩ := geometric_hahn_banach_closed_point hKv hKc hnot
            have h0K : (0 : ℝ × EuclideanSpace ℝ (Fin n)) ∈ K := by
              simpa using hKs _ (hsosK (0 : MvPolynomial (Fin n) ℝ) (by simp) ⟨0, Fin.elim0, fun i => i.elim0, by simp⟩) 0 le_rfl
            have hu : 0 < u := by have := hfK 0 h0K; simpa using this
            have hfle : ∀ q ∈ K, f q ≤ 0 := by
              intro q hqK
              by_contra hpos
              push_neg at hpos
              have := hfK _ (hKs q hqK (u / f q + 1) (by positivity))
              rw [map_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ hpos.ne'] at this
              linarith
            set t := f (1, 0) with htdef
            set g : Fin n → ℝ := fun i => f (0, EuclideanSpace.single i 1) with hgdef
            have hfdec : ∀ (a : ℝ) (b : EuclideanSpace ℝ (Fin n)), f (a, b) = a * t + ∑ i, g i * b i := by
              intro a b
              have hab : ((a, b) : ℝ × EuclideanSpace ℝ (Fin n)) = a • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n))) +
                  ∑ i, b i • ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) := by
                ext
                · simp [Prod.fst_sum]
                · simp only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add, Prod.snd_sum]
                  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr b]
                  simp
              rw [hab, map_add, map_smul, map_sum, smul_eq_mul]
              congr 1
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_smul, smul_eq_mul, mul_comm]
            have h1K : vec 1 ∈ K := hsosK 1 (by simp) ⟨1, fun _ => 1, fun _ => by simp, by simp⟩
            have ht : t ≤ 0 := by
              have := hfle _ h1K
              have hv1 : vec 1 = ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n))) := by
                ext i
                · simp [vec]
                · simp [vec, MvPolynomial.coeff_one]
                  exact (Finsupp.single_ne_zero.2 one_ne_zero).symm
              rwa [hv1] at this
            set a0 := (vec ℓ).1 with ha0
            have hfqpos : 0 < f (vec ℓ) := hu.trans hfq
            set ε := f (vec ℓ) / (2 * (|a0| + 1)) with hεdef
            have hε : 0 < ε := by positivity
            have hεa : ε * a0 < f (vec ℓ) := by
              have h1 : ε * (2 * (|a0| + 1)) = f (vec ℓ) := by
                rw [hεdef]; field_simp
              have h2 : ε * a0 ≤ ε * |a0| := mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
              nlinarith [abs_nonneg a0]
            set σ := -t + ε with hσ
            have hσp : 0 < σ := by linarith
            let z : EuclideanSpace ℝ (Fin n) := (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i => g i / σ)
            have hz : ∀ q : ℝ × EuclideanSpace ℝ (Fin n), σ * (q.1 - inner ℝ z q.2) = ε * q.1 - f q := by
              intro q
              obtain ⟨a, b⟩ := q
              rw [hfdec, hinner, mul_sub, Finset.mul_sum]
              have hzi : ∀ i, z i = g i / σ := fun i => by simp [z]
              have : ∀ i, σ * (b i * z i) = g i * b i := fun i => by
                rw [hzi]; field_simp
              rw [Finset.sum_congr rfl fun i _ => this i]
              rw [hσ]
              ring
            have hzT : z ∈ thetaBody I k := by
              intro ℓ' h' hs'
              have h0 : 0 ≤ (vec ℓ').1 := by
                have := hsub (interior_subset hC.2.2) ℓ' h' hs'
                rw [hvec ℓ' h'] at this
                simpa using this
              have hf' := hfle _ (hsosK ℓ' h' hs')
              rw [hvec ℓ' h']
              have := hz (vec ℓ')
              have : 0 ≤ σ * ((vec ℓ').1 - inner ℝ z (vec ℓ').2) := by rw [this]; nlinarith
              exact (mul_nonneg_iff_of_pos_left hσp).1 this
            rw [hTH] at hzT
            have := hℓC z hzT
            rw [hvec ℓ hℓ] at this
            have h3 := hz (vec ℓ)
            have : 0 ≤ σ * ((vec ℓ).1 - inner ℝ z (vec ℓ).2) := mul_nonneg hσp.le this
            linarith
