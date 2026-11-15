-- Prove2me | solution 1 for DiazModulus.dalag_prop_12_13_iv_iii
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-15T05:49:41.949652+00:00
-- url     : https://prove2.me/submissions/fd7f8920-1f8a-497f-be8d-824a7611e54f

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_dalag_prop_12_10
import Theorems.Thm_DiazModulus_dalag_lemma_12_9_dehomog

open Complex ComplexConjugate

/-! # DALAG Prop. 12.13, (iv) ⇒ (iii)

Suppose `P(x) = 0`, and let `p = P(1, X₁, …, X_n)` be the dehomogenisation of `P`. Since `P` is homogeneous of
degree `D`, `P(z) = z₀^D · p(z₁/z₀, …, z_n/z₀)` whenever `z₀ ≠ 0`. At `z = x` (where `x₀ ≠ 0`, the `x_i` being
`k`-free) this gives `p(y) = 0` for `y_i = x_i/x₀`; at the generic point `z = (X₀, …, X_n)` of the fraction field
of `k[X₀, …, X_n]` it gives `p ≠ 0`, since `P ≠ 0`. By Prop. 12.10, `p = det(N₀ + Σ_i X_i N_i)` with square
matrices `N_i` over `k`, of size `s`. Let `M = Σ_j x_j N_j` over `K`. By (iv), the rank of `M` equals the rank of
`Σ_j X_j N_j` over `k(X₀, …, X_n)`, which by dehomogenisation equals the rank of `N₀ + Σ_i X_i N_i` over
`k(X₁, …, X_n)`; the determinant of that matrix is `p ≠ 0`, so `M` has rank `s`. But
`M = x₀ (N₀ + Σ_i y_i N_i)`, whose determinant is `x₀^s p(y) = 0`, so `M` has a non-zero kernel and rank less
than `s`: a contradiction. -/

namespace RC8_P1213
open DiazModulus

/-- Scaling a homogeneous polynomial. -/
theorem scale {k S : Type*} [CommRing k] [CommRing S] [Algebra k S] {N D : ℕ}
    (P : MvPolynomial (Fin N) k) (hP : P.IsHomogeneous D) (c : S) (z : Fin N → S) :
    MvPolynomial.aeval (c • z) P = c ^ D * MvPolynomial.aeval z P := by
  rw [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hdeg : ∑ i, a i = D := by
    rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    exact hP (MvPolynomial.mem_support_iff.mp ha)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- Evaluating the dehomogenisation at `w` is evaluating `P` at `(1, w)`. -/
theorem dehom_eval {k S : Type*} [CommRing k] [CommRing S] [Algebra k S] {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) k) (w : Fin n → S) :
    MvPolynomial.aeval w (MvPolynomial.aeval
      (Fin.cons 1 MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin n) k) P) =
      MvPolynomial.aeval (Fin.cons 1 w : Fin (n + 1) → S) P := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp
  · simp

/-- `P(z) = z₀^D · p(z₁/z₀, …, z_n/z₀)` for `z₀ ≠ 0`. -/
theorem dehom {k S : Type*} [CommRing k] [Field S] [Algebra k S] {n D : ℕ}
    (P : MvPolynomial (Fin (n + 1)) k) (hP : P.IsHomogeneous D) (z : Fin (n + 1) → S) (hz : z 0 ≠ 0) :
    MvPolynomial.aeval z P = z 0 ^ D * MvPolynomial.aeval (fun i : Fin n => z i.succ / z 0)
      (MvPolynomial.aeval (Fin.cons 1 MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin n) k) P) := by
  rw [dehom_eval, ← scale P hP]
  have hzc : z = z 0 • (Fin.cons 1 (fun i : Fin n => z i.succ / z 0) : Fin (n + 1) → S) := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · simp [mul_div_cancel₀ _ hz]
  conv_lhs => rw [hzc]

end RC8_P1213

open DiazModulus RC8_P1213 in
theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    (hiv : ∀ (s t m : ℕ) (M : Matrix (Fin s) (Fin t) K) (e : Fin m → K)
      (N : Fin m → Matrix (Fin s) (Fin t) k), LinearIndependent k e → (∀ j, e j ∈ E) →
      M = ∑ j, e j • (N j).map (algebraMap k K) →
      M.rank = (∑ j, (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))
        (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).rank)
    {n D : ℕ} (x : Fin (n + 1) → K) (hx : LinearIndependent k x) (hxE : ∀ i, x i ∈ E)
    (P : MvPolynomial (Fin (n + 1)) k) (hP : P.IsHomogeneous D) (hP0 : P ≠ 0) :
    MvPolynomial.aeval x P ≠ 0 := by
  classical
  intro hPx
  set p : MvPolynomial (Fin n) k :=
    MvPolynomial.aeval (Fin.cons 1 MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin n) k) P with hp_def
  have hx0 : x 0 ≠ 0 := hx.ne_zero 0
  set y : Fin n → K := fun i => x i.succ / x 0 with hy
  -- p vanishes at y
  have hpy : MvPolynomial.aeval y p = 0 := by
    have h := dehom P hP x hx0
    rw [hPx] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ hx0)
  -- p is not zero, by the generic point
  have hp0 : p ≠ 0 := by
    intro hp
    let L := FractionRing (MvPolynomial (Fin (n + 1)) k)
    let z : Fin (n + 1) → L := fun j => algebraMap (MvPolynomial (Fin (n + 1)) k) L (MvPolynomial.X j)
    have hz0 : z 0 ≠ 0 := by
      intro h
      exact MvPolynomial.X_ne_zero (R := k) (0 : Fin (n + 1))
        ((IsFractionRing.injective (MvPolynomial (Fin (n + 1)) k) L) (h.trans (map_zero _).symm))
    have h := dehom P hP z hz0
    rw [← hp_def, hp, map_zero, mul_zero] at h
    have hz : MvPolynomial.aeval z P = algebraMap (MvPolynomial (Fin (n + 1)) k) L P := by
      have : z = algebraMap (MvPolynomial (Fin (n + 1)) k) L ∘ MvPolynomial.X := rfl
      rw [this, MvPolynomial.aeval_algebraMap_apply, MvPolynomial.aeval_X_left_apply]
    apply hP0
    apply IsFractionRing.injective (MvPolynomial (Fin (n + 1)) k) L
    rw [map_zero, ← hz, h]
  -- p as a determinant, and the matrix M over K
  obtain ⟨s, N₀, N, hdet⟩ := dalag_prop_12_10 p
  set M : Matrix (Fin s) (Fin s) K :=
    ∑ j, x j • ((Fin.cons N₀ N : Fin (n + 1) → Matrix (Fin s) (Fin s) k) j).map (algebraMap k K) with hM
  have h41 : M.rank = (N₀.map (algebraMap k (FractionRing (MvPolynomial (Fin n) k))) +
      ∑ j, (algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k))
        (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin n) k)))).rank :=
    (hiv s s (n + 1) M x (Fin.cons N₀ N) hx hxE rfl).trans (dalag_lemma_12_9_dehomog N₀ N).symm
  have hmap : (N₀.map (MvPolynomial.C : k →+* MvPolynomial (Fin n) k) +
        ∑ i, (MvPolynomial.X i : MvPolynomial (Fin n) k) •
          (N i).map (MvPolynomial.C : k →+* MvPolynomial (Fin n) k)).map
        (algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k))) =
      N₀.map (algebraMap k (FractionRing (MvPolynomial (Fin n) k))) +
        ∑ j, (algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k))
          (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin n) k))) := by
    ext a b
    simp [Matrix.sum_apply, map_sum, MvPolynomial.algebraMap_eq,
      IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k))]
    simp only [Algebra.smul_def]
  have hdetF : (N₀.map (algebraMap k (FractionRing (MvPolynomial (Fin n) k))) +
        ∑ j, (algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k))
          (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin n) k)))).det =
      algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k)) p := by
    rw [← hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet]
  -- rank s by (iv)
  have hrank : M.rank = s := by
    rw [h41, Matrix.rank_of_det_ne_zero, Fintype.card_fin]
    rw [hdetF]
    exact fun h => hp0 ((IsFractionRing.injective _ _) (h.trans (map_zero _).symm))
  -- det M = x₀^s p(y) = 0
  have hev : MvPolynomial.aeval y p =
      (N₀.map (algebraMap k K) + ∑ i, y i • (N i).map (algebraMap k K)).det := by
    rw [← hdet, AlgHom.map_det]
    congr 1
    ext a b
    simp [Matrix.sum_apply]
  have hMy : M = x 0 • (N₀.map (algebraMap k K) + ∑ i, y i • (N i).map (algebraMap k K)) := by
    rw [hM, Fin.sum_univ_succ, smul_add, Finset.smul_sum]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_smul, hy, mul_div_cancel₀ _ hx0]
  have hdetM : M.det = 0 := by
    rw [hMy, Matrix.det_smul, ← hev, hpy, mul_zero]
  -- rank s and determinant 0 contradict
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetM
  have hker : v ∈ LinearMap.ker M.mulVecLin := hv
  have hk : 0 < Module.finrank K (LinearMap.ker M.mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hker⟩, fun h => hv0 (congrArg Subtype.val h)⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  have : M.rank = Module.finrank K (LinearMap.range M.mulVecLin) := rfl
  omega
