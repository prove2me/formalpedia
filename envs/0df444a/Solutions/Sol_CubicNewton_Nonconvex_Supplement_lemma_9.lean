-- Prove2me | solution 1 for CubicNewton.Nonconvex.Supplement.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:40:18.636025+00:00
-- url     : https://prove2.me/submissions/7f236c7f-0199-48f1-876c-90fc09b207cb

import Mathlib
import Definitions.Def_CubicNewton_Nonconvex_Supplement_CubicDual

open Filter Topology
open scoped RealInnerProductSpace

open CubicNewton
open CubicNewton.Nonconvex
open CubicNewton.Nonconvex.Supplement

/-- Nesterov–Polyak 2006, Lemma 9, p. 200. Let `b₁, …, bₙ` be an orthonormal eigenbasis of the
symmetric operator `H` with eigenvalues `λ₁ ≥ ⋯ ≥ λₙ` (here indexed by `Fin (n+1)`, the last
index playing the role of `n`), and let `g̃_i = ⟨b_i, g⟩` be the coordinates of `g` in this
basis, with `g̃ₙ = 0`. For `ε ≠ 0` put `g(ε) = g + ε bₙ` and let `r*(ε)` be the solution of the
secular equation (5.5) for `g(ε)`,
`r² = Σ_i ⟨b_i, g(ε)⟩² / (λ_i + M r/2)²`, `r > (2/M)(−λₙ)₊`
(for `ε ≠ 0` the solution lies in the interior of the domain, p. 200). Then every limit point, as
`ε → 0` through nonzero values, of the trajectory `h(g(ε); r*(ε)) = −(H + (M r*(ε)/2) I)⁻¹ g(ε)`
is a global minimizer of `h ↦ v_u(g; h)`. -/
theorem solution {n : ℕ} (g : EuclideanSpace ℝ (Fin (n + 1)))
    (H : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (M : ℝ) (hM : 0 < M)
    (b : OrthonormalBasis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (lam : Fin (n + 1) → ℝ) (hb : ∀ i, H (b i) = lam i • b i) (hlam : Antitone lam)
    (hgn : ⟪b (Fin.last n), g⟫ = 0)
    (rstar : ℝ → ℝ)
    (hr : ∀ ε : ℝ, ε ≠ 0 →
      2 / M * max (-lam (Fin.last n)) 0 < rstar ε ∧
      rstar ε ^ 2 = ∑ i, ⟪b i, g + ε • b (Fin.last n)⟫ ^ 2 / (lam i + M * rstar ε / 2) ^ 2)
    (p : EuclideanSpace ℝ (Fin (n + 1)))
    (hp : MapClusterPt p (𝓝[≠] (0 : ℝ))
      (fun ε => hDir (g + ε • b (Fin.last n)) H M (rstar ε))) :
    ∀ h : EuclideanSpace ℝ (Fin (n + 1)), vu g H M p ≤ vu g H M h := by
      intro h
      have hbb : ∀ i j, ⟪b i, b j⟫ = if i = j then (1:ℝ) else 0 :=
        orthonormal_iff_ite.mp b.orthonormal
      have hHc : ∀ x i, ⟪b i, H x⟫ = lam i * ⟪b i, x⟫ := by
        intro x i
        conv_lhs => rw [← b.sum_repr' x]
        rw [map_sum, inner_sum]
        simp only [map_smul, hb, inner_smul_right, hbb]
        simp [Finset.sum_ite_eq, mul_comm]
      have hin : ∀ x y, ⟪x, y⟫ = ∑ i, ⟪b i, x⟫ * ⟪b i, y⟫ := by
        intro x y
        rw [← b.sum_inner_mul_inner x y]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [real_inner_comm x]
      have hnorm : ∀ x, ‖x‖ ^ 2 = ∑ i, ⟪b i, x⟫ ^ 2 := by
        intro x
        rw [← real_inner_self_eq_norm_sq, hin]
        simp [sq]
      have hHq : ∀ x, ⟪H x, x⟫ = ∑ i, lam i * ⟪b i, x⟫ ^ 2 := by
        intro x
        rw [hin]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hHc]; ring
      -- the key fact: for ε ≠ 0, the direction is a global minimizer of vu (g ε)
      have hmin : ∀ ε : ℝ, ε ≠ 0 →
          vu (g + ε • b (Fin.last n)) H M (hDir (g + ε • b (Fin.last n)) H M (rstar ε))
            ≤ vu (g + ε • b (Fin.last n)) H M h := by
        intro ε hε
        obtain ⟨hr1, hr2⟩ := hr ε hε
        set c := g + ε • b (Fin.last n) with hc
        set r := rstar ε with hrdef
        have hr0 : 0 < r := by
          have : 0 ≤ 2 / M * max (-lam (Fin.last n)) 0 :=
            mul_nonneg (by positivity) (le_max_right _ _)
          linarith
        have hμ : ∀ i, 0 < lam i + M * r / 2 := by
          intro i
          have h1 : lam (Fin.last n) ≤ lam i := hlam (Fin.le_last i)
          have h2 : -lam (Fin.last n) < M * r / 2 := by
            have h3 : max (-lam (Fin.last n)) 0 = M / 2 * (2 / M * max (-lam (Fin.last n)) 0) := by
              field_simp
            have h4 := le_max_left (-lam (Fin.last n)) 0
            nlinarith
          linarith
        set A := shiftedOp H M r with hA
        have hAc : ∀ x i, ⟪b i, A x⟫ = (lam i + M * r / 2) * ⟪b i, x⟫ := by
          intro x i
          simp only [hA, shiftedOp, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.id_apply, inner_add_right, inner_smul_right, hHc]
          ring
        have hinj : Function.Injective (A : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) := by
          intro x y hxy
          have hxy' : A x = A y := hxy
          rw [← b.sum_repr' x, ← b.sum_repr' y]
          refine Finset.sum_congr rfl fun i _ => ?_
          have := congrArg (fun z => ⟪b i, z⟫) hxy'
          simp only [hAc] at this
          rw [mul_right_inj' (hμ i).ne'] at this
          rw [this]
        have hsurj := LinearMap.injective_iff_surjective.mp hinj
        let e := (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).toContinuousLinearEquiv
        have he : (e : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) = A := by
          ext x; rfl
        set y := hDir c H M r with hy
        have hAy : A y = -c := by
          rw [hy, hDir, ← hA, ← he, ContinuousLinearMap.inverse_equiv]
          simp
        have hyc : ∀ i, (lam i + M * r / 2) * ⟪b i, y⟫ = -⟪b i, c⟫ := by
          intro i
          rw [← hAc, hAy, inner_neg_right]
        have hny : ‖y‖ = r := by
          have h2 : ‖y‖ ^ 2 = r ^ 2 := by
            rw [hnorm, hr2]
            refine Finset.sum_congr rfl fun i _ => ?_
            have := hμ i
            have hyi : ⟪b i, y⟫ = -⟪b i, c⟫ / (lam i + M * r / 2) := by
              rw [eq_div_iff this.ne']; linarith [hyc i]
            rw [hyi, div_pow, neg_sq]
          nlinarith [norm_nonneg y, sq_nonneg (‖y‖ - r), sq_nonneg (‖y‖ + r)]
        -- now compare
        have hs := hnorm h
        have hry := hnorm y
        rw [hny] at hry
        have hvu : ∀ x, vu c H M x = ∑ i, (⟪b i, c⟫ * ⟪b i, x⟫ + 1 / 2 * (lam i * ⟪b i, x⟫ ^ 2))
            + M / 6 * ‖x‖ ^ 3 := by
          intro x
          simp only [vu, hin c x, hHq, Finset.sum_add_distrib, Finset.mul_sum]
        have hterm : ∀ i, -(M * r / 4) * (⟪b i, h⟫ ^ 2 - ⟪b i, y⟫ ^ 2) ≤
            (⟪b i, c⟫ * ⟪b i, h⟫ + 1 / 2 * (lam i * ⟪b i, h⟫ ^ 2)) -
            (⟪b i, c⟫ * ⟪b i, y⟫ + 1 / 2 * (lam i * ⟪b i, y⟫ ^ 2)) := by
          intro i
          have hci : ⟪b i, c⟫ = -((lam i + M * r / 2) * ⟪b i, y⟫) := by rw [hyc]; ring
          rw [hci]
          nlinarith [mul_nonneg (hμ i).le (sq_nonneg (⟪b i, h⟫ - ⟪b i, y⟫))]
        have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, ← hs, ← hry] at hsum
        rw [hvu h, hvu y, hny]
        have hsn := norm_nonneg h
        nlinarith [mul_nonneg (mul_nonneg hM.le (sq_nonneg (‖h‖ - r))) (by linarith : 0 ≤ 2 * ‖h‖ + r)]
      -- passing to the limit
      set bL := b (Fin.last n)
      set F : ℝ × EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
        fun q => vu (g + q.1 • bL) H M q.2 - vu (g + q.1 • bL) H M h with hF
      have hFc : Continuous F := by
        simp only [hF, vu]
        fun_prop
      by_contra hcon
      push Not at hcon
      have hF0 : 0 < F (0, p) := by simp [hF]; linarith
      have hU : {q | 0 < F q} ∈ 𝓝 ((0 : ℝ), p) :=
        (isOpen_lt continuous_const hFc).mem_nhds hF0
      obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hU
      have hfr := (mapClusterPt_iff_frequently.mp hp) v hv
      have hev : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ε ∈ u ∧ ε ≠ 0 :=
        Filter.Eventually.and (mem_nhdsWithin_of_mem_nhds hu) self_mem_nhdsWithin
      obtain ⟨ε, hεv, hεu, hε0⟩ := (hfr.and_eventually hev).exists
      have h1 : 0 < F (ε, hDir (g + ε • bL) H M (rstar ε)) := huv ⟨hεu, hεv⟩
      have h2 := hmin ε hε0
      simp only [hF] at h1
      linarith
