-- Prove2me | solution 1 for BootstrapRound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:11:49.967817+00:00
-- url     : https://prove2.me/submissions/d3043f7b-1d7b-4cd0-94e4-b26947b0c682

import Definitions.Def_PHigherOrder_DivFormSchauderInput
import Definitions.Def_PHigherOrder_GradientFieldOrderShift
import Definitions.Def_PHigherOrder_IsLinearDivSol
import Definitions.Def_PHigherOrder_BootstrapRound
import Theorems.Thm_GradientFieldOrderShift


set_option autoImplicit false

theorem _root_.solution (hS : DivFormSchauderInput)
    (j : ℕ) (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLL : lam ≤ Lam)
    (M b : ℝ) (hM : 0 < M) (hb : 0 < b)
    (r r' : ℝ) (hr' : 0 < r') (hrr : r' < r) :
    ∃ N : ℝ, 0 < N ∧
      ∀ (v : Plane → ℝ) (A : Plane → (Plane →L[ℝ] Plane)),
        ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 r) →
        (∀ x ∈ Metric.ball (0 : Plane) r, ‖gradient v x‖ ≤ b) →
        (∀ x ∈ Metric.ball (0 : Plane) r, ∀ ξ : Plane,
            lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ ∧ ‖A x ξ‖ ≤ Lam * ‖ξ‖) →
        ContDiffOn ℝ (j : ℕ∞) A (Metric.ball 0 r) →
        (∀ i ≤ j, ∀ x ∈ Metric.ball (0 : Plane) r, ‖iteratedFDeriv ℝ i A x‖ ≤ M) →
        (∀ x ∈ Metric.ball (0 : Plane) r, ∀ y ∈ Metric.ball (0 : Plane) r,
            ‖iteratedFDeriv ℝ j A x - iteratedFDeriv ℝ j A y‖ ≤ M * ‖x - y‖ ^ κ) →
        (∀ e : Plane, IsLinearDivSol (Metric.ball 0 r) A
            (fun x => inner ℝ (gradient v x) e)
            (fun x => gradient (fun y => inner ℝ (gradient v y) e) x)) →
        (∀ m, 1 ≤ m → m ≤ j + 2 → ∀ x ∈ Metric.ball (0 : Plane) r',
            ‖iteratedFDeriv ℝ m v x‖ ≤ N)
          ∧ (∀ x ∈ Metric.ball (0 : Plane) r', ∀ y ∈ Metric.ball (0 : Plane) r',
              ‖iteratedFDeriv ℝ (j + 2) v x - iteratedFDeriv ℝ (j + 2) v y‖
                ≤ N * ‖x - y‖ ^ κ) := by
  obtain ⟨c, hcdef⟩ : ∃ t : ℝ, t = b + 1 := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; linarith
  have hcb : b ≤ c := by rw [hcdef]; linarith
  obtain ⟨S, hS0, hSch⟩ := hS.schauder j κ lam Lam M r r' hκ0 hκ1 hlam hLL hM hr' hrr
  refine ⟨2 * c * S, by positivity, ?_⟩
  intro v A hv hgb hell hAC hAsup hAhol hdiv
  have hUo : IsOpen (Metric.ball (0 : Plane) r) := Metric.isOpen_ball
  have hsub : Metric.ball (0 : Plane) r' ⊆ Metric.ball (0 : Plane) r :=
    Metric.ball_subset_ball (le_of_lt hrr)
  -- The Riesz factorization of the gradient field, its smoothness, and the sharp order-shift
  -- bridges between the scalar function and its gradient field, at a point and at a pair.
  obtain ⟨-, hgC, hbrSup, hbrHol⟩ := GradientFieldOrderShift (Metric.ball 0 r) v hUo hv
  -- The standard orthonormal basis, the component isometries, and the splitting of `Dv`.
  obtain ⟨e, he⟩ : ∃ t : Fin 2 → Plane, t = fun l => (EuclideanSpace.single l (1 : ℝ) : Plane) :=
    ⟨_, rfl⟩
  have hen : ∀ l, ‖e l‖ = 1 := by
    intro l; rw [he]; simp
  have hdec : ∀ z : Plane, z = (inner ℝ z (e 0)) • e 0 + (inner ℝ z (e 1)) • e 1 := by
    intro z
    rw [he]
    have h0 : inner ℝ z (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : Plane) = z 0 := by
      simp [EuclideanSpace.inner_single_right]
    have h1 : inner ℝ z (EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : Plane) = z 1 := by
      simp [EuclideanSpace.inner_single_right]
    rw [h0, h1]
    ext i
    fin_cases i <;> simp
  obtain ⟨L, hL⟩ : ∃ L : Fin 2 → (ℝ →ₗᵢ[ℝ] Plane), ∀ (l : Fin 2) (t : ℝ), L l t = t • e l := by
    refine ⟨fun l => ⟨(LinearMap.id (R := ℝ) (M := ℝ)).smulRight (e l), ?_⟩, fun l t => rfl⟩
    intro t
    show ‖t • e l‖ = ‖t‖
    rw [norm_smul, hen l, mul_one]
  -- The two directional derivatives, their smoothness, and the component splitting of `Dv`.
  have hdAt : ∀ (l : Fin 2) (n : ℕ), ∀ x ∈ Metric.ball (0 : Plane) r,
      ContDiffAt ℝ (n : ℕ∞) (fun y => inner ℝ (gradient v y) (e l)) x := by
    intro l n x hx
    exact (((hgC.contDiffAt (hUo.mem_nhds hx)).inner ℝ contDiffAt_const).of_le
      (by exact_mod_cast le_top))
  have hcomp : ∀ l : Fin 2, (fun y => L l (inner ℝ (gradient v y) (e l)))
      = (L l) ∘ (fun y => inner ℝ (gradient v y) (e l)) := fun l => rfl
  have hcAt : ∀ (l : Fin 2) (n : ℕ), ∀ x ∈ Metric.ball (0 : Plane) r,
      ContDiffAt ℝ (n : ℕ∞) (fun y => L l (inner ℝ (gradient v y) (e l))) x := by
    intro l n x hx
    rw [hcomp l]
    exact (L l).toContinuousLinearMap.contDiff.comp_contDiffAt x (hdAt l n x hx)
  have hsplit : gradient v
      = (fun y => L 0 (inner ℝ (gradient v y) (e 0)))
        + (fun y => L 1 (inner ℝ (gradient v y) (e 1))) := by
    funext z
    show gradient v z = L 0 (inner ℝ (gradient v z) (e 0)) + L 1 (inner ℝ (gradient v z) (e 1))
    rw [hL 0, hL 1]
    exact hdec (gradient v z)
  -- THE REASSEMBLY, in both forms.
  have hreSup : ∀ (n : ℕ), ∀ x ∈ Metric.ball (0 : Plane) r,
      ‖iteratedFDeriv ℝ (n + 1) v x‖
        ≤ ‖iteratedFDeriv ℝ n (fun y => inner ℝ (gradient v y) (e 0)) x‖
          + ‖iteratedFDeriv ℝ n (fun y => inner ℝ (gradient v y) (e 1)) x‖ := by
    intro n x hx
    rw [← hbrSup n x]
    have hkey : iteratedFDeriv ℝ n (gradient v) x
        = iteratedFDeriv ℝ n ((fun y => L 0 (inner ℝ (gradient v y) (e 0)))
            + (fun y => L 1 (inner ℝ (gradient v y) (e 1)))) x := by
      conv_lhs => rw [hsplit]
    rw [hkey, iteratedFDeriv_add_apply (hcAt 0 n x hx) (hcAt 1 n x hx)]
    refine le_trans (norm_add_le _ _) ?_
    rw [hcomp 0, hcomp 1,
      (L 0).norm_iteratedFDeriv_comp_left (hdAt 0 n x hx) (le_refl _),
      (L 1).norm_iteratedFDeriv_comp_left (hdAt 1 n x hx) (le_refl _)]
  have hreHol : ∀ (n : ℕ), ∀ x ∈ Metric.ball (0 : Plane) r, ∀ y ∈ Metric.ball (0 : Plane) r,
      ‖iteratedFDeriv ℝ (n + 1) v x - iteratedFDeriv ℝ (n + 1) v y‖
        ≤ ‖iteratedFDeriv ℝ n (fun z => inner ℝ (gradient v z) (e 0)) x
            - iteratedFDeriv ℝ n (fun z => inner ℝ (gradient v z) (e 0)) y‖
          + ‖iteratedFDeriv ℝ n (fun z => inner ℝ (gradient v z) (e 1)) x
              - iteratedFDeriv ℝ n (fun z => inner ℝ (gradient v z) (e 1)) y‖ := by
    intro n x hx y hy
    rw [← hbrHol n x hx y hy]
    have hkey : ∀ z ∈ Metric.ball (0 : Plane) r, iteratedFDeriv ℝ n (gradient v) z
        = iteratedFDeriv ℝ n ((L 0) ∘ (fun y => inner ℝ (gradient v y) (e 0))) z
          + iteratedFDeriv ℝ n ((L 1) ∘ (fun y => inner ℝ (gradient v y) (e 1))) z := by
      intro z hz
      have h1 : iteratedFDeriv ℝ n (gradient v) z
          = iteratedFDeriv ℝ n ((fun y => L 0 (inner ℝ (gradient v y) (e 0)))
              + (fun y => L 1 (inner ℝ (gradient v y) (e 1)))) z := by
        conv_lhs => rw [hsplit]
      rw [h1, iteratedFDeriv_add_apply (hcAt 0 n z hz) (hcAt 1 n z hz), hcomp 0, hcomp 1]
    rw [hkey x hx, hkey y hy, (sub_add_sub_comm _ _ _ _).symm]
    refine le_trans (norm_add_le _ _) ?_
    have hiso : ∀ (l : Fin 2) (z : Plane), z ∈ Metric.ball (0 : Plane) r →
        iteratedFDeriv ℝ n ((L l) ∘ (fun y => inner ℝ (gradient v y) (e l))) z
          = (L l).toContinuousLinearMap.compContinuousMultilinearMap
              (iteratedFDeriv ℝ n (fun y => inner ℝ (gradient v y) (e l)) z) := by
      intro l z hz
      exact (L l).toContinuousLinearMap.iteratedFDeriv_comp_left (hdAt l n z hz) (le_refl _)
    rw [hiso 0 x hx, hiso 0 y hy, hiso 1 x hx, hiso 1 y hy]
    have hpull : ∀ (l : Fin 2) (P Q : ContinuousMultilinearMap ℝ (fun _ : Fin n => Plane) ℝ),
        (L l).toContinuousLinearMap.compContinuousMultilinearMap P
          - (L l).toContinuousLinearMap.compContinuousMultilinearMap Q
          = (L l).toContinuousLinearMap.compContinuousMultilinearMap (P - Q) := by
      intro l P Q
      ext u
      simp
    rw [hpull 0, hpull 1, LinearIsometry.norm_compContinuousMultilinearMap,
      LinearIsometry.norm_compContinuousMultilinearMap]
  -- NORMALIZATION:  `IsLinearDivSol` is stable under a positive scalar multiple.
  have hnorm : ∀ l : Fin 2, IsLinearDivSol (Metric.ball 0 r) A
      (fun x => c⁻¹ * inner ℝ (gradient v x) (e l))
      (fun x => c⁻¹ • gradient (fun y => inner ℝ (gradient v y) (e l)) x) := by
    intro l
    obtain ⟨hw, hmG, hsq, hwg, heq⟩ := hdiv (e l)
    refine ⟨continuousOn_const.mul hw, hmG.const_smul (c⁻¹ : ℝ), ?_, ?_, ?_⟩
    · intro K hKΩ hK
      refine MeasureTheory.IntegrableOn.congr_fun
        ((hsq K hKΩ hK).const_mul ((c⁻¹ : ℝ) ^ 2)) ?_ hK.measurableSet
      intro z _
      dsimp only
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), mul_pow]
    · intro φ hφ hφs hφΩ
      have h := hwg φ hφ hφs hφΩ
      have e1 : ∀ z : Plane, (c⁻¹ * inner ℝ (gradient v z) (e l)) • gradient φ z
          = c⁻¹ • ((inner ℝ (gradient v z) (e l) : ℝ) • gradient φ z) := fun z => mul_smul _ _ _
      have e2 : ∀ z : Plane,
          φ z • (c⁻¹ • gradient (fun y => inner ℝ (gradient v y) (e l)) z)
            = c⁻¹ • (φ z • gradient (fun y => inner ℝ (gradient v y) (e l)) z) :=
        fun z => smul_comm _ _ _
      simp only [e1, e2]
      rw [MeasureTheory.integral_smul, MeasureTheory.integral_smul, h, smul_neg]
    · intro φ hφ hφs hφΩ
      have h := heq φ hφ hφs hφΩ
      have e3 : ∀ z : Plane,
          inner ℝ (A z (c⁻¹ • gradient (fun y => inner ℝ (gradient v y) (e l)) z))
              (gradient φ z)
            = c⁻¹ * inner ℝ (A z (gradient (fun y => inner ℝ (gradient v y) (e l)) z))
                (gradient φ z) := by
        intro z
        rw [map_smul, real_inner_smul_left]
      simp only [e3]
      rw [MeasureTheory.integral_const_mul, h, mul_zero]
  -- the normalized solutions are bounded by `1`
  have hbd1 : ∀ l : Fin 2, ∀ x ∈ Metric.ball (0 : Plane) r,
      |c⁻¹ * inner ℝ (gradient v x) (e l)| ≤ 1 := by
    intro l x hx
    have hcs : |(inner ℝ (gradient v x) (e l) : ℝ)| ≤ ‖gradient v x‖ := by
      have := abs_real_inner_le_norm (gradient v x) (e l)
      rwa [hen l, mul_one] at this
    rw [abs_mul, abs_of_pos (inv_pos.mpr hc)]
    rw [inv_mul_le_iff₀ hc, mul_one]
    exact le_trans (le_trans hcs (hgb x hx)) hcb
  -- ONE SCHAUDER ROUND in each coordinate direction, with the scaling undone.
  have hround : ∀ l : Fin 2,
      (∀ m ≤ j + 1, ∀ x ∈ Metric.ball (0 : Plane) r',
          ‖iteratedFDeriv ℝ m (fun y => inner ℝ (gradient v y) (e l)) x‖ ≤ c * S)
        ∧ (∀ x ∈ Metric.ball (0 : Plane) r', ∀ y ∈ Metric.ball (0 : Plane) r',
            ‖iteratedFDeriv ℝ (j + 1) (fun z => inner ℝ (gradient v z) (e l)) x
              - iteratedFDeriv ℝ (j + 1) (fun z => inner ℝ (gradient v z) (e l)) y‖
              ≤ c * S * ‖x - y‖ ^ κ) := by
    intro l
    obtain ⟨-, hsup, hhol⟩ := hSch A _ _ hell hAC hAsup hAhol (hnorm l) (hbd1 l)
    -- undo the scaling:  `D^m (c⁻¹ w) = c⁻¹ • D^m w`
    have hscale : ∀ (m : ℕ) (z : Plane), z ∈ Metric.ball (0 : Plane) r →
        iteratedFDeriv ℝ m (fun x => c⁻¹ * inner ℝ (gradient v x) (e l)) z
          = c⁻¹ • iteratedFDeriv ℝ m (fun x => inner ℝ (gradient v x) (e l)) z := by
      intro m z hz
      have hfe : (fun x => c⁻¹ * inner ℝ (gradient v x) (e l))
          = (c⁻¹ : ℝ) • (fun x => (inner ℝ (gradient v x) (e l) : ℝ)) := by
        funext x; rfl
      rw [hfe]
      exact iteratedFDeriv_const_smul_apply (hdAt l m z hz)
    have hcinv : ‖(c⁻¹ : ℝ)‖ = c⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    refine ⟨?_, ?_⟩
    · intro m hm x hx
      have h := hsup m hm x hx
      rw [hscale m x (hsub hx), norm_smul, hcinv] at h
      rw [inv_mul_le_iff₀ hc] at h
      calc ‖iteratedFDeriv ℝ m (fun y => inner ℝ (gradient v y) (e l)) x‖
          ≤ c * S := h
        _ = c * S := rfl
    · intro x hx y hy
      have h := hhol x hx y hy
      rw [hscale (j + 1) x (hsub hx), hscale (j + 1) y (hsub hy), ← smul_sub, norm_smul,
        hcinv] at h
      rw [inv_mul_le_iff₀ hc] at h
      calc ‖iteratedFDeriv ℝ (j + 1) (fun z => inner ℝ (gradient v z) (e l)) x
              - iteratedFDeriv ℝ (j + 1) (fun z => inner ℝ (gradient v z) (e l)) y‖
          ≤ c * (S * ‖x - y‖ ^ κ) := h
        _ = c * S * ‖x - y‖ ^ κ := by ring
  -- CONCLUSION:  reassemble.
  refine ⟨?_, ?_⟩
  · intro m hm1 hm2 x hx
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hn : n ≤ j + 1 := by omega
    refine le_trans (hreSup n x (hsub hx)) ?_
    have h0 := (hround 0).1 n hn x hx
    have h1 := (hround 1).1 n hn x hx
    linarith
  · intro x hx y hy
    have hj : j + 2 = (j + 1) + 1 := by omega
    rw [hj]
    refine le_trans (hreHol (j + 1) x (hsub hx) y (hsub hy)) ?_
    have h0 := (hround 0).2 x hx y hy
    have h1 := (hround 1).2 x hx y hy
    have hpow : (0 : ℝ) ≤ ‖x - y‖ ^ κ := Real.rpow_nonneg (norm_nonneg _) κ
    nlinarith [h0, h1]
