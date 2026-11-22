-- Prove2me | solution 1 for BlowupUniformConvergence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:14:06.559657+00:00
-- url     : https://prove2.me/submissions/1382bd05-b3c1-4f36-a929-c40a51359a80

import Definitions.Def_PHigherOrder_IteratedDerivAlongRay
import Definitions.Def_PHigherOrder_BlowupUniformConvergence
import Theorems.Thm_IteratedDerivAlongRay


set_option autoImplicit false

theorem _root_.solution (Ω : Set Plane) (hΩ : IsOpen Ω) (u : Plane → ℝ)
    (x₀ : Plane) (hx₀ : x₀ ∈ Ω) (m : ℕ) (hm : 1 ≤ m)
    (hu : ContDiffOn ℝ (m : ℕ∞) u Ω)
    (hvan : ∀ j, 1 ≤ j → j < m → ∀ w : Plane, iteratedFDeriv ℝ j u x₀ (fun _ => w) = 0) :
    ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn
        (fun (r : ℝ) (x : Plane) => (u (x₀ + r • x) - u x₀) / r ^ m)
        (fun x => (1 / (Nat.factorial m : ℝ)) * iteratedFDeriv ℝ m u x₀ (fun _ => x))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (Metric.closedBall (0 : Plane) R) := by
  -- Step 1a: `y ↦ D^m u y` is continuous on the open set `Ω`.
  have hcontD : ContinuousOn (fun y => iteratedFDeriv ℝ m u y) Ω :=
    (hu.continuousOn_iteratedFDerivWithin le_rfl hΩ.uniqueDiffOn).congr
      (iteratedFDerivWithin_of_isOpen m hΩ).symm
  have hcontAt : ContinuousAt (fun y => iteratedFDeriv ℝ m u y) x₀ :=
    hcontD.continuousAt (hΩ.mem_nhds hx₀)
  -- Step 1b: a closed ball around `x₀` inside `Ω`.
  obtain ⟨ρ, hρpos, hρsub⟩ : ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall x₀ ρ ⊆ Ω := by
    obtain ⟨ρ', hρ'pos, hρ'sub⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
    refine ⟨ρ' / 2, by linarith, fun y hy => hρ'sub ?_⟩
    simp only [Metric.mem_closedBall] at hy
    simp only [Metric.mem_ball]
    linarith
  have hm1 : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hm
  have hfacpos : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  intro R hR
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hRm : (0 : ℝ) < R ^ m := pow_pos hR m
  -- Step 1c: the modulus of continuity of `D^m u` at `x₀`, at the scale the estimate needs.
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    Metric.continuousAt_iff.mp hcontAt (ε * (Nat.factorial m : ℝ) / (2 * R ^ m)) (by positivity)
  have hδ₀pos : (0 : ℝ) < min (δ₁ / 2) ρ := lt_min (by linarith) hρpos
  refine Filter.eventually_of_mem (Ioo_mem_nhdsGT (div_pos hδ₀pos hR)) ?_
  intro r hr x hx
  have hr0 : (0 : ℝ) < r := hr.1
  have hxR : ‖x‖ ≤ R := by simpa using hx
  -- `r R` undershoots the modulus, which is what makes every point of the segment admissible.
  have hrR : r * R < min (δ₁ / 2) ρ := by
    have h := mul_lt_mul_of_pos_right hr.2 hR
    rwa [div_mul_cancel₀ _ (ne_of_gt hR)] at h
  have hnormle : ∀ s : ℝ, |s| ≤ r → ‖s • x‖ ≤ r * R := by
    intro s hs
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hs hxR (norm_nonneg x) hr0.le
  have hmem : ∀ s : ℝ, |s| ≤ r → x₀ + s • x ∈ Ω := by
    intro s hs
    refine hρsub ?_
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact (hnormle s hs).trans (hrR.le.trans (min_le_right _ _))
  have hdistD : ∀ s : ℝ, |s| ≤ r →
      ‖iteratedFDeriv ℝ m u (x₀ + s • x) - iteratedFDeriv ℝ m u x₀‖
        < ε * (Nat.factorial m : ℝ) / (2 * R ^ m) := by
    intro s hs
    have hd : dist (x₀ + s • x) x₀ < δ₁ := by
      simp only [dist_eq_norm, add_sub_cancel_left]
      calc ‖s • x‖ ≤ r * R := hnormle s hs
        _ < min (δ₁ / 2) ρ := hrR
        _ ≤ δ₁ / 2 := min_le_left _ _
        _ < δ₁ := by linarith
    simpa [dist_eq_norm] using hδ₁ hd
  -- Step 2: the one-variable restriction, smooth on the open preimage of `Ω`.
  have hγ : ContDiff ℝ (m : ℕ∞) (fun s : ℝ => x₀ + s • x) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hJopen : IsOpen ((fun s : ℝ => x₀ + s • x) ⁻¹' Ω) := hΩ.preimage (by fun_prop)
  have h0J : (0 : ℝ) ∈ (fun s : ℝ => x₀ + s • x) ⁻¹' Ω := by simpa using hx₀
  have hphiJ : ContDiffOn ℝ (m : ℕ∞) (fun s : ℝ => u (x₀ + s • x))
      ((fun s : ℝ => x₀ + s • x) ⁻¹' Ω) :=
    hu.comp hγ.contDiffOn fun s hs => hs
  have hphiAt : ContDiffAt ℝ (m : ℕ∞) (fun s : ℝ => u (x₀ + s • x)) 0 :=
    hphiJ.contDiffAt (hJopen.mem_nhds h0J)
  have hsubJ : Set.uIcc (0 : ℝ) r ⊆ (fun s : ℝ => x₀ + s • x) ⁻¹' Ω := by
    intro s hs
    rw [Set.uIcc_of_le hr0.le] at hs
    exact hmem s (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩)
  -- Step 3: the ray lemma, at every admissible parameter and every order up to `m`.
  have hray : ∀ j : ℕ, j ≤ m → ∀ t : ℝ, |t| ≤ r →
      iteratedDeriv j (fun s : ℝ => u (x₀ + s • x)) t
        = iteratedFDeriv ℝ j u (x₀ + t • x) (fun _ => x) := fun j hj t ht =>
    IteratedDerivAlongRay Ω hΩ u j (hu.of_le (by exact_mod_cast hj)) x₀ x t (hmem t ht)
  -- Step 3b: the Taylor polynomial of order `m - 1` at `0` collapses to the constant `u x₀`.
  have hpoly : taylorWithinEval (fun s : ℝ => u (x₀ + s • x)) (m - 1) (Set.uIcc 0 r) 0 r
      = u x₀ := by
    rw [taylor_within_apply, hm1, Finset.sum_eq_single 0]
    · simp
    · intro j hj hj0
      have hjm : j < m := Finset.mem_range.mp hj
      have hzero : iteratedDerivWithin j (fun s : ℝ => u (x₀ + s • x)) (Set.uIcc 0 r) 0 = 0 := by
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (ne_of_lt hr0))
            (hphiAt.of_le (by exact_mod_cast hjm.le)) Set.left_mem_uIcc,
          hray j hjm.le 0 (by simpa using hr0.le)]
        simpa using hvan j (Nat.one_le_iff_ne_zero.mpr hj0) hjm x
      rw [hzero, smul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (lt_of_lt_of_le Nat.zero_lt_one hm)) h
  -- Step 4: Taylor with Lagrange remainder, in the plain `iteratedDeriv` form.
  obtain ⟨xi, hxi, hTay⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := fun s : ℝ => u (x₀ + s • x))
      (x₀ := (0 : ℝ)) (x := r) (n := m - 1) (ne_of_lt hr0)
      ((hphiJ.mono hsubJ).of_le
        (by
          -- `(m - 1) + 1` and `m` agree, but the index lives in `WithTop ℕ∞` and the
          -- cast does not normalise away, so rewrite with `hm1` after `norm_cast`.
          norm_cast
          rw [hm1]))
  rw [Set.uIoo_of_lt hr0, Set.mem_Ioo] at hxi
  rw [hpoly, hm1] at hTay
  have hximem : |xi| ≤ r := abs_le.mpr ⟨by linarith [hxi.1], hxi.2.le⟩
  rw [hray m le_rfl xi hximem] at hTay
  -- Step 5: the estimate.  Both sides are one multilinear form evaluated at `(x, ..., x)`.
  have hval : (u (x₀ + r • x) - u x₀) / r ^ m
      = (1 / (Nat.factorial m : ℝ)) * iteratedFDeriv ℝ m u (x₀ + xi • x) (fun _ => x) := by
    have hrm : (r : ℝ) ^ m ≠ 0 := ne_of_gt (pow_pos hr0 m)
    rw [sub_zero] at hTay
    field_simp at hTay ⊢
    linarith [hTay]
  have hsplit : (1 / (Nat.factorial m : ℝ)) * iteratedFDeriv ℝ m u x₀ (fun _ => x)
      - (u (x₀ + r • x) - u x₀) / r ^ m
      = (1 / (Nat.factorial m : ℝ))
        * ((iteratedFDeriv ℝ m u x₀ - iteratedFDeriv ℝ m u (x₀ + xi • x)) (fun _ => x)) := by
    rw [hval, sub_apply]
    ring
  have hnormx : ‖(fun _ : Fin m => x)‖ ≤ R :=
    (pi_norm_le_iff_of_nonneg hR.le).mpr fun _ => hxR
  have hopn : ‖(iteratedFDeriv ℝ m u x₀ - iteratedFDeriv ℝ m u (x₀ + xi • x)) (fun _ : Fin m => x)‖
      ≤ ‖iteratedFDeriv ℝ m u x₀ - iteratedFDeriv ℝ m u (x₀ + xi • x)‖ * R ^ m :=
    ContinuousMultilinearMap.le_opNorm_mul_pow_of_le _ hnormx
  have hopn2 : ‖iteratedFDeriv ℝ m u x₀ - iteratedFDeriv ℝ m u (x₀ + xi • x)‖
      < ε * (Nat.factorial m : ℝ) / (2 * R ^ m) := by
    rw [norm_sub_rev]
    exact hdistD xi hximem
  rw [Real.dist_eq, hsplit, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (Nat.factorial m : ℝ))]
  have hfinal :
      |(iteratedFDeriv ℝ m u x₀ - iteratedFDeriv ℝ m u (x₀ + xi • x)) (fun _ : Fin m => x)|
        < ε * (Nat.factorial m : ℝ) / 2 := by
    have hstep :
        |(iteratedFDeriv ℝ m u x₀ - iteratedFDeriv ℝ m u (x₀ + xi • x)) (fun _ : Fin m => x)|
          < ε * (Nat.factorial m : ℝ) / (2 * R ^ m) * R ^ m :=
      lt_of_le_of_lt hopn (mul_lt_mul_of_pos_right hopn2 hRm)
    have hrw : ε * (Nat.factorial m : ℝ) / (2 * R ^ m) * R ^ m
        = ε * (Nat.factorial m : ℝ) / 2 := by
      field_simp
    rwa [hrw] at hstep
  calc 1 / (Nat.factorial m : ℝ)
        * |(iteratedFDeriv ℝ m u x₀ - iteratedFDeriv ℝ m u (x₀ + xi • x)) (fun _ : Fin m => x)|
      < 1 / (Nat.factorial m : ℝ) * (ε * (Nat.factorial m : ℝ) / 2) :=
        mul_lt_mul_of_pos_left hfinal (by positivity)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith
