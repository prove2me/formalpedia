-- Prove2me | solution 3 for FourExp.transcendence_criterion_continuous
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T04:14:36.011984+00:00
-- url     : https://prove2.me/submissions/41f98a19-edae-4c25-83c8-f4af23bad773

import Mathlib
import Theorems.Thm_FourExp_height_dvd_le
import Theorems.Thm_FourExp_small_irreducible_factor
import Theorems.Thm_FourExp_dvd_of_small_values_at_scale

/-!
# A transcendence criterion with continuous scales

Suppose `α` is transcendental, and put `C = max (10 + ε) ((4 + ε) a₁ a₂)`. Heights are Mathlib's
`Polynomial.supNorm`, the largest absolute value of a coefficient.

* **A small factor.** For large `q`, Gel'fond's lemma (`FourExp.small_irreducible_factor`, with
  `H = exp σ₁(q)`, `n = σ₂(q)` and `λ = C`), applied to the primitive part of `P q`, gives an
  irreducible `Q` of positive degree and a real `s ≥ 1` with
  `‖Q(α)‖ < exp(-(C - 6) σ₁(q) σ₂(q) / s)`, height at most `exp(3 σ₁(q) / s)` and degree at most
  `σ₂(q) / s`.
* **Its scale set** `T(Q) = {x ≥ 1 | height ≤ exp(3 σ₁(x)), degree ≤ (1 + ε/2) σ₂(x)}` is closed
  and contains `q`. At a transcendental point, the finitely many non-zero integer polynomials of
  bounded degree and height take values bounded away from `0` (`exists_pos_le_norm_aeval`). With
  `q` large, `‖Q(α)‖` is below that bound for the degree and height allowed at a fixed scale `Zs`,
  so `T(Q)` lies in `[Zs, ∞)`.
* **The least scale.** Let `z = min T(Q)`, `u = σ₁(z)` and `v = σ₂(z)`. By continuity, the two
  bounds are not both strict at `z`. Either way `uv ≤ σ₁(q) σ₂(q) / s`, so
  `‖Q(α)‖ < exp(-(4 + ε) uv)`.
* **A contradiction.** For `N = ⌊z⌋₊` the growth bounds give `uv ≤ a₁ a₂ σ₁(N) σ₂(N)`, so
  `‖P_N(α)‖ < exp(-(4 + ε) uv)` as well. The resultant step at the scale `(u, v)`
  (`FourExp.dvd_of_small_values_at_scale`) gives `Q ∣ P_N`. Gel'fond's height bound
  (`FourExp.height_dvd_le`) and `deg Q ≤ deg P_N ≤ v < (1 + ε/2) v` then make both bounds strict
  at `z`.
-/

open Filter Topology Polynomial

namespace W5_transcendence_criterion_continuous

/-- At a transcendental `α`, the non-zero integer polynomials of bounded degree and height take
values bounded away from `0`: there are finitely many of them. -/
theorem exists_pos_le_norm_aeval (α : ℂ) (hα : Transcendental ℚ α) (D : ℕ) (K : ℝ) :
    ∃ m : ℝ, 0 < m ∧ ∀ Q : ℤ[X], Q ≠ 0 → Q.natDegree ≤ D → (∀ i, |(Q.coeff i : ℝ)| ≤ K) →
      m ≤ ‖aeval α Q‖ := by
  classical
  set S := {Q : ℤ[X] | Q ≠ 0 ∧ Q.natDegree ≤ D ∧ ∀ i, |(Q.coeff i : ℝ)| ≤ K}
  have hfin : S.Finite := by
    let π : ℤ[X] → Fin (D + 1) → ℤ := fun f i => f.coeff i
    refine ((Set.Finite.pi fun _ => Set.finite_Icc (-⌈K⌉) ⌈K⌉).subset ?_).of_finite_image
      (?_ : Set.InjOn π S)
    · rintro _ ⟨Q, hQ, rfl⟩ i -
      have h := abs_le.1 ((hQ.2.2 i).trans (Int.le_ceil K))
      exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    · exact fun x hx y hy hxy => (ext_iff_natDegree_le hx.2.1 hy.2.1).2 fun i hi =>
        congr_fun hxy ⟨i, Nat.lt_succ_of_le hi⟩
  have hval : ∀ Q ∈ hfin.toFinset, 0 < ‖aeval α Q‖ := fun Q hQ => norm_pos_iff.2 fun h =>
    hα ⟨Q.map (algebraMap ℤ ℚ), (Polynomial.map_ne_zero_iff (algebraMap ℤ ℚ).injective_int).2
      (hfin.mem_toFinset.1 hQ).1, by rwa [aeval_map_algebraMap]⟩
  rcases hfin.toFinset.eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun Q h0 hD hK => by simpa [he] using hfin.mem_toFinset.2 ⟨h0, hD, hK⟩⟩
  · exact ⟨_, (Finset.lt_inf'_iff hne).2 hval, fun Q h0 hD hK =>
      Finset.inf'_le _ (hfin.mem_toFinset.2 ⟨h0, hD, hK⟩)⟩

end W5_transcendence_criterion_continuous

open W5_transcendence_criterion_continuous in
theorem solution
    (α : ℂ) (ε : ℝ) (hε : 0 < ε)
    (σ₁ σ₂ : ℝ → ℝ) (hσ₁ : StrictMono σ₁) (hσ₂ : StrictMono σ₂)
    (hσ₁c : Continuous σ₁) (hσ₂c : Continuous σ₂)
    (hσ₁t : Tendsto σ₁ atTop atTop) (hσ₂t : Tendsto σ₂ atTop atTop)
    (a₁ a₂ : ℝ) (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂)
    (h₂₁ : ∀ x : ℝ, 1 ≤ x → σ₂ x ≤ σ₁ x)
    (hgrowth₁ : ∀ x : ℝ, 1 ≤ x → σ₁ (x + 1) ≤ a₁ * σ₁ x)
    (hgrowth₂ : ∀ x : ℝ, 1 ≤ x → σ₂ (x + 1) ≤ a₂ * σ₂ x)
    (N₀ : ℕ) (P : ℕ → Polynomial ℤ)
    (hP_ne : ∀ N : ℕ, N₀ < N → P N ≠ 0)
    (hP_height : ∀ N : ℕ, N₀ < N → ∀ i : ℕ, |((P N).coeff i : ℝ)| ≤ Real.exp (σ₁ N))
    (hP_deg : ∀ N : ℕ, N₀ < N → ((P N).natDegree : ℝ) ≤ σ₂ N)
    (hP_small : ∀ N : ℕ, N₀ < N →
      ‖Polynomial.aeval α (P N)‖ <
        Real.exp (-(max (10 + ε) ((4 + ε) * (a₁ * a₂)) * σ₁ N * σ₂ N))) :
    IsAlgebraic ℚ α := by
  classical
  by_contra hαalg
  have hα : Transcendental ℚ α := hαalg
  set C : ℝ := max (10 + ε) ((4 + ε) * (a₁ * a₂)) with hCdef
  have hC10 : 10 + ε ≤ C := le_max_left _ _
  have hCa : (4 + ε) * (a₁ * a₂) ≤ C := le_max_right _ _
  have hco : ∀ (Q : ℤ[X]) i, |(Q.coeff i : ℝ)| ≤ Q.supNorm := fun Q i => by
    simpa only [Int.norm_eq_abs] using Q.le_supNorm i
  -- where `σ₂ ≥ 1`
  obtain ⟨X₀, hX₀1, hX₀⟩ : ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ x, X₀ ≤ x → 1 ≤ σ₂ x := by
    obtain ⟨X, hX⟩ := eventually_atTop.mp (hσ₂t.eventually_ge_atTop 1)
    exact ⟨max X 1, le_max_right _ _, fun x hx => hX x (le_of_max_le_left hx)⟩
  have hσ₁ge : ∀ x, X₀ ≤ x → 1 ≤ σ₁ x := fun x hx => (hX₀ x hx).trans (h₂₁ x (by linarith))
  -- Step 1: a small irreducible factor of each `P q`, through its primitive part
  have step1 : ∀ q : ℕ, N₀ < q → X₀ ≤ (q : ℝ) → ∃ Q : ℤ[X], Irreducible Q ∧ 1 ≤ Q.natDegree ∧
      ∃ s : ℝ, 1 ≤ s ∧ ‖aeval α Q‖ < Real.exp (-((C - 6) * σ₁ q * σ₂ q / s)) ∧
        Q.supNorm ≤ Real.exp (3 * σ₁ q / s) ∧ (Q.natDegree : ℝ) ≤ σ₂ q / s := by
    intro q hq hqX
    have hdec := eq_C_content_mul_primPart (P q)
    have hc1 : (1 : ℝ) ≤ |((P q).content : ℝ)| := by
      exact_mod_cast Int.one_le_abs (mt content_eq_zero_iff.1 (hP_ne q hq))
    have hpH : ∀ i, |((P q).primPart.coeff i : ℝ)| ≤ Real.exp (σ₁ q) := fun i => by
      have h := hP_height q hq i
      rw [hdec, coeff_C_mul, Int.cast_mul, abs_mul] at h
      nlinarith [abs_nonneg ((P q).primPart.coeff i : ℝ)]
    have hpα : ‖aeval α (P q).primPart‖ ≤ ‖aeval α (P q)‖ := by
      conv_rhs => rw [hdec, map_mul, aeval_C, norm_mul]
      exact le_mul_of_one_le_left (norm_nonneg _) (by simpa using hc1)
    obtain ⟨Q, -, hprim, hirr, s, hs, hQα, hQh, hQd⟩ := FourExp.small_irreducible_factor α hα
      (P q).primPart (isPrimitive_primPart _) (Real.exp (σ₁ q)) (σ₂ q) C hpH
      (by rw [Real.log_exp]; exact h₂₁ q (by linarith))
      (by rw [natDegree_primPart]; exact hP_deg q hq) (by linarith)
      (by rw [← Real.exp_mul]; exact hpα.trans_lt ((hP_small q hq).trans_eq (by congr 1; ring)))
    refine ⟨Q, hirr, ?_, s, by exact_mod_cast hs, ?_, ?_, hQd⟩
    · have := ((IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).1 hirr).natDegree_pos
      rwa [natDegree_map_eq_of_injective (Int.castRingHom ℚ).injective_int] at this
    · rw [← Real.exp_mul] at hQα; convert hQα using 2; ring
    · obtain ⟨i, hi⟩ := Q.exists_eq_supNorm
      rw [hi, Int.norm_eq_abs]
      refine (hQh i).trans ?_
      rw [← Real.exp_mul, ← Real.exp_add, mul_one_div, ← add_div]
      exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith [h₂₁ q (by linarith)])
        (by positivity))
  -- the scale set of `Q`: the `x ≥ 1` whose height and degree bounds `Q` meets
  let T : ℤ[X] → Set ℝ := fun Q =>
    {x | 1 ≤ x ∧ Q.supNorm ≤ Real.exp (3 * σ₁ x) ∧ (Q.natDegree : ℝ) ≤ (1 + ε / 2) * σ₂ x}
  have hTc : ∀ Q, IsClosed (T Q) := fun Q =>
    (isClosed_le continuous_const continuous_id).inter ((isClosed_le continuous_const
      (Real.continuous_exp.comp (continuous_const.mul hσ₁c))).inter
        (isClosed_le continuous_const (continuous_const.mul hσ₂c)))
  obtain ⟨U, hU⟩ := FourExp.dvd_of_small_values_at_scale α ε hε
  obtain ⟨Z₁, hZ₁⟩ := eventually_atTop.mp (hσ₁t.eventually_ge_atTop U)
  set Zs : ℝ := max (max (X₀ + 1) ((N₀ : ℝ) + 2)) Z₁ with hZs
  -- Step 2: a factor with value below every bounded polynomial, so its scale set lies past `Zs`
  obtain ⟨m, hm0, hm⟩ :=
    exists_pos_le_norm_aeval α hα ⌈(1 + ε / 2) * σ₂ Zs⌉₊ (Real.exp (3 * σ₁ Zs))
  obtain ⟨q, hq, hqX, hqm⟩ : ∃ q : ℕ, N₀ < q ∧ X₀ ≤ (q : ℝ) ∧ -Real.log m / (C - 6) ≤ σ₁ q :=
    ((eventually_gt_atTop N₀).and (((tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      X₀).and ((hσ₁t.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _))).exists
  obtain ⟨Q, hirr, hδ1, s, hs, hQα, hQh, hQd⟩ := step1 q hq hqX
  have hσ₁q := hσ₁ge q hqX
  have hσ₂q := hX₀ q hqX
  have hqT : (q : ℝ) ∈ T Q := ⟨by linarith,
    hQh.trans (Real.exp_le_exp.2 (div_le_self (by linarith) hs)),
    hQd.trans ((div_le_self (by linarith) hs).trans
      (le_mul_of_one_le_left (by linarith) (by linarith)))⟩
  have hQm : ‖aeval α Q‖ < m := by
    refine hQα.trans_le ((Real.exp_le_exp.2 ?_).trans_eq (Real.exp_log hm0))
    have h1 : (1 : ℝ) ≤ σ₂ q / s := (by exact_mod_cast hδ1 : (1 : ℝ) ≤ Q.natDegree).trans hQd
    have h2 := (div_le_iff₀ (by linarith : (0 : ℝ) < C - 6)).1 hqm
    rw [show (C - 6) * σ₁ q * σ₂ q / s = (C - 6) * σ₁ q * (σ₂ q / s) by ring]
    nlinarith [mul_le_mul_of_nonneg_left h1 (by nlinarith : (0 : ℝ) ≤ (C - 6) * σ₁ q)]
  have hZ : ∀ x ∈ T Q, Zs ≤ x := fun x ⟨_, hxh, hxd⟩ => by
    by_contra! hx
    refine absurd hQm (not_lt.2 (hm Q hirr.ne_zero ?_ fun i => (hco Q i).trans (hxh.trans ?_)))
    · exact_mod_cast (hxd.trans (mul_le_mul_of_nonneg_left (hσ₂.monotone hx.le)
        (by positivity))).trans (Nat.le_ceil _)
    · exact Real.exp_le_exp.2 (by linarith [hσ₁.monotone hx.le])
  -- Step 3: `z`, the least point of the scale set, where one of its bounds is tight
  have hbdd : BddBelow (T Q) := ⟨1, fun x hx => hx.1⟩
  set z := sInf (T Q) with hzdef
  have hzT : z ∈ T Q := (hTc Q).csInf_mem ⟨q, hqT⟩ hbdd
  have hzZ : Zs ≤ z := hZ z hzT
  have hzq : z ≤ q := csInf_le hbdd hqT
  have hz1 : X₀ + 1 ≤ z := (le_max_left _ _).trans ((le_max_left _ _).trans hzZ)
  have hz2 : (N₀ : ℝ) + 2 ≤ z := (le_max_right _ _).trans ((le_max_left _ _).trans hzZ)
  have hz3 : Z₁ ≤ z := (le_max_right _ _).trans hzZ
  have hnotboth : ¬ (Q.supNorm < Real.exp (3 * σ₁ z) ∧
      (Q.natDegree : ℝ) < (1 + ε / 2) * σ₂ z) := by
    rintro ⟨h1, h2⟩
    have hev : ∀ᶠ x in 𝓝 z, 1 < x ∧ Q.supNorm < Real.exp (3 * σ₁ x) ∧
        (Q.natDegree : ℝ) < (1 + ε / 2) * σ₂ x :=
      (lt_mem_nhds (by linarith)).and
        ((((Real.continuous_exp.comp (continuous_const.mul hσ₁c)).tendsto z).eventually
          (lt_mem_nhds h1)).and
            (((continuous_const.mul hσ₂c).tendsto z).eventually (lt_mem_nhds h2)))
    obtain ⟨x, hxz, h1x, h2x, h3x⟩ := hev.exists_lt
    exact absurd (csInf_le hbdd ⟨h1x.le, h2x.le, h3x.le⟩) (not_le.2 hxz)
  obtain ⟨-, hlh, hdz⟩ := hzT
  set u := σ₁ z with hudef
  set v := σ₂ z with hvdef
  have hv1 : 1 ≤ v := hX₀ z (by linarith)
  have hvu : v ≤ u := h₂₁ z (by linarith)
  have huq : u ≤ σ₁ q := hσ₁.monotone hzq
  have hvq : v ≤ σ₂ q := hσ₂.monotone hzq
  -- (3.9)
  have h39 : u * v ≤ σ₁ q * σ₂ q / s := by
    rcases not_and_or.mp hnotboth with ha | hb
    · have h := Real.exp_le_exp.1 ((not_lt.1 ha).trans hQh)
      rw [mul_div_assoc] at h
      calc u * v ≤ (σ₁ q / s) * σ₂ q :=
            mul_le_mul (by linarith) hvq (by linarith) (div_nonneg (by linarith) (by linarith))
        _ = σ₁ q * σ₂ q / s := by ring
    · calc u * v ≤ σ₁ q * (σ₂ q / s) :=
            mul_le_mul huq (by nlinarith [not_lt.1 hb]) (by linarith) (by linarith)
        _ = σ₁ q * σ₂ q / s := by ring
  have hQsmall : ‖aeval α Q‖ < Real.exp (-((4 + ε) * (u * v))) := by
    refine hQα.trans_le (Real.exp_le_exp.2 ?_)
    rw [show (C - 6) * σ₁ q * σ₂ q / s = (C - 6) * (σ₁ q * σ₂ q / s) by ring]
    nlinarith [mul_le_mul_of_nonneg_left h39 (by linarith : (0 : ℝ) ≤ C - 6),
      mul_le_mul_of_nonneg_right (by linarith : 4 + ε ≤ C - 6) (by nlinarith : (0 : ℝ) ≤ u * v)]
  -- the polynomial `P N`, `N = ⌊z⌋₊`, is as small at the scale `(u, v)`
  set N : ℕ := ⌊z⌋₊ with hNdef
  have hN1 : (N : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hN2 : z - 1 ≤ N := by linarith [Nat.lt_floor_add_one z]
  have hNN₀ : N₀ < N := by exact_mod_cast (show (N₀ : ℝ) < N by linarith)
  have hPsmall : ‖aeval α (P N)‖ < Real.exp (-((4 + ε) * (u * v))) := by
    refine (hP_small N hNN₀).trans_le (Real.exp_le_exp.2 ?_)
    have hg₁ : u ≤ a₁ * σ₁ (z - 1) := by simpa using hgrowth₁ (z - 1) (by linarith)
    have hg₂ : v ≤ a₂ * σ₂ (z - 1) := by simpa using hgrowth₂ (z - 1) (by linarith)
    have h₁ := hσ₁.monotone hN2
    have h₂ := hσ₂.monotone hN2
    have hm₂ := hX₀ (z - 1) (by linarith)
    have hm₁ := h₂₁ (z - 1) (by linarith)
    have h1 : u * v ≤ (a₁ * a₂) * (σ₁ N * σ₂ N) := by
      linarith [mul_le_mul hg₁ hg₂ (by linarith) (mul_nonneg (by linarith) (by linarith)),
        mul_le_mul_of_nonneg_left (mul_le_mul h₁ h₂ (by linarith) (by linarith))
          (mul_nonneg (by linarith) (by linarith) : (0 : ℝ) ≤ a₁ * a₂)]
    linarith [mul_le_mul_of_nonneg_right hCa (mul_nonneg (by linarith) (by linarith) :
      (0 : ℝ) ≤ σ₁ N * σ₂ N), mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 4 + ε)]
  -- the resultant step at the scale `(u, v)`
  have hdvd : Q ∣ P N := hU u v (hZ₁ z hz3) hv1 hvu (P N) Q hirr
    (fun i => (hP_height N hNN₀ i).trans (Real.exp_le_exp.2 (hσ₁.monotone hN1)))
    ((hP_deg N hNN₀).trans (hσ₂.monotone hN1)) (fun i => (hco Q i).trans hlh) hdz hPsmall hQsmall
  -- Gel'fond's height bound makes both scale bounds strict at `z`
  have hd : ((P N).natDegree : ℝ) ≤ v := (hP_deg N hNN₀).trans (hσ₂.monotone hN1)
  refine hnotboth ⟨?_, ?_⟩
  · obtain ⟨i, hi⟩ := Q.exists_eq_supNorm
    rw [hi, Int.norm_eq_abs]
    refine (FourExp.height_dvd_le (P N) Q (hP_ne N hNN₀) hdvd _ (hP_height N hNN₀) i).trans_lt ?_
    rw [← Real.exp_add]
    exact Real.exp_lt_exp.2 (by linarith [hσ₁.monotone hN1])
  · have : (Q.natDegree : ℝ) ≤ (P N).natDegree := by
      exact_mod_cast natDegree_le_of_dvd hdvd (hP_ne N hNN₀)
    linarith [mul_pos hε (by linarith : (0 : ℝ) < v)]
