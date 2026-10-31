-- Prove2me | solution 1 for FiniteEnergyPlane.tendstoZeroCInfty_comp_periodic_of_drift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T15:57:51.859476+00:00
-- url     : https://prove2.me/submissions/94b0f1fe-cab4-4da7-aadc-5ee23163fbe0

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_exists_norm_le_mul_norm_of_periodic
import Theorems.Thm_FiniteEnergyPlane_exists_bound_iteratedFDeriv_comp_periodic
import Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd



namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

/-- `D^i` of `q ↦ (θ q - θ p, v q)` at `p`, in norm. -/
lemma cd_norm_iteratedFDeriv_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ : ℝ × ℝ → ℝ} {v : ℝ × ℝ → E} {p : ℝ × ℝ} (hθ : ContDiffAt ℝ ∞ θ p)
    (hv : ContDiffAt ℝ ∞ v p) {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun q => (θ q - θ p, v q)) p‖ =
      max ‖iteratedFDeriv ℝ i θ p‖ ‖iteratedFDeriv ℝ i v p‖ := by
  have hθc : ContDiffAt ℝ ∞ (fun q => θ q - θ p) p := hθ.sub contDiffAt_const
  rw [iteratedFDeriv_prodMk hθc hv (by exact_mod_cast le_top),
    ContinuousMultilinearMap.opNorm_prod]
  congr 2
  show iteratedFDeriv ℝ i (θ - fun _ => θ p) p = _
  rw [iteratedFDeriv_sub_apply (hθ.of_le (by exact_mod_cast le_top)) contDiffAt_const,
    iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, sub_zero]

/-- Let `Φ(φ, v)` be smooth on `ℝ × B(0, r)`, `T`-periodic in `φ`, with `Φ(φ, 0) = 0`. Let `θ` be
smooth on a half-plane `(s₂, ∞) × ℝ` with every derivative of order `≥ 1` bounded there for large
`s` (`θ` itself need not be bounded). If `v(s, t) → 0` in `C^∞` on the end, then so does
`Φ(a t + θ(s, t), v(s, t))`, for any `a ∈ ℝ`. -/
theorem tendstoZeroCInfty_comp_periodic_of_drift_aux {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝ × E → F) (T r a : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ ∞ Φ (Set.univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (v : E), ‖v‖ < r → Φ (φ + T, v) = Φ (φ, v))
    (h0 : ∀ φ : ℝ, Φ (φ, 0) = 0) (θ : ℝ × ℝ → ℝ)
    (hθs : ∃ s₂ : ℝ, ContDiffOn ℝ ∞ θ (Set.Ioi s₂ ×ˢ Set.univ))
    (hθ : ∀ m : ℕ, 1 ≤ m → ∃ B s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ, ‖iteratedFDeriv ℝ m θ (s, t)‖ ≤ B)
    (v : ℝ × ℝ → E) (hv : TendstoZeroCInfty v) :
    TendstoZeroCInfty (fun p : ℝ × ℝ => Φ (a * p.2 + θ p, v p)) := by
  obtain ⟨sθ, hθC⟩ := hθs
  obtain ⟨sv, hvC⟩ := hv.1
  obtain ⟨L, hL0, hL⟩ := exists_norm_le_mul_norm_of_periodic Φ T r hT hr
    (hΦ.of_le (by exact_mod_cast le_top)) hper h0
  obtain ⟨sr, hsr⟩ := hv.2 0 (r / 2) (half_pos hr)
  have hvs : ∀ s ≥ sr, ∀ t, ‖v (s, t)‖ ≤ r / 2 := fun s hs t => by
    simpa [norm_iteratedFDeriv_zero] using hsr s hs t
  set s₃ := max (max sθ sv) sr with hs₃
  have hU : IsOpen (Set.Ioi s₃ ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hθU : ContDiffOn ℝ ∞ θ (Set.Ioi s₃ ×ˢ Set.univ) :=
    hθC.mono (Set.prod_mono (Set.Ioi_subset_Ioi (by simp [hs₃])) le_rfl)
  have hvU : ContDiffOn ℝ ∞ v (Set.Ioi s₃ ×ˢ Set.univ) :=
    hvC.mono (Set.prod_mono (Set.Ioi_subset_Ioi (by simp [hs₃])) le_rfl)
  have hsm : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Φ (a * p.2 + θ p, v p))
      (Set.Ioi s₃ ×ˢ Set.univ) := by
    refine hΦ.comp (((contDiff_const.mul contDiff_snd).contDiffOn.add hθU).prodMk hvU) ?_
    rintro ⟨s, t⟩ ⟨hs, -⟩
    refine ⟨trivial, mem_ball_zero_iff.2 ?_⟩
    exact lt_of_le_of_lt (hvs s (le_trans (by simp [hs₃]) (le_of_lt hs)) t) (half_lt_self hr)
  -- uniform convergence
  have h0u : TendstoZeroUnif (fun p : ℝ × ℝ => Φ (a * p.2 + θ p, v p)) := by
    intro e he
    obtain ⟨se, hse⟩ := hv.2 0 (min (r / 2) (e / (L + 1))) (lt_min (half_pos hr) (by positivity))
    refine ⟨se, fun s hs t => ?_⟩
    have h1 : ‖v (s, t)‖ ≤ min (r / 2) (e / (L + 1)) := by
      simpa [norm_iteratedFDeriv_zero] using hse s hs t
    calc ‖Φ (a * (s, t).2 + θ (s, t), v (s, t))‖ ≤ L * ‖v (s, t)‖ :=
          hL _ _ (h1.trans (min_le_left _ _))
      _ ≤ L * (e / (L + 1)) := mul_le_mul_of_nonneg_left (h1.trans (min_le_right _ _)) hL0
      _ ≤ e := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  -- bounded derivatives
  refine tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd _ s₃ hsm h0u fun m => ?_
  set Ψ : ℝ × (ℝ × E) → F := fun z => Φ (z.1 + z.2.1, z.2.2) with hΨ
  have hΨs : ContDiffOn ℝ ∞ Ψ (Set.univ ×ˢ ball (0 : ℝ × E) r) := by
    refine hΦ.comp ((contDiff_fst.add contDiff_snd.fst).prodMk contDiff_snd.snd).contDiffOn ?_
    rintro ⟨φ, y, w⟩ ⟨-, hz⟩
    refine ⟨trivial, mem_ball_zero_iff.2 ?_⟩
    exact lt_of_le_of_lt (norm_snd_le (y, w)) (mem_ball_zero_iff.1 hz)
  have hΨp : ∀ (φ : ℝ) (z : ℝ × E), ‖z‖ < r → Ψ (φ + T, z) = Ψ (φ, z) := by
    intro φ z hz
    simp only [hΨ]
    rw [show φ + T + z.1 = φ + z.1 + T by ring]
    exact hper _ _ (lt_of_le_of_lt (norm_snd_le z) hz)
  -- derivative bounds of `θ` (orders `j + 1`) and `v` (orders `j`)
  have hθ' : ∀ j : ℕ, ∃ B s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ, ‖iteratedFDeriv ℝ (j + 1) θ (s, t)‖ ≤ B :=
    fun j => hθ (j + 1) (by omega)
  choose Bθ sθ' hBθ using hθ'
  choose sv' hsv' using fun j : ℕ => hv.2 j 1 one_pos
  set B : ℝ := r / 2 + 1 + ∑ j ∈ Finset.range (m + 1), |Bθ j| with hB
  have hBθle : ∀ j ≤ m, Bθ j ≤ B := by
    intro j hj
    have : |Bθ j| ≤ ∑ j ∈ Finset.range (m + 1), |Bθ j| :=
      Finset.single_le_sum (f := fun j => |Bθ j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    have := le_abs_self (Bθ j)
    linarith [hr]
  have hBθ0 : Bθ 0 ≤ B := hBθle 0 (Nat.zero_le _)
  have hB1 : 1 ≤ B := by
    have : 0 ≤ ∑ j ∈ Finset.range (m + 1), |Bθ j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith [hr]
  have hBr : r / 2 ≤ B := by
    have : 0 ≤ ∑ j ∈ Finset.range (m + 1), |Bθ j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  obtain ⟨M, hM⟩ := exists_bound_iteratedFDeriv_comp_periodic Ψ T r a hT hr hΨs hΨp m B
  set S' : ℝ := |s₃| + 1 + |sθ' 0| + ∑ j ∈ Finset.range (m + 1), (|sθ' j| + |sv' j|) with hS'
  have hsum : ∀ j ≤ m, sθ' j ≤ S' ∧ sv' j ≤ S' := by
    intro j hj
    have hle : |sθ' j| + |sv' j| ≤ ∑ j ∈ Finset.range (m + 1), (|sθ' j| + |sv' j|) :=
      Finset.single_le_sum (f := fun j => |sθ' j| + |sv' j|) (fun _ _ => by positivity)
        (Finset.mem_range.2 (by omega))
    have := le_abs_self (sθ' j); have := le_abs_self (sv' j)
    have := abs_nonneg (sθ' j); have := abs_nonneg (sv' j); have := abs_nonneg (sθ' 0)
    have := abs_nonneg s₃
    constructor <;> linarith
  have hsθ0 : sθ' 0 ≤ S' := (hsum 0 (Nat.zero_le _)).1
  refine ⟨M, S' + 1, fun s hs t => ?_⟩
  set p : ℝ × ℝ := (s, t) with hp
  set ρ : ℝ := min 1 (r / (2 * B)) with hρ
  have hρ0 : 0 < ρ := lt_min one_pos (div_pos hr (by positivity))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  -- the ball lies in the half-plane where all bounds hold
  have hball : ∀ q ∈ ball p ρ, S' < q.1 := by
    intro q hq
    have h1 : |q.1 - s| < ρ := by
      have := (mem_ball.1 hq)
      exact lt_of_le_of_lt (by simpa [hp, Prod.dist_eq, Real.dist_eq] using
        (le_max_left (dist q.1 p.1) (dist q.2 p.2))) this
    have := (abs_lt.1 h1).1
    linarith
  have hS's₃ : s₃ + 1 ≤ S' := by
    have : 0 ≤ ∑ j ∈ Finset.range (m + 1), (|sθ' j| + |sv' j|) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have := abs_nonneg (sθ' 0)
    have := le_abs_self s₃
    linarith
  have hballU : ball p ρ ⊆ Set.Ioi s₃ ×ˢ Set.univ := fun q hq =>
    ⟨show s₃ < q.1 by linarith [hball q hq], trivial⟩
  have hsr3 : sr ≤ s₃ := by simp [hs₃]
  set V : ℝ × ℝ → ℝ × E := fun q => (θ q - θ p, v q) with hVdef
  have hVs : ContDiffOn ℝ ∞ V (ball p ρ) :=
    ((hθU.mono hballU).sub contDiffOn_const).prodMk (hvU.mono hballU)
  -- `θ` moves by at most `r / 2` on the ball
  have hθmv : ∀ q ∈ ball p ρ, ‖θ q - θ p‖ ≤ r / 2 := by
    intro q hq
    have hdiff : ∀ x ∈ ball p ρ, DifferentiableAt ℝ θ x := fun x hx =>
      ((hθU.contDiffAt (hU.mem_nhds (hballU hx))).differentiableAt (by simp))
    have hbd : ∀ x ∈ ball p ρ, ‖fderiv ℝ θ x‖ ≤ B := by
      intro x hx
      rw [← norm_iteratedFDeriv_one]
      obtain ⟨x1, x2⟩ := x
      exact (hBθ 0 x1 (by linarith [hball _ hx]) x2).trans hBθ0
    have := (convex_ball p ρ).norm_image_sub_le_of_norm_fderiv_le hdiff hbd (mem_ball_self hρ0) hq
    calc ‖θ q - θ p‖ ≤ B * ‖q - p‖ := this
      _ ≤ B * (r / (2 * B)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          exact (le_of_lt (show ‖q - p‖ < ρ by simpa [dist_eq_norm] using mem_ball.1 hq)).trans
            (min_le_right _ _)
      _ = r / 2 := by field_simp
  have hVsmall : ∀ q ∈ ball p ρ, ‖V q‖ ≤ r / 2 := by
    intro q hq
    rw [hVdef, Prod.norm_def]
    refine max_le (hθmv q hq) ?_
    obtain ⟨q1, q2⟩ := q
    exact hvs q1 (by linarith [hball _ hq]) q2
  have hpU : p ∈ Set.Ioi s₃ ×ˢ (Set.univ : Set ℝ) := ⟨show s₃ < s by linarith, trivial⟩
  have hθat : ContDiffAt ℝ ∞ θ p := hθU.contDiffAt (hU.mem_nhds hpU)
  have hvat : ContDiffAt ℝ ∞ v p := hvU.contDiffAt (hU.mem_nhds hpU)
  have hVbd : ∀ i ≤ m, ‖iteratedFDeriv ℝ i V p‖ ≤ B := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · rw [norm_iteratedFDeriv_zero]
      exact (hVsmall p (mem_ball_self hρ0)).trans hBr
    · rw [hVdef, cd_norm_iteratedFDeriv_pair hθat hvat hi1]
      refine max_le ?_ ?_
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        exact (hBθ j s (by linarith [(hsum j (by omega)).1]) t).trans (hBθle j (by omega))
      · exact (hsv' i s (by linarith [(hsum i hi).2]) t).trans hB1
  have key := hM (θ p) V (ball p ρ) p isOpen_ball (mem_ball_self hρ0) hVs hVsmall hVbd
  have hfun : (fun q : ℝ × ℝ => Ψ (a * q.2 + θ p, V q)) =
      fun q : ℝ × ℝ => Φ (a * q.2 + θ q, v q) := by
    funext q
    simp only [hΨ, hVdef]
    rw [show a * q.2 + θ p + (θ q - θ p) = a * q.2 + θ q by ring]
  rw [hfun] at key
  exact key

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped ContDiff

theorem solution {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝ × E → F) (T r a : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ ∞ Φ (Set.univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (v : E), ‖v‖ < r → Φ (φ + T, v) = Φ (φ, v))
    (h0 : ∀ φ : ℝ, Φ (φ, 0) = 0) (θ : ℝ × ℝ → ℝ)
    (hθs : ∃ s₂ : ℝ, ContDiffOn ℝ ∞ θ (Set.Ioi s₂ ×ˢ Set.univ))
    (hθ : ∀ m : ℕ, 1 ≤ m → ∃ B s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ, ‖iteratedFDeriv ℝ m θ (s, t)‖ ≤ B)
    (v : ℝ × ℝ → E) (hv : TendstoZeroCInfty v) :
    TendstoZeroCInfty (fun p : ℝ × ℝ => Φ (a * p.2 + θ p, v p)) :=
  tendstoZeroCInfty_comp_periodic_of_drift_aux Φ T r a hT hr hΦ hper h0 θ hθs hθ v hv
