-- Prove2me | solution 1 for FiniteEnergyPlane.bounded_iteratedFDeriv_of_comp_immersion
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T17:44:32.124655+00:00
-- url     : https://prove2.me/submissions/77321112-df15-4429-bcf9-9281ef02375f

import Mathlib



/-!
# A3 child B: derivative bounds through a uniform immersion

If `Ξ` has bounded derivatives of order `≥ 1` on an open set `Ω` and `‖DΞ h‖ ≥ c ‖h‖` there,
then bounds of the derivatives of order `≥ 1` of `Ξ ∘ X` on the end of `ℝ × ℝ` give bounds of the
derivatives of order `≥ 1` of `X`.
-/

namespace FiniteEnergyPlane

open Metric Set Filter Topology
open scoped ContDiff Nat

namespace DGA3B

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- `‖A‖ ≤ ‖G ∘ A‖ / c` when `G` is bounded below by `c`. -/
lemma norm_le_of_lower {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {G : E →L[ℝ] F} {c : ℝ} (hc : 0 < c) (hG : ∀ h, c * ‖h‖ ≤ ‖G h‖) (A : D →L[ℝ] E) :
    ‖A‖ ≤ ‖G.comp A‖ / c := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  have h1 := hG (A h)
  have h2 := (G.comp A).le_opNorm h
  simp only [ContinuousLinearMap.comp_apply] at h2
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  linarith

/-- The same for multilinear maps with values in `D →L E`. -/
lemma cmm_norm_le_of_lower {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] {k : ℕ}
    {G : E →L[ℝ] F} {c : ℝ} (hc : 0 < c) (hG : ∀ h, c * ‖h‖ ≤ ‖G h‖)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => D) (D →L[ℝ] E)) :
    ‖T‖ ≤ ‖(ContinuousLinearMap.compL ℝ D E F G).compContinuousMultilinearMap T‖ / c := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  have h1 := norm_le_of_lower hc hG (T v)
  have h2 := ((ContinuousLinearMap.compL ℝ D E F G).compContinuousMultilinearMap T).le_opNorm v
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.compL_apply] at h2
  calc ‖T v‖ ≤ ‖G.comp (T v)‖ / c := h1
    _ ≤ _ := by
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right h2 hc.le

/-- Leibniz bound for a pointwise composition of linear maps. -/
lemma norm_iteratedFDerivWithin_clm_comp_le {D D' : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup D'] [NormedSpace ℝ D']
    {f : D' → E →L[ℝ] F} {g : D' → D →L[ℝ] E} {s : Set D'} {x : D'}
    (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s)
    (n : ℕ) :
    ‖iteratedFDerivWithin ℝ n (fun y => (f y).comp (g y)) s x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f s x‖ *
        ‖iteratedFDerivWithin ℝ (n - i) g s x‖ := by
  have h := (ContinuousLinearMap.compL ℝ D E F).norm_iteratedFDerivWithin_le_of_bilinear
    hf hg hs hx (n := n) (by exact_mod_cast le_top)
  refine h.trans ?_
  refine (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_compL_le ℝ D E F)
    (Finset.sum_nonneg fun i _ => by positivity)).trans ?_
  rw [one_mul]

theorem bounded_iteratedFDeriv_of_comp_immersion_aux
    (Ξ : E → F) (Ω : Set E) (hΩ : IsOpen Ω) (hΞ : ContDiffOn ℝ ∞ Ξ Ω)
    (X : ℝ × ℝ → E) (s₀ : ℝ) (hX : ContDiffOn ℝ ∞ X (Ioi s₀ ×ˢ univ))
    (hXΩ : ∀ s > s₀, ∀ t : ℝ, X (s, t) ∈ Ω)
    (hΞb : ∀ m : ℕ, 1 ≤ m → ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m Ξ (X (s, t))‖ ≤ C)
    (c : ℝ) (hc : 0 < c)
    (hlow : ∀ s > s₀, ∀ t : ℝ, ∀ h : E, c * ‖h‖ ≤ ‖fderiv ℝ Ξ (X (s, t)) h‖)
    (hY : ∀ m : ℕ, 1 ≤ m → ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p => Ξ (X p)) (s, t)‖ ≤ C) :
    ∀ m : ℕ, 1 ≤ m → ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖iteratedFDeriv ℝ m X (s, t)‖ ≤ C := by
  set U : Set (ℝ × ℝ) := Ioi s₀ ×ˢ univ with hUdef
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hXU : MapsTo X U Ω := fun p hp => hXΩ p.1 hp.1 p.2
  have hZ : ContDiffOn ℝ ∞ (fderiv ℝ X) U := hX.fderiv_of_isOpen hU (by simp)
  have hDΞ : ContDiffOn ℝ ∞ (fderiv ℝ Ξ) Ω := hΞ.fderiv_of_isOpen hΩ (by simp)
  have hGd : ContDiffOn ℝ ∞ (fun p => fderiv ℝ Ξ (X p)) U := hDΞ.comp hX hXU
  have hDΞb : ∀ j : ℕ, ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j (fderiv ℝ Ξ) (X (s, t))‖ ≤ C := fun j => by
    obtain ⟨C, s₁, hC⟩ := hΞb (j + 1) (by omega)
    exact ⟨C, s₁, fun s hs t => by rw [norm_iteratedFDeriv_fderiv]; exact hC s hs t⟩
  choose CΞ' sΞ' hCΞ' using hDΞb
  suffices H : ∀ k : ℕ, ∃ C S : ℝ, s₀ < S ∧ ∀ i, 1 ≤ i → i ≤ k → ∀ s ≥ S, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ i X (s, t)‖ ≤ C by
    intro m hm
    obtain ⟨C, S, -, h⟩ := H m
    exact ⟨C, S, fun s hs t => h m hm le_rfl s hs t⟩
  intro k
  induction k with
  | zero => exact ⟨0, s₀ + 1, by linarith, fun i hi hik => by omega⟩
  | succ k ih =>
    obtain ⟨Ck, Sk, hSk, hk⟩ := ih
    set Dk : ℝ := max 1 Ck with hDk
    have hDk1 : 1 ≤ Dk := le_max_left _ _
    set CΞ : ℝ := ∑ j ∈ Finset.range (k + 1), |CΞ' j| with hCΞdef
    have hCΞ0 : 0 ≤ CΞ := Finset.sum_nonneg fun _ _ => abs_nonneg _
    set SΞ : ℝ := ∑ j ∈ Finset.range (k + 1), |sΞ' j| with hSΞdef
    have hCΞ : ∀ j ≤ k, ∀ s ≥ SΞ, ∀ t : ℝ,
        ‖iteratedFDeriv ℝ j (fderiv ℝ Ξ) (X (s, t))‖ ≤ CΞ := fun j hj s hs t =>
      (hCΞ' j s ((le_abs_self _).trans ((Finset.single_le_sum
        (f := fun j => |sΞ' j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hj))).trans hs)) t).trans
        ((le_abs_self _).trans (Finset.single_le_sum
        (f := fun j => |CΞ' j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hj))))
    set CG : ℝ := (k ! : ℝ) * CΞ * Dk ^ k with hCG
    have hCG0 : 0 ≤ CG := by positivity
    obtain ⟨CY, sY, hYb⟩ := hY (k + 1) (by omega)
    set R : ℝ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * CG * Dk with hR
    refine ⟨max Ck ((CY + R) / c), max (max Sk sY) SΞ,
      lt_of_lt_of_le hSk ((le_max_left _ _).trans (le_max_left _ _)),
      fun i hi hik s hs t => ?_⟩
    have hsk : Sk ≤ s := le_of_max_le_left (le_of_max_le_left hs)
    have hsY : sY ≤ s := le_of_max_le_right (le_of_max_le_left hs)
    have hsΞ : SΞ ≤ s := le_of_max_le_right hs
    rcases Nat.lt_or_ge i (k + 1) with hlt | hge
    · exact (hk i hi (by omega) s hsk t).trans (le_max_left _ _)
    have hi' : i = k + 1 := by omega
    subst hi'
    refine le_trans ?_ (le_max_right _ _)
    set p₀ : ℝ × ℝ := (s, t) with hp₀def
    have hp₀ : p₀ ∈ U := ⟨show s₀ < s by linarith, mem_univ _⟩
    have hXp₀ : X p₀ ∈ Ω := hXU hp₀
    -- bounds of the derivatives of `X` and of `DΞ ∘ X` at `p₀`
    have hXb : ∀ j, 1 ≤ j → j ≤ k → ‖iteratedFDeriv ℝ j X p₀‖ ≤ Dk := fun j hj1 hjk =>
      (hk j hj1 hjk s hsk t).trans (le_max_right _ _)
    have hGdb : ∀ i, 1 ≤ i → i ≤ k →
        ‖iteratedFDeriv ℝ i (fun p => fderiv ℝ Ξ (X p)) p₀‖ ≤ CG := by
      intro i hi1 hik
      have h := norm_iteratedFDerivWithin_comp_le (n := i) hDΞ hX (by exact_mod_cast le_top)
        hΩ.uniqueDiffOn hU.uniqueDiffOn hXU hp₀ (C := CΞ) (D := Dk)
        (fun j hj => by
          rw [iteratedFDerivWithin_of_isOpen j hΩ hXp₀]
          exact hCΞ j (by omega) s hsΞ t)
        (fun j hj1 hji => by
          rw [iteratedFDerivWithin_of_isOpen j hU hp₀]
          exact (hXb j hj1 (by omega)).trans (le_self_pow₀ hDk1 (by omega)))
      rw [iteratedFDerivWithin_of_isOpen i hU hp₀] at h
      refine h.trans ?_
      exact mul_le_mul (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.factorial_le hik)) hCΞ0)
        (pow_le_pow_right₀ hDk1 hik) (by positivity) (by positivity)
    -- the decomposition of `D(Ξ ∘ X)` near `p₀`
    set G₀ : E →L[ℝ] F := fderiv ℝ Ξ (X p₀) with hG₀
    set L := ContinuousLinearMap.compL ℝ (ℝ × ℝ) E F G₀ with hL
    have hW : fderiv ℝ (fun p => Ξ (X p)) =ᶠ[𝓝 p₀]
        (fun p => G₀.comp (fderiv ℝ X p)) +
          fun p => (fderiv ℝ Ξ (X p) - G₀).comp (fderiv ℝ X p) := by
      filter_upwards [hU.mem_nhds hp₀] with p hp
      have hdΞ : DifferentiableAt ℝ Ξ (X p) :=
        (hΞ.contDiffAt (hΩ.mem_nhds (hXU hp))).differentiableAt (by simp)
      have hdX : DifferentiableAt ℝ X p := (hX.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
      rw [fderiv_comp' p hdΞ hdX]
      simp [ContinuousLinearMap.sub_comp]
    have hZa : ContDiffAt ℝ ∞ (fderiv ℝ X) p₀ := hZ.contDiffAt (hU.mem_nhds hp₀)
    have hGa : ContDiffAt ℝ ∞ (fun p => fderiv ℝ Ξ (X p)) p₀ := hGd.contDiffAt (hU.mem_nhds hp₀)
    have htop_cd : ContDiffAt ℝ ∞ (fun p => G₀.comp (fderiv ℝ X p)) p₀ :=
      contDiffAt_const.clm_comp hZa
    have hrest_cd : ContDiffAt ℝ ∞ (fun p => (fderiv ℝ Ξ (X p) - G₀).comp (fderiv ℝ X p)) p₀ :=
      (hGa.sub contDiffAt_const).clm_comp hZa
    have hsplit := (hW.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds
    rw [iteratedFDeriv_add_apply (htop_cd.of_le (by exact_mod_cast le_top))
      (hrest_cd.of_le (by exact_mod_cast le_top))] at hsplit
    -- the top term
    have htop : iteratedFDeriv ℝ k (fun p => G₀.comp (fderiv ℝ X p)) p₀ =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fderiv ℝ X) p₀) :=
      L.iteratedFDeriv_comp_left (hZa.of_le (by exact_mod_cast le_top)) le_rfl
    -- the remainder
    have hrest : ‖iteratedFDeriv ℝ k
        (fun p => (fderiv ℝ Ξ (X p) - G₀).comp (fderiv ℝ X p)) p₀‖ ≤ R := by
      have h := norm_iteratedFDerivWithin_clm_comp_le
        (f := fun p => fderiv ℝ Ξ (X p) - G₀) (g := fderiv ℝ X)
        (hGd.sub contDiffOn_const) hZ hU.uniqueDiffOn hp₀ k
      rw [iteratedFDerivWithin_of_isOpen k hU hp₀] at h
      refine h.trans (Finset.sum_le_sum fun i hi => ?_)
      have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [iteratedFDerivWithin_of_isOpen i hU hp₀, iteratedFDerivWithin_of_isOpen (k - i) hU hp₀]
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simp only [norm_iteratedFDeriv_zero, hG₀, sub_self, norm_zero, mul_zero, zero_mul]
        positivity
      · have e : iteratedFDeriv ℝ i (fun p => fderiv ℝ Ξ (X p) - G₀) p₀ =
            iteratedFDeriv ℝ i (fun p => fderiv ℝ Ξ (X p)) p₀ := by
          rw [show (fun p => fderiv ℝ Ξ (X p) - G₀) =
              (fun p => fderiv ℝ Ξ (X p)) - fun _ => G₀ from rfl,
            iteratedFDeriv_sub_apply (hGa.of_le (by exact_mod_cast le_top)) contDiffAt_const,
            iteratedFDeriv_const_of_ne hi0.ne', Pi.zero_apply, sub_zero]
        rw [e]
        have hZb : ‖iteratedFDeriv ℝ (k - i) (fderiv ℝ X) p₀‖ ≤ Dk := by
          rw [norm_iteratedFDeriv_fderiv]
          exact hXb (k - i + 1) (by omega) (by omega)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hGdb i hi0 hik) (Nat.cast_nonneg _)) hZb
          (norm_nonneg _) (by positivity)
    -- the bound
    have hWb : ‖iteratedFDeriv ℝ k (fderiv ℝ (fun p => Ξ (X p))) p₀‖ ≤ CY := by
      rw [norm_iteratedFDeriv_fderiv]; exact hYb s hsY t
    have hlowG : ∀ h : E, c * ‖h‖ ≤ ‖G₀ h‖ := hlow s (by linarith) t
    have hT := cmm_norm_le_of_lower (D := ℝ × ℝ) (k := k) hc hlowG
      (iteratedFDeriv ℝ k (fderiv ℝ X) p₀)
    rw [← hL, ← htop] at hT
    have htopb : ‖iteratedFDeriv ℝ k (fun p => G₀.comp (fderiv ℝ X p)) p₀‖ ≤ CY + R := by
      have e : iteratedFDeriv ℝ k (fun p => G₀.comp (fderiv ℝ X p)) p₀ =
          iteratedFDeriv ℝ k (fderiv ℝ (fun p => Ξ (X p))) p₀ -
            iteratedFDeriv ℝ k (fun p => (fderiv ℝ Ξ (X p) - G₀).comp (fderiv ℝ X p)) p₀ := by
        rw [hsplit]; abel
      rw [e]
      exact (norm_sub_le _ _).trans (add_le_add hWb hrest)
    rw [← norm_iteratedFDeriv_fderiv]
    exact hT.trans (div_le_div_of_nonneg_right htopb hc.le)

end DGA3B

end FiniteEnergyPlane

open FiniteEnergyPlane

open Set
open scoped ContDiff

theorem solution {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ξ : E → F) (Ω : Set E) (hΩ : IsOpen Ω) (hΞ : ContDiffOn ℝ ∞ Ξ Ω)
    (X : ℝ × ℝ → E) (s₀ : ℝ) (hX : ContDiffOn ℝ ∞ X (Ioi s₀ ×ˢ univ))
    (hXΩ : ∀ s > s₀, ∀ t : ℝ, X (s, t) ∈ Ω)
    (hΞb : ∀ m : ℕ, 1 ≤ m → ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m Ξ (X (s, t))‖ ≤ C)
    (c : ℝ) (hc : 0 < c)
    (hlow : ∀ s > s₀, ∀ t : ℝ, ∀ h : E, c * ‖h‖ ≤ ‖fderiv ℝ Ξ (X (s, t)) h‖)
    (hY : ∀ m : ℕ, 1 ≤ m → ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p => Ξ (X p)) (s, t)‖ ≤ C) :
    ∀ m : ℕ, 1 ≤ m → ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖iteratedFDeriv ℝ m X (s, t)‖ ≤ C :=
  FiniteEnergyPlane.DGA3B.bounded_iteratedFDeriv_of_comp_immersion_aux Ξ Ω hΩ hΞ X s₀ hX hXΩ hΞb c hc hlow hY
