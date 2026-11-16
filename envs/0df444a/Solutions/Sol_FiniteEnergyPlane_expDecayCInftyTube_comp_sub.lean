-- Prove2me | solution 1 for FiniteEnergyPlane.expDecayCInftyTube_comp_sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-15T17:37:42.638219+00:00
-- url     : https://prove2.me/submissions/76ff4d3e-3ca9-46c5-8d3b-73de4b1b762e

import Definitions.Def_FiniteEnergyPlane_Tube
import Theorems.Thm_FiniteEnergyPlane_hadamard_integral_fderiv
import Theorems.Thm_FiniteEnergyPlane_exists_bound_iteratedFDeriv_of_periodic



/-!
# Tube composition, layer A (local): a global smooth extension of a map smooth on an open set,
agreeing with it near a compact subset.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff Manifold

noncomputable section

namespace SMC

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A map smooth on an open set agrees, on a closed thickening of a compact subset, with a
globally smooth map. -/
lemma exists_contDiff_eqOn_cthickening (G : E → F) {U : Set E} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {C : Set E} (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ δ > 0, ∃ G' : E → F, ContDiff ℝ ∞ G' ∧ cthickening δ C ⊆ U ∧
      ∀ y ∈ cthickening δ C, G' y = G y := by
  obtain ⟨δ₂, hδ₂, hsub⟩ := hC.exists_cthickening_subset_open hU hCU
  set δ := δ₂ / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδsub : cthickening δ C ⊆ cthickening δ₂ C := cthickening_mono (by linarith) C
  have hdisj : Disjoint Uᶜ (cthickening δ C) := by
    rw [disjoint_compl_left_iff_subset]
    exact hδsub.trans hsub
  obtain ⟨χ, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
    (n := ⊤) hU.isClosed_compl isClosed_cthickening hdisj
  have hχ : ContDiff ℝ ∞ (χ : E → ℝ) := contMDiff_iff_contDiff.1 χ.contMDiff
  refine ⟨δ, hδ0, fun y => χ y • G y, ?_, hδsub.trans hsub, fun y hy => ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun y => ?_
    by_cases hy : y ∈ U
    · exact hχ.contDiffAt.smul (hG.contDiffAt (hU.mem_nhds hy))
    · have hev : ∀ᶠ z in 𝓝 y, (χ : E → ℝ) z = 0 :=
        (hχ0.filter_mono (nhds_le_nhdsSet (show y ∈ Uᶜ from hy)))
      have : (fun z => χ z • G z) =ᶠ[𝓝 y] fun _ => (0 : F) := by
        filter_upwards [hev] with z hz
        rw [hz, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq this
  · have h1 : (χ : E → ℝ) y = 1 := hχ1.self_of_nhdsSet y hy
    simp [h1]

end SMC

end

end FiniteEnergyPlane

/-!
# Tube composition, layer B: exponential `C^∞` decay is preserved by composition with a map
smooth near the limit.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff Nat

noncomputable section

theorem expDecayCInftyTube_comp_sub_aux {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (G : E → F) (U : Set E) (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (g : ℝ × ℂ → E) (hg : ContDiffOn ℝ ∞ g (Set.univ ×ˢ ball (0 : ℂ) (2 * ρ)))
    (hgper : ∀ (t : ℝ) (w : ℂ), g (t + 1, w) = g (t, w))
    (hgU : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ → g (t, w) ∈ U)
    (f : ℝ × ℝ × ℂ → E)
    (hf : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ => f q - g (q.2.1, q.2.2)) ρ b) :
    ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ => G (f q) - G (g (q.2.1, q.2.2))) ρ b := by
  -- the compact image of the limit
  set K := g '' (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) ρ) with hKdef
  have hball : closedBall (0 : ℂ) ρ ⊆ ball (0 : ℂ) (2 * ρ) :=
    closedBall_subset_ball (by linarith)
  have hK : IsCompact K :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).image_of_continuousOn
      (hg.continuousOn.mono (prod_mono (subset_univ _) hball))
  have hgK : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ → g (t, w) ∈ K := by
    intro t w hw
    have hper : Function.Periodic (fun t : ℝ => g (t, w)) 1 := fun t => hgper t w
    obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ one_pos t
    exact ⟨(y, w), ⟨⟨hy.1, hy.2.le⟩, hw⟩, hty.symm⟩
  have hKU : K ⊆ U := by
    rintro _ ⟨⟨t, w⟩, ⟨-, hw⟩, rfl⟩
    exact hgU t w hw
  obtain ⟨δ, hδ, G', hG', hthU, hG'eq⟩ := SMC.exists_contDiff_eqOn_cthickening G hU hG hK hKU
  -- Hadamard factorisation of `G'`
  obtain ⟨hΨ, hΨeq⟩ := hadamard_integral_fderiv (fun p : E × E => G' (p.1 + p.2))
    (hG'.comp (contDiff_fst.add contDiff_snd))
  set Ψ := fun p : E × E => ∫ θ in (0 : ℝ)..1, fderiv ℝ (fun a => G' (p.1 + a)) (θ • p.2)
    with hΨdef
  -- the decaying difference
  obtain ⟨⟨s₀, hvs⟩, hvl⟩ := hf
  set v : ℝ × ℝ × ℂ → E := fun q => f q - g (q.2.1, q.2.2) with hvdef
  obtain ⟨C₀, s₀', h₀⟩ := hvl 0
  have htend : Tendsto (fun s : ℝ => |C₀| * Real.exp (-(b * s))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => Real.exp (-(b * s))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hb)
    simpa using h1.const_mul |C₀|
  obtain ⟨s₂, hs₂⟩ := eventually_atTop.1 (htend.eventually (ge_mem_nhds hδ))
  set S := max (max s₀ s₀') (max s₂ 0) with hS
  set Ω : Set (ℝ × ℝ × ℂ) := Ioi S ×ˢ univ ×ˢ ball (0 : ℂ) ρ with hΩ
  have hΩo : IsOpen Ω := isOpen_Ioi.prod (isOpen_univ.prod isOpen_ball)
  have hΩsub : Ω ⊆ Ioi s₀ ×ˢ univ ×ˢ ball (0 : ℂ) ρ := by
    rintro ⟨s, t, w⟩ ⟨hs, ht, hw⟩
    have h1 : s₀ ≤ S := le_trans (le_max_left _ _) (le_max_left _ _)
    exact ⟨show s₀ < s from lt_of_le_of_lt h1 hs, ht, hw⟩
  have hvsmall : ∀ q ∈ Ω, ‖v q‖ ≤ δ := by
    rintro ⟨s, t, w⟩ ⟨hs, -, hw⟩
    have hs' : S < s := hs
    have h1 := h₀ s (by
      have : s₀' ≤ S := le_trans (le_max_right _ _) (le_max_left _ _)
      linarith) t w hw
    rw [norm_iteratedFDeriv_zero] at h1
    have h2 := hs₂ s (by
      have : s₂ ≤ S := le_trans (le_max_left _ _) (le_max_right _ _)
      linarith)
    have h3 : C₀ * Real.exp (-(b * s)) ≤ |C₀| * Real.exp (-(b * s)) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
    linarith
  have hwmem : ∀ q ∈ Ω, q.2.2 ∈ closedBall (0 : ℂ) ρ := fun q hq =>
    ball_subset_closedBall hq.2.2
  -- the factorised form
  set R : ℝ × ℝ × ℂ → F := fun q => Ψ (g (q.2.1, q.2.2), v q) (v q) with hRdef
  have hEq : EqOn (fun q : ℝ × ℝ × ℂ => G (f q) - G (g (q.2.1, q.2.2))) R Ω := by
    intro q hq
    have hgq := hgK q.2.1 q.2.2 (hwmem q hq)
    have hfq : f q = g (q.2.1, q.2.2) + v q := by simp [hvdef]
    have hfK : f q ∈ cthickening δ K := by
      refine mem_cthickening_of_dist_le _ (g (q.2.1, q.2.2)) _ _ hgq ?_
      rw [dist_eq_norm, hfq, add_sub_cancel_left]
      exact hvsmall q hq
    have h1 := hΨeq (g (q.2.1, q.2.2), v q)
    simp only [add_zero] at h1
    show G (f q) - G (g (q.2.1, q.2.2)) = Ψ (g (q.2.1, q.2.2), v q) (v q)
    rw [← hG'eq _ hfK, ← hG'eq _ (self_subset_cthickening K hgq), hfq, h1]
    simp [hΨdef]
  -- smoothness
  have hv : ContDiffOn ℝ ∞ v Ω := hvs.mono hΩsub
  have hgp : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ × ℂ => g (q.2.1, q.2.2)) Ω := by
    refine hg.comp contDiff_snd.contDiffOn ?_
    rintro q ⟨-, -, hw⟩
    exact ⟨trivial, ball_subset_ball (by linarith) hw⟩
  have hh : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ × ℂ => (g (q.2.1, q.2.2), v q)) Ω := hgp.prodMk hv
  have hA : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ × ℂ => Ψ (g (q.2.1, q.2.2), v q)) Ω :=
    hΨ.comp_contDiffOn hh
  have hR : ContDiffOn ℝ ∞ R Ω := hA.clm_apply hv
  refine ⟨⟨S, (hR.congr hEq)⟩, fun m => ?_⟩
  -- constants
  set B : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F := ContinuousLinearMap.id ℝ (E →L[ℝ] F) with hBdef
  choose Cv sv hCv using hvl
  choose Cg hCg using fun j => exists_bound_iteratedFDeriv_of_periodic g 1 (2 * ρ) one_pos
    (by positivity) hg (fun τ w _ => hgper τ w) j
  have hKδ : IsCompact (K ×ˢ closedBall (0 : E) δ) := hK.prod (isCompact_closedBall _ _)
  choose CΨ hCΨ using fun j : ℕ => hKδ.exists_bound_of_continuousOn
    ((ContDiff.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top) hΨ).continuousOn)
  set CΨs := ∑ j ∈ Finset.range (m + 1), |CΨ j| with hCΨs
  set D := max 1 (∑ j ∈ Finset.range (m + 1), (|Cg j| + |Cv j|)) with hD
  set Cv' := ∑ j ∈ Finset.range (m + 1), |Cv j| with hCv'
  set CA := (m ! : ℝ) * CΨs * D ^ m with hCA
  have hD1 : 1 ≤ D := le_max_left _ _
  set s₁ := max (S + 1) (∑ j ∈ Finset.range (m + 1), |sv j|) with hs₁
  refine ⟨‖B‖ * (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) * CA * Cv', s₁,
    fun s hs t w hw => ?_⟩
  have hsS : S < s := by linarith [le_max_left (S + 1) (∑ j ∈ Finset.range (m + 1), |sv j|)]
  have hs0 : 0 ≤ s := by
    have : (0 : ℝ) ≤ S := le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  have hq : ((s, t, w) : ℝ × ℝ × ℂ) ∈ Ω := ⟨hsS, trivial, hw⟩
  have hsv : ∀ j ≤ m, sv j ≤ s := fun j hj =>
    (le_abs_self _).trans ((Finset.single_le_sum (f := fun j => |sv j|)
      (fun j _ => abs_nonneg (sv j)) (Finset.mem_range.2 (by omega))).trans
      (le_trans (le_max_right _ _) hs))
  have hexp1 : Real.exp (-(b * s)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  -- bounds on `v`
  have hvb : ∀ j ≤ m, ‖iteratedFDeriv ℝ j v (s, t, w)‖ ≤ Cv' * Real.exp (-(b * s)) := by
    intro j hj
    refine (hCv j s (hsv j hj) t w hw).trans ?_
    refine mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) (Real.exp_pos _).le
    exact Finset.single_le_sum (f := fun j => |Cv j|) (fun j _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega))
  have hvb1 : ∀ j ≤ m, ‖iteratedFDeriv ℝ j v (s, t, w)‖ ≤ |Cv j| := by
    intro j hj
    refine (hCv j s (hsv j hj) t w hw).trans ?_
    calc Cv j * Real.exp (-(b * s)) ≤ |Cv j| * Real.exp (-(b * s)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
      _ ≤ |Cv j| * 1 := mul_le_mul_of_nonneg_left hexp1 (abs_nonneg _)
      _ = |Cv j| := mul_one _
  -- bounds on `g ∘ snd`
  have hsnd : ‖(ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ))‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simpa using norm_snd_le x
  set W : Set (ℝ × ℂ) := univ ×ˢ ball (0 : ℂ) (2 * ρ) with hW
  have hWo : IsOpen W := isOpen_univ.prod isOpen_ball
  have hWpre : IsOpen ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)) ⁻¹' W) :=
    hWo.preimage (ContinuousLinearMap.continuous _)
  have hqW : (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)) (s, t, w) ∈ W :=
    ⟨trivial, ball_subset_ball (by linarith) hw⟩
  have hgb : ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun q : ℝ × ℝ × ℂ => g (q.2.1, q.2.2)) (s, t, w)‖ ≤
      |Cg j| := by
    intro j hj
    have e := ContinuousLinearMap.iteratedFDerivWithin_comp_right
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)) hg hWo.uniqueDiffOn hWpre.uniqueDiffOn hqW
      (i := j) (by exact_mod_cast le_top)
    rw [iteratedFDerivWithin_of_isOpen j hWpre hqW,
      iteratedFDerivWithin_of_isOpen j hWo hqW] at e
    have e' : (fun q : ℝ × ℝ × ℂ => g (q.2.1, q.2.2)) =
        g ∘ (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)) := rfl
    rw [e', e]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hprod : ∏ _i : Fin j, ‖(ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ))‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => hsnd
    have hgj : ‖iteratedFDeriv ℝ j g (t, w)‖ ≤ |Cg j| :=
      (hCg j t w (by rw [mem_ball_zero_iff] at hw; linarith)).trans (le_abs_self _)
    calc ‖iteratedFDeriv ℝ j g ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)) (s, t, w))‖ *
          ∏ _i : Fin j, ‖(ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ))‖ ≤ |Cg j| * 1 :=
          mul_le_mul hgj hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _) (abs_nonneg _)
      _ = |Cg j| := mul_one _
  -- bounds on `A = Ψ ∘ h`
  have hAb : ∀ i ≤ m, ‖iteratedFDerivWithin ℝ i
      (fun q : ℝ × ℝ × ℂ => Ψ (g (q.2.1, q.2.2), v q)) Ω (s, t, w)‖ ≤ CA := by
    intro i hi
    have key := norm_iteratedFDerivWithin_comp_le (g := Ψ)
      (f := fun q : ℝ × ℝ × ℂ => (g (q.2.1, q.2.2), v q)) hΨ.contDiffOn hh (n := i)
      (by exact_mod_cast le_top) uniqueDiffOn_univ hΩo.uniqueDiffOn (mapsTo_univ _ _) hq
      (C := CΨs) (D := D)
      (by
        intro j hj
        rw [iteratedFDerivWithin_univ]
        have hmem : (g (t, w), v (s, t, w)) ∈ K ×ˢ closedBall (0 : E) δ :=
          ⟨hgK t w (ball_subset_closedBall hw), mem_closedBall_zero_iff.2 (hvsmall _ hq)⟩
        refine ((hCΨ j _ hmem).trans (le_abs_self _)).trans ?_
        exact Finset.single_le_sum (f := fun j => |CΨ j|) (fun j _ => abs_nonneg _)
          (Finset.mem_range.2 (by omega)))
      (by
        intro j hj1 hji
        rw [iteratedFDerivWithin_of_isOpen j hΩo hq]
        have hgat : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℂ => g (q.2.1, q.2.2)) (s, t, w) :=
          hgp.contDiffAt (hΩo.mem_nhds hq)
        have hvat : ContDiffAt ℝ ∞ v (s, t, w) := hv.contDiffAt (hΩo.mem_nhds hq)
        rw [iteratedFDeriv_prodMk hgat hvat (by exact_mod_cast le_top),
          ContinuousMultilinearMap.opNorm_prod]
        have hDj : D ≤ D ^ j := le_self_pow₀ hD1 (by omega)
        have hsum : |Cg j| + |Cv j| ≤ D := by
          refine le_trans ?_ (le_max_right _ _)
          exact Finset.single_le_sum (f := fun j => |Cg j| + |Cv j|)
            (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_range.2 (by omega))
        refine max_le ?_ ?_
        · exact (hgb j (by omega)).trans (by linarith [abs_nonneg (Cv j)])
        · exact (hvb1 j (by omega)).trans (by linarith [abs_nonneg (Cg j)]))
    refine key.trans ?_
    have hfac : (i ! : ℝ) ≤ m ! := by exact_mod_cast Nat.factorial_le hi
    have hpow : D ^ i ≤ D ^ m := pow_le_pow_right₀ hD1 hi
    have hCΨs0 : 0 ≤ CΨs := Finset.sum_nonneg fun j _ => abs_nonneg _
    calc (i ! : ℝ) * CΨs * D ^ i ≤ (m ! : ℝ) * CΨs * D ^ m := by gcongr
      _ = CA := rfl
  -- the bilinear bound
  have hRB : R = fun q => B (Ψ (g (q.2.1, q.2.2), v q)) (v q) := rfl
  rw [← iteratedFDerivWithin_of_isOpen m hΩo hq, iteratedFDerivWithin_congr hEq hq m, hRB]
  refine (B.norm_iteratedFDerivWithin_le_of_bilinear hA hv hΩo.uniqueDiffOn hq
    (n := m) (by exact_mod_cast le_top)).trans ?_
  have hterm : ∀ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      ‖iteratedFDerivWithin ℝ i (fun q : ℝ × ℝ × ℂ => Ψ (g (q.2.1, q.2.2), v q)) Ω (s, t, w)‖ *
      ‖iteratedFDerivWithin ℝ (m - i) v Ω (s, t, w)‖ ≤
        (m.choose i : ℝ) * (CA * (Cv' * Real.exp (-(b * s)))) := by
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [iteratedFDerivWithin_of_isOpen (m - i) hΩo hq]
    have hCA0 : 0 ≤ CA := (norm_nonneg _).trans (hAb 0 (Nat.zero_le _))
    calc (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i
          (fun q : ℝ × ℝ × ℂ => Ψ (g (q.2.1, q.2.2), v q)) Ω (s, t, w)‖ *
          ‖iteratedFDeriv ℝ (m - i) v (s, t, w)‖ ≤
          (m.choose i : ℝ) * CA * (Cv' * Real.exp (-(b * s))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hAb i hi') (Nat.cast_nonneg _))
            (hvb (m - i) (by omega)) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) hCA0)
      _ = (m.choose i : ℝ) * (CA * (Cv' * Real.exp (-(b * s)))) := by ring
  calc ‖B‖ * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i (fun q : ℝ × ℝ × ℂ => Ψ (g (q.2.1, q.2.2), v q)) Ω (s, t, w)‖ *
        ‖iteratedFDerivWithin ℝ (m - i) v Ω (s, t, w)‖ ≤
        ‖B‖ * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (CA * (Cv' * Real.exp (-(b * s)))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (norm_nonneg B)
    _ = ‖B‖ * (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) * CA * Cv' *
        Real.exp (-(b * s)) := by
        rw [← Finset.sum_mul]; ring

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (G : E → F) (U : Set E) (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (g : ℝ × ℂ → E) (hg : ContDiffOn ℝ ∞ g (Set.univ ×ˢ ball (0 : ℂ) (2 * ρ)))
    (hgper : ∀ (t : ℝ) (w : ℂ), g (t + 1, w) = g (t, w))
    (hgU : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ → g (t, w) ∈ U)
    (f : ℝ × ℝ × ℂ → E)
    (hf : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ => f q - g (q.2.1, q.2.2)) ρ b) :
    ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ => G (f q) - G (g (q.2.1, q.2.2))) ρ b :=
  expDecayCInftyTube_comp_sub_aux G U hU hG ρ b hρ hb g hg hgper hgU f hf
