-- Prove2me | solution 1 for FiniteEnergyPlane.tendsto_aCoord_atTop_of_small_area
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T19:52:37.721841+00:00
-- url     : https://prove2.me/submissions/26bbd873-175a-4fb0-9901-75010824969e

import Definitions.Def_FiniteEnergyPlane_Compactness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_proj_aCoord
import Theorems.Thm_FiniteEnergyPlane_proj_smul_aCoord_smul
import Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_mono
import Theorems.Thm_FiniteEnergyPlane_tendsto_loopAction_of_tendstoCInftyLocOn
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInftyLocOn_of_dlambdaEnergy_le
import Theorems.Thm_FiniteEnergyPlane_rescale_isFiniteEnergyCurve
import Theorems.Thm_FiniteEnergyPlane_punctured_disk_asymptotics
import Theorems.Thm_FiniteEnergyPlane_tendsto_loopAction_of_isRemovablePuncture
import Theorems.Thm_FiniteEnergyPlane_loopAction_cwLoop_eq_neg_ccwLoop



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem tendsto_aCoord_atTop_of_small_area_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (T γ e N : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ T → γ < Q.T) (he : 0 < e)
    (r : ℕ → ℝ) (hr0 : ∀ k, 0 < r k) (hr : Tendsto r atTop (𝓝 0)) (v : ℕ → ℂ → V n)
    (hv : ∀ k, IsFiniteEnergyCurve H J Set.univ (v k))
    (hE : ∀ k, energy H Set.univ (v k) ≤ ENNReal.ofReal T)
    (hdl : ∀ k, dlambdaEnergy H {z | r k < ‖z‖} (v k) ≤ ENNReal.ofReal γ)
    (hact : ∀ k, ∀ ρ : ℝ, r k < ρ → e ≤ loopAction H (v k) (ccwLoop ρ))
    (hN : ∀ k z, -N ≤ aCoord H (v k z)) :
    ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc →
      ∀ M : ℝ, ∀ᶠ k in atTop, ∀ z ∈ Kc, M ≤ aCoord H (v k z) := by
  intro Kc hKc h0 M
  have hunifK : ∀ (f : ℕ → ℂ → V n) (g : ℂ → V n) (O K : Set ℂ),
      JHolomorphic.TendstoCInftyLocOn f g O → K ⊆ O → IsCompact K →
      TendstoUniformlyOn f g atTop K := by
    intro f g O K h hKO hK
    have h0 := h K hKO hK 0
    have hev : UniformContinuous fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => ℂ) (V n) =>
        L Fin.elim0 :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => ℂ) (V n) Fin.elim0).uniformContinuous
    have := hev.comp_tendstoUniformlyOn h0
    simpa [Function.comp_def, iteratedFDeriv_zero_apply] using this
  have hPs : ContDiffOn ℝ ∞ (proj H) {0}ᶜ := (contDiffOn_proj_aCoord H hH).1
  have hacont : ∀ y : V n, y ≠ 0 → ContinuousAt (aCoord H) y := fun y hy =>
    (contDiffOn_proj_aCoord H hH).2.continuousOn.continuousAt
      (isOpen_compl_singleton.mem_nhds hy)
  have hloopC : ∀ ρ : ℝ, ContDiff ℝ ∞ (ccwLoop ρ) := by
    intro ρ
    unfold ccwLoop
    have hin : ContDiff ℝ ∞ (fun t : ℝ => ((2 * π * t : ℝ) : ℂ) * Complex.I) :=
      (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const
    exact contDiff_const.mul ((Complex.contDiff_exp (𝕜 := ℝ)).comp hin)
  have hloop0 : ∀ ρ : ℝ, 0 < ρ → ∀ t, ccwLoop ρ t ≠ 0 := by
    intro ρ hρ t
    unfold ccwLoop
    exact mul_ne_zero (by exact_mod_cast hρ.ne') (Complex.exp_ne_zero _)
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  -- extract a subsequence with bad points and radii `r < 1/(j+1)`
  have hfreq : ∀ j : ℕ, ∃ᶠ k in atTop,
      r k < 1 / ((j : ℝ) + 1) ∧ ∃ z ∈ Kc, aCoord H (v k z) < M := by
    intro j
    have hr' : ∀ᶠ k in atTop, r k < 1 / ((j : ℝ) + 1) :=
      hr.eventually (gt_mem_nhds (by positivity))
    refine (hcon.and_eventually hr').mono ?_
    rintro k ⟨h1, h2⟩
    push_neg at h1
    exact ⟨h2, h1⟩
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_forall_of_frequently hfreq
  choose z hzK hzM using fun j => (hφP j).2
  obtain ⟨zs, hzs, χ, hχ, hzlim⟩ := hKc.tendsto_subseq hzK
  have hzs0 : zs ≠ 0 := fun h => h0 (h ▸ hzs)
  set ψ : ℕ → ℕ := φ ∘ χ with hψdef
  have hrψ : ∀ j, r (ψ j) < 1 / ((j : ℝ) + 1) := by
    intro j
    refine ((hφP (χ j)).1).trans_le ?_
    have : (j : ℝ) ≤ χ j := by exact_mod_cast hχ.id_le j
    gcongr
  -- normalisation
  set c : ℕ → ℝ := fun j => aCoord H (v (ψ j) 1) with hcdef
  set w : ℕ → ℂ → V n := fun j z => Real.exp (-2 * c j) • v (ψ j) z with hwdef
  have hresc := fun j => rescale_isFiniteEnergyCurve H hH J hJ Set.univ isOpen_univ (v (ψ j))
    (hv (ψ j)) 0 1 one_pos (Real.exp (-2 * c j)) (Real.exp_pos _)
  simp only [zero_add, one_smul, Set.mem_univ, Set.setOf_true, Set.setOf_mem_eq,
    Set.subset_univ, true_implies, forall_const] at hresc
  have hlog : ∀ j, Real.log (Real.exp (-2 * c j)) / 2 = -c j := by
    intro j; rw [Real.log_exp]; ring
  have hwFE : ∀ j, IsFiniteEnergyCurve H J Set.univ (w j) := fun j => (hresc j).1
  have hwa : ∀ j z, aCoord H (w j z) = aCoord H (v (ψ j) z) - c j := by
    intro j z
    rw [(hresc j).2.1 z, hlog]; ring
  have hwproj : ∀ j z, proj H (w j z) = proj H (v (ψ j) z) := fun j z =>
    (proj_smul_aCoord_smul H hH _ ((hv (ψ j)).2.1 z trivial) _ (Real.exp_pos _)).1
  have hwact : ∀ j γ', loopAction H (w j) γ' = loopAction H (v (ψ j)) γ' := by
    intro j γ'
    have hl : loopInS H (w j) γ' = loopInS H (v (ψ j)) γ' := funext fun t => hwproj j _
    unfold loopAction
    rw [hl]
  have hwa1 : ∀ j, aCoord H (w j 1) = 0 := by intro j; rw [hwa]; simp [c]
  -- exhaustion
  set U : ℕ → Set ℂ := fun j => {z : ℂ | 1 / ((j : ℝ) + 1) < ‖z‖} with hUdef
  have hUo : ∀ j, IsOpen (U j) := fun j => isOpen_lt continuous_const continuous_norm
  have hUm : Monotone U := by
    intro i j hij z hz
    simp only [U, Set.mem_setOf_eq] at hz ⊢
    refine lt_of_le_of_lt ?_ hz
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    gcongr
  have hUu : ⋃ j, U j = {z : ℂ | z ≠ 0} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, U]
    constructor
    · rintro ⟨j, hj⟩ rfl
      simp at hj
      linarith [show (0 : ℝ) < 1 / ((j : ℝ) + 1) by positivity]
    · intro hz
      have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hpos
      exact ⟨j, hj⟩
  have hUsub : ∀ j, U j ⊆ {z | r (ψ j) < ‖z‖} := fun j z hz =>
    lt_trans (hrψ j) hz
  have hwU : ∀ j, IsFiniteEnergyCurve H J (U j) (w j) := fun j =>
    (isFiniteEnergyCurve_mono H J _ _ _ (hwFE j) (Set.subset_univ _)).1
  have hwE : ∀ j, energy H (U j) (w j) ≤ ENNReal.ofReal T := by
    intro j
    refine ((isFiniteEnergyCurve_mono H J _ _ _ (hwFE j) (Set.subset_univ _)).2.1).trans ?_
    rw [((hresc j).2.2.2 Set.univ MeasurableSet.univ).1]
    exact hE _
  have hwd : ∀ j, dlambdaEnergy H (U j) (w j) ≤ ENNReal.ofReal γ := by
    intro j
    rw [((hresc j).2.2.2 (U j) (hUo j).measurableSet).2]
    exact (lintegral_mono_set (hUsub j)).trans (hdl _)
  obtain ⟨χ₂, hχ₂, W, hW, -, -, hconv⟩ :=
    exists_subseq_tendstoCInftyLocOn_of_dlambdaEnergy_le H hH J hJ U hUo hUm hUu w hwU T γ
      hwE hwd hγ₁ hwa1
  have hO : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
  -- pointwise convergence of `a`
  have hapt : ∀ z, z ≠ 0 →
      Tendsto (fun j => aCoord H (w (χ₂ j) z)) atTop (𝓝 (aCoord H (W z))) := by
    intro z hz
    have hu := hunifK _ _ _ {z} hconv
      (Set.singleton_subset_iff.2 hz) isCompact_singleton
    have := hu.tendsto_at (Set.mem_singleton z)
    exact (hacont _ (hW.2.1 z hz)).tendsto.comp this
  by_cases hB : ∃ B : ℝ, ∃ᶠ j in atTop, c (χ₂ j) ≤ B
  · -- bounded normalisations: the limit cylinder has `a` bounded below and action `≥ e`
    obtain ⟨B, hBf⟩ := hB
    have hWa : ∀ z, z ≠ 0 → -N - B ≤ aCoord H (W z) := by
      intro z hz
      have hmem : ∃ᶠ j in atTop, aCoord H (w (χ₂ j) z) ∈ Set.Ici (-N - B) := by
        refine hBf.mono fun j hj => ?_
        simp only [Set.mem_Ici, hwa]
        linarith [hN (ψ (χ₂ j)) z]
      exact isClosed_Ici.mem_of_frequently_of_tendsto hmem (hapt z hz)
    have hWact : ∀ ρ : ℝ, 0 < ρ → e ≤ loopAction H W (ccwLoop ρ) := by
      intro ρ hρ
      have hlim := tendsto_loopAction_of_tendstoCInftyLocOn H hH {z : ℂ | z ≠ 0} hO
        (fun j => w (χ₂ j)) W (fun j => (hwFE _).1.mono (Set.subset_univ _)) hW.1
        (fun j z _ => (hwFE _).2.1 z trivial) hW.2.1 hconv (ccwLoop ρ) (hloopC ρ)
        (hloop0 ρ hρ)
      refine ge_of_tendsto hlim ?_
      have hrr : Tendsto (fun j => r (ψ (χ₂ j))) atTop (𝓝 0) :=
        hr.comp ((hφ.comp hχ).comp hχ₂).tendsto_atTop
      filter_upwards [hrr.eventually (gt_mem_nhds hρ)] with j hj
      rw [hwact]
      exact hact _ ρ hj
    -- restrict to the punctured unit disk
    have hsub : ball (0 : ℂ) 1 \ {0} ⊆ {z : ℂ | z ≠ 0} := fun z hz => hz.2
    have hW1 := (isFiniteEnergyCurve_mono H J _ _ _ hW hsub).1
    have hPW : ContDiffOn ℝ ∞ (fun z => proj H (W z)) {z : ℂ | z ≠ 0} :=
      hPs.comp hW.1 (fun z hz => hW.2.1 z hz)
    have hcw : ∀ ρ : ℝ, 0 < ρ → loopAction H W (cwLoop 0 ρ) ≤ -e := by
      intro ρ hρ
      rw [loopAction_cwLoop_eq_neg_ccwLoop H W hO hPW ρ (fun θ => by
        simp only [Set.mem_setOf_eq]
        exact circleMap_ne_center hρ.ne')]
      linarith [hWact ρ hρ]
    have hcwev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), loopAction H W (cwLoop 0 ρ) ≤ -e :=
      eventually_nhdsWithin_of_forall fun ρ hρ => hcw ρ hρ
    rcases punctured_disk_asymptotics H hH J hJ W hW1 with hrem | ⟨Q, -, hQ, -, hQneg, -⟩
    · have h0l := tendsto_loopAction_of_isRemovablePuncture H hH J hJ W hrem
      have := le_of_tendsto h0l hcwev
      linarith
    · have hQle : Q ≤ -e := le_of_tendsto hQ hcwev
      have hbot := hQneg (by linarith)
      have hev := hbot.eventually (eventually_lt_atBot (-N - B))
      obtain ⟨z, hz1, hz2⟩ := (hev.and self_mem_nhdsWithin).exists
      exact absurd (hWa z hz2) (not_le.2 hz1)
  · -- unbounded normalisations: contradiction at the limit point `zs`
    push_neg at hB
    have hctop : Tendsto (fun j => c (χ₂ j)) atTop atTop := by
      rw [Filter.tendsto_atTop]
      intro B
      exact (hB B).mono fun j hj => hj.le
    set zz : ℕ → ℂ := fun j => z (χ (χ₂ j)) with hzz
    have hzzlim : Tendsto zz atTop (𝓝 zs) := hzlim.comp hχ₂.tendsto_atTop
    have hKsub : Kc ⊆ {z : ℂ | z ≠ 0} := fun z hz h => h0 (h ▸ hz)
    have hunif := hunifK _ _ _ Kc hconv hKsub hKc
    have hWc : ContinuousWithinAt W Kc zs :=
      ((hW.1.continuousOn).continuousAt (hO.mem_nhds hzs0)).continuousWithinAt
    have hval : Tendsto (fun j => w (χ₂ j) (zz j)) atTop (𝓝 (W zs)) :=
      hunif.tendsto_comp hWc (tendsto_nhdsWithin_iff.2 ⟨hzzlim,
        Eventually.of_forall fun j => hzK _⟩)
    have hA : Tendsto (fun j => aCoord H (w (χ₂ j) (zz j))) atTop (𝓝 (aCoord H (W zs))) :=
      (hacont _ (hW.2.1 zs hzs0)).tendsto.comp hval
    have hA' : Tendsto (fun j => aCoord H (w (χ₂ j) (zz j))) atTop atBot := by
      have hlow : Tendsto (fun j => M - c (χ₂ j)) atTop atBot :=
        tendsto_atBot_add_const_left _ M (tendsto_neg_atTop_atBot.comp hctop)
      refine tendsto_atBot_mono (fun j => ?_) hlow
      rw [hwa]
      have := hzM (χ (χ₂ j))
      simp only [ψ, Function.comp] at this ⊢
      linarith
    exact not_tendsto_nhds_of_tendsto_atBot hA' _ hA

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (T γ e N : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ T → γ < Q.T) (he : 0 < e)
    (r : ℕ → ℝ) (hr0 : ∀ k, 0 < r k) (hr : Tendsto r atTop (𝓝 0)) (v : ℕ → ℂ → V n)
    (hv : ∀ k, IsFiniteEnergyCurve H J Set.univ (v k))
    (hE : ∀ k, energy H Set.univ (v k) ≤ ENNReal.ofReal T)
    (hdl : ∀ k, dlambdaEnergy H {z | r k < ‖z‖} (v k) ≤ ENNReal.ofReal γ)
    (hact : ∀ k, ∀ ρ : ℝ, r k < ρ → e ≤ loopAction H (v k) (ccwLoop ρ))
    (hN : ∀ k z, -N ≤ aCoord H (v k z)) :
    ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc →
      ∀ M : ℝ, ∀ᶠ k in atTop, ∀ z ∈ Kc, M ≤ aCoord H (v k z) :=
  tendsto_aCoord_atTop_of_small_area_aux H hH J hJ T γ e N hγ hγ₁ he r hr0 hr v hv hE hdl hact hN
