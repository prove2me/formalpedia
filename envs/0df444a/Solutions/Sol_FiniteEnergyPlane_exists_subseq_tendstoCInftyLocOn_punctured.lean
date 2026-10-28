-- Prove2me | solution 1 for FiniteEnergyPlane.exists_subseq_tendstoCInftyLocOn_punctured
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-26T21:52:44.665447+00:00
-- url     : https://prove2.me/submissions/480b278a-95e9-41cc-b05e-6d80ada1b1c3

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInftyLocOn_of_isOpen
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- `C^∞_loc` compactness on the punctured plane for pseudoholomorphic maps on growing punctured
discs. -/
theorem exists_subseq_tendstoCInftyLocOn_punctured_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (v : ℕ → ℂ → E) (R : ℕ → ℝ)
    (hR : Tendsto R atTop atTop) (hv : ∀ k, ContDiffOn ℝ ∞ (v k) {z | z ≠ 0 ∧ ‖z‖ < R k})
    (hhol : ∀ k, JHolomorphic.IsJHolomorphicOn J {z | z ≠ 0 ∧ ‖z‖ < R k} (v k))
    (hbd : ∀ K ⊆ {z : ℂ | z ≠ 0}, IsCompact K → ∃ K' : Set E, IsCompact K' ∧ K' ⊆ O ∧
      ∃ M : ℝ, ∀ᶠ k in atTop, ∀ z ∈ K, v k z ∈ K' ∧ ‖fderiv ℝ (v k) z‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → E, ContDiffOn ℝ ∞ w {z | z ≠ 0} ∧
      JHolomorphic.IsJHolomorphicOn J {z | z ≠ 0} w ∧ Set.MapsTo w {z | z ≠ 0} O ∧
      JHolomorphic.TendstoCInftyLocOn (fun j => v (φ j)) w {z | z ≠ 0} := by
  classical
  -- the exhausting annuli
  set A : ℕ → Set ℂ := fun N => {z | ((N : ℝ) + 2)⁻¹ < ‖z‖ ∧ ‖z‖ < (N : ℝ) + 2} with hAdef
  have hAo : ∀ N, IsOpen (A N) := fun N =>
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hA0 : ∀ N, ∀ z ∈ A N, z ≠ 0 := fun N z hz =>
    norm_pos_iff.1 (lt_trans (by positivity) hz.1)
  -- one stage: a convergent subsequence on the annulus `A N`
  have hstage : ∀ (ψ : ℕ → ℕ) (N : ℕ), ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (Tendsto ψ atTop atTop → ∃ g : ℂ → E, ContDiffOn ℝ ∞ g (A N) ∧
        JHolomorphic.IsJHolomorphicOn J (A N) g ∧ Set.MapsTo g (A N) O ∧
        JHolomorphic.TendstoCInftyLocOn (fun j => v (ψ (σ j))) g (A N)) := by
    intro ψ N
    by_cases hψ : Tendsto ψ atTop atTop
    swap
    · exact ⟨id, strictMono_id, fun h => absurd h hψ⟩
    set C : Set ℂ := {z | ((N : ℝ) + 2)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (N : ℝ) + 2} with hCdef
    have hCc : IsCompact C := by
      refine (isCompact_closedBall (0 : ℂ) ((N : ℝ) + 2)).of_isClosed_subset
        ((isClosed_le continuous_const continuous_norm).inter
          (isClosed_le continuous_norm continuous_const)) fun z hz => ?_
      rw [mem_closedBall_zero_iff]; exact hz.2
    have hC0 : C ⊆ {z : ℂ | z ≠ 0} := fun z hz =>
      norm_pos_iff.1 (lt_of_lt_of_le (by positivity) hz.1)
    have hAC : A N ⊆ C := fun z hz => ⟨hz.1.le, hz.2.le⟩
    obtain ⟨K', hK'c, hK'O, M, hM⟩ := hbd C hC0 hCc
    obtain ⟨k₁, hk₁⟩ := eventually_atTop.1
      (((hR.comp hψ).eventually (eventually_gt_atTop ((N : ℝ) + 2))).and (hψ.eventually hM))
    have hk : ∀ j, (N : ℝ) + 2 < R (ψ (j + k₁)) ∧
        ∀ z ∈ C, v (ψ (j + k₁)) z ∈ K' ∧ ‖fderiv ℝ (v (ψ (j + k₁))) z‖ ≤ M :=
      fun j => hk₁ _ (Nat.le_add_left _ _)
    have hsub : ∀ j, A N ⊆ {z | z ≠ 0 ∧ ‖z‖ < R (ψ (j + k₁))} := fun j z hz =>
      ⟨hA0 N z hz, hz.2.trans (hk j).1⟩
    obtain ⟨σ₀, hσ₀, g, hgs, hgh, hgO, hconv⟩ :=
      exists_subseq_tendstoCInftyLocOn_of_isOpen J O hJ (A N) (hAo N)
        (fun j => v (ψ (j + k₁))) (fun j => (hv _).mono (hsub j))
        (fun j z hz => hhol _ z (hsub j hz))
        (fun K hK _ => ⟨K', hK'c, hK'O, M, fun j z hz => (hk j).2 z (hAC (hK hz))⟩)
    refine ⟨fun j => σ₀ j + k₁, fun a b hab => by
      have := hσ₀ hab
      simp only
      omega, fun _ => ⟨g, hgs, hgh, hgO, hconv⟩⟩
  choose σf hσf hgf using hstage
  -- nested subsequences
  let Ψ : ℕ → ℕ → ℕ := fun N =>
    Nat.rec (motive := fun _ => ℕ → ℕ) (σf id 0) (fun N ΨN => ΨN ∘ σf ΨN (N + 1)) N
  have hΨ0 : Ψ 0 = σf id 0 := rfl
  have hΨs : ∀ N, Ψ (N + 1) = Ψ N ∘ σf (Ψ N) (N + 1) := fun N => rfl
  have hΨmono : ∀ N, StrictMono (Ψ N) := by
    intro N
    induction N with
    | zero => rw [hΨ0]; exact hσf _ _
    | succ N ih => rw [hΨs]; exact ih.comp (hσf _ _)
  have hΨconv : ∀ N : ℕ, ∃ g : ℂ → E, ContDiffOn ℝ ∞ g (A N) ∧
      JHolomorphic.IsJHolomorphicOn J (A N) g ∧ Set.MapsTo g (A N) O ∧
      JHolomorphic.TendstoCInftyLocOn (fun j => v (Ψ N j)) g (A N) := by
    intro N
    cases N with
    | zero => simpa [hΨ0] using hgf id 0 tendsto_id
    | succ N =>
      rw [hΨs]
      exact hgf (Ψ N) (N + 1) (hΨmono N).tendsto_atTop
  choose g hgs hgh hgO hgc using hΨconv
  have hrange : ∀ N j : ℕ, N ≤ j → Set.range (Ψ j) ⊆ Set.range (Ψ N) := by
    intro N j hNj
    induction j, hNj using Nat.le_induction with
    | base => exact subset_rfl
    | succ j _ ih => rw [hΨs]; exact (Set.range_comp_subset_range _ _).trans ih
  -- the diagonal
  set d : ℕ → ℕ := fun j => Ψ j j with hd
  have hdmono : StrictMono d := by
    refine strictMono_nat_of_lt_succ fun j => ?_
    show Ψ j j < Ψ (j + 1) (j + 1)
    rw [hΨs]
    exact hΨmono j (lt_of_lt_of_le (Nat.lt_succ_self j) ((hσf _ _).id_le _))
  have hdconv : ∀ N : ℕ, JHolomorphic.TendstoCInftyLocOn (fun j => v (d j)) (g N) (A N) := by
    intro N K hK hKc m
    have hex : ∀ j : ℕ, N ≤ j → ∃ i, Ψ N i = d j := fun j hj => hrange N j hj ⟨j, rfl⟩
    set τ : ℕ → ℕ := fun j : ℕ =>
      @dite _ (∃ i : ℕ, Ψ N i = d j) (Classical.propDecidable _) (fun h => Classical.choose h)
        (fun _ => 0) with hτ
    have hτspec : ∀ j : ℕ, N ≤ j → Ψ N (τ j) = d j := by
      intro j hj
      simp only [hτ, dif_pos (hex j hj)]
      exact Classical.choose_spec (hex j hj)
    have hτt : Tendsto τ atTop atTop := by
      refine tendsto_atTop.2 fun b => ?_
      filter_upwards [eventually_ge_atTop N, eventually_gt_atTop (Ψ N b)] with j hjN hjb
      by_contra hlt
      push_neg at hlt
      have h1 := (hΨmono N).monotone hlt.le
      rw [hτspec j hjN] at h1
      have h2 := hdmono.id_le j
      exact lt_irrefl _ (hjb.trans_le (h2.trans h1))
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h := Metric.tendstoUniformlyOn_iff.1 (hgc N K hK hKc m) ε hε
    filter_upwards [hτt.eventually h, eventually_ge_atTop N] with j hj hjN x hx
    have := hj x hx
    rwa [hτspec j hjN] at this
  -- pointwise limits agree
  have hpt : ∀ (N : ℕ) (z : ℂ), z ∈ A N → Tendsto (fun j => v (d j) z) atTop (𝓝 (g N z)) := by
    intro N z hz
    have h0 := (hdconv N {z} (by simpa using hz) isCompact_singleton 0).tendsto_at rfl
    have := ((continuous_eval_const (Fin.elim0 : Fin 0 → ℂ)).tendsto _).comp h0
    simpa [Function.comp_def, iteratedFDeriv_zero_apply] using this
  have hmemA : ∀ (N : ℕ) (z : ℂ), z ≠ 0 → ‖z‖ ≤ N → ‖z‖⁻¹ ≤ N → z ∈ A N := by
    intro N z hz h1 h2
    have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
    refine ⟨?_, by linarith⟩
    rw [inv_lt_comm₀ (by positivity) hzp]
    linarith
  set Nz : ℂ → ℕ := fun z => ⌈max ‖z‖ ‖z‖⁻¹⌉₊ with hNz
  have hfl : ∀ z : ℂ, z ≠ 0 → z ∈ A (Nz z) := fun z hz =>
    hmemA _ z hz ((le_max_left _ _).trans (Nat.le_ceil _))
      ((le_max_right _ _).trans (Nat.le_ceil _))
  set w : ℂ → E := fun z => g (Nz z) z with hw
  have hwN : ∀ N : ℕ, ∀ z ∈ A N, w z = g N z := fun N z hz =>
    tendsto_nhds_unique (hpt _ z (hfl z (hA0 N z hz))) (hpt N z hz)
  have hwev : ∀ N : ℕ, ∀ z ∈ A N, w =ᶠ[𝓝 z] g N := fun N z hz =>
    Filter.eventually_of_mem ((hAo N).mem_nhds hz) (hwN N)
  have hUo : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
  have hwsm : ContDiffOn ℝ ∞ w {z | z ≠ 0} := by
    intro z hz
    have hz' := hfl z hz
    exact (((hgs _).contDiffAt ((hAo _).mem_nhds hz')).congr_of_eventuallyEq
      (hwev _ z hz')).contDiffWithinAt
  refine ⟨d, hdmono, w, hwsm, fun z hz => ?_, fun z hz => ?_, ?_⟩
  · have hz' := hfl z hz
    obtain ⟨-, hdb⟩ := hgh _ z hz'
    refine ⟨((hwsm.contDiffAt (hUo.mem_nhds hz)).differentiableAt (by simp)), ?_⟩
    unfold JHolomorphic.dbarJ at hdb ⊢
    rw [(hwev _ z hz').fderiv_eq, hwN _ z hz']
    exact hdb
  · rw [hwN _ z (hfl z hz)]
    exact hgO _ (hfl z hz)
  · intro K hK hKc m
    have hgc' : ContinuousOn (fun z : ℂ => ‖z‖ + ‖z‖⁻¹) K :=
      continuous_norm.continuousOn.add
        (continuous_norm.continuousOn.inv₀ fun z hz => norm_ne_zero_iff.2 (hK hz))
    obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hgc'
    set N := ⌈B⌉₊ with hN
    have hKN : K ⊆ A N := by
      intro z hz
      have h := hB z hz
      have h0 : 0 ≤ ‖z‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
      rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) h0)] at h
      exact hmemA N z (hK hz) (by linarith [Nat.le_ceil B]) (by linarith [Nat.le_ceil B, norm_nonneg z])
    refine (hdconv N K hKN hKc m).congr_right fun z hz => ?_
    exact ((hwev N z (hKN hz)).iteratedFDeriv (𝕜 := ℝ) m).self_of_nhds.symm

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (v : ℕ → ℂ → E) (R : ℕ → ℝ)
    (hR : Tendsto R atTop atTop) (hv : ∀ k, ContDiffOn ℝ ∞ (v k) {z | z ≠ 0 ∧ ‖z‖ < R k})
    (hhol : ∀ k, JHolomorphic.IsJHolomorphicOn J {z | z ≠ 0 ∧ ‖z‖ < R k} (v k))
    (hbd : ∀ K ⊆ {z : ℂ | z ≠ 0}, IsCompact K → ∃ K' : Set E, IsCompact K' ∧ K' ⊆ O ∧
      ∃ M : ℝ, ∀ᶠ k in atTop, ∀ z ∈ K, v k z ∈ K' ∧ ‖fderiv ℝ (v k) z‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → E, ContDiffOn ℝ ∞ w {z | z ≠ 0} ∧
      JHolomorphic.IsJHolomorphicOn J {z | z ≠ 0} w ∧ Set.MapsTo w {z | z ≠ 0} O ∧
      JHolomorphic.TendstoCInftyLocOn (fun j => v (φ j)) w {z | z ≠ 0} :=
  FiniteEnergyPlane.exists_subseq_tendstoCInftyLocOn_punctured_aux J O hJ v R hR hv hhol hbd
