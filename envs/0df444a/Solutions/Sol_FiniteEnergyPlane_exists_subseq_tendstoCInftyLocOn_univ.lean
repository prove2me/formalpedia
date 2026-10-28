-- Prove2me | solution 1 for FiniteEnergyPlane.exists_subseq_tendstoCInftyLocOn_univ
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-25T18:35:30.482605+00:00
-- url     : https://prove2.me/submissions/12b1a604-a678-4714-8e4f-9322c35fed8b

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_JHolomorphic_exists_subseq_tendstoCInftyLocOn
import Theorems.Thm_FiniteEnergyPlane_isJHolomorphicOn_comp_add_smul
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- `C^∞_loc` compactness on the whole plane for pseudoholomorphic maps on growing discs. -/
theorem exists_subseq_tendstoCInftyLocOn_univ_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (v : ℕ → ℂ → E) (ρ : ℕ → ℝ)
    (hρ : Tendsto ρ atTop atTop) (hv : ∀ k, ContDiffOn ℝ 1 (v k) (ball 0 (ρ k)))
    (hhol : ∀ k, JHolomorphic.IsJHolomorphicOn J (ball 0 (ρ k)) (v k))
    (hbd : ∀ R : ℝ, ∃ K : Set E, IsCompact K ∧ K ⊆ O ∧ ∃ M : ℝ, ∀ k, R < ρ k →
      ∀ z ∈ ball (0 : ℂ) R, v k z ∈ K ∧ ‖fderiv ℝ (v k) z‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → E, ContDiff ℝ ∞ w ∧
      JHolomorphic.IsJHolomorphicOn J Set.univ w ∧ (∀ z, w z ∈ O) ∧
      JHolomorphic.TendstoCInftyLocOn (fun j => v (φ j)) w Set.univ := by
  classical
  -- transfer of `C^∞` convergence from the unit disc to the disc of radius `r`
  have htr : ∀ r : ℝ, 0 < r → ∀ (F : ℕ → ℂ → E) (g : ℂ → E),
      JHolomorphic.TendstoCInftyLocOn F g (ball 0 1) →
      JHolomorphic.TendstoCInftyLocOn (fun j y => F j (r⁻¹ • y)) (fun y => g (r⁻¹ • y))
        (ball 0 r) := by
    intro r hr F g hFg K hK hKc m
    set L : ℂ ≃L[ℝ] ℂ :=
      (LinearEquiv.smulOfNeZero ℝ ℂ r⁻¹ (inv_ne_zero hr.ne')).toContinuousLinearEquiv with hLdef
    have hLx : ∀ y, L y = r⁻¹ • y := fun y => rfl
    set T := ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := E)
      (fun _ : Fin m => (L : ℂ →L[ℝ] ℂ)) with hT
    have hcomp : ∀ f : ℂ → E, iteratedFDeriv ℝ m (fun y => f (r⁻¹ • y)) =
        (T ∘ iteratedFDeriv ℝ m f) ∘ L := by
      intro f
      funext y
      have := L.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (Set.mem_univ (L y)) m
      simp only [iteratedFDerivWithin_univ, Set.preimage_univ] at this
      rw [show (fun y => f (r⁻¹ • y)) = f ∘ L from funext fun y => by simp [hLx], this]
      rfl
    have hK' : L '' K ⊆ ball 0 1 := by
      rintro _ ⟨y, hy, rfl⟩
      have := mem_ball_zero_iff.1 (hK hy)
      rw [mem_ball_zero_iff, hLx, norm_smul, norm_inv, Real.norm_of_nonneg hr.le,
        inv_mul_lt_iff₀ hr, mul_one]
      exact this
    have hU := hFg (L '' K) hK' (hKc.image L.continuous) m
    have h2 := (T.uniformContinuous.comp_tendstoUniformlyOn hU).comp L
    simp only [hcomp]
    exact h2.mono (Set.subset_preimage_image L K)
  -- one stage: a convergent subsequence on the disc of radius `N + 1`
  have hstage : ∀ (ψ : ℕ → ℕ) (N : ℕ), ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (Tendsto ψ atTop atTop → ∃ g : ℂ → E, ContDiffOn ℝ ∞ g (ball 0 ((N : ℝ) + 1)) ∧
        JHolomorphic.IsJHolomorphicOn J (ball 0 ((N : ℝ) + 1)) g ∧
        Set.MapsTo g (ball 0 ((N : ℝ) + 1)) O ∧
        JHolomorphic.TendstoCInftyLocOn (fun j => v (ψ (σ j))) g (ball 0 ((N : ℝ) + 1))) := by
    intro ψ N
    by_cases hψ : Tendsto ψ atTop atTop
    swap
    · exact ⟨id, strictMono_id, fun h => absurd h hψ⟩
    set R : ℝ := (N : ℝ) + 1 with hRdef
    have hR : 0 < R := by positivity
    obtain ⟨K, hKc, hKO, M, hM⟩ := hbd R
    obtain ⟨k₁, hk₁⟩ := eventually_atTop.1 ((hρ.comp hψ).eventually (eventually_gt_atTop R))
    have hk : ∀ j, R < ρ (ψ (j + k₁)) := fun j => hk₁ _ (Nat.le_add_left _ _)
    set u : ℕ → ℂ → E := fun j x => v (ψ (j + k₁)) (R • x) with hu
    have hmem : ∀ x ∈ ball (0 : ℂ) 1, R • x ∈ ball (0 : ℂ) R := by
      intro x hx
      rw [mem_ball_zero_iff] at hx ⊢
      rw [norm_smul, Real.norm_of_nonneg hR.le]
      nlinarith
    have hmemρ : ∀ j, ∀ x ∈ ball (0 : ℂ) 1, R • x ∈ ball (0 : ℂ) (ρ (ψ (j + k₁))) :=
      fun j x hx => ball_subset_ball (hk j).le (hmem x hx)
    have hA := fun j => isJHolomorphicOn_comp_add_smul J (ball 0 (ρ (ψ (j + k₁))))
      (v (ψ (j + k₁))) (hhol _) 0 R
    have hu1 : ∀ j, ContDiffOn ℝ 1 (u j) (ball 0 1) := fun j =>
      (hv _).comp (by fun_prop : ContDiff ℝ 1 fun x : ℂ => R • x).contDiffOn
        (fun x hx => hmemρ j x hx)
    have huhol : ∀ j, JHolomorphic.IsJHolomorphicOn J (ball 0 1) (u j) := by
      intro j x hx
      have h := (hA j).1 x (by simpa using hmemρ j x hx)
      simp only [zero_add] at h
      exact h
    have humaps : ∀ j, Set.MapsTo (u j) (ball 0 1) K := fun j x hx =>
      (hM _ (hk j) _ (hmem x hx)).1
    have huC : ∀ j, ∀ x ∈ ball (0 : ℂ) 1, ‖fderiv ℝ (u j) x‖ ≤ R * M := by
      intro j x hx
      have h := (hA j).2 x (by simpa using hmemρ j x hx)
      simp only [zero_add] at h
      rw [show u j = fun w => v (ψ (j + k₁)) (R • w) from rfl, h, norm_smul,
        Real.norm_of_nonneg hR.le]
      exact mul_le_mul_of_nonneg_left (hM _ (hk j) _ (hmem x hx)).2 hR.le
    obtain ⟨σ₀, hσ₀, h, hh, hhh, hhK, hconv⟩ :=
      JHolomorphic.exists_subseq_tendstoCInftyLocOn J (fun _ => J) O K hJ (fun _ => hJ)
        (fun K' _ _ m => Metric.tendstoUniformlyOn_iff.2 fun e he =>
          Eventually.of_forall fun _ _ _ => by simpa using he) hKc hKO u hu1 huhol humaps
        (R * M) huC
    refine ⟨fun j => σ₀ j + k₁, fun a b hab => by
        have := hσ₀ hab
        simp only
        omega, fun _ => ⟨fun y => h (R⁻¹ • y), ?_, ?_, ?_, ?_⟩⟩
    · have hmap : ∀ y ∈ ball (0 : ℂ) R, R⁻¹ • y ∈ ball (0 : ℂ) 1 := by
        intro y hy
        rw [mem_ball_zero_iff] at hy ⊢
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hR.le, inv_mul_lt_iff₀ hR, mul_one]
        exact hy
      exact hh.comp (by fun_prop : ContDiff ℝ ∞ fun y : ℂ => R⁻¹ • y).contDiffOn hmap
    · intro y hy
      have hy1 : (0 : ℂ) + R⁻¹ • y ∈ ball (0 : ℂ) 1 := by
        rw [zero_add, mem_ball_zero_iff]
        rw [mem_ball_zero_iff] at hy
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hR.le, inv_mul_lt_iff₀ hR, mul_one]
        exact hy
      have := (isJHolomorphicOn_comp_add_smul J (ball 0 1) h hhh 0 R⁻¹).1 y hy1
      simp only [zero_add] at this
      exact this
    · intro y hy
      refine hKO (hhK ?_)
      rw [mem_ball_zero_iff] at hy ⊢
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hR.le, inv_mul_lt_iff₀ hR, mul_one]
      exact hy
    · have := htr R hR (fun j => u (σ₀ j)) h hconv
      have he : (fun j y => u (σ₀ j) (R⁻¹ • y)) = fun j => v (ψ (σ₀ j + k₁)) := by
        funext j y
        simp only [hu, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
      rw [he] at this
      exact this
  choose σf hσf hgf using hstage
  -- nested subsequences
  let Ψ : ℕ → ℕ → ℕ := fun N => Nat.rec (motive := fun _ => ℕ → ℕ) (σf id 0) (fun N ΨN => ΨN ∘ σf ΨN (N + 1)) N
  have hΨ0 : Ψ 0 = σf id 0 := rfl
  have hΨs : ∀ N, Ψ (N + 1) = Ψ N ∘ σf (Ψ N) (N + 1) := fun N => rfl
  have hΨmono : ∀ N, StrictMono (Ψ N) := by
    intro N
    induction N with
    | zero => rw [hΨ0]; exact hσf _ _
    | succ N ih => rw [hΨs]; exact ih.comp (hσf _ _)
  have hΨconv : ∀ N : ℕ, ∃ g : ℂ → E, ContDiffOn ℝ ∞ g (ball 0 ((N : ℝ) + 1)) ∧
      JHolomorphic.IsJHolomorphicOn J (ball 0 ((N : ℝ) + 1)) g ∧
      Set.MapsTo g (ball 0 ((N : ℝ) + 1)) O ∧
      JHolomorphic.TendstoCInftyLocOn (fun j => v (Ψ N j)) g (ball 0 ((N : ℝ) + 1)) := by
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
  have hdconv : ∀ N : ℕ, JHolomorphic.TendstoCInftyLocOn (fun j => v (d j)) (g N)
      (ball 0 ((N : ℝ) + 1)) := by
    intro N K hK hKc m
    have hex : ∀ j : ℕ, N ≤ j → ∃ i, Ψ N i = d j := fun j hj => hrange N j hj ⟨j, rfl⟩
    set τ : ℕ → ℕ := fun j : ℕ =>
      @dite _ (∃ i : ℕ, Ψ N i = d j) (Classical.propDecidable _) (fun h => Classical.choose h) (fun _ => 0) with hτ
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
  have hpt : ∀ (N : ℕ) (z : ℂ), z ∈ ball (0 : ℂ) ((N : ℝ) + 1) →
      Tendsto (fun j => v (d j) z) atTop (𝓝 (g N z)) := by
    intro N z hz
    have h0 := (hdconv N {z} (by simpa using hz) isCompact_singleton 0).tendsto_at rfl
    have := ((continuous_eval_const (Fin.elim0 : Fin 0 → ℂ)).tendsto _).comp h0
    simpa [Function.comp_def, iteratedFDeriv_zero_apply] using this
  set w : ℂ → E := fun z => g ⌊‖z‖⌋₊ z with hw
  have hfl : ∀ z : ℂ, z ∈ ball (0 : ℂ) ((⌊‖z‖⌋₊ : ℝ) + 1) := fun z => by
    rw [mem_ball_zero_iff]
    exact Nat.lt_floor_add_one _
  have hwN : ∀ N : ℕ, ∀ z ∈ ball (0 : ℂ) ((N : ℝ) + 1), w z = g N z := fun N z hz =>
    tendsto_nhds_unique (hpt _ z (hfl z)) (hpt N z hz)
  have hwev : ∀ N : ℕ, ∀ z ∈ ball (0 : ℂ) ((N : ℝ) + 1), w =ᶠ[𝓝 z] g N := fun N z hz =>
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) (hwN N)
  have hwsm : ContDiff ℝ ∞ w := by
    refine contDiff_iff_contDiffAt.2 fun z => ?_
    have hz := hfl z
    exact ((hgs _).contDiffAt (isOpen_ball.mem_nhds hz)).congr_of_eventuallyEq (hwev _ z hz)
  refine ⟨d, hdmono, w, hwsm, fun z _ => ?_, fun z => ?_, ?_⟩
  · have hz := hfl z
    obtain ⟨-, hdb⟩ := hgh _ z hz
    refine ⟨hwsm.differentiable (by simp) z, ?_⟩
    unfold JHolomorphic.dbarJ at hdb ⊢
    rw [(hwev _ z hz).fderiv_eq, hwN _ z hz]
    exact hdb
  · rw [hwN _ z (hfl z)]
    exact hgO _ (hfl z)
  · intro K _ hKc m
    obtain ⟨r, hr⟩ := hKc.isBounded.subset_ball (0 : ℂ)
    set N := ⌈r⌉₊ with hN
    have hKN : K ⊆ ball (0 : ℂ) ((N : ℝ) + 1) :=
      hr.trans (ball_subset_ball (by linarith [Nat.le_ceil r]))
    refine (hdconv N K hKN hKc m).congr_right fun z hz => ?_
    exact ((hwev N z (hKN hz)).iteratedFDeriv (𝕜 := ℝ) m).self_of_nhds.symm

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (v : ℕ → ℂ → E) (ρ : ℕ → ℝ)
    (hρ : Tendsto ρ atTop atTop) (hv : ∀ k, ContDiffOn ℝ 1 (v k) (ball 0 (ρ k)))
    (hhol : ∀ k, JHolomorphic.IsJHolomorphicOn J (ball 0 (ρ k)) (v k))
    (hbd : ∀ R : ℝ, ∃ K : Set E, IsCompact K ∧ K ⊆ O ∧ ∃ M : ℝ, ∀ k, R < ρ k →
      ∀ z ∈ ball (0 : ℂ) R, v k z ∈ K ∧ ‖fderiv ℝ (v k) z‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → E, ContDiff ℝ ∞ w ∧
      JHolomorphic.IsJHolomorphicOn J Set.univ w ∧ (∀ z, w z ∈ O) ∧
      JHolomorphic.TendstoCInftyLocOn (fun j => v (φ j)) w Set.univ :=
  exists_subseq_tendstoCInftyLocOn_univ_aux J O hJ v ρ hρ hv hhol hbd
