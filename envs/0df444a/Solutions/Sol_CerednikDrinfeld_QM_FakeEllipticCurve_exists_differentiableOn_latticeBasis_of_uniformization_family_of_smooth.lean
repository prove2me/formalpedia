-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_differentiableOn_latticeBasis_of_uniformization_family_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/350a28ab-b984-5c4b-a895-494288abe475

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_CerednikDrinfeld_QMFineModuli

import Theorems.Thm_Complex_contDiffOn_one_of_differentiableOn_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_differentiableOn_latticeBasis_of_uniformization_family_of_smooth

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise BigOperators

open Topology Metric Filter Set

noncomputable section

namespace RelKerFrame

local notation "P" => ℂ × (Fin 2 → ℂ)

theorem contDiffOn_one_of_differentiableOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {Φ : P → E} {U : Set P} (hU : IsOpen U) (hΦ : DifferentiableOn ℂ Φ U) : ContDiffOn ℂ 1 Φ U := by
  have hfin : Module.finrank ℂ (Fin 3 → ℂ) = Module.finrank ℂ P := by
    rw [Module.finrank_fin_fun, Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]
  let A : (Fin 3 → ℂ) ≃L[ℂ] P := ContinuousLinearEquiv.ofFinrankEq hfin
  have hU' : IsOpen (A ⁻¹' U) := hU.preimage A.continuous
  have hf : DifferentiableOn ℂ (Φ ∘ A) (A ⁻¹' U) :=
    hΦ.comp A.differentiableOn (fun x hx => hx)
  have hC : ContDiffOn ℂ 1 (Φ ∘ A) (A ⁻¹' U) := Complex.contDiffOn_one_of_differentiableOn_pi hU' hf
  have heq : Φ = (Φ ∘ A) ∘ A.symm := by funext p; simp
  rw [heq]
  exact hC.comp A.symm.contDiff.contDiffOn (fun p hp => by simpa using hp)

theorem exists_branch
    (Φ : P → P) (U : Set P) (hU : IsOpen U) (hΦ : DifferentiableOn ℂ Φ U)
    (z₀ : ℂ) (w₀ : Fin 2 → ℂ) (hp₀ : ((z₀, w₀) : P) ∈ U)
    (hfst : ∀ p ∈ U, (Φ p).1 = p.1)
    (D : P ≃L[ℂ] P) (hD : HasFDerivAt Φ (D : P →L[ℂ] P) (z₀, w₀))
    (c : ℂ → (Fin 2 → ℂ)) (η : ℝ) (hη : 0 < η) (hc : DifferentiableOn ℂ c (ball z₀ η))
    (hc₀ : Φ (z₀, w₀) = (z₀, c z₀))
    (W : Set P) (hW : W ∈ 𝓝 ((z₀, w₀) : P)) :
    ∃ (ρ : ℝ) (v : ℂ → (Fin 2 → ℂ)), 0 < ρ ∧ ρ ≤ η ∧ v z₀ = w₀ ∧
      DifferentiableOn ℂ v (ball z₀ ρ) ∧
      (∀ z ∈ ball z₀ ρ, ((z, v z) : P) ∈ W ∧ Φ (z, v z) = (z, c z)) ∧
      (∃ W' ∈ 𝓝 ((z₀, w₀) : P), ∀ z ∈ ball z₀ ρ, ∀ w : Fin 2 → ℂ,
          ((z, w) : P) ∈ W' → Φ (z, w) = (z, c z) → w = v z) := by

  have hC1 : ContDiffAt ℂ 1 Φ (z₀, w₀) := (contDiffOn_one_of_differentiableOn hU hΦ).contDiffAt (hU.mem_nhds hp₀)
  have hstrict : HasStrictFDerivAt Φ (D : P →L[ℂ] P) (z₀, w₀) := hC1.hasStrictFDerivAt' hD one_ne_zero
  set Ψ := hC1.localInverse hD one_ne_zero with hΨ
  have hΨdef : Ψ = hstrict.localInverse Φ D (z₀, w₀) := rfl
  have hΨq₀ : Ψ (Φ (z₀, w₀)) = (z₀, w₀) := hC1.localInverse_apply_image hD one_ne_zero
  have hΨC1 : ContDiffAt ℂ 1 Ψ (Φ (z₀, w₀)) := hC1.to_localInverse hD one_ne_zero
  have hright : ∀ᶠ y in 𝓝 (Φ (z₀, w₀)), Φ (Ψ y) = y := by rw [hΨdef]; exact hstrict.eventually_right_inverse
  have hleft : ∀ᶠ x in 𝓝 ((z₀, w₀) : P), Ψ (Φ x) = x := by rw [hΨdef]; exact hstrict.eventually_left_inverse
  have hΨcont : ContinuousAt Ψ (Φ (z₀, w₀)) := by rw [hΨdef]; exact hstrict.localInverse_continuousAt

  have hΨdiff : ∀ᶠ y in 𝓝 (Φ (z₀, w₀)), DifferentiableAt ℂ Ψ y := by
    filter_upwards [hΨC1.eventually (by simp)] with y hy
    exact hy.differentiableAt one_ne_zero
  have hΨmem : ∀ᶠ y in 𝓝 (Φ (z₀, w₀)), Ψ y ∈ U ∩ W := by
    have : U ∩ W ∈ 𝓝 (Ψ (Φ (z₀, w₀))) := by rw [hΨq₀]; exact Filter.inter_mem (hU.mem_nhds hp₀) hW
    exact hΨcont.preimage_mem_nhds this
  obtain ⟨τ, hτ, hτsub⟩ := Metric.eventually_nhds_iff_ball.mp (hright.and (hΨdiff.and hΨmem))

  have hγc : ContinuousAt (fun z : ℂ => ((z, c z) : P)) z₀ :=
    continuousAt_id.prodMk ((hc.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hη))).continuousAt)
  have hγin : ∀ᶠ z in 𝓝 z₀, ((z, c z) : P) ∈ ball (Φ (z₀, w₀)) τ := by
    apply hγc.preimage_mem_nhds
    rw [← hc₀]; exact isOpen_ball.mem_nhds (mem_ball_self hτ)
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.eventually_nhds_iff_ball.mp hγin
  set ρ : ℝ := min ρ₁ η with hρ
  have hρpos : 0 < ρ := lt_min hρ₁ hη
  refine ⟨ρ, fun z => (Ψ (z, c z)).2, hρpos, min_le_right _ _, ?_, ?_, ?_, ?_⟩
  ·
    show (Ψ (z₀, c z₀)).2 = w₀
    rw [← hc₀, hΨq₀]
  ·
    intro z hz
    have hz₁ : z ∈ ball z₀ ρ₁ := ball_subset_ball (min_le_left _ _) hz
    have hzη : z ∈ ball z₀ η := ball_subset_ball (min_le_right _ _) hz
    have hy := hτsub _ (hρ₁sub z hz₁)
    have hΨd : DifferentiableAt ℂ Ψ (z, c z) := hy.2.1
    have hγd : DifferentiableAt ℂ (fun z : ℂ => ((z, c z) : P)) z :=
      differentiableAt_id.prodMk (hc.differentiableAt (isOpen_ball.mem_nhds hzη))
    exact ((hΨd.comp z hγd).snd).differentiableWithinAt
  ·
    intro z hz
    have hz₁ : z ∈ ball z₀ ρ₁ := ball_subset_ball (min_le_left _ _) hz
    have hy := hτsub _ (hρ₁sub z hz₁)
    obtain ⟨hr, -, hUW⟩ := hy

    have h1 : (Ψ (z, c z)).1 = z := by
      have := hfst _ hUW.1
      rw [hr] at this
      exact this.symm
    have hΨeq : Ψ (z, c z) = (z, (Ψ (z, c z)).2) := Prod.ext h1 rfl
    refine ⟨hΨeq ▸ hUW.2, ?_⟩
    rw [← hΨeq]; exact hr
  ·
    obtain ⟨W', hW', hW'sub⟩ : ∃ W' ∈ 𝓝 ((z₀, w₀) : P), ∀ x ∈ W', Ψ (Φ x) = x :=
      ⟨{x | Ψ (Φ x) = x}, hleft, fun x hx => hx⟩
    refine ⟨W', hW', fun z hz w hwW hΦw => ?_⟩
    have := hW'sub _ hwW
    rw [hΦw] at this

    show w = (Ψ (z, c z)).2
    rw [this]

theorem norm_sum_smul_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (u : ι → X) : ‖∑ i, θ i • u i‖ ≤ (∑ i, ‖u i‖) * ‖θ‖ := by
  calc ‖∑ i, θ i • u i‖ ≤ ∑ i, ‖θ i • u i‖ := norm_sum_le _ _
    _ = ∑ i, |θ i| * ‖u i‖ := by simp [norm_smul]
    _ ≤ ∑ i, ‖θ‖ * ‖u i‖ := by
        gcongr with i
        exact norm_le_pi_norm θ i
    _ = (∑ i, ‖u i‖) * ‖θ‖ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem basis_persists {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {ι : Type*} [Fintype ι]
    (K : ℂ → Set X) (hKsub : ∀ z (x y : X), x ∈ K z → y ∈ K z → x - y ∈ K z)
    (z₀ : ℂ) (b : Module.Basis ι ℝ X) (hK₀ : K z₀ = (Submodule.span ℤ (Set.range b) : Set X))
    (v : ι → ℂ → X) (hv₀ : ∀ i, v i z₀ = b i) (hvc : ∀ i, ContinuousAt (v i) z₀)
    (ρ₁ : ℝ) (hρ₁ : 0 < ρ₁) (hKz : ∀ z ∈ ball z₀ ρ₁, ∀ n : ι → ℤ, (∑ i, (n i : ℝ) • v i z) ∈ K z)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (hdisc : ∀ z ∈ ball z₀ ρ₀, ∀ x ∈ K z, ‖x‖ < ρ₀ → x = 0)
    (hKCL : ∀ S : Set X, IsCompact S → S ∩ K z₀ = ∅ → ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball z₀ δ, ∀ x ∈ K z, x ∉ S) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ ball z₀ ρ, ∀ x ∈ K z, ∃! n : ι → ℤ, (∑ i, (n i : ℝ) • v i z) = x := by
  classical

  set T : ℂ → (ι → ℝ) →ₗ[ℝ] X := fun z => Fintype.linearCombination ℝ (fun i => v i z) with hT
  have hTapp : ∀ z (θ : ι → ℝ), T z θ = ∑ i, θ i • v i z := fun z θ => Fintype.linearCombination_apply _ _ _
  have hT₀ : ∀ θ : ι → ℝ, T z₀ θ = ∑ i, θ i • b i := fun θ => by rw [hTapp]; simp only [hv₀]
  have hker : LinearMap.ker (T z₀) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro θ hθ
    rw [hT₀] at hθ
    funext l
    exact Fintype.linearIndependent_iff.mp b.linearIndependent θ hθ l
  obtain ⟨A₀, hA0, hA⟩ := (T z₀).exists_antilipschitzWith hker
  set A : ℝ := (A₀ : ℝ) with hAdef
  have hApos : (0 : ℝ) < A := by rw [hAdef]; exact_mod_cast hA0
  have hAθ : ∀ θ : ι → ℝ, ‖θ‖ ≤ A * ‖T z₀ θ‖ := by
    intro θ
    have h := hA.le_mul_dist θ 0
    rwa [dist_zero_right, map_zero, dist_zero_right] at h

  set C : ℝ := (Fintype.card ι : ℝ) + 1 with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  set ε₁ : ℝ := (4 * A)⁻¹ / C with hε₁
  have hε₁pos : 0 < ε₁ := by rw [hε₁]; positivity
  have hnear : ∀ i, ∀ᶠ z in 𝓝 z₀, ‖v i z - b i‖ < ε₁ := by
    intro i
    filter_upwards [Metric.tendsto_nhds.mp (hvc i) ε₁ hε₁pos] with z hz
    rwa [dist_eq_norm, hv₀ i] at hz
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Metric.eventually_nhds_iff_ball.mp (Filter.eventually_all.mpr hnear)
  have hcoef : (Fintype.card ι : ℝ) * ε₁ ≤ (4 * A)⁻¹ := by
    rw [hε₁, mul_div_assoc', div_le_iff₀ hCpos, mul_comm]
    gcongr
    rw [hC]; linarith
  have hpert : ∀ z ∈ ball z₀ ρ₂, ∀ θ : ι → ℝ, ‖T z θ - T z₀ θ‖ ≤ ‖θ‖ / (4 * A) := by
    intro z hz θ
    rw [hTapp, hT₀, ← Finset.sum_sub_distrib]
    simp_rw [← smul_sub]
    calc ‖∑ i, θ i • (v i z - b i)‖ ≤ (∑ i, ‖v i z - b i‖) * ‖θ‖ := norm_sum_smul_le θ _
      _ ≤ (∑ _i : ι, ε₁) * ‖θ‖ := by
          gcongr with i
          exact (hρ₂sub z hz i).le
      _ = (Fintype.card ι : ℝ) * ε₁ * ‖θ‖ := by simp [Finset.sum_const, Finset.card_univ]
      _ ≤ (4 * A)⁻¹ * ‖θ‖ := by gcongr
      _ = ‖θ‖ / (4 * A) := by rw [div_eq_inv_mul]

  have hanti : ∀ z ∈ ball z₀ ρ₂, ∀ θ : ι → ℝ, ‖θ‖ ≤ 2 * A * ‖T z θ‖ := by
    intro z hz θ
    have h2 := hpert z hz θ
    have h3 : ‖T z₀ θ‖ ≤ ‖T z θ‖ + ‖θ‖ / (4 * A) := by
      calc ‖T z₀ θ‖ = ‖T z θ - (T z θ - T z₀ θ)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖T z θ‖ + ‖T z θ - T z₀ θ‖ := norm_sub_le _ _
        _ ≤ ‖T z θ‖ + ‖θ‖ / (4 * A) := by linarith
    have h4 : ‖θ‖ ≤ A * ‖T z θ‖ + ‖θ‖ / 4 := by
      calc ‖θ‖ ≤ A * ‖T z₀ θ‖ := hAθ θ
        _ ≤ A * (‖T z θ‖ + ‖θ‖ / (4 * A)) := by gcongr
        _ = A * ‖T z θ‖ + ‖θ‖ / 4 := by field_simp
    nlinarith [norm_nonneg (T z θ), hApos.le, norm_nonneg θ]
  have hinj : ∀ z ∈ ball z₀ ρ₂, Function.Injective (T z) := by
    intro z hz θ θ' h
    have := hanti z hz (θ - θ')
    rw [map_sub, h, sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hfin : Module.finrank ℝ (ι → ℝ) = Module.finrank ℝ X := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_basis b]
  have hsurj : ∀ z ∈ ball z₀ ρ₂, Function.Surjective (T z) := fun z hz =>
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp (hinj z hz)

  set S : Set X := (T z₀) '' (closedBall 0 (3 / 4)) ∩ {x | ρ₀ / 2 ≤ ‖x‖} with hS
  have hSc : IsCompact S :=
    ((isCompact_closedBall (0 : ι → ℝ) (3 / 4)).image (T z₀).continuous_of_finiteDimensional).inter_right
      (isClosed_le continuous_const continuous_norm)
  have hS0 : S ∩ K z₀ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨⟨φ, hφ, rfl⟩, hxρ⟩, hxK⟩
    rw [hK₀, SetLike.mem_coe] at hxK
    obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hxK
    have hφn : φ = fun i => (n i : ℝ) := by
      apply hinj z₀ (mem_ball_self hρ₂)
      rw [← hn, hT₀]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact (Int.cast_smul_eq_zsmul ℝ (n i) (b i)).symm
    rw [mem_closedBall, dist_zero_right] at hφ
    have hn0 : ∀ i, n i = 0 := by
      intro i
      have h1 : |(n i : ℝ)| ≤ 3 / 4 := by
        have := norm_le_pi_norm φ i
        rw [hφn, Real.norm_eq_abs] at this
        rw [hφn] at hφ
        exact this.trans hφ
      have h2 : |n i| < 1 := by
        have : |(n i : ℝ)| < 1 := h1.trans_lt (by norm_num)
        exact_mod_cast this
      exact Int.abs_lt_one_iff.mp h2
    have hx0 : T z₀ φ = 0 := by
      rw [hφn, hT₀]
      simp [hn0]
    have : (ρ₀ / 2 : ℝ) ≤ ‖T z₀ φ‖ := hxρ
    rw [hx0, norm_zero] at this
    linarith
  obtain ⟨δ, hδ, hδK⟩ := hKCL S hSc hS0
  refine ⟨min (min δ ρ₂) (min ρ₀ ρ₁), by positivity, ?_⟩
  intro z hz x hx
  have hzδ : z ∈ ball z₀ δ := ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hz
  have hzρ₂ : z ∈ ball z₀ ρ₂ := ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hz
  have hzρ₀ : z ∈ ball z₀ ρ₀ := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hz
  have hzρ₁ : z ∈ ball z₀ ρ₁ := ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hz
  obtain ⟨θ, hθ⟩ := hsurj z hzρ₂ x
  set m : ι → ℤ := fun i => round (θ i) with hm
  set φ : ι → ℝ := fun i => θ i - (m i : ℝ) with hφdef
  have hφle : ‖φ‖ ≤ 1 / 2 := by
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    exact abs_sub_round (θ i)
  have hφθ : φ = θ - fun i => (m i : ℝ) := rfl
  have hTm : T z (fun i => (m i : ℝ)) = ∑ i, (m i : ℝ) • v i z := hTapp z _
  have hy : T z φ = x - ∑ i, (m i : ℝ) • v i z := by
    rw [hφθ, map_sub, hθ, hTm]
  have hyK : T z φ ∈ K z := by
    rw [hy]; exact hKsub z x _ hx (hKz z hzρ₁ m)
  have hy0 : T z φ = 0 := by
    by_contra hne
    have hyρ : ρ₀ ≤ ‖T z φ‖ := by
      by_contra h
      push_neg at h
      exact hne (hdisc z hzρ₀ _ hyK h)
    apply hδK z hzδ _ hyK
    refine ⟨?_, show ρ₀ / 2 ≤ ‖T z φ‖ by linarith⟩
    obtain ⟨φ', hφ'⟩ := hsurj z₀ (mem_ball_self hρ₂) (T z φ)
    refine ⟨φ', ?_, hφ'⟩
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖φ' - φ‖ ≤ 1 / 8 := by
      calc ‖φ' - φ‖ ≤ A * ‖T z₀ (φ' - φ)‖ := hAθ _
        _ = A * ‖T z φ - T z₀ φ‖ := by rw [map_sub, hφ']
        _ ≤ A * (‖φ‖ / (4 * A)) := by gcongr; exact hpert z hzρ₂ φ
        _ = ‖φ‖ / 4 := by field_simp
        _ ≤ 1 / 8 := by linarith
    calc ‖φ'‖ = ‖φ + (φ' - φ)‖ := by rw [add_sub_cancel]
      _ ≤ ‖φ‖ + ‖φ' - φ‖ := norm_add_le _ _
      _ ≤ 3 / 4 := by linarith
  have hxm : (∑ i, (m i : ℝ) • v i z) = x := by
    have := hy
    rw [hy0] at this
    exact (sub_eq_zero.mp this.symm).symm
  refine ⟨m, hxm, fun n hn => ?_⟩
  have h1 : T z (fun i => (n i : ℝ)) = T z (fun i => (m i : ℝ)) := by
    rw [hTapp, hTapp, hn, hxm]
  have h2 := hinj z hzρ₂ h1
  funext i
  exact_mod_cast congrFun h2 i

theorem compact_avoid_of_pointwise {X : Type*} [MetricSpace X] (K : ℂ → Set X) (z₀ : ℂ)
    (hcl : ∀ x, x ∉ K z₀ → ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball z₀ δ, ∀ y ∈ K z, δ ≤ dist y x)
    (S : Set X) (hS : IsCompact S) (hSK : S ∩ K z₀ = ∅) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball z₀ δ, ∀ x ∈ K z, x ∉ S := by
  classical
  have hnot : ∀ x ∈ S, x ∉ K z₀ := fun x hx hxK => by
    have : x ∈ S ∩ K z₀ := ⟨hx, hxK⟩
    rw [hSK] at this; exact this
  choose δ hδ hδfar using fun x (hx : x ∈ S) => hcl x (hnot x hx)

  obtain ⟨t, hSsub⟩ := hS.elim_nhds_subcover' (fun x hx => ball x (δ x hx / 2))
    (fun x hx => ball_mem_nhds x (by linarith [hδ x hx]))
  by_cases ht : t = ∅
  ·
    refine ⟨1, one_pos, fun z _ x hx hxS => ?_⟩
    have := hSsub hxS
    rw [ht] at this
    simp at this
  · have htne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr ht
    set δ₀ : ℝ := t.inf' htne (fun x => δ x.1 x.2) with hδ₀
    have hδ₀pos : 0 < δ₀ := by
      rw [hδ₀, Finset.lt_inf'_iff]
      intro x _; exact hδ x.1 x.2
    have hδ₀le : ∀ x ∈ t, δ₀ ≤ δ x.1 x.2 := fun x hx => Finset.inf'_le _ hx
    refine ⟨δ₀, hδ₀pos, fun z hz y hy hyS => ?_⟩
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (hSsub hyS)
    have hzx : z ∈ ball z₀ (δ x.1 x.2) := ball_subset_ball (hδ₀le x hxt) hz
    have hfar := hδfar x.1 x.2 z hzx y hy
    rw [mem_ball] at hyx
    linarith [hδ x.1 x.2]

end RelKerFrame

namespace RelKerAsm

theorem mono_of_isPullback_spec {Sc : Type} [CommRing Sc] [Algebra ℂ Sc] {X Y : Scheme.{0}}
    (g : X ⟶ Y) (fX : X ⟶ Spec (CommRingCat.of ℂ)) (fY : Y ⟶ Spec (CommRingCat.of Sc)) (σ : Sc →ₐ[ℂ] ℂ)
    (h : IsPullback g fX fY (Spec.map (CommRingCat.ofHom σ.toRingHom))) : Mono g := by
  have hsurj : Function.Surjective (CommRingCat.ofHom σ.toRingHom) := fun c => ⟨algebraMap ℂ Sc c, σ.commutes c⟩
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom σ.toRingHom)) := IsClosedImmersion.spec_of_surjective _ hsurj
  have := Limits.PullbackCone.mono_fst_of_is_pullback_of_mono h.isLimit
  simp at this
  exact this

theorem val_congr {A : Scheme.{0}} (V : A.Opens) (f : Γ(A, V)) {M M' : Spec (CommRingCat.of ℂ) ⟶ A} (h : M = M')
    (hV : ⊤ ≤ M ⁻¹ᵁ V) (hV' : ⊤ ≤ M' ⁻¹ᵁ V) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((M.appLE V ⊤ hV) f) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((M'.appLE V ⊤ hV') f) := by
  subst h; rfl

theorem differentiableOn_vec2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {F G : E → ℂ} {s : Set E}
    (hF : DifferentiableOn ℂ F s) (hG : DifferentiableOn ℂ G s) :
    DifferentiableOn ℂ (fun p => (![F p, G p] : Fin 2 → ℂ)) s := by
  refine differentiableOn_pi.mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · simpa using hF
  · simpa using hG

theorem vec2_eq_iff (a b c d : ℂ) : (![a, b] : Fin 2 → ℂ) = ![c, d] ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem ker_eq_span (L : Submodule ℤ (Fin 2 → ℂ)) (b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ))
    (hL : L = Submodule.span ℤ (Set.range b₀)) (c : ℂ) (hc : c ≠ 0) :
    ∃ b : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), (∀ i, b i = c⁻¹ • b₀ i) ∧
      {w : Fin 2 → ℂ | c • w ∈ L} = (Submodule.span ℤ (Set.range b) : Set (Fin 2 → ℂ)) := by
  let e : (Fin 2 → ℂ) ≃ₗ[ℝ] (Fin 2 → ℂ) :=
    (LinearEquiv.smulOfUnit (Units.mk0 c⁻¹ (inv_ne_zero hc))).restrictScalars ℝ
  have he : ∀ w, e w = c⁻¹ • w := fun w => rfl
  refine ⟨b₀.map e, fun i => by simp [he], ?_⟩
  ext w
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  have hrange : Set.range (b₀.map e) = (fun w => c⁻¹ • w) '' Set.range b₀ := by
    rw [← Set.range_comp]; rfl

  let φ : (Fin 2 → ℂ) →ₗ[ℤ] (Fin 2 → ℂ) := (e.toLinearMap.restrictScalars ℤ)
  have hφ : ∀ w, φ w = c⁻¹ • w := fun w => rfl
  have hspan : Submodule.span ℤ (Set.range (b₀.map e)) = (Submodule.span ℤ (Set.range b₀)).map φ := by
    rw [hrange, Submodule.map_span]; rfl
  rw [hspan, hL, Submodule.mem_map]
  constructor
  · intro h
    exact ⟨c • w, h, by rw [hφ, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
  · rintro ⟨y, hy, rfl⟩
    rw [hφ, smul_smul, mul_inv_cancel₀ hc, one_smul]; exact hy

end RelKerAsm

namespace RelKerAsm

local notation "P2" => ℂ × (Fin 2 → ℂ)

theorem mem_ball_prod_zero {z z₀ : ℂ} {δ : ℝ} (hz : z ∈ ball z₀ δ) (w₀ : Fin 2 → ℂ) :
    ((z, w₀) : P2) ∈ ball ((z₀, w₀) : P2) δ := by
  rw [mem_ball, Prod.dist_eq, dist_self, max_eq_left dist_nonneg]; exact hz

theorem chart_branch {T : Type*} (Pm : ℂ → (Fin 2 → ℂ) → T) (z₀ : ℂ) (w₁ : Fin 2 → ℂ)
    (Dom : Set P2) (hDom : IsOpen Dom) (F₂ F₃ : P2 → ℂ) (hF₂ : DifferentiableOn ℂ F₂ Dom) (hF₃ : DifferentiableOn ℂ F₃ Dom)
    (δ : ℝ) (hδ : 0 < δ) (hb₁ : ball ((z₀, w₁) : P2) δ ⊆ Dom) (hb₂ : ball ((z₀, (0 : Fin 2 → ℂ)) : P2) δ ⊆ Dom)
    (Φ : P2 → P2) (hΦ₁ : ∀ p ∈ ball ((z₀, w₁) : P2) δ, Φ p = (p.1, ![F₂ p, F₃ p]))
    (hΦ₂ : ∀ p ∈ ball ((z₀, (0 : Fin 2 → ℂ)) : P2) δ, Φ p = (p.1, ![F₂ p, F₃ p]))
    (D : P2 ≃L[ℂ] P2) (hD : HasFDerivAt Φ (D : P2 →L[ℂ] P2) (z₀, w₁))
    (hval : ∀ p q : P2, p ∈ Dom → q ∈ Dom → p.1 = q.1 → Pm p.1 p.2 = Pm q.1 q.2 → F₂ p = F₂ q ∧ F₃ p = F₃ q)
    (hsep : ∀ p ∈ ball ((z₀, w₁) : P2) δ, ∀ q ∈ ball ((z₀, (0 : Fin 2 → ℂ)) : P2) δ, p.1 = q.1 →
      F₂ p = F₂ q → F₃ p = F₃ q → Pm p.1 p.2 = Pm q.1 q.2)
    (h₀ : Pm z₀ w₁ = Pm z₀ 0) :
    ∃ (ρ : ℝ) (v : ℂ → (Fin 2 → ℂ)), 0 < ρ ∧ v z₀ = w₁ ∧ DifferentiableOn ℂ v (ball z₀ ρ) ∧
      ∀ z ∈ ball z₀ ρ, Pm z (v z) = Pm z 0 := by
  set U : Set P2 := ball ((z₀, w₁) : P2) δ with hU
  have hG : DifferentiableOn ℂ (fun p : P2 => ((p.1, ![F₂ p, F₃ p]) : P2)) Dom :=
    differentiableOn_fst.prodMk (differentiableOn_vec2 hF₂ hF₃)
  have hΦd : DifferentiableOn ℂ Φ U := (hG.mono hb₁).congr fun p hp => hΦ₁ p hp
  set c : ℂ → (Fin 2 → ℂ) := fun z => ![F₂ (z, 0), F₃ (z, 0)] with hc
  have hcd : DifferentiableOn ℂ c (ball z₀ δ) := by
    have hι : DifferentiableOn ℂ (fun z : ℂ => ((z, (0 : Fin 2 → ℂ)) : P2)) (ball z₀ δ) :=
      differentiableOn_id.prodMk (differentiableOn_const _)
    have hmaps : Set.MapsTo (fun z : ℂ => ((z, (0 : Fin 2 → ℂ)) : P2)) (ball z₀ δ) Dom :=
      fun z hz => hb₂ (mem_ball_prod_zero hz 0)
    exact differentiableOn_vec2 (hF₂.comp hι hmaps) (hF₃.comp hι hmaps)
  have hp₁ : ((z₀, w₁) : P2) ∈ U := mem_ball_self hδ
  have hq₀ : ((z₀, (0 : Fin 2 → ℂ)) : P2) ∈ ball ((z₀, (0 : Fin 2 → ℂ)) : P2) δ := mem_ball_self hδ
  have hc₀ : Φ (z₀, w₁) = (z₀, c z₀) := by
    rw [hΦ₁ _ hp₁]
    obtain ⟨h2, h3⟩ := hval (z₀, w₁) (z₀, 0) (hb₁ hp₁) (hb₂ hq₀) rfl h₀
    simp only [hc, h2, h3]
  obtain ⟨ρ, v, hρ, hρδ, hv₀, hvd, hveq, -⟩ :=
    RelKerFrame.exists_branch Φ U isOpen_ball hΦd z₀ w₁ hp₁ (fun p hp => by rw [hΦ₁ p hp]) D hD c δ hδ hcd hc₀ U
      (isOpen_ball.mem_nhds hp₁)
  refine ⟨ρ, v, hρ, hv₀, hvd, fun z hz => ?_⟩
  obtain ⟨hmem, heq⟩ := hveq z hz
  have hzδ : z ∈ ball z₀ δ := ball_subset_ball hρδ hz
  have hq : ((z, (0 : Fin 2 → ℂ)) : P2) ∈ ball ((z₀, (0 : Fin 2 → ℂ)) : P2) δ := mem_ball_prod_zero hzδ 0
  have h1 : (![F₂ (z, v z), F₃ (z, v z)] : Fin 2 → ℂ) = ![F₂ (z, 0), F₃ (z, 0)] := by
    have := heq
    rw [hΦ₁ _ hmem] at this
    simpa [hc] using congrArg Prod.snd this
  obtain ⟨h2, h3⟩ := (vec2_eq_iff _ _ _ _).mp h1
  exact hsep (z, v z) hmem (z, 0) hq rfl h2 h3

theorem chart_disc {T : Type*} (Pm : ℂ → (Fin 2 → ℂ) → T) (z₀ : ℂ)
    (Dom : Set P2) (hDom : IsOpen Dom) (F₂ F₃ : P2 → ℂ) (hF₂ : DifferentiableOn ℂ F₂ Dom) (hF₃ : DifferentiableOn ℂ F₃ Dom)
    (δ : ℝ) (hδ : 0 < δ) (hb : ball ((z₀, (0 : Fin 2 → ℂ)) : P2) δ ⊆ Dom)
    (Φ : P2 → P2) (hΦ : ∀ p ∈ ball ((z₀, (0 : Fin 2 → ℂ)) : P2) δ, Φ p = (p.1, ![F₂ p, F₃ p]))
    (D : P2 ≃L[ℂ] P2) (hD : HasFDerivAt Φ (D : P2 →L[ℂ] P2) (z₀, 0))
    (hval : ∀ p q : P2, p ∈ Dom → q ∈ Dom → p.1 = q.1 → Pm p.1 p.2 = Pm q.1 q.2 → F₂ p = F₂ q ∧ F₃ p = F₃ q) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ z ∈ ball z₀ ρ₀, ∀ w : Fin 2 → ℂ, ‖w‖ < ρ₀ → Pm z w = Pm z 0 → w = 0 := by
  set U : Set P2 := ball ((z₀, (0 : Fin 2 → ℂ)) : P2) δ with hU
  have hG : DifferentiableOn ℂ (fun p : P2 => ((p.1, ![F₂ p, F₃ p]) : P2)) Dom :=
    differentiableOn_fst.prodMk (differentiableOn_vec2 hF₂ hF₃)
  have hΦd : DifferentiableOn ℂ Φ U := (hG.mono hb).congr fun p hp => hΦ p hp
  set c : ℂ → (Fin 2 → ℂ) := fun z => ![F₂ (z, 0), F₃ (z, 0)] with hc
  have hcd : DifferentiableOn ℂ c (ball z₀ δ) := by
    have hι : DifferentiableOn ℂ (fun z : ℂ => ((z, (0 : Fin 2 → ℂ)) : P2)) (ball z₀ δ) :=
      differentiableOn_id.prodMk (differentiableOn_const _)
    have hmaps : Set.MapsTo (fun z : ℂ => ((z, (0 : Fin 2 → ℂ)) : P2)) (ball z₀ δ) Dom :=
      fun z hz => hb (mem_ball_prod_zero hz 0)
    exact differentiableOn_vec2 (hF₂.comp hι hmaps) (hF₃.comp hι hmaps)
  have hp₀ : ((z₀, (0 : Fin 2 → ℂ)) : P2) ∈ U := mem_ball_self hδ
  have hc₀ : Φ (z₀, 0) = (z₀, c z₀) := by rw [hΦ _ hp₀]
  obtain ⟨ρ, v, hρ, hρδ, hv₀, -, hveq, W', hW', huniq⟩ :=
    RelKerFrame.exists_branch Φ U isOpen_ball hΦd z₀ 0 hp₀ (fun p hp => by rw [hΦ p hp]) D hD c δ hδ hcd hc₀ U
      (isOpen_ball.mem_nhds hp₀)

  obtain ⟨τ, hτ, hτsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hW' (isOpen_ball.mem_nhds hp₀))
  set ρ₀ : ℝ := min τ ρ with hρ₀
  refine ⟨ρ₀, lt_min hτ hρ, fun z hz w hw hker => ?_⟩
  have hzρ : z ∈ ball z₀ ρ := ball_subset_ball (min_le_right _ _) hz
  have hzτ : dist z z₀ < τ := lt_of_lt_of_le (mem_ball.mp hz) (min_le_left _ _)
  have hwτ : ‖w‖ < τ := lt_of_lt_of_le hw (min_le_left _ _)
  have hmem : ∀ u : Fin 2 → ℂ, ‖u‖ < τ → ((z, u) : P2) ∈ W' ∩ U := by
    intro u hu
    apply hτsub
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hzτ, by rwa [dist_zero_right]⟩
  have h0 : (0 : Fin 2 → ℂ) = v z :=
    huniq z hzρ 0 (hmem 0 (by simpa using hτ)).1 (by rw [hΦ _ (hmem 0 (by simpa using hτ)).2])
  have hw' : w = v z := by
    refine huniq z hzρ w (hmem w hwτ).1 ?_
    rw [hΦ _ (hmem w hwτ).2]
    obtain ⟨h2, h3⟩ := hval (z, w) (z, 0) (hb (hmem w hwτ).2) (hb (hmem 0 (by simpa using hτ)).2) rfl hker
    simp only [hc, h2, h3]
  rw [hw', ← h0]

end RelKerAsm

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)

    (latt : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (e : ∀ E : FakeEllipticCurve Λ N ℂ,
      SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))

    (hL1 : ∀ E : FakeEllipticCurve Λ N ℂ,
        (∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), latt E = Submodule.span ℤ (Set.range b₀)) ∧
        (∀ x ∈ Λ, ∀ v ∈ latt E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ latt E))

    (hE1 : ∀ (E : FakeEllipticCurve Λ N ℂ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
        e E (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e E P + e E Q)

    (hE2 : ∀ (E : FakeEllipticCurve Λ N ℂ) (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
        e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
        e E (pushPt (E.act x) (E.act_over x) P) =
          ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))

    (hH1 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) →
        ∃ c : ℂ, (∀ v ∈ latt E, c • v ∈ latt E') ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))

    (hH2 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (c : ℂ), (∀ v ∈ latt E, c • v ∈ latt E') →
        ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
            mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
          (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))

    (hH3 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ ψ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E'.f = E.f),
        (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, mapPt φ hφ P = mapPt ψ hψ P) → φ = ψ)

    (hAN : ∀ (E : FakeEllipticCurve Λ N ℂ) (U : E.A.Opens) (f : Γ(E.A, U)),
        IsOpen {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∃ F : (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
          ∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
              ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f))

    (hCOV : ∀ (E : FakeEllipticCurve Λ N ℂ) (v₀ : Fin 2 → ℂ),
        ∃ (U : E.A.Opens) (f₁ f₂ : Γ(E.A, U)) (ε : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
          (F : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
          0 < ε ∧
          (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U) ∧
          (∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            v ∈ Metric.ball v₀ ε →
            F v = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₁),
                    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₂)]) ∧
          HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀)

    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))

    (𝒜 : FakeEllipticCurve Λ N Sc)
    (E : ℂ → FakeEllipticCurve Λ N ℂ) (g : ∀ z : ℂ, (E z).A ⟶ 𝒜.A)
    (hg : ∀ σ ∈ 𝒰,
      ∃ hc : CategoryTheory.IsPullback (g (σ t)) (E (σ t)).f 𝒜.f (Spec.map (CommRingCat.ofHom σ.toRingHom)),

        (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (E (σ t)).f),
          ((E (σ t)).L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q).1 ≫ g (σ t) =
            (𝒜.L.mul (𝟙 (Spec (CommRingCat.of ℂ)) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
              ⟨P.1 ≫ g (σ t), by rw [Category.assoc, hc.w, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ g (σ t), by rw [Category.assoc, hc.w, ← Category.assoc, Q.2]⟩).1) ∧

        (∀ x : ↥Λ, (E (σ t)).act x ≫ g (σ t) = g (σ t) ≫ 𝒜.act x))

    (ε : ℝ) (κ : ℂ → ℂ) (hε : 0 < ε) (hεr : ε ≤ r) (hκ : ∀ z ∈ Metric.ball (σ₀ t) ε, κ z ≠ 0)
    (hRELAN :
      (∀ (V : 𝒜.A.Opens) (f : Γ(𝒜.A, V)),
        IsOpen {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
          ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫
                  g (σ t)) ⁻¹ᵁ V} ∧
        ∃ F : ℂ × (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫
                    g (σ t)) ⁻¹ᵁ V} ∧
          ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε → ∀ (w : Fin 2 → ℂ)
            (hV : ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫
                    g (σ t)) ⁻¹ᵁ V),
            F (σ t, w) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
              (((((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫
                  g (σ t)).appLE V ⊤ hV) f)))
    (hRELCOV :
      (∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε → ∀ w₁ w₁' : Fin 2 → ℂ,
        (((e (E (σ₁ t))).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t)) =
          (((e (E (σ₁ t))).symm ((κ (σ₁ t) • w₁' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t)) →
        ∃ (V : 𝒜.A.Opens) (f₂ f₃ : Γ(𝒜.A, V)) (δ : ℝ)
          (D D' : (ℂ × (Fin 2 → ℂ)) ≃L[ℂ] (ℂ × (Fin 2 → ℂ))) (Φ : ℂ × (Fin 2 → ℂ) → ℂ × (Fin 2 → ℂ)),
          0 < δ ∧
          ⊤ ≤ (((e (E (σ₁ t))).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t)) ⁻¹ᵁ V ∧
          (∀ p ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ, p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V) ∧
          (∀ p ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ, p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V) ∧
          (∀ σ ∈ 𝒰, ∀ (w : Fin 2 → ℂ),
            (((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ ∨ ((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ) →
            ∀ (hV : ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V),
            Φ (σ t, w) = (σ t, ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₂),
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₃)])) ∧
          HasFDerivAt Φ (D : (ℂ × (Fin 2 → ℂ)) →L[ℂ] (ℂ × (Fin 2 → ℂ))) (σ₁ t, w₁) ∧
          HasFDerivAt Φ (D' : (ℂ × (Fin 2 → ℂ)) →L[ℂ] (ℂ × (Fin 2 → ℂ))) (σ₁ t, w₁') ∧
          (∀ σ ∈ 𝒰, ∀ (w w' : Fin 2 → ℂ),
            ((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ →
            ((σ t, w') : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ →
            ∀ (hV : ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V)
              (hV' : ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V),
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₂) =
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (E (σ t))).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV') f₂) →
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₃) =
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (E (σ t))).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV') f₃) →
              (((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) =
                (((e (E (σ t))).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)))))
    (hKCL :
      (∀ w : Fin 2 → ℂ, κ (σ₀ t) • w ∉ latt (E (σ₀ t)) →
        ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Metric.ball (σ₀ t) δ, ∀ w' : Fin 2 → ℂ,
          κ z • w' ∈ latt (E z) → δ ≤ ‖w' - w‖)) :
    ∃ (ε' : ℝ) (v : Fin 4 → ℂ → (Fin 2 → ℂ)), 0 < ε' ∧ ε' ≤ ε ∧
      (∀ i : Fin 4, DifferentiableOn ℂ (v i) (Metric.ball (σ₀ t) ε')) ∧
      ∀ z ∈ Metric.ball (σ₀ t) ε',
        (∀ i : Fin 4, κ z • v i z ∈ latt (E z)) ∧
        ∀ x ∈ latt (E z), ∃! n : Fin 4 → ℤ, (∑ i, (n i : ℂ) • v i z) = (κ z)⁻¹ • x  := by
  classical

  have hsurj : ∀ z ∈ ball (σ₀ t) r, ∃ σ ∈ 𝒰, σ t = z := fun z hz => hbij.surjOn hz
  have hinj : ∀ σ ∈ 𝒰, ∀ σ' ∈ 𝒰, σ t = σ' t → σ = σ' := fun σ hσ σ' hσ' h => hbij.injOn hσ hσ' h
  have hz₀ε : σ₀ t ∈ ball (σ₀ t) ε := mem_ball_self hε

  set Pm : ℂ → (Fin 2 → ℂ) → (Spec (CommRingCat.of ℂ) ⟶ 𝒜.A) :=
    fun z w => ((e (E z)).symm ((κ z • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E z)).toAddSubgroup)).1 ≫ g z with hPm

  have hfwd : ∀ (z : ℂ) (w w' : Fin 2 → ℂ), κ z • w - κ z • w' ∈ latt (E z) → Pm z w = Pm z w' := by
    intro z w w' h
    have hq : ((κ z • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E z)).toAddSubgroup) =
        ((κ z • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E z)).toAddSubgroup) :=
      (QuotientAddGroup.eq_iff_sub_mem).mpr h
    simp only [hPm, hq]

  have hbwd : ∀ σ ∈ 𝒰, ∀ (w w' : Fin 2 → ℂ), Pm (σ t) w = Pm (σ t) w' → κ (σ t) • w - κ (σ t) • w' ∈ latt (E (σ t)) := by
    intro σ hσ w w' h
    obtain ⟨hc, -, -⟩ := hg σ hσ
    haveI := RelKerAsm.mono_of_isPullback_spec _ _ _ σ hc
    have h1 : ((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 =
        ((e (E (σ t))).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 := by
      rw [← cancel_mono (g (σ t))]; exact h
    have h2 := (e (E (σ t))).symm.injective (Subtype.ext h1)
    exact (QuotientAddGroup.eq_iff_sub_mem).mp h2

  set Dom : 𝒜.A.Opens → Set (ℂ × (Fin 2 → ℂ)) := fun V =>
    {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
      ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫
        g (σ t)) ⁻¹ᵁ V} with hDom
  have hDomOpen : ∀ V : 𝒜.A.Opens, IsOpen (Dom V) := by
    intro V
    have := (hRELAN V 0).1
    exact this

  have hFpack : ∀ (V : 𝒜.A.Opens) (f : Γ(𝒜.A, V)), ∃ F : ℂ × (Fin 2 → ℂ) → ℂ,
      DifferentiableOn ℂ F (Dom V) ∧
      (∀ σ ∈ 𝒰, ∀ (w : Fin 2 → ℂ) (hV : ⊤ ≤ (Pm (σ t) w) ⁻¹ᵁ V), ((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Dom V →
        F (σ t, w) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pm (σ t) w).appLE V ⊤ hV) f)) ∧
      (∀ p q : ℂ × (Fin 2 → ℂ), p ∈ Dom V → q ∈ Dom V → p.1 = q.1 → Pm p.1 p.2 = Pm q.1 q.2 → F p = F q) := by
    intro V f
    obtain ⟨-, F, hFd, hFeq⟩ := hRELAN V f
    refine ⟨F, hFd, fun σ hσ w hV hmem => hFeq σ hσ hmem.1 w hV, ?_⟩
    rintro ⟨z, w⟩ ⟨z', w'⟩ ⟨hz, σ, hσ, hσt, hV⟩ ⟨hz', σ', hσ', hσ't, hV'⟩ hzz hP
    simp only at hzz hσt hσ't hV hV' hP
    subst hzz; subst hσt
    have hσσ : σ = σ' := hinj σ hσ σ' hσ' hσ't.symm
    subst hσσ
    rw [hFeq σ hσ hz w hV, hFeq σ hσ hz w' hV']
    exact RelKerAsm.val_congr V f hP hV hV'

  obtain ⟨b₀, hb₀⟩ := (hL1 (E (σ₀ t))).1
  obtain ⟨b, hb, hKb⟩ := RelKerAsm.ker_eq_span (latt (E (σ₀ t))) b₀ hb₀ (κ (σ₀ t)) (hκ _ hz₀ε)
  have hbK : ∀ i, κ (σ₀ t) • b i ∈ latt (E (σ₀ t)) := by
    intro i
    have : b i ∈ {w : Fin 2 → ℂ | κ (σ₀ t) • w ∈ latt (E (σ₀ t))} := by
      rw [hKb]; exact Submodule.subset_span (Set.mem_range_self i)
    exact this

  have hbr : ∀ i : Fin 4, ∃ (ρ : ℝ) (v : ℂ → (Fin 2 → ℂ)), 0 < ρ ∧ v (σ₀ t) = b i ∧
      DifferentiableOn ℂ v (ball (σ₀ t) ρ) ∧ ∀ z ∈ ball (σ₀ t) ρ, Pm z (v z) = Pm z 0 := by
    intro i
    have h₀ : Pm (σ₀ t) (b i) = Pm (σ₀ t) 0 := hfwd _ _ _ (by rw [smul_zero, sub_zero]; exact hbK i)
    obtain ⟨V, f₂, f₃, δ, D, D', Φ, hδ, -, hball₁, hball₂, hΦ, hD, -, hsep⟩ :=
      hRELCOV σ₀ hσ₀ hz₀ε (b i) 0 h₀
    obtain ⟨F₂, hF₂d, hF₂eq, hF₂val⟩ := hFpack V f₂
    obtain ⟨F₃, hF₃d, hF₃eq, hF₃val⟩ := hFpack V f₃
    have hb₁ : ball ((σ₀ t, b i) : ℂ × (Fin 2 → ℂ)) δ ⊆ Dom V := fun p hp => hball₁ p hp
    have hb₂ : ball ((σ₀ t, (0 : Fin 2 → ℂ)) : ℂ × (Fin 2 → ℂ)) δ ⊆ Dom V := fun p hp => hball₂ p hp
    have hΦeq : ∀ p : ℂ × (Fin 2 → ℂ),
        (p ∈ ball ((σ₀ t, b i) : ℂ × (Fin 2 → ℂ)) δ ∨ p ∈ ball ((σ₀ t, (0 : Fin 2 → ℂ)) : ℂ × (Fin 2 → ℂ)) δ) →
        p ∈ Dom V → Φ p = (p.1, ![F₂ p, F₃ p]) := by
      rintro ⟨z, w⟩ hp ⟨hz, σ, hσ, hσt, hV⟩
      simp only at hσt hV
      subst hσt
      rw [hΦ σ hσ w hp hV, hF₂eq σ hσ w hV ⟨hz, σ, hσ, rfl, hV⟩, hF₃eq σ hσ w hV ⟨hz, σ, hσ, rfl, hV⟩]
    obtain ⟨ρ, v, hρ, hv₀, hvd, hvker⟩ := RelKerAsm.chart_branch Pm (σ₀ t) (b i) (Dom V) (hDomOpen V) F₂ F₃ hF₂d hF₃d
      δ hδ hb₁ hb₂ Φ (fun p hp => hΦeq p (Or.inl hp) (hb₁ hp)) (fun p hp => hΦeq p (Or.inr hp) (hb₂ hp)) D hD
      (fun p q hp hq h1 hP => ⟨hF₂val p q hp hq h1 hP, hF₃val p q hp hq h1 hP⟩)
      (by
        rintro ⟨z, w⟩ hp ⟨z', w'⟩ hq hzz h2 h3
        simp only at hzz h2 h3
        subst hzz
        obtain ⟨hz, σ, hσ, hσt, hV⟩ := hb₁ hp
        obtain ⟨-, σ', hσ', hσ't, hV'⟩ := hb₂ hq
        simp only at hσt hσ't hV hV'
        subst hσt
        have hσσ : σ = σ' := hinj σ hσ σ' hσ' hσ't.symm
        subst hσσ
        refine hsep σ hσ w w' hp hq hV hV' ?_ ?_
        · rw [← hF₂eq σ hσ w hV (hb₁ hp), ← hF₂eq σ hσ w' hV' (hb₂ hq)]; exact h2
        · rw [← hF₃eq σ hσ w hV (hb₁ hp), ← hF₃eq σ hσ w' hV' (hb₂ hq)]; exact h3)
      h₀
    exact ⟨ρ, v, hρ, hv₀, hvd, hvker⟩
  choose ρv v hρv hv₀ hvd hvker using hbr

  obtain ⟨ρ₀, hρ₀, hdisc₀⟩ : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ z ∈ ball (σ₀ t) ρ₀, ∀ w : Fin 2 → ℂ, ‖w‖ < ρ₀ →
      Pm z w = Pm z 0 → w = 0 := by
    obtain ⟨V, f₂, f₃, δ, D, D', Φ, hδ, -, hball₁, -, hΦ, hD, -, -⟩ :=
      hRELCOV σ₀ hσ₀ hz₀ε 0 0 rfl
    obtain ⟨F₂, hF₂d, hF₂eq, hF₂val⟩ := hFpack V f₂
    obtain ⟨F₃, hF₃d, hF₃eq, hF₃val⟩ := hFpack V f₃
    have hb₁ : ball ((σ₀ t, (0 : Fin 2 → ℂ)) : ℂ × (Fin 2 → ℂ)) δ ⊆ Dom V := fun p hp => hball₁ p hp
    refine RelKerAsm.chart_disc Pm (σ₀ t) (Dom V) (hDomOpen V) F₂ F₃ hF₂d hF₃d δ hδ hb₁ Φ ?_ D hD
      (fun p q hp hq h1 hP => ⟨hF₂val p q hp hq h1 hP, hF₃val p q hp hq h1 hP⟩)
    rintro ⟨z, w⟩ hp
    obtain ⟨hz, σ, hσ, hσt, hV⟩ := hb₁ hp
    simp only at hσt hV
    subst hσt
    rw [hΦ σ hσ w (Or.inl hp) hV, hF₂eq σ hσ w hV (hb₁ hp), hF₃eq σ hσ w hV (hb₁ hp)]

  set K : ℂ → Set (Fin 2 → ℂ) := fun z => {w | κ z • w ∈ latt (E z)} with hK
  have hKsub : ∀ z (x y : Fin 2 → ℂ), x ∈ K z → y ∈ K z → x - y ∈ K z := by
    intro z x y hx hy
    show κ z • (x - y) ∈ latt (E z)
    rw [smul_sub]; exact Submodule.sub_mem _ hx hy
  have hK₀ : K (σ₀ t) = (Submodule.span ℤ (Set.range b) : Set (Fin 2 → ℂ)) := hKb
  set ρ₁ : ℝ := min (min (min (ρv 0) (ρv 1)) (min (ρv 2) (ρv 3))) ε with hρ₁
  have hρ₁pos : 0 < ρ₁ := by
    rw [hρ₁]; exact lt_min (lt_min (lt_min (hρv 0) (hρv 1)) (lt_min (hρv 2) (hρv 3))) hε
  have hρ₁le : ∀ i, ρ₁ ≤ ρv i := by
    intro i; rw [hρ₁]
    fin_cases i
    · exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
    · exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    · exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hρ₁ε : ρ₁ ≤ ε := min_le_right _ _
  have hvK : ∀ i, ∀ z ∈ ball (σ₀ t) ρ₁, κ z • v i z ∈ latt (E z) := by
    intro i z hz
    have hzr : z ∈ ball (σ₀ t) r := ball_subset_ball (hρ₁ε.trans hεr) hz
    obtain ⟨σ, hσ, rfl⟩ := hsurj z hzr
    have := hbwd σ hσ (v i (σ t)) 0 (hvker i (σ t) (ball_subset_ball (hρ₁le i) hz))
    rwa [smul_zero, sub_zero] at this
  have hKz : ∀ z ∈ ball (σ₀ t) ρ₁, ∀ n : Fin 4 → ℤ, (∑ i, (n i : ℝ) • v i z) ∈ K z := by
    intro z hz n
    show κ z • (∑ i, (n i : ℝ) • v i z) ∈ latt (E z)
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_comm, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (hvK i z hz)
  have hdisc : ∀ z ∈ ball (σ₀ t) ρ₀, ∀ x ∈ K z, ‖x‖ < ρ₀ → x = 0 := by
    intro z hz x hx hxn
    refine hdisc₀ z hz x hxn (hfwd z x 0 ?_)
    rw [smul_zero, sub_zero]; exact hx
  have hKCL' : ∀ S : Set (Fin 2 → ℂ), IsCompact S → S ∩ K (σ₀ t) = ∅ →
      ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball (σ₀ t) δ, ∀ x ∈ K z, x ∉ S := by
    refine RelKerFrame.compact_avoid_of_pointwise K (σ₀ t) fun x hx => ?_
    obtain ⟨δ, hδ, h⟩ := hKCL x hx
    exact ⟨δ, hδ, fun z hz y hy => by rw [dist_eq_norm]; exact h z hz y hy⟩
  obtain ⟨ρp, hρp, hpers⟩ := RelKerFrame.basis_persists K hKsub (σ₀ t) b hK₀ v hv₀
    (fun i => ((hvd i).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (hρv i)))).continuousAt)
    ρ₁ hρ₁pos hKz ρ₀ hρ₀ hdisc hKCL'

  set ε' : ℝ := min ρp ρ₁ with hε'
  refine ⟨ε', v, lt_min hρp hρ₁pos, (min_le_right _ _).trans hρ₁ε,
    fun i => (hvd i).mono (ball_subset_ball ((min_le_right _ _).trans (hρ₁le i))), fun z hz => ⟨?_, ?_⟩⟩
  · exact fun i => hvK i z (ball_subset_ball (min_le_right _ _) hz)
  · intro x hx
    have hzε : z ∈ ball (σ₀ t) ε := ball_subset_ball ((min_le_right _ _).trans hρ₁ε) hz
    have hκz : κ z ≠ 0 := hκ z hzε
    have hy : (κ z)⁻¹ • x ∈ K z := by
      show κ z • ((κ z)⁻¹ • x) ∈ latt (E z)
      rw [smul_smul, mul_inv_cancel₀ hκz, one_smul]; exact hx
    obtain ⟨n, hn, huniq⟩ := hpers z (ball_subset_ball (min_le_left _ _) hz) _ hy
    have hcast : ∀ m : Fin 4 → ℤ, (∑ i, (m i : ℂ) • v i z) = ∑ i, (m i : ℝ) • v i z := by
      intro m
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    refine ⟨n, ?_, fun m hm => huniq m ?_⟩
    · show (∑ i, (n i : ℂ) • v i z) = (κ z)⁻¹ • x
      rw [hcast]; exact hn
    · have hm' : (∑ i, (m i : ℂ) • v i z) = (κ z)⁻¹ • x := hm
      rw [hcast] at hm'; exact hm'

end
end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_differentiableOn_latticeBasis_of_uniformization_family_of_smooth
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_differentiableOn_latticeBasis_of_uniformization_family_of_smooth (solution)
