-- Prove2me | solution 1 for ContinuousMap.exists_continuous_monoidHom_forall_sum_eq_zero_of_compactSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/f9955ec0-c46d-5eac-9357-fdd8be04ef16

import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Instances.Complex
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Theorems.Thm_MeasureTheory_L2_exists_convolutionCLM_isCompactOperator_of_compactSpace
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ContinuousMap_exists_continuous_monoidHom_forall_sum_eq_zero_of_compactSpace
p2m_attr_erase "simp" "MeasureTheory.L2.kernelIntegralLM_apply"

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped Convolution

noncomputable section

private theorem ra_exists_joint_eigenvector {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [Nontrivial E] {ι : Type*} (T : ι → Module.End ℂ E) (hcomm : ∀ i j, Commute (T i) (T j)) :
    ∃ e : E, e ≠ 0 ∧ ∀ i, ∃ a : ℂ, T i e = a • e := by
  classical
  have hP : ∃ n : ℕ, ∃ W : Submodule ℂ E, W ≠ ⊥ ∧ (∀ i, ∀ w ∈ W, T i w ∈ W) ∧ Module.finrank ℂ W = n := by
    refine ⟨_, ⊤, ?_, fun i w _ => Submodule.mem_top, rfl⟩
    rw [Submodule.ne_bot_iff]
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact ⟨x, Submodule.mem_top, hx⟩
  obtain ⟨W, hWbot, hWinv, hWrank⟩ := Nat.find_spec hP
  have hmin : ∀ W' : Submodule ℂ E, W' ≠ ⊥ → (∀ i, ∀ w ∈ W', T i w ∈ W') →
      Nat.find hP ≤ Module.finrank ℂ W' :=
    fun W' h1 h2 => Nat.find_min' hP ⟨W', h1, h2, rfl⟩
  have hscalar : ∀ i, ∃ a : ℂ, ∀ w ∈ W, T i w = a • w := by
    intro i
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWbot
    obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue ((T i).restrict (hWinv i))
    obtain ⟨w, hw⟩ := ha.exists_hasEigenvector
    refine ⟨a, ?_⟩
    have hw_eq : T i (w : E) = a • (w : E) := by
      have h1 := congrArg Subtype.val hw.apply_eq_smul
      simpa [LinearMap.coe_restrict_apply] using h1
    have hW'bot : W ⊓ Module.End.eigenspace (T i) a ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      refine ⟨(w : E), Submodule.mem_inf.mpr ⟨w.2, Module.End.mem_eigenspace_iff.mpr hw_eq⟩, ?_⟩
      intro h0
      exact hw.2 (Subtype.ext h0)
    have hW'inv : ∀ j, ∀ x ∈ W ⊓ Module.End.eigenspace (T i) a, T j x ∈ W ⊓ Module.End.eigenspace (T i) a := by
      intro j x hx
      rw [Submodule.mem_inf] at hx ⊢
      refine ⟨hWinv j x hx.1, ?_⟩
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      have hc := LinearMap.congr_fun (hcomm i j).eq x
      simp only [Module.End.mul_apply] at hc
      rw [hc, hx.2, map_smul]
    have hle : W ⊓ Module.End.eigenspace (T i) a ≤ W := inf_le_left
    have hrank : Module.finrank ℂ ↥(W ⊓ Module.End.eigenspace (T i) a) = Module.finrank ℂ W := by
      apply le_antisymm (Submodule.finrank_mono hle)
      rw [hWrank]
      exact hmin _ hW'bot hW'inv
    have hWeq : W ⊓ Module.End.eigenspace (T i) a = W := Submodule.eq_of_le_of_finrank_eq hle hrank
    intro x hxW
    have hx' : x ∈ W ⊓ Module.End.eigenspace (T i) a := by rw [hWeq]; exact hxW
    exact Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp hx').2
  obtain ⟨e, heW, he0⟩ := (Submodule.ne_bot_iff W).mp hWbot
  exact ⟨e, he0, fun i => (hscalar i).imp fun a ha => ha e heW⟩

private theorem ra_exists_monoidHom_of_eigen {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Ψ : C(G, ℂ)) (x₀ : G) (hx₀ : Ψ x₀ ≠ 0) (heig : ∀ g, ∃ a : ℂ, ∀ x, Ψ (x * g) = a * Ψ x) :
    ∃ χ : G →* ℂˣ, Continuous χ ∧ ∀ g x, Ψ (x * g) = ((χ g : ℂˣ) : ℂ) * Ψ x := by
  have hc : ∀ g x, Ψ (x * g) = (Ψ (x₀ * g) / Ψ x₀) * Ψ x := by
    intro g x
    obtain ⟨a, ha⟩ := heig g
    rw [ha x₀, mul_div_assoc, div_self hx₀, mul_one]
    exact ha x
  have hc1 : Ψ (x₀ * 1) / Ψ x₀ = 1 := by rw [mul_one]; exact div_self hx₀
  have hcmul : ∀ g h, Ψ (x₀ * (g * h)) / Ψ x₀ = (Ψ (x₀ * g) / Ψ x₀) * (Ψ (x₀ * h) / Ψ x₀) := by
    intro g h
    rw [← mul_assoc x₀ g h, hc h (x₀ * g)]
    ring
  let cHom : G →* ℂ :=
    { toFun := fun g => Ψ (x₀ * g) / Ψ x₀
      map_one' := hc1
      map_mul' := hcmul }
  have hcont : Continuous fun g => Ψ (x₀ * g) / Ψ x₀ :=
    (Ψ.continuous.comp (continuous_const.mul continuous_id)).div_const _
  refine ⟨cHom.toHomUnits, ?_, fun g x => hc g x⟩
  rw [Units.continuous_iff]
  refine ⟨hcont, ?_⟩
  have hinv : (fun g => (((cHom.toHomUnits g)⁻¹ : ℂˣ) : ℂ)) = fun g => Ψ (x₀ * g⁻¹) / Ψ x₀ := by
    funext g
    rw [← map_inv]
    rfl
  rw [hinv]
  exact hcont.comp continuous_inv

section Core

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsAddHaarMeasure]

private theorem ra_mp_add_right (h : H) : MeasurePreserving (fun x : H => x + h) μ μ := by
  have e : (fun x : H => x + h) = fun x => h + x := funext fun x => add_comm x h
  rw [e]
  exact measurePreserving_add_left μ h

private def ra_τ (h : H) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x : H => x + h) (ra_mp_add_right μ h)).toContinuousLinearMap

private theorem ra_coeFn_τ (h : H) (φ : Lp ℂ 2 μ) : (ra_τ μ h φ : H → ℂ) =ᵐ[μ] fun x => φ (x + h) :=
  Lp.coeFn_compMeasurePreserving φ (ra_mp_add_right μ h)

private theorem ra_τ_comm (g h : H) (φ : Lp ℂ 2 μ) : ra_τ μ h (ra_τ μ g φ) = ra_τ μ g (ra_τ μ h φ) := by
  apply Lp.ext
  have h1 := ra_coeFn_τ μ h (ra_τ μ g φ)
  have h2 : (fun x => (ra_τ μ g φ : H → ℂ) (x + h)) =ᵐ[μ] fun x => φ (x + h + g) :=
    (ra_coeFn_τ μ g φ).comp_tendsto (ra_mp_add_right μ h).quasiMeasurePreserving.tendsto_ae
  have h3 := ra_coeFn_τ μ g (ra_τ μ h φ)
  have h4 : (fun x => (ra_τ μ h φ : H → ℂ) (x + g)) =ᵐ[μ] fun x => φ (x + g + h) :=
    (ra_coeFn_τ μ h φ).comp_tendsto (ra_mp_add_right μ g).quasiMeasurePreserving.tendsto_ae
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
  rw [hx1, hx2, hx3, hx4, add_right_comm]

omit [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [BorelSpace H] [μ.IsAddHaarMeasure] in
private theorem ra_coeFn_finset_sum {α : Type*} (t : Finset α) (ψ : α → Lp ℂ 2 μ) :
    ((∑ a ∈ t, ψ a : Lp ℂ 2 μ) : H → ℂ) =ᵐ[μ] fun x => ∑ a ∈ t, (ψ a : H → ℂ) x := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    exact hx
  · intro a t hat ih
    rw [Finset.sum_insert hat]
    filter_upwards [Lp.coeFn_add (ψ a) (∑ b ∈ t, ψ b), ih] with x hx hih
    rw [hx, Pi.add_apply, hih, Finset.sum_insert hat]

variable {ι : Type*} (s : ι → Finset H) (c : ι → H → ℂ)

private def ra_relOp (i : ι) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := ∑ g ∈ s i, c i g • ra_τ μ g

private def ra_relSpace : Submodule ℂ (Lp ℂ 2 μ) :=
  ⨅ i, LinearMap.ker (ra_relOp μ s c i : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ)

private theorem ra_coeFn_relOp (i : ι) (φ : Lp ℂ 2 μ) {φ' : H → ℂ} (hφ : (φ : H → ℂ) =ᵐ[μ] φ') :
    (ra_relOp μ s c i φ : H → ℂ) =ᵐ[μ] fun x => ∑ g ∈ s i, c i g * φ' (x + g) := by
  have hterm : ∀ g ∈ s i, ((c i g • ra_τ μ g φ : Lp ℂ 2 μ) : H → ℂ) =ᵐ[μ] fun x => c i g * φ' (x + g) := by
    intro g _
    have h1 := Lp.coeFn_smul (c i g) (ra_τ μ g φ)
    have h2 := ra_coeFn_τ μ g φ
    have h3 : (fun x => (φ : H → ℂ) (x + g)) =ᵐ[μ] fun x => φ' (x + g) :=
      hφ.comp_tendsto (ra_mp_add_right μ g).quasiMeasurePreserving.tendsto_ae
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    rw [hx1, Pi.smul_apply, smul_eq_mul, hx2, hx3]
  have hsum : (ra_relOp μ s c i φ : H → ℂ) =ᵐ[μ] fun x => ∑ g ∈ s i, ((c i g • ra_τ μ g φ : Lp ℂ 2 μ) : H → ℂ) x := by
    have e : ra_relOp μ s c i φ = ∑ g ∈ s i, c i g • ra_τ μ g φ := by
      simp only [ra_relOp, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    rw [e]
    exact ra_coeFn_finset_sum μ (s i) fun g => c i g • ra_τ μ g φ
  refine hsum.trans ?_
  have hall := (Filter.eventually_all_finset (s i)).mpr hterm
  filter_upwards [hall] with x hx
  exact Finset.sum_congr rfl hx

private theorem ra_relSpace_isClosed : IsClosed ((ra_relSpace μ s c : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) := by
  unfold ra_relSpace
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun i => ContinuousLinearMap.isClosed_ker (ra_relOp μ s c i)

private theorem ra_map_relSpace_of_comm (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hT : ∀ g φ, T (ra_τ μ g φ) = ra_τ μ g (T φ)) :
    ∀ φ ∈ ra_relSpace μ s c, T φ ∈ ra_relSpace μ s c := by
  intro φ hφ
  unfold ra_relSpace at hφ ⊢
  rw [Submodule.mem_iInf] at hφ ⊢
  intro i
  have h1 := hφ i
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at h1 ⊢
  have hcomm : ra_relOp μ s c i (T φ) = T (ra_relOp μ s c i φ) := by
    simp only [ra_relOp, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul, hT]
  rw [hcomm, h1, map_zero]

private theorem ra_τ_mem_relSpace (h : H) : ∀ φ ∈ ra_relSpace μ s c, ra_τ μ h φ ∈ ra_relSpace μ s c :=
  ra_map_relSpace_of_comm μ s c (ra_τ μ h) fun g φ => ra_τ_comm μ g h φ

private theorem ra_toLp_mem_relSpace [CompactSpace H] [IsFiniteMeasure μ] (F : C(H, ℂ))
    (hrel : ∀ i x, ∑ g ∈ s i, c i g * F (x + g) = 0) :
    (ContinuousMap.toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ)) F ∈ ra_relSpace μ s c := by
  unfold ra_relSpace
  rw [Submodule.mem_iInf]
  intro i
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have h := ra_coeFn_relOp μ s c i ((ContinuousMap.toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ)) F)
    (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) F)
  filter_upwards [h] with x hx
  rw [hx]
  exact hrel i x

private theorem ra_conv_congr_ae [μ.IsNegInvariant] (b : H → ℂ) {φ ψ : H → ℂ} (h : φ =ᵐ[μ] ψ) (x : H) :
    (b ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] φ) x = (b ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] ψ) x := by
  simp only [convolution_def]
  apply integral_congr_ae
  have h' : (fun t => φ (x - t)) =ᵐ[μ] fun t => ψ (x - t) :=
    h.comp_tendsto (Measure.measurePreserving_sub_left μ x).quasiMeasurePreserving.tendsto_ae
  filter_upwards [h'] with t ht
  rw [ht]

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [BorelSpace H] [μ.IsAddHaarMeasure] in
private theorem ra_conv_translate (b : H → ℂ) (φ : H → ℂ) (h x : H) :
    (b ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] fun y => φ (y + h)) x
      = (b ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] φ) (x + h) := by
  simp only [convolution_def, sub_add_eq_add_sub]

private theorem ra_T_comm_τ [μ.IsNegInvariant] (b : H → ℂ) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ φ : Lp ℂ 2 μ, (T φ : H → ℂ) =ᵐ[μ] (b ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (φ : H → ℂ)))
    (h : H) (φ : Lp ℂ 2 μ) : T (ra_τ μ h φ) = ra_τ μ h (T φ) := by
  apply Lp.ext
  have h1 := hT (ra_τ μ h φ)
  have h2 : ∀ x, (b ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (ra_τ μ h φ : H → ℂ)) x
      = (b ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (φ : H → ℂ)) (x + h) := fun x =>
    (ra_conv_congr_ae μ b (ra_coeFn_τ μ h φ) x).trans (ra_conv_translate μ b (φ : H → ℂ) h x)
  have h3 := ra_coeFn_τ μ h (T φ)
  have h4 : (fun x => (T φ : H → ℂ) (x + h)) =ᵐ[μ]
      fun x => (b ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (φ : H → ℂ)) (x + h) :=
    (hT φ).comp_tendsto (ra_mp_add_right μ h).quasiMeasurePreserving.tendsto_ae
  filter_upwards [h1, h3, h4] with x hx1 hx3 hx4
  rw [hx1, h2 x, hx3, hx4]

private theorem ra_re_mul_conj_pos {z u : ℂ} (hu : u ≠ 0) (hz : ‖z - u‖ < ‖u‖ / 2) :
    0 < (z * (starRingEnd ℂ) u).re := by
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hsplit : z * (starRingEnd ℂ) u = u * (starRingEnd ℂ) u + (z - u) * (starRingEnd ℂ) u := by ring
  have h1 : (u * (starRingEnd ℂ) u).re = ‖u‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have h2 : -(‖z - u‖ * ‖u‖) ≤ ((z - u) * (starRingEnd ℂ) u).re := by
    have h3 := Complex.abs_re_le_norm ((z - u) * (starRingEnd ℂ) u)
    rw [norm_mul, Complex.norm_conj] at h3
    exact (abs_le.mp h3).1
  have h4 : ‖z - u‖ * ‖u‖ < ‖u‖ / 2 * ‖u‖ := mul_lt_mul_of_pos_right hz hupos
  rw [hsplit, Complex.add_re, h1]
  nlinarith

private theorem ra_exists_bump [CompactSpace H] [T2Space H] [IsFiniteMeasure μ] (F : C(H, ℂ)) (x₀ : H)
    (hx₀ : F x₀ ≠ 0) :
    ∃ b : C(H, ℂ), (∀ x, b (-x) = star (b x)) ∧
      ((b : H → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (F : H → ℂ)) x₀ ≠ 0 := by

  have hten : Tendsto (fun t : H => F (x₀ - t)) (𝓝 0) (𝓝 (F x₀)) := by
    have h : ContinuousAt (fun t : H => F (x₀ - t)) 0 :=
      (F.continuous.comp (continuous_const.sub continuous_id)).continuousAt
    have h2 := h.tendsto
    simp only [sub_zero] at h2
    exact h2
  have hev : ∀ᶠ t in 𝓝 (0 : H), ‖F (x₀ - t) - F x₀‖ < ‖F x₀‖ / 2 := by
    have h := (Metric.tendsto_nhds.mp hten) (‖F x₀‖ / 2) (half_pos (norm_pos_iff.mpr hx₀))
    exact h.mono fun t ht => by rwa [dist_eq_norm] at ht
  obtain ⟨W, hW, hWopen, hW0⟩ := eventually_nhds_iff.mp hev

  obtain ⟨b₀, hb₀off, hb₀one, hb₀Icc⟩ := exists_continuous_zero_one_of_isClosed hWopen.isClosed_compl
    (isClosed_singleton (x := (0 : H))) (Set.disjoint_singleton_right.mpr fun h => h hW0)

  let b₁ : H → ℝ := fun t => b₀ t * b₀ (-t)
  have hb₁cont : Continuous b₁ := b₀.continuous.mul (b₀.continuous.comp continuous_neg)
  have hb₁nonneg : ∀ t, 0 ≤ b₁ t := fun t => mul_nonneg (hb₀Icc t).1 (hb₀Icc (-t)).1
  have hb₁zero : b₁ 0 = 1 := by
    have h : b₀ 0 = 1 := hb₀one (Set.mem_singleton (0 : H))
    show b₀ 0 * b₀ (-0) = 1
    rw [neg_zero, h, mul_one]
  have hb₁W : ∀ t, b₁ t ≠ 0 → t ∈ W := by
    intro t ht
    by_contra htW
    apply ht
    have h : b₀ t = 0 := hb₀off htW
    show b₀ t * b₀ (-t) = 0
    rw [h, zero_mul]
  let b : C(H, ℂ) := ⟨fun t => (b₁ t : ℂ), Complex.continuous_ofReal.comp hb₁cont⟩
  refine ⟨b, ?_, ?_⟩
  · intro t
    show ((b₁ (-t) : ℝ) : ℂ) = star ((b₁ t : ℝ) : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal]
    congr 1
    show b₀ (-t) * b₀ (- -t) = b₀ t * b₀ (-t)
    rw [neg_neg, mul_comm]
  ·
    let r : H → ℝ := fun t => b₁ t * (F (x₀ - t) * (starRingEnd ℂ) (F x₀)).re
    have hrcont : Continuous r := by
      apply hb₁cont.mul
      exact Complex.continuous_re.comp
        ((F.continuous.comp (continuous_const.sub continuous_id)).mul continuous_const)
    have hrnonneg : ∀ t, 0 ≤ r t := by
      intro t
      by_cases h : b₁ t = 0
      · show 0 ≤ b₁ t * (F (x₀ - t) * (starRingEnd ℂ) (F x₀)).re
        rw [h, zero_mul]
      · exact mul_nonneg (hb₁nonneg t) (ra_re_mul_conj_pos hx₀ (hW t (hb₁W t h))).le
    have hrint : Integrable r μ :=
      hrcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace r)
    have hrpos : 0 < ∫ t, r t ∂μ := by
      rw [integral_pos_iff_support_of_nonneg hrnonneg hrint]

      have hopen : IsOpen (W ∩ b₁ ⁻¹' Set.Ioi 0) := hWopen.inter (isOpen_Ioi.preimage hb₁cont)
      have hmem : (0 : H) ∈ W ∩ b₁ ⁻¹' Set.Ioi 0 := by
        refine ⟨hW0, ?_⟩
        rw [Set.mem_preimage, Set.mem_Ioi, hb₁zero]
        exact one_pos
      have hsub : W ∩ b₁ ⁻¹' Set.Ioi 0 ⊆ Function.support r := by
        intro t ht
        rw [Function.mem_support]
        have hpos : 0 < b₁ t := Set.mem_Ioi.mp (Set.mem_preimage.mp ht.2)
        exact (mul_pos hpos (ra_re_mul_conj_pos hx₀ (hW t ht.1))).ne'
      exact (hopen.measure_pos μ ⟨0, hmem⟩).trans_le (measure_mono hsub)

    have hconv : ((b : H → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (F : H → ℂ)) x₀
        = ∫ t, (b t : ℂ) * F (x₀ - t) ∂μ := by
      simp only [convolution_def, ContinuousLinearMap.mul_apply']
    have hcint : Integrable (fun t => (b t : ℂ) * F (x₀ - t) * (starRingEnd ℂ) (F x₀)) μ := by
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      exact (b.continuous.mul (F.continuous.comp (continuous_const.sub continuous_id))).mul continuous_const
    intro hzero
    have hI : ∫ t, (b t : ℂ) * F (x₀ - t) ∂μ = 0 := by rw [← hconv]; exact hzero
    have hI2 : ∫ t, (b t : ℂ) * F (x₀ - t) * (starRingEnd ℂ) (F x₀) ∂μ = 0 := by
      rw [integral_mul_const, hI, zero_mul]
    have hI3 : ∫ t, ((b t : ℂ) * F (x₀ - t) * (starRingEnd ℂ) (F x₀)).re ∂μ = 0 := by
      have h : ∫ t, ((b t : ℂ) * F (x₀ - t) * (starRingEnd ℂ) (F x₀)).re ∂μ
          = (∫ t, (b t : ℂ) * F (x₀ - t) * (starRingEnd ℂ) (F x₀) ∂μ).re := integral_re hcint
      rw [h, hI2, Complex.zero_re]
    have hI4 : ∫ t, r t ∂μ = ∫ t, ((b t : ℂ) * F (x₀ - t) * (starRingEnd ℂ) (F x₀)).re ∂μ := by
      apply integral_congr_ae
      filter_upwards with t
      show b₁ t * (F (x₀ - t) * (starRingEnd ℂ) (F x₀)).re
        = (((b₁ t : ℝ) : ℂ) * F (x₀ - t) * (starRingEnd ℂ) (F x₀)).re
      rw [mul_assoc ((b₁ t : ℝ) : ℂ), Complex.re_ofReal_mul]
    rw [hI4, hI3] at hrpos
    exact lt_irrefl 0 hrpos

private theorem ra_core [CompactSpace H] [T2Space H] [IsFiniteMeasure μ] [μ.IsNegInvariant]
    (hconv : ∀ b : C(H, ℂ), (∀ x, b (-x) = star (b x)) →
      ∃ T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ,
        (∀ φ : Lp ℂ 2 μ, (T φ : H → ℂ) =ᵐ[μ] ((b : H → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (φ : H → ℂ))) ∧
        IsCompactOperator T ∧ LinearMap.IsSymmetric (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ))
    (F : C(H, ℂ)) (x₀ : H) (hx₀ : F x₀ ≠ 0)
    (hrel : ∀ i x, ∑ g ∈ s i, c i g * F (x + g) = 0) :
    ∃ Ψ : C(H, ℂ), (∃ y₀, Ψ y₀ ≠ 0) ∧ (∀ h, ∃ a : ℂ, ∀ x, Ψ (x + h) = a * Ψ x) ∧
      ∀ i x, ∑ g ∈ s i, c i g * Ψ (x + g) = 0 := by
  classical

  obtain ⟨b, hb, hbF⟩ := ra_exists_bump μ F x₀ hx₀
  obtain ⟨T, hTconv, hTcomp, hTsymm⟩ := hconv b hb

  obtain ⟨F₂, hF₂def⟩ : ∃ F₂ : Lp ℂ 2 μ, F₂ = (ContinuousMap.toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ)) F :=
    ⟨_, rfl⟩
  have hF₂ae : (F₂ : H → ℂ) =ᵐ[μ] F := by
    rw [hF₂def]
    exact ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) F
  have hF₂V : F₂ ∈ ra_relSpace μ s c := by
    rw [hF₂def]
    exact ra_toLp_mem_relSpace μ s c F hrel

  have hTF₂ : T F₂ ≠ 0 := by
    intro h0
    have h1 : (T F₂ : H → ℂ) =ᵐ[μ] 0 := by
      rw [h0]
      exact Lp.coeFn_zero ℂ 2 μ
    have h2 : ((b : H → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (F : H → ℂ)) =ᵐ[μ] 0 := by
      have h3 := (hTconv F₂).symm.trans h1
      filter_upwards [h3] with x hx
      rw [← ra_conv_congr_ae μ (b : H → ℂ) hF₂ae x]
      exact hx
    have hcont : Continuous ((b : H → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (F : H → ℂ)) :=
      (HasCompactSupport.of_compactSpace (b : H → ℂ)).continuous_convolution_left
        (L := ContinuousLinearMap.mul ℂ ℂ) b.continuous (F.continuous.locallyIntegrable (μ := μ))
    have h4 := (hcont.ae_eq_iff_eq (μ := μ) continuous_zero).mp h2
    exact hbF (congrFun h4 x₀)

  have hTτ : ∀ g φ, T (ra_τ μ g φ) = ra_τ μ g (T φ) := fun g φ => ra_T_comm_τ μ (b : H → ℂ) T hTconv g φ
  have hTV : ∀ φ ∈ ra_relSpace μ s c, T φ ∈ ra_relSpace μ s c := ra_map_relSpace_of_comm μ s c T hTτ
  haveI : CompleteSpace (ra_relSpace μ s c) := (ra_relSpace_isClosed μ s c).completeSpace_coe

  let S : ra_relSpace μ s c →L[ℂ] ra_relSpace μ s c := T.restrict hTV
  have hS_compact : IsCompactOperator S := hTcomp.restrict' hTV
  have hS_symm : S.IsSymmetric := hTsymm.restrict_invariant hTV
  have hS_ne : S ≠ 0 := by
    intro h
    apply hTF₂
    have h1 : ((S ⟨F₂, hF₂V⟩ : ra_relSpace μ s c) : Lp ℂ 2 μ) = T F₂ := rfl
    rw [h] at h1
    exact h1.symm
  obtain ⟨lam, hlam_eig, hlam_ne⟩ :
      ∃ lam : ℂ, Module.End.HasEigenvalue (S : Module.End ℂ (ra_relSpace μ s c)) lam ∧ lam ≠ 0 := by
    by_contra hcon
    have hall : ∀ l : ℂ, Module.End.HasEigenvalue (S : Module.End ℂ (ra_relSpace μ s c)) l → l = 0 :=
      fun l hl => Classical.byContradiction fun hne => hcon ⟨l, hl, hne⟩
    exact hS_ne ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hS_compact hS_symm).mp hall)

  obtain ⟨E₀, hE₀def⟩ : ∃ E₀ : Submodule ℂ (ra_relSpace μ s c),
      E₀ = Module.End.eigenspace (S : Module.End ℂ (ra_relSpace μ s c)) lam := ⟨_, rfl⟩
  have hE₀ne : E₀ ≠ ⊥ := by
    rw [hE₀def]
    exact Module.End.hasEigenvalue_iff.mp hlam_eig
  haveI : FiniteDimensional ℂ E₀ := by
    rw [hE₀def]
    exact ContinuousLinearMap.finite_dimensional_eigenspace hS_compact lam hlam_ne
  haveI : Nontrivial E₀ := Submodule.nontrivial_iff_ne_bot.mpr hE₀ne
  let τV : H → (ra_relSpace μ s c →ₗ[ℂ] ra_relSpace μ s c) :=
    fun h => (ra_τ μ h : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ).restrict (ra_τ_mem_relSpace μ s c h)
  have hτE₀ : ∀ h, ∀ e ∈ E₀, τV h e ∈ E₀ := by
    intro h e he
    rw [hE₀def, Module.End.mem_eigenspace_iff] at he ⊢
    have h4 : T (e : Lp ℂ 2 μ) = lam • (e : Lp ℂ 2 μ) := congrArg Subtype.val he
    apply Subtype.ext
    show T (ra_τ μ h (e : Lp ℂ 2 μ)) = lam • ra_τ μ h (e : Lp ℂ 2 μ)
    rw [hTτ h, h4, map_smul]
  let ρ : H → Module.End ℂ E₀ := fun h => (τV h).restrict (hτE₀ h)
  have hρcomm : ∀ g h, Commute (ρ g) (ρ h) := by
    intro g h
    show ρ g * ρ h = ρ h * ρ g
    apply LinearMap.ext
    intro e
    apply Subtype.ext
    apply Subtype.ext
    show ra_τ μ g (ra_τ μ h e.1.1) = ra_τ μ h (ra_τ μ g e.1.1)
    exact ra_τ_comm μ h g e.1.1
  obtain ⟨e, he0, heig⟩ := ra_exists_joint_eigenvector ρ hρcomm

  have hφ₀ne : e.1.1 ≠ 0 := fun h => he0 (Subtype.ext (Subtype.ext h))
  have hφ₀V : e.1.1 ∈ ra_relSpace μ s c := e.1.2
  have hTφ₀ : T e.1.1 = lam • e.1.1 := by
    have h1 : (e : ra_relSpace μ s c) ∈ Module.End.eigenspace (S : Module.End ℂ (ra_relSpace μ s c)) lam := by
      rw [← hE₀def]
      exact e.2
    rw [Module.End.mem_eigenspace_iff] at h1
    exact congrArg Subtype.val h1
  have hτφ₀ : ∀ h, ∃ a : ℂ, ra_τ μ h e.1.1 = a • e.1.1 := by
    intro h
    obtain ⟨a, ha⟩ := heig h
    exact ⟨a, congrArg (fun z : E₀ => z.1.1) ha⟩

  have hli : LocallyIntegrable (e.1.1 : H → ℂ) μ := (Lp.memLp e.1.1).locallyIntegrable one_le_two
  obtain ⟨Ψf, hΨf⟩ : ∃ Ψf : H → ℂ,
      Ψf = fun x => lam⁻¹ * ((b : H → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (e.1.1 : H → ℂ)) x := ⟨_, rfl⟩
  have hΨcont : Continuous Ψf := by
    rw [hΨf]
    exact continuous_const.mul ((HasCompactSupport.of_compactSpace (b : H → ℂ)).continuous_convolution_left
      (L := ContinuousLinearMap.mul ℂ ℂ) b.continuous hli)
  have hφ₀Ψ : (e.1.1 : H → ℂ) =ᵐ[μ] Ψf := by
    rw [hΨf]
    have h1 := hTconv e.1.1
    rw [hTφ₀] at h1
    have h2 := Lp.coeFn_smul lam e.1.1
    filter_upwards [h1, h2] with x hx1 hx2
    simp only [Pi.smul_apply, smul_eq_mul] at hx2
    rw [← hx1, hx2, ← mul_assoc, inv_mul_cancel₀ hlam_ne, one_mul]
  refine ⟨⟨Ψf, hΨcont⟩, ?_, ?_, ?_⟩
  ·
    by_contra hcon
    have hall : ∀ y, Ψf y = 0 := fun y => Classical.byContradiction fun hy => hcon ⟨y, hy⟩
    apply hφ₀ne
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hφ₀Ψ] with x hx
    rw [hx]
    exact hall x
  ·
    intro h
    obtain ⟨a, ha⟩ := hτφ₀ h
    refine ⟨a, ?_⟩
    have h1 := ra_coeFn_τ μ h e.1.1
    rw [ha] at h1
    have h2 := Lp.coeFn_smul a e.1.1
    have h3 : (fun x => (e.1.1 : H → ℂ) (x + h)) =ᵐ[μ] fun x => Ψf (x + h) :=
      hφ₀Ψ.comp_tendsto (ra_mp_add_right μ h).quasiMeasurePreserving.tendsto_ae
    have h4 : (fun x => Ψf (x + h)) =ᵐ[μ] fun x => a * Ψf x := by
      filter_upwards [h1, h2, h3, hφ₀Ψ] with x hx1 hx2 hx3 hx0
      simp only [Pi.smul_apply, smul_eq_mul] at hx2
      rw [← hx3, ← hx1, hx2, hx0]
    have hc1 : Continuous fun x => Ψf (x + h) := hΨcont.comp (continuous_id.add continuous_const)
    have hc2 : Continuous fun x => a * Ψf x := continuous_const.mul hΨcont
    have h5 := (hc1.ae_eq_iff_eq (μ := μ) hc2).mp h4
    intro x
    show Ψf (x + h) = a * Ψf x
    exact congrFun h5 x
  ·
    intro i x
    have h1 : ra_relOp μ s c i e.1.1 = 0 := by
      have h := hφ₀V
      unfold ra_relSpace at h
      rw [Submodule.mem_iInf] at h
      have h' := h i
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at h'
      exact h'
    have h2 : (ra_relOp μ s c i e.1.1 : H → ℂ) =ᵐ[μ] 0 := by
      rw [h1]
      exact Lp.coeFn_zero ℂ 2 μ
    have h3 := (ra_coeFn_relOp μ s c i e.1.1 hφ₀Ψ).symm.trans h2
    have hc1 : Continuous fun x => ∑ g ∈ s i, c i g * Ψf (x + g) :=
      continuous_finsetSum (s i) fun g _ => continuous_const.mul (hΨcont.comp (continuous_id.add continuous_const))
    have h4 := (hc1.ae_eq_iff_eq (μ := μ) continuous_zero).mp h3
    show ∑ g ∈ s i, c i g * Ψf (x + g) = 0
    exact congrFun h4 x

end Core

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (f : C(G, ℂ)) (hf : f ≠ 0) (R : Set (G →₀ ℂ))
    (hR : ∀ r ∈ R, ∀ x : G, (r.sum fun g c => c * f (x * g)) = 0) :
    ∃ χ : G →* ℂˣ, Continuous χ ∧ ∀ r ∈ R, (r.sum fun g c => c * ((χ g : ℂˣ) : ℂ)) = 0 := by
  classical

  haveI : CompactSpace (Additive G) := ‹CompactSpace G›
  haveI : T2Space (Additive G) := ‹T2Space G›
  borelize (Additive G)
  let F : C(Additive G, ℂ) := f.comp ⟨Additive.toMul, continuous_toMul⟩
  have hF : ∃ y₀ : Additive G, F y₀ ≠ 0 := by
    by_contra hcon
    have hall : ∀ y, F y = 0 := fun y => Classical.byContradiction fun hy => hcon ⟨y, hy⟩
    apply hf
    ext g
    rw [ContinuousMap.zero_apply]
    exact hall (Additive.ofMul g)
  obtain ⟨y₀, hy₀⟩ := hF

  let sR : R → Finset (Additive G) := fun r => (r : G →₀ ℂ).support
  let cR : R → Additive G → ℂ := fun r h => (r : G →₀ ℂ) (Additive.toMul h)
  have hrel : ∀ (r : R) (x : Additive G), ∑ h ∈ sR r, cR r h * F (x + h) = 0 := by
    intro r x
    have h := hR r.1 r.2 (Additive.toMul x)
    rw [Finsupp.sum] at h
    exact h
  obtain ⟨Ψ', ⟨z₀, hz₀⟩, heig', hrel'⟩ :=
    ra_core (Measure.addHaar : Measure (Additive G)) sR cR
      (fun b hb =>
        MeasureTheory.L2.exists_convolutionCLM_isCompactOperator_of_compactSpace (Additive G) Measure.addHaar b hb)
      F y₀ hy₀ hrel

  let Ψ : C(G, ℂ) := Ψ'.comp ⟨Additive.ofMul, continuous_ofMul⟩
  have hΨx₀ : Ψ (Additive.toMul z₀) ≠ 0 := hz₀
  have heig : ∀ g, ∃ a : ℂ, ∀ x, Ψ (x * g) = a * Ψ x := by
    intro g
    obtain ⟨a, ha⟩ := heig' (Additive.ofMul g)
    exact ⟨a, fun x => ha (Additive.ofMul x)⟩
  obtain ⟨χ, hχc, hχ⟩ := ra_exists_monoidHom_of_eigen Ψ (Additive.toMul z₀) hΨx₀ heig
  refine ⟨χ, hχc, fun r hr => ?_⟩
  have h1 : ∑ g ∈ r.support, r g * Ψ (Additive.toMul z₀ * g) = 0 := hrel' ⟨r, hr⟩ z₀
  simp only [hχ] at h1
  have h3 : (∑ g ∈ r.support, r g * ((χ g : ℂˣ) : ℂ)) * Ψ (Additive.toMul z₀) = 0 := by
    rw [Finset.sum_mul]
    simpa only [mul_assoc] using h1
  rw [Finsupp.sum]
  exact (mul_eq_zero.mp h3).resolve_right hΨx₀

end

#print axioms solution

end S_ContinuousMap_exists_continuous_monoidHom_forall_sum_eq_zero_of_compactSpace
end P2MW
export P2MW.S_ContinuousMap_exists_continuous_monoidHom_forall_sum_eq_zero_of_compactSpace (solution)
