-- Prove2me | solution 1 for ContinuousLinearMap.map_highPart_orthogonal_le_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/0c0c4cc7-bbb5-5b20-a494-a9c3b5b2d3f5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ContinuousLinearMap_map_highPart_orthogonal_le_of_commute

set_option autoImplicit false

open Module.End

namespace ContinuousLinearMap
p2m_export "ContinuousLinearMap" "apply comp eq_zero_of_forall_hasEigenvalue_eq_zero finite_dimensional_eigenspace coe_coe restrict adjoint_comp adjoint comp_apply ext coe_comp' adjoint_inner_left inl inr"
p2m_open "ContinuousLinearMap"

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

def highPart (T : E →L[𝕜] E) (r : ℝ) : Submodule 𝕜 E :=
  ⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), eigenspace (T : Module.End 𝕜 E) μ

omit [CompleteSpace E] in

theorem le_norm_sub_of_mem_eigenspace {T : E →L[𝕜] E} (hT' : (T : E →ₗ[𝕜] E).IsSymmetric)
    {μ ν : 𝕜} (hμν : μ ≠ ν) {r : ℝ} (hr : 0 ≤ r) (hμ : r ≤ ‖μ‖) (hν : r ≤ ‖ν‖)
    {e e' : E} (he : e ∈ eigenspace (T : Module.End 𝕜 E) μ) (he' : e' ∈ eigenspace (T : Module.End 𝕜 E) ν)
    (hne : ‖e‖ = 1) (hne' : ‖e'‖ = 1) : r ≤ ‖T e - T e'‖ := by
  have h0 : inner 𝕜 e e' = 0 := hT'.orthogonalFamily_eigenspaces hμν ⟨e, he⟩ ⟨e', he'⟩
  have horth : inner 𝕜 (μ • e) (ν • e') = 0 := by
    rw [inner_smul_left, inner_smul_right, h0]; simp
  have hTe : T e = μ • e := mem_eigenspace_iff.mp he
  have hTe' : T e' = ν • e' := mem_eigenspace_iff.mp he'
  rw [hTe, hTe']
  have hpy : ‖μ • e - ν • e'‖ * ‖μ • e - ν • e'‖ = ‖μ • e‖ * ‖μ • e‖ + ‖ν • e'‖ * ‖ν • e'‖ := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) (μ • e) (-(ν • e'))
      (by rw [inner_neg_right, horth, neg_zero])
    rwa [← sub_eq_add_neg, norm_neg] at this
  rw [norm_smul, norm_smul, hne, hne', mul_one, mul_one] at hpy
  have h1 : r * r ≤ ‖μ • e - ν • e'‖ * ‖μ • e - ν • e'‖ := by
    rw [hpy]; nlinarith [norm_nonneg μ, norm_nonneg ν]
  nlinarith [norm_nonneg (μ • e - ν • e'), h1]

theorem finite_setOf_hasEigenvalue_le_norm_pf {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) {r : ℝ} (hr : 0 < r) :
    {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 E) μ ∧ r ≤ ‖μ‖}.Finite := by
  by_contra hinf
  have hinf' : {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 E) μ ∧ r ≤ ‖μ‖}.Infinite := hinf

  let μ : ℕ → 𝕜 := fun n => (hinf'.natEmbedding _ n : 𝕜)
  have hμmem : ∀ n, HasEigenvalue (T : Module.End 𝕜 E) (μ n) ∧ r ≤ ‖μ n‖ := fun n => (hinf'.natEmbedding _ n).2
  have hμinj : Function.Injective μ := fun a b h =>
    (hinf'.natEmbedding _).injective (Subtype.ext h)
  have hex : ∀ n, ∃ e : E, e ∈ eigenspace (T : Module.End 𝕜 E) (μ n) ∧ ‖e‖ = 1 := by
    intro n
    obtain ⟨v, hv, hv0⟩ := (hμmem n).1.exists_hasEigenvector
    refine ⟨(‖v‖⁻¹ : 𝕜) • v, Submodule.smul_mem _ _ hv, ?_⟩
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  choose e he hne using hex

  have hsep : ∀ n m, n ≠ m → r ≤ ‖T (e n) - T (e m)‖ := fun n m hnm =>
    le_norm_sub_of_mem_eigenspace hT' (fun h => hnm (hμinj h)) hr.le (hμmem n).2 (hμmem m).2 (he n) (he m)
      (hne n) (hne m)
  have hK : IsCompact (closure (T '' Metric.closedBall (0 : E) 1)) := hT.isCompact_closure_image_closedBall 1
  have hin : ∀ n, T (e n) ∈ closure (T '' Metric.closedBall (0 : E) 1) := fun n =>
    subset_closure ⟨e n, by simp [hne n], rfl⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hin
  have hc : CauchySeq (fun n => T (e (φ n))) := hlim.cauchySeq
  rw [Metric.cauchySeq_iff] at hc
  obtain ⟨N₀, hN₀⟩ := hc r hr
  have := hN₀ N₀ le_rfl (N₀ + 1) (by omega)
  rw [dist_eq_norm] at this
  exact absurd (hsep (φ N₀) (φ (N₀ + 1)) (fun h => by have := hφ.injective h; omega)) (not_le.mpr this)

theorem finiteDimensional_highPart_pf {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) {r : ℝ} (hr : 0 < r) :
    FiniteDimensional 𝕜 ↥(highPart T r) := by
  set M := {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 E) μ ∧ r ≤ ‖μ‖} with hM
  have hfin : M.Finite := finite_setOf_hasEigenvalue_le_norm_pf hT hT' hr
  haveI : ∀ μ : 𝕜, μ ∈ hfin.toFinset → FiniteDimensional 𝕜 ↥(eigenspace (T : Module.End 𝕜 E) μ) := by
    intro μ hμ
    rw [Set.Finite.mem_toFinset] at hμ
    exact finite_dimensional_eigenspace hT μ (fun h => by
      have h2 : r ≤ ‖μ‖ := hμ.2
      rw [h, norm_zero] at h2; exact absurd h2 (not_le.mpr hr))
  have hle : highPart T r ≤ hfin.toFinset.sup fun μ => eigenspace (T : Module.End 𝕜 E) μ := by
    refine iSup₂_le fun μ hμ => ?_
    by_cases h : HasEigenvalue (T : Module.End 𝕜 E) μ
    · exact Finset.le_sup (f := fun μ => eigenspace (T : Module.End 𝕜 E) μ)
        (hfin.mem_toFinset.mpr ⟨h, hμ⟩)
    · rw [hasEigenvalue_iff, not_ne_iff] at h
      rw [h]; exact bot_le
  haveI : ∀ i : { x // x ∈ hfin.toFinset }, FiniteDimensional 𝕜 ↥(eigenspace (T : Module.End 𝕜 E) i) :=
    fun i => this i i.2
  haveI : FiniteDimensional 𝕜 ↥(hfin.toFinset.sup fun μ => eigenspace (T : Module.End 𝕜 E) μ) := by
    rw [Finset.sup_eq_iSup]
    have e : (⨆ μ ∈ hfin.toFinset, eigenspace (T : Module.End 𝕜 E) μ)
        = ⨆ i : { x // x ∈ hfin.toFinset }, eigenspace (T : Module.End 𝕜 E) i := by
      rw [iSup_subtype']
    rw [e]
    exact Submodule.finiteDimensional_iSup _
  exact Submodule.finiteDimensional_of_le hle

theorem apply_mem_iSup_eigenspace_ne_zero {T : E →L[𝕜] E} {u : E}
    (hu : u ∈ ⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ) :
    T u ∈ ⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ := by
  refine Submodule.iSup_induction _
    (motive := fun u => T u ∈ ⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ) hu
    (fun μ x hx => ?_) (by simp) (fun x y hx hy => ?_)
  · by_cases hμ : μ = 0
    · simp [hμ] at hx; simp [hx]
    · rw [iSup_pos hμ, mem_eigenspace_iff] at hx
      have hx' : T x = μ • x := hx
      rw [hx']
      refine Submodule.smul_mem _ μ (Submodule.mem_iSup_of_mem μ ?_)
      rw [iSup_pos hμ, mem_eigenspace_iff]
      show T x = μ • x
      exact hx'
  · rw [map_add]; exact Submodule.add_mem _ hx hy

theorem orthogonal_iSup_eigenspace_ne_zero_eq_ker_pf {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    (⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ)ᗮ = LinearMap.ker (T : E →ₗ[𝕜] E) := by
  set K : Submodule 𝕜 E := ⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ with hK
  apply le_antisymm
  · intro v hv
    have hinv : ∀ w ∈ Kᗮ, T w ∈ Kᗮ := by
      intro w hw
      rw [Submodule.mem_orthogonal] at hw ⊢
      intro u hu
      have e : inner 𝕜 u (T w) = inner 𝕜 ((T : E →ₗ[𝕜] E) u) w := (hT' u w).symm
      rw [e]
      exact hw _ (apply_mem_iSup_eigenspace_ne_zero hu)
    let S : ↥Kᗮ →L[𝕜] ↥Kᗮ := T.restrict hinv
    have hS_compact : IsCompactOperator S := hT.restrict' hinv
    have hS_symm : (S : ↥Kᗮ →ₗ[𝕜] ↥Kᗮ).IsSymmetric := hT'.restrict_invariant hinv
    have hS0 : S = 0 := by
      rw [← eq_zero_of_forall_hasEigenvalue_eq_zero hS_compact hS_symm]
      intro μ hμ
      by_contra hμ0
      rw [hasEigenvalue_iff] at hμ
      apply hμ
      rw [eq_bot_iff]
      intro w hw
      rw [mem_eigenspace_iff] at hw
      have hw' : ((S w : Kᗮ) : E) = ((μ • w : Kᗮ) : E) := congrArg Subtype.val hw
      have hwE : (w : E) ∈ eigenspace (T : Module.End 𝕜 E) μ := by
        rw [mem_eigenspace_iff]
        exact hw'
      have hwK : (w : E) ∈ K := by
        refine Submodule.mem_iSup_of_mem μ ?_
        rw [iSup_pos hμ0]; exact hwE
      have hw0 : (w : E) ∈ K ⊓ Kᗮ := ⟨hwK, w.2⟩
      rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hw0
      rw [Submodule.mem_bot]
      exact Subtype.ext hw0
    have h1 : ((S ⟨v, hv⟩ : Kᗮ) : E) = 0 := by rw [hS0]; rfl
    exact h1
  ·
    intro v hv
    have hv0 : v ∈ eigenspace (T : Module.End 𝕜 E) 0 := by
      rw [mem_eigenspace_iff, zero_smul]; exact hv
    rw [Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.iSup_induction _ (motive := fun u => inner 𝕜 u v = 0) hu
      (fun μ x hx => ?_) (by simp) (fun x y hx hy => ?_)
    · by_cases hμ : μ = 0
      · simp [hμ] at hx; simp [hx]
      · rw [iSup_pos hμ] at hx
        exact hT'.orthogonalFamily_eigenspaces hμ ⟨x, hx⟩ ⟨v, hv0⟩
    · rw [inner_add_left, hx, hy, add_zero]

theorem highPart_sup_orthogonal_eq_top_pf {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) {r : ℝ} (hr : 0 < r) :
    highPart T r ⊔ (highPart T r)ᗮ = ⊤ := by
  haveI := finiteDimensional_highPart_pf hT hT' hr
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

theorem map_highPart_le_of_commute_pf {T S : E →L[𝕜] E}
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) (r : ℝ) :
    Submodule.map (S : E →ₗ[𝕜] E) (highPart T r) ≤ highPart T r := by
  unfold highPart
  rw [Submodule.map_iSup]
  refine iSup_mono fun μ => ?_
  rw [Submodule.map_iSup]
  refine iSup_mono fun hμ => ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_eigenspace_iff] at hx
  rw [mem_eigenspace_iff]
  have h := congrArg (fun A : E →L[𝕜] E => A x) hST
  simp only [coe_comp', Function.comp_apply] at h
  show (T : E →ₗ[𝕜] E) (S x) = μ • S x
  have : T (S x) = S (T x) := h.symm
  rw [ContinuousLinearMap.coe_coe, this, show (T x) = μ • x from hx, map_smul]

theorem adjoint_comp_eq_of_isSymmetric {T S : E →L[𝕜] E}
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) :
    (adjoint S).comp T = T.comp (adjoint S) := by
  have hT : adjoint T = T := hT'.isSelfAdjoint.adjoint_eq
  have := congrArg adjoint hST
  rw [adjoint_comp, adjoint_comp, hT] at this
  exact this.symm

theorem map_highPart_orthogonal_le_of_commute_pf {T S : E →L[𝕜] E}
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) (r : ℝ) :
    Submodule.map (S : E →ₗ[𝕜] E) (highPart T r)ᗮ ≤ (highPart T r)ᗮ := by
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_orthogonal] at hy
  rw [Submodule.mem_orthogonal]
  intro x hx
  have hx' : adjoint S x ∈ highPart T r :=
    map_highPart_le_of_commute_pf hT' (adjoint_comp_eq_of_isSymmetric hT' hST) r ⟨x, hx, rfl⟩
  rw [ContinuousLinearMap.coe_coe, ← adjoint_inner_left]
  exact hy _ hx'

theorem iInf_highPart_orthogonal_eq_ker_pf {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    (⨅ (r : ℝ) (_ : 0 < r), (highPart T r)ᗮ) = LinearMap.ker (T : E →ₗ[𝕜] E) := by
  rw [← orthogonal_iSup_eigenspace_ne_zero_eq_ker_pf hT hT']
  have e : (⨅ (r : ℝ) (_ : 0 < r), (highPart T r)ᗮ) = (⨆ (r : ℝ) (_ : 0 < r), highPart T r)ᗮ := by
    rw [← Submodule.iInf_orthogonal]
    refine iInf_congr fun r => ?_
    by_cases hr : 0 < r
    · simp only [iInf_pos hr, iSup_pos hr]
    · simp only [iInf_neg hr, iSup_neg hr, Submodule.bot_orthogonal_eq_top]
  rw [e]
  congr 1
  apply le_antisymm
  · refine iSup₂_le fun r hr => iSup₂_le fun μ hμ => ?_
    have hμ0 : μ ≠ 0 := fun h => by rw [h, norm_zero] at hμ; exact absurd hμ (not_le.mpr hr)
    exact le_iSup₂_of_le μ hμ0 le_rfl
  · refine iSup₂_le fun μ hμ => ?_
    have hr : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
    exact le_iSup₂_of_le ‖μ‖ hr (le_iSup₂_of_le μ le_rfl le_rfl)

theorem exists_inf_highPart_orthogonal_eq_bot_of_not_le_ker_pf {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (X : Submodule 𝕜 E)
    (hX : ∀ r : ℝ, 0 < r → X ⊓ (highPart T r)ᗮ = ⊥ ∨ X ≤ (highPart T r)ᗮ)
    (hTX : ¬ X ≤ LinearMap.ker (T : E →ₗ[𝕜] E)) :
    ∃ r : ℝ, 0 < r ∧ X ⊓ (highPart T r)ᗮ = ⊥ ∧
      ∃ L : ↥X →ₗ[𝕜] ↥(highPart T r), Function.Injective L := by
  by_contra hcon
  push Not at hcon
  apply hTX
  rw [← iInf_highPart_orthogonal_eq_ker_pf hT hT']
  refine le_iInf₂ fun r hr => ?_
  rcases hX r hr with h | h
  · exfalso
    haveI := finiteDimensional_highPart_pf hT hT' hr

    have hinj : Function.Injective
        (((highPart T r).orthogonalProjection : E →ₗ[𝕜] ↥(highPart T r)).comp X.subtype) := by
      intro a b hab
      apply Subtype.ext
      have h2 : (a : E) - b ∈ (highPart T r)ᗮ := by
        rw [← Submodule.orthogonalProjection_eq_zero_iff, map_sub, sub_eq_zero]
        exact hab
      have hmem : (a : E) - b ∈ X ⊓ (highPart T r)ᗮ := ⟨X.sub_mem a.2 b.2, h2⟩
      rw [h, Submodule.mem_bot, sub_eq_zero] at hmem
      exact hmem
    exact hcon r hr h _ hinj
  · exact h

theorem le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal_pf {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (X : Submodule 𝕜 E)
    (hX : ∀ r : ℝ, 0 < r → X ⊓ (highPart T r)ᗮ = ⊥ ∨ X ≤ (highPart T r)ᗮ) :
    X ≤ LinearMap.ker (T : E →ₗ[𝕜] E) ∨ FiniteDimensional 𝕜 ↥X := by
  by_cases hTX : X ≤ LinearMap.ker (T : E →ₗ[𝕜] E)
  · exact Or.inl hTX
  obtain ⟨r, hr, -, L, hL⟩ := exists_inf_highPart_orthogonal_eq_bot_of_not_le_ker_pf hT hT' X hX hTX
  haveI := finiteDimensional_highPart_pf hT hT' hr
  exact Or.inr (Module.Finite.of_injective L hL)

end ContinuousLinearMap

open Module.End in
theorem solution {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {T S : E →L[𝕜] E}
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) (r : ℝ) :
    Submodule.map (S : E →ₗ[𝕜] E) (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ ≤ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ :=
  ContinuousLinearMap.map_highPart_orthogonal_le_of_commute_pf hT' hST r

end S_ContinuousLinearMap_map_highPart_orthogonal_le_of_commute
end P2MW
export P2MW.S_ContinuousLinearMap_map_highPart_orthogonal_le_of_commute (solution)
