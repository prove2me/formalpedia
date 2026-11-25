-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.shortDual_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:24.494293+00:00
-- url     : https://prove2.me/submissions/afbeb66c-bccd-4d22-90fe-8090ada9a0a4

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinSt
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceMinima
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinF
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_transference_successive_minima
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
open Matrix
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
theorem _root_.solution : ShortDualStatement := by
  intro d L R μ hd hL hR hμ hmin δ hδ
  obtain ⟨e, he⟩ : ∃ e : (Fin d → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d), ∀ a, (e a).ofLp = a :=
    ⟨(WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm,
      fun a => (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).apply_symm_apply a⟩
  have hin : ∀ a b : Fin d → ℝ, inner ℝ (e a) (e b) = a ⬝ᵥ b := by
    intro a b
    rw [EuclideanSpace.inner_eq_star_dotProduct, he, he, dotProduct_comm]
    congr 1
  have hnorm : ∀ a : Fin d → ℝ, ‖e a‖ ^ 2 = a ⬝ᵥ a := by
    intro a
    rw [← real_inner_self_eq_norm_sq, hin]
  have hRR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hR
  have hRR' : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have hcast : ∀ j : Fin d, (fun i => (((Pi.single j (1 : ℤ) : Fin d → ℤ) i : ℤ) : ℝ)) = Pi.single j (1 : ℝ) := by
    intro j
    funext i
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.single_apply, hij]

  obtain ⟨g, hg⟩ : ∃ g : (Fin d → ℤ) →ₗ[ℤ] EuclideanSpace ℝ (Fin d),
      ∀ t, g t = e (R *ᵥ fun i => (t i : ℝ)) :=
    ⟨(AddMonoidHom.mk' (fun t : Fin d → ℤ => e (R *ᵥ fun i => (t i : ℝ))) (by
        intro a b
        show e (R *ᵥ fun i => ((a + b) i : ℝ)) =
          e (R *ᵥ fun i => (a i : ℝ)) + e (R *ᵥ fun i => (b i : ℝ))
        have h1 : (fun i => ((a + b) i : ℝ)) = (fun i => (a i : ℝ)) + fun i => (b i : ℝ) := by
          funext i
          simp
        rw [h1, Matrix.mulVec_add, map_add])).toIntLinearMap, fun t => rfl⟩

  obtain ⟨hZ, hh⟩ : ∃ hZ : (Fin d → ℤ) →ₗ[ℤ] EuclideanSpace ℝ (Fin d),
      ∀ u, hZ u = e ((fun i => (u i : ℝ)) ᵥ* R⁻¹) :=
    ⟨(AddMonoidHom.mk' (fun u : Fin d → ℤ => e ((fun i => (u i : ℝ)) ᵥ* R⁻¹)) (by
        intro a b
        show e ((fun i => ((a + b) i : ℝ)) ᵥ* R⁻¹) =
          e ((fun i => (a i : ℝ)) ᵥ* R⁻¹) + e ((fun i => (b i : ℝ)) ᵥ* R⁻¹)
        have h1 : (fun i => ((a + b) i : ℝ)) = (fun i => (a i : ℝ)) + fun i => (b i : ℝ) := by
          funext i
          simp
        rw [h1, Matrix.add_vecMul, map_add])).toIntLinearMap, fun u => rfl⟩
  have hquad : ∀ t : Fin d → ℝ, ‖e (R *ᵥ t)‖ ^ 2 = t ⬝ᵥ (L *ᵥ t) := by
    intro t
    rw [hnorm, hL, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec t, Matrix.vecMul_transpose]
  have hlow : ∀ t : Fin d → ℤ, t ≠ 0 → μ ≤ ‖g t‖ := by
    intro t ht
    have h2 := hmin t ht
    rw [← hquad (fun i => (t i : ℝ)), ← hg t] at h2
    nlinarith [norm_nonneg (g t), hμ]

  have hdisc : DiscreteTopology (LinearMap.range g) := by
    apply DiscreteTopology.of_forall_le_dist hμ
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    obtain ⟨s, rfl⟩ := LinearMap.mem_range.mp hx
    obtain ⟨t, rfl⟩ := LinearMap.mem_range.mp hy
    have hst : s - t ≠ 0 := by
      intro h0
      apply hxy
      have h1 : s = t := sub_eq_zero.mp h0
      subst h1
      rfl
    rw [Subtype.dist_eq, dist_eq_norm]
    show μ ≤ ‖g s - g t‖
    rw [← map_sub]
    exact hlow _ hst

  have hFsurj : ∀ x : EuclideanSpace ℝ (Fin d), ∃ w, e (R *ᵥ w) = x := by
    intro x
    refine ⟨R⁻¹ *ᵥ e.symm x, ?_⟩
    rw [Matrix.mulVec_mulVec, hRR', Matrix.one_mulVec, LinearEquiv.apply_symm_apply]
  have hspan : Submodule.span ℝ
      ((LinearMap.range g : Submodule ℤ (EuclideanSpace ℝ (Fin d))) :
        Set (EuclideanSpace ℝ (Fin d))) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨w, rfl⟩ := hFsurj x
    have hw : w ∈ Submodule.span ℝ (Set.range (Pi.basisFun ℝ (Fin d))) := by
      rw [(Pi.basisFun ℝ (Fin d)).span_eq]
      exact Submodule.mem_top
    have h1 := Submodule.mem_map_of_mem (f := e.toLinearMap ∘ₗ Matrix.mulVecLin R) hw
    rw [← Submodule.span_image] at h1
    have h2 : e (R *ᵥ w) = (e.toLinearMap ∘ₗ Matrix.mulVecLin R) w := rfl
    rw [h2]
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    refine LinearMap.mem_range.mpr ⟨Pi.single j 1, ?_⟩
    rw [hg, hcast, Pi.basisFun_apply]
    rfl

  have hT := transference_successive_minima d (LinearMap.range g) hdisc hspan 1 le_rfl hd
  rw [Nat.add_sub_cancel] at hT
  obtain ⟨i0⟩ : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hne0 : (Pi.single i0 (1 : ℤ) : Fin d → ℤ) ≠ 0 := by
    intro h
    have := congr_fun h i0
    simp at this
  have hS1 : μ ≤ PI.succMin (LinearMap.range g) 1 := by
    unfold PI.succMin
    apply le_csInf
    · refine ⟨‖g (Pi.single i0 1)‖, norm_nonneg _, fun _ => g (Pi.single i0 1),
        fun _ => LinearMap.mem_range_self g _, ?_, fun _ => le_rfl⟩
      rw [linearIndependent_unique_iff]
      intro h0
      have h1 := hlow (Pi.single i0 1) hne0
      rw [show g (Pi.single i0 1) = 0 from h0, norm_zero] at h1
      linarith
    · rintro b ⟨hb0, v, hvM, hvli, hvb⟩
      obtain ⟨t, ht⟩ := LinearMap.mem_range.mp (hvM 0)
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact hvli.ne_zero 0 (by rw [← ht, map_zero])
      calc μ ≤ ‖g t‖ := hlow t ht0
        _ = ‖v 0‖ := by rw [ht]
        _ ≤ b := hvb 0

  have hdual : ∀ u : Fin d → ℤ, hZ u ∈ PI.dualZ (LinearMap.range g) := by
    intro u
    show ∀ y ∈ LinearMap.range g, ∃ z : ℤ, inner ℝ (hZ u) y = (z : ℝ)
    intro y hy
    obtain ⟨t, rfl⟩ := LinearMap.mem_range.mp hy
    refine ⟨u ⬝ᵥ t, ?_⟩
    rw [hh, hg, hin, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hRR, Matrix.vecMul_one]
    simp [dotProduct]
  have hinj : Function.Injective (e.toLinearMap ∘ₗ Matrix.vecMulLinear R⁻¹) := by
    intro a b hab
    have h0 : e (a ᵥ* R⁻¹) = e (b ᵥ* R⁻¹) := hab
    have h1 : a ᵥ* R⁻¹ = b ᵥ* R⁻¹ := e.injective h0
    have h2 := congrArg (fun x => x ᵥ* R) h1
    simpa only [Matrix.vecMul_vecMul, hRR, Matrix.vecMul_one] using h2
  have hne2 : ∃ b : ℝ, 0 ≤ b ∧ ∃ v : Fin d → EuclideanSpace ℝ (Fin d),
      (∀ j, v j ∈ PI.dualZ (LinearMap.range g)) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ b := by
    refine ⟨∑ j, ‖hZ (Pi.single j 1)‖, Finset.sum_nonneg (fun j _ => norm_nonneg _),
      fun j => hZ (Pi.single j 1), fun j => hdual _, ?_,
      fun j => Finset.single_le_sum (f := fun j => ‖hZ (Pi.single j 1)‖)
        (fun i _ => norm_nonneg _) (Finset.mem_univ j)⟩
    have hli := (Pi.basisFun ℝ (Fin d)).linearIndependent.map'
      (e.toLinearMap ∘ₗ Matrix.vecMulLinear R⁻¹) (LinearMap.ker_eq_bot.mpr hinj)
    have hfun : (fun j => hZ (Pi.single j 1)) =
        ⇑(e.toLinearMap ∘ₗ Matrix.vecMulLinear R⁻¹) ∘ ⇑(Pi.basisFun ℝ (Fin d)) := by
      funext j
      rw [hh, hcast]
      show _ = e ((Pi.basisFun ℝ (Fin d) j) ᵥ* R⁻¹)
      rw [Pi.basisFun_apply]
    rw [hfun]
    exact hli
  have hs2nn : 0 ≤ PI.succMin (PI.dualZ (LinearMap.range g)) d := by
    unfold PI.succMin
    exact le_csInf (by exact hne2) (fun x hx => hx.1)
  have hS2 : PI.succMin (PI.dualZ (LinearMap.range g)) d ≤ d / μ := by
    rw [le_div_iff₀ hμ]
    nlinarith [hT, hS1, hs2nn]
  have hlt : PI.succMin (PI.dualZ (LinearMap.range g)) d < d / μ + δ := by linarith
  unfold PI.succMin at hlt
  obtain ⟨b, ⟨hb0, v, hvD, hvli, hvb⟩, hb⟩ := exists_lt_of_csInf_lt (by exact hne2) hlt
  have hvD' : ∀ j, ∀ y ∈ LinearMap.range g, ∃ z : ℤ, inner ℝ (v j) y = (z : ℝ) :=
    fun j => hvD j
  have hc : ∀ j k, ∃ z : ℤ, inner ℝ (v j) (g (Pi.single k 1)) = (z : ℝ) :=
    fun j k => hvD' j _ (LinearMap.mem_range_self g _)
  choose c hc using hc
  have hv : ∀ j, v j = hZ (c j) := by
    intro j
    have hw : e.symm (v j) ᵥ* R = fun k => ((c j k : ℤ) : ℝ) := by
      funext k
      have h1 := hc j k
      rw [hg (Pi.single k 1), hcast k, ← e.apply_symm_apply (v j), hin,
        Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at h1
      exact h1
    calc v j = e (e.symm (v j)) := (e.apply_symm_apply _).symm
      _ = e ((e.symm (v j) ᵥ* R) ᵥ* R⁻¹) := by
        rw [Matrix.vecMul_vecMul, hRR', Matrix.vecMul_one]
      _ = hZ (c j) := by rw [hw, hh]
  have hliZ : LinearIndependent ℤ v :=
    hvli.restrict_scalars (fun a b hab => by simpa using hab)
  have hcli : LinearIndependent ℤ c := by
    apply LinearIndependent.of_comp hZ
    have hcomp : (hZ ∘ c) = v := funext fun j => (hv j).symm
    rw [hcomp]
    exact hliZ
  refine ⟨c, hcli, fun j => ?_⟩
  have hT' : ∀ x : Fin d → ℝ, (R⁻¹)ᵀ *ᵥ x = x ᵥ* R⁻¹ := by
    intro x
    rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]
  rw [hT', ← hnorm, ← hh (c j), ← hv j]
  have h3 := hvb j
  have h4 := norm_nonneg (v j)
  have hdm : 0 ≤ (d : ℝ) / μ := div_nonneg (Nat.cast_nonneg d) hμ.le
  nlinarith
end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
