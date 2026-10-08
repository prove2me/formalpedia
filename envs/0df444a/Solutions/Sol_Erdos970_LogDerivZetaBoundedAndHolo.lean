-- Prove2me | solution 1 for Erdos970.LogDerivZetaBoundedAndHolo
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:02:31.266985+00:00
-- url     : https://prove2.me/submissions/d70cf01d-2bbc-4cfa-b6fa-df501e2eddb4

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_Erdos970_LogDerivZetaBndUnif2
import Theorems.Thm_Erdos970_log_Deriv_Expansion_Zeta

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MellinCalculus
namespace Erdos970

open scoped _root_.ContDiff


open _root_.Complex _root_.Topology _root_.Filter _root_.Real _root_.MeasureTheory _root_.Set _root_.Function



variable {𝕂 : Type*} [RCLike 𝕂]








@[simp]
lemma Function.support_abs {α : Type*} (f : α → 𝕂) :
    (fun x ↦ ‖f x‖).support = f.support := by
  simp only [support, ne_eq]; simp_rw [norm_ne_zero_iff]

@[simp]
lemma Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  apply Function.support_comp_eq (g := ofReal); simp

















local notation (name := mellintransform) "𝓜" => mellin















@[fun_prop]
lemma DeltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by
  apply diffν.continuous.comp (g := ν) _ |>.div_const
  exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le


























end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Rectangle
namespace Erdos970

open _root_.Complex _root_.Set _root_.Topology

open scoped _root_.Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl





































end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.ResidueCalcOnRectangles
namespace Erdos970

open _root_.Complex _root_.BigOperators _root_.Nat _root_.Classical _root_.Real _root_.Topology _root_.Filter
open _root_.Set _root_.MeasureTheory _root_.intervalIntegral _root_.Asymptotics

open scoped _root_.Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}
















theorem existsDifferentiableOn_of_bddAbove [CompleteSpace E]
    {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c}))
    (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E),
      HolomorphicOn g s ∧ Set.EqOn f g (s \ {c}) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim
      else by simp [h]⟩







































lemma IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by
  simp only [isBigO_iff, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at f_near_p
  obtain ⟨c, hc⟩ := f_near_p
  dsimp [Filter.Eventually, nhdsWithin] at hc
  rw [mem_inf_principal'] at hc
  obtain ⟨U, hU, ⟨U_is_open, p_in_U⟩⟩ := mem_nhds_iff.mp hc
  use U
  constructor
  · exact IsOpen.mem_nhds U_is_open p_in_U
  · refine bddAbove_def.mpr ?_
    use c
    intro y hy
    simp only [Function.comp_apply, mem_image, Set.mem_sdiff, mem_singleton_iff] at hy
    obtain ⟨x, ⟨x_in_U, x_not_p⟩, fxy⟩ := hy
    rw [← fxy]
    simpa [x_not_p] using hU x_in_U






























end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Sobolev
namespace Erdos970

open _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap _root_.BigOperators
open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun




section lemmas




end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun



















end CS

namespace trunc







end trunc

namespace W1











end W1

namespace W21













end W21


end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Fourier
namespace Erdos970

open _root_.FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap VectorFourier _root_.BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]


@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl



@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas


@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.ZetaBounds
namespace Erdos970


open _root_.Complex _root_.Topology _root_.Filter _root_.Interval _root_.Set _root_.Asymptotics






local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

theorem ResidueOfTendsTo {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (hU : U ∈ 𝓝 p)
    (hf : HolomorphicOn f (U \ {p}))
    {A : ℂ}
    (h_limit : Tendsto (fun s ↦ (s - p) * f s) (𝓝[≠] p) (𝓝 A)) :
    ∃ V ∈ 𝓝 p,
    BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (V \ {p})) := by
                                                                
  have h_event : ∀ᶠ s in 𝓝[≠] p, ‖(s - p) * f s - A‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_nhds :
      ∀ᶠ s in 𝓝 p, s ≠ p → ‖(s - p) * f s - A‖ < 1 := by
    exact (eventually_nhdsWithin_iff).1 h_event
  rcases (eventually_nhds_iff.1 h_event_nhds) with ⟨V₀, hV₀_mem, hV₀_prop⟩
  have h_bound :
      ∀ s, s ∈ V₀ \ {p} → ‖(s - p) * f s‖ ≤ ‖A‖ + 1 := by
    intro s hs
    rcases hs with ⟨hV₀, hsne⟩
    calc ‖(s - p) * f s‖ = ‖((s - p) * f s - A) + A‖ := by
          ring_nf
        _ ≤ ‖(s - p) * f s - A‖ + ‖A‖ := norm_add_le ((s - p) * f s - A) A
        _ ≤ 1 + ‖A‖ := add_le_add_left (le_of_lt (hV₀_mem s hV₀ hsne)) ‖A‖
        _ = ‖A‖ + 1 := add_comm 1 ‖A‖
  have h_bdd :
      BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (V₀ \ {p})) := by
    refine ⟨‖A‖ + 1, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact h_bound s hs
                                                                 
  set W : Set ℂ := V₀ ∩ U with hW_def
  have hW_mem : (W : Set ℂ) ∈ 𝓝 p := inter_mem (IsOpen.mem_nhds hV₀_prop.1 hV₀_prop.2) hU
  have h_subset_V₀ : (W \ {p}) ⊆ (V₀ \ {p}) := by
    intro z hz; exact ⟨hz.1.1, hz.2⟩
  have h_prod_holo : HolomorphicOn (fun z ↦ (z - p) * f z) (W \ {p}) := by
    have h_id : HolomorphicOn (fun z : ℂ ↦ z - p) (W \ {p}) :=
      Differentiable.differentiableOn (Differentiable.sub_const differentiable_fun_id p)
    have hfW : HolomorphicOn f (W \ {p}) := by
      apply hf.mono
      exact Set.sdiff_subset_sdiff_left inter_subset_right
    simpa using! h_id.mul hfW
  have h_bdd_W : BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (W \ {p})) :=
    h_bdd.mono (image_mono h_subset_V₀)
                                                                    
  obtain ⟨g, hg_holo, hg_eq⟩ :=
    existsDifferentiableOn_of_bddAbove hW_mem h_prod_holo h_bdd_W
  have h_event_eq :
      (fun z ↦ g z) =ᶠ[𝓝[≠] p] fun z ↦ (z - p) * f z := by
    have hW_diff_mem : (W \ {p} : Set ℂ) ∈ 𝓝[≠] p :=
      sdiff_mem_nhdsWithin_compl hW_mem {p}
    exact (hg_eq.eventuallyEq_of_mem hW_diff_mem).symm
  have h_tendsto_gA : Tendsto g (𝓝[≠] p) (𝓝 A) :=
      h_limit.congr' (id (EventuallyEq.symm h_event_eq))
  have hpW : p ∈ W := by
    exact mem_of_mem_nhds hW_mem
  have h_cont_g : ContinuousAt g p := by
    apply (hg_holo.continuousOn.continuousWithinAt hpW).continuousAt hW_mem
  have h_tendsto_gp : Tendsto g (𝓝[≠] p) (𝓝 (g p)) :=
    h_cont_g.tendsto.mono_left inf_le_left
  have g_p_eq : g p = A :=
    tendsto_nhds_unique' (NormedField.nhdsNE_neBot p) h_tendsto_gp h_tendsto_gA
  let q : ℂ → ℂ := fun z ↦ (g z - A) / (z - p)
  have h_deriv : HasDerivAt g (deriv g p) p := by
    exact DifferentiableOn.hasDerivAt hg_holo hW_mem
  have h_q_limit : Tendsto q (𝓝[≠] p) (𝓝 (deriv g p)) := by
    rw [hasDerivAt_iff_tendsto_slope] at h_deriv
    unfold slope at h_deriv
    simp only [vsub_eq_sub, smul_eq_mul, inv_mul_eq_div, g_p_eq] at h_deriv
    exact h_deriv
  have h_event_q : ∀ᶠ z in 𝓝[≠] p, ‖q z - deriv g p‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_q_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_q_nhds : ∀ᶠ z in 𝓝 p, z ≠ p → ‖q z - deriv g p‖ < 1 := by
    simpa using (eventually_nhdsWithin_iff).1 h_event_q
  rcases (eventually_nhds_iff.1 h_event_q_nhds) with
    ⟨V₁, hV₁_mem, hV₁_prop⟩
  have h_q_bound :
      ∀ z, z ∈ V₁ \ {p} → ‖q z‖ ≤ ‖deriv g p‖ + 1 := by
    intro z hz
    rcases hz with ⟨hV₁, hz_ne⟩
    calc ‖q z‖ = ‖(q z - deriv g p) + (deriv g p)‖ := by
          ring_nf
        _ ≤ ‖q z - deriv g p‖ + ‖deriv g p‖ := norm_add_le (q z - deriv g p) (deriv g p)
        _ ≤ 1 + ‖deriv g p‖  := add_le_add_left (le_of_lt (hV₁_mem z hV₁ hz_ne)) ‖deriv g p‖
        _ = ‖deriv g p‖ + 1 := add_comm 1 ‖deriv g p‖
                                                   
  have h_eq_diff :
      EqOn (fun z ↦ f z - A * (z - p)⁻¹) q (W \ {p}) := by
    intro z hz
    simp only
    have hz_ne : (z - p) ≠ 0 := sub_ne_zero.mpr hz.2
    have hgz : g z = (z - p) * f z := by
      exact id (EqOn.symm hg_eq) hz
    simp only [hgz, q]
    field_simp
  apply IsBigO_to_BddAbove
  rw [isBigO_iff]
  use ‖deriv g p‖ + 1
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [IsOpen.mem_nhds hV₁_prop.1 hV₁_prop.2, hW_mem] with z hV₁ hW z_ne_p
  specialize h_eq_diff ⟨ hW, z_ne_p⟩
  simp only [Pi.sub_apply, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary,
    mul_one] at h_eq_diff ⊢
  rw [h_eq_diff]
  exact h_q_bound _ ⟨hV₁, z_ne_p⟩

theorem analyticAt_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
  AnalyticAt ℂ riemannZeta s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds s_ne_one] with z hz using differentiableAt_riemannZeta hz

theorem differentiableAt_deriv_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
    DifferentiableAt ℂ ζ' s := by
  exact (analyticAt_riemannZeta s_ne_one).deriv.differentiableAt

theorem riemannZetaResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (ζ - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  have zeta_holc : HolomorphicOn ζ (univ \ {1}) := by
    intro y hy
    exact DifferentiableAt.differentiableWithinAt <| differentiableAt_riemannZeta hy.2
  convert (preTransparency := .instances) ResidueOfTendsTo univ_mem zeta_holc riemannZeta_residue_one using 6
  simp

theorem deriv_eqOn_of_eqOn_punctured (f g : ℂ → ℂ) (U : Set ℂ) (p : ℂ)
    (hU_open : IsOpen U)
    (h_eq : EqOn f g (U \ {p})) :
    EqOn (deriv f) (deriv g) (U \ {p}) := by
  intro x hx
  apply EventuallyEq.deriv_eq
  filter_upwards [IsOpen.mem_nhds (hU_open.sdiff isClosed_singleton) hx] with t ht using h_eq ht

theorem analytic_deriv_bounded_near_point
    (f : ℂ → ℂ) {U : Set ℂ} {p : ℂ} (hU : IsOpen U) (hp : p ∈ U) (hf : HolomorphicOn f U) :
    (deriv f) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have U_in_filter : U ∈ 𝓝 p := by
    exact IsOpen.mem_nhds hU hp
  have T := (analyticOn_iff_differentiableOn hU).mpr hf
  have T2 : ContDiffOn ℂ 1 f U :=
      DifferentiableOn.contDiffOn hf hU
  have T3 : ContinuousOn (fun x ↦ ((deriv f) x)) U := by
    apply T2.continuousOn_deriv_of_isOpen hU (by simp)
  have T4 := T3.continuousAt U_in_filter
  have T5 : (deriv f) =O[𝓝 p] (1 : ℂ → ℂ) :=
    T4.norm.isBoundedUnder_le.isBigO_one ℂ
  exact Asymptotics.IsBigO.mono T5 inf_le_left

theorem derivative_const_plus_product {g : ℂ → ℂ} (A p x : ℂ) (hg : DifferentiableAt ℂ g x) :
    deriv ((fun _ ↦ A) + g * fun s ↦ s - p) x = deriv g x * (x - p) + g x := by
  rw [deriv_add (by fun_prop) (by fun_prop), deriv_const, deriv_mul hg (by fun_prop)]
  simp

lemma deriv_inv_sub {x p : ℂ} (hp : x ≠ p) :
  deriv (fun z => (z - p)⁻¹) x =  -((x - p) ^ 2)⁻¹ := by
  rw [deriv_fun_inv'' (by fun_prop) (by grind)]
  simp
  field

theorem deriv_f_minus_A_inv_sub_clean (f : ℂ → ℂ) (A x p : ℂ)
    (hf : DifferentiableAt ℂ f x) (hp : x ≠ p) :
    deriv (f  - (fun z ↦ A * (z - p)⁻¹)) x = deriv f x + A * ((x - p) ^ 2)⁻¹ := by
  have h1 : DifferentiableAt ℂ (fun z => (z - p)⁻¹) x := by
    fun_prop (disch := grind)
  rw [deriv_sub hf (h1.const_mul A), deriv_const_mul A h1, deriv_inv_sub hp]
  ring

theorem nonZeroOfBddAbove {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, IsOpen V ∧ ∀ s ∈ V \ {p}, f s ≠ 0 := by

  have h_decomp : ∀ s, f s = (f s - A * (s - p)⁻¹) + A * (s - p)⁻¹ := by
    intro s
    ring
                                      
  obtain ⟨M, hM⟩ := f_near_p

  have A_norm_pos : 0 < ‖A‖ := norm_pos_iff.mpr A_ne_zero
                                                                        
  let δ := ‖A‖ / (‖M‖ + 1)
  have δ_pos : 0 < δ := by
    refine div_pos A_norm_pos (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)
                                                                            
  obtain ⟨V, hV_open, hV_mem, hV_sub⟩ : ∃ V, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∩ Metric.ball p δ := by
                                     
    obtain ⟨W, hW_sub, hW_open, hW_mem⟩ := mem_nhds_iff.mp U_in_nhds
    let V := W ∩ Metric.ball p δ
    have VNp : V ∈ 𝓝 p := (𝓝 p).inter_mem (IsOpen.mem_nhds hW_open hW_mem)
      (Metric.ball_mem_nhds p δ_pos)
    exact ⟨V, IsOpen.inter hW_open Metric.isOpen_ball, mem_of_mem_nhds VNp,
      inter_subset_inter_left _ hW_sub⟩
  use V, mem_nhds_iff.mpr ⟨V, subset_refl V, hV_open, hV_mem⟩, hV_open
                    
  intro s hs
  have hs_in_U : s ∈ U := hV_sub hs.1 |>.1
  have hs_near_p : dist s p < δ := hV_sub hs.1 |>.2
  have hs_ne_p : s ≠ p := hs.2
                                                              
  rw [h_decomp s]
                                 
  have bound_first : ‖f s - A * (s - p)⁻¹‖ ≤ M := by
    apply hM
    exact ⟨s, ⟨hs_in_U, hs_ne_p⟩, rfl⟩
                                      
  have large_second : ‖M‖ + 1 < ‖A * (s - p)⁻¹‖ := by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    rw [lt_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs_ne_p))]
    rw [mul_comm, ← lt_div_iff₀ (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)]
    rw [dist_eq_norm_sub] at hs_near_p
    exact hs_near_p
                                                
  by_contra h_zero
                                                                  
  rw [add_eq_zero_iff_eq_neg] at h_zero
  rw [h_zero, norm_neg] at bound_first
                                    
  have : ‖M‖ + 1 < ‖M‖ := (lt_of_lt_of_le (lt_of_lt_of_le large_second bound_first)
    (Real.le_norm_self M))
  norm_num at this

theorem logDerivResidue' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_is_open : IsOpen U)
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by

  have simpleHolo : HolomorphicOn (fun s ↦ A / (s - p)) (U \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by rw [sub_ne_zero]; exact hx
    · rintro s ⟨_, hs⟩ ; exact hs

  have f_minus_pole_is_holomorphic : HolomorphicOn (f - (fun s ↦ A * (s - p)⁻¹)) (U \ {p}) := by
    exact (DifferentiableOn.sub_iff_right holc).mpr simpleHolo

  let ⟨g, ⟨g_is_holomorphic, g_is_f_minus_pole⟩⟩ := existsDifferentiableOn_of_bddAbove
    U_in_nhds f_minus_pole_is_holomorphic f_near_p

  let h := (fun _ ↦ A) + g * (fun (s : ℂ) ↦ (s - p))

  have linear_is_holomorphic : HolomorphicOn (fun (s : ℂ ) ↦ (s - p)) U := by
    exact DifferentiableOn.sub_const differentiableOn_id p

  have h_is_holomorphic : HolomorphicOn h U := by
    have T := DifferentiableOn.mul g_is_holomorphic linear_is_holomorphic
    exact DifferentiableOn.const_add A T

  have h_continuous : ContinuousOn h U :=
    by exact DifferentiableOn.continuousOn h_is_holomorphic

  have deriv_h_identity : ∀x ∈ (U \ {p}), (deriv h) x = f x + (deriv f x) * (x - p) := by
    intro x x_in_u_not_p
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff x_in_u_not_p
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2

    have weird : U ∈ 𝓝 x := by
      exact IsOpen.mem_nhds (U_is_open) (x_in_u)

    rw [derivative_const_plus_product, ← g_is_f_minus_pole x_in_u_not_p,
      ← deriv_eqOn_of_eqOn_punctured _ _ U p U_is_open g_is_f_minus_pole x_in_u_not_p,
      deriv_f_minus_A_inv_sub_clean]
    · simp only [Pi.sub_apply]
      have := sub_ne_zero_of_ne x_not_p
      field_simp
      ring
    · apply holc.differentiableAt
      exact Filter.inter_mem weird <| compl_singleton_mem_nhds x_not_p
    · exact x_not_p
    · exact g_is_holomorphic.differentiableAt weird
  have h_identity : ∀x ∈ (U \ {p}), h x = (f x) * (x - p)  := by
    intro x x_in_u_not_p
    have hyp_x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2
    simp only [h, Pi.add_apply, Pi.mul_apply]
    rw [← g_is_f_minus_pole x_in_u_not_p]
    simp only [Pi.sub_apply]
    field [sub_ne_zero.mpr hyp_x_not_p]
  have log_deriv_f_plus_pole_equal_log_deriv_h :
      EqOn (deriv f * f⁻¹ + fun s ↦ (s - p)⁻¹) ((deriv h) * h⁻¹) (U \ {p}) := by
    simp only [Set.mem_sdiff, mem_singleton_iff, ne_eq, and_imp, Function.comp_apply, Pi.sub_apply,
      DifferentiableOn.sub_iff_right, differentiableOn_const, DifferentiableOn.fun_sub_iff_left,
      holc] at *
    intro x hyp_x
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp hyp_x).2
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff hyp_x
    simp only [Pi.add_apply, Pi.mul_apply, Pi.inv_apply]
    rw [deriv_h_identity _ x_in_u x_not_p, h_identity _ x_in_u x_not_p]

    field [sub_ne_zero.mpr x_not_p, non_zero x (x_in_u) x_not_p]
  have h_inv_bounded :
      h⁻¹ =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    have : ContinuousAt h⁻¹ p := by
      apply ContinuousOn.continuousAt h_continuous U_in_nhds |>.inv₀
      simp [h, A_ne_zero]
    exact Asymptotics.IsBigO.mono (this.norm.isBoundedUnder_le.isBigO_one ℂ) inf_le_left

  have h_deriv_bounded :
        (deriv h) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
          analytic_deriv_bounded_near_point h U_is_open
            (by exact mem_of_mem_nhds U_in_nhds) h_is_holomorphic

  have h_log_deriv_bounded :
    ((deriv h) * h⁻¹) =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
      have T := Asymptotics.IsBigO.mul h_deriv_bounded h_inv_bounded
      exact IsBigO.of_const_mul_right T

  have u_not_p_in_filter : U \ {p} ∈ 𝓝[≠] p := by
    exact sdiff_mem_nhdsWithin_compl U_in_nhds {p}
  have T := Set.EqOn.eventuallyEq_of_mem log_deriv_f_plus_pole_equal_log_deriv_h u_not_p_in_filter
  exact EventuallyEq.trans_isBigO T h_log_deriv_bounded

theorem logDerivResidue {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    by
      let ⟨U', ⟨a,b,c⟩⟩ := mem_nhds_iff.mp U_in_nhds
      have W : (U' \ {p}) ⊆ U' := by
        exact Set.sdiff_subset

      have T : (U' \ {p}) ⊆ (U \ {p}) := by
        exact Set.sdiff_subset_sdiff a (subset_refl _)

      refine logDerivResidue' b ?_ ?_ (IsOpen.mem_nhds b c) A_ne_zero ?_
      · intro x hyp_x
        exact non_zero x <| T hyp_x
      · exact DifferentiableOn.mono holc T
      · exact (f_near_p.mono (image_mono (Set.sdiff_subset_sdiff a (subset_refl _))))

lemma BddAbove_to_IsBigO {f : ℂ → ℂ} {p : ℂ}
    {U : Set ℂ} (hU : U ∈ 𝓝 p) (bdd : BddAbove (norm ∘ f '' (U \ {p}))) :
    f =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
  dsimp [BddAbove, upperBounds] at bdd
  rcases bdd with ⟨C, hC⟩

  have h : ∀ x ∈ U \ {p}, ‖f x‖ ≤ C := by
    intro x hx
    have fx_is_norm : ‖f x‖ ∈ norm ∘ f ''(U \ {p}) := by
      exact ⟨x, hx, rfl⟩
    exact hC fx_is_norm

  rw [Asymptotics.isBigO_iff]
  use C
  rw [eventually_nhdsWithin_iff]
  simp only [Set.mem_sdiff, mem_singleton_iff, and_imp, mem_compl_iff, Pi.one_apply, one_mem,
    CStarRing.norm_of_mem_unitary, mul_one] at h ⊢
  filter_upwards [hU] using h

theorem logDerivResidue'' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, BddAbove (norm ∘ (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) '' (V \ {p})) := by
  apply IsBigO_to_BddAbove
  exact logDerivResidue non_zero holc U_in_nhds A_ne_zero f_near_p


theorem riemannZetaLogDerivResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (-(ζ' / ζ) - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  obtain ⟨U,U_in_nhds, hU⟩ := riemannZetaResidue
  have hU' : BddAbove (norm ∘ (ζ - fun s ↦ 1 * (s - 1)⁻¹) '' (U \ {1})) := by
    simp only [Function.comp_apply, Pi.sub_apply, one_mul] at hU ⊢
    exact hU
  obtain ⟨V,V_in_nhds, V_is_open, hV⟩ := nonZeroOfBddAbove U_in_nhds one_ne_zero hU'
  let W := V ∩ interior U
  have hW : ∀ s ∈ W \ {1}, ζ s ≠ 0 := by
    intro s hs
    have s_in_V_diff : s ∈ V \ {1} := ⟨hs.1.1, hs.2⟩
    exact hV s s_in_V_diff
  have ζ_holc: HolomorphicOn ζ (W \ {1}) := by
    intro y hy
    simp only [Set.mem_sdiff, mem_singleton_iff] at hy
    refine DifferentiableAt.differentiableWithinAt ?_
    apply differentiableAt_riemannZeta hy.2
  have W_in_nhds : W ∈ 𝓝 1 := by
    refine inter_mem V_in_nhds ?_
    exact interior_mem_nhds.mpr U_in_nhds
  have := logDerivResidue'' hW ζ_holc W_in_nhds one_ne_zero
  have HW : BddAbove (norm ∘ (ζ - fun s ↦ (s - 1)⁻¹) '' (W \ {1})) := by
    obtain ⟨c, hc⟩ := bddAbove_def.mp hU
    apply bddAbove_def.mpr
    use c
    rintro y ⟨x, x_in_W, fxy⟩
    apply hc
    exact ⟨x, ⟨interior_subset x_in_W.1.2, x_in_W.2⟩, fxy⟩
  simp only [one_mul] at this
  have aux: ∀ a, ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by
    intro a
    calc ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖
         = ‖-((deriv ζ a / ζ a) + (a - 1)⁻¹)‖ := by ring_nf
       _ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by rw [norm_neg]
  simp only [Function.comp_apply, Pi.sub_apply] at hU
  simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, aux]
  apply this HW

theorem riemannZetaLogDerivResidueBigO :
    (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
  obtain ⟨U, hU, bdd⟩ := riemannZetaLogDerivResidue
  convert (preTransparency := .instances) BddAbove_to_IsBigO hU bdd using 2
  rw [neg_div]


local notation (name := riemannzeta0) "ζ₀" => riemannZeta0





























































































































lemma LogDerivZetaHoloOn {S : Set ℂ} (s_ne_one : 1 ∉ S)
    (nonzero : ∀ s ∈ S, ζ s ≠ 0) :
    HolomorphicOn (fun s ↦ ζ' s / ζ s) S := by
  apply DifferentiableOn.div _ _ nonzero <;> intro s hs <;> apply DifferentiableAt.differentiableWithinAt
  · apply differentiableAt_deriv_riemannZeta
    exact ne_of_mem_of_not_mem hs s_ne_one
  · apply differentiableAt_riemannZeta
    exact ne_of_mem_of_not_mem hs s_ne_one




open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
                                                              



end Erdos970

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.PNT1_ComplexAnalysis
namespace Erdos970






lemma lem_exprule (n : ℕ) (hn : n ≥ 1) (α β : ℂ) : (n : ℂ) ^ (α + β) = (n : ℂ) ^ α * (n : ℂ) ^ β := by
  apply Complex.cpow_add
                              
  rw [Nat.cast_ne_zero]
                        
  rw [← Nat.one_le_iff_ne_zero]
  exact hn

lemma lem_realbw (b : ℝ) (w : ℂ) : (b * w).re = b * w.re := by
  exact Complex.re_ofReal_mul b w


lemma lem_Euler (a : ℝ) : Complex.exp (a * Complex.I) = Real.cos a + Real.sin a * Complex.I := by
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma lem_Reecos (a : ℝ) : (Complex.exp (a * Complex.I)).re = Real.cos a := by
  rw [lem_Euler]
  rw [Complex.add_re]
  rw [Complex.ofReal_re]
  rw [Complex.re_ofReal_mul]
  rw [Complex.I_re]
  simp


lemma lem_coseven (a : ℝ) : Real.cos (-a) = Real.cos a := by
  exact Real.cos_neg a

lemma lem_coseveny (n : ℕ) (_hn : n ≥ 1) (y : ℝ) : Real.cos (-y * Real.log (n : ℝ)) = Real.cos (y * Real.log (n : ℝ)) := by
  rw [neg_mul]
  exact lem_coseven (y * Real.log (n : ℝ))

lemma lem_niyelog (n : ℕ) (hn : n ≥ 1) (y : ℝ) : (n : ℂ) ^ (-y * Complex.I) = Complex.exp (-y * Complex.I * Real.log (n : ℝ)) := by
                                
  have h1 : (n : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    rw [← Nat.one_le_iff_ne_zero]
    exact hn
                                                     
  rw [Complex.cpow_def_of_ne_zero h1]

  rw [← Complex.natCast_log]

  ring_nf

lemma lem_eacosalog (n : ℕ) (_hn : n ≥ 1) (y : ℝ) : (Complex.exp (-y * Complex.I * Real.log (n : ℝ))).re = Real.cos (-y * Real.log (n : ℝ)) := by
                                  
  let a := -y * Real.log (n : ℝ)
                                               
  have h : -y * Complex.I * Real.log (n : ℝ) = a * Complex.I := by
    simp [a, mul_assoc, mul_comm Complex.I]
  rw [h]
                     
  exact lem_Reecos a

lemma lem_eacosalog2 (n : ℕ) (hn : n ≥ 1) (y : ℝ) : ((n : ℂ) ^ (-y * Complex.I)).re = Real.cos (-y * Real.log (n : ℝ)) := by
  rw [lem_niyelog n hn y]
  exact lem_eacosalog n hn y

lemma lem_eacosalog3 (n : ℕ) (hn : n ≥ 1) (y : ℝ) : ((n : ℂ) ^ (-y * Complex.I)).re = Real.cos (y * Real.log (n : ℝ)) := by
  rw [lem_eacosalog2 n hn y]
  exact lem_coseveny n hn y

lemma lem_cos2t (θ : ℝ) : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := by
  exact Real.cos_two_mul θ

lemma lem_cos2t2 (θ : ℝ) : 2 * Real.cos θ ^ 2 = 1 + Real.cos (2 * θ) := by
  rw [lem_cos2t]
  ring

lemma lem_cosSquare (θ : ℝ) : 2 * (1 + Real.cos θ)^2 = 2 + 4 * Real.cos θ + 2 * Real.cos θ^2 := by
  ring

lemma lem_cos2cos341 (θ : ℝ) : 2 * (1 + Real.cos θ) ^ 2 = 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [lem_cosSquare]
  rw [lem_cos2t2]
  ring

lemma lem_SquarePos (y : ℝ) : 0 ≤ y ^ 2 := by
  exact sq_nonneg y

lemma lem_SquarePos2 (y : ℝ) : 0 ≤ 2 * y ^ 2 := by
  apply mul_nonneg
  · norm_num
  · exact lem_SquarePos y

lemma lem_SquarePoscos (θ : ℝ) : 0 ≤ 2 * (1 + Real.cos θ) ^ 2 := by
  exact lem_SquarePos2 (1 + Real.cos θ)

lemma lem_postrig (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [← lem_cos2cos341]
  exact lem_SquarePoscos θ

lemma lem_postriglogn (n : ℕ) (_hn : n ≥ 1) (t : ℝ) : 0 ≤ 3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ)) := by
  rw [mul_assoc]
  exact lem_postrig (t * Real.log (n : ℝ))










lemma lem_abspos (z : ℂ) : z ≠ 0 → norm z > 0 := by
  intro h_ne_zero
  apply Real.sqrt_pos.mpr
  exact Complex.normSq_pos.mpr h_ne_zero

































































































































































































open _root_.Complex _root_.MeasureTheory _root_.intervalIntegral
open scoped _root_.Interval











































open _root_.Filter _root_.Topology



















open _root_.Classical
                                                                                      

















open scoped _root_.Topology






























end Erdos970

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.PNT2_LogDerivative
namespace Erdos970




open _root_.Filter _root_.Metric _root_.Set _root_.Bornology _root_.Function


open _root_.Classical

























































































lemma lem_three_gt_e : (3 : ℝ) > Real.exp 1 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : (2.7182818286 : ℝ) < 3 := by norm_num
  exact lt_trans h1 h2                                            












variable {R R1 r B : ℝ} {f : ℂ → ℂ} {h_σ : ℂ → (ℂ → ℂ)}
variable (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
variable (hR1_pos : 0 < R1)
variable (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
variable (h_f_zero : f 0 = 1)
variable (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
variable (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)


























































































end Erdos970

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.PNT3_RiemannZeta
namespace Erdos970


open scoped _root_.BigOperators _root_.Topology

lemma p_s_abs_1 (p : ℙ) (s : ℂ) (hs : 1 < s.re) : norm (((p : ℕ) : ℂ) ^ (-s : ℂ)) < 1 := by
                        
  have hx1 : 1 < ((p : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by
      exact_mod_cast (p.2.two_le : 2 ≤ (p : ℕ))
    exact lt_of_lt_of_le one_lt_two h2
  have hx0 : 0 < ((p : ℕ) : ℝ) := lt_trans zero_lt_one hx1
                                                                  
  have hnorm_eq : ‖(((p : ℕ) : ℂ) ^ (-s : ℂ))‖ = ((p : ℕ) : ℝ) ^ ((-s : ℂ).re) := by
    simpa using (Complex.norm_cpow_eq_rpow_re_of_pos hx0 (-s : ℂ))
                                                
  have hz : ((-s : ℂ).re) < 0 := by
    have h0 : 0 < s.re := lt_trans zero_lt_one hs
    have : -s.re < 0 := neg_lt_zero.mpr h0
    simpa using this
                                                           
  have hlt : ((p : ℕ) : ℝ) ^ ((-s : ℂ).re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hx1 hz
                                                   
  have : ‖(((p : ℕ) : ℂ) ^ (-s : ℂ))‖ < 1 := by simpa [hnorm_eq] using hlt
  simpa [norm] using this

lemma zetaEulerprod (s : ℂ) (hs : 1 < s.re) : Multipliable (fun p : ℙ => (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) ∧ riemannZeta s = ∏' p : ℙ, (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹ := by
  have hprod : HasProd (fun p : ℙ => (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) (riemannZeta s) := by
    simpa using (riemannZeta_eulerProduct_hasProd (s := s) hs)
  refine And.intro ?_ ?_
  · exact hprod.multipliable
  · simpa using (hprod.tprod_eq.symm)

lemma abs_of_tprod {P : Type*} (w : P → ℂ) (hw : Multipliable w) : norm (∏' p : P, w p) = ∏' p : P, norm (w p) := by exact Multipliable.norm_tprod hw

lemma abs_P_prod (s : ℂ) (hs : 1 < s.re) : norm (∏' p : ℙ, (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) = ∏' p : ℙ, norm ((1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := by
  have hw : Multipliable (fun p : ℙ => (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := (zetaEulerprod s hs).1
  simpa using abs_of_tprod (fun p : ℙ => (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) hw

lemma abs_zeta_prod (s : ℂ) (hs : 1 < s.re) : norm (riemannZeta s) = ∏' p : ℙ, norm ((1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := by
  rw [zetaEulerprod s hs |>.2, abs_P_prod s hs]

lemma abs_of_inv (z : ℂ) (_hz : z ≠ 0) : norm (z⁻¹) = (norm z)⁻¹ := norm_inv z

lemma one_minus_p_s_neq_0 (p : ℙ) (s : ℂ) (hs : 1 < s.re) : 1 - ((p : ℕ) : ℂ) ^ (-s : ℂ) ≠ 0 := by
  intro h
  have hz : ((p : ℕ) : ℂ) ^ (-s : ℂ) = 1 := by
    simpa using (sub_eq_zero.mp h).symm
  have : (1 : ℝ) < 1 := by
    simpa [hz] using (p_s_abs_1 p s hs)
  exact (lt_irrefl (1 : ℝ)) this

lemma abs_zeta_prod_prime (s : ℂ) (hs : 1 < s.re) :
  norm (riemannZeta s) = ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ)))⁻¹ := by
  rw [abs_zeta_prod s hs]
  congr 1
  ext p
  rw [abs_of_inv (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ)) (one_minus_p_s_neq_0 p s hs)]

lemma Re2s (s : ℂ) : (2 * s).re = 2 * s.re := by simp

lemma Re2sge1 (s : ℂ) (hs : 1 < s.re) : 1 < (2 * s).re := by
  rw [Re2s]
  linarith

lemma zeta_ratio_prod (s : ℂ) (hs : 1 < s.re) : riemannZeta (2 * s) / riemannZeta s = (∏' p : ℙ, (1 - ((p : ℕ) : ℂ) ^ (-(2 * s) : ℂ))⁻¹) / (∏' p : ℙ, (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := by
  have h2 := (zetaEulerprod (2 * s) (Re2sge1 s hs)).2
  have h1 := (zetaEulerprod s hs).2
  simp [h2, h1]

local notation "ι" => fun (z : ℂˣ) ↦ (z : ℂ)

theorem tprod_commutes_with_inclusion_infinite {α : Type*} (f : α → ℂˣ) (h : Multipliable f) :
    ι (tprod f) = tprod (fun i ↦ ι (f i)) :=
by
  change ((tprod f : ℂˣ) : ℂ) = tprod (fun i ↦ ((f i : ℂˣ) : ℂ))
  have hcont : Continuous (Units.coeHom ℂ) := by
    simpa using! (Units.continuous_val : Continuous (fun u : ℂˣ => ((u : ℂˣ) : ℂ)))
  simpa [Units.coeHom] using
    (Multipliable.map_tprod (f := f) (γ := ℂ) h (g := Units.coeHom ℂ) hcont)

theorem inclusion_commutes_with_division (a b : ℂˣ) :
    ι (a / b) = ι a / ι b := by
  exact Units.val_div_eq_div_val a b

lemma lift_multipliable_of_nonzero {P : Type*} (a : P → ℂ) (ha : Multipliable a) (h_a_nonzero : ∀ p, a p ≠ 0) (hA_nonzero' : ∀ A, HasProd a A → A ≠ 0):
  Multipliable (fun p ↦ Units.mk0 (a p) (h_a_nonzero p)) := by

  obtain ⟨A, hA⟩ := ha
  have hA_nonzero := hA_nonzero' A hA
  refine ⟨Units.mk0 A hA_nonzero, ?_⟩
  simp [HasProd, tendsto_nhds] at hA ⊢
  intro sU h_sU_open hA_mem
  have hA_im_mem : ι (Units.mk0 A hA_nonzero) ∈ ι '' sU := Set.mem_image_of_mem ι hA_mem
  have sU_im_open : IsOpen (ι '' sU) := by
    apply (Topology.IsOpenEmbedding.isOpen_iff_image_isOpen ?_).mp
    assumption
    exact Units.isOpenEmbedding_val
  have := hA (ι '' sU) sU_im_open hA_im_mem
  obtain ⟨a1, ha⟩ := this
  use a1
  intro b ha1
  obtain ⟨x', x'_spec_mem, x'_spec_eq⟩ := ha b ha1
  suffices x' = ∏ b ∈ b, Units.mk0 (a b) (by simp [*]) by
    rwa [← this]
  have : Units.mk0 (ι x') (Units.ne_zero x') = x' :=
    Units.mk0_val x' (Units.ne_zero x')
  have this2 : (Units.mk0 (∏ b ∈ b, a b)
    (Finset.prod_ne_zero_iff.mpr fun a a_1 => h_a_nonzero a)) = x' :=
      Units.ext (id (Eq.symm x'_spec_eq))
  rw [Units.mk0_prod] at this2
  rw [←this2]
  conv =>
    rhs
    rw [← Finset.prod_attach]

lemma prod_of_ratios_simplified {P : Type*} (a b : P → ℂ)
(ha : Multipliable a) (hb : Multipliable b)
    (h_a_nonzero : ∀ p, a p ≠ 0) (h_b_nonzero : ∀ p, b p ≠ 0) (hA_nonzero' : ∀ A, HasProd a A → A ≠ 0) (hB_nonzero' : ∀ A, HasProd b A → A ≠ 0):
  (∏' p : P, a p) / (∏' p : P, b p) = ∏' p : P, (a p / b p) := by
                                                                      
  let a' : P → ℂˣ := fun p ↦ Units.mk0 (a p) (h_a_nonzero p)
  let b' : P → ℂˣ := fun p ↦ Units.mk0 (b p) (h_b_nonzero p)

  have h_multipliable_a' : Multipliable a' := lift_multipliable_of_nonzero a ha h_a_nonzero hA_nonzero'
  have h_multipliable_b' : Multipliable b' := lift_multipliable_of_nonzero b hb h_b_nonzero hB_nonzero'
  have h_multipliable_a'_div_b' : Multipliable (fun p ↦ a' p / b' p) := Multipliable.div h_multipliable_a' h_multipliable_b'

  calc
    (∏' p, a p) / (∏' p, b p)
                                                         
    _ = (∏' p, ι (a' p)) / (∏' p, ι (b' p)) := by simp [a', b']
                                                                             
    _ = ι (∏' p, a' p) / ι (∏' p, b' p) := by simp [tprod_commutes_with_inclusion_infinite, *]
                                                              
    _ = ι ((∏' p, a' p) / (∏' p, b' p)) := by rw [← inclusion_commutes_with_division]
                                                                                                        
    _ = ι (∏' p, a' p / b' p) := by simp [Multipliable.tprod_div, *]
                                                                           
    _ = ∏' p, ι (a' p / b' p) := by simp [tprod_commutes_with_inclusion_infinite, *]
                                                                                   
    _ = ∏' p, (ι (a' p) / ι (b' p)) := by simp
                                                                         
    _ = ∏' p, a p / b p := by simp [a', b']

lemma prod_of_ratios {P : Type*} (a b : P → ℂ) (ha : Multipliable a) (hb : Multipliable b) (h_b_nonzero : ∀ p, b p ≠ 0) (hA_nonzero' : ∀ A, HasProd a A → A ≠ 0) (hB_nonzero' : ∀ B, HasProd b B → B ≠ 0):
  (∏' p : P, a p) / (∏' p : P, b p) = ∏' p : P, (a p / b p) := by
                                                         
  by_cases h_a_zero : ∃ p, a p = 0
  case pos =>

    have lhs_zero : ∏' p : P, a p = 0 := by
                                                                      
      exact tprod_of_exists_eq_zero h_a_zero
    have rhs_zero : ∏' p : P, (a p / b p) = 0 := by
                                                        
      obtain ⟨p₀, hp₀⟩ := h_a_zero
      have h_div_zero : ∃ p, (a p / b p) = 0 := by
        use p₀
        simp [hp₀]
      exact tprod_of_exists_eq_zero h_div_zero
    simp [lhs_zero, rhs_zero]
  case neg =>
                                  
    push Not at h_a_zero
                                                                          
    exact prod_of_ratios_simplified a b ha hb h_a_zero h_b_nonzero hA_nonzero' hB_nonzero'

lemma simplify_prod_ratio (s : ℂ) (hs : 1 < s.re) : (∏' p : ℙ, (1 - (p : ℂ) ^ (-(2 * s) : ℂ))⁻¹) / (∏' p : ℙ, (1 - (p : ℂ) ^ (-s : ℂ))⁻¹) = ∏' p : ℙ, ((1 - (p : ℂ) ^ (-(2 * s) : ℂ))⁻¹ / (1 - (p : ℂ) ^ (-s : ℂ))⁻¹) := by
                                                                                   
  let a := fun p : ℙ => (1 - (p : ℂ) ^ (-(2 * s) : ℂ))⁻¹
  let b := fun p : ℙ => (1 - (p : ℂ) ^ (-s : ℂ))⁻¹

  have ha : Multipliable a := (zetaEulerprod (2 * s) (Re2sge1 s hs)).1
  have hb : Multipliable b := (zetaEulerprod s hs).1

  have h_b_nonzero : ∀ p, b p ≠ 0 := by
    intro p
    exact inv_ne_zero (one_minus_p_s_neq_0 p s hs)

  exact prod_of_ratios a b ha hb h_b_nonzero (by
    intro A hA
                                 
    have h_eq : A = riemannZeta (2 * s) := by
      have h : HasProd a (riemannZeta (2 * s)) := by
        simpa [a] using riemannZeta_eulerProduct_hasProd (s := 2 * s) (by simp; linarith)
      exact HasProd.unique hA h
    rw [h_eq]
    exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  ) (by
  intro B hB
                                      
  have h_eq : B = riemannZeta s := by
    have h : HasProd b (riemannZeta s) := by
      simpa [b] using riemannZeta_eulerProduct_hasProd (s := s) hs
    exact HasProd.unique hB h
  rw [h_eq]
  exact riemannZeta_ne_zero_of_one_lt_re hs
  )

lemma zeta_ratios (s : ℂ) (hs : 1 < s.re) : riemannZeta (2 * s) / riemannZeta s = ∏' p : ℙ, ((1 - ((p : ℕ) : ℂ) ^ (-(2 * s) : ℂ))⁻¹ / (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := by
  have h1 := zeta_ratio_prod s hs
  have h2 := simplify_prod_ratio s hs
  exact h1.trans h2

lemma diff_of_squares (z : ℂ) : 1 - z^2 = (1 - z) * (1 + z) := by ring

lemma one_sub_ne_zero_of_abs_lt_one (z : ℂ) (hz : norm z < 1) : 1 - z ≠ 0 := by
  intro h
  have h1 : 1 = z := by
    have := congrArg (fun w : ℂ => w + z) h
    simpa [sub_add_cancel, zero_add] using this
  have habs1lt : norm (1 : ℂ) < 1 := by simpa [h1] using hz
  have hnorm1lt : ‖(1 : ℂ)‖ < 1 := by simp [norm] at habs1lt
  have : (1 : ℝ) < 1 := by simp [norm_one] at hnorm1lt
  exact (lt_irrefl _) this


lemma inv_mul_div_cancel_right_of_ne_zero (a b : ℂ) (ha : a ≠ 0) : ((a * b)⁻¹) / a⁻¹ = b⁻¹ := by
  simp [div_eq_mul_inv, inv_inv, mul_inv_rev, mul_comm, ha]

lemma ratio_invs (z : ℂ) (hz : norm z < 1) : (1 - z^2)⁻¹ / (1 - z)⁻¹ = (1 + z)⁻¹ := by
  have hz1 : 1 - z ≠ 0 := one_sub_ne_zero_of_abs_lt_one z hz
  simpa [diff_of_squares z] using
    inv_mul_div_cancel_right_of_ne_zero (1 - z) (1 + z) hz1

lemma complex_cpow_neg_two_mul (z w : ℂ) (_hz : z ≠ 0) : z^(-(2*w)) = (z^(-w))^2 := by
  have h1 : -(2*w) = 2*(-w) := by ring
  rw [h1]
  have h2 : (2 : ℂ)*(-w) = ((2 : ℕ) : ℂ)*(-w) := by norm_cast
  rw [h2, Complex.cpow_nat_mul]

theorem zeta_ratio_identity (s : ℂ) (hs : 1 < s.re) : riemannZeta (2 * s) / riemannZeta s = ∏' p : ℙ, (1 + ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹ := by
  rw [zeta_ratios s hs]; congr 1; ext p
  have hp : ((p : ℕ) : ℂ) ≠ 0 := by rw [ne_eq, Nat.cast_eq_zero]; exact Nat.Prime.ne_zero p.2
  have h1 : ((p : ℕ) : ℂ) ^ (-(2 * s)) = (((p : ℕ) : ℂ) ^ (-s))^2 := complex_cpow_neg_two_mul ((p : ℕ) : ℂ) s hp
  have h2 : norm (((p : ℕ) : ℂ) ^ (-s)) < 1 := p_s_abs_1 p s hs
  rw [h1]; exact ratio_invs (((p : ℕ) : ℂ) ^ (-s)) h2

lemma two_mul_ofReal_div_two (r : ℝ) : (2 : ℂ) * ((r : ℝ) / 2 : ℂ) = (r : ℂ) := by
  have hreal : (2 : ℝ) * (r / 2) = r := by
    calc
      (2 : ℝ) * (r / 2) = (2 : ℝ) * r / 2 := by
        have h : (2 : ℝ) * r / 2 = (2 : ℝ) * (r / 2) := by
          simpa using (mul_div_assoc (2 : ℝ) r (2 : ℝ))
        simpa using h.symm
      _ = r := by
        simp
  calc
    (2 : ℂ) * ((r : ℝ) / 2 : ℂ)
        = ((2 * (r / 2) : ℝ) : ℂ) := by
              simp
    _ = (r : ℂ) := by simp [hreal]

lemma zeta_ratio_identity_ofReal_div_two (r : ℝ) (hr : 1 < ( ((r : ℝ) / 2 : ℂ) ).re) : riemannZeta (r : ℂ) / riemannZeta ((r / 2 : ℝ) : ℂ) = ∏' p : ℙ, (1 + ((p : ℕ) : ℂ) ^ (-(((r : ℝ) / 2) : ℂ)))⁻¹ := by
  have h := zeta_ratio_identity (((r : ℝ) / 2 : ℂ)) hr
  simpa [two_mul_ofReal_div_two r] using h

lemma zeta_ratio_at_3_2 : riemannZeta 3 / riemannZeta ((3 : ℝ) / 2) = ∏' p : ℙ, (1 + ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)))⁻¹ := by
  have hr : 1 < (((3 : ℝ) / 2 : ℂ)).re := by
    simpa using (by norm_num : (1 : ℝ) < (3 : ℝ) / 2)
  simpa using zeta_ratio_identity_ofReal_div_two (3 : ℝ) hr

lemma triangle_inequality_specific (z : ℂ) : norm (1 - z) ≤ 1 + norm z := by
  simpa [sub_eq_add_neg, norm_one, norm_neg] using (norm_add_le (1 : ℂ) (-z))

lemma re_neg_eq_neg_re (s : ℂ) : (-s).re = - s.re := by
  simp

lemma abs_cpow_eq_rpow_re_of_pos {x : ℝ} (hx : 0 < x) (y : ℂ) : norm ((x : ℂ) ^ y) = x ^ y.re := by
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos hx y

lemma abs_p_pow_s (p : ℙ) (s : ℂ) : norm (((p : ℕ) : ℂ) ^ (-s : ℂ)) = ((p : ℕ) : ℝ) ^ (-s.re : ℝ) := by
  have hx : 0 < ((p : ℕ) : ℝ) := by
    exact_mod_cast (p.property.pos : 0 < (p : ℕ))
  simpa [Complex.ofReal_natCast, re_neg_eq_neg_re] using
    (abs_cpow_eq_rpow_re_of_pos hx (-s))

lemma abs_term_bound (p : ℙ) (t : ℝ) :
  norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))) ≤ 1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) := by
                                                              
  have h1 := triangle_inequality_specific (((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I)))
                                                                                    
  have h2 := abs_p_pow_s p (((3 : ℝ) / 2) + t * Complex.I)
                                  
  have h3 : (((3 : ℝ) / 2) + t * Complex.I).re = ((3 : ℝ) / 2) := by simp [Complex.add_re, Complex.ofReal_re]
                                    
  have h4 : -(((3 : ℝ) / 2) + t * Complex.I).re = -((3 : ℝ) / 2) := by rw [h3]
                       
  have h5 : norm (((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))) = ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) := by
    rw [h2, h4]
                
  rw [h5] at h1
  exact h1

lemma inv_inequality {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  simpa [one_div] using (one_div_le_one_div_of_le ha hab)

lemma eq_of_one_sub_eq_zero (z : ℂ) (h : 1 - z = 0) : z = 1 := by
  rw [sub_eq_zero] at h
  exact h.symm

lemma condp32 (p : ℙ) (t : ℝ) : 1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I)) ≠ 0 := by
  intro h
  have hp_eq_one : ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I)) = 1 := eq_of_one_sub_eq_zero _ h
  let s := ((3 : ℝ) / 2) + t * Complex.I
  have hs : 1 < s.re := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero]
    norm_num
  have h_abs_lt : norm (((p : ℕ) : ℂ) ^ (-s)) < 1 := p_s_abs_1 p s hs
  have h_s_eq : ((p : ℕ) : ℂ) ^ (-s) = ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I)) := by simp only [s]
  rw [h_s_eq, hp_eq_one] at h_abs_lt
  have : norm (1 : ℂ) = 1 := by simp [norm]
  rw [this] at h_abs_lt
  exact lt_irrefl 1 h_abs_lt

lemma abs_term_inv_bound (p : ℙ) (t : ℝ) : (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ ≤ (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ := by
  have h1 := abs_term_bound p t
  have h2 := condp32 p t
  have h3 := lem_abspos _ h2
  exact inv_inequality h3 h1

open _root_.NNReal in
lemma prod_inequality {P : Type*} (a b : P → ℝ≥0) (ha : Multipliable a) (hb : Multipliable b)
  (hab : ∀ p : P, a p ≤ b p) :
  ∏' p : P, a p ≤ ∏' p : P, b p := by
  exact Multipliable.tprod_le_tprod hab ha hb

lemma multipliable_complex_abs_inv {i : Type*} (g : i → ℂ) (h_mult : Multipliable (fun i => (1 - g i)⁻¹)) (_h_nonzero : ∀ i, 1 - g i ≠ 0) : Multipliable (fun i => (norm (1 - g i))⁻¹) := by
                                                       
  have h_eq : (fun i => (norm (1 - g i))⁻¹) = (fun i => ‖1 - g i‖⁻¹) := by
    ext i
    simp
  rw [h_eq]
                                       
  have h_norm_mult : Multipliable (fun i => ‖(1 - g i)⁻¹‖) := Multipliable.norm h_mult
  have h_norm_eq : (fun i => ‖(1 - g i)⁻¹‖) = (fun i => ‖1 - g i‖⁻¹) := by
    ext i
    rw [norm_inv]
  rwa [← h_norm_eq]

lemma multipliable_positive_inv_powers (r : ℝ) (hr : 1 < r) : Multipliable (fun p : ℙ => (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹) := by
                                                                   
  have h_sum : Summable (fun p : ℙ => ((p : ℕ) : ℝ) ^ (-r)) := by
    rw [Nat.Primes.summable_rpow]
    linarith

  have h_log_sum : Summable (fun p : ℙ => Real.log (1 + ((p : ℕ) : ℝ) ^ (-r))) := by
    exact Real.summable_log_one_add_of_summable h_sum

  have h_log_inv_sum : Summable (fun p : ℙ => Real.log ((1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹)) := by
    have h_eq : (fun p : ℙ => Real.log ((1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹)) =
                (fun p : ℙ => -(Real.log (1 + ((p : ℕ) : ℝ) ^ (-r)))) := by
      ext p
      rw [Real.log_inv]
    rw [h_eq]
    exact Summable.neg h_log_sum

  have h_pos : ∀ p : ℙ, 0 < (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
    intro p
    apply inv_pos.mpr
    have h_ge : 0 ≤ ((p : ℕ) : ℝ) ^ (-r) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith

  exact Real.multipliable_of_summable_log h_pos h_log_inv_sum




lemma hasProd_nonneg_of_pos {i : Type*} (f : i → ℝ) (hpos : ∀ i, 0 < f i) (a : ℝ) (ha : HasProd f a) : 0 ≤ a := by
                                     
  have h_pos : ∀ s : Finset i, 0 < ∏ i ∈ s, f i := fun s => Finset.prod_pos (fun i _ => hpos i)
                                                         
  have h_nonneg : ∀ s : Finset i, 0 ≤ ∏ i ∈ s, f i := fun s => le_of_lt (h_pos s)
                                                 
  exact ge_of_tendsto ha (Filter.Eventually.of_forall h_nonneg)

lemma tendsto_finprod_coe_iff_tendsto_coe_finprod {i : Type*} (f : i → NNReal) (a : NNReal) :
  Filter.Tendsto (fun s => ∏ i ∈ s, (f i : ℝ)) Filter.atTop (𝓝 (a : ℝ)) ↔
  Filter.Tendsto ((fun x : NNReal => (x : ℝ)) ∘ (fun s => ∏ i ∈ s, f i)) Filter.atTop (𝓝 (a : ℝ)) := by
                                                                                           
  have h_comp : ((fun x : NNReal => (x : ℝ)) ∘ (fun s => ∏ i ∈ s, f i)) = (fun s => ↑(∏ i ∈ s, f i)) := by
    rfl
                                                                  
  have h_eq : (fun s => ∏ i ∈ s, (f i : ℝ)) = (fun s => ↑(∏ i ∈ s, f i)) := by
    ext s
    exact (NNReal.coe_prod s f).symm
                                                                   
  rw [h_comp, ← h_eq]

lemma pnt_nnreal_isEmbedding_coe : Topology.IsEmbedding (fun x : NNReal => (x : ℝ)) := by
  refine ⟨?_, NNReal.coe_injective⟩
                                                              
  exact Topology.IsInducing.subtypeVal

lemma HasProd.of_coe_hasProd {i : Type*} (f : i → NNReal) (a : NNReal) (h : HasProd (fun i => (f i : ℝ)) (a : ℝ)) : HasProd f a := by
                                                                                     
  have h_comp : Filter.Tendsto ((fun x : NNReal => (x : ℝ)) ∘ (fun s => ∏ i ∈ s, f i)) Filter.atTop (𝓝 (a : ℝ)) := by
    rw [← tendsto_finprod_coe_iff_tendsto_coe_finprod]
    exact h

  have h_embed : Topology.IsEmbedding (fun x : NNReal => (x : ℝ)) := pnt_nnreal_isEmbedding_coe

  exact h_embed.tendsto_nhds_iff.mpr h_comp

lemma hasProd_nnreal_of_coe {i : Type*} (g : i → NNReal) (b : NNReal) (h : HasProd (fun i => (g i : ℝ)) (b : ℝ)) : HasProd g b := by
  exact HasProd.of_coe_hasProd g b h

lemma multipliable_real_to_nnreal {i : Type*} (f : i → ℝ) (hpos : ∀ i, 0 < f i) (h_mult : Multipliable f) : Multipliable (fun i => ⟨f i, le_of_lt (hpos i)⟩ : i → NNReal) := by
                                         
  obtain ⟨a, ha⟩ := h_mult
                                                            
  have ha_nonneg : 0 ≤ a := hasProd_nonneg_of_pos f hpos a ha
                                   
  let a_nnreal : NNReal := ⟨a, ha_nonneg⟩
                                                           
  have h_coe_eq : (fun i => ((⟨f i, le_of_lt (hpos i)⟩ : NNReal) : ℝ)) = f := by
    ext i
    rfl
                                                             
  have ha_coe : HasProd (fun i => ((⟨f i, le_of_lt (hpos i)⟩ : NNReal) : ℝ)) (a_nnreal : ℝ) := by
    rw [h_coe_eq]
    simp only [a_nnreal]
    exact ha
                                                        
  have ha_nnreal : HasProd (fun i => ⟨f i, le_of_lt (hpos i)⟩) a_nnreal :=
    hasProd_nnreal_of_coe (fun i => ⟨f i, le_of_lt (hpos i)⟩) a_nnreal ha_coe
                                                  
  exact ⟨a_nnreal, ha_nnreal⟩

lemma nnreal_coe_tprod_eq_tprod_coe {i : Type*} (f : i → NNReal) (hf : Multipliable f) :
  ∏' i, (↑(f i) : ℝ) = ↑(∏' i, f i) := by
                                                                  
  have h_prod : HasProd f (∏' i, f i) := Multipliable.hasProd hf
                                                                               
  have h_map : HasProd (NNReal.toRealHom ∘ f) (NNReal.toRealHom (∏' i, f i)) :=
    HasProd.map h_prod NNReal.toRealHom NNReal.continuous_coe
                                                                                                     
  have h_comp : NNReal.toRealHom ∘ f = fun i => (↑(f i) : ℝ) := by
    ext i
    rfl
  have h_val : NNReal.toRealHom (∏' i, f i) = ↑(∏' i, f i) := rfl
                              
  rw [h_comp, h_val] at h_map
                                             
  exact HasProd.tprod_eq h_map

lemma nnreal_tprod_le_coe {i : Type*} (f g : i → NNReal) (hf : Multipliable f) (hg : Multipliable g) (h : ∏' i, f i ≤ ∏' i, g i) : ∏' i, (f i : ℝ) ≤ ∏' i, (g i : ℝ) := by
                                                               
  rw [nnreal_coe_tprod_eq_tprod_coe f hf, nnreal_coe_tprod_eq_tprod_coe g hg]
                                                                                               
  exact NNReal.coe_le_coe.mpr h

lemma abs_zeta_inequality (t : ℝ) :
  ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ ≤
  ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ := by

  have h_pos_left : ∀ p : ℙ, 0 < (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := by
    intro p
    apply inv_pos.mpr
    apply add_pos zero_lt_one
                                                             
    apply Real.rpow_pos_of_pos
    exact_mod_cast (p.property.pos : 0 < (p : ℕ))

  have h_pos_right : ∀ p : ℙ, 0 < (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ := by
    intro p
    apply inv_pos.mpr
                                                            
    rw [norm_pos_iff]
    exact condp32 p t

  have h_mult_left : Multipliable (fun p : ℙ => (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹) :=
    multipliable_positive_inv_powers ((3 : ℝ) / 2) (by norm_num : 1 < (3 : ℝ) / 2)

  have h_mult_right : Multipliable (fun p : ℙ => (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹) := by
    let s := ((3 : ℝ) / 2) + t * Complex.I
    have hs : 1 < s.re := by
      simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero]
      norm_num
                                               
    have h_euler := (zetaEulerprod s hs).1
    have h_nonzero : ∀ p : ℙ, 1 - ((p : ℕ) : ℂ) ^ (-s) ≠ 0 := fun p => condp32 p t
    exact multipliable_complex_abs_inv (fun p : ℙ => ((p : ℕ) : ℂ) ^ (-s)) h_euler h_nonzero

  let f : ℙ → NNReal := fun p => ⟨(1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹, le_of_lt (h_pos_left p)⟩
  let g : ℙ → NNReal := fun p => ⟨(norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹, le_of_lt (h_pos_right p)⟩

  have hf : Multipliable f := multipliable_real_to_nnreal _ h_pos_left h_mult_left
  have hg : Multipliable g := multipliable_real_to_nnreal _ h_pos_right h_mult_right

  have h_pointwise : ∀ p : ℙ, f p ≤ g p := by
    intro p
    simp only [f, g]
    exact abs_term_inv_bound p t

  have h_nnreal_ineq : ∏' p, f p ≤ ∏' p, g p := prod_inequality f g hf hg h_pointwise

  have h_convert : ∏' p, (f p : ℝ) ≤ ∏' p, (g p : ℝ) := nnreal_tprod_le_coe f g hf hg h_nnreal_ineq

  have h_eq_f : ∏' p, (f p : ℝ) = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := by
    rfl

  have h_eq_g : ∏' p, (g p : ℝ) = ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ := by
    rfl

  rw [h_eq_f, h_eq_g] at h_convert
  exact h_convert

lemma abs_zeta_ratio_eval : norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)) = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := by
                                                 
  have hratio := zeta_ratio_at_3_2
                                          
  let w : ℙ → ℂ := fun p => (1 + ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)))⁻¹
  let u : ℙ → ℝ := fun p => (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹
                                        
  have hu_mult : Multipliable u :=
    multipliable_positive_inv_powers ((3 : ℝ) / 2) (by norm_num : 1 < (3 : ℝ) / 2)
                                        
  have hw_eq : w = fun p : ℙ => (u p : ℂ) := by
    funext p
                                                                               
    have hx : 0 ≤ ((p : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (p : ℕ))
    have hcpow : (((((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2))) : ℝ) : ℂ)
        = ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)) := by
      simpa using (Complex.ofReal_cpow (x := ((p : ℕ) : ℝ)) (hx := hx) (y := -((3 : ℝ) / 2)))
    calc
      w p = (1 + ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)))⁻¹ := rfl
      _ = (1 + (((((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2))) : ℝ) : ℂ))⁻¹ := by
        simp [hcpow]
      _ = (((1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ : ℝ) : ℂ) := by
        simp [Complex.ofReal_add, Complex.ofReal_inv, Complex.ofReal_one]
                                                                 
  have hw_mult : Multipliable w := by
    have hmap : Multipliable ((fun x : ℝ => (x : ℂ)) ∘ u) :=
      Multipliable.map (hf := hu_mult) Complex.ofRealHom Complex.continuous_ofReal
    simpa [hw_eq] using! hmap
                                            
  have h_abs_tprod : norm (∏' p : ℙ, w p) = ∏' p : ℙ, norm (w p) :=
    abs_of_tprod w hw_mult
                                                               
  have h_abs_eq_fun : (fun p : ℙ => norm (w p)) = u := by
    funext p
              
    have hge : 0 ≤ ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) :=
      Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le (p : ℕ))) _
    have hpos : 0 < 1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) := by linarith
    have hnonneg : 0 ≤ u p := by
      have : 0 < (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := inv_pos.mpr hpos
      exact this.le
               
    simp [hw_eq, Complex.norm_real, abs_of_nonneg hnonneg]
                                                        
  have h_abs_ratio : norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
      = norm (∏' p : ℙ, w p) := by
    simpa [w] using congrArg norm hratio
  calc
    norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
        = norm (∏' p : ℙ, w p) := h_abs_ratio
    _ = ∏' p : ℙ, norm (w p) := h_abs_tprod
    _ = ∏' p : ℙ, u p := by simp [h_abs_eq_fun]
    _ = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := rfl

theorem zeta_lower_bound (t : ℝ) :
  norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)) ≤
    norm (riemannZeta (((3 : ℝ) / 2) + t * Complex.I)) := by
  have hs : 1 < (((3 : ℝ) / 2 : ℂ) + t * Complex.I).re := by
    simp only [Complex.add_re, Complex.mul_I_re]
    norm_num
  calc
    norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
        = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := abs_zeta_ratio_eval
    _ ≤ ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ :=
          abs_zeta_inequality t
    _ = norm (riemannZeta (((3 : ℝ) / 2 : ℂ) + t * Complex.I)) := by
          simpa using (abs_zeta_prod_prime (((3 : ℝ) / 2 : ℂ) + t * Complex.I) hs).symm

lemma summable_one_div_nat_add_rpow' {x : ℝ} (hx : 1 < x) : Summable (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)) := by
  have h := (Real.summable_one_div_nat_add_rpow (1 : ℝ) x).2 hx
  have h' : Summable (fun n : ℕ => (|((n : ℝ) + 1)| ^ x)⁻¹) := by
    simpa [one_div] using h
  have h2 : (fun n : ℕ => (|((n : ℝ) + 1)| ^ x)⁻¹) = (fun n : ℕ => (((n : ℝ) + 1) ^ x)⁻¹) := by
    funext n
    have hn : 0 ≤ (n : ℝ) + 1 := by
      have : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      exact add_nonneg this (show 0 ≤ (1 : ℝ) from zero_le_one)
    simp [abs_of_nonneg hn]
  have h'' : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ x)⁻¹) := by
    simpa [h2] using h'
  have h''' : Summable (fun n : ℕ => ((n + 1 : ℝ) ^ x)⁻¹) := by
    simpa [Nat.cast_add] using h''
  simpa [one_div] using h'''

lemma tsum_pos_of_pos_first_term {f : ℕ → ℝ} (hf : Summable f) (h0 : 0 < f 0) (hnonneg : ∀ n, 0 ≤ f n) : 0 < ∑' n, f n := by
  have hsum0 : ∑ n ∈ Finset.range 1, f n = f 0 := by
    simp
  have hpos_partial : 0 < ∑ n ∈ Finset.range 1, f n := by
    simpa [hsum0] using h0
  have hsumle : ∑ n ∈ Finset.range 1, f n ≤ ∑' n, f n := by
    have hnonneg' : ∀ n ∉ Finset.range 1, 0 ≤ f n := by
      intro n hn
      exact hnonneg n
    simpa using (hf.sum_le_tsum (s := Finset.range 1) hnonneg')
  exact lt_of_lt_of_le hpos_partial hsumle


lemma terms_nonneg (x : ℝ) : ∀ n : ℕ, 0 ≤ (1 : ℝ) / ((n + 1 : ℝ) ^ x) := by
  intro n
  have hposb' : 0 < ((n : ℝ) + 1) :=
    add_pos_of_nonneg_of_pos (show 0 ≤ (n : ℝ) from by exact_mod_cast (Nat.zero_le n)) zero_lt_one
  have hposb : 0 < ((n + 1 : ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_one] using hposb'
  have hdenpos : 0 < ((n + 1 : ℝ) ^ x) := by
    simpa using (Real.rpow_pos_of_pos hposb x)
  have hden_nonneg : 0 ≤ ((n + 1 : ℝ) ^ x) := le_of_lt hdenpos
  have hnum_nonneg : 0 ≤ (1 : ℝ) := le_of_lt (zero_lt_one : 0 < (1 : ℝ))
  exact div_nonneg hnum_nonneg hden_nonneg

lemma term_eq_ofRealC (x : ℝ) (n : ℕ) : (1 / ((n + 1 : ℂ) ^ (x : ℂ))) = ((1 / ((n + 1 : ℝ) ^ x) : ℝ) : ℂ) := by
  have hbase_nonneg : 0 ≤ (n + 1 : ℝ) := by
    have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have : 0 ≤ (n : ℝ) + 1 := add_nonneg hn (show 0 ≤ (1 : ℝ) from zero_le_one)
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hpow' : ((n + 1 : ℂ) ^ (x : ℂ)) = (((n + 1 : ℝ) ^ x : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow (x := (n + 1 : ℝ)) (hx := hbase_nonneg) (y := x)).symm
  have hdiv : (1 : ℂ) / (((n + 1 : ℝ) ^ x : ℝ) : ℂ) = ((1 / ((n + 1 : ℝ) ^ x) : ℝ) : ℂ) := by
    simp
  calc
    1 / ((n + 1 : ℂ) ^ (x : ℂ))
        = (1 : ℂ) / (((n + 1 : ℝ) ^ x : ℝ) : ℂ) := by simp [hpow']
    _ = ((1 / ((n + 1 : ℝ) ^ x) : ℝ) : ℂ) := hdiv



lemma im_tsum_ofReal (g : ℕ → ℝ) : (∑' n : ℕ, (g n : ℂ)).im = 0 := by
  have him := congrArg Complex.im (Complex.ofReal_tsum (L := SummationFilter.unconditional ℕ) (f := g)).symm
  have hz : (((∑' n : ℕ, g n) : ℝ) : ℂ).im = 0 := by
    simp
  exact Eq.trans him hz

lemma re_tsum_ofReal (g : ℕ → ℝ) : (∑' n : ℕ, (g n : ℂ)).re = ∑' n : ℕ, g n := by
  have h := congrArg Complex.re (Complex.ofReal_tsum (L := SummationFilter.unconditional ℕ) (f := g)).symm
  simpa [Complex.ofReal_re] using h

lemma zetapos (x : ℝ) (hx : 1 < x) : (riemannZeta x).im = 0 ∧ 0 < (riemannZeta x).re := by
  have hxC : 1 < (Complex.ofReal x).re := by simpa [Complex.ofReal_re] using hx
  have hz : riemannZeta (x : ℂ) = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (x : ℂ) :=
    zeta_eq_tsum_one_div_nat_add_one_cpow (s := (x : ℂ)) hxC
  have him : (riemannZeta x).im = 0 := by
    simpa [hz, term_eq_ofRealC x] using
      (im_tsum_ofReal (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)))
  have hre : (riemannZeta x).re = ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ x) := by
    simpa [hz, term_eq_ofRealC x] using
      (re_tsum_ofReal (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)))
  have hsum : Summable (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)) :=
    summable_one_div_nat_add_rpow' (x := x) hx
  have hpos0 : 0 < 1 / ((Nat.cast 0 + 1 : ℝ) ^ x) := by
    simp [zero_add]
  have hnonneg : ∀ n : ℕ, 0 ≤ 1 / ((n + 1 : ℝ) ^ x) := terms_nonneg x
  have hpos : 0 < ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ x) :=
    tsum_pos_of_pos_first_term hsum hpos0 hnonneg
  exact ⟨him, by simpa [hre] using hpos⟩

lemma zeta332pos : 0 < norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)) := by
  have h3 : (1 : ℝ) < 3 := by norm_num
  have h32 : (1 : ℝ) < (3 : ℝ) / 2 := by norm_num
  obtain ⟨h3im, h3repos⟩ := zetapos 3 h3
  obtain ⟨h32im, h32repos⟩ := zetapos ((3 : ℝ) / 2) h32
  have h3ne : riemannZeta (3 : ℝ) ≠ 0 := by
    intro hz
    exact (ne_of_gt h3repos) (by simpa using congrArg Complex.re hz)
  have h32ne : riemannZeta ((3 : ℝ) / 2) ≠ 0 := by
    intro hz
    exact (ne_of_gt h32repos) (by simpa using congrArg Complex.re hz)
  have hdivne : riemannZeta (3 : ℝ) / riemannZeta ((3 : ℝ) / 2) ≠ 0 :=
    div_ne_zero h3ne h32ne
  simpa using (norm_pos_iff.mpr hdivne)

lemma zeta_low_332 : ∃ a : ℝ, 0 < a ∧ ∀ t : ℝ, a ≤ norm (riemannZeta (((3 : ℝ) / 2) + t * Complex.I)) := by
  use norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
  exact ⟨zeta332pos, zeta_lower_bound⟩

open _root_.Real _root_.Set _root_.Filter _root_.Topology _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Topology

lemma one_div_nat_cpow_eq_ite_cpow_neg (s : ℂ) (hs : s ≠ 0) (n : ℕ) : 1 / (n : ℂ) ^ s = if n = 0 then 0 else (n : ℂ) ^ (-s) := by
  by_cases h : n = 0
  · simp [h, Complex.zero_cpow hs]
  · have hcalc : 1 / (n : ℂ) ^ s = (n : ℂ) ^ (-s) := by
      calc
        1 / (n : ℂ) ^ s = ((n : ℂ) ^ s)⁻¹ := by simp [one_div]
        _ = (n : ℂ) ^ (-s) := by simpa using (Complex.cpow_neg (n : ℂ) s).symm
    simpa [h] using hcalc

lemma lem_zetaLimit (s : ℂ) (hs : 1 < s.re) : riemannZeta s = ∑' n : ℕ, if n = 0 then 0 else (n : ℂ) ^ (-s) := by
  classical
  have hsne : s ≠ 0 := by
    intro h
    have hpos : 0 < s.re := lt_trans (show (0 : ℝ) < 1 from zero_lt_one) hs
    have hne : s.re ≠ 0 := ne_of_gt hpos
    simp [h] at hne
  have hz : riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s := zeta_eq_tsum_one_div_nat_cpow (s := s) hs
  simpa [one_div_nat_cpow_eq_ite_cpow_neg s hsne] using hz


lemma sum_Icc1_eq_sum_range_succ (N : ℕ) (g : ℕ → ℂ) :
  (∑ k ∈ Finset.Icc 1 N, g k) = ∑ n ∈ Finset.range N, g (n + 1) := by
  classical
                                                                  
  symm
  refine Finset.sum_bij (s := Finset.range N) (t := Finset.Icc 1 N)
    (f := fun n => g (n + 1)) (g := fun k => g k)
    (i := fun n (_hn : n ∈ Finset.range N) => n + 1)
    ?hi ?hinj ?hsurj ?hcongr
  · intro n hn
    have hlt : n < N := Finset.mem_range.mp hn
    have h1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have h2 : n + 1 ≤ N := Nat.succ_le_of_lt hlt
    exact (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  · intro a ha b hb h
                             
    simpa using Nat.succ_injective h
  · intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk1, hk2⟩
    refine ⟨k - 1, ?_, ?_⟩
    ·                      
      have hsucc : (k - 1) + 1 = k := Nat.sub_add_cancel hk1
      have hle : (k - 1) + 1 ≤ N := by simpa [hsucc] using hk2
      have hlt : k - 1 < N := lt_of_lt_of_le (Nat.lt_succ_self (k - 1)) hle
      exact Finset.mem_range.mpr hlt
    ·                  
      simp [Nat.sub_add_cancel hk1]
  · intro n hn
    rfl

lemma sum_Icc0_eq_sum_Icc1_of_zero (N : ℕ) (g : ℕ → ℂ) (h0 : g 0 = 0) :
  (∑ k ∈ Finset.Icc 0 N, g k) = ∑ k ∈ Finset.Icc 1 N, g k := by
  classical
  have hdecomp : insert (0 : ℕ) (Finset.Icc 1 N) = Finset.Icc 0 N := by
    simpa [Nat.succ_eq_add_one] using
      (Finset.insert_Icc_succ_left_eq_Icc (a := 0) (b := N) (h := Nat.zero_le N))
  have hnotmem : (0 : ℕ) ∉ Finset.Icc 1 N := by
    intro h
    rcases Finset.mem_Icc.mp h with ⟨h1, _h2⟩
    have : ¬ (1 ≤ (0 : ℕ)) := by decide
    exact this h1
  calc
    (∑ k ∈ Finset.Icc 0 N, g k)
        = ∑ k ∈ insert 0 (Finset.Icc 1 N), g k := by
            simp [hdecomp]
    _ = g 0 + ∑ k ∈ Finset.Icc 1 N, g k := by
            simp
    _ = ∑ k ∈ Finset.Icc 1 N, g k := by simp [h0]

lemma sum_Icc0_shifted_eq_sum_range (a : ℕ → ℂ) (m : ℕ) :
  (∑ k ∈ Finset.Icc 0 m, (if k = 0 then 0 else a k)) = ∑ n ∈ Finset.range m, a (n + 1) := by
  classical
  calc
    (∑ k ∈ Finset.Icc 0 m, (if k = 0 then 0 else a k))
        = ∑ k ∈ Finset.Icc 1 m, (if k = 0 then 0 else a k) := by
          simpa using
            (sum_Icc0_eq_sum_Icc1_of_zero (N := m)
              (g := fun k => (if k = 0 then 0 else a k)) (h0 := by simp))
    _ = ∑ n ∈ Finset.range m, (if n + 1 = 0 then 0 else a (n + 1)) := by
          simpa using
            (sum_Icc1_eq_sum_range_succ (N := m) (g := fun k => (if k = 0 then 0 else a k)))
    _ = ∑ n ∈ Finset.range m, a (n + 1) := by
          apply Finset.sum_congr rfl
          intro n hn
          simp

lemma sum_Icc0_shifted_floor_eq (a : ℕ → ℂ) (t : ℝ) :
  (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k = 0 then 0 else a k)) = ∑ n ∈ Finset.range ⌊t⌋₊, a (n + 1) := by
  simpa using (sum_Icc0_shifted_eq_sum_range a ⌊t⌋₊)








lemma lem_fDeriv (s : ℂ) (u : ℝ) (hu : 0 < u) :
    (let f := fun u : ℝ => (u : ℂ) ^ (-s)
     deriv f u = -s * (u : ℂ) ^ (-s - 1)) := by
                             
  show deriv (fun u : ℝ => (u : ℂ) ^ (-s)) u = -s * (u : ℂ) ^ (-s - 1)
  have hu_ne_zero : u ≠ 0 := ne_of_gt hu
  by_cases h : s = 0
  ·                                
    simp [h]
  ·                                
    have hneg_s_ne_zero : -s ≠ 0 := neg_ne_zero.mpr h
    exact Complex.deriv_ofReal_cpow_const hu_ne_zero hneg_s_ne_zero

lemma differentiable_integrable_cpow_on_Icc (s : ℂ) (a b : ℝ) (h0 : 0 < a) (_hle : a ≤ b) :
  (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun u : ℝ => (u : ℂ) ^ (-s)) t)
  ∧ IntegrableOn (deriv (fun u : ℝ => (u : ℂ) ^ (-s))) (Set.Icc a b) :=
by
  classical
                                                       
  set f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s)
  set g : ℝ → ℂ := fun u => -s * (u : ℂ) ^ (-s - 1)
                            
  have hpos_of_mem : ∀ {t : ℝ}, t ∈ Set.Icc a b → 0 < t := by
    intro t ht; exact lt_of_lt_of_le h0 ht.1
                                    
  have hdiff_at : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t := by
    intro t ht
    have ht_ne : t ≠ 0 := ne_of_gt (hpos_of_mem ht)
    by_cases hs : s = 0
    ·                   
      simp [f, hs]
    ·                                                        
      have hr : (-s) ≠ 0 := by simpa using (neg_ne_zero.mpr hs)
      have hhas : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) ((-s) * t ^ ((-s) - 1)) t :=
        hasDerivAt_ofReal_cpow_const (x := t) (hx := ht_ne) (r := -s) (hr := hr)
      exact hhas.differentiableAt
                             
  have hcont_pow : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Set.Icc a b) := by
    intro t ht
    have ht_ne : t ≠ 0 := ne_of_gt (hpos_of_mem ht)
    by_cases hzero : (-s - 1) = 0
    ·                       
      have : (fun u : ℝ => (u : ℂ) ^ (-s - 1)) = fun _ : ℝ => (1 : ℂ) := by
        funext u; simp [hzero]
      simpa [this] using (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℂ)) t).continuousWithinAt
    ·                                             
      have hr : (-s - 1) ≠ 0 := hzero
      have hcpow : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s - 1)) ((-s - 1) * t ^ ((-s - 1) - 1)) t :=
        hasDerivAt_ofReal_cpow_const (x := t) (hx := ht_ne) (r := -s - 1) (hr := hr)
      have hcont_at : ContinuousAt (fun u : ℝ => (u : ℂ) ^ (-s - 1)) t :=
        hcpow.differentiableAt.continuousAt
      simpa using hcont_at.continuousWithinAt
  have hcont_g : ContinuousOn g (Set.Icc a b) := by
    have hconst : ContinuousOn (fun _ : ℝ => (-s : ℂ)) (Set.Icc a b) := continuousOn_const
    simpa only [g, Pi.mul_def, neg_mul] using! hconst.mul hcont_pow
                                                                                  
  have hEqOn : EqOn (deriv f) g (Set.Icc a b) := by
    intro u hu
    have hu_pos : 0 < u := hpos_of_mem hu
    simpa [f, g] using (lem_fDeriv s u hu_pos)
                                                                                                            
  have hcont_deriv : ContinuousOn (deriv f) (Set.Icc a b) := by
                                            
    have hg_restr : Continuous ((Set.Icc a b).domRestrict g) := hcont_g.domRestrict
    have hEqRestr : (Set.Icc a b).domRestrict (deriv f) = (Set.Icc a b).domRestrict g := by
      funext x; exact hEqOn x.property
    have hderiv_restr : Continuous ((Set.Icc a b).domRestrict (deriv f)) := by
      simpa [hEqRestr] using hg_restr
    simpa [continuousOn_iff_continuous_domRestrict] using hderiv_restr
                                                              
  have hInt : IntegrableOn (deriv f) (Set.Icc a b) :=
    hcont_deriv.integrableOn_compact isCompact_Icc
  exact And.intro hdiff_at hInt

lemma intervalIntegral_congr_of_Ioc_eq (a b : ℝ) (h : a ≤ b)
  (f g : ℝ → ℂ)
  (hpt : ∀ u ∈ Set.Ioc a b, f u = g u) :
  (∫ u in a..b, f u) = ∫ u in a..b, g u := by
                                                                                
  have h1 : (∀ᵐ u ∂(MeasureTheory.volume), u ∈ Set.Ioc a b → f u = g u) := by
    refine Filter.Eventually.of_forall ?_;
    intro u hu; exact hpt u hu
  have hIocEmpty : Set.Ioc b a = (∅ : Set ℝ) := by
    simpa using! (Set.Ioc_eq_empty_of_le h)
  have h2 : (∀ᵐ u ∂(MeasureTheory.volume), u ∈ Set.Ioc b a → f u = g u) := by
    refine Filter.Eventually.of_forall ?_;
    intro u hu
    have : u ∈ (∅ : Set ℝ) := by simp [hIocEmpty] at hu
    exact this.elim
  simpa using
    (intervalIntegral.integral_congr_ae' (a := a) (b := b) (μ := MeasureTheory.volume)
      (f := f) (g := g) h1 h2)

lemma lem_applyAbel (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) * (N : ℂ) ^ (-s)
        - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
  classical
                   
  set f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s)
  let c : ℕ → ℂ := fun k => if k = 0 then 0 else (1 : ℂ)
                                             
  have hle : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hdiff_int :=
    differentiable_integrable_cpow_on_Icc (s := s) (a := (1 : ℝ)) (b := (N : ℝ))
      (h0 := by exact zero_lt_one) (_hle := hle)
  rcases hdiff_int with ⟨hdiff, hint⟩
                                                         
  have habel :=
    sum_mul_eq_sub_integral_mul₀' (c := c) (f := f) (m := N)
      (hc := by simp [c])
      (hf_diff := by intro t ht; simpa [f] using (hdiff t ht))
      (hf_int := by simpa [f] using hint)
                                         
  have hLHS : (∑ k ∈ Finset.Icc 0 N, f k * c k) = zetaPartialSum s N := by
                                    
    have h0 :
        (∑ k ∈ Finset.Icc 0 N, f k * c k) = ∑ k ∈ Finset.Icc 1 N, f k * c k := by
      simpa [c] using
        (sum_Icc0_eq_sum_Icc1_of_zero (N := N)
          (g := fun k => f k * c k) (h0 := by simp [c]))
    have h1 : (∑ k ∈ Finset.Icc 1 N, f k * c k)
                = ∑ n ∈ Finset.range N, f (n + 1) * c (n + 1) := by
      simpa using (sum_Icc1_eq_sum_range_succ (N := N) (g := fun k => f k * c k))
    have h2 : (∑ n ∈ Finset.range N, f (n + 1) * c (n + 1))
                = ∑ n ∈ Finset.range N, f (n + 1) := by
      apply Finset.sum_congr rfl; intro n hn; simp [c]
    calc
      (∑ k ∈ Finset.Icc 0 N, f k * c k)
          = ∑ k ∈ Finset.Icc 1 N, f k * c k := by simpa using h0
      _ = ∑ n ∈ Finset.range N, f (n + 1) * c (n + 1) := by simpa using h1
      _ = ∑ n ∈ Finset.range N, f (n + 1) := by simpa using h2
      _ = zetaPartialSum s N := by simp [zetaPartialSum, f]
                                                     
  have hset_to_interval :
      (∫ t in Set.Ioc (1 : ℝ) N, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
        = ∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k := by
    simpa using
      (intervalIntegral.integral_of_le
        (f := fun u => deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
        (μ := volume) hle).symm
  have hstep1 :
      zetaPartialSum s N
        = f N * (∑ k ∈ Finset.Icc 0 N, c k)
          - ∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k := by
    simpa [hLHS, hset_to_interval] using habel
                                                
  have hInt_congr :
      (∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
        = ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
                                                                             
    apply intervalIntegral_congr_of_Ioc_eq (a := (1 : ℝ)) (b := (N : ℝ)) (h := hle)
      (f := fun u => deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
      (g := fun u => (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)))
    intro u hu
    have hu_pos : 0 < u := lt_trans zero_lt_one hu.1
    have hderiv : deriv f u = -s * (u : ℂ) ^ (-s - 1) := by
      simpa [f] using (lem_fDeriv s u hu_pos)
                                          
    have hsumfloor : (∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k) = (Nat.floor u : ℂ) := by
      have hshift := sum_Icc0_shifted_floor_eq (a := fun _ => (1 : ℂ)) (t := u)
      have hsum : (∑ n ∈ Finset.range ⌊u⌋₊, (1 : ℂ)) = (Nat.floor u : ℂ) := by
        simp [Finset.sum_const, Finset.card_range]
      simpa [c, hsum] using hshift
    calc
      deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k
          = deriv f u * (Nat.floor u : ℂ) := by simp [hsumfloor]
      _ = (Nat.floor u : ℂ) * deriv f u := by simp [mul_comm]
      _ = (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by simp [hderiv]
                                     
  have hstep2 :
      zetaPartialSum s N
        = f N * (∑ k ∈ Finset.Icc 0 N, c k)
          - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
    simpa [hInt_congr] using hstep1
                                                      
  have hMain : f N * (∑ k ∈ Finset.Icc 0 N, c k) = (N : ℂ) * f N := by
    have hs : (∑ k ∈ Finset.Icc 0 N, c k) = ∑ n ∈ Finset.range N, (1 : ℂ) := by
      simpa [c] using (sum_Icc0_shifted_eq_sum_range (a := fun _ => (1 : ℂ)) (m := N))
    have hsumN : (∑ n ∈ Finset.range N, (1 : ℂ)) = (N : ℂ) := by
      simp [Finset.sum_const, Finset.card_range]
    calc
      f N * (∑ k ∈ Finset.Icc 0 N, c k)
          = f N * (∑ n ∈ Finset.range N, (1 : ℂ)) := by simp [hs]
      _ = f N * (N : ℂ) := by simp [hsumN]
      _ = (N : ℂ) * f N := by simp [mul_comm]
                                     
  have hfinal :
      zetaPartialSum s N
        = (N : ℂ) * (N : ℂ) ^ (-s)
          - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
    calc
      zetaPartialSum s N
          = f N * (∑ k ∈ Finset.Icc 0 N, c k)
              - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
            simpa using hstep2
      _ = (N : ℂ) * f N
              - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
            simp [hMain]
      _ = (N : ℂ) * (N : ℂ) ^ (-s)
              - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
            simp [f]
  exact hfinal



lemma helper_cpow_mul_cpow_neg_eq_cpow_sub (x s : ℂ) (hx : x ≠ 0) : x * x ^ (-s) = x ^ (1 - s) := by
  calc
    x * x ^ (-s) = x ^ (1 : ℂ) * x ^ (-s) := by
      simp [Complex.cpow_one]
    _ = x ^ (1 + (-s)) := by
      simpa using (Complex.cpow_add (x := x) (y := (1 : ℂ)) (z := (-s)) hx).symm
    _ = x ^ (1 - s) := by
      simp [sub_eq_add_neg]

lemma lem_zetaNsimplified1 (s : ℂ) (N : ℕ) (hN : 1 ≤ N) : zetaPartialSum s N = (N : ℂ) ^ (1 - s) + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
  have happly := lem_applyAbel s N hN
                                               
  have hInt :
      ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1))
        = (-s) * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
    simp [mul_left_comm]
  calc
    zetaPartialSum s N
        = (N : ℂ) * (N : ℂ) ^ (-s)
          - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
          simpa using happly
    _ = (N : ℂ) * (N : ℂ) ^ (-s)
          - ((-s) * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)) := by
          rw [hInt]
    _ = (N : ℂ) * (N : ℂ) ^ (-s)
          + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
          simp [sub_eq_add_neg, neg_mul]
    _ = (N : ℂ) ^ (1 - s)
          + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
          have hpos : 0 < N := (Nat.succ_le_iff).mp hN
          have hNz : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hpos)
          have hpow := helper_cpow_mul_cpow_neg_eq_cpow_sub (x := (N : ℂ)) (s := s) hNz
          simp [hpow]

lemma lem_floorUdecomp (u : ℝ) : (Int.floor u : ℝ) = u - Int.fract u := by exact (eq_sub_iff_add_eq).2 (Int.floor_add_fract u)

lemma lem_fracPartBound (u : ℝ) : 0 ≤ Int.fract u ∧ Int.fract u < 1 ∧ |Int.fract u| ≤ (1 : ℝ) := by
  constructor
  · exact Int.fract_nonneg u
  · constructor
    · exact Int.fract_lt_one u
    · have hnonneg : 0 ≤ Int.fract u := Int.fract_nonneg u
      have hle : Int.fract u ≤ (1 : ℝ) := le_of_lt (Int.fract_lt_one u)
      simpa [abs_of_nonneg hnonneg] using hle

lemma helper_continuousOn_cpow (r : ℂ) {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ r) (Set.Icc a b) := by
  classical
  intro t ht
  have ht_pos : 0 < t := lt_of_lt_of_le ha ht.1
  by_cases hr : r = 0
  ·              
    have hconst : (fun u : ℝ => (u : ℂ) ^ r) = fun _ => (1 : ℂ) := by
      funext u; simp [hr]
    simpa [hconst] using (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℂ)) t).continuousWithinAt
  ·                                        
    have hderiv : HasDerivAt (fun u : ℝ => (u : ℂ) ^ r) (r * t ^ (r - 1)) t :=
      hasDerivAt_ofReal_cpow_const (x := t) (hx := ne_of_gt ht_pos) (r := r) (hr := hr)
    exact hderiv.differentiableAt.continuousAt.continuousWithinAt

lemma helper_intervalIntegrable_mul_cpow_id (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
  classical
                          
  have hcont1 : ContinuousOn (fun u : ℝ => (u : ℂ)) (Set.Icc a b) :=
    (Complex.continuous_ofReal).continuousOn
  have hcont2 : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Set.Icc a b) :=
    helper_continuousOn_cpow (-s - 1) (lt_of_lt_of_le zero_lt_one ha) hab
  have hcont : ContinuousOn (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) (Set.Icc a b) :=
    hcont1.mul hcont2
                                                            
  have hint_on : IntegrableOn (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) (Set.Icc a b) :=
    hcont.integrableOn_compact isCompact_Icc
  have hint : IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
    simpa using
      (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) (a := a) (b := b)
        (f := fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) hab).2 hint_on
  exact hint

lemma helper_aestronglyMeasurable_kernel_Icc (s : ℂ) {a b : ℝ} :
  AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
    (volume.restrict (Icc a b)) := by
                                
  have hmeas_fract : Measurable (Int.fract : ℝ → ℝ) := by simpa using (measurable_fract : Measurable (Int.fract : ℝ → ℝ))
  have h1 : AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) (volume.restrict (Icc a b)) :=
    (Complex.measurable_ofReal.comp hmeas_fract).aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (volume.restrict (Icc a b)) := by
    have hmeas : Measurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) := by measurability
    exact hmeas.aestronglyMeasurable
  simpa using! (MeasureTheory.AEStronglyMeasurable.mul h1 h2)

lemma helper_intervalIntegrable_frac_kernel (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
  classical
                                             
  let μ := volume.restrict (Icc a b)
  set f : ℝ → ℂ := fun u => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
  set g : ℝ → ℝ := fun u => ‖(u : ℂ) ^ (-s - 1)‖
                       
  have hmeas : AEStronglyMeasurable f μ := by simpa [μ, f] using helper_aestronglyMeasurable_kernel_Icc (s := s) (a := a) (b := b)
                                  
  have hbound_ae : ∀ᵐ u ∂μ, ‖f u‖ ≤ g u := by
                                                  
    refine ((ae_restrict_iff' (μ := volume) (s := Icc a b)
      (p := fun u : ℝ => ‖f u‖ ≤ g u) measurableSet_Icc)).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro u hu
                    
    have hfract_le1 : ‖(Int.fract u : ℝ)‖ ≤ (1 : ℝ) := by
      simpa using (lem_fracPartBound u).2.2
                           
    have : ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ ‖(Int.fract u : ℝ)‖ * ‖(u : ℂ) ^ (-s - 1)‖ := by
      simp
    have : ‖f u‖ ≤ ‖(Int.fract u : ℝ)‖ * ‖(u : ℂ) ^ (-s - 1)‖ := by
      simp [f]
    have : ‖f u‖ ≤ 1 * ‖(u : ℂ) ^ (-s - 1)‖ :=
      le_trans this (mul_le_mul_of_nonneg_right hfract_le1 (by exact norm_nonneg _))
    simpa [g] using (by simpa [one_mul] using this)
                                             
  have hcont : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Icc a b) :=
    helper_continuousOn_cpow (-s - 1) (lt_of_lt_of_le zero_lt_one ha) hab
  have hg_int_on : IntegrableOn g (Icc a b) := by
    have hcont_norm : ContinuousOn g (Icc a b) := by
      simpa [g] using (hcont.norm)
    exact hcont_norm.integrableOn_compact isCompact_Icc
                    
  have hf0 : Integrable (fun _ : ℝ => (0 : ℂ)) μ := by simp [μ]
  have hg : Integrable g μ := by simpa [μ] using! hg_int_on
                                                        
  have hf : Integrable f μ :=
    MeasureTheory.integrable_of_norm_sub_le (μ := μ) hmeas hf0 hg
      (by
                                    
        have : ∀ᵐ u ∂μ, ‖(0 : ℂ) - f u‖ ≤ g u := by
          simpa [sub_eq_add_neg, norm_neg, μ, f, g] using hbound_ae
        simpa using this)
                                         
  have hf_on : IntegrableOn f (Icc a b) := by simpa [μ, f] using! hf
  simpa using
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) (a := a) (b := b)
      (f := f) hab).2 hf_on

lemma lem_integralSplit (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
      = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
  have hab : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
                                          
  have hcongr1 :
      (∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1))
        = ∫ u in (1 : ℝ)..N,
            ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1) := by
    apply intervalIntegral_congr_of_Ioc_eq (a := (1 : ℝ)) (b := (N : ℝ)) (h := hab)
    intro u hu
    have hu0 : 0 ≤ u := le_trans (by norm_num) (le_of_lt hu.1)
    have hfloorR : (Nat.floor u : ℝ) = (Int.floor u : ℝ) := by
      simpa using (natCast_floor_eq_intCast_floor (R := ℝ) (a := u) hu0)
    have hfloorC : (Nat.floor u : ℂ) = ((Int.floor u : ℝ) : ℂ) := by
      simpa using congrArg (fun x : ℝ => (x : ℂ)) hfloorR
    have hIFR : (Int.floor u : ℝ) = u - Int.fract u := lem_floorUdecomp u
    have hIFC : ((Int.floor u : ℝ) : ℂ) = ((u - Int.fract u : ℝ) : ℂ) :=
      congrArg (fun x : ℝ => (x : ℂ)) hIFR
    have : (Nat.floor u : ℂ) = ((u - Int.fract u : ℝ) : ℂ) := hfloorC.trans hIFC
    simp [this, sub_eq_add_neg]
                               
  have hcongr2 :
      (∫ u in (1 : ℝ)..N,
          ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1))
        = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
          - ∫ u in (1 : ℝ)..N, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
    have hI1 : IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume (1 : ℝ) (N : ℝ) :=
      helper_intervalIntegrable_mul_cpow_id (s := s) (a := (1 : ℝ)) (b := (N : ℝ)) (ha := le_rfl) (hab := hab)
    have hI2 : IntervalIntegrable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) volume (1 : ℝ) (N : ℝ) :=
      helper_intervalIntegrable_frac_kernel (s := s) (a := (1 : ℝ)) (b := (N : ℝ)) (ha := le_rfl) (hab := hab)
    have :
        (∫ u in (1 : ℝ)..N,
            ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1))
          = ∫ u in (1 : ℝ)..N,
              ((u : ℂ) * (u : ℂ) ^ (-s - 1)
                - ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) := by
      apply intervalIntegral_congr_of_Ioc_eq (a := (1 : ℝ)) (b := (N : ℝ)) (h := hab)
      intro u hu; simp [sub_mul]
    calc
      (∫ u in (1 : ℝ)..N,
          ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1))
          = ∫ u in (1 : ℝ)..N,
              ((u : ℂ) * (u : ℂ) ^ (-s - 1)
                - ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) := this
      _ = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
            - ∫ u in (1 : ℝ)..N, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) :=
        (intervalIntegral.integral_sub (μ := volume) (a := (1 : ℝ)) (b := (N : ℝ)) hI1 hI2)
                                              
  have hpow :
      (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
        = ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s) := by
    apply intervalIntegral_congr_of_Ioc_eq (a := (1 : ℝ)) (b := (N : ℝ)) (h := hab)
    intro u hu
    have hu_pos : 0 < u := lt_trans zero_lt_one hu.1
    have hux0 : (u : ℝ) ≠ 0 := ne_of_gt hu_pos
    have hcx0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hux0
    calc
      (u : ℂ) * (u : ℂ) ^ (-s - 1)
          = (u : ℂ) ^ (1 : ℂ) * (u : ℂ) ^ (-s - 1) := by simp [Complex.cpow_one]
      _ = (u : ℂ) ^ (1 + (-s - 1)) := by
        simpa using
          (Complex.cpow_add (x := (u : ℂ)) (y := (1 : ℂ)) (z := (-s - 1)) hcx0).symm
      _ = (u : ℂ) ^ (-s) := by
        simp [add_left_comm, sub_eq_add_neg]
             
  calc
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
        = ∫ u in (1 : ℝ)..N,
            ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1) := hcongr1
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
          - ∫ u in (1 : ℝ)..N, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := hcongr2
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
          - ∫ u in (1 : ℝ)..N, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
      simp [hpow]

lemma lem_zetaNsimplified2 (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s)
        + (s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - (s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) := by
  have hstep1: _ := lem_zetaNsimplified1 s N hN
  rw [lem_integralSplit] at hstep1
  rw [mul_sub] at hstep1
  rw [hstep1]
  exact (add_sub_assoc _ _ _).symm
  exact hN

lemma lem_evalMainIntegral (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) : s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s) = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by
  have h01leN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h0notIcc : (0 : ℝ) ∉ Set.Icc (1 : ℝ) (N : ℝ) := by
    intro hx
    exact (not_le.mpr (by norm_num : (0 : ℝ) < 1)) hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ) := by
    simp [uIcc_of_le h01leN]
  have hrne : -s ≠ (-1 : ℂ) := by
    intro h
    apply hs
    simpa using congrArg Neg.neg h
  have hint : ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = ((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1) := by
    have hcond : (-1 < (-s).re) ∨ (-s ≠ -1 ∧ (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ)) := by
      exact Or.inr ⟨hrne, h0not⟩
    simpa using (integral_cpow (a := (1 : ℝ)) (b := (N : ℝ)) (r := -s) hcond)
  have hmul : s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1)) := by
    simpa using congrArg (fun x => s * x) hint
  have hrewrite :
      s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1))
        = s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s)) := by
    have : s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1))
          = s * (((N : ℂ) ^ (1 - s) - (1 : ℂ) ^ (1 - s)) / (1 - s)) := by
      simp [add_comm, sub_eq_add_neg]
    have h1pow : (1 : ℂ) ^ (1 - s) = 1 := by simp
    simpa [h1pow] using this
  have hsplit : s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s))
      = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by
    have h1 : s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s))
        = (s * ((N : ℂ) ^ (1 - s) - 1)) / (1 - s) := by
      simpa using (mul_div_assoc s ((N : ℂ) ^ (1 - s) - 1) (1 - s)).symm
    have h2 : (s * ((N : ℂ) ^ (1 - s) - 1)) / (1 - s)
        = (s / (1 - s)) * ((N : ℂ) ^ (1 - s) - 1) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (div_mul_eq_mul_div (a := s) (b := (1 - s)) (c := ((N : ℂ) ^ (1 - s) - 1))).symm
    exact h1.trans h2
  calc
    s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
        = s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1)) := hmul
    _ = s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s)) := hrewrite
    _ = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := hsplit

lemma lem_zetaNfinal (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
        - s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
                                                                         
  have hstep := lem_zetaNsimplified2 s N hN
                                                       
  rw [lem_evalMainIntegral s hs N hN] at hstep

  have hden : (1 - s) ≠ 0 := by
    intro h
    have h1 : 1 = s := by simpa [sub_eq_zero] using h
    have h2 : s = 1 := h1.symm
    exact hs h2
  let A := (N : ℂ) ^ (1 - s)
                                                                             
  have h1 : (1 - s) * (A + s / (1 - s) * (A - 1)) = A - s := by
    calc
      (1 - s) * (A + s / (1 - s) * (A - 1))
          = (1 - s) * A + (1 - s) * (s / (1 - s) * (A - 1)) := by ring
      _ = (1 - s) * A + s * (A - 1) := by field_simp [hden]
      _ = A - s := by ring
  have h2 : (1 - s) * (A / (1 - s) + 1 + 1 / (s - 1)) = A - s := by
    have hne : s - 1 ≠ 0 := by simpa [sub_eq_zero] using hs
    field_simp [hden, hne]; ring
  have halg : A + s / (1 - s) * (A - 1) = A / (1 - s) + 1 + 1 / (s - 1) :=
    mul_left_cancel₀ hden (h1.trans h2.symm)

  rw [halg] at hstep
  exact hstep

lemma complex_tendsto_zero_iff_norm_tendsto_zero {α : Type*} {f : α → ℂ} {l : Filter α} :
    Tendsto f l (𝓝 0) ↔ Tendsto (fun x => ‖f x‖) l (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_zero_right]

lemma complex_norm_natCast_cpow (N : ℕ) (w : ℂ) (hN : 0 < N) :
    ‖(N : ℂ) ^ w‖ = (N : ℝ) ^ w.re := by
  have hNnz : (N : ℂ) ≠ 0 := by
    simp [Ne, Nat.cast_eq_zero]
    exact ne_of_gt hN
  rw [Complex.norm_cpow_of_ne_zero hNnz]
  rw [Complex.norm_natCast]
  rw [Complex.natCast_arg]
  simp [Real.exp_zero]

lemma tendsto_natCast_cpow_zero_of_neg_re (w : ℂ) (hw : w.re < 0) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ w) atTop (𝓝 0) := by
  rw [complex_tendsto_zero_iff_norm_tendsto_zero]
                                
  have h1 : ∀ᶠ (N : ℕ) in atTop, ‖(N : ℂ) ^ w‖ = (N : ℝ) ^ w.re := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact complex_norm_natCast_cpow N w hN
  rw [tendsto_congr' h1]

  have hw_pos : 0 < -w.re := neg_pos.mpr hw
                                 
  have h_eq : w.re = -(-w.re) := by ring
  rw [h_eq]
                                                                                               
  have h_comp : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h_rpow : Tendsto (fun x : ℝ => x ^ (-(-w.re))) atTop (𝓝 0) := tendsto_rpow_neg_atTop hw_pos
  exact Tendsto.comp h_rpow h_comp

lemma lem_limitTerm1 (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  apply tendsto_natCast_cpow_zero_of_neg_re
  simp only [Complex.sub_re, Complex.one_re]
  linarith

lemma lem_integrandBound (u : ℝ) (hu : 1 ≤ u) (s : ℂ) : ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1) := by
                  
  set a : ℂ := ((Int.fract u : ℝ) : ℂ)
  set b : ℂ := (u : ℂ) ^ (-s - 1)
                  
  have hfract_le1 : ‖a‖ ≤ (1 : ℝ) := by
    simpa [a, Complex.norm_real] using (lem_fracPartBound u).2.2
                          
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
                                                     
  have h₁ : ‖a * b‖ ≤ ‖a‖ * ‖b‖ := by simp
  have h₂ : ‖a‖ * ‖b‖ ≤ 1 * ‖b‖ :=
    mul_le_mul_of_nonneg_right hfract_le1 (norm_nonneg _)
  have h₃ : ‖a * b‖ ≤ 1 * ‖b‖ := le_trans h₁ h₂
  have hle : ‖a * b‖ ≤ ‖b‖ := by simpa [one_mul] using h₃
                                                                   
  have hb : ‖b‖ = u ^ ((-s - 1).re) := by
    simpa [b] using
      Complex.norm_cpow_eq_rpow_re_of_pos (x := u) (hx := hu0) (y := -s - 1)
                                           
  have hexp : (-s - 1).re = -s.re - 1 := by
    simp [sub_eq_add_neg]
                                                       
  calc
    ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖
        = ‖a * b‖ := rfl
    _ ≤ ‖b‖ := hle
    _ = u ^ ((-s - 1).re) := hb
    _ = u ^ (-s.re - 1) := by simp [hexp]

lemma lem_integrandBoundeps (ε : ℝ) (_hε : 0 < ε) (u : ℝ) (hu : 1 ≤ u) (s : ℂ) (hs : ε ≤ s.re) : ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-1 - ε) := by
  have h1 : ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1) := lem_integrandBound u hu s
  have h2 : -s.re - 1 ≤ -1 - ε := by linarith [hs]
  have h3 : u ^ (-s.re - 1) ≤ u ^ (-1 - ε) := Real.rpow_le_rpow_of_exponent_le hu h2
  exact le_trans h1 h3

lemma lem_triangleInequality_add (z₁ z₂ : ℂ) :
    ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := by
  exact norm_add_le z₁ z₂


lemma helper_integral_interval_sub_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b c : ℝ}
    (hab : IntervalIntegrable f volume a b) (hac : IntervalIntegrable f volume a c) :
    ((∫ x in a..b, f x) - ∫ x in a..c, f x) = ∫ x in c..b, f x := by
  simpa using
    (intervalIntegral.integral_interval_sub_left (μ := volume) (f := f) (a := a) (b := b) (c := c)
      hab hac)

lemma helper_integral_rpow_eval {ε : ℝ} (hε : 0 < ε) {m n : ℝ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∫ u in m..n, u ^ (-1 - ε) = (m ^ (-ε) - n ^ (-ε)) / ε := by
                                         
  have h0notIcc : (0 : ℝ) ∉ Set.Icc m n := by
    intro hx
    have : ¬ m ≤ 0 := not_le.mpr (lt_of_lt_of_le zero_lt_one hm)
    exact this hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc m n := by
    simpa [uIcc_of_le hmn] using h0notIcc
                              
  have hrne : (-1 - ε) ≠ (-1 : ℝ) := by
    intro h
    have hplus := congrArg (fun t => t + 1) h
    have hminus : -ε = 0 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hplus
    have hε0 : ε = 0 := by simpa using congrArg Neg.neg hminus
    exact (ne_of_gt hε) hε0
                                               
  have hint : ∫ u in m..n, u ^ (-1 - ε)
      = (n ^ ((-1 - ε) + 1) - m ^ ((-1 - ε) + 1)) / ((-1 - ε) + 1) := by
    have hcond : (-1 < (-1 - ε)) ∨ ((-1 - ε) ≠ -1 ∧ (0 : ℝ) ∉ Set.uIcc m n) := by
      exact Or.inr ⟨hrne, h0not⟩
    simpa using (integral_rpow (a := m) (b := n) (r := -1 - ε) hcond)
                                                      
  have h1 : ((-1 - ε) + 1) = -ε := by
    simp [sub_eq_add_neg, add_comm, add_left_comm]
  have : ∫ u in m..n, u ^ (-1 - ε)
      = (n ^ (-ε) - m ^ (-ε)) / (-ε) := by
    simpa [h1]
      using hint
  have hnegnum : -(n ^ (-ε) - m ^ (-ε)) = m ^ (-ε) - n ^ (-ε) := by
    simp
  calc
    ∫ u in m..n, u ^ (-1 - ε)
        = (n ^ (-ε) - m ^ (-ε)) / (-ε) := this
    _ = (n ^ (-ε) - m ^ (-ε)) * ((-ε)⁻¹) := by simp [div_eq_mul_inv]
    _ = (n ^ (-ε) - m ^ (-ε)) * (-(ε⁻¹)) := by simp [inv_neg]
    _ = -((n ^ (-ε) - m ^ (-ε)) * ε⁻¹) := by simp [mul_neg]
    _ = (-(n ^ (-ε) - m ^ (-ε))) * ε⁻¹ := by
      simpa using (neg_mul (n ^ (-ε) - m ^ (-ε)) (ε⁻¹)).symm
    _ = (m ^ (-ε) - n ^ (-ε)) * ε⁻¹ := by
      simp
    _ = (m ^ (-ε) - n ^ (-ε)) / ε := by simp [div_eq_mul_inv]

lemma helper_integral_rpow_le {ε : ℝ} (hε : 0 < ε) {m n : ℝ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∫ u in m..n, u ^ (-1 - ε) ≤ (1 / ε) * m ^ (-ε) := by
  have heval := helper_integral_rpow_eval (ε := ε) hε hm hmn
  have hn0 : 0 ≤ n := by
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    exact le_trans h01 (le_trans hm hmn)
  have hsub_le : m ^ (-ε) - n ^ (-ε) ≤ m ^ (-ε) := by
    exact sub_le_self _ (Real.rpow_nonneg hn0 (-ε))
  have hinv_nonneg : 0 ≤ ε⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt hε)
  have hdiv_le : ((m ^ (-ε) - n ^ (-ε)) / ε) ≤ (m ^ (-ε) / ε) := by
    have := mul_le_mul_of_nonneg_right hsub_le hinv_nonneg
    simpa [div_eq_mul_inv, mul_comm] using this
  calc
    ∫ u in m..n, u ^ (-1 - ε)
        = (m ^ (-ε) - n ^ (-ε)) / ε := heval
    _ ≤ m ^ (-ε) / ε := hdiv_le
    _ = (1 / ε) * m ^ (-ε) := by simp [div_eq_mul_inv, mul_comm]

lemma helper_tendsto_nat_rpow_neg (ε : ℝ) (hε : 0 < ε) :
  Tendsto (fun m : ℕ => (m : ℝ) ^ (-ε)) atTop (𝓝 0) := by
                                                                              
  have hcont : Tendsto (fun x : ℝ => x ^ (-ε)) atTop (𝓝 0) := by
                                                                              
    simpa using (tendsto_rpow_neg_atTop (y := ε) hε)

  have hcoe : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop

  have : Tendsto ((fun x : ℝ => x ^ (-ε)) ∘ fun n : ℕ => (n : ℝ)) atTop (𝓝 0) :=
    hcont.comp hcoe
                                       
  simpa using! this

lemma helper_exists_limit_of_tail_bound (a : ℕ → ℂ) (b : ℕ → ℝ)
    (hb_nonneg : ∀ m, 0 ≤ b m)
    (hb_tendsto : Tendsto b atTop (𝓝 0))
    (hbound : ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n → ‖a n - a m‖ ≤ b m) :
    ∃ l : ℂ, Tendsto a atTop (𝓝 l) := by
  classical
                                              
  have hCauchy : CauchySeq a := by
                                      
    refine (Metric.cauchySeq_iff).2 ?_
    intro ε hε
                                                               
    have h_ball : ∀ᶠ m in atTop, dist (b m) 0 < ε / 2 := by
      exact hb_tendsto (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε))
    have h_b_lt : ∀ᶠ m in atTop, b m < ε / 2 := by
      refine h_ball.mono ?_
      intro m hm
      have : |b m| < ε / 2 := by
        simpa [Metric.mem_ball, Real.dist_eq] using hm
      simpa [abs_of_nonneg (hb_nonneg m)] using this
                                  
    rcases eventually_atTop.1 hbound with ⟨M1, hM1⟩
    rcases eventually_atTop.1 h_b_lt with ⟨M2, hM2⟩
    let M := max M1 M2
    have hPM : ∀ᶠ n in atTop, M ≤ n → ‖a n - a M‖ ≤ b M := by
      have h' := hM1 M (le_max_left _ _)
      exact h'
    have hMb : b M < ε / 2 := hM2 M (le_max_right _ _)
    rcases eventually_atTop.1 hPM with ⟨N0, hN0⟩
    refine ⟨max N0 M, ?_⟩
    intro n hn k hk
    have hMn : M ≤ n := le_trans (le_max_right _ _) hn
    have hMk : M ≤ k := le_trans (le_max_right _ _) hk
    have hN0n : N0 ≤ n := le_trans (le_max_left _ _) hn
    have hN0k : N0 ≤ k := le_trans (le_max_left _ _) hk
    have h1 : ‖a n - a M‖ ≤ b M := (hN0 n hN0n) hMn
    have h2 : ‖a k - a M‖ ≤ b M := (hN0 k hN0k) hMk
                                           
    have htri : ‖a n - a k‖ ≤ ‖a n - a M‖ + ‖a M - a k‖ := by
      have h := norm_add_le (a n - a M) (a M - a k)
      simpa [sub_add_sub_cancel (a n) (a M) (a k)] using h
    have h2' : ‖a M - a k‖ ≤ b M := by simpa [norm_sub_rev] using h2
    have hsumle : ‖a n - a k‖ ≤ b M + b M :=
      le_trans htri (add_le_add h1 h2')
    have hsumlt : b M + b M < ε := by
      have := add_lt_add hMb hMb
      simpa [add_halves] using this
    have : ‖a n - a k‖ < ε := lt_of_le_of_lt hsumle hsumlt
    simpa [dist_eq_norm] using this
                                                 
  rcases cauchySeq_tendsto_of_complete (u := a) hCauchy with ⟨l, hl⟩
  exact ⟨l, hl⟩



lemma helper_intervalIntegrable_rpow_neg {ε : ℝ} {a b : ℝ} (_hε : 0 < ε)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => u ^ (-1 - ε)) volume a b := by
  have h0notIcc : (0 : ℝ) ∉ Set.Icc a b := by
    intro hx
    have : ¬ a ≤ 0 := not_le.mpr (lt_of_lt_of_le zero_lt_one ha)
    exact this hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc a b := by
    simpa [uIcc_of_le hab] using h0notIcc
  simpa using
    (intervalIntegral.intervalIntegrable_rpow (μ := volume) (a := a) (b := b) (r := -1 - ε)
      (Or.inr h0not))

lemma helper_one_le_of_mem_Ioc {m n u : ℝ} (hm : 1 ≤ m) (hu : u ∈ Ioc m n) : 1 ≤ u := by
  exact le_trans hm (le_of_lt hu.1)

lemma helper_integrableOn_of_bound_Ioc {m n : ℝ} {f : ℝ → ℂ} {g : ℝ → ℝ}
  (hmeas : AEStronglyMeasurable f (volume.restrict (Ioc m n)))
  (hbound : ∀ᵐ u ∂(volume.restrict (Ioc m n)), ‖f u‖ ≤ g u)
  (hg : IntegrableOn g (Ioc m n) volume) :
  IntegrableOn f (Ioc m n) volume := by
                                                                    
  let μ := volume.restrict (Ioc m n)
                    
  have hf0 : Integrable (fun _ : ℝ => (0 : ℂ)) μ := by
    simp
                             
  have hg' : Integrable g μ := by
    simpa [μ] using! hg
                                           
  have hmeas' : AEStronglyMeasurable f μ := by
    simpa [μ] using hmeas
                                               
  have hineq : ∀ᵐ u ∂μ, ‖(0 : ℂ) - f u‖ ≤ g u := by
    simpa [μ, sub_eq_add_neg, norm_neg] using hbound
                                                        
  have hf : Integrable f μ :=
    MeasureTheory.integrable_of_norm_sub_le (μ := μ) hmeas' hf0 hg' hineq
                                     
  simpa [μ] using! hf

lemma helper_aestronglyMeasurable_kernel_Ioc (s : ℂ) {m n : ℝ} :
  AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
    (volume.restrict (Ioc m n)) := by
                                                           
  have h1 : AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) (volume.restrict (Ioc m n)) := by
    have hmeas_fract : Measurable (Int.fract : ℝ → ℝ) := by
      simpa using (measurable_fract : Measurable (Int.fract : ℝ → ℝ))
    have hmeas_coe : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) :=
      (Complex.measurable_ofReal.comp hmeas_fract)
    exact hmeas_coe.aestronglyMeasurable
                                                        
  have h2 : AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (volume.restrict (Ioc m n)) := by
    have hmeas : Measurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) := by
      measurability
    exact hmeas.aestronglyMeasurable
                                             
  simpa using! (MeasureTheory.AEStronglyMeasurable.mul h1 h2)

lemma helper_aebound_kernel_Ioc {ε : ℝ} (hε : 0 < ε) (s : ℂ) (hs : ε ≤ s.re)
    {m n : ℝ} (hm : 1 ≤ m) (_hmn : m ≤ n) :
    ∀ᵐ u ∂(volume.restrict (Ioc m n)),
      ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-1 - ε) := by
                                                                                             
  refine
    ((ae_restrict_iff' (μ := volume) (s := Ioc m n)
        (p := fun u : ℝ => ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-1 - ε))
        measurableSet_Ioc)).2 ?_
                                                  
  refine Filter.Eventually.of_forall ?_
  intro u hu
  have hu1 : 1 ≤ u := helper_one_le_of_mem_Ioc hm hu
  simpa using (lem_integrandBoundeps ε hε u hu1 s hs)

lemma helper_integrableOn_rpow_neg_Ioc {ε : ℝ} (hε : 0 < ε)
    {m n : ℝ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    IntegrableOn (fun u : ℝ => u ^ (-1 - ε)) (Ioc m n) volume := by
  have hInt : IntervalIntegrable (fun u : ℝ => u ^ (-1 - ε)) volume m n :=
    helper_intervalIntegrable_rpow_neg (ε := ε) hε hm hmn
  exact
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (f := fun u : ℝ => u ^ (-1 - ε)) hmn).1 hInt




lemma helper_tendsto_const_mul_zero (c : ℝ) {f : ℕ → ℝ}
  (h : Tendsto f atTop (𝓝 0)) : Tendsto (fun n => c * f n) atTop (𝓝 0) := by
  simpa using (Filter.Tendsto.const_mul (b := c) h)

lemma helper_limit_norm_le_of_eventual_bound {a : ℕ → ℂ} {l : ℂ} {B : ℝ}
  (h : Tendsto a atTop (𝓝 l)) (hbound : ∀ᶠ n in atTop, ‖a n‖ ≤ B) : ‖l‖ ≤ B := by
  have hnorm : Tendsto (fun n => ‖a n‖) atTop (𝓝 ‖l‖) := (Filter.Tendsto.norm h)
  exact le_of_tendsto hnorm hbound

lemma lem_integralConvergence (ε : ℝ) (hε : 0 < ε) (s : ℂ) (hs : ε ≤ s.re) :
    ∃ I : ℂ,
      Tendsto
        (fun N : ℕ =>
          ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))
        atTop (𝓝 I)
      ∧ ‖I‖ ≤ (1 / ε) := by
  classical
                
  let fC : ℝ → ℂ := fun u => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
  let gR : ℝ → ℝ := fun u => u ^ (-1 - ε)
  let a : ℕ → ℂ := fun N => ∫ u in (1 : ℝ)..(N : ℝ), fC u
  let b : ℕ → ℝ := fun m => (1 / ε) * (m : ℝ) ^ (-ε)
          
  have hb_nonneg : ∀ m, 0 ≤ b m := by
    intro m
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have hpow : 0 ≤ (m : ℝ) ^ (-ε) := Real.rpow_nonneg hm0 _
    have hpos : 0 ≤ 1 / ε := by exact le_of_lt (one_div_pos.mpr hε)
    have := mul_le_mul_of_nonneg_left hpow hpos
    simpa [b] using this
          
  have hb_tendsto : Tendsto b atTop (𝓝 0) := by
    have hpow := helper_tendsto_nat_rpow_neg (ε := ε) hε
    have hmul := helper_tendsto_const_mul_zero (c := (1 / ε)) hpow
    simpa [b] using hmul
                                    
  have h_tail_pointwise : ∀ m n : ℕ, 1 ≤ m → m ≤ n → ‖a n - a m‖ ≤ b m := by
    intro m n hm1 hmn
                        
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
                                                                                     
    have hInt_f_1n : IntervalIntegrable fC volume (1 : ℝ) (n : ℝ) := by
                              
      have h1nNat : 1 ≤ n := le_trans hm1 hmn
      have h1nR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1nNat
      have hmeas := helper_aestronglyMeasurable_kernel_Ioc (s := s) (m := (1 : ℝ)) (n := (n : ℝ))
      have hgIntOn : IntegrableOn gR (Ioc (1 : ℝ) (n : ℝ)) volume :=
        helper_integrableOn_rpow_neg_Ioc (ε := ε) hε (m := (1 : ℝ)) (n := (n : ℝ)) (hm := by norm_num) (hmn := h1nR)
      have hbound := helper_aebound_kernel_Ioc (ε := ε) hε s hs (m := (1 : ℝ)) (n := (n : ℝ)) (hm := by norm_num) (_hmn := h1nR)
      have hintOn := helper_integrableOn_of_bound_Ioc (m := (1 : ℝ)) (n := (n : ℝ)) (f := fC) (g := gR)
        (hmeas := hmeas) (hbound := hbound) (hg := hgIntOn)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (a := (1 : ℝ)) (b := (n : ℝ)) (f := fC) h1nR).2 hintOn
    have hInt_f_1m : IntervalIntegrable fC volume (1 : ℝ) (m : ℝ) := by
      have hmeas := helper_aestronglyMeasurable_kernel_Ioc (s := s) (m := (1 : ℝ)) (n := (m : ℝ))
      have hgIntOn : IntegrableOn gR (Ioc (1 : ℝ) (m : ℝ)) volume :=
        helper_integrableOn_rpow_neg_Ioc (ε := ε) hε (m := (1 : ℝ)) (n := (m : ℝ)) (hm := by norm_num) (hmn := hmR)
      have hbound := helper_aebound_kernel_Ioc (ε := ε) hε s hs (m := (1 : ℝ)) (n := (m : ℝ)) (hm := by norm_num) (_hmn := hmR)
      have hintOn := helper_integrableOn_of_bound_Ioc (m := (1 : ℝ)) (n := (m : ℝ)) (f := fC) (g := gR)
        (hmeas := hmeas) (hbound := hbound) (hg := hgIntOn)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (a := (1 : ℝ)) (b := (m : ℝ)) (f := fC) hmR).2 hintOn
    have hdiff := helper_integral_interval_sub_left
      (E := ℂ) (f := fC) (a := (1 : ℝ)) (b := (n : ℝ)) (c := (m : ℝ))
      (hab := hInt_f_1n) (hac := hInt_f_1m)
    have hsub : a n - a m = ∫ u in (m : ℝ)..(n : ℝ), fC u := by
      simpa [a] using hdiff
                                                                      
    have hbound_Ioc := helper_aebound_kernel_Ioc (ε := ε) hε s hs
      (m := (m : ℝ)) (n := (n : ℝ)) (hm := hmR) (_hmn := hmnR)
    have hbound_Ioc_imp : ∀ᵐ t ∂(volume), t ∈ Ioc (m : ℝ) (n : ℝ) → ‖fC t‖ ≤ gR t := by
      simpa [fC, gR] using
        ((ae_restrict_iff' (μ := volume) (s := Ioc (m : ℝ) (n : ℝ)) measurableSet_Ioc).1 hbound_Ioc)
                                     
    have hgInt_mn : IntervalIntegrable gR volume (m : ℝ) (n : ℝ) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (a := (m : ℝ)) (b := (n : ℝ)) (f := gR) hmnR).2
        (helper_integrableOn_rpow_neg_Ioc (ε := ε) hε (m := (m : ℝ)) (n := (n : ℝ)) (hm := hmR) (hmn := hmnR))
                                      
    have h1 : ‖∫ u in (m : ℝ)..(n : ℝ), fC u‖ ≤ ∫ u in (m : ℝ)..(n : ℝ), gR u := by
      simpa using
        (intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
          (a := (m : ℝ)) (b := (n : ℝ)) (f := fC) (g := gR)
          (hab := hmnR) (h := hbound_Ioc_imp) (hbound := hgInt_mn))
                                            
    have h3 : ∫ u in (m : ℝ)..(n : ℝ), gR u ≤ (1 / ε) * (m : ℝ) ^ (-ε) :=
      helper_integral_rpow_le (ε := ε) hε (m := (m : ℝ)) (n := (n : ℝ)) (hm := hmR) (hmn := hmnR)
              
    have : ‖∫ u in (m : ℝ)..(n : ℝ), fC u‖ ≤ (1 / ε) * (m : ℝ) ^ (-ε) :=
      le_trans h1 h3
    simpa [hsub, b] using this
                        
  have hbound : ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n → ‖a n - a m‖ ≤ b m := by
    have h_m_ge1 : ∀ᶠ m in atTop, 1 ≤ m := eventually_ge_atTop 1
    refine h_m_ge1.mono ?_
    intro m hm1
    have h_n_ge_m : ∀ᶠ n in atTop, m ≤ n := eventually_ge_atTop m
    exact h_n_ge_m.mono (fun n hmn => by intro hle; exact h_tail_pointwise m n hm1 hle)
                           
  rcases helper_exists_limit_of_tail_bound a b hb_nonneg hb_tendsto hbound with ⟨I, hT⟩
                                    
  have h_eventual_bound : ∀ᶠ N in atTop, ‖a N‖ ≤ (1 / ε) := by
    have hN1 : ∀ᶠ N in atTop, 1 ≤ N := eventually_ge_atTop 1
    refine hN1.mono ?_
    intro N hNge1
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNge1
                                                                      
    have hbound_Ioc := helper_aebound_kernel_Ioc (ε := ε) hε s hs (m := (1 : ℝ)) (n := (N : ℝ)) (hm := by norm_num) (_hmn := h1N)
    have hbound_Ioc_imp : ∀ᵐ t ∂(volume), t ∈ Ioc (1 : ℝ) (N : ℝ) → ‖fC t‖ ≤ gR t := by
      simpa [fC, gR] using
        ((ae_restrict_iff' (μ := volume) (s := Ioc (1 : ℝ) (N : ℝ)) measurableSet_Ioc).1 hbound_Ioc)
                                     
    have hgInt_1N : IntervalIntegrable gR volume (1 : ℝ) (N : ℝ) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (a := (1 : ℝ)) (b := (N : ℝ)) (f := gR) h1N).2
        (helper_integrableOn_rpow_neg_Ioc (ε := ε) hε (m := (1 : ℝ)) (n := (N : ℝ)) (hm := by norm_num) (hmn := h1N))
                                      
    have h1 : ‖∫ u in (1 : ℝ)..(N : ℝ), fC u‖ ≤ ∫ u in (1 : ℝ)..(N : ℝ), gR u := by
      simpa [a] using
        (intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
          (a := (1 : ℝ)) (b := (N : ℝ)) (f := fC) (g := gR)
          (hab := h1N) (h := hbound_Ioc_imp) (hbound := hgInt_1N))
                                    
    have h3 : ∫ u in (1 : ℝ)..(N : ℝ), gR u ≤ (1 / ε) := by
      have := helper_integral_rpow_le (ε := ε) hε (m := (1 : ℝ)) (n := (N : ℝ)) (hm := by norm_num) (hmn := h1N)
      simpa [one_div, Real.one_rpow, one_mul] using this
    have : ‖a N‖ ≤ (1 / ε) := by exact le_trans h1 h3
    exact this
                                              
  have hIle : ‖I‖ ≤ (1 / ε) :=
    helper_limit_norm_le_of_eventual_bound (a := a) (l := I) (B := 1 / ε) hT h_eventual_bound
                                                   
  refine ⟨I, ?_, hIle⟩
  simpa [a, fC] using hT

lemma helper_tendsto_zetaPartialSum_to_zeta (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => zetaPartialSum s N) atTop (𝓝 (riemannZeta s)) := by
  classical
                                                                                    
  set g : ℕ → ℂ := fun n => if n = 0 then 0 else (n : ℂ) ^ (-s)
  set h : ℕ → ℂ := fun n => (n + 1 : ℂ) ^ (-s)
                          
  have hsne : s ≠ 0 := by
    intro h0
    have : (0 : ℝ) < s.re := lt_trans (show (0 : ℝ) < 1 by norm_num) hs
    simpa [h0] using (ne_of_gt this)
                                                          
  have hsum_div : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    (Complex.summable_one_div_nat_cpow (p := s)).2 hs
  have hgSumm : Summable g := by
    simpa [g, one_div_nat_cpow_eq_ite_cpow_neg s hsne] using hsum_div
                                                   
  have h_eq_tail : (fun n => g (n + 1)) = h := by
    funext n; simp [g, h]
  have hhSumm : Summable h := by
    have : Summable (fun n : ℕ => g (n + 1)) := (summable_nat_add_iff (f := g) (k := 1)).2 hgSumm
    simpa [h_eq_tail] using this
                                                                         
  have hg0 : g 0 = 0 := by simp [g]
  have h_tsum_eq : (∑' n : ℕ, h n) = ∑' n : ℕ, g n := by
    have hzero_add := (Summable.tsum_eq_zero_add (f := g) hgSumm)
                                                         
    have : (∑' n : ℕ, g n) = ∑' n : ℕ, g (n + 1) := by
      simpa [hg0, add_comm] using hzero_add
    simpa [h_eq_tail] using this.symm
                                             
  have hzeta : riemannZeta s = ∑' n : ℕ, g n := by
    simpa [g] using lem_zetaLimit s hs
                                                                         
  have h_tendsto : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, h n) atTop (𝓝 (∑' n, h n)) :=
    (Summable.tendsto_sum_tsum_nat hhSumm)
                                                               
  have htsumeq : (∑' n, h n) = riemannZeta s := h_tsum_eq.trans hzeta.symm
  simpa [zetaPartialSum, htsumeq, h] using h_tendsto

lemma integrableOn_of_ae_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {g : ℝ → ℝ} {s : Set ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict s))
    (hgint : IntegrableOn g s)
    (hbound : ∀ᵐ x ∂(volume.restrict s), ‖f x‖ ≤ g x) :
    IntegrableOn f s := by
  have hg' : Integrable g (volume.restrict s) := by
    simpa [IntegrableOn] using hgint
  have hf' : Integrable f (volume.restrict s) :=
    MeasureTheory.Integrable.mono' (μ := volume.restrict s) hg' hfm hbound
  simpa [IntegrableOn] using hf'

lemma kernel_aestronglyMeasurable_on_Ioi (s : ℂ) (a : ℝ) :
  AEStronglyMeasurable (fun u : ℝ => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) (volume.restrict (Ioi a)) := by
                                                                                                           
  have hmeas_fract : Measurable (fun u : ℝ => (Int.fract u : ℝ)) := by
    simpa using (measurable_fract : Measurable (Int.fract : ℝ → ℝ))
  have hmeas_fractC : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) :=
    hmeas_fract.complex_ofReal
  have hmeas_cpow : Measurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) := by
    have hmeas_ofReal : Measurable (fun u : ℝ => (u : ℂ)) := Complex.measurable_ofReal
    simpa using hmeas_ofReal.pow_const (-s - 1)
  have hmeas : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) :=
    hmeas_fractC.mul hmeas_cpow
                                                                                                  
  simpa using hmeas.aestronglyMeasurable

lemma kernel_ae_bound_on_Ioi (s : ℂ) :
  ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
    ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1) := by
                                                          
  let p : ℝ → Prop := fun u => ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1)
                             
  have hAll : ∀ u ∈ Ioi (1 : ℝ), p u := by
    intro u hu
    have hu' : (1 : ℝ) ≤ u := le_of_lt hu
    dsimp [p]
    simpa using (lem_integrandBound u hu' s)
                                                          
  have hAE : ∀ᵐ u ∂volume, u ∈ Ioi (1 : ℝ) → p u :=
    MeasureTheory.ae_of_all _ hAll
                                                              
  have hiff :
      (∀ᵐ u ∂volume.restrict (Ioi (1 : ℝ)), p u) ↔ ∀ᵐ u ∂volume, u ∈ Ioi (1 : ℝ) → p u :=
    (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Ioi (1 : ℝ)) (p := p)) measurableSet_Ioi
  exact hiff.mpr hAE

lemma helper_intervalIntegral_tendstoIoi_kernel (s : ℂ) (hs : 1 < s.re) :
  Tendsto (fun N : ℕ => ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) atTop
    (𝓝 (∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))) := by
                                                                    
  have hfm : AEStronglyMeasurable (fun u : ℝ => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))
      (volume.restrict (Ioi (1 : ℝ))) := by
    simpa using kernel_aestronglyMeasurable_on_Ioi (s := s) (a := (1 : ℝ))
  have hbound' : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1) := by
                                                                      
    simpa using kernel_ae_bound_on_Ioi (s := s)
  have hlt : (-s.re - 1) < (-1 : ℝ) := by linarith
  have hpos : 0 < (1 : ℝ) := by norm_num
  have hgint : IntegrableOn (fun u : ℝ => u ^ (-s.re - 1)) (Ioi (1 : ℝ)) := by
    simpa using integrableOn_Ioi_rpow_of_lt (a := (-s.re - 1)) (c := (1 : ℝ)) hlt hpos
  have hint : IntegrableOn (fun u : ℝ => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
                              
    exact integrableOn_of_ae_bound (s := Ioi (1 : ℝ)) hfm hgint hbound'
                                                   
  have hb : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  simpa using
    (MeasureTheory.intervalIntegral_tendsto_integral_Ioi (μ := volume)
      (f := fun u : ℝ => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) (a := (1 : ℝ))
      (b := fun N : ℕ => (N : ℝ)) hint hb)

lemma helper_zetaNfinal (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
        - s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
  simpa using (lem_zetaNfinal s hs N hN)

lemma helper_eventually_eq_from_zetaNfinal (s : ℂ) (hs : s ≠ 1) :
  ∀ᶠ N in atTop,
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
        - s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
  have hEv : ∀ᶠ N : ℕ in atTop, 1 ≤ N := Filter.eventually_ge_atTop (1 : ℕ)
  refine hEv.mono ?_
  intro N hN
  simpa using (helper_zetaNfinal s hs N hN)

lemma helper_limit_scaled_cpow (s : ℂ) (hs : 1 < s.re) (_hsne : s ≠ 1) :
  Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 0) := by
  have h := lem_limitTerm1 s hs
  have h' := (Filter.Tendsto.const_mul (b := (1 / (1 - s))) h)
  simpa [div_eq_mul_inv, mul_comm] using h'

lemma helper_tendsto_const_mul {f : ℕ → ℂ} {l : ℂ} (c : ℂ)
  (h : Tendsto f atTop (𝓝 l)) : Tendsto (fun n => c * f n) atTop (𝓝 (c * l)) := by
  exact h.const_mul c

lemma helper_tendsto_add {f g : ℕ → ℂ} {a b : ℂ}
  (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b)) :
  Tendsto (fun n => f n + g n) atTop (𝓝 (a + b)) := by
                                                   
  have hpair : Tendsto (fun n => (f n, g n)) atTop (𝓝 (a, b)) := by
    simpa using (hf.prodMk_nhds hg)
  have hadd : Continuous (fun p : ℂ × ℂ => p.1 + p.2) := by
    simpa using! (continuous_fst.add continuous_snd)
  simpa using! ((hadd.tendsto (a, b)).comp hpair)

lemma helper_tendsto_neg {f : ℕ → ℂ} {a : ℂ}
  (hf : Tendsto f atTop (𝓝 a)) : Tendsto (fun n => - f n) atTop (𝓝 (-a)) := by
  simpa only [Function.comp_def] using! ((continuous_neg.tendsto a).comp hf)

lemma helper_tendsto_sub {f g : ℕ → ℂ} {a b : ℂ}
  (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b)) :
  Tendsto (fun n => f n - g n) atTop (𝓝 (a - b)) := by
  have hneg : Tendsto (fun n => - g n) atTop (𝓝 (-b)) :=
    helper_tendsto_neg (f := g) (a := b) hg
  simpa [sub_eq_add_neg] using
    helper_tendsto_add (f := f) (g := fun n => - g n) hf hneg

lemma lem_zetaFormula (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s
      = 1 + 1 / (s - 1)
        - s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
  classical
                          
  have hsne : s ≠ 1 := by
    intro h
    have hlt : 1 < (1 : ℝ) := by simp [h, Complex.one_re] at hs
    exact (lt_irrefl _ ) hlt
                                                           
  let G : ℕ → ℂ := fun N =>
    (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
      - s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)
                                          
  have hEv : ∀ᶠ N in atTop, zetaPartialSum s N = G N := by
    simpa [G] using helper_eventually_eq_from_zetaNfinal s hsne
                                  
  have h_ps : Tendsto (fun N : ℕ => zetaPartialSum s N) atTop (𝓝 (riemannZeta s)) :=
    helper_tendsto_zetaPartialSum_to_zeta s hs
                                      
  have hG_to_zeta : Tendsto G atTop (𝓝 (riemannZeta s)) := by
    have hcongr := (Filter.tendsto_congr' (hl := hEv) :
      Tendsto (fun N : ℕ => zetaPartialSum s N) atTop (𝓝 (riemannZeta s)) ↔
      Tendsto G atTop (𝓝 (riemannZeta s)))
    exact hcongr.mp h_ps

  have hA : Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 0) :=
    helper_limit_scaled_cpow s hs hsne
                                  
  have hK : Tendsto (fun _ : ℕ => (1 : ℂ) + 1 / (s - 1)) atTop (𝓝 ((1 : ℂ) + 1 / (s - 1))) :=
    tendsto_const_nhds
                                             
  have hInt : Tendsto (fun N : ℕ => ∫ u in (1 : ℝ)..N,
      (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) atTop
      (𝓝 (∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))) :=
    helper_intervalIntegral_tendstoIoi_kernel s hs
                           
  have hIntMul : Tendsto (fun N : ℕ => s * ∫ u in (1 : ℝ)..N,
      (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) atTop
      (𝓝 (s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))) :=
    helper_tendsto_const_mul (c := s) hInt
                                             
  set Aseq : ℕ → ℂ := fun N => (N : ℂ) ^ (1 - s) / (1 - s)
  set Kseq : ℕ → ℂ := fun _ => (1 : ℂ) + 1 / (s - 1)
  have hA2 : Tendsto Aseq atTop (𝓝 0) := by simpa [Aseq] using hA
  have hK2 : Tendsto Kseq atTop (𝓝 ((1 : ℂ) + 1 / (s - 1))) := by simp [Kseq]
  have hSum : Tendsto (fun N => Aseq N + Kseq N) atTop (𝓝 (0 + ((1 : ℂ) + 1 / (s - 1)))) :=
    helper_tendsto_add (hf := hA2) (hg := hK2)
  set Iseq : ℕ → ℂ := fun N => s * ∫ u in (1 : ℝ)..N,
      (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)
  have hIseq : Tendsto Iseq atTop (𝓝 (s * ∫ u in Ioi (1 : ℝ),
      (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))) := by
    simpa [Iseq] using hIntMul
  have hG_limit : Tendsto G atTop
      (𝓝 ((0 + ((1 : ℂ) + 1 / (s - 1)))
        - (s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)))) := by
    have hSub := helper_tendsto_sub (hf := hSum) (hg := hIseq)
                                            
    have hGdef : (fun N => (Aseq N + Kseq N) - Iseq N) = G := by
      funext N; simp [Aseq, Kseq, Iseq, G, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    simpa [hGdef]
      using hSub
                                                    
  have huniq :=
    tendsto_nhds_unique (f := G) (l := atTop)
      (a := riemannZeta s)
      (b := ((0 + ((1 : ℂ) + 1 / (s - 1)))
        - (s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))))
      (ha := hG_to_zeta) (hb := hG_limit)
                                     
  simpa [zero_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using huniq

lemma lem_zetaanalOnnot1 : AnalyticOn ℂ riemannZeta {s : ℂ | s ≠ 1} := by
                                                                             
  have hset : {s : ℂ | s ≠ 1} = ({1} : Set ℂ)ᶜ := by
    ext z; simp
  have hopen : IsOpen ({s : ℂ | s ≠ 1}) := by
    simp [hset]
                                               
  have hdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := by
    intro z hz

    simpa using (differentiableAt_riemannZeta (by simpa [Set.mem_ofPred_eq] using hz)).differentiableWithinAt
  simpa [Complex.analyticOn_iff_differentiableOn hopen] using hdiff

lemma lem_zetaanalS : (let S := {s : ℂ | s ≠ 1}; AnalyticOn ℂ riemannZeta S) := by exact lem_zetaanalOnnot1

lemma lem_S_isOpen : (let S := {s : ℂ | s ≠ 1}; IsOpen S) := by
                                                            
  have h : {s : ℂ | s ≠ 1} = {(1 : ℂ)}ᶜ := by
    ext s; simp [Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [h]
  exact isOpen_compl_singleton

lemma lem_T_isOpen : (let S := {s : ℂ | s ≠ 1}; let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}; IsOpen T) := by
                                      
  show IsOpen {s : ℂ | s ≠ 1 ∧ 1/10 < s.re}

  apply IsOpen.and
  ·                           
    exact lem_S_isOpen
  ·                                 
                                                             
    have h_eq : {s : ℂ | 1/10 < s.re} = Complex.re ⁻¹' (Set.Ioi (1/10)) := by
      ext s
      simp [Set.mem_preimage, Set.mem_Ioi]
    rw [h_eq]
    exact Complex.continuous_re.isOpen_preimage (Set.Ioi (1/10)) isOpen_Ioi




lemma T_eq_inter_S_half (S T : Set ℂ) (_hS : S = {s : ℂ | s ≠ 1}) (hT : T = {s : ℂ | s ∈ S ∧ (1/10 : ℝ) < s.re}) :
  T = S ∩ {s : ℂ | (1/10 : ℝ) < s.re} := by
  classical
  ext z
  simp [hT, Set.inter_def]

lemma inter_compl_singleton_eq_diff {α : Type*} [DecidableEq α] (A : Set α) (x : α) :
  A ∩ ({x} : Set α)ᶜ = A \ ({x} : Set α) := by
  ext z; simp [Set.mem_inter_iff, Set.mem_singleton_iff]



lemma isPathConnected_punctured_halfplane_re_gt (a : ℝ) (p : ℂ) (hp : a < p.re) :
  IsPathConnected ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) := by
  classical
                                                                 
  let S1 : Set ℂ := {z : ℂ | a < z.re ∧ z.im < p.im}
  let S2 : Set ℂ := {z : ℂ | a < z.re ∧ z.re < p.re}
  let S3 : Set ℂ := {z : ℂ | a < z.re ∧ p.im < z.im}
  let S4 : Set ℂ := {z : ℂ | p.re < z.re}
                            
  have hS1conv : Convex ℝ S1 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.im < p.im} := convex_halfSpace_im_lt (r := p.im)
    simpa [S1, Set.ofPred_and] using h1.inter h2
  have hS2conv : Convex ℝ S2 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.re < p.re} := convex_halfSpace_re_lt (r := p.re)
    simpa [S2, Set.ofPred_and] using h1.inter h2
  have hS3conv : Convex ℝ S3 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | p.im < z.im} := convex_halfSpace_im_gt (r := p.im)
    simpa [S3, Set.ofPred_and] using h1.inter h2
  have hS4conv : Convex ℝ S4 := by
    simpa [S4] using (convex_halfSpace_re_gt (r := p.re))
                    
  have hS1ne : S1.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : (p.im - 1) < p.im := by linarith
    simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS2ne : S2.Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im : ℝ) * Complex.I, ?_⟩
    have h1 : a < (a + p.re) / 2 := by linarith
    have h2 : (a + p.re) / 2 < p.re := by linarith
    simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS3ne : S3.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : p.im < (p.im + 1) := by linarith
    simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS4ne : S4.Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (0 : ℝ) * Complex.I, ?_⟩
    have : p.re < p.re + 1 := by linarith
    simp [S4, Complex.add_re]
                           
  have hS1pc : IsPathConnected S1 := (hS1conv.isPathConnected hS1ne)
  have hS2pc : IsPathConnected S2 := (hS2conv.isPathConnected hS2ne)
  have hS3pc : IsPathConnected S3 := (hS3conv.isPathConnected hS3ne)
  have hS4pc : IsPathConnected S4 := (hS4conv.isPathConnected hS4ne)
                          
  let A : Set ℂ := S1 ∪ S2
  let B : Set ℂ := S3 ∪ S4
                               
  have hS1S2_int : (S1 ∩ S2).Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im - (1/2)) * Complex.I, ?_⟩
    have h1a : a < (a + p.re) / 2 := by linarith
    have h1b : (p.im - (1/2)) < p.im := by linarith
    have h2a : a < (a + p.re) / 2 := by linarith
    have h2b : (a + p.re) / 2 < p.re := by linarith
    constructor
    ·         
      simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1a h1b
    ·         
      simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h2a h2b
  have hApc : IsPathConnected A :=
    IsPathConnected.union (U := S1) (V := S2) hS1pc hS2pc (by
      rcases hS1S2_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hS3S4_int : (S3 ∩ S4).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h3a : a < p.re + 1 := lt_trans hp (by linarith)
    have h3b : p.im < p.im + 1 := by linarith
    have h4 : p.re < p.re + 1 := by linarith
    constructor
    ·         
      simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h3a h3b
    ·         
      simp [S4, Complex.add_re, Complex.mul_re]
  have hBpc : IsPathConnected B :=
    IsPathConnected.union (U := S3) (V := S4) hS3pc hS4pc (by
      rcases hS3S4_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
                      
  have hABint : (A ∩ B).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    constructor
    ·               
      refine Or.inl ?_
      have h1 : a < p.re + 1 := lt_trans hp (by linarith)
      have h2 : (p.im - 1) < p.im := by linarith
      simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1 h2
    ·               
      refine Or.inr ?_
      have h4 : p.re < p.re + 1 := by linarith
      simp [S4, Complex.add_re, Complex.mul_re]
                                      
  have hUnionPC : IsPathConnected (A ∪ B) :=
    IsPathConnected.union (U := A) (V := B) hApc hBpc (by
      rcases hABint with ⟨z, hz⟩; exact ⟨z, hz⟩)
                                                 
  have hcover : ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) = A ∪ B := by
    ext z; constructor
    · intro hz
      rcases hz with ⟨hzH, hznot⟩
                            
      rcases lt_trichotomy z.re p.re with hlt | heq | hgt
      ·                        
        exact Or.inl (Or.inr ⟨hzH, hlt⟩)
      ·                                             
        rcases lt_trichotomy z.im p.im with himlt | himeq | himgt
        ·                    
          exact Or.inl (Or.inl ⟨hzH, himlt⟩)
        ·                                                
          have hz_eq : z = p := by
                                              
            have hzdecomp : (z.re : ℂ) + (z.im : ℝ) * Complex.I = z := by
              simp
            have hpdecomp : (p.re : ℂ) + (p.im : ℝ) * Complex.I = p := by
              simp
            have : (z.re : ℂ) + (z.im : ℝ) * Complex.I = (p.re : ℂ) + (p.im : ℝ) * Complex.I := by
                                            
              simp [heq, himeq]
                                
            simpa [hzdecomp, hpdecomp] using this
          have : z ∈ ({p} : Set ℂ) := by simp [Set.mem_singleton_iff, hz_eq]
          exact (hznot this).elim
        ·                    
          exact Or.inr (Or.inl ⟨hzH, himgt⟩)
      ·                         
        exact Or.inr (Or.inr hgt)
    · intro hz
                        
      have hzH : a < z.re := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          · exact hS1.1
          · exact hS2.1
        · rcases hB with hS3 | hS4
          · exact hS3.1
          · exact lt_trans hp hS4
      have hzneq : z ≠ p := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          ·             
            intro h
            have : z.im = p.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS1.2
            exact lt_irrefl _ this
          ·             
            intro h
            have : z.re = p.re := by simp [h]
            exact (ne_of_lt hS2.2) this
        · rcases hB with hS3 | hS4
          ·             
            intro h
            have : p.im = z.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS3.2
            exact lt_irrefl _ this
          ·             
            intro h
            have : p.re = z.re := by simp [h]
            exact (ne_of_gt hS4) this.symm
      exact And.intro hzH (by intro hzmem; exact hzneq (by simpa [Set.mem_singleton_iff] using hzmem))
             
  simpa [hcover] using hUnionPC


lemma lem_T_isPreconnected : (let S := {s : ℂ | s ≠ 1}; let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}; IsPreconnected T) := by
  classical
                              
  let S : Set ℂ := {s : ℂ | s ≠ 1}
  let T : Set ℂ := {s : ℂ | s ∈ S ∧ (1/10 : ℝ) < s.re}
                                 
  have hTinter : T = S ∩ {s : ℂ | (1/10 : ℝ) < s.re} := by
    simpa using (T_eq_inter_S_half S T (by rfl) (by rfl))
                                       
  have hScompl : S = ({(1 : ℂ)} : Set ℂ)ᶜ := by
    ext z; simp [S]
                                            
  have hTdiff : T = {s : ℂ | (1/10 : ℝ) < s.re} \ (({(1 : ℂ)} : Set ℂ)) := by
    have : T = {s : ℂ | (1/10 : ℝ) < s.re} ∩ S := by
      simpa [Set.inter_comm] using hTinter
                                                                    
    simpa [hScompl, inter_compl_singleton_eq_diff] using this
                     
  have hp : (1/10 : ℝ) < (1 : ℂ).re := by
    simpa using (by norm_num : (1/10 : ℝ) < (1 : ℝ))
                                               
  have hpc : IsPathConnected ({z : ℂ | (1/10 : ℝ) < z.re} \ (({(1 : ℂ)} : Set ℂ))) :=
    isPathConnected_punctured_halfplane_re_gt (a := (1/10 : ℝ)) (p := (1 : ℂ)) (hp := hp)
                                              
  have hpcT : IsPathConnected T := by
    simpa [hTdiff] using hpc
                                                         
  have hconnT : IsConnected T := hpcT.isConnected
  exact (IsConnected.isPreconnected (s := T) hconnT)



lemma aestronglyMeasurable_kernel_param_deriv (z : ℂ) :
  AEStronglyMeasurable (fun u : ℝ => -((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1))) (volume.restrict (Ioi (1 : ℝ))) := by
                                                                  
  let μ := volume.restrict (Ioi (1 : ℝ))
                                                                                                 
  have hmeas_logR : Measurable (fun u : ℝ => Real.log u) := Real.measurable_log
  have hmeas_logC : Measurable (fun u : ℝ => ((Real.log u) : ℂ)) := hmeas_logR.complex_ofReal
  have hmeas_neg : Measurable (fun u : ℝ => -((Real.log u) : ℂ)) := hmeas_logC.neg
  have h1 : AEStronglyMeasurable (fun u : ℝ => -((Real.log u) : ℂ)) μ := by
    simpa [μ] using hmeas_neg.aestronglyMeasurable
                                                                                 
  have h2 : AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)) μ := by
    simpa [μ] using kernel_aestronglyMeasurable_on_Ioi (s := z) (a := (1 : ℝ))
                                      
  have hmul : AEStronglyMeasurable
      (fun u : ℝ => (-((Real.log u) : ℂ)) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)))
      μ := (MeasureTheory.AEStronglyMeasurable.mul h1 h2)
  simpa [μ] using hmul

lemma kernel_deriv_norm_bound_on_ball (ε : ℝ) (u : ℝ) (hu : 1 < u) (x : ℂ) (hx : ε ≤ x.re) :
  ‖-((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1))‖ ≤ Real.log u * u ^ (-1 - ε) := by
                                       
  have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
                                                                  
  have hinner1 : ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖ ≤ u ^ (-x.re - 1) := by
    simpa using (lem_integrandBound u hu1 x)
  have hexp_le : -x.re - 1 ≤ -1 - ε := by linarith
  have hmono : u ^ (-x.re - 1) ≤ u ^ (-1 - ε) :=
    Real.rpow_le_rpow_of_exponent_le hu1 hexp_le
  have hinner : ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖ ≤ u ^ (-1 - ε) :=
    le_trans hinner1 hmono
                      
  have hmul : ‖-((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1))‖
      = ‖-((Real.log u) : ℂ)‖ * ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖ := by
    simp
  have hnorm_nonneg : 0 ≤ ‖-((Real.log u) : ℂ)‖ := by simp
  have hmul_le : ‖-((Real.log u) : ℂ)‖ * ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖
      ≤ ‖-((Real.log u) : ℂ)‖ * (u ^ (-1 - ε)) := by
    exact mul_le_mul_of_nonneg_left hinner hnorm_nonneg
                                                                  
  have hlognorm_neg : ‖-((Real.log u) : ℂ)‖ = Real.log u := by
    have hnonneg : 0 ≤ Real.log u := le_of_lt (Real.log_pos hu)
    simp [norm_neg, Complex.norm_real, abs_of_nonneg hnonneg]
             
  calc
    ‖-((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1))‖
        = ‖-((Real.log u) : ℂ)‖ * ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖ := hmul
    _ ≤ ‖-((Real.log u) : ℂ)‖ * (u ^ (-1 - ε)) := hmul_le
    _ = (Real.log u) * u ^ (-1 - ε) := by simp [hlognorm_neg, mul_comm]

lemma exists_radius_ball_two_step_subset_halfspace (s : ℂ) {ε : ℝ} (hε : ε < s.re) :
  ∃ δ > 0, ∀ x, dist x s < δ → ∀ y, dist y x < δ → ε ≤ y.re := by
                                  
  set δ : ℝ := (s.re - ε) / 2 with hδdef
  have hpos : 0 < s.re - ε := sub_pos.mpr hε
  have hδpos : 0 < δ := by simpa [hδdef] using (half_pos hpos)
  refine ⟨δ, hδpos, ?_⟩
  intro x hx y hy
                                                                           
  have htri : dist y s ≤ dist y x + dist x s := by
    simpa using (dist_triangle y x s)
  have hsumlt : dist y x + dist x s < δ + δ := add_lt_add hy hx
  have hnorm_lt : ‖y - s‖ < δ + δ := by
    have := lt_of_le_of_lt htri hsumlt
    simpa [dist_eq_norm] using this
  have hdeltaSum : δ + δ = s.re - ε := by
    simp [hδdef, add_halves]
  have hnorm_lt_re : ‖y - s‖ < s.re - ε := by simpa [hdeltaSum] using hnorm_lt
                                  
  have h_eps_lt : ε < s.re - ‖y - s‖ := by
    have hsum' : ε + ‖y - s‖ < s.re := by
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
        (add_lt_add_right hnorm_lt_re ε)
    simpa [lt_sub_iff_add_lt] using hsum'
                                       
  have hre_abs : |(y - s).re| ≤ ‖y - s‖ := by
    simpa using (Complex.abs_re_le_norm (y - s))
  have hre_lower : -‖y - s‖ ≤ (y - s).re := by
                                                  
    have hpair := (abs_le.mp hre_abs)
    exact hpair.left
  have hyge : s.re - ‖y - s‖ ≤ y.re := by
    have h' : s.re + (-‖y - s‖) ≤ s.re + (y - s).re := add_le_add_right hre_lower s.re
    have h'' : s.re + (y - s).re = y.re := by
      simp [sub_eq_add_neg]
    simpa [sub_eq_add_neg, h''] using h'
                                            
  have hygt : ε < y.re := lt_of_lt_of_le h_eps_lt hyge
  exact le_of_lt hygt

lemma integrable_kernel_at_param (s : ℂ) (hs : 0 < s.re) :
  Integrable ((fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))) (volume.restrict (Ioi (1 : ℝ))) := by
  classical
                                                
  set f : ℝ → ℂ := fun u => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
  set ε : ℝ := s.re / 2
  set g1 : ℝ → ℝ := fun u => u ^ (-s.re - 1)
  set g : ℝ → ℝ := fun u => u ^ (-1 - ε)
                                           
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioi (1 : ℝ))) := by
    simpa [f] using kernel_aestronglyMeasurable_on_Ioi (s := s) (a := (1 : ℝ))
                       
  have hε : 0 < ε := by
    have : 0 < s.re := hs
    simpa [ε] using (half_pos this)
  have hεle : ε ≤ s.re := by
    have hnonneg : 0 ≤ s.re := le_of_lt hs
    simpa [ε] using (half_le_self hnonneg)
                                            
  have hbound1 : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ‖f u‖ ≤ g1 u := by
    simpa [f, g1] using (kernel_ae_bound_on_Ioi (s := s))
                                             
  have hpow_ae : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), g1 u ≤ g u := by
                                      
    have hAll : ∀ u ∈ Ioi (1 : ℝ), g1 u ≤ g u := by
      intro u hu
      have hx : (1 : ℝ) ≤ u := le_of_lt hu
      have hlexp : (-s.re - 1) ≤ (-1 - ε) := by linarith
      have := Real.rpow_le_rpow_of_exponent_le hx hlexp
      simpa [g1, g] using this
                                           
    have hAE : ∀ᵐ u ∂volume, u ∈ Ioi (1 : ℝ) → g1 u ≤ g u :=
      MeasureTheory.ae_of_all _ hAll
    have hiff :=
      (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Ioi (1 : ℝ))
        (p := fun u => g1 u ≤ g u) measurableSet_Ioi)
    exact hiff.mpr hAE
                   
  have hbound : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ‖f u‖ ≤ g u := by
    filter_upwards [hbound1, hpow_ae] with u hu1 hu2
    exact le_trans hu1 hu2
                                               
  have hgint : IntegrableOn g (Ioi (1 : ℝ)) := by
    have ha_lt : (-1 - ε) < (-1 : ℝ) := by linarith
    have hc : 0 < (1 : ℝ) := by norm_num
    simpa [g] using (integrableOn_Ioi_rpow_of_lt (a := (-1 - ε)) (ha := ha_lt) (c := (1 : ℝ)) (hc := hc))
                                        
  have hint : IntegrableOn f (Ioi (1 : ℝ)) :=
    integrableOn_of_ae_bound (s := Ioi (1 : ℝ)) (f := f) (g := g)
      (hfm := hfm) (hgint := hgint) (hbound := hbound)
  simpa [IntegrableOn, f] using hint

lemma eventually_aestronglyMeasurable_kernel_param (s : ℂ) :
  ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)) (volume.restrict (Ioi (1 : ℝ))) := by
  refine Filter.Eventually.of_forall ?_
  intro z
                                
  have hmeas_fract : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) := by
    have hmeas_fr : Measurable (Int.fract : ℝ → ℝ) := by
      simpa using (measurable_fract : Measurable (Int.fract : ℝ → ℝ))
    exact (Complex.measurable_ofReal.comp hmeas_fr)
  have hmeas_cpow : Measurable (fun u : ℝ => (u : ℂ) ^ (-z - 1)) := by
                                                                                
    measurability
  have hmeas : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)) :=
    hmeas_fract.mul hmeas_cpow
  simpa using hmeas.aestronglyMeasurable

lemma hasDerivAt_kernel_in_param (u : ℝ) (hu : 1 < u) (z : ℂ) :
  HasDerivAt (fun w : ℂ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-w - 1))
    ( -((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)) ) z := by
                       
  set c0 : ℂ := ((Int.fract u : ℝ) : ℂ)
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hux0 : (u : ℝ) ≠ 0 := ne_of_gt hu0
  have hcz : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hux0
                                      
  have hfneg : HasDerivAt (fun w : ℂ => -w) (-1) z := (hasDerivAt_id z).neg
  have hf : HasDerivAt (fun w : ℂ => -w - 1) (-1) z := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hfneg.sub_const (1 : ℂ)
                                         
  have hbase : HasDerivAt (fun w : ℂ => (u : ℂ) ^ (-w - 1))
      ((u : ℂ) ^ (-z - 1) * Complex.log (u : ℂ) * (-1)) z :=
    HasDerivAt.const_cpow (c := (u : ℂ)) (hf := hf) (h0 := Or.inl hcz)
  have hbase' : HasDerivAt (fun w : ℂ => (u : ℂ) ^ (-w - 1))
      (-(Complex.log (u : ℂ)) * (u : ℂ) ^ (-z - 1)) z := by
                        
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
                            
  have hmul : HasDerivAt (fun w : ℂ => c0 * ((u : ℂ) ^ (-w - 1)))
      (c0 * (-(Complex.log (u : ℂ)) * (u : ℂ) ^ (-z - 1))) z :=
    HasDerivAt.const_mul c0 hbase'
                                             
  have hlog : (Real.log u : ℂ) = Complex.log (u : ℂ) := by
    simpa using (Complex.ofReal_log (x := u) (hx := le_of_lt hu0))
                        
  simpa [c0, hlog, mul_comm, mul_left_comm, mul_assoc] using hmul

lemma hasDerivAt_integral_param_dominated_Ioi
  (F F' : ℂ → ℝ → ℂ) (s : ℂ) (δ : ℝ) (hδ : 0 < δ)
  (hmeas : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (F z) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (hFint : Integrable (F s) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (hF'meas : AEStronglyMeasurable (F' s) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (bound : ℝ → ℝ)
  (hbound_int : Integrable bound (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (hbound : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ, ‖F' z u‖ ≤ bound u)
  (hderiv : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ, HasDerivAt (fun w => F w u) (F' z u) z)
  :
  HasDerivAt (fun z => ∫ u in Ioi (1 : ℝ), F z u) (∫ u in Ioi (1 : ℝ), F' s u) s := by
                                                                                                 
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume.restrict (Ioi (1 : ℝ)))
      (F := F) (F' := F') (x₀ := s)
      (s := Metric.ball s δ) (hs := Metric.ball_mem_nhds s hδ)
      (hF_meas := hmeas) (hF_int := hFint)
      (hF'_meas := hF'meas)
      (h_bound := hbound) (bound_integrable := hbound_int)
      (h_diff := hderiv)
  rcases h with ⟨_hint, hDeriv⟩
                                                                                 
  simpa using hDeriv





lemma analyticAt_of_eventually_differentiableAt {f : ℂ → ℂ} {s : ℂ}
  (h : ∀ᶠ z in 𝓝 s, DifferentiableAt ℂ f z) : AnalyticAt ℂ f s := by
  simpa using
    (Complex.analyticAt_iff_eventually_differentiableAt (f := f) (c := s)).2 h



lemma lem_integralAnalytic (s : ℂ) (hs : 1/10 < s.re) :
    AnalyticAt ℂ (fun z : ℂ => ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)) s := by
  classical
                                                            
  have hspos : 0 < s.re := lt_trans (by norm_num : (0 : ℝ) < 1/10) hs
  set ε : ℝ := s.re / 2 with hεdef
  have hεpos : 0 < ε := by simpa [ε] using (half_pos hspos)
  have hεlt : ε < s.re := by
    have : s.re / 2 < s.re := by simpa [ε] using (half_lt_self hspos)
    simpa [ε] using this
                                                                        
  rcases exists_radius_ball_two_step_subset_halfspace (s := s) (ε := ε) hεlt with ⟨δ, hδpos, hδprop⟩
                                                            
  let F : ℂ → ℝ → ℂ := fun z u => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)
  let F' : ℂ → ℝ → ℂ := fun z u => -((Real.log u) : ℂ) * F z u
                                                 
  let bound : ℝ → ℝ := fun u => (2/ε) * u ^ (-1 - (ε/2))
                                                     
  have hbound_int : Integrable bound (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
    have hlt : (-1 - (ε/2)) < (-1 : ℝ) := by
      have : 0 < ε/2 := by simpa using (half_pos hεpos)
      linarith
    have hpos1 : 0 < (1 : ℝ) := by norm_num
    have hpow_int : IntegrableOn (fun u : ℝ => u ^ (-1 - (ε/2))) (Ioi (1 : ℝ)) := by
      simpa using (integrableOn_Ioi_rpow_of_lt (a := (-1 - (ε/2))) hlt (c := (1 : ℝ)) hpos1)
    have hconst : IntegrableOn (fun u : ℝ => (2/ε) * u ^ (-1 - (ε/2))) (Ioi (1 : ℝ)) :=
      hpow_int.const_mul (2/ε)
    simpa [IntegrableOn, bound] using hconst
                                                                                  
  have hDiff_eventually : ∀ᶠ z in 𝓝 s,
      DifferentiableAt ℂ (fun z0 => ∫ u in Ioi (1 : ℝ), F z0 u) z := by
                                              
    have hball : Metric.ball s (δ/2) ∈ 𝓝 s := Metric.ball_mem_nhds _ (by simpa using (half_pos hδpos))
    refine Filter.eventually_of_mem hball ?_
    intro z hz
                                                                                            
    have hz_lt_δ : dist z s < δ := lt_trans (by simpa [Metric.mem_ball] using hz) (by simpa using (half_lt_self hδpos))
    have hRe_inner : ∀ y, y ∈ Metric.ball z (δ/2) → ε ≤ y.re := by
      intro y hy
      have hy_lt_δ : dist y z < δ := lt_trans (by simpa [Metric.mem_ball] using hy) (by simpa using (half_lt_self hδpos))
      exact hδprop z hz_lt_δ y hy_lt_δ
                                              
    have hmeas_z : ∀ᶠ w in 𝓝 z,
        AEStronglyMeasurable (F w) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) :=
      eventually_aestronglyMeasurable_kernel_param (s := z)
                                                                     
    have hzRe_ge : ε ≤ z.re := by
                                                      
      have hss : dist s s < δ := by simpa [dist_self] using hδpos
      have hz_lt_δ' : dist z s < δ := hz_lt_δ
      exact hδprop s hss z hz_lt_δ'
    have hzpos : 0 < z.re := lt_of_lt_of_le hεpos hzRe_ge
    have hFint_z : Integrable (F z) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
      simpa [F] using integrable_kernel_at_param (s := z) hzpos
                                      
    have hF'meas_z : AEStronglyMeasurable (F' z) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
      simpa [F, F'] using aestronglyMeasurable_kernel_param_deriv (z := z)
                                                       
    have hbound_z : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))),
        ∀ w ∈ Metric.ball z (δ/2), ‖F' w u‖ ≤ bound u := by
                                                                                           
      have hAll : ∀ u ∈ Ioi (1 : ℝ), ∀ w ∈ Metric.ball z (δ/2), ‖F' w u‖ ≤ bound u := by
        intro u hu w hw
        have hu1 : 1 < u := hu
        have hu0 : 0 < u := lt_trans zero_lt_one hu1
                                                             
        have hwRe : ε ≤ w.re := hRe_inner w hw
        have hker : ‖-((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-w - 1))‖
              ≤ Real.log u * u ^ (-1 - ε) :=
          kernel_deriv_norm_bound_on_ball (ε := ε) (u := u) (hu := hu1) (x := w) (hx := hwRe)
        have hF'le : ‖F' w u‖ ≤ Real.log u * u ^ (-1 - ε) := by
          simpa [F, F', mul_comm, mul_left_comm, mul_assoc] using hker
                                                    
        have hx' := Real.add_one_le_exp ((ε/2) * Real.log u)
        have hx : 1 + (ε/2) * Real.log u ≤ Real.exp ((ε/2) * Real.log u) := by
          simpa [add_comm] using hx'
        have hsub : (ε/2) * Real.log u ≤ Real.exp ((ε/2) * Real.log u) - 1 := by
          have := sub_le_sub_right hx 1
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
        have hle_exp : (ε/2) * Real.log u ≤ Real.exp ((ε/2) * Real.log u) := by
          have hnonneg : 0 ≤ (1 : ℝ) := by norm_num
          have : Real.exp ((ε/2) * Real.log u) - 1 ≤ Real.exp ((ε/2) * Real.log u) :=
            sub_le_self _ hnonneg
          exact le_trans hsub this
        have hεne : (ε : ℝ) ≠ 0 := ne_of_gt hεpos
        have hpos_inv : 0 < ε⁻¹ := inv_pos.mpr hεpos
        have hpos_coeff : 0 < (2/ε) := by
          have : 0 < (2 : ℝ) := by norm_num
          simpa [one_div, div_eq_mul_inv] using (mul_pos this hpos_inv)
        have hlog_bound : Real.log u ≤ (2/ε) * Real.exp ((ε/2) * Real.log u) := by
          have hmul := mul_le_mul_of_nonneg_left hle_exp (le_of_lt hpos_coeff)
                                            
          have hleft : (2/ε) * ((ε/2) * Real.log u) = Real.log u := by
            have h2ne : (2 : ℝ) ≠ 0 := by norm_num
            calc
              (2/ε) * ((ε/2) * Real.log u)
                  = ((2/ε) * (ε/2)) * Real.log u := by ring
              _ = ((2 * ε⁻¹) * (ε * (2)⁻¹)) * Real.log u := by simp [div_eq_mul_inv]
              _ = ((2 * (2)⁻¹) * (ε⁻¹ * ε)) * Real.log u := by ring
              _ = (1 * 1) * Real.log u := by simp [hεne, h2ne]
              _ = Real.log u := by simp
          simpa [hleft]
            using hmul
                                                
        have hexp_rpow : Real.exp ((ε/2) * Real.log u) = u ^ (ε/2) := by
          have : 0 < u := hu0
          simp [Real.rpow_def_of_pos this, mul_comm]
                                                 
        have hmul : Real.log u * u ^ (-1 - ε)
              ≤ ((2/ε) * u ^ (ε/2)) * u ^ (-1 - ε) := by
          have hqpos : 0 < u ^ (-1 - ε) := Real.rpow_pos_of_pos hu0 _
          have hq : 0 ≤ u ^ (-1 - ε) := le_of_lt hqpos
          exact mul_le_mul_of_nonneg_right (by simpa [hexp_rpow] using hlog_bound) hq
                                                                    
        have hpow_mul : u ^ (ε/2) * u ^ (-1 - ε) = u ^ (-1 - (ε/2)) := by
          have hu0' : 0 < u := hu0
          have h1 : Real.exp ((ε/2) * Real.log u) * Real.exp ((-1 - ε) * Real.log u)
              = Real.exp (((ε/2) * Real.log u) + ((-1 - ε) * Real.log u)) := by
            simpa using (Real.exp_add ((ε/2) * Real.log u) ((-1 - ε) * Real.log u)).symm
          calc
            u ^ (ε/2) * u ^ (-1 - ε)
                = Real.exp ((ε/2) * Real.log u) * Real.exp ((-1 - ε) * Real.log u) := by
                    simp [Real.rpow_def_of_pos hu0', mul_comm]
            _ = Real.exp (((ε/2) * Real.log u) + ((-1 - ε) * Real.log u)) := by
                    simpa using h1
            _ = Real.exp (((ε/2) + (-1 - ε)) * Real.log u) := by
                    ring_nf
            _ = u ^ (-1 - (ε/2)) := by
                    have : (ε/2) + (-1 - ε) = -1 - (ε/2) := by ring
                    simp [this, Real.rpow_def_of_pos hu0', mul_comm]
        have hmul' : ((2/ε) * u ^ (ε/2)) * u ^ (-1 - ε) = (2/ε) * u ^ (-1 - (ε/2)) := by
          simp [mul_assoc, hpow_mul]
                      
        have : ‖F' w u‖ ≤ bound u := by
          refine le_trans hF'le ?_
          simpa [bound, hmul'] using hmul
        simpa [F, F', bound]
          using this
                                             
      have hiff :=
        (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume) (s := Ioi (1 : ℝ))
          (p := fun u : ℝ => ∀ w ∈ Metric.ball z (δ/2), ‖F' w u‖ ≤ bound u) measurableSet_Ioi)
      exact hiff.mpr (MeasureTheory.ae_of_all _ hAll)
                                                                           
    have hderiv_z : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))),
        ∀ w ∈ Metric.ball z (δ/2), HasDerivAt (fun w0 => F w0 u) (F' w u) w := by
                                                  
      have hAll : ∀ u ∈ Ioi (1 : ℝ), ∀ w ∈ Metric.ball z (δ/2),
          HasDerivAt (fun w0 => F w0 u) (F' w u) w := by
        intro u hu w hw
        simpa [F, F', mul_comm, mul_left_comm, mul_assoc]
          using hasDerivAt_kernel_in_param (u := u) (hu := hu) (z := w)
                                             
      have hiff :=
        (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume) (s := Ioi (1 : ℝ))
          (p := fun u : ℝ => ∀ w ∈ Metric.ball z (δ/2),
            HasDerivAt (fun w0 => F w0 u) (F' w u) w) measurableSet_Ioi)
      exact hiff.mpr (MeasureTheory.ae_of_all _ hAll)
                                                                         
    have hD := hasDerivAt_integral_param_dominated_Ioi
      (F := F) (F' := F') (s := z) (δ := δ/2) (hδ := by simpa using (half_pos hδpos))
      (hmeas := hmeas_z) (hFint := hFint_z) (hF'meas := hF'meas_z)
      (bound := bound) (hbound_int := hbound_int) (hbound := hbound_z) (hderiv := hderiv_z)
                                      
    simpa using hD.differentiableAt
                                                               
  exact analyticAt_of_eventually_differentiableAt hDiff_eventually

lemma lem_zetaFormulaAC :
    (let S := {s : ℂ | s ≠ 1}
     let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}
     let F := fun z : ℂ =>
       z / (z - 1)
       - z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)
     AnalyticOn ℂ F T) := by
                                    
  simp only [AnalyticOn]
  intro s hs
  simp at hs
  obtain ⟨hs_ne_1, hs_re⟩ := hs

  apply AnalyticAt.analyticWithinAt

  have h1 : AnalyticAt ℂ (fun z => z / (z - 1)) s := by
    apply AnalyticAt.div
    · exact analyticAt_id
    · exact analyticAt_id.sub analyticAt_const
    ·                             
      rw [sub_ne_zero]
      exact hs_ne_1

  have hs_re_eq : (10 : ℝ)⁻¹ = (1 : ℝ) / 10 := by norm_num
  have hs_re_correct : (1 : ℝ) / 10 < s.re := by rwa [← hs_re_eq]

  have hconv := lem_integralConvergence (1/10) (by norm_num) s (le_of_lt hs_re_correct)

  obtain ⟨I, hI_tendsto, hI_bound⟩ := hconv

  have hI_bound_10 : ‖I‖ ≤ 10 := by
    convert (preTransparency := .instances) hI_bound
    norm_num

  have h_integral : AnalyticAt ℂ (fun z => ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)) s := by
    apply lem_integralAnalytic s hs_re_correct

  have h2 : AnalyticAt ℂ (fun z => z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)) s := by
    exact analyticAt_id.mul h_integral

  exact h1.sub h2

lemma lem_div_eq_one_plus_one_div (z : ℂ) (hz : z ≠ 1) : z / (z - 1) = 1 + 1 / (z - 1) := by
  have h : z - 1 ≠ 0 := by
    intro h0
    have : z = 1 := by
      rw [sub_eq_zero] at h0
      exact h0
    exact hz this
  calc z / (z - 1)
    = ((z - 1) + 1) / (z - 1) := by ring_nf
    _ = (z - 1) / (z - 1) + 1 / (z - 1) := by rw [add_div]
    _ = 1 + 1 / (z - 1) := by simp [div_self h]

lemma lem_zetaAnalyticContinuation :
    (let S := {s : ℂ | s ≠ 1}
     let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}
     ∀ s ∈ T,
       riemannZeta s
         = 1 + 1 / (s - 1)
           - s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) := by
                              
  simp only [Set.mem_ofPred_eq]
  intro s h_s
                          
  have hs_ne_1 : s ≠ 1 := h_s.1
  have hs_re : 1/10 < s.re := h_s.2

  let F := fun z : ℂ => 1 + 1 / (z - 1) - z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)

  let S := {s : ℂ | s ≠ 1}
  let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}

  have hs_in_T : s ∈ T := by
    simp only [T, S, Set.mem_ofPred_eq]
    exact ⟨hs_ne_1, hs_re⟩

  have h_T_open := lem_T_isOpen
  have h_T_preconnected := lem_T_isPreconnected

  have h_zeta_analytic_S := lem_zetaanalS
  have h_zeta_analytic_T : AnalyticOn ℂ riemannZeta T := by
    apply AnalyticOn.mono h_zeta_analytic_S
    intro x hx; exact hx.1
  have h_zeta_analyticOnNhd_T : AnalyticOnNhd ℂ riemannZeta T := by
    rwa [← h_T_open.analyticOn_iff_analyticOnNhd]

  have h_F_orig_analytic := lem_zetaFormulaAC
                                                                                 
  have h_F_eq : EqOn F (fun z => z / (z - 1) - z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)) T := by
    intro z hz
    simp only [F]
    rw [lem_div_eq_one_plus_one_div z hz.1]

  have h_F_analytic_T : AnalyticOn ℂ F T :=
    AnalyticOn.congr h_F_orig_analytic h_F_eq
  have h_F_analyticOnNhd_T : AnalyticOnNhd ℂ F T := by
    rwa [← h_T_open.analyticOn_iff_analyticOnNhd]

  have ⟨s₀, hs₀_T, hs₀_re⟩ : ∃ s₀, s₀ ∈ T ∧ 1 < s₀.re := by
    use 2
    constructor
    · simp only [T, S, Set.mem_ofPred_eq]
      norm_num
    · norm_num

  have h_eventually_eq : riemannZeta =ᶠ[𝓝 s₀] F := by
                                                                                 
    have h_re_cont : ContinuousAt Complex.re s₀ := Complex.continuous_re.continuousAt
    have h_nhd_re : ∀ᶠ s in 𝓝 s₀, 1 < s.re :=
      ContinuousAt.eventually_lt continuousAt_const h_re_cont hs₀_re
                                            
    have h_nhd_T : ∀ᶠ s in 𝓝 s₀, s ∈ T := h_T_open.mem_nhds hs₀_T

    filter_upwards [h_nhd_re, h_nhd_T] with w hw_re hw_T
                                            
    have h_formula := lem_zetaFormula w hw_re
    simp only [F]
    exact h_formula

  have h_eqOn_global := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    h_zeta_analyticOnNhd_T h_F_analyticOnNhd_T h_T_preconnected hs₀_T h_eventually_eq

  exact h_eqOn_global hs_in_T

lemma lem_zetaBound1 (s : ℂ) (hs_re : 1/10 < s.re) (hs_ne : s ≠ 1) : ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ := by
  classical
  set S : Set ℂ := {z : ℂ | z ≠ 1}
  set T : Set ℂ := {z : ℂ | z ∈ S ∧ 1/10 < z.re}
  set Iint : ℂ := ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)
  have hT : s ∈ T := by
    have hsS : s ∈ S := by simpa [S, Set.mem_ofPred_eq] using hs_ne
    simpa [T, Set.mem_ofPred_eq] using And.intro hsS hs_re
  have hAC : ∀ z ∈ T, riemannZeta z = 1 + 1 / (z - 1) - z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1) := by
    simpa [S, T] using lem_zetaAnalyticContinuation
  have hzeta : riemannZeta s = 1 + 1 / (s - 1) - s * Iint := by
    simpa [Iint] using hAC s hT
  have h1 : ‖riemannZeta s‖ ≤ ‖1 + 1 / (s - 1)‖ + ‖-s * Iint‖ := by
    simpa [hzeta, sub_eq_add_neg] using (lem_triangleInequality_add (1 + 1 / (s - 1)) (-s * Iint))
  have hA : ‖1 + 1 / (s - 1)‖ ≤ ‖(1 : ℂ)‖ + ‖1 / (s - 1)‖ := by
    simpa using (lem_triangleInequality_add (1 : ℂ) (1 / (s - 1)))
  have hmul : ‖-s * Iint‖ = ‖-s‖ * ‖Iint‖ := by
    simp
  have hB : ‖-s * Iint‖ ≤ ‖s‖ * ‖Iint‖ := by
    have : ‖-s * Iint‖ = ‖s‖ * ‖Iint‖ := by simp
    exact this.le
  have h2 : ‖riemannZeta s‖ ≤ (‖(1 : ℂ)‖ + ‖1 / (s - 1)‖) + (‖s‖ * ‖Iint‖) :=
    le_trans h1 (add_le_add hA hB)
  have h1norm : ‖(1 : ℂ)‖ = 1 := by simp
  simpa [Iint, h1norm, add_comm, add_left_comm, add_assoc] using h2

lemma lem_integralBoundValue (s : ℂ) (hs : 0 < s.re) : ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) = 1 / s.re := by
  have ha : (-s.re - 1) < -1 := by linarith
  have hc : 0 < (1 : ℝ) := by exact zero_lt_one
  have h := integral_Ioi_rpow_of_lt (a := (-s.re - 1)) ha (c := (1 : ℝ)) hc
  have h' : ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) = - (1 : ℝ) ^ (-s.re) / (-s.re) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  calc
    ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1)
        = - (1 : ℝ) ^ (-s.re) / (-s.re) := h'
    _ = - (1 : ℝ) / (-s.re) := by simp [Real.one_rpow]
    _ = 1 / s.re := by simp

lemma lem_zetaBound2 (s : ℂ) (hs_re : 1/10 < s.re) (hs_ne : s ≠ 1) : ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := by
                                            
  set f : ℝ → ℂ := fun u => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) with hfdef
  set g : ℝ → ℝ := fun u => u ^ (-s.re - 1) with hgdef
                               
  have hζ : ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), f u‖ := by
    simpa [hfdef] using lem_zetaBound1 s hs_re hs_ne
                                               
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioi (1 : ℝ))
                                   
  have h_ae_bound : ∀ᵐ u ∂μ, ‖f u‖ ≤ g u := by
    have hforall : ∀ u ∈ Ioi (1 : ℝ), ‖f u‖ ≤ g u := by
      intro u hu
      have := lem_integrandBound u (le_of_lt hu) s
      simpa [hfdef, hgdef] using this
    have hmeas : MeasurableSet (Ioi (1 : ℝ)) := measurableSet_Ioi
    simpa [μ] using
      (MeasureTheory.ae_restrict_of_forall_mem (μ := volume) (s := Ioi (1 : ℝ)) hmeas hforall)
                                                                               
  have hg_intOn : IntegrableOn g (Ioi (1 : ℝ)) := by
    classical
    by_contra hnot
    have hnot' : ¬ Integrable g μ := by simpa [μ, IntegrableOn] using hnot
    have hint0 : (∫ u, g u ∂μ) = 0 := by
      simpa using (integral_undef (μ := μ) (f := g) hnot')
    have hval : ∫ u in Ioi (1 : ℝ), g u = 1 / s.re := by
      simpa [hgdef] using lem_integralBoundValue s (by linarith [hs_re])
    have hne : (1 / s.re) ≠ 0 := by exact one_div_ne_zero (ne_of_gt (by linarith [hs_re]))
    have : (∫ u in Ioi (1 : ℝ), g u) = 0 := by simpa [μ] using hint0
    exact hne (by simpa [hval] using this)
  have hg_int : Integrable g μ := by simpa [μ, IntegrableOn] using hg_intOn
                                                             
  have h_int_bound : ‖∫ u in Ioi (1 : ℝ), f u‖ ≤ ∫ u in Ioi (1 : ℝ), g u := by
    have :=
      (MeasureTheory.norm_integral_le_of_norm_le (μ := μ) (f := f) (g := g) hg_int h_ae_bound)
    simpa [μ] using this
                                                                      
  have h_g_val : ∫ u in Ioi (1 : ℝ), g u = 1 / s.re := by
    simpa [hgdef] using lem_integralBoundValue s (by linarith [hs_re])
  have h_int_bound_conc : ‖∫ u in Ioi (1 : ℝ), f u‖ ≤ 1 / s.re := by
    simpa [h_g_val] using h_int_bound
                        
  have hmul : ‖s‖ * ‖∫ u in Ioi (1 : ℝ), f u‖ ≤ ‖s‖ * (1 / s.re) := by
    exact mul_le_mul_of_nonneg_left h_int_bound_conc (by exact norm_nonneg s)
                        
  have hsum0 : (1 + ‖1 / (s - 1)‖) + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), f u‖
      ≤ (1 + ‖1 / (s - 1)‖) + ‖s‖ * (1 / s.re) := by
    exact add_le_add_right hmul (1 + ‖1 / (s - 1)‖)
  have hsum : 1 + ‖1 / (s - 1)‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), f u‖
      ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ * (1 / s.re) := by
    simpa [add_assoc] using hsum0
                                                          
  have hfinal1 : ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ * (1 / s.re) :=
    le_trans hζ hsum
  simpa [div_eq_mul_inv] using hfinal1

lemma lem_sOverSminus1Bound (s : ℂ) (_hs : s ≠ 1) : ‖(1 / (s - 1))‖ = 1 / ‖s - 1‖ := by simp [one_div]

lemma lem_zetaBound3 (s : ℂ) (hs_re : 1/10 < s.re) (hs_ne : s ≠ 1) : ‖riemannZeta s‖ ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ / s.re := by
  simpa [lem_sOverSminus1Bound s hs_ne] using lem_zetaBound2 s hs_re hs_ne

lemma helper_normsq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  simpa [Complex.normSq, pow_two] using (Complex.normSq_eq_norm_sq z).symm

lemma helper_three_abs_sq (t : ℝ) : (3 : ℝ) ^ 2 + t ^ 2 ≤ (3 + |t|) ^ 2 := by
  have hnonneg : 0 ≤ (6 : ℝ) * |t| := by
    have h6 : (0 : ℝ) ≤ 6 := by norm_num
    exact mul_nonneg h6 (abs_nonneg t)
  have hmul : |t| * |t| = t * t := by
    simp
  calc
    (3 : ℝ) ^ 2 + t ^ 2 = (3 : ℝ) ^ 2 + t * t := by simp [pow_two]
    _ = (3 : ℝ) ^ 2 + |t| * |t| := by simp [hmul]
    _ ≤ (3 : ℝ) ^ 2 + |t| * |t| + (6 : ℝ) * |t| := by exact le_add_of_nonneg_right hnonneg
    _ = (3 + |t|) ^ 2 := by ring

lemma lem_sBound (s : ℂ) (hs : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) : ‖s‖ < (3 : ℝ) + |s.im| := by
  have hnegthree_lt_re : (- (3 : ℝ)) < s.re := by
    have hlt : (- (3 : ℝ)) < (1 / 2 : ℝ) := by norm_num
    exact lt_of_lt_of_le hlt hs.1
  have hlt3 : s.re < (3 : ℝ) := hs.2
  have h_re_sq_lt : s.re ^ 2 < (3 : ℝ) ^ 2 := by
    simpa using (sq_lt_sq' hnegthree_lt_re hlt3)
  have hsumlt : s.re ^ 2 + s.im ^ 2 < (3 : ℝ) ^ 2 + s.im ^ 2 := by
    exact add_lt_add_left h_re_sq_lt _
  have hsq : ‖s‖ ^ 2 < (3 + |s.im|) ^ 2 := by
    have h := lt_of_lt_of_le hsumlt (helper_three_abs_sq s.im)
    simpa [helper_normsq s] using h
  have hnormnn : 0 ≤ ‖s‖ := norm_nonneg _
  have hpos : 0 ≤ (3 : ℝ) + |s.im| := add_nonneg (by norm_num) (abs_nonneg _)
  exact (sq_lt_sq₀ hnormnn hpos).1 hsq

lemma lem_invReSbound (s : ℂ) (hs : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) :
    1 / s.re ≤ (2 : ℝ) := by
  have h_pos : (0 : ℝ) < s.re := by
    linarith [hs.1]
  have h_half_pos : (0 : ℝ) < (1/2 : ℝ) := by norm_num
  have h_recip : 1 / s.re ≤ 1 / (1/2 : ℝ) := one_div_le_one_div_of_le h_half_pos hs.1
  have h_simplify : 1 / (1/2 : ℝ) = (2 : ℝ) := by norm_num
  rw [h_simplify] at h_recip
  exact h_recip

lemma lem_invSminus1bound (s : ℂ) (_hs_re : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) (hs_im : (1 : ℝ) ≤ |s.im|) : (1 : ℝ) ≤ ‖s - 1‖ := by
  have h2 : |s.im| ≤ ‖s - 1‖ := by
    have : (s - (1 : ℂ)).im = s.im := by
      simp [Complex.sub_im, Complex.one_im]
    simpa [this] using Complex.abs_im_le_norm (s - 1)
  exact le_trans hs_im h2

lemma reciprocal_le_one_of_one_le {x : ℝ} (hx_pos : 0 < x) (hx_ge : 1 ≤ x) : 1 / x ≤ 1 := by
                                                            
  have h_div_pos : 0 < 1 / x := one_div_pos.mpr hx_pos
                                     
  have h1 : (1 / x) * 1 ≤ (1 / x) * x := by
    exact mul_le_mul_of_nonneg_left hx_ge (le_of_lt h_div_pos)
                                                
  rw [mul_one] at h1
  rw [one_div_mul_cancel (ne_of_gt hx_pos)] at h1
  exact h1

lemma div_le_mul_of_one_div_le {a c d : ℝ} (ha : 0 ≤ a) (_hc : 0 < c) (h : 1 / c ≤ d) : a / c ≤ a * d := by
                                 
  rw [div_eq_mul_one_div]
                                                                  
  exact mul_le_mul_of_nonneg_left h ha

lemma lem_finalBoundCombination (s : ℂ) (hs_re : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) (hs_im : (1 : ℝ) ≤ |s.im|) : ‖riemannZeta s‖ < 1 + 1 + ((3 : ℝ) + |s.im|) * 2 := by
                                                                                   
  have hs_ne : s ≠ 1 := by
    intro h
    rw [h] at hs_im
    simp at hs_im
    linarith
                                  
  have hs_re_pos : 0 < s.re := by linarith [hs_re.1]
                                               
  have h1 : ‖riemannZeta s‖ ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ / s.re := lem_zetaBound3 s (by linarith [hs_re_pos]) hs_ne
                                                   
  have h2 : (1 : ℝ) ≤ ‖s - 1‖ := lem_invSminus1bound s hs_re hs_im
  have h3 : 1 / ‖s - 1‖ ≤ 1 := reciprocal_le_one_of_one_le (by linarith [h2]) h2
                                             
  have h4 : ‖s‖ < (3 : ℝ) + |s.im| := lem_sBound s hs_re
                                            
  have h5 : 1 / s.re ≤ (2 : ℝ) := lem_invReSbound s hs_re
                                  
  calc ‖riemannZeta s‖
    ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ / s.re := h1
    _ ≤ 1 + 1 + ‖s‖ / s.re := by linarith [h3]
    _ ≤ 1 + 1 + ‖s‖ * 2 := by
      have s_nonneg : 0 ≤ ‖s‖ := norm_nonneg _
      exact add_le_add_right (div_le_mul_of_one_div_le s_nonneg hs_re_pos h5) _
    _ < 1 + 1 + ((3 : ℝ) + |s.im|) * 2 := by linarith [h4]

lemma lem_finalAlgebra (t : ℝ) : 1 + 1 + ((3 : ℝ) + |t|) * 2 = (8 : ℝ) + 2 * |t| := by ring

lemma lem_zetaUppBd (z : ℂ) (hz_re : z.re ∈ Ico (1/2 : ℝ) (3 : ℝ)) (hz_im : (1 : ℝ) ≤ |z.im|) : ‖riemannZeta z‖ < (8 : ℝ) + 2 * |z.im| := by
  have hz_re' : (1/2 : ℝ) ≤ z.re ∧ z.re < (3 : ℝ) := by
    simpa [Ico] using hz_re
  have h := lem_finalBoundCombination z hz_re' hz_im
  simpa [lem_finalAlgebra] using h

lemma lem_zfroms_calc (s : ℂ) (t : ℝ) :
    (let z := s + (3/2 : ℝ) + I * t
     z.re = s.re + (3/2 : ℝ) ∧ z.im = s.im + t) := by
  constructor
  ·                           
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
                                                                       
    have h1 : I.re = 0 := Complex.I_re
    have h2 : I.im * 0 = 0 := mul_zero _
    rw [h1, h2]
    simp
  ·                   
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
                                                                   
    have h1 : I.re * 0 = 0 := mul_zero _
    have h2 : I.im = 1 := Complex.I_im
    rw [h1, h2]
    simp

lemma lem_zfroms_conditions (s : ℂ) (t : ℝ)
    (hs : ‖s‖ ≤ (1 : ℝ)) (ht : (2 : ℝ) < |t|) :
    (let z := s + (3/2 : ℝ) + I * t
     z.re ∈ Ico (1/2 : ℝ) (3 : ℝ) ∧ (1 : ℝ) ≤ |z.im|) := by
                                                        
  have h_calc := lem_zfroms_calc s t
  simp only [h_calc.1, h_calc.2]
  constructor

  ·                                                   
                                                                
    have hs_re_bound : |s.re| ≤ 1 :=
      (Complex.abs_re_le_norm s).trans hs
    rw [abs_le] at hs_re_bound

    rw [Set.mem_Ico]
    constructor
    ·                                     
      linarith [hs_re_bound.1]
    ·                                    
      linarith [hs_re_bound.2]

  ·                                            
    have hs_im_bound : |s.im| ≤ 1 :=
      (Complex.abs_im_le_norm s).trans hs
    rw [abs_le] at hs_im_bound

    by_cases h : 0 ≤ t
    ·                                        
      have ht_pos : t > 2 := by
        rwa [abs_of_nonneg h] at ht
                                       
      have lower_bound : s.im + t ≥ 1 := by
        linarith [hs_im_bound.1, ht_pos]
      have nonneg : 0 ≤ s.im + t := by linarith
      rw [abs_of_nonneg nonneg]
      linarith [lower_bound]
    ·                                                     
      push Not at h
      have ht_neg : t < -2 := by
        rw [abs_of_neg h] at ht
        linarith [ht]
                                                                 
      have upper_bound : s.im + t ≤ -1 := by
        linarith [hs_im_bound.2, ht_neg]
      have neg : s.im + t < 0 := by linarith
      rw [abs_of_neg neg]
      linarith [upper_bound]

lemma lem_abs_im_bound (s : ℂ) (t : ℝ) (hs : ‖s‖ ≤ 1) : |s.im + t| ≤ 1 + |t| := by
  have h1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have h2 : |s.im| ≤ 1 := le_trans h1 hs
  have h3 : |s.im + t| ≤ |s.im| + |t| := abs_add_le s.im t
  linarith

lemma lem_zetaUppBound :
    ∀ t : ℝ, ∀ s : ℂ, ‖s‖ ≤ (1 : ℝ) → (2 : ℝ) < |t| →
      ‖riemannZeta (s + (3/2 : ℝ) + I * t)‖ < (10 : ℝ) + 2 * |t| := by
  intro t s hs ht
  set z := s + (3/2 : ℝ) + I * t with hz_def
                                                       
  have hz_cond : z.re ∈ Ico (1/2 : ℝ) (3 : ℝ) ∧ (1 : ℝ) ≤ |z.im| :=
    lem_zfroms_conditions s t hs ht
                        
  have h_bound : ‖riemannZeta z‖ < (8 : ℝ) + 2 * |z.im| :=
    lem_zetaUppBd z hz_cond.1 hz_cond.2
                                         
  have hz_im_calc : z.im = s.im + t := (lem_zfroms_calc s t).2
  have h_im_bound : |z.im| ≤ 1 + |t| := by
    rw [hz_im_calc]
    exact lem_abs_im_bound s t hs
                   
  have h_intermediate : ‖riemannZeta z‖ < (8 : ℝ) + 2 * (1 + |t|) := by
    calc ‖riemannZeta z‖
      < (8 : ℝ) + 2 * |z.im| := h_bound
      _ ≤ (8 : ℝ) + 2 * (1 + |t|) := by linarith [h_im_bound]
                           
  have h_algebra : (8 : ℝ) + 2 * (1 + |t|) = (10 : ℝ) + 2 * |t| := by ring
                
  have h_final : ‖riemannZeta z‖ < (10 : ℝ) + 2 * |t| := by
    linarith [h_intermediate, h_algebra]
                                                
  rwa [hz_def] at h_final

open _root_.Metric _root_.Set _root_.Filter _root_.Asymptotics _root_.BigOperators
















lemma sigmageq1 (s : ℂ) (hs : s.re > 1) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re hs

lemma Complex_I_mul_ofReal_re (r : ℝ) : (I * (r : ℂ)).re = 0 := by
  have h : (I * (r : ℂ)).re = -(r : ℂ).im := Complex.I_mul_re (r : ℂ)
  rw [h]
  simp

lemma re_real_add_I_mul_gt (a b : ℝ) (h : a > 1) : (a + I * b).re > 1 := by
  rw [Complex.add_re]
  rw [Complex.ofReal_re]
  rw [Complex_I_mul_ofReal_re]
  simp
  exact h

lemma zetacnot0 (t : ℝ) : riemannZeta (3/2 + I * t) ≠ 0 := by
  apply sigmageq1
  apply re_real_add_I_mul_gt
  norm_num





















lemma zeta32lower : ∃ a > 0, ∀ t : ℝ, ‖riemannZeta (3/2 + I * t)‖ ≥ a := by
  rcases zeta_low_332 with ⟨a, ha_pos, hbound⟩
  refine ⟨a, ha_pos, ?_⟩
  intro t
  simpa [mul_comm] using! (hbound t)

lemma zeta32lower_log : ∃ A > 1, ∀ t : ℝ,
    Real.log (1 / ‖riemannZeta (3/2 + I * t)‖) ≤ A := by
  obtain ⟨a, ha_pos, hbound⟩ := zeta32lower
  refine ⟨max (2 : ℝ) (Real.log (1 / a)), ?_, ?_⟩
  · have h1 : (1 : ℝ) < 2 := by norm_num
    have h2 : (2 : ℝ) ≤ max (2 : ℝ) (Real.log (1 / a)) := by exact le_max_left _ _
    exact lt_of_lt_of_le h1 h2
  · intro t
    set x := ‖riemannZeta (3/2 + I * t)‖ with hx
    have hax : a ≤ x := by
      simpa [hx] using (hbound t)
    have hxpos : 0 < x := lt_of_lt_of_le ha_pos hax
    have hxy : 1 / x ≤ 1 / a := by
                                               
      have := one_div_le_one_div_of_le ha_pos hax
                                          
      simpa [hx] using this
    have hxpos' : 0 < 1 / x := one_div_pos.mpr hxpos
    have hlog : Real.log (1 / x) ≤ Real.log (1 / a) :=
      Real.log_le_log hxpos' hxy
    have : Real.log (1 / x) ≤ max (2 : ℝ) (Real.log (1 / a)) :=
      le_trans hlog (le_max_right _ _)
    simpa [hx] using this

lemma zeta32upper_pre : ∃ b > 1, ∀ t : ℝ, ∀ s : ℂ, ‖s‖ ≤ 1 → (2 : ℝ) < |t| → ‖riemannZeta (s + 3/2 + Complex.I * t)‖ < b * |t| := by
  refine ⟨(12 : ℝ), by norm_num, ?_⟩
  intro t s hs ht
  have hlt : ‖riemannZeta (s + 3/2 + Complex.I * t)‖ < (10 : ℝ) + 2 * |t| := by
    simpa using! (lem_zetaUppBound t s hs ht)
  have honele : (1 : ℝ) ≤ |t| := by
    have : (1 : ℝ) < |t| := lt_trans (by norm_num) ht
    exact le_of_lt this
  have h10le : (10 : ℝ) ≤ 10 * |t| := by
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_right honele (by norm_num : (0 : ℝ) ≤ (10 : ℝ)))
  have hle2 : (10 : ℝ) + 2 * |t| ≤ (12 : ℝ) * |t| := by
    have htmp := add_le_add_left h10le (2 * |t|)
    have hcalc : 10 * |t| + 2 * |t| = (12 : ℝ) * |t| := by ring
    simpa [hcalc] using! htmp
  exact lt_of_lt_of_le hlt hle2

lemma zeta32upper : ∃ b > 1, ∀ t : ℝ, |t| > 2 →
  let c := (3/2 : ℂ) + I * t
  ∀ s ∈ closedBall c 1, ‖riemannZeta s‖ < b * |t| := by
                                         
  obtain ⟨b, hb_gt, hbound⟩ := zeta32upper_pre
  refine ⟨b, hb_gt, ?_⟩
  intro t ht c s hs
                                         
  rw [mem_closedBall] at hs
                                         
  set s_pre := s - c with hs_pre_def
  have hs_pre_bound : ‖s_pre‖ ≤ 1 := by
    rw [hs_pre_def]
    rwa [Complex.dist_eq] at hs
                                            
  have hs_eq : s = s_pre + 3/2 + I * t := by
    rw [hs_pre_def]
    ring
                          
  rw [hs_eq]
  exact hbound t s_pre hs_pre_bound ht








end Erdos970

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.Z0
namespace Erdos970

open _root_.Complex _root_.Topology _root_.Filter _root_.Interval _root_.Set _root_.Asymptotics

local notation (name := riemannzeta1) "ζ" => riemannZeta
local notation (name := derivriemannzeta1) "ζ'" => deriv riemannZeta

lemma Z0bound_aux :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (fun (delta : ℝ) => -(ζ' / ζ) ((1 : ℂ) + delta) - (1 / (delta : ℂ))) (fun _ => (1 : ℂ)) := by

  let F := fun s : ℂ => -(ζ' / ζ) s - (s - 1)⁻¹

  have h_F_bigO : F =O[𝓝[≠] 1] (1 : ℂ → ℂ) := by
    have h_fun_eq : F = (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) := by
      ext s
      simp only [F, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, neg_div]
    rw [h_fun_eq]
    exact riemannZetaLogDerivResidueBigO

  let u := fun (delta : ℝ) => (1 : ℂ) + delta
  have h_tendsto : Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (𝓝[≠] 1) := by

    apply tendsto_inf.mpr
    constructor
    ·                                     
      have h_cont : Continuous u := continuous_const.add continuous_ofReal
                                                             
      have h_tendsto_nhds : Tendsto u (𝓝 0) (𝓝 (u 0)) := h_cont.continuousAt.tendsto
                                                                     
      simp only [u, Complex.ofReal_zero, add_zero] at h_tendsto_nhds

      exact h_tendsto_nhds.mono_left nhdsWithin_le_nhds
    ·                                                  
                                                      
      simp
                                                  
      filter_upwards [self_mem_nhdsWithin] with delta h_delta_pos
      simp only [u]

      refine add_ne_left.mpr ?_
      rw [Complex.ofReal_ne_zero]
      exact ne_of_gt h_delta_pos

  have h_comp := h_F_bigO.comp_tendsto h_tendsto

  convert (preTransparency := .instances) h_comp using 1
  ext delta
                                                           
  simp only [F, u, Function.comp_apply, Pi.div_apply]
  rw [inv_eq_one_div]
  aesop
  all_goals rfl

lemma Z0bound :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (fun (delta : ℝ) => -logDerivZeta ((1 : ℂ) + delta) - (1 / (delta : ℂ))) (fun _ => (1 : ℂ)) := Z0bound_aux

end Erdos970

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.PNT4_ZeroFreeRegion
namespace Erdos970




lemma ZetaZerosNearPoint_finite (t : ℝ) : Set.Finite (ZetaZerosNearPoint t) := by
                                  
  let c : ℂ := (3/2 : ℂ) + t * Complex.I
  let R : ℝ := (5/6 : ℝ)
  have hRpos : 0 < R := by norm_num

  let H : ℂ → ℂ := Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1
  have hH_diff : Differentiable ℂ H := by
                                                               
    intro s
    rcases eq_or_ne s 1 with rfl | hs
    ·                                                                                                
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      ·                                             
        filter_upwards [self_mem_nhdsWithin] with t ht
                                                                              
        have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) t := by
          have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) t :=
            (differentiableAt_id.sub_const 1)
          have h2 : DifferentiableAt ℂ riemannZeta t :=
            (differentiableAt_riemannZeta ht)
          exact h1.mul h2
        apply DifferentiableAt.congr_of_eventuallyEq hdiff
        filter_upwards [eventually_ne_nhds ht] with u hu using by
          simp [H, Function.update_of_ne hu]
      ·                                                           
        simpa [H, continuousAt_update_same] using riemannZeta_residue_one
    ·                                                        
      have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) s := by
        have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) s :=
          (differentiableAt_id.sub_const 1)
        have h2 : DifferentiableAt ℂ riemannZeta s :=
          (differentiableAt_riemannZeta hs)
        exact h1.mul h2
      apply DifferentiableAt.congr_of_eventuallyEq hdiff
      filter_upwards [eventually_ne_nhds hs] with u hu using by
        simp [H, Function.update_of_ne hu]

  by_cases hPoleIn : ‖1 - c‖ ≤ R
  ·                                                         
    let g : ℂ → ℂ := fun z => H (z + c)
                                                                                                   
    have hzeta_c_ne : riemannZeta c ≠ 0 := by
                                     
      have : c.re = (3/2 : ℝ) := by
        simp [c, Complex.add_re, Complex.mul_re, Complex.I_re]
      have hgt : c.re > 1 := by simpa [this] using (by norm_num : (3:ℝ)/2 > 1)
                                                             
      exact riemannZeta_ne_zero_of_one_le_re (by
                        
        have : (1 : ℝ) < c.re := hgt
        exact le_of_lt this)
    have hg_nonzero : ∃ z ∈ Metric.ball (0 : ℂ) R, g z ≠ 0 := by
                                                           
      have h0in : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hRpos
      refine ⟨0, h0in, ?_⟩
                                                             
      have hcne1 : c ≠ (1 : ℂ) := by
        intro hc; have hcreq : c.re = 1 := by simp [hc, Complex.one_re]
        have : (3 : ℝ) / 2 = (1 : ℝ) := by
          simpa [c, Complex.add_re, Complex.mul_re, Complex.I_re] using hcreq
        norm_num at this
      have hHc : g 0 = H c := by simp [g]
      have : g 0 = (c - 1) * riemannZeta c := by
        simpa [H, Function.update_of_ne hcne1] using hHc
      simpa [this] using mul_ne_zero (sub_ne_zero.mpr (by
                                 
        exact hcne1)) hzeta_c_ne
                                                  
    let Kg : Set ℂ := {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ g ρ = 0}
                                                                        
    have h_subset : ZetaZerosNearPoint t ⊆ {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} := by
      intro ρ hρ
      rcases hρ with ⟨hzero, hdist⟩
                                          
      have hball : ρ - c ∈ Metric.closedBall 0 R := by
        simpa [Metric.mem_closedBall, Complex.dist_eq, c, sub_eq_add_neg] using hdist
                                                      
      have hρne1 : (ρ : ℂ) ≠ 1 := by
        intro hρ1
                                          
        have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
        exact hz1_ne (by simpa [hρ1] using! hzero)
      have hsum : (ρ - c) + c = ρ := by simp [sub_add_cancel]
      have hxne : (ρ - c) + c ≠ (1 : ℂ) := by simpa [hsum] using hρne1
      have hform : g (ρ - c) = (ρ - 1) * riemannZeta ρ := by
        simp [g, H, hsum, Function.update_of_ne hxne]
      have hzeroζ : riemannZeta ρ = 0 := hzero
      have hzero' : g (ρ - c) = 0 := by simp [hform, hzeroζ]
      exact ⟨hball, hzero'⟩
                                                                                                 
    have hg_diff : Differentiable ℂ g := by
      intro z
      have hH := hH_diff (z + c)
      have h_addc : DifferentiableAt ℂ (fun z : ℂ => z + c) z :=
        (differentiableAt_id.add_const c)
      simpa [g] using! hH.comp z h_addc
    have hg_analyticNhd_univ : AnalyticOnNhd ℂ g Set.univ :=
      (Complex.analyticOnNhd_univ_iff_differentiable).2 hg_diff
    have hg_analyticNhd : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) :=
      AnalyticOnNhd.mono hg_analyticNhd_univ (by intro z hz; simp)
    have hNonzero : ∃ z ∈ Metric.ball (0 : ℂ) 1, g z ≠ 0 := by
      rcases hg_nonzero with ⟨z, hz_in, hz_ne⟩
                                        
      have hz_in' : z ∈ Metric.ball (0 : ℂ) 1 := by
        have hRle : (R : ℝ) ≤ 1 := by norm_num
        exact Metric.ball_subset_ball hRle hz_in
      exact ⟨z, hz_in', hz_ne⟩
    have hfiniteKg : Set.Finite Kg :=
      (lem_Contra_finiteKR R hRpos (by norm_num : R < 1) g hg_analyticNhd hNonzero)
                                                                    
    have hTarget_eq : {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} =
          (fun ρ : ℂ => ρ + c) '' Kg := by
      ext ρ; constructor
      · intro h
        rcases h with ⟨hball, hzero⟩
        refine ⟨ρ - c, ⟨?_, ?_⟩, ?_⟩
        · exact hball
        · exact hzero
        · simp [sub_add_cancel]
      · intro h
        rcases h with ⟨z, ⟨hzball, hz0⟩, rfl⟩
        constructor
        · simpa [sub_add_cancel] using hzball
        · simpa [sub_add_cancel] using hz0
                                                                                    
    have hTarget_fin : Set.Finite {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} := by
      have himg : Set.Finite ((fun ρ : ℂ => ρ + c) '' Kg) := hfiniteKg.image _
                                                
      exact hTarget_eq ▸ himg
    exact Set.Finite.subset hTarget_fin h_subset
  ·                                             
    let g : ℂ → ℂ := fun z => H (z + c)
                                          
    have hzeta_c_ne : riemannZeta c ≠ 0 := by
      have : c.re = (3/2 : ℝ) := by
        simp [c, Complex.add_re, Complex.mul_re, Complex.I_re]
      have hgt : c.re > 1 := by simpa [this] using (by norm_num : (3:ℝ)/2 > 1)
      exact riemannZeta_ne_zero_of_one_le_re (le_of_lt hgt)
    have hg_nonzero : ∃ z ∈ Metric.ball (0 : ℂ) R, g z ≠ 0 := by
      have h0in : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hRpos
      refine ⟨0, h0in, ?_⟩
      have hcne1 : c ≠ (1 : ℂ) := by
        intro hc; have hcreq : c.re = 1 := by simp [hc, Complex.one_re]
        have : (3 : ℝ) / 2 = (1 : ℝ) := by
          simpa [c, Complex.add_re, Complex.mul_re, Complex.I_re] using hcreq
        norm_num at this
                                      
      have hHc : g 0 = H c := by simp [g]
      have : g 0 = (c - 1) * riemannZeta c := by
        simpa [H, Function.update_of_ne hcne1] using hHc
      simpa [this] using mul_ne_zero (sub_ne_zero.mpr hcne1) hzeta_c_ne
                                          
    let Kg : Set ℂ := {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ g ρ = 0}
                     
    have h_subset : ZetaZerosNearPoint t ⊆ {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} := by
      intro ρ hρ
      rcases hρ with ⟨hzero, hdist⟩
      have hball : ρ - c ∈ Metric.closedBall 0 R := by
        simpa [Metric.mem_closedBall, Complex.dist_eq, c, sub_eq_add_neg] using hdist
      have hρne1 : (ρ : ℂ) ≠ 1 := by
        intro hρ1
        have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
        exact hz1_ne (by simpa [hρ1] using! hzero)
      have hsum : (ρ - c) + c = ρ := by simp [sub_add_cancel]
      have hxne : (ρ - c) + c ≠ (1 : ℂ) := by simpa [hsum] using hρne1
      have hform : g (ρ - c) = (ρ - 1) * riemannZeta ρ := by
        simp [g, H, hsum, Function.update_of_ne hxne]
                                                   
      have hzeroζ : riemannZeta ρ = 0 := hzero
      have hzero' : g (ρ - c) = 0 := by
        calc
          g (ρ - c) = (ρ - 1) * riemannZeta ρ := hform
          _ = (ρ - 1) * 0 := by simp [hzeroζ]
          _ = 0 := by simp
      exact ⟨hball, hzero'⟩
                            
    have hg_diff : Differentiable ℂ g := by
      intro z
      have hH := hH_diff (z + c)
      have h_addc : DifferentiableAt ℂ (fun z : ℂ => z + c) z :=
        (differentiableAt_id.add_const c)
      simpa [g] using! hH.comp z h_addc
    have hg_analyticNhd_univ : AnalyticOnNhd ℂ g Set.univ :=
      (Complex.analyticOnNhd_univ_iff_differentiable).2 hg_diff
    have hg_analyticNhd : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) :=
      AnalyticOnNhd.mono hg_analyticNhd_univ (by intro z hz; simp)
    have hNonzero : ∃ z ∈ Metric.ball (0 : ℂ) 1, g z ≠ 0 := by
      rcases hg_nonzero with ⟨z, hz_in, hz_ne⟩
      have hz_in' : z ∈ Metric.ball (0 : ℂ) 1 := by
        have hRle : (R : ℝ) ≤ 1 := by norm_num
        exact Metric.ball_subset_ball hRle hz_in
      exact ⟨z, hz_in', hz_ne⟩
    have hfiniteKg : Set.Finite Kg :=
      (lem_Contra_finiteKR R hRpos (by norm_num : R < 1) g hg_analyticNhd hNonzero)
    have hTarget_eq : {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} =
          (fun ρ : ℂ => ρ + c) '' Kg := by
      ext ρ; constructor
      · intro h
        rcases h with ⟨hball, hzero⟩
        refine ⟨ρ - c, ⟨?_, ?_⟩, ?_⟩
        · exact hball
        · exact hzero
        · simp [sub_add_cancel]
      · intro h
        rcases h with ⟨z, ⟨hzball, hz0⟩, rfl⟩
        constructor
        · simpa [sub_add_cancel] using hzball
        · simpa [sub_add_cancel] using hz0
    have hTarget_fin : Set.Finite {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} := by
      have himg : Set.Finite ((fun ρ : ℂ => ρ + c) '' Kg) := hfiniteKg.image _
      exact hTarget_eq ▸ himg
    exact Set.Finite.subset hTarget_fin h_subset

lemma lem_Re1zge0 (z : ℂ) : z.re > 0 → (1 / z).re > 0 := by
  intro h
                          
  have hz_ne_zero : z ≠ 0 := by
    intro hz_eq_zero
    rw [hz_eq_zero] at h
    simp at h
                                
  rw [one_div]
                                               
  rw [Complex.inv_re]
                                                                                                     
  apply div_pos h
                             
  rwa [Complex.normSq_pos]

lemma lem_sigmage1 (sigma t : ℝ) (hsigma : sigma > 1) : riemannZeta (sigma + t * Complex.I) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_le_re
  simp [Complex.add_re, Complex.mul_re, Complex.I_re]
  linarith

lemma lem_sigmale1 (sigma1 t1 : ℝ) : riemannZeta (sigma1 + t1 * Complex.I) = 0 → sigma1 ≤ 1 := by
  intro h
                                       
  by_contra h_not_le
                                                   
  push Not at h_not_le
                                                                             
  have h_nonzero := lem_sigmage1 sigma1 t1 h_not_le
                                                              
  exact h_nonzero h

lemma lem_sigmale1Zt (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) : rho1.re ≤ 1 := by
                                                                    
  have h1 : rho1 ∈ zeroZ := h_rho1_in_Zt.1
                                                                  
  have h2 : riemannZeta rho1 = 0 := h1
                                                       
  have h3 : rho1 = rho1.re + rho1.im * Complex.I := by simp [Complex.re_add_im]
                                         
  rw [h3] at h2
                           
  exact lem_sigmale1 rho1.re rho1.im h2


lemma complex_abs_of_real (x : ℝ) : ‖(x : ℂ)‖ = abs x := by
  rw [Complex.norm_real, Real.norm_eq_abs]


lemma complex_abs_real_cast (r : ℝ) : ‖(r : ℂ)‖ = abs r := Complex.norm_real r




lemma zerosetKfRc_eq_ZetaZerosNearPoint (t : ℝ) :
  zerosetKfRc (5/6 : ℝ) ((3/2 : ℂ) + t * Complex.I) riemannZeta = ZetaZerosNearPoint t := by
  ext ρ; constructor
  · intro h
    rcases h with ⟨hball, hzero⟩
    refine ⟨?hz, ?hnorm⟩
    · simpa [zeroZ] using hzero
    · simpa [Metric.mem_closedBall, Complex.dist_eq, sub_eq_add_neg] using hball
  · intro h
    rcases h with ⟨hz, hnorm⟩
    refine ⟨?hball, ?hzero⟩
    · simpa [Metric.mem_closedBall, Complex.dist_eq, sub_eq_add_neg] using hnorm
    · simpa [zeroZ] using hz



lemma center_eq_comm (t : ℝ) :
  ((3/2 : ℂ) + (Complex.I : ℂ) * (t : ℂ)) = ((3/2 : ℂ) + (t : ℂ) * Complex.I) := by
  have h : (Complex.I : ℂ) * (t : ℂ) = (t : ℂ) * Complex.I := by
    simpa using mul_comm (Complex.I : ℂ) (t : ℂ)
  simp [h]

lemma log_abs_le_log_abs_add_two {t : ℝ} (ht : 2 < |t|) :
  Real.log (abs t) ≤ Real.log (abs t + 2) := by
  have hpos : 0 < |t| := lt_trans (by norm_num) ht
  have hle : |t| ≤ |t| + 2 := by nlinarith
  simpa using Real.log_le_log hpos hle

lemma s_notin_ZetaZerosNearPoint (δ t : ℝ) (hδ_pos : 0 < δ) :
  ((1 : ℂ) + δ + t * Complex.I) ∉ ZetaZerosNearPoint t := by
  intro hmem
  have hz0 : riemannZeta ((1 : ℂ) + δ + t * Complex.I) = 0 := hmem.1
  have : ((1 : ℂ) + δ + t * Complex.I).re = 1 + δ := by simp
  have hpos : (1 : ℝ) < 1 + δ := by linarith
  have hnonzero := lem_sigmage1 (1 + δ) t hpos
  exact hnonzero (by simpa using hz0)

lemma norm_sub_comm' (x y : ℂ) : ‖x - y‖ = ‖y - x‖ := by
  calc
    ‖x - y‖ = ‖-(x - y)‖ := by simpa using (norm_neg (x - y)).symm
    _ = ‖y - x‖ := by simp [neg_sub]

lemma s_in_closedBall_12 (δ t : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
  ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) ∈
    Metric.closedBall ((3 / 2 : ℂ) + (t : ℝ) * Complex.I) (1 / 2) := by
                                         
  have hdiff :
      ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) - ((3 / 2 : ℂ) + (t : ℝ) * Complex.I)
        = ((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ) := by
    simp
  have hreal :
      ((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ) = ((δ - (1 / 2 : ℝ)) : ℂ) := by
    have h' : ((1 + δ : ℝ) - (3 / 2 : ℝ)) = δ - (1 / 2 : ℝ) := by
      calc
        (1 + δ) - (3 / 2 : ℝ) = δ + 1 - (3 / 2 : ℝ) := by ac_rfl
        _ = δ + (1 - (3 / 2 : ℝ)) := by simp [add_sub_assoc]
        _ = δ + (- (1 / 2 : ℝ)) := by norm_num
        _ = δ - (1 / 2 : ℝ) := by simp [sub_eq_add_neg]
    calc
      ((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ)
          = ((1 + δ : ℝ) : ℂ) - (3 / 2 : ℂ) := by
              simp [add_comm]
      _ = (↑((1 + δ : ℝ) - (3 / 2 : ℝ)) : ℂ) := by
              simp [Complex.ofReal_sub]
      _ = ((δ - (1 / 2 : ℝ)) : ℂ) := by simp [h']
  have hnormle :
      ‖((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) - ((3 / 2 : ℂ) + (t : ℝ) * Complex.I)‖
        ≤ (1 / 2 : ℝ) := by
    calc
      ‖((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) - ((3 / 2 : ℂ) + (t : ℝ) * Complex.I)‖
          = ‖((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ)‖ := by simp [hdiff]
      _ = ‖((δ - (1 / 2 : ℝ)) : ℂ)‖ := by simp [hreal]
      _ = |δ - (1 / 2 : ℝ)| := by simpa using complex_abs_real_cast (δ - (1 / 2 : ℝ))
      _ ≤ 1 / 2 := by
        have hleft : - (1 / 2 : ℝ) ≤ δ - 1 / 2 := by linarith [hδ_pos]
        have hright : δ - 1 / 2 ≤ 1 / 2 := by linarith [hδ_lt]
        simpa using (abs_le.mpr ⟨hleft, hright⟩)
                                           
  simpa [Metric.mem_closedBall, Complex.dist_eq] using hnormle

lemma lem_explicit1deltat :
  ∃ C > 1,
      ∀ t : ℝ, 2 < |t| →
        ∀ δ : ℝ, 0 < δ ∧ δ < 1 →
          ‖Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
                  (fun rho1 : ℂ =>
                    ((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
                      (((1 : ℂ) + δ + t * Complex.I) - rho1))
                - logDerivZeta ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I)‖
          ≤ C * Real.log (abs t + 2) := by
  classical
                               
  let r1 : ℝ := (1/2 : ℝ)
  let r  : ℝ := (2/3 : ℝ)
  let R1 : ℝ := (5/6 : ℝ)
  let R  : ℝ := (9/10 : ℝ)
  have hr1_pos : 0 < r1 := by norm_num
  have hr_pos  : 0 < r := by norm_num
  have hr1_lt_r : r1 < r := by norm_num
  have hr_lt_R1 : r < R1 := by norm_num
  have hR1_pos : 0 < R1 := by norm_num
  have hR1_lt_R : R1 < R := by norm_num
  have hR_lt_1  : R < 1 := by norm_num
                     
  let F : ℝ := (16 * r^2 / ((r - r1)^3) + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)))
                       
  obtain ⟨b, hb_gt1, hb_bound⟩ := zeta32upper
  obtain ⟨A, hA_gt1, hA_bound⟩ := zeta32lower_log
                                                      
  let K : ℝ := 1 + (Real.log b + A) / Real.log 4
                   
  let C : ℝ := max (F * K) 2
  have hC_gt1 : 1 < C := by
    have : (1 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le this (le_max_right _ _)
  refine ⟨C, hC_gt1, ?_⟩
                             
  intro t ht δ hδ
  rcases hδ with ⟨hδ_pos, hδ_lt1⟩
                                 
  let c_std : ℂ := ((3/2 : ℂ) + Complex.I * (t : ℂ))
  let c_comm : ℂ := ((3/2 : ℂ) + (t : ℝ) * Complex.I)
  have hcenter_eq : c_std = c_comm := by simpa [c_std, c_comm] using (center_eq_comm t)
  let s : ℂ := (1 : ℂ) + δ + t * Complex.I
                            
  have hs_mem_comm : s ∈ Metric.closedBall c_comm r1 := s_in_closedBall_12 δ t hδ_pos hδ_lt1
  have hs_mem_std : s ∈ Metric.closedBall c_std r1 := by simpa [c_std, c_comm, hcenter_eq] using hs_mem_comm
                 
  have hs_notin_Zt : s ∉ ZetaZerosNearPoint t := s_notin_ZetaZerosNearPoint δ t hδ_pos
  have hzeros_eq : zerosetKfRc (5/6 : ℝ) c_comm riemannZeta = ZetaZerosNearPoint t := by
    simpa [c_comm] using zerosetKfRc_eq_ZetaZerosNearPoint t
  have hs_notin_comm : s ∉ zerosetKfRc (5/6 : ℝ) c_comm riemannZeta := by simpa [hzeros_eq] using hs_notin_Zt
  have hs_notin_std : s ∉ zerosetKfRc (5/6 : ℝ) c_std riemannZeta := by simpa [c_std, c_comm, hcenter_eq] using hs_notin_comm
                    
  have hfin_comm : (zerosetKfRc (5/6 : ℝ) c_comm riemannZeta).Finite := by
    simpa [hzeros_eq] using (ZetaZerosNearPoint_finite t)
  have hfin_std : (zerosetKfRc (5/6 : ℝ) c_std riemannZeta).Finite := by
    simpa [c_std, c_comm, hcenter_eq] using hfin_comm
                                                         
  have h_bound_R : ∀ z ∈ Metric.closedBall c_std R, ‖riemannZeta z‖ < b * |t| := by
    intro z hz
    have hsubs : Metric.closedBall c_std R ⊆ Metric.closedBall c_std (1 : ℝ) := by
      intro w hw; exact Metric.closedBall_subset_closedBall (by norm_num : (R : ℝ) ≤ (1 : ℝ)) hw
    exact hb_bound t (by simpa using ht) z (hsubs hz)
                                  
  have hmain :=
    log_Deriv_Expansion_Zeta t ht
      r1 r R1 R hr1_pos hr1_lt_r hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1
                    
  have hbpos : 0 < b := lt_trans (by norm_num) hb_gt1
  have ht1 : 1 < |t| := lt_trans (by norm_num) ht
  have hmul : b * 1 < b * |t| := (mul_lt_mul_of_pos_left ht1 hbpos)
  have hB_gt1 : 1 < b * |t| := lt_trans hb_gt1 (by simpa using hmul)
  have hineq := hmain (b * |t|) hB_gt1 h_bound_R
  have hz_in : s ∈ Metric.closedBall c_std r1 \ zerosetKfRc (5/6 : ℝ) c_std riemannZeta := ⟨hs_mem_std, hs_notin_std⟩
  have hineq2 := hineq hfin_std s hz_in
                                                           
  have hFinset_eq : hfin_std.toFinset = (ZetaZerosNearPoint_finite t).toFinset := by
    ext ρ; constructor <;> intro hρ
    · have : ρ ∈ zerosetKfRc (5/6 : ℝ) c_std riemannZeta := by simpa [Set.mem_toFinset] using hρ
      have : ρ ∈ ZetaZerosNearPoint t := by
        have heq : zerosetKfRc (5/6 : ℝ) c_std riemannZeta = zerosetKfRc (5/6 : ℝ) c_comm riemannZeta := by
                                                                                    
          simp [c_std, c_comm, hcenter_eq]
        simpa [hzeros_eq, heq]
          using this
      simpa [Set.mem_toFinset] using this
    · have : ρ ∈ ZetaZerosNearPoint t := by simpa [Set.mem_toFinset] using hρ
      have : ρ ∈ zerosetKfRc (5/6 : ℝ) c_comm riemannZeta := by simpa [hzeros_eq] using this
      have heq : zerosetKfRc (5/6 : ℝ) c_std riemannZeta = zerosetKfRc (5/6 : ℝ) c_comm riemannZeta := by
        simp [c_std, c_comm, hcenter_eq]
      have : ρ ∈ zerosetKfRc (5/6 : ℝ) c_std riemannZeta := by simpa [heq] using this
      simpa [Set.mem_toFinset] using this
  have hLHS_le :
      ‖Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
            (fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (s - rho1))
          - logDerivZeta s‖
      ≤ F * Real.log (b * |t| / ‖riemannZeta c_std‖) := by
    have :
        ‖logDerivZeta s -
            Finset.sum (hfin_std.toFinset)
              (fun ρ : ℂ => ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (s - ρ))‖
        ≤ F * Real.log (b * |t| / ‖riemannZeta c_std‖) := by
      simpa [F] using! hineq2
    simpa [norm_sub_comm', hFinset_eq]
      using this
                                   
  have hc_ne : riemannZeta c_std ≠ 0 := by simpa [c_std] using! zetacnot0 t
  have hnorm_pos : 0 < ‖riemannZeta c_std‖ := by simpa [norm_pos_iff] using hc_ne
  have hnorm_ne : ‖riemannZeta c_std‖ ≠ 0 := ne_of_gt hnorm_pos
  have hb_ne : b ≠ 0 := ne_of_gt hbpos
  have htpos0 : 0 < |t| := lt_trans (by norm_num) ht
  have ht_ne : |t| ≠ 0 := ne_of_gt htpos0
  have hlog_mul1 :
      Real.log (b * |t| / ‖riemannZeta c_std‖)
        = Real.log (b * |t|) + Real.log (1 / ‖riemannZeta c_std‖) := by
    simpa [div_eq_mul_inv] using Real.log_mul (mul_ne_zero hb_ne ht_ne) (inv_ne_zero hnorm_ne)
  have hlog_mul2 : Real.log (b * |t|) = Real.log b + Real.log (|t|) := by
    simpa using Real.log_mul hb_ne ht_ne
  have hζ_log_le : Real.log (1 / ‖riemannZeta c_std‖) ≤ A := by
    simpa [c_std] using! hA_bound t
  have hlog_bound1 :
      Real.log (b * |t| / ‖riemannZeta c_std‖)
        ≤ (Real.log b + Real.log (|t|)) + A := by
    have := add_le_add_right hζ_log_le (Real.log (b * |t|))
    simpa [hlog_mul1, hlog_mul2, add_comm, add_left_comm, add_assoc] using this
                                    
  have hlog_mono : Real.log (|t|) ≤ Real.log (|t| + 2) :=
    log_abs_le_log_abs_add_two (by simpa using ht)
  have hlog_bound2 :
      Real.log (b * |t| / ‖riemannZeta c_std‖)
        ≤ Real.log (|t| + 2) + (Real.log b + A) := by
    have : Real.log b + Real.log (|t|) + A ≤ Real.log b + Real.log (|t| + 2) + A := by
      have := add_le_add_right hlog_mono (Real.log b)
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left this A
    exact le_trans hlog_bound1 (by simpa [add_comm, add_left_comm, add_assoc] using this)
                                                
  have hlog5pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hge5 : Real.log 4 ≤ Real.log (|t| + 2) := by
    have hxy : (4 : ℝ) ≤ |t| + 2 := by nlinarith [le_of_lt ht]
    exact Real.log_le_log (by norm_num) hxy
  have hconst_nonneg : 0 ≤ Real.log b + A := by
    have hbposlog : 0 < Real.log b := Real.log_pos hb_gt1
    have hApos : 0 < A := lt_trans (by norm_num) hA_gt1
    have : 0 ≤ Real.log b := le_of_lt hbposlog
    nlinarith
  have hnonneg : 0 ≤ (Real.log b + A) / Real.log 4 := div_nonneg hconst_nonneg (le_of_lt hlog5pos)
  have hne5 : Real.log 4 ≠ 0 := ne_of_gt hlog5pos
  have hconst_bound : (Real.log b + A)
        ≤ (Real.log b + A) / Real.log 4 * Real.log (|t| + 2) := by
    have := mul_le_mul_of_nonneg_left hge5 hnonneg
                             
    have : ((Real.log b + A) / Real.log 4) * Real.log 4 ≤ (Real.log b + A) / Real.log 4 * Real.log (|t| + 2) := this
                                        
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hne5] using this
  have hlog_bound3 :
      Real.log (|t| + 2) + (Real.log b + A)
        ≤ K * Real.log (|t| + 2) := by
    have := add_le_add_right hconst_bound (Real.log (|t| + 2))

    simpa [K, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, one_mul]
      using this
  have hlog_bound_final :
      Real.log (b * |t| / ‖riemannZeta c_std‖)
        ≤ K * Real.log (|t| + 2) := le_trans hlog_bound2 hlog_bound3
               
  have hF_nonneg : 0 ≤ F := by
    have h1 : 0 ≤ 16 * r ^ 2 / (r - r1) ^ 3 := by
      have hnum : 0 ≤ 16 * r ^ 2 := by
        have : 0 ≤ (16 : ℝ) := by norm_num
        have : 0 ≤ r ^ 2 := by
          have := sq_nonneg r
          simpa [pow_two] using this
        simpa [mul_comm] using mul_nonneg (show 0 ≤ (16 : ℝ) by norm_num) this
      have hden : 0 < (r - r1) ^ 3 := by
        have : 0 < r - r1 := sub_pos.mpr hr1_lt_r
        simpa using pow_pos this 3
      exact div_nonneg hnum (le_of_lt hden)
    have h2 : 0 ≤ 1 / ((R ^ 2 / R1 - R1) * Real.log (R / R1)) := by
                           
      have hden1 : 0 < (R ^ 2 / R1 - R1) := by
        change 0 < ((9/10 : ℝ) ^ 2 / (5/6 : ℝ) - (5/6 : ℝ))
        norm_num
      have hden2 : 0 < Real.log (R / R1) := by
        have : 1 < R / R1 := by
          change (1 : ℝ) < (9/10 : ℝ) / (5/6 : ℝ)
          norm_num
        exact Real.log_pos this
      have hpos : 0 < ((R ^ 2 / R1 - R1) * Real.log (R / R1)) := mul_pos hden1 hden2
      exact le_of_lt (one_div_pos.mpr hpos)
    have := add_nonneg h1 h2
    simpa [F] using this
                                       
  have hY_nonneg : 0 ≤ Real.log (|t| + 2) := by
                            
    have hgt1 : (1 : ℝ) < |t| + 2 := by
      have : (2 : ℝ) ≤ |t| + 2 := by
        have : 0 ≤ |t| := abs_nonneg t
        simp
      exact lt_of_lt_of_le (by norm_num) this
    exact le_of_lt (Real.log_pos hgt1)
  have hfinal1 :
      ‖Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
            (fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (s - rho1))
          - logDerivZeta s‖
      ≤ F * (K * Real.log (|t| + 2)) :=
    le_trans hLHS_le (by exact mul_le_mul_of_nonneg_left hlog_bound_final hF_nonneg)
  have hFactor_leC : F * K ≤ C := by exact le_trans (le_of_eq rfl) (le_max_left _ _)
  have hfinal2 : F * (K * Real.log (|t| + 2)) ≤ C * Real.log (|t| + 2) := by
    have := mul_le_mul_of_nonneg_right hFactor_leC hY_nonneg
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have := le_trans hfinal1 hfinal2
  simpa [s]

lemma lem_explicit1RealReal :
  ∃ C > 1,
      ∀ t : ℝ, 2 < |t| →
        ∀ δ : ℝ, 0 < δ ∧ δ < 1 →
          abs ((logDerivZeta ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I)).re
            - (Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
                (fun rho1 : ℂ =>
                  (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
                    (((1 : ℂ) + δ + t * Complex.I) - rho1)).re)))
          ≤ C * Real.log (|t| + 2) := by
  rcases lem_explicit1deltat with ⟨C, hCpos, hE⟩
  refine ⟨C, hCpos, ?_⟩
  intro t ht δ hδ
                  
  let s : ℂ := (1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I
  let S : Finset ℂ := Set.Finite.toFinset (ZetaZerosNearPoint_finite t)
  let g : ℂ → ℂ := fun rho1 : ℂ =>
    ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (s - rho1)
                                           
  have ht' : ‖logDerivZeta s - ∑ rho1 ∈ S, g rho1‖
      ≤ C * Real.log (abs t + 2) := by
                                                 
    have h_app := hE t ht δ hδ
    rw [norm_sub_rev] at h_app
    exact h_app
                                
  have hleft_eq :
      abs ((logDerivZeta s).re - ∑ rho1 ∈ S, (g rho1).re)
        = abs ((logDerivZeta s - ∑ rho1 ∈ S, g rho1).re) := by
    simp [Complex.sub_re, Complex.re_sum]
                 
  have hbound :
      abs ((logDerivZeta s - ∑ rho1 ∈ S, g rho1).re)
        ≤ ‖logDerivZeta s - ∑ rho1 ∈ S, g rho1‖ := by
    simpa using Complex.abs_re_le_norm (logDerivZeta s - ∑ rho1 ∈ S, g rho1)
            
  have hfinal :
      abs ((logDerivZeta s - ∑ rho1 ∈ S, g rho1).re)
        ≤ C * Real.log (abs t + 2) :=
    le_trans hbound ht'
                                                      
  have hnorm : |t| = abs t := rfl
  simpa [s, S, g, hleft_eq, hnorm] using hfinal

lemma lem_explicit2Real :
  ∃ C > 1,
      ∀ t : ℝ, 2 < |t| →
        ∀ δ : ℝ, 0 < δ ∧ δ < 1 →
          abs (
            (logDerivZeta ((1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I)).re
            - (Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t)))
                (fun rho1 : ℂ =>
                  (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
                    (((1 : ℂ) + δ + (2 * t) * Complex.I) - rho1)).re))
          )
          ≤ C * Real.log (abs (2 * t) + 2) := by
  rcases lem_explicit1RealReal with ⟨C, hCpos, hEv⟩
  refine ⟨C, hCpos, ?_⟩
  intro t ht δ hδ
                       
  have h_2t : 2 < |2 * t| := by
    rw [abs_mul, abs_two]
    linarith [ht]
  have h_bound := hEv (2 * t) h_2t δ hδ
                                 
  simp only [Complex.ofReal_mul] at h_bound
  exact h_bound

lemma lem_Realsum {α : Type*} (s : Finset α) (f : α → ℂ) : (Finset.sum s f).re = Finset.sum s (fun i => (f i).re) := by
  exact Complex.re_sum s f


lemma lem_sumrho1 (t : ℝ) (δ : ℝ) (_hdelta_pos : δ > 0) (_hdelta_lt1 : δ < 1) :
    (Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
        (fun rho1 : ℂ =>
                    ((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
                      (((1 : ℂ) + δ + t * Complex.I) - rho1))).re =
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
    (fun rho1 : ℂ =>
                    (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
                      (((1 : ℂ) + δ + t * Complex.I) - rho1)).re) := by
  exact lem_Realsum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t)) _

lemma lem_sumrho2 (t : ℝ) (delta : ℝ) (_hdelta : delta > 0) (_hdelta_lt1 : delta < 1) :
    (Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t)))
        (fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + (2 * t) * Complex.I) - rho1))).re =
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t)))
    (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + (2 * t) * Complex.I) - rho1)).re) := by
  rw [Complex.re_sum]

lemma lem_1deltatrho1 (delta : ℝ) (_hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (_h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :    ((1 : ℂ) + delta + t * Complex.I - rho1) = ((1 : ℝ) + delta - rho1.re) + (t - rho1.im) * Complex.I := by
                                                           
  conv_lhs => rw [← Complex.re_add_im rho1]

  simp only [sub_add_eq_sub_sub]
                                                      
  ring_nf
                                                               
  simp only [Complex.ofReal_one]
  ring

lemma lem_Re1deltatrho1 (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
((1 : ℂ) + delta + t * Complex.I - rho1).re = (1 : ℝ) + delta - rho1.re := by
                                                   
  rw [lem_1deltatrho1 delta hdelta t rho1 h_rho1_in_Zt]

  rw [Complex.add_re]
                                      
  rw [Complex.mul_I_re]
             
  simp

lemma lem_Re1delta1 (delta : ℝ) (_hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
(1 : ℝ) + delta - rho1.re ≥ delta := by
                                            
  have h_rho1_re_le_1 : rho1.re ≤ 1 := lem_sigmale1Zt t rho1 h_rho1_in_Zt
                               
  have h_nonneg : 1 - rho1.re ≥ 0 := by linarith
                                                                              
  linarith

lemma lem_Re1deltatge (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :    ((1 : ℂ) + delta + t * Complex.I - rho1).re ≥ delta := by
                                                     
  rw [lem_Re1deltatrho1 delta hdelta t rho1 h_rho1_in_Zt]
                                                      
  exact lem_Re1delta1 delta hdelta t rho1 h_rho1_in_Zt

lemma lem_Re1deltatneq0 (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
((1 : ℂ) + delta + t * Complex.I - rho1).re > 0 := by
                                                               
  have h_ge_delta : ((1 : ℂ) + delta + t * Complex.I - rho1).re ≥ delta := lem_Re1deltatge delta hdelta t rho1 h_rho1_in_Zt
                                                                         
  linarith [hdelta]

lemma lem_Re1deltatge0 (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
(1 / ((1 : ℂ) + delta + t * Complex.I - rho1)).re ≥ 0 := by
                                                                      
  apply le_of_lt
  apply lem_Re1zge0
                                                          
  exact lem_Re1deltatneq0 delta hdelta t rho1 h_rho1_in_Zt

lemma lem_Re1deltatge0m (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (_hdelta_lt_1 : delta < 1)
  (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
  (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
    (((1 : ℂ) + delta + t * Complex.I) - rho1)).re ≥ 0 := by
                                                     
  let n := (analyticOrderAt riemannZeta rho1).toNat
  let z := ((1 : ℂ) + delta + t * Complex.I) - rho1

  have h_eq : (n : ℂ) / z = n • (1/z) := by
    rw [nsmul_eq_mul]
    simp [div_eq_mul_inv]

  rw [h_eq, Complex.re_nsmul]

  apply nsmul_nonneg
  exact lem_Re1deltatge0 delta hdelta t rho1 h_rho1_in_Zt

lemma lem_Re1delta2tge0 (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint (2 * t)) :
(((analyticOrderAt riemannZeta rho1).toNat : ℂ) / ((1 : ℂ) + delta + (2 * t) * Complex.I - rho1)).re ≥ 0 := by
                                                      
  convert (preTransparency := .instances) lem_Re1deltatge0m delta hdelta (2 * t) hdelta_lt_1 rho1 h_rho1_in_Zt
  simp

lemma lem_sumrho2ge (t : ℝ) (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) :
Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t))) (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / ((1 : ℂ) + delta + (2 * t) * Complex.I - rho1)).re) ≥ 0 := by
  apply Finset.sum_nonneg
  intro rho1 h_rho1_in_finset
                                                                   
  have h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint (2 * t) := by
    rwa [Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite (2 * t))] at h_rho1_in_finset
                            
  exact lem_Re1delta2tge0 delta hdelta hdelta_lt_1 t rho1 h_rho1_in_Zt

lemma lem_sumrho2ge02 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) :
    (Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t)))
(fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + (2 * t) * Complex.I) - rho1))).re ≥ 0 := by
                                                                                   
  rw [lem_sumrho2 t delta hdelta hdelta_lt_1]
                                                             
  exact lem_sumrho2ge t delta hdelta hdelta_lt_1

lemma lem_explicit2Real2 :
  ∃ C > 1,
      ∀ t : ℝ, 2 < |t| →
        ∀ δ : ℝ, 0 < δ ∧ δ < 1 →
          ((-logDerivZeta ((1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I)).re)
          ≤ C * Real.log (abs (2 * t) + 2) := by
  rcases lem_explicit2Real with ⟨C, hCpos, hEv⟩
  refine ⟨C, hCpos, ?_⟩
  intro t ht δ hδ
                  
  set s : ℂ := (1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I
  set S : Finset ℂ := Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t))
  set Sre : ℝ :=
    Finset.sum S
      (fun rho1 : ℂ =>
        (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
          (s - rho1)).re)
                                                                  
  have h_bound :
      abs ((logDerivZeta s).re - Sre)
        ≤ C * Real.log (abs (2 * t) + 2) := by
    simpa [s, S, Sre] using hEv t ht δ hδ
                                                                     
  have hS_nonneg : 0 ≤ Sre := by
                                                                       
    have h0 := lem_sumrho2ge02 t δ hδ.1 hδ.2

    simpa [s, S, Sre, lem_sumrho2 t δ hδ.1 hδ.2] using h0
                                             
  have h_left : -(C * Real.log (abs (2 * t) + 2)) ≤ (logDerivZeta s).re - Sre :=
    (abs_le.mp h_bound).1
                                        
  have h_neg : -((logDerivZeta s).re - Sre) ≤ C * Real.log (abs (2 * t) + 2) := by
    simpa using neg_le_neg h_left
                                                                  
  have h_aux := sub_le_sub_right h_neg Sre
  have h_isol : - (logDerivZeta s).re ≤ C * Real.log (abs (2 * t) + 2) - Sre := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_aux
                                               
  have h_drop : C * Real.log (abs (2 * t) + 2) - Sre ≤ C * Real.log (abs (2 * t) + 2) :=
    sub_le_self _ hS_nonneg
             
  have h_final := le_trans h_isol h_drop
                                                            
  simpa [s, Complex.neg_re] using h_final




lemma lem_Z2bound :
  ∃ C > 1,
     ∀ t : ℝ, 2 < |t| →
      ∀ δ, 0 < δ ∧ δ < 1 →
        (-(logDerivZeta ((1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I))).re
          ≤ C * Real.log (abs t + 2) := by
                                                     
  obtain ⟨C₁, hC₁_pos, hbound₁⟩ := lem_explicit2Real2

  have h_log_comp :
      ∀ t : ℝ, 2 < |t| → Real.log (abs (2 * t) + 2) ≤ 2 * Real.log (abs t + 2) := by
    intro t ht
    have h_pos_2t : 0 < abs (2 * t) + 2 := by linarith [abs_nonneg (2 * t)]
    have h_pos_t : 0 < abs t + 2 := by linarith [abs_nonneg t]
    have h_2t_eq : abs (2 * t) = 2 * abs t := by
      rw [abs_mul, abs_two]

    have h_bound : abs (2 * t) + 2 ≤ 4 * (abs t + 2) := by
      rw [h_2t_eq]
                                         
      linarith [abs_nonneg t]

    have h_4_pos : (0 : ℝ) < 4 := by norm_num
    have h_log_bound : Real.log (abs (2 * t) + 2) ≤ Real.log (4 * (abs t + 2)) :=
      Real.log_le_log h_pos_2t h_bound

    have h_log_mul_eq : Real.log (4 * (abs t + 2)) = Real.log 4 + Real.log (abs t + 2) := by
      exact Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt h_pos_t)

    have h_4_le : (4 : ℝ) ≤ abs t + 2 := by linarith [ht]
    have h_log_4 : Real.log 4 ≤ Real.log (abs t + 2) :=
      Real.log_le_log (by norm_num) h_4_le

    calc Real.log (abs (2 * t) + 2)
      ≤ Real.log (4 * (abs t + 2)) := h_log_bound
      _ = Real.log 4 + Real.log (abs t + 2) := h_log_mul_eq
      _ ≤ Real.log (abs t + 2) + Real.log (abs t + 2) := add_le_add_left h_log_4 _
      _ = 2 * Real.log (abs t + 2) := by ring

  have hC₁_nonneg : 0 ≤ C₁ := le_of_lt (lt_trans zero_lt_one hC₁_pos)

  refine ⟨2 * C₁, ?_, ?_⟩
  ·                   
    linarith [hC₁_pos]
  ·              
    intro t ht δ hδ
    let s := (1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I

    have h1 : (-(logDerivZeta s)).re ≤ C₁ * Real.log (abs (2 * t) + 2) := hbound₁ t ht δ hδ

    have h3 : Real.log (abs (2 * t) + 2) ≤ 2 * Real.log (abs t + 2) := h_log_comp t ht

    calc (-(logDerivZeta s)).re
      ≤ C₁ * Real.log (abs (2 * t) + 2) := h1
      _ ≤ C₁ * (2 * Real.log (abs t + 2)) := mul_le_mul_of_nonneg_left h3 hC₁_nonneg
      _ = (2 * C₁) * Real.log (abs t + 2) := by ring

lemma lem_Z1split (delta : ℝ) (_hdelta : delta > 0) (_hdelta_lt1 : delta < 1) (rho : ℂ)
  (_h_rho_in_zeroZ : rho ∈ zeroZ)
  (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint rho.im) :
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im))
      (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) =
    (((analyticOrderAt riemannZeta rho).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re +
    Finset.sum ((Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)).erase rho)
      (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) := by
  classical
  set s := Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)
  set f := fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re
  have hmem : rho ∈ s := by
    simpa [s, Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite rho.im)] using h_rho_in_Zt
                                                            
  have h_decomp : ∑ x ∈ s, f x = f rho + ∑ x ∈ s.erase rho, f x := by
    rw [← Finset.insert_erase hmem]
    rw [Finset.sum_insert (Finset.notMem_erase rho s)]
    simp
  exact h_decomp



lemma re_ofReal_div_ge_one (a : ℝ) (z : ℂ) (ha : 1 ≤ a) (hz : 0 ≤ (1 / z).re) : ((a : ℂ) / z).re ≥ (1 / z).re := by
  have hrepr : ((a : ℂ) / z).re = a * (1 / z).re := by
    simp [div_eq_mul_inv, Complex.mul_re]
  have hmul : (1 : ℝ) * (1 / z).re ≤ a * (1 / z).re :=
    mul_le_mul_of_nonneg_right ha hz
  calc
    ((a : ℂ) / z).re = a * (1 / z).re := hrepr
    _ ≥ 1 * (1 / z).re := by exact hmul
    _ = (1 / z).re := by simp [one_mul]

lemma analyticAt_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
                                                                  
  refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
                                                                                          
  filter_upwards [eventually_ne_nhds hs] with z hz
  exact differentiableAt_riemannZeta hz

lemma riemannZeta_not_eventually_zero_of_ne_one {s : ℂ} (hs : s ≠ 1) :
  ¬ (∀ᶠ z in nhds s, riemannZeta z = 0) := by
  intro hEvZero
                                                                                            
  let H : ℂ → ℂ := Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1
                                                    
  have hH_diff : Differentiable ℂ H := by
    intro z
    rcases eq_or_ne z 1 with rfl | hz
    ·                                   
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      ·                                                 
                                                                 
        filter_upwards [self_mem_nhdsWithin] with t ht
        have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) t := (differentiableAt_id.sub_const 1)
        have h2 : DifferentiableAt ℂ riemannZeta t := by
                                               
          exact differentiableAt_riemannZeta ht
        have hdiff := h1.mul h2
                                                           
        apply hdiff.congr_of_eventuallyEq
        filter_upwards [eventually_ne_nhds ht] with u hu
        simp [H, Function.update_of_ne hu]
      ·                                        
        simpa [H, continuousAt_update_same] using riemannZeta_residue_one
    ·                                     
      have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) z := (differentiableAt_id.sub_const 1)
      have h2 : DifferentiableAt ℂ riemannZeta z := by
        exact differentiableAt_riemannZeta hz
      have hdiff := h1.mul h2
                                                      
      apply hdiff.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz] with u hu
      simp [H, Function.update_of_ne hu]
                                                                            
  have hH_analytic : AnalyticOnNhd ℂ H Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable).2 hH_diff
                                             
  have h0_analytic : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ := by
    intro z _; simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z)
                                                                                         
  have hEv_ne1 : ∀ᶠ z in nhds s, z ≠ 1 := eventually_ne_nhds hs
  have hEv_H0 : ∀ᶠ z in nhds s, H z = 0 := by
    filter_upwards [hEvZero, hEv_ne1] with z hz_zero hz_ne1
                                        
    have : H z = (z - 1) * riemannZeta z := by simp [H, Function.update_of_ne hz_ne1]
    simp [this, hz_zero]
                                                                              
  have hEqOn : Set.EqOn H (fun _ : ℂ => (0 : ℂ)) Set.univ := by
                           
    have hU : IsPreconnected (Set.univ : Set ℂ) := by simpa using isPreconnected_univ
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hH_analytic h0_analytic hU (by simp) hEv_H0
  have hHeq : H = fun _ : ℂ => (0 : ℂ) := by
    funext z; simpa using hEqOn (by simp : z ∈ (Set.univ : Set ℂ))
                                         
  have h2ne1 : (2 : ℂ) ≠ 1 := by norm_num
  have hH2 : H (2 : ℂ) = (2 - 1) * riemannZeta (2 : ℂ) := by
    simp [H]
  have hzeta2_ne : riemannZeta (2 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp)
  have hprod_zero' : 0 = (2 - 1) * riemannZeta (2 : ℂ) := by
    simpa [hHeq] using hH2
  have hprod_zero : (2 - 1) * riemannZeta (2 : ℂ) = 0 := hprod_zero'.symm
  have hnonzero : (2 - 1) * riemannZeta (2 : ℂ) ≠ 0 := by
    have hcoeff : (2 : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr h2ne1
    exact mul_ne_zero hcoeff hzeta2_ne
  exact hnonzero hprod_zero

lemma analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero {f : ℂ → ℂ} {z0 : ℂ}
  (hf : AnalyticAt ℂ f z0) (hzero : f z0 = 0)
  (hnot : ¬ (∀ᶠ z in nhds z0, f z = 0)) :
  1 ≤ (analyticOrderAt f z0).toNat := by
  classical
                                                 
  have hne0 : analyticOrderAt f z0 ≠ 0 := by
    intro h0
    have hzne : f z0 ≠ 0 := (AnalyticAt.analyticOrderAt_eq_zero hf).1 h0
    exact hzne hzero
                                                                         
  have hneTop : analyticOrderAt f z0 ≠ ⊤ := by
    intro htop
    have hall : (∀ᶠ z in nhds z0, f z = 0) := (analyticOrderAt_eq_top).1 htop
    exact hnot hall
                                          
  rcases WithTop.ne_top_iff_exists.mp hneTop with ⟨n, hn⟩
                             
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    apply hne0
                                            
    simp [hn.symm, hn0]
    rfl
                    
  have hposn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn_ne_zero)
                                         
  simpa [hn.symm] using! hposn

lemma lem_Z1splitge (delta : ℝ) (hdelta_pos : delta > 0) (hdelta : delta < 1) (rho : ℂ)
  (h_rho_in_zeroZ : rho ∈ zeroZ) (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint rho.im) :
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)) (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) ≥
(1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re := by
  classical
                           
  have hsplit :=
    lem_Z1split delta hdelta_pos hdelta rho h_rho_in_zeroZ h_rho_in_Zt
                                    
  rw [hsplit]
                                       
  have h_rho_ne_one : rho ≠ (1 : ℂ) := by
    intro h
    have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
    exact hz1_ne (by simpa [h] using! h_rho_in_zeroZ)
  have hAnal : AnalyticAt ℂ riemannZeta rho := analyticAt_riemannZeta_of_ne_one h_rho_ne_one
  have hNotEv : ¬ (∀ᶠ z in nhds rho, riemannZeta z = 0) :=
    riemannZeta_not_eventually_zero_of_ne_one h_rho_ne_one
  have horder_nat : 1 ≤ (analyticOrderAt riemannZeta rho).toNat :=
    analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero
      hAnal (by simpa using! h_rho_in_zeroZ) hNotEv
  have ha_real : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta rho).toNat : ℝ) := by exact_mod_cast horder_nat
  have hz_nonneg : 0 ≤ (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re :=
    lem_Re1deltatge0 delta hdelta_pos rho.im rho h_rho_in_Zt
  have hfirst :
      (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re
        ≤ (((((analyticOrderAt riemannZeta rho).toNat : ℝ) : ℂ) /
            (((1 : ℂ) + delta + rho.im * Complex.I) - rho))).re := by
                               
    simpa [ge_iff_le] using
      (re_ofReal_div_ge_one ((analyticOrderAt riemannZeta rho).toNat : ℝ)
        ((((1 : ℂ) + delta + rho.im * Complex.I) - rho)) ha_real hz_nonneg)
                                        
  have hsum_nonneg :
      0 ≤ Finset.sum
        ((Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)).erase rho)
        (fun rho1 : ℂ =>
          (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
            (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) := by
    apply Finset.sum_nonneg
    intro rho1 hmem
    rcases Finset.mem_erase.mp hmem with ⟨_, hmemS⟩
                                     
    have hZt : rho1 ∈ ZetaZerosNearPoint rho.im := by
      simpa [Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite rho.im)] using hmemS
                    
    have hne1 : rho1 ≠ (1 : ℂ) := by
      intro h
      have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
      have hzero1 : riemannZeta rho1 = 0 := hZt.1
      exact hz1_ne (by simpa [h] using hzero1)
                           
    have hAnal1 : AnalyticAt ℂ riemannZeta rho1 := analyticAt_riemannZeta_of_ne_one hne1
    have hNotEv1 : ¬ (∀ᶠ z in nhds rho1, riemannZeta z = 0) :=
      riemannZeta_not_eventually_zero_of_ne_one hne1
    have hzero1 : riemannZeta rho1 = 0 := hZt.1
    have horder1 : 1 ≤ (analyticOrderAt riemannZeta rho1).toNat :=
      analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero hAnal1 hzero1 hNotEv1
    have ha1_real : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta rho1).toNat : ℝ) := by exact_mod_cast horder1
                       
    have hz1_nonneg : 0 ≤ (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re :=
      lem_Re1deltatge0 delta hdelta_pos rho.im rho1 hZt
                                           
    have hge :
        (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re ≤
          (((((analyticOrderAt riemannZeta rho1).toNat : ℝ) : ℂ) /
            (((1 : ℂ) + delta + rho.im * Complex.I) - rho1))).re := by
      simpa [ge_iff_le] using
        (re_ofReal_div_ge_one ((analyticOrderAt riemannZeta rho1).toNat : ℝ)
          ((((1 : ℂ) + delta + rho.im * Complex.I) - rho1)) ha1_real hz1_nonneg)
                                                       
    exact le_trans hz1_nonneg hge
                           
  have h := add_le_add hfirst hsum_nonneg
                             
  simpa using h

lemma lem_1deltatrho0 (delta : ℝ) (_hdelta : delta > 0) (rho : ℂ) (_h_rho_in_zeroZ : rho ∈ zeroZ) :
((1 : ℂ) + delta + rho.im * Complex.I - rho) = ((1 : ℝ) + delta - rho.re) := by

  calc (1 : ℂ) + delta + rho.im * Complex.I - rho
    = (1 : ℂ) + delta + rho.im * Complex.I - (rho.re + rho.im * Complex.I) := by rw [Complex.re_add_im]
  _ = (1 : ℂ) + delta - rho.re := by ring
  _ = ((1 : ℝ) + delta - rho.re : ℂ) := by norm_cast





lemma lem_1delsigReal2 (delta : ℝ) (_hdelta : delta > 0) (rho : ℂ) (_h_rho_in_zeroZ : rho ∈ zeroZ) :
(1 / ((1 : ℂ) + delta - rho.re)).re = 1 / ((1 : ℝ) + delta - rho.re) := by
                                                                           
  have h_eq : (1 : ℂ) + delta - rho.re = (1 + delta - rho.re : ℝ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one]

  rw [h_eq]

  rw [Complex.div_ofReal_re]

  rw [Complex.one_re]

lemma lem_re_inv_one_plus_delta_minus_rho_real (delta : ℝ) (hdelta : delta > 0)  (rho : ℂ) (h_rho_in_zeroZ : rho ∈ zeroZ) :
(1 / ((1 : ℂ) + delta + rho.im * Complex.I - rho)).re = 1 / ((1 : ℝ) + delta - rho.re) := by
                                                      
  rw [lem_1deltatrho0 delta hdelta rho h_rho_in_zeroZ]
                               
  exact lem_1delsigReal2 delta hdelta rho h_rho_in_zeroZ

lemma lem_Z1splitge2 (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) (rho : ℂ)
  (h_rho_in_zeroZ : rho ∈ zeroZ) (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint rho.im) :
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im))
      (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / ((1 : ℂ) + delta + rho.im * Complex.I - rho1)).re) ≥
1 / ((1 : ℝ) + delta - rho.re) := by
                                                    
  have h1 := lem_Z1splitge delta hdelta hdelta_lt_1 rho h_rho_in_zeroZ h_rho_in_Zt
                                                                                  
  have h2 := lem_re_inv_one_plus_delta_minus_rho_real delta hdelta rho h_rho_in_zeroZ
                        
  rw [← h2]
  exact h1

lemma lem_Z1splitge3 (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) (sigma t : ℝ) (rho : ℂ)
  (h_rho_eq : rho = sigma + t * Complex.I) (h_rho_in_zeroZ : rho ∈ zeroZ)
  (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint t) :
(Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t)) (fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + t * Complex.I) - rho1)) ).re ≥ 1 / ((1 : ℝ) + delta - sigma) := by
                                                                                   
  rw [lem_sumrho1 t delta hdelta hdelta_lt_1]

  have h_rho_im : rho.im = t := by
    rw [h_rho_eq]
    simp [Complex.add_im, Complex.mul_im, Complex.I_im]
  have h_rho_re : rho.re = sigma := by
    rw [h_rho_eq]
    simp [Complex.add_re, Complex.mul_re, Complex.I_re]

  have h_rho_in_Zt' : rho ∈ ZetaZerosNearPoint rho.im := by
    rw [h_rho_im]
    exact h_rho_in_Zt

  have h_bound := lem_Z1splitge2 delta hdelta hdelta_lt_1 rho h_rho_in_zeroZ h_rho_in_Zt'

  convert (preTransparency := .instances) h_bound using 1
                                                       
  simp_rw [← h_rho_im]
                                                             
  rw [h_rho_re]


lemma Z1bound :
  ∃ C > 1,
    ∀ (delta : ℝ), (0 < delta ∧ delta < 1) →
      ∀ t : ℝ, 2 < |t| →
        ∀ s : ℂ, s ∈ zeroZ ∧ s.im = t →
          (-(logDerivZeta ((1 : ℂ) + delta + t * Complex.I))).re
            ≤ - (1 / (1 + delta - s.re)) + C * Real.log (abs t + 2) := by
  classical
                                            
  obtain ⟨C0, hC0gt1, hExp⟩ := lem_explicit1RealReal
                                                                                  
  have hlog5pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  let C : ℝ := max (C0 + 3 / Real.log 4) 2
  have hCgt1 : 1 < C := by
    have : (1 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le this (le_max_right _ _)
  refine ⟨C, hCgt1, ?_⟩
  intro delta hdelta t ht s hs
                  
  set sp : ℂ := (1 : ℂ) + delta + t * Complex.I
  set S : Finset ℂ := Set.Finite.toFinset (ZetaZerosNearPoint_finite t)
  set Sre : ℝ :=
    Finset.sum S
      (fun rho1 : ℂ =>
        (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (sp - rho1)).re)
                                                                        
  have h_bound : abs ((logDerivZeta sp).re - Sre)
        ≤ C0 * Real.log (abs t + 2) := by
    simpa [sp, S, Sre] using hExp t ht delta hdelta
                                                                         
  have h_left : -(C0 * Real.log (abs t + 2)) ≤ (logDerivZeta sp).re - Sre :=
    (abs_le.mp h_bound).1
  have h_neg : -((logDerivZeta sp).re - Sre) ≤ C0 * Real.log (abs t + 2) := by
    simpa using neg_le_neg h_left
  have h_isol : - (logDerivZeta sp).re ≤ C0 * Real.log (abs t + 2) - Sre := by
    have := sub_le_sub_right h_neg Sre
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
                                              
  have hS_nonneg : 0 ≤ Sre := by
    apply Finset.sum_nonneg
    intro rho1 hmem
    have hZt : rho1 ∈ ZetaZerosNearPoint t := by
      simpa [S, Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite t)] using hmem
                                   
    simpa [sp] using
      (lem_Re1deltatge0m delta hdelta.1 t hdelta.2 rho1 hZt)
                                 
  have h_basic : (-(logDerivZeta sp)).re ≤ C0 * Real.log (abs t + 2) := by
    have h_drop : C0 * Real.log (abs t + 2) - Sre ≤ C0 * Real.log (abs t + 2) :=
      sub_le_self _ hS_nonneg
    exact le_trans h_isol h_drop
                                              
  by_cases hmem : s ∈ ZetaZerosNearPoint t
  ·                                                               
    set sigma : ℝ := s.re
    have h_rho_eq : s = (sigma : ℂ) + t * Complex.I := by
      have : s = s.re + s.im * Complex.I := by simp [Complex.re_add_im]
      simpa [sigma, hs.2] using this
                                              
    have hsum_rew := lem_sumrho1 t delta hdelta.1 hdelta.2
    have h_sum_ge' :=
      lem_Z1splitge3 delta hdelta.1 hdelta.2 sigma t s h_rho_eq hs.1 hmem
    have h_sum_ge : Sre ≥ 1 / ((1 : ℝ) + delta - sigma) := by
      simpa [sp, S, Sre, hsum_rew] using h_sum_ge'
                                                                                  
    have h1 : (-(logDerivZeta sp)).re ≤ C0 * Real.log (abs t + 2) - (1 / ((1 : ℝ) + delta - sigma)) := by
      have : (1 / ((1 : ℝ) + delta - sigma)) ≤ Sre := h_sum_ge
      have := sub_le_sub_left this (C0 * Real.log (abs t + 2))
      exact le_trans h_isol (by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this)
                                              
    have hCge : C0 ≤ C :=
      le_trans (by
        have : 0 ≤ 3 / Real.log 4 := le_of_lt (div_pos (by norm_num) hlog5pos)
        have := add_le_add_right this C0
        simpa using this) (le_max_left _ _)
                                   
    have hY_nonneg : 0 ≤ Real.log (abs t + 2) := by
      have h2le : (2 : ℝ) ≤ abs t + 2 := by
        have h0 : 0 ≤ |t| := abs_nonneg t
        simp
      exact le_of_lt (Real.log_pos (lt_of_lt_of_le (by norm_num) h2le))
    have h_enlarge : C0 * Real.log (abs t + 2) ≤ C * Real.log (abs t + 2) :=
      mul_le_mul_of_nonneg_right hCge hY_nonneg
    have h2 : C0 * Real.log (abs t + 2) - (1 / ((1 : ℝ) + delta - sigma)) ≤
              C * Real.log (abs t + 2) - (1 / ((1 : ℝ) + delta - sigma)) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (sub_le_sub_right h_enlarge (1 / ((1 : ℝ) + delta - sigma)))
    have := le_trans h1 h2
    simpa [sp, sigma, Complex.neg_re, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using this
  ·                                                                                           
                                                                             
    have h_notle : ¬ ‖s - ((3/2 : ℂ) + t * Complex.I)‖ ≤ (5/6 : ℝ) := by
      intro hle
      exact hmem ⟨hs.1, hle⟩
    have hdist_gt : (5/6 : ℝ) < ‖s - ((3/2 : ℂ) + t * Complex.I)‖ := not_le.mp h_notle
                                                                                            
    have h_re : (s - ((3/2 : ℂ) + t * Complex.I)).re = s.re - (3/2 : ℝ) := by
      simp [Complex.sub_re, Complex.add_re]
    have h_im : (s - ((3/2 : ℂ) + t * Complex.I)).im = 0 := by
      have : (s - ((3/2 : ℂ) + t * Complex.I)).im = s.im - t := by
        simp [Complex.sub_im, Complex.add_im]
      simp [hs.2]
    have h_eq : s - ((3/2 : ℂ) + t * Complex.I) = (((s.re - (3/2 : ℝ)) : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [h_re]
      · simp [h_im]
    have hdist_real : ‖s - ((3/2 : ℂ) + t * Complex.I)‖ = |s.re - (3/2 : ℝ)| := by
      simpa [h_eq] using complex_abs_of_real (s.re - (3/2 : ℝ))
    have habs_gt : (5/6 : ℝ) < |s.re - (3/2 : ℝ)| := by simpa [hdist_real] using hdist_gt
                                 
    have h0 : riemannZeta (s.re + s.im * Complex.I) = 0 := by
      simpa [Complex.re_add_im] using! hs.1
    have hs_le1 : s.re ≤ 1 := lem_sigmale1 s.re s.im h0
                                                        
    have h_nonpos : s.re - (3/2 : ℝ) ≤ 0 := by linarith [hs_le1]
    have h_abs_eq : |s.re - (3/2 : ℝ)| = (3/2 : ℝ) - s.re := by
      have : |s.re - (3/2 : ℝ)| = -(s.re - (3/2 : ℝ)) := abs_of_nonpos h_nonpos
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have h_gt' : (5/6 : ℝ) < (3/2 : ℝ) - s.re := by simpa [h_abs_eq] using habs_gt
    have hs_le_23 : s.re ≤ (2/3 : ℝ) := by linarith [h_gt']
                                                                    
    have hden_ge : (1/3 : ℝ) ≤ 1 + delta - s.re := by
      have : (1/3 : ℝ) ≤ 1 - s.re := by linarith [hs_le_23]
      have : 1 - s.re ≤ 1 + delta - s.re := by linarith [hdelta.1]
      exact le_trans ‹(1/3 : ℝ) ≤ 1 - s.re› this
    have hone_div_le3 : 1 / (1 + delta - s.re) ≤ (3 : ℝ) := by
      have : 1 / (1 + delta - s.re) ≤ 1 / (1/3 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/3) hden_ge
      simpa [one_div] using this
    have hneg_ge : - (3 : ℝ) ≤ - (1 / (1 + delta - s.re)) := by
      simpa using (neg_le_neg hone_div_le3)
                                            
    have hlog_ge : Real.log 4 ≤ Real.log (abs t + 2) := by
      have : (4 : ℝ) < abs t + 2 := by linarith [ht]
      exact Real.log_le_log (by norm_num) (le_of_lt this)
    have hC_ge_add : C ≥ C0 + 3 / Real.log 4 := by exact le_max_left _ _
    have hCminus : C - C0 ≥ 3 / Real.log 4 := by linarith
    have hY_nonneg : 0 ≤ Real.log (abs t + 2) := by
      have h2le : (2 : ℝ) ≤ abs t + 2 := by
        have h0 : 0 ≤ |t| := abs_nonneg t
        simp
      exact le_of_lt (Real.log_pos (lt_of_lt_of_le (by norm_num) h2le))
    have hmul1 : (3 / Real.log 4) * Real.log 4 ≤ (3 / Real.log 4) * Real.log (abs t + 2) := by
      have hk_nonneg : 0 ≤ 3 / Real.log 4 := le_of_lt (div_pos (by norm_num) hlog5pos)
      exact mul_le_mul_of_nonneg_left hlog_ge hk_nonneg
    have hmul2 : (3 / Real.log 4) * Real.log (abs t + 2) ≤ (C - C0) * Real.log (abs t + 2) := by
      exact mul_le_mul_of_nonneg_right hCminus hY_nonneg
    have hmul_ge3 : (3 : ℝ) ≤ (C - C0) * Real.log (abs t + 2) := by
      have hne5 : Real.log 4 ≠ 0 := ne_of_gt hlog5pos
      have hcalc : (3 / Real.log 4) * Real.log 4 = 3 := by
        simp [div_eq_mul_inv, hne5]
      have : (3 / Real.log 4) * Real.log 4 ≤ (C - C0) * Real.log (abs t + 2) :=
        le_trans hmul1 hmul2
      simpa [hcalc] using this
                                 
    have hCmul' : C0 * Real.log (abs t + 2) + 3 ≤ C * Real.log (abs t + 2) := by
      have : C0 * Real.log (abs t + 2) + 3 ≤ C0 * Real.log (abs t + 2) + (C - C0) * Real.log (abs t + 2) := by
        exact add_le_add_right hmul_ge3 _
      have hcalc : C * Real.log (abs t + 2) =
          C0 * Real.log (abs t + 2) + (C - C0) * Real.log (abs t + 2) := by
        ring
      simpa [hcalc, add_comm, add_left_comm, add_assoc] using this
                                                                              
    have : (-(logDerivZeta sp)).re ≤ - (1 / (1 + delta - s.re)) + C * Real.log (abs t + 2) := by
      have h1 : (-(logDerivZeta sp)).re ≤ C0 * Real.log (abs t + 2) := h_basic
      have h2 : C0 * Real.log (abs t + 2) ≤ C * Real.log (abs t + 2) - 3 := by
        linarith [hCmul']
      have h3 : C * Real.log (abs t + 2) - 3 ≤ - (1 / (1 + delta - s.re)) + C * Real.log (abs t + 2) := by
        have := add_le_add_left hneg_ge (C * Real.log (abs t + 2))
        simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
      exact le_trans h1 (le_trans h2 h3)
    simpa [sp, Complex.neg_re, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this










lemma absorb_pos_constant_into_log {L A c : ℝ} (hL : 1 ≤ L) (hc : 0 ≤ c) : A * L + c ≤ (A + c) * L := by
                                             
  have hc_le : c ≤ L * c := by
    have h := mul_le_mul_of_nonneg_right hL hc
    simpa [one_mul] using h
                                        
  have h0 : A * L + c ≤ A * L + L * c := by
    exact add_le_add_right hc_le (A * L)
  calc
    A * L + c ≤ A * L + L * c := h0
    _ = A * L + c * L := by simp [mul_comm]
    _ = (A + c) * L := by simp [right_distrib]

lemma neg_logDeriv_zeta_eq_vonMangoldt_sum (s : ℂ) (hs : 1 < s.re) : -(deriv riemannZeta s / riemannZeta s) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s) := by
                                                                                     
  have h1 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

  have h2 : -deriv riemannZeta s / riemannZeta s = LSeries (fun n => ↑(ArithmeticFunction.vonMangoldt n)) s := h1.symm
                                                                                                                 
  have h3 : -(deriv riemannZeta s / riemannZeta s) = -deriv riemannZeta s / riemannZeta s := by ring
  rw [h3, h2]

  rw [LSeries]
  congr 1
  ext n
  rw [LSeries.term_def]
  split_ifs with h_zero
  ·                                
    simp [h_zero]
  ·                                                                     
    rw [div_eq_mul_inv, Complex.cpow_neg]

lemma zeta1zetaseries {s : ℂ} (hs : 1 < s.re) :
-logDerivZeta s = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s) := by
  unfold logDerivZeta
                                                                                                                       
  exact neg_logDeriv_zeta_eq_vonMangoldt_sum s hs

lemma zeta1zetaseriesxy (x y : ℝ) (hx : 1 < x) :
    -logDerivZeta (x + y * I) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I)) := by
  apply zeta1zetaseries

  have h : (x + y * I).re = x := by
    simp [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
    right
    exact Complex.I_re
  rw [h]
  exact hx

lemma Zconverges1 (x y : ℝ) (hx : 1 < x) : riemannZeta (x + y * I) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_lt_re

  have h : (x + y * I).re = x := by
    rw [Complex.add_re, Complex.ofReal_re]
    simp [Complex.mul_re]
    right
    exact Complex.I_re
  rw [h]
  exact hx

lemma complex_re_of_real_add_imag (x y : ℝ) : (x + y * I).re = x := by
  simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im]
                                                                           
  right
  exact Complex.I_re

lemma vonMangoldt_LSeriesSummable (s : ℂ) (hs : 1 < s.re) : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
                                                                            
  exact ArithmeticFunction.LSeriesSummable_vonMangoldt hs

lemma summable_of_support_singleton {α : Type*} [SeminormedAddCommGroup α] (f : ℕ → α) (n₀ : ℕ) (h : ∀ n : ℕ, n ≠ n₀ → f n = 0) : Summable f := by
                                                     
  have h_finite_support : Set.Finite (Function.support f) := by
                                       
    have h_subset : Function.support f ⊆ {n₀} := by
      intro n hn

      by_contra h_ne
                                                 
      have h_zero : f n = 0 := h n h_ne
                                     
      simp [Function.mem_support] at hn
      exact hn h_zero
                                                                 
    exact Set.Finite.subset (Set.finite_singleton n₀) h_subset

  exact summable_of_hasFiniteSupport h_finite_support

lemma summable_of_summable_add_sub {α : Type*} [SeminormedAddCommGroup α] (f g h : ℕ → α) (h_eq : f = g + h) (hf : Summable f) (hh : Summable h) : Summable g := by

  have g_eq_f_sub_h : g = f - h := by
                                           
    rw [← sub_eq_iff_eq_add] at h_eq
    exact h_eq.symm

  rw [g_eq_f_sub_h]

  exact hf.sub hh

lemma LSeriesSummable_to_summable (f : ℕ → ℂ) (s : ℂ) (h : LSeriesSummable f s) : Summable (fun n => f n * (n : ℂ) ^ (-s)) := by
                                                          
  have h_term_summable : Summable (LSeries.term f s) := h

  have h_eq_nonzero : ∀ n : ℕ, n ≠ 0 → LSeries.term f s n = f n * (n : ℂ) ^ (-s) := by
    intro n hn
    rw [LSeries.term_of_ne_zero hn]
    rw [div_eq_mul_inv, Complex.cpow_neg]

  let diff := fun n => LSeries.term f s n - f n * (n : ℂ) ^ (-s)

  have h_diff_support : ∀ n : ℕ, n ≠ 0 → diff n = 0 := by
    intro n hn
    simp only [diff]
    rw [h_eq_nonzero n hn]
    simp

  have h_diff_summable : Summable diff := by
                                              
    apply summable_of_support_singleton diff 0 h_diff_support

  have h_rw : LSeries.term f s = (fun n => f n * (n : ℂ) ^ (-s)) + diff := by
    ext n
    simp only [diff, Pi.add_apply]
    ring

  exact summable_of_summable_add_sub (LSeries.term f s) (fun n => f n * (n : ℂ) ^ (-s)) diff h_rw h_term_summable h_diff_summable

lemma ReZconverges1 (x y : ℝ) (hx : 1 < x) :
Summable (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) := by
                                                                                                
  have h_nonzero : riemannZeta (x + y * I) ≠ 0 := Zconverges1 x y hx

  have h_re_gt_one : 1 < (x + y * I).re := by
    rw [complex_re_of_real_add_imag]
    exact hx

  have h_L_summable : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) :=
    vonMangoldt_LSeriesSummable (x + y * I) h_re_gt_one

  have h_summable : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) :=
    LSeriesSummable_to_summable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) h_L_summable

  have h_hasSum : HasSum (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) :=
    h_summable.hasSum

  have h_hasSum_re : HasSum (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))).re) (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))).re :=
    Complex.hasSum_re h_hasSum

  exact h_hasSum_re.summable


lemma lem_nxy (n : ℕ) (hn : n ≥ 1) (x y : ℝ) :
    Complex.cpow (n : ℂ) (-(x + y * I)) = Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I)) := by
                                              
  have h : -(x + y * I) = (-x : ℂ) + (-(y * I)) := by ring
  rw [h]
                                                         
  exact lem_exprule n hn (-x : ℂ) (-(y * I))

lemma lem_zeta1zetaseriesxy2 (x y : ℝ) (hx : 1 < x) :
    -logDerivZeta (x + y * I) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (Complex.cpow (n : ℂ) ((-x) : ℂ)) * (Complex.cpow (n : ℂ) (-(y * I))) := by
                            
  rw [zeta1zetaseriesxy x y hx]
                                             
  congr 1
  ext n
                      
  rw [← Complex.cpow_eq_pow]
                                                          
  by_cases h : n = 0
  ·                                
    simp [h]
  ·                                 
    have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [lem_nxy n hn x y]
                                                          
    ring

lemma complex_add_re_ofReal_mul_I (x y : ℝ) : (x + y * I).re = x := by
  rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
                                  
  have h : I.re = 0 := Complex.I_re
  rw [h]
  simp

lemma LSeriesSummable_to_explicit_summable (x y : ℝ) (_hx : 1 < x) : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) → Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))) := by
  intro h_summable

  have h_vm_zero : (ArithmeticFunction.vonMangoldt 0 : ℂ) = 0 := by
    simp

  have h_eq : ∀ n : ℕ, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) n =
    (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I)) := by
    intro n
                                                     
    rw [LSeries.term_def₀ h_vm_zero]

    rw [← Complex.cpow_eq_pow]

    by_cases hn : n = 0
    ·                                
      simp [hn]
    ·                                    
      have hn_ge : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
      rw [lem_nxy n hn_ge x y]
      ring

  have h_term_summable : Summable (fun n => LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) n) := by
    exact h_summable

  convert (preTransparency := .instances) h_term_summable using 1
  ext n
  exact (h_eq n).symm

lemma Zseriesconverges1 (x y : ℝ) (hx : 1 < x) :
Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))) := by
                                                        
  have h_zeta_ne_zero := Zconverges1 x y hx

  have h_series := lem_zeta1zetaseriesxy2 x y hx

  have h_re : 1 < (x + y * I).re := by
    rw [complex_add_re_ofReal_mul_I]
    exact hx

  have h_summable := ArithmeticFunction.LSeriesSummable_vonMangoldt h_re

  exact LSeriesSummable_to_explicit_summable x y hx h_summable

lemma lem_realnx (n : ℕ) (x : ℝ) (_hn : n ≥ 1) (_hx : x ≥ 1) :
    ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-x) ≥ 0 := by
  apply mul_nonneg
  ·                                             
    exact ArithmeticFunction.vonMangoldt_nonneg
  ·                           
    apply Real.rpow_nonneg
                       
    exact Nat.cast_nonneg n


lemma sumRealLambda (x y : ℝ) (hx : 1 < x) :
    (∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re =
    ∑' (n : ℕ), ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re := by
  apply Complex.re_tsum
  exact Zseriesconverges1 x y hx

lemma lem_sumRealZ (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * I)).re = ∑' (n : ℕ), ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re := by
                                                         
  rw [lem_zeta1zetaseriesxy2 x y hx]
                                                   
  exact sumRealLambda x y hx

lemma complex_cpow_neg_real (n : ℕ) (x : ℝ) (_hn : n ≥ 1) : Complex.cpow (n : ℂ) ((-x) : ℂ) = Complex.ofReal ((n : ℝ) ^ (-x)) := by
                                     
  have h_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
                                   
  rw [Complex.cpow_eq_pow]
                                                   
  rw [Complex.ofReal_cpow h_nonneg (-x)]
                                          
  congr 1
                                 
  simp

lemma RealLambdaxy (n : ℕ) (x y : ℝ) (hn : n ≥ 1) (_hx : 1 < x) :
    ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re =
((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) * (Complex.cpow (n : ℂ) (-(y * I))).re := by
                                                              
  let b := ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-x)

  have h1 : (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) = (b : ℂ) := by
                                                
    have h_real_pow : Complex.cpow (n : ℂ) ((-x) : ℂ) = Complex.ofReal ((n : ℝ) ^ (-x)) := by
      exact complex_cpow_neg_real n x hn

    rw [h_real_pow]
    rw [← Complex.ofReal_mul]

  have h2 : (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I)) =
           ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ)) * Complex.cpow (n : ℂ) (-(y * I)) := by
    rw [mul_assoc]

  rw [h2, h1]

  exact lem_realbw b (Complex.cpow (n : ℂ) (-(y * I)))

lemma ReZseriesRen (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * I)).re = ∑' (n : ℕ), ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) * (Complex.cpow (n : ℂ) (-(y * I))).re := by
  rw [lem_sumRealZ x y hx]
  congr 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    exact RealLambdaxy n x y hn hx

lemma Rezeta1zetaseries (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
  rw [ReZseriesRen x y hx]
  congr 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [← lem_eacosalog3 n hn y]
                                                                                          
    congr 1
                                                                        
    rw [Complex.cpow_eq_pow]
                                     
    simp [I]

lemma complex_vonMangoldt_real_part_eq (n : ℕ) (x y : ℝ) (hn : n ≥ 1) (hx : 1 < x) :
((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re =
(ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
                                                   
  rw [lem_nxy n hn x y]

  rw [← mul_assoc]

  rw [RealLambdaxy n x y hn hx]

  have h_cpow : (Complex.cpow (n : ℂ) (-(y * I))).re = ((n : ℂ) ^ (-(y * I))).re := by
    rw [Complex.cpow_eq_pow]

  have h_I : -(y * I) = -y * Complex.I := by
    simp [I]

  rw [h_cpow, h_I]

  rw [lem_eacosalog3 n hn y]

lemma Rezetaseries_convergence (x y : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ))) := by
                                                                           
  have h1 : Summable (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) :=
    ReZconverges1 x y hx

  have h2 : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re =
                      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
    intro n
    by_cases h : n = 0
    · simp [h]
    · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      exact complex_vonMangoldt_real_part_eq n x y hn hx

  have h3 : (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) =
            (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ))) :=
    funext h2
  rwa [← h3]

lemma Rezetaseries2t (x t : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (2 * t * Real.log (n : ℝ))) := by
                                                  
  exact Rezetaseries_convergence x (2 * t) hx

lemma lem_cost0 (n : ℕ) (_hn : n ≥ 1) (t : ℝ) (ht : t = 0) : Real.cos (t * Real.log (n : ℝ)) = 1 := by
  rw [ht]
  simp

lemma Rezetaseries0 (x : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) := by
                                              
  have h1 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (0 * Real.log (n : ℝ))) :=
    Rezetaseries_convergence x 0 hx
                                             
  convert (preTransparency := .instances) h1 using 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [lem_cost0 n hn 0 rfl]
    ring

lemma uniform_bound_Z0_complex : ∃ δ0 > 0, ∃ C0 ≥ 0, ∀ δ : ℝ, 0 < δ → δ < δ0 → ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C0 := by
                                             
  let f : ℝ → ℂ := fun δ => -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))
                                           
  have hO := Z0bound
                                                                 
  rcases (Asymptotics.isBigO_iff).1 hO with ⟨c, hc⟩
  have h_event : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c := by
                             
    have : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c * ‖(1 : ℂ)‖ := hc
    refine this.mono ?_
    intro δ hδ
    have : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
    simpa [this] using hδ
                                                                                 
  rcases (Filter.eventually_iff_exists_mem).1 h_event with ⟨S, hS_in, hS_bound⟩
                                                                   
  rcases (mem_nhdsGT_iff_exists_Ioc_subset).1 hS_in with ⟨δ0, hδ0pos, hIoc_sub_S⟩
                                                                       
  refine ⟨δ0, hδ0pos, max c 0, le_max_right _ _, ?_⟩
  intro δ hδpos hδlt
                             
  have hδ_in_S : δ ∈ S := hIoc_sub_S ⟨hδpos, le_of_lt hδlt⟩
                                        
  have hnorm_le_c : ‖f δ‖ ≤ c := hS_bound δ hδ_in_S
                                                      
  exact le_trans hnorm_le_c (le_max_left _ _)


lemma tsum_nonneg_of_nonneg {f : ℕ → ℝ} (hnon : ∀ n, 0 ≤ f n) : 0 ≤ ∑' n, f n := by
  simpa using (tsum_nonneg hnon)

lemma vonMangoldt_rpow_nonneg (x : ℝ) : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) := by
  intro n
  have h1 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have h2 : 0 ≤ (n : ℝ) ^ (-x) := by
    exact Real.rpow_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n) _
  simpa using mul_nonneg h1 h2


lemma norm_negLogDerivZeta_real_eq_abs_tsum_vonMangoldt (x : ℝ) (hx : 1 < x) :
  ‖-logDerivZeta (x : ℂ)‖ = |∑' n, ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x))| := by
                                                    
  have hx' : 1 < (x : ℂ).re := by simpa using hx
  have hseries := zeta1zetaseries (s := (x : ℂ)) hx'
                                                                                      
  let g : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
  have hterm : ∀ n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)) = (g n : ℂ) := by
    intro n
    by_cases h : n = 0
    ·                                               
      have hv0C : (ArithmeticFunction.vonMangoldt 0 : ℂ) = 0 := by
        simp
      have hv0R : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by
        simp
      simp [g, h, hv0R]
    ·                                               
      have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
      have hcp : (n : ℂ) ^ (-(x : ℂ)) = Complex.ofReal ((n : ℝ) ^ (-x)) :=
        complex_cpow_neg_real n x hn
                                              
      have : (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ))
              = Complex.ofReal (ArithmeticFunction.vonMangoldt n) * Complex.ofReal ((n : ℝ) ^ (-x)) := by
        simp [hcp]
      simpa [g, Complex.ofReal_mul] using this
                                                          
  have hsum_eq : (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)))
                = ∑' n, (g n : ℂ) := by
                                             
    have hfun : (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)))
                = (fun n => (g n : ℂ)) := funext hterm
    simp [hfun]
                                                                     
  have hsum_ofReal : (∑' n, (g n : ℂ)) = Complex.ofReal (∑' n, g n) := by
    simpa using (Complex.ofReal_tsum g).symm
                                                                                               
  have hval : -logDerivZeta (x : ℂ) = Complex.ofReal (∑' n, g n) := by
                                         
    simpa [hsum_eq, hsum_ofReal] using hseries
                                                                            
  calc
    ‖-logDerivZeta (x : ℂ)‖ = ‖Complex.ofReal (∑' n, g n)‖ := by simp [hval]
    _ = |∑' n, g n| := by
      exact (RCLike.norm_ofReal (K := ℂ) (∑' n, g n))

lemma tsum_le_of_nonneg_of_le {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g) (_hnonneg : ∀ n, 0 ≤ f n) (hle : ∀ n, f n ≤ g n) : (∑' n, f n) ≤ (∑' n, g n) := by
  classical
  exact Summable.tsum_le_tsum hle hf hg

lemma rpow_neg_antitone {a x y : ℝ} (ha : 1 ≤ a) (hxy : x ≥ y) : a ^ (-x) ≤ a ^ (-y) := by

  simpa using (Real.rpow_le_rpow_of_exponent_le ha (neg_le_neg hxy))


lemma bounded_on_compact_interval (a b : ℝ) (h0 : 0 < a) (_hle : a ≤ b) : ∃ Cmid ≥ 0, ∀ δ : ℝ, a ≤ δ → δ ≤ b → ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ Cmid := by
                                      
  let s : Set ℝ := Set.Icc a b
  let f : ℝ → ℂ := fun δ => -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))

  let H : ℂ → ℂ := Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1

  have hH_diff : Differentiable ℂ H := by
    intro z
    rcases eq_or_ne z 1 with rfl | hz
    ·                                                 
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      ·                                                           
        filter_upwards [self_mem_nhdsWithin] with t ht
        have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) t := by
          have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) t :=
            (differentiableAt_id.sub_const 1)
          have h2 : DifferentiableAt ℂ riemannZeta t :=
            (differentiableAt_riemannZeta ht)
          exact h1.mul h2
        apply DifferentiableAt.congr_of_eventuallyEq hdiff
        filter_upwards [eventually_ne_nhds ht] with u hu using by
          simp [H, Function.update_of_ne hu]
      ·                                                     
        simpa [H, continuousAt_update_same] using riemannZeta_residue_one
    ·                                                        
      have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) z := by
        have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) z := (differentiableAt_id.sub_const 1)
        have h2 : DifferentiableAt ℂ riemannZeta z := (differentiableAt_riemannZeta hz)
        exact h1.mul h2
      apply DifferentiableAt.congr_of_eventuallyEq hdiff
      filter_upwards [eventually_ne_nhds hz] with u hu using by
        simp [H, Function.update_of_ne hu]

  let G : ℂ → ℂ := fun z => - (deriv H z) / H z

  have h_eq_on_pos : ∀ ⦃δ : ℝ⦄, 0 < δ →
      (-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))) = G ((1 : ℂ) + δ) := by
    intro δ hδ
                    
    let z : ℂ := (1 : ℂ) + δ
    have hz_ne_one : z ≠ (1 : ℂ) := by
      intro h
      have hre : (1 + δ : ℝ) = 1 := by
        simpa [z, Complex.add_re, Complex.ofReal_re] using congrArg Complex.re h
      have : δ = 0 := by linarith
      exact (ne_of_gt hδ) this
    have hzeta_ne : riemannZeta z ≠ 0 := by
      have : 1 < z.re := by simpa [z, Complex.add_re, Complex.ofReal_re] using by linarith
      exact riemannZeta_ne_zero_of_one_le_re (le_of_lt this)

    have h_id_deriv : deriv (fun u : ℂ => u - 1) z = 1 := by
      exact ((hasDerivAt_id z).sub_const 1).deriv
    have h_log_id : logDeriv (fun u : ℂ => u - 1) z = 1 / (z - 1) := by
      simp [logDeriv_apply, h_id_deriv]
    have hz1 : z - 1 ≠ 0 := by simpa using sub_ne_zero.mpr hz_ne_one
    have hζ : riemannZeta z ≠ 0 := hzeta_ne

    have h_deriv_mul : deriv (fun u : ℂ => (u - 1) * riemannZeta u) z
          = riemannZeta z + (z - 1) * deriv riemannZeta z := by
      have h1 : HasDerivAt (fun u : ℂ => u - 1) 1 z := (hasDerivAt_id z).sub_const 1
      have h2 : HasDerivAt riemannZeta (deriv riemannZeta z) z :=
        (differentiableAt_riemannZeta hz_ne_one).hasDerivAt
      simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using! (h1.mul h2).deriv

    have h_prodLog :
        logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z =
          logDeriv (fun u : ℂ => u - 1) z + logDerivZeta z := by
      have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) z := (differentiableAt_id.sub_const 1)
      have h2 : DifferentiableAt ℂ riemannZeta z := (differentiableAt_riemannZeta hz_ne_one)
      have hfnz : (fun u : ℂ => u - 1) z ≠ 0 := by simpa using hz1
      have hgnz : riemannZeta z ≠ 0 := hζ
      simpa [logDerivZeta] using!
        (logDeriv_mul (x := z) (f := fun u : ℂ => u - 1) (g := riemannZeta) hfnz hgnz h1 h2)

    have h_step : -logDerivZeta z - (1 / (z - 1))
        = - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z := by
      have : logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z
            = 1 / (z - 1) + logDerivZeta z := by
        simpa [h_log_id, add_comm] using h_prodLog
      have hneg : - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z
                 = - (1 / (z - 1) + logDerivZeta z) := by
        simpa using congrArg Neg.neg this
      simpa [sub_eq_add_neg, add_comm] using hneg.symm

    have h_H_eq : H z = (z - 1) * riemannZeta z := by
      simp [H, Function.update_of_ne hz_ne_one]

    have h_eq_event : (fun u : ℂ => H u) =ᶠ[nhds z] (fun u : ℂ => (u - 1) * riemannZeta u) := by
      filter_upwards [eventually_ne_nhds hz_ne_one] with u hu
      simp [H, Function.update_of_ne hu]

    have h_hasDeriv_prod :
        HasDerivAt (fun u : ℂ => (u - 1) * riemannZeta u)
          (riemannZeta z + (z - 1) * deriv riemannZeta z) z := by
      have h1 : HasDerivAt (fun u : ℂ => u - 1) 1 z := (hasDerivAt_id z).sub_const 1
      have h2 : HasDerivAt riemannZeta (deriv riemannZeta z) z :=
        (differentiableAt_riemannZeta hz_ne_one).hasDerivAt
      simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using! (h1.mul h2)

    have h_hasDeriv_H :
        HasDerivAt H (riemannZeta z + (z - 1) * deriv riemannZeta z) z :=
      h_hasDeriv_prod.congr_of_eventuallyEq h_eq_event

    have h_dH : deriv H z = riemannZeta z + (z - 1) * deriv riemannZeta z := by
      simpa using h_hasDeriv_H.deriv

    have h_log_to_G : - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z = G z := by
      have h' : logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z = (deriv H z) / H z := by
        simp [logDeriv_apply, h_H_eq, h_dH, h_deriv_mul]
      have hneg' := congrArg (fun w => -w) h'
      simpa [G, neg_div] using hneg'

    have : -logDerivZeta z - (1 / (z - 1)) = G z := by
      simpa using h_step.trans h_log_to_G

    simpa [z] using this

  let F : ℝ → ℂ := fun δ => G ((1 : ℂ) + δ)

  have hH_analytic_univ : AnalyticOnNhd ℂ H Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable).2 hH_diff

  have hF_contOn : ContinuousOn F s := by
    intro δ0 hδ0
                           
    let s0 : ℂ := (1 : ℂ) + δ0
    have hδ0pos : 0 < δ0 := lt_of_lt_of_le h0 hδ0.1
    have hs0_ne_one : s0 ≠ (1 : ℂ) := by
      intro h
      have hre : (1 + δ0 : ℝ) = 1 := by
        simpa [s0, Complex.add_re, Complex.ofReal_re] using congrArg Complex.re h
      have : δ0 = 0 := by linarith
      exact (ne_of_gt hδ0pos) this
    have hs0_re_gt_one : 1 < s0.re := by
      simpa [s0, Complex.add_re, Complex.ofReal_re] using by linarith
    have hζ_ne : riemannZeta s0 ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (le_of_lt hs0_re_gt_one)
    have hHs0_eq : H s0 = (s0 - 1) * riemannZeta s0 := by
      simp [H, Function.update_of_ne hs0_ne_one]
    have hHs0_ne : H s0 ≠ 0 := by
      have hs0m1_ne : s0 - 1 ≠ 0 := sub_ne_zero.mpr hs0_ne_one
      have : (s0 - 1) * riemannZeta s0 ≠ 0 := mul_ne_zero hs0m1_ne hζ_ne
      simpa [hHs0_eq] using this
                                                                                
    have hH_an_at_s0 : AnalyticAt ℂ H s0 := hH_analytic_univ s0 (by simp)
    have hH'_an_at_s0 : AnalyticAt ℂ (fun z => deriv H z) s0 := hH_an_at_s0.deriv
    have hG_an_at_s0 : AnalyticAt ℂ (fun z => G z) s0 := by
      have h_div : AnalyticAt ℂ (fun z => (deriv H z) / H z) s0 :=
        hH'_an_at_s0.div hH_an_at_s0 (by simpa using hHs0_ne)
      have h_neg : AnalyticAt ℂ (fun z => -((deriv H z) / H z)) s0 := h_div.neg
      simpa [G, div_eq_mul_inv, mul_left_comm, mul_comm, mul_assoc] using h_neg
    have hG_cont_s0 : ContinuousAt (fun z : ℂ => G z) s0 := hG_an_at_s0.continuousAt
                                               
    let affine : ℝ → ℂ := fun δ => (1 : ℂ) + (δ : ℂ)
    have h_affine_at : ContinuousAt affine δ0 :=
      (continuousAt_const).add Complex.continuous_ofReal.continuousAt
                           
    have hy : affine δ0 = s0 := by simp [affine, s0]
    have hG_at : ContinuousAt (fun z : ℂ => G z) (affine δ0) := by simpa [hy] using hG_cont_s0
    have h_comp_at : ContinuousAt (fun δ : ℝ => G (affine δ)) δ0 := hG_at.comp h_affine_at
    simpa [F, s, affine] using h_comp_at.continuousWithinAt

  have h_eq_on_s : ∀ ⦃δ : ℝ⦄, δ ∈ s → f δ = F δ := by
    intro δ hδ
    have hδpos : 0 < δ := lt_of_lt_of_le h0 hδ.1
    simpa [f, F] using h_eq_on_pos hδpos

  have hK : IsCompact s := isCompact_Icc
  have hNorm_contOn : ContinuousOn (fun δ => ‖F δ‖) s := hF_contOn.norm
  have hBdd : BddAbove ((fun δ => ‖F δ‖) '' s) := IsCompact.bddAbove_image hK hNorm_contOn
  rcases hBdd with ⟨C, hC⟩

  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro δ hδa hδb
                                                               
  change ‖f δ‖ ≤ max C 0
  have hδmem : δ ∈ s := ⟨hδa, hδb⟩
  have himg : (fun δ => ‖F δ‖) δ ∈ (fun δ => ‖F δ‖) '' s := ⟨δ, hδmem, rfl⟩
  have hbound : ‖F δ‖ ≤ C := hC himg
  have hbound' : ‖F δ‖ ≤ max C 0 := le_trans hbound (le_max_left _ _)
                                       
  have hfδ_eq : f δ = F δ := h_eq_on_s hδmem
  calc
    ‖f δ‖ = ‖F δ‖ := by simp [hfδ_eq]
    _ ≤ max C 0 := hbound'

lemma norm_one_div_coe_real_le_one_of_one_le {δ : ℝ} (h : 1 ≤ δ) : ‖(1 : ℂ) / (δ : ℂ)‖ ≤ 1 := by
                                                
  have hδpos : 0 < δ := lt_of_lt_of_le zero_lt_one h
  calc
    ‖(1 : ℂ) / (δ : ℂ)‖ = ‖(1 : ℂ)‖ / ‖(δ : ℂ)‖ := by
      exact norm_div (1 : ℂ) (δ : ℂ)
    _ = 1 / ‖(δ : ℂ)‖ := by simp
    _ = 1 / |δ| := by simp
    _ = 1 / δ := by simp [abs_of_nonneg (le_of_lt hδpos)]
    _ ≤ 1 := by
                                                           
      simpa using (one_div_le_one_div_of_le (ha := (zero_lt_one)) (h := h))

lemma Z0bound_const :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    ‖ -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C := by
                                                 
  rcases uniform_bound_Z0_complex with ⟨δ0, hδ0pos, C0, hC0nonneg, hsmall⟩
                          
  let a : ℝ := min δ0 1
  have ha_pos : 0 < a := lt_min_iff.2 ⟨hδ0pos, zero_lt_one⟩
  have ha_le_one : a ≤ 1 := min_le_right _ _
  rcases bounded_on_compact_interval a 1 ha_pos ha_le_one with ⟨Cmid, hCmid_nonneg, hmid⟩
                                                       
  let C2 : ℝ := ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ))
  have hC2_nonneg : 0 ≤ C2 := by
    have hnn : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) :=
      vonMangoldt_rpow_nonneg 2
    exact tsum_nonneg_of_nonneg hnn
                                                                                
  let C : ℝ := 2 + C0 + Cmid + C2
  have hCgt1 : 1 < C := by
    have : 2 ≤ 2 + C0 + Cmid + C2 := by linarith [hC0nonneg, hCmid_nonneg, hC2_nonneg]
    linarith
  refine ⟨C, hCgt1, ?_⟩
  intro δ hδpos
  by_cases hlt : δ < δ0
  ·                                        
    have hbound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C0 :=
      hsmall δ hδpos hlt
             
    have hC0_le_C : C0 ≤ C := by linarith
    exact le_trans hbound hC0_le_C
  ·          
    have hge : δ0 ≤ δ := le_of_not_gt hlt
    rcases le_total δ 1 with hδle1 | hδge1
    ·                              
      have ha_le_δ : a ≤ δ := le_trans (min_le_left δ0 1) hge
      have hbound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ Cmid :=
        hmid δ ha_le_δ hδle1
                 
      have hCmid_le_C : Cmid ≤ C := by linarith
      exact le_trans hbound hCmid_le_C
    ·                                                     
                      
      let x : ℝ := 1 + δ
      have hx1 : 1 < x := by
        have : 0 < δ := hδpos
        have : 1 < 1 + δ := lt_add_of_pos_right 1 this
        exact this
                                                           
      have h_norm_eq_abs_real : ‖-logDerivZeta (x : ℂ)‖
            = |∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)| :=
        norm_negLogDerivZeta_real_eq_abs_tsum_vonMangoldt x hx1
                                      
      have eqArg : ((1 : ℂ) + δ) = (x : ℂ) := by simp [x]
                                             
      have h_norm_eq_abs : ‖-logDerivZeta ((1 : ℂ) + δ)‖
            = |∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)| := by
        simpa [eqArg] using h_norm_eq_abs_real
                              
      let S : ℝ := ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
      have hsum_nonneg : 0 ≤ S := by
        change 0 ≤ ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
        exact tsum_nonneg_of_nonneg (vonMangoldt_rpow_nonneg x)
                                                                      
      have h_norm_le_sum : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ S := by
        have : ‖-logDerivZeta ((1 : ℂ) + δ)‖ = |S| := h_norm_eq_abs
        have : |S| = S := abs_of_nonneg hsum_nonneg
        exact le_of_eq (h_norm_eq_abs.trans this)
                                                                 
      have hx_ge_two : 2 ≤ x := by
                                     
        have : 1 ≤ δ := hδge1
        have : 2 ≤ 1 + δ := by linarith
        exact this
                                                   
      have h_le_2 : ∀ n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
                          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) := by
        intro n
        by_cases h0 : n = 0
        · simp [h0]
        · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h0
          have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have hrpow : (n : ℝ) ^ (-x) ≤ (n : ℝ) ^ (-(2 : ℝ)) :=
            rpow_neg_antitone hn' hx_ge_two
          have hΛ_nonneg : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
            ArithmeticFunction.vonMangoldt_nonneg
          exact mul_le_mul_of_nonneg_left hrpow hΛ_nonneg
                                   
      have h_summ_x : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) := by
        exact Rezetaseries0 x hx1
      have h_summ_2 : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ))) :=
        Rezetaseries0 2 (by norm_num)
      have hsum_le : S ≤ C2 := by
                                                
        have h_nonneg_x : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) :=
          vonMangoldt_rpow_nonneg x
        exact tsum_le_of_nonneg_of_le h_summ_x h_summ_2 h_nonneg_x h_le_2
                                        
      have h_norm_le_C2 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C2 :=
        le_trans h_norm_le_sum hsum_le
                                                                
      have h_one_div_le : ‖(1 : ℂ) / (δ : ℂ)‖ ≤ 1 := norm_one_div_coe_real_le_one_of_one_le hδge1
      have htriangle : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖
                        ≤ ‖-logDerivZeta ((1 : ℂ) + δ)‖ + ‖(1 : ℂ) / (δ : ℂ)‖ :=
        norm_sub_le _ _
      have hlarge_bound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C2 + 1 := by
        refine le_trans htriangle ?_
        exact add_le_add h_norm_le_C2 h_one_div_le
                     
      have hC2_le_C : C2 + 1 ≤ C := by linarith
      exact le_trans hlarge_bound hC2_le_C

lemma Z0boundRe_const :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    ((-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))).re) ≤ C := by
                                                 
  rcases Z0bound_const with ⟨C, hCpos, hC⟩
  use C
  constructor
  · exact hCpos
  · intro δ hδ
                                                    
    have h_bound := hC δ hδ
    exact le_trans (Complex.re_le_norm _) h_bound

lemma Z0boundRe_const2 :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    ((-logDerivZeta ((1 : ℂ) + δ)).re + (-(1 / (δ : ℂ))).re) ≤ C := by
                                           
  rcases Z0boundRe_const with ⟨C, hC_pos, hC⟩
  use C, hC_pos
  intro δ hδ
  have h_sub_re : ((-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))).re) =
    ((-logDerivZeta ((1 : ℂ) + δ)).re + (-(1 / (δ : ℂ))).re) := by
    rw [Complex.sub_re]
    rfl
  rw [← h_sub_re]
  exact hC δ hδ

lemma Z0boundRe_const3 :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    (-logDerivZeta ((1 : ℂ) + δ)).re - (1 / δ) ≤ C := by
                                                                        
  rcases Z0boundRe_const2 with ⟨C, hCpos, hC⟩
  use C, hCpos
  intro δ hδ
                           
  have h := hC δ hδ
                                                                  
  have h_re_eq : (-(1 / (δ : ℂ))).re = -(1 / δ) := by
    rw [Complex.neg_re, Complex.div_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im]
    simp [Complex.normSq_ofReal]
                                          
  rwa [h_re_eq] at h

lemma Z341bounds_const :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0) (_hδ1 : δ < 1), ∀ t : ℝ, 2 < |t| → ∀ σ : ℝ,
    (σ + t * Complex.I) ∈ zeroZ →
      3 * (-logDerivZeta ((1 : ℂ) + δ)).re
    + 4 * (-logDerivZeta ((1 : ℂ) + δ + t * Complex.I)).re
    +     (-logDerivZeta ((1 : ℂ) + δ + (2 * t) * Complex.I)).re
    ≤ 3 / δ - 4 / (1 + δ - σ) + C * Real.log (|t| + 2) := by
                                                                                           
  rcases Z0boundRe_const3 with ⟨C0, hC0pos, hZ0⟩
  rcases Z1bound with ⟨C1, hC1pos, hZ1⟩
  rcases lem_Z2bound with ⟨C2, hC2pos, hZ2⟩

  let C := 3 * C0 + 4 * C1 + C2

  have hC_gt_one : 1 < C := by
    have h1 : 1 < C0 := hC0pos
    have h2 : 3 < 3 * C0 := by linarith [mul_lt_mul_of_pos_left h1 (by norm_num : (0 : ℝ) < 3)]
    have h3 : 0 < 4 * C1 := mul_pos (by norm_num) (lt_trans zero_lt_one hC1pos)
    have h4 : 0 < C2 := lt_trans zero_lt_one hC2pos
    linarith [h2, h3, h4]

  use C
  constructor
  · exact hC_gt_one
  · intro δ hδpos hδ1 t ht σ hσ

    have hZ0_bound : (-logDerivZeta ((1 : ℂ) + δ)).re ≤ C0 + (1 / δ) := by
      have := hZ0 δ hδpos
      linarith

    have hZ1_bound : (-logDerivZeta ((1 : ℂ) + δ + t * Complex.I)).re ≤ -(1 / (1 + δ - σ)) + C1 * Real.log (|t| + 2) := by
      let s := σ + t * Complex.I
      have hs_mem : s ∈ zeroZ := hσ
      have hs_im : s.im = t := by simp [s]
      have hs_re : s.re = σ := by simp [s]
      have hδ_cond : 0 < δ ∧ δ < 1 := ⟨hδpos, hδ1⟩
      have := hZ1 δ hδ_cond t ht s ⟨hs_mem, hs_im⟩
      rw [hs_re] at this
      exact this

    have hZ2_bound : (-logDerivZeta ((1 : ℂ) + δ + (2 * t) * Complex.I)).re ≤ C2 * Real.log (|t| + 2) := by
      have hδ_cond : 0 < δ ∧ δ < 1 := ⟨hδpos, hδ1⟩
      exact hZ2 t ht δ hδ_cond

    have hlog_ge_one : 1 ≤ Real.log (|t| + 2) := by
      have h1 : 2 < |t| := ht
      have h2 : Real.exp 1 < 3 := lem_three_gt_e
      have he_lt_t2 : Real.exp 1 < |t| + 2 := by linarith
      have ht2_pos : 0 < |t| + 2 := by linarith [abs_nonneg t]
      exact Real.le_log_iff_exp_le ht2_pos |>.mpr (le_of_lt he_lt_t2)

    calc
      3 * (-logDerivZeta ((1 : ℂ) + δ)).re + 4 * (-logDerivZeta ((1 : ℂ) + δ + t * Complex.I)).re + (-logDerivZeta ((1 : ℂ) + δ + (2 * t) * Complex.I)).re
        ≤ 3 * (C0 + (1 / δ)) + 4 * (-(1 / (1 + δ - σ)) + C1 * Real.log (|t| + 2)) + C2 * Real.log (|t| + 2) := by
          exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hZ0_bound (by norm_num)) (mul_le_mul_of_nonneg_left hZ1_bound (by norm_num))) hZ2_bound
      _ = 3 * C0 + 3 / δ - 4 / (1 + δ - σ) + (4 * C1 + C2) * Real.log (|t| + 2) := by ring
      _ = 3 / δ - 4 / (1 + δ - σ) + 3 * C0 + (4 * C1 + C2) * Real.log (|t| + 2) := by ring
      _ = 3 / δ - 4 / (1 + δ - σ) + ((4 * C1 + C2) * Real.log (|t| + 2) + 3 * C0) := by ring
      _ ≤ 3 / δ - 4 / (1 + δ - σ) + (4 * C1 + C2 + 3 * C0) * Real.log (|t| + 2) := by
                                                                           
        have hC0_pos : 0 < C0 := lt_trans zero_lt_one hC0pos
        have hC0_nonneg : 0 ≤ 3 * C0 := mul_nonneg (by norm_num) (le_of_lt hC0_pos)
        have h_absorb := absorb_pos_constant_into_log (L := Real.log (|t| + 2)) (A := 4 * C1 + C2) (c := 3 * C0) hlog_ge_one hC0_nonneg
                                                                                                               
        exact add_le_add_right h_absorb (3 / δ - 4 / (1 + δ - σ))
      _ = 3 / δ - 4 / (1 + δ - σ) + (3 * C0 + 4 * C1 + C2) * Real.log (|t| + 2) := by ring
      _ = 3 / δ - 4 / (1 + δ - σ) + C * Real.log (|t| + 2) := by ring




lemma Rezeta1zetaseries1 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta + t * I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)) := by
                                                         
  have h1 : 1 < 1 + delta := by linarith [hdelta]
  convert (preTransparency := .instances) Rezeta1zetaseries (1 + delta) t h1
                                                
  simp [Complex.ofReal_add]

lemma Rezeta1zetaseries2 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ)) := by
                                                             
  have h1 : 1 < 1 + delta := by linarith [hdelta]
                                                                                 
  have h2 : (1 : ℂ) + delta + (2 * t) * I = (1 + delta : ℝ) + ((2 * t) : ℝ) * I := by
    simp [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul]
  rw [h2]
  exact Rezeta1zetaseries (1 + delta) (2 * t) h1

lemma Rezeta1zetaseries0 (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) := by
                                             
  have h_series : (-logDerivZeta ((1 : ℂ) + delta + 0 * I)).re =
                  ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (0 * Real.log (n : ℝ)) :=
    Rezeta1zetaseries1 0 delta hdelta

  have h_lhs : (-logDerivZeta ((1 : ℂ) + delta + 0 * I)).re = (-logDerivZeta ((1 : ℂ) + delta)).re := by
    congr 2
    simp

  have h_rhs : ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (0 * Real.log (n : ℝ)) =
               ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) := by
    congr 1
    funext n
    by_cases h : n = 0
    · simp [h]
    · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      rw [lem_cost0 n hn 0 rfl, mul_one]

  rw [← h_lhs, h_series, h_rhs]

lemma Z341series (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (3 * (-logDerivZeta ((1 : ℂ) + delta)).re +
     4 * (-logDerivZeta ((1 : ℂ) + delta + t * I)).re +
     (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * I)).re)
    =
    (3 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) +
     4 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)) +
     ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ))) := by
  rw [Rezeta1zetaseries0 delta hdelta, Rezeta1zetaseries1 t delta hdelta, Rezeta1zetaseries2 t delta hdelta]


lemma lem341series (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (3 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)))
    + (4 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)))
    + (∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ)))
    = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
                                       
  have h1 : 1 < 1 + delta := by linarith [hdelta]

  have h2 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta))) :=
    Rezetaseries0 (1 + delta) h1

  have h3 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ))) :=
    Rezetaseries_convergence (1 + delta) t h1

  have h4 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ))) :=
    Rezetaseries2t (1 + delta) t h1

  rw [← Summable.tsum_mul_left 3 h2]
  rw [← Summable.tsum_mul_left 4 h3]

  rw [← Summable.tsum_add (Summable.mul_left 3 h2) (Summable.mul_left 4 h3)]
  rw [← Summable.tsum_add]

  congr 1
  ext n
  ring

  · exact Summable.add (Summable.mul_left 3 h2) (Summable.mul_left 4 h3)
  · exact h4


lemma lem_341series2 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (3 * (-logDerivZeta ((1 : ℂ) + delta)).re +
     4 * (-logDerivZeta ((1 : ℂ) + delta + t * I)).re +
     (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * I)).re)
    =
    ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  rw [Z341series t delta hdelta]
  exact lem341series t delta hdelta

lemma lem_Lambda_pos_trig_sum (n : ℕ) (delta : ℝ) (t : ℝ) (hn : n ≥ 1) (hdelta : delta > 0) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  apply mul_nonneg
  ·                                                                        
    apply lem_realnx n (1 + delta) hn
                         
    linarith [hdelta]
  ·                                                                                          
    exact lem_postriglogn n hn t


lemma lem_seriespos (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    0 ≤ ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  apply tsum_nonneg
  intro n
  by_cases h : n = 0
  ·                                                            
    simp [h]
  ·                                             
    have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    exact lem_Lambda_pos_trig_sum n delta t hn hdelta

lemma Z341pos (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    0 ≤ 3 * (-logDerivZeta ((1 : ℂ) + delta)).re +
        4 * (-logDerivZeta ((1 : ℂ) + delta + t * I)).re +
        (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * I)).re := by
  rw [lem_341series2 t delta hdelta]
  exact lem_seriespos t delta hdelta


lemma log_abs_add_two_pos (t : ℝ) : 0 < Real.log (abs t + 2) := by
                                                    
  have h0 : 0 ≤ abs t + 2 := by
    have h' : 0 ≤ abs t := abs_nonneg t
    linarith
  have hge : (2 : ℝ) ≤ abs t + 2 := by
    have h' : 0 ≤ abs t := abs_nonneg t
    have := add_le_add_left h' (2 : ℝ)
    simp
  have hgt : 1 < abs t + 2 := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hge
                                                                
  exact (Real.log_pos_iff h0).2 hgt



lemma pos_delta_from_C_L {C L : ℝ} (hC : 0 < C) (hL : 0 < L) : 0 < 1 / (2 * C * L) := by
  have hCL : 0 < C * L := mul_pos hC hL
  have h2 : 0 < (2 : ℝ) := by norm_num
  have hpos : 0 < 2 * C * L := by
    have : 0 < 2 * (C * L) := mul_pos h2 hCL
    simpa [mul_assoc] using this
  exact one_div_pos.mpr hpos


lemma log_abs_two_pos (t : ℝ) : 0 < Real.log (|t| + 2) := by
  simpa using log_abs_add_two_pos t

lemma two_C_log_pos {C t : ℝ} (hC : 0 < C) : 0 < 2 * C * Real.log (|t| + 2) := by
  have hL : 0 < Real.log (|t| + 2) := log_abs_two_pos t
  have h2 : 0 < (2 : ℝ) := by norm_num
  have hCL : 0 < C * Real.log (|t| + 2) := mul_pos hC hL
  have : 0 < 2 * (C * Real.log (|t| + 2)) := mul_pos h2 hCL
  simpa [mul_comm, mul_left_comm, mul_assoc] using this





lemma rhs_eval_of_inv (C L δ : ℝ) (h : 1 / δ = 2 * C * L) : 3 / δ + C * L = 7 * C * L := by
  calc
    3 / δ + C * L
        = 3 * (1 / δ) + C * L := by simp [div_eq_mul_inv]
    _   = 3 * (2 * C * L) + C * L := by simp [h]
    _   = 6 * C * L + C * L := by ring
    _   = 7 * C * L := by ring

lemma lem341tsC :
    ∃ C > 1, ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| →
    4 / (1 - s.re + 1 / (2 * C * Real.log (abs s.im + 2))) ≤ 7 * C * Real.log (abs s.im + 2) := by
                                             
  obtain ⟨C, hCpos, hbound⟩ := Z341bounds_const
  refine ⟨C, hCpos, ?_⟩
  intro s hs hTim

  let L : ℝ := Real.log (|s.im| + 2)
  have hLpos : 0 < L := log_abs_two_pos (s.im)
  let δ : ℝ := 1 / (2 * C * L)

  have hCpos_weak : 0 < C := lt_trans zero_lt_one hCpos
  have hδpos : 0 < δ := pos_delta_from_C_L hCpos_weak hLpos

  have hδlt : δ < 1 := by
                                               
    have hL_gt_1 : 1 < L := by
      have h5_lt : 4 < |s.im| + 2 := by linarith [hTim]
      have hL_gt_log5 : Real.log 4 < L := Real.log_lt_log (by norm_num) h5_lt
      have hlog5_gt_1 : 1 < Real.log 4 := by
        have h5_gt_e : Real.exp 1 < 4 := by
          have h3_gt_e := lem_three_gt_e
          linarith [h3_gt_e]
        rw [← Real.log_exp 1]
        exact Real.log_lt_log (Real.exp_pos 1) h5_gt_e
      linarith [hlog5_gt_1, hL_gt_log5]
                                                      
    have h2CL_gt_1 : 1 < 2 * C * L := by
                                                                             
      have hCL_gt_1 : 1 < C * L := by
        calc C * L
          > 1 * L := by exact mul_lt_mul_of_pos_right hCpos hLpos
          _ = L := by simp
          _ > 1 := hL_gt_1
      have h2_pos : (0 : ℝ) < 2 := by norm_num
      calc 2 * C * L
        = 2 * (C * L) := by ring
        _ > 2 * 1 := by exact mul_lt_mul_of_pos_left hCL_gt_1 h2_pos
        _ = 2 := by simp
        _ > 1 := by norm_num
                                  
    simp only [δ]
    rw [div_lt_one_iff]
    left
    exact ⟨two_C_log_pos hCpos_weak, h2CL_gt_1⟩

  have hmem : (s.re + s.im * Complex.I) ∈ zeroZ := by
    simpa [Complex.re_add_im] using hs.1
  have hupper := hbound δ hδpos hδlt (s.im) hTim (s.re) hmem

  have hpos := Z341pos (s.im) δ hδpos

  have hRHS_nonneg : 0 ≤ 3 / δ - 4 / (1 + δ - s.re) + C * L := le_trans hpos hupper
  have hineq1 : 4 / (1 + δ - s.re) ≤ 3 / δ + C * L := by linarith [hRHS_nonneg]

  have hineq2 : 4 / (1 - s.re + δ) ≤ 3 / δ + C * L := by
    convert (preTransparency := .instances) hineq1 using 2
    ring

  have hinv : 1 / δ = 2 * C * L := by
    simp only [δ, one_div, inv_inv]

  have hrhs_eval : 3 / δ + C * L = 7 * C * L := rhs_eval_of_inv C L δ hinv

  have hfinal : 4 / (1 - s.re + δ) ≤ 7 * C * L := by
    rw [← hrhs_eval]
    exact hineq2

  convert (preTransparency := .instances) hfinal


lemma div_le_to_le_mul (x y z : ℝ) (hy : 0 < y) (h : x / y ≤ z) : x ≤ z * y := by
  rwa [div_le_iff₀ hy] at h

lemma le_mul_to_le_div (x y z : ℝ) (hy : 0 < y) (h : x ≤ z * y) : x / y ≤ z := by
  rw [div_le_iff₀ hy]
  exact h

lemma reciprocal_div_inequality (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : 4 / a ≤ b) : a ≥ 4 / b := by
                                                                
  have h1 : 4 ≤ b * a := div_le_to_le_mul 4 a b ha h
                                       
  have h2 : 4 ≤ a * b := by
    rwa [mul_comm] at h1
                                                              
  have h3 : 4 / b ≤ a := le_mul_to_le_div 4 b a hb h2
                                                                           
  exact h3

lemma lem341tsC2 :
    ∃ C > 1, ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| →
          1 - s.re + 1 / (2 * C * Real.log (abs s.im + 2)) ≥ 4 / (7 * C * Real.log (abs s.im + 2)) := by
                                                 
  rcases lem341tsC with ⟨C, hCpos, hT⟩
  refine ⟨C, hCpos, ?_⟩
  intro s hs hTs
                                                      
  set a := 1 - s.re + 1 / (2 * C * Real.log (abs s.im + 2)) with ha
  set b := 7 * C * Real.log (abs s.im + 2) with hb
  have hineq : 4 / a ≤ b := by
    simpa [ha, hb] using hT s hs hTs
                  
  have h_abs_nonneg : 0 ≤ |s.im| := abs_nonneg _
  have h_two_le : (2 : ℝ) ≤ |s.im| + 2 := by
    have h' : (2 : ℝ) + 0 ≤ 2 + |s.im| := add_le_add_right h_abs_nonneg 2
    simp
  have h_one_lt : (1 : ℝ) < |s.im| + 2 := lt_of_lt_of_le one_lt_two h_two_le
  have hx0 : 0 ≤ |s.im| + 2 := by linarith [h_abs_nonneg]
  have hlogpos : 0 < Real.log (|s.im| + 2) := (Real.log_pos_iff hx0).2 h_one_lt
  have h7pos : 0 < (7 : ℝ) := by exact_mod_cast (by decide : (0 : ℕ) < 7)
  have hbpos : 0 < b := by
    have h7Cpos : 0 < 7 * C := by linarith
    exact mul_pos h7Cpos hlogpos
                  
  rcases hs with ⟨_, hRepos, hRelt⟩
  have h1 : 0 < 1 - s.re := sub_pos.mpr hRelt
  have h2pos : 0 < (2 : ℝ) := lt_trans zero_lt_one one_lt_two
  have h2Cpos : 0 < (2 : ℝ) * C := by linarith
  have hdenpos : 0 < 2 * C * Real.log (|s.im| + 2) := mul_pos h2Cpos hlogpos
  have hinvpos : 0 < 1 / (2 * C * Real.log (|s.im| + 2)) := one_div_pos.mpr hdenpos
  have hapos : 0 < a := by
    have := add_pos h1 hinvpos
    simpa [ha] using this
                                                           
  have hres := reciprocal_div_inequality a b hapos hbpos hineq
  simpa [ha, hb] using hres

lemma simplify_4_7_2 (C L : ℝ) : 4 / (7 * C * L) - 1 / (2 * C * L) = 1 / (14 * C * L) := by
                                             
  have h1 : (4 : ℝ) / (7 * (C * L)) = (4 : ℝ) / (7 : ℝ) / (C * L) := by
    simpa using (div_mul_eq_div_div (a := (4 : ℝ)) (b := (7 : ℝ)) (c := C * L))
  have h2 : (1 : ℝ) / (2 * (C * L)) = (1 : ℝ) / (2 : ℝ) / (C * L) := by
    simpa using (div_mul_eq_div_div (a := (1 : ℝ)) (b := (2 : ℝ)) (c := C * L))
                                                     
  have h3' : ((4 : ℝ) / (7 : ℝ)) - (2 : ℝ)⁻¹ = (14 : ℝ)⁻¹ := by
    have h3 : ((4 : ℝ) / (7 : ℝ)) - ((1 : ℝ) / (2 : ℝ)) = (1 : ℝ) / (14 : ℝ) := by
      norm_num
    simpa [one_div] using h3
  calc
    4 / (7 * C * L) - 1 / (2 * C * L)
        = (4 : ℝ) / (7 * (C * L)) - (1 : ℝ) / (2 * (C * L)) := by
          simp [mul_assoc]
    _ = (4 : ℝ) / (7 : ℝ) / (C * L) - (1 : ℝ) / (2 : ℝ) / (C * L) := by
          simp [h1, h2]
    _ = (((4 : ℝ) / (7 : ℝ)) - ((1 : ℝ) / (2 : ℝ))) / (C * L) := by
          simpa using (sub_div (a := ((4 : ℝ) / (7 : ℝ))) (b := ((1 : ℝ) / (2 : ℝ))) (c := C * L)).symm
    _ = (((4 : ℝ) / (7 : ℝ)) - (2 : ℝ)⁻¹) / (C * L) := by
          simp [one_div]
    _ = (14 : ℝ)⁻¹ / (C * L) := by
          simp [h3']
    _ = 1 / (14 * (C * L)) := by
          simpa [mul_comm, mul_left_comm, mul_assoc, one_div] using
            (div_mul_eq_div_div (a := (1 : ℝ)) (b := (14 : ℝ)) (c := C * L)).symm
    _ = 1 / (14 * C * L) := by simp [mul_assoc]

lemma fraction_diff_lower_bound (C L a : ℝ) : 4 / (7 * C * L) ≤ a + 1 / (2 * C * L) → 1 / (14 * C * L) ≤ a := by
  intro h
  have h' : 4 / (7 * C * L) - 1 / (2 * C * L) ≤ a := (sub_le_iff_le_add).mpr h
  have hdiff : 1 / (14 * C * L) = 4 / (7 * C * L) - 1 / (2 * C * L) := by
    symm
    exact simplify_4_7_2 C L
  calc
    1 / (14 * C * L)
        = 4 / (7 * C * L) - 1 / (2 * C * L) := hdiff
    _ ≤ a := h'

lemma lem341tsC3 :
    ∃ C > 1, ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| →
    1 - s.re ≥ 1 / (14 * C * Real.log (abs s.im + 2)) := by
  obtain ⟨C, hCpos, hT⟩ := lem341tsC2
  refine ⟨C, hCpos, ?_⟩
  intro s hs hTle
  have h := hT s hs hTle
                                                                             
  have h' : 4 / (7 * C * Real.log (abs s.im + 2)) ≤
      (1 - s.re) + 1 / (2 * C * Real.log (abs s.im + 2)) := by
    simpa [ge_iff_le, add_comm, add_left_comm, add_assoc] using h
                                            
  have h'' := fraction_diff_lower_bound C (Real.log (abs s.im + 2)) (1 - s.re) h'
             
  simpa [ge_iff_le, mul_comm, mul_left_comm, mul_assoc] using h''

lemma zerofree :
    ∃ c, c > 0 ∧ c < 1 ∧ ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| → s.re ≤ 1 - c / (Real.log (abs s.im + 2)) := by
                                          
  rcases lem341tsC3 with ⟨C0, hC0pos, hT⟩
                                                 
  set C : ℝ := 1 / (14 * C0) with hCdef
               
  have h14pos : 0 < (14 : ℝ) := by norm_num
  have hC0pos' : 0 < C0 := lt_trans zero_lt_one hC0pos
  have hCpos : 0 < C := by
    have hdenpos : 0 < 14 * C0 := mul_pos h14pos hC0pos'
    exact one_div_pos.mpr hdenpos
                                                                             
  have hClt1 : C < 1 := by
    have h14C0_pos : 0 < 14 * C0 := mul_pos h14pos hC0pos'
    have h14C0_gt_1 : 1 < 14 * C0 := by
      have h14_gt_1 : (1 : ℝ) < 14 := by norm_num
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ < 14 * 1 := by exact mul_lt_mul_of_pos_right h14_gt_1 zero_lt_one
        _ < 14 * C0 := by exact mul_lt_mul_of_pos_left hC0pos h14pos
    rw [hCdef]
    rw [div_lt_one_iff]
    left
    exact ⟨h14C0_pos, h14C0_gt_1⟩
                                                  
  refine ⟨C, hCpos, hClt1, ?_⟩
  intro s hs hTle
                                    
  set L := Real.log (abs s.im + 2) with hLdef
                                                          
  have hb0 := hT s hs hTle
                                                 
  have hb' : C / L ≤ 1 - s.re := by
    simpa [hLdef, hCdef, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hb0
                                             
  have : s.re ≤ 1 - C / L := by linarith
  simpa [hLdef] using this


















































































































lemma ZetaZeroFree_p :
    ∃ (A : ℝ) (_ : A ∈ Set.Ioc 0 (1 / 2)),
    ∀ (σ : ℝ)
    (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Set.Ico (1 - A / Real.log |t| ^ 1) 1),
    riemannZeta (σ + t * Complex.I) ≠ 0 := by
                                                                             
  obtain ⟨c, hc_pos, hc_lt_one, hbound⟩ := zerofree
                                               
  let A0 : ℝ := min (1 / 2 : ℝ) (c / 2)
  let A : ℝ := min A0 ((1 / 4 : ℝ) * Real.log 3)
  have hA_pos : 0 < A := by
    have h1 : 0 < (1 / 2 : ℝ) := by norm_num
    have h2 : 0 < c / 2 := by
      have : 0 < (2 : ℝ) := by norm_num
      exact div_pos hc_pos this
    have hA0pos : 0 < A0 := lt_min_iff.mpr ⟨h1, h2⟩
    have hlog3pos : 0 < Real.log (3 : ℝ) :=
      (Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 3)).2 (by norm_num)
    have h3 : 0 < (1 / 4 : ℝ) * Real.log 3 := by
      exact mul_pos (by norm_num) hlog3pos
    exact lt_min_iff.mpr ⟨hA0pos, h3⟩
  have hA_le_half : A ≤ 1/2 := by
    have : A ≤ A0 := min_le_left _ _
    exact this.trans (min_le_left _ _)
  have hA_le_c2 : A ≤ c / 2 := by
    have : A ≤ A0 := min_le_left _ _
    exact this.trans (min_le_right _ _)
  have hA_le_log3quarter : A ≤ (1 / 4 : ℝ) * Real.log 3 := min_le_right _ _
  refine ⟨A, ?_, ?_⟩
  · exact ⟨hA_pos, hA_le_half⟩
  · intro σ t htgt3 hσI hzero
                        
    set L := Real.log |t| with hLdef
    set Lp := Real.log (|t| + 2) with hLpdef
    have hpos_abs : 0 ≤ |t| := abs_nonneg t
    have hLpos : 0 < L := (Real.log_pos_iff hpos_abs).2 (lt_trans (by norm_num) htgt3)
    have hLp_pos_arg : 0 < |t| + 2 := by linarith
    have hLp_pos : 0 < Lp := (Real.log_pos_iff (le_of_lt hLp_pos_arg)).2 (by linarith)
                                      
    have hlog3_le_L : Real.log 3 ≤ L := by
      have h3pos : 0 < (3 : ℝ) := by norm_num
      have : (3 : ℝ) ≤ |t| := le_of_lt htgt3
      simpa [hLdef] using Real.log_le_log h3pos this
                                  
    have hquarter_ratio_le : ((1 / 4 : ℝ) * Real.log 3) / L ≤ (1 / 4 : ℝ) := by
      have h := div_le_div_of_nonneg_right hlog3_le_L (le_of_lt hLpos)
      have h' := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1/4)
      have hne : L ≠ 0 := ne_of_gt hLpos
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hne] using h'
                          
    have hA_over_le_quarter : A / L ≤ (1 / 4 : ℝ) := by
      have := div_le_div_of_nonneg_right hA_le_log3quarter (le_of_lt hLpos)
      exact this.trans hquarter_ratio_le
                                   
    have hlow : 1 - A / L ≤ σ := by simpa [hLdef, pow_one] using hσI.1
    have hσ_ge_34 : (3 / 4 : ℝ) ≤ σ := by
      have : (3 / 4 : ℝ) ≤ 1 - A / L := by linarith
      exact this.trans hlow
    have hσ_pos : 0 < σ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < (3/4 : ℝ)) hσ_ge_34
    have hσ_lt_one : σ < 1 := hσI.2
                   
    have hlog_lt : Lp < 2 * L := by
      have h1 : 0 < |t| - 2 := by linarith
      have h2 : 0 < |t| + 1 := by linarith
      have hprod_pos : 0 < (|t| - 2) * (|t| + 1) := mul_pos h1 h2
      have hpoly : |t| * |t| - (|t| + 2) = (|t| - 2) * (|t| + 1) := by ring
      have hlt : |t| + 2 < |t| * |t| := by
        calc
          |t| + 2 < |t| + 2 + (|t| - 2) * (|t| + 1) := by linarith [hprod_pos]
          _ = |t| * |t| := by rw [← hpoly]; ring
      have hposb : 0 < |t| + 2 := by linarith
      have hlog_lt' : Real.log (|t| + 2) < Real.log (|t| * |t|) := Real.log_lt_log hposb hlt
      have hlogmul : Real.log (|t| ^ 2) = 2 * Real.log |t| := Real.log_pow |t| 2
      calc
        Lp = Real.log (|t| + 2) := by simp [hLpdef]
        _ < Real.log (|t| * |t|) := hlog_lt'
        _ = Real.log (|t| ^ 2) := by simp [pow_two]
        _ = 2 * Real.log |t| := by simp
        _ = 2 * L := by simp [hLdef]
                                               
    have h_inv_comp : 1 / (2 * L) < 1 / Lp := one_div_lt_one_div_of_lt hLp_pos hlog_lt
    have hstep2 : (c / 2) / L < c / Lp := by
      have hcpos' : 0 < c := hc_pos
      have : c * (1 / (2 * L)) < c * (1 / Lp) := mul_lt_mul_of_pos_left h_inv_comp hcpos'
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
                                          
    have hstep1 : A / L ≤ (c / 2) / L := by
      have := div_le_div_of_nonneg_right hA_le_c2 (le_of_lt hLpos)
      simpa [div_eq_mul_inv] using this
    have hstrict_div : A / L < c / Lp := lt_of_le_of_lt hstep1 hstep2
                                                       
    have hσ_gt : 1 - c / Lp < σ := by
      have hneg' : - (c / Lp) < - (A / L) := by simpa [neg_div] using neg_lt_neg hstrict_div
      have : 1 - c / Lp < 1 - A / L := by simpa [sub_eq_add_neg] using! add_lt_add_right hneg' 1
      exact this.trans_le hlow
                                             
    let s : ℂ := Complex.mk σ t
    have hs_zero : riemannZeta s = 0 := by simpa [s, Complex.mk_eq_add_mul_I] using hzero
    have hs_in_zeroZ : s ∈ zeroZ := by simpa [zeroZ] using hs_zero
    have hpre : s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1 := by
      refine ⟨hs_in_zeroZ, ?_, ?_⟩
      · simpa [s] using hσ_pos
      · simpa [s] using hσ_lt_one
    have him_bound : 2 < |s.im| := by
      have : 2 < |t| := lt_trans (by norm_num) htgt3
      simpa [s] using this
    have hbound_applied : s.re ≤ 1 - c / Real.log (abs s.im + 2) := hbound s hpre him_bound
    have hle : σ ≤ 1 - c / Lp := by simpa [s, hLpdef] using hbound_applied
    have hcontr : σ < σ := lt_of_le_of_lt hle hσ_gt
    exact (lt_irrefl _ : ¬ σ < σ) hcontr

open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

end Erdos970

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.ZetaZeroFree
namespace Erdos970

open _root_.Complex _root_.Topology _root_.Filter _root_.Interval _root_.Set _root_.Asymptotics
local notation (name := riemannzeta') "ζ" => riemannZeta
local notation (name := derivriemannzeta') "ζ'" => deriv riemannZeta

local notation "I" => Complex.I



lemma ZetaNoZerosInBox' (T : ℝ) :
    ∃ (σ : ℝ) (_ : σ < 1), ∀ (t : ℝ) (_ : |t| ≤ T)
    (σ' : ℝ) (_ : σ' ≥ σ), ζ (σ' + t * I) ≠ 0 := by
  by_contra h
  push Not at h

  have hn (n : ℕ) := h (σ := 1 - 1 / (n + 1)) (sub_lt_self _ (by positivity))

  have : ∃ (tn : ℕ → ℝ) (σn : ℕ → ℝ), (∀ n, σn n ≤ 1) ∧
    (∀ n, (1 : ℝ) - 1 / (n + 1) ≤ σn n) ∧ (∀ n, |tn n| ≤ T) ∧
    (∀ n, ζ (σn n + tn n * I) = 0) := by
    choose t ht σ' hσ' hζ using hn
    refine ⟨t, σ', ?_, hσ', ht, hζ⟩
    intro n
    by_contra hσn
    push Not at hσn
    have := riemannZeta_ne_zero_of_one_lt_re (s := σ' n + t n * I)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, ne_eq] at this
    exact this hσn (hζ n)

  choose t σ' hσ'_le hσ'_ge ht hζ using this

  have σTo1 : Filter.Tendsto σ' Filter.atTop (𝓝 1) := by
    have hlow : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (n + 1)) atTop (𝓝 1) := by
      simpa using! (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hσ'_ge hσ'_le

  have : ∃ (t₀ : ℝ) (subseq : ℕ → ℕ),
      Filter.Tendsto (t ∘ subseq) Filter.atTop (𝓝 t₀) ∧
      Filter.Tendsto subseq Filter.atTop Filter.atTop := by
    refine (isCompact_Icc.isSeqCompact fun and => abs_le.1 (ht and)).imp fun and ⟨x, A, B, _⟩ => ?_
    use A, by valid, B.tendsto_atTop

  obtain ⟨t₀, subseq, tTendsto, subseqTendsto⟩ := this

  have σTo1 : Filter.Tendsto (σ' ∘ subseq) Filter.atTop (𝓝 1) :=
    σTo1.comp subseqTendsto

  have (n : ℕ) : ζ (σ' (subseq n) + I * (t (subseq n))) = 0 := by
    convert (preTransparency := .instances) hζ (subseq n) using 3
    ring

  have ToOneT0 : Filter.Tendsto (fun n ↦ (σ' (subseq n) : ℂ) + Complex.I * (t (subseq n))) Filter.atTop
      (𝓝[≠]((1 : ℂ) + I * t₀)) := by
    simp_rw [tendsto_nhdsWithin_iff, Function.comp_def] at tTendsto ⊢
    constructor
    · exact (σTo1.ofReal.add (tTendsto.ofReal.const_mul _)).trans (by simp)
    · filter_upwards with n
      apply ne_of_apply_ne ζ
      rw [this]
      apply Ne.symm
      apply riemannZeta_ne_zero_of_one_le_re
      simp only [add_re, one_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, le_refl]

  by_cases ht₀ : t₀ = 0
  · have ZetaBlowsUp : ∀ᶠ s in 𝓝[≠](1 : ℂ), ‖ζ s‖ ≥ 1 := by
      have hprod : Tendsto (fun s : ℂ => ‖(s - 1) * ζ s‖) (𝓝[≠] 1) (𝓝 1) := by
        simpa only [norm_one] using! riemannZeta_residue_one.norm
      have hid : Tendsto (fun s : ℂ => s) (𝓝[≠] 1) (𝓝 1) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hdist : Tendsto (fun s : ℂ => ‖s - 1‖) (𝓝[≠] 1) (𝓝 0) := by
        simpa only [sub_self, norm_zero] using! (hid.sub_const 1).norm
      filter_upwards [hprod.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1),
        hdist.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with s hp hs
      by_contra h
      have hlt : ‖ζ s‖ < 1 := lt_of_not_ge h
      have hm := mul_le_mul_of_nonneg_left hlt.le (norm_nonneg (s - 1))
      rw [norm_mul] at hp
      rw [mul_one] at hm
      linarith

    have ZetaNonZ : ∀ᶠ s in 𝓝[≠](1 : ℂ), ζ s ≠ 0 := by
      filter_upwards [ZetaBlowsUp]
      intro s hs hfalse
      rw [hfalse] at hs
      simp only [norm_zero, ge_iff_le] at hs
      linarith

    rw [ht₀] at ToOneT0
    simp only [ofReal_zero, mul_zero, add_zero] at ToOneT0
    rcases (ToOneT0.eventually ZetaNonZ).exists with ⟨n, hn⟩
    exact hn (this n)

  · have zetaIsZero : ζ (1 + Complex.I * t₀) = 0 := by
      have hpoint : (1 + Complex.I * t₀ : ℂ) ≠ 1 := by
        intro heq
        have him := congrArg Complex.im heq
        have htzero : t₀ = 0 := by simpa using him
        exact ht₀ htzero
      have hcont := (differentiableAt_riemannZeta hpoint).continuousAt
      have hlim : Tendsto (fun n : ℕ => ζ (σ' (subseq n) + I * t (subseq n))) atTop
          (𝓝 (ζ (1 + I * t₀))) := by
        simpa only [Function.comp_def] using!
          hcont.tendsto.comp (ToOneT0.mono_right nhdsWithin_le_nhds)
      have hfun : (fun n : ℕ => ζ (σ' (subseq n) + I * t (subseq n))) = (fun _ => 0) :=
        funext this
      rw [hfun] at hlim
      exact tendsto_nhds_unique hlim tendsto_const_nhds

    exact riemannZeta_ne_zero_of_one_le_re (s := 1 + I * t₀) (by simp) zetaIsZero



theorem LogDerivZetaHolcLargeT' :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)), ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( (Icc ((1 : ℝ) - A / Real.log T ^ 1) 2)  ×ℂ (Icc (-T) T) ) \ {1}) := by
  obtain ⟨A, A_inter, restOfZetaZeroFree⟩ := ZetaZeroFree_p
  obtain ⟨σ₁, σ₁_lt_one, noZerosInBox⟩ := ZetaNoZerosInBox' 3
  let A₀ := min A ((1 - σ₁) * Real.log 3 ^ 1)
  refine ⟨A₀, ?_, ?_⟩
  · constructor
    · apply lt_min A_inter.1
      bound
    · exact le_trans (min_le_left _ _) A_inter.2
  intro T hT
  apply LogDerivZetaHoloOn
  · exact notMem_sdiff_of_mem rfl
  intro s hs
  rcases le_or_gt 1 s.re with one_le|lt_one
  · exact riemannZeta_ne_zero_of_one_le_re one_le
  rw [← re_add_im s]
  have := Complex.mem_reProdIm.mp hs.1
  rcases lt_or_ge 3 |s.im| with gt3|le3
  · apply restOfZetaZeroFree _ _ gt3
    refine ⟨?_, lt_one⟩
    calc
      _ ≤ 1 - A₀ / Real.log T ^ 1 := by
        gcongr
        · exact A_inter.1.le
        · bound
        · bound
        · bound
        · exact abs_le.mpr ⟨this.2.1, this.2.2⟩
      _ ≤ _:= by exact this.1.1

  · apply noZerosInBox _ le3
    calc
      _ ≥ 1 - A₀ / Real.log T ^ 1 := by exact this.1.1
      _ ≥ 1 - A₀ / Real.log 3 ^ 1 := by
        gcongr
        apply le_min A_inter.1.le
        bound
      _ ≥ 1 - (((1 - σ₁) * Real.log 3 ^ 1)) / Real.log 3 ^ 1:= by
        gcongr
        apply min_le_right
      _ = _ := by field_simp; ring

end Erdos970

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.PNT5_Strong
namespace Erdos970


open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

open _root_.ArithmeticFunction (vonMangoldt)







local notation (name := mellintransform2) "𝓜" => MellinTransform

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

local notation "I" => Complex.I


local notation "ψ" => ChebyshevPsi




open _root_.ComplexConjugate


open _root_.MeasureTheory


attribute [fun_prop] Continuous.const_cpow




























































lemma LogDerivZetaBoundedAndHolo : ∃ A C : ℝ, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧ LogDerivZetaHasBound A C
    ∧ ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (( (Icc ((1 : ℝ) - A / Real.log T ^ 1) 2)  ×ℂ (Icc (-T) T) ) \ {1}) := by

  obtain ⟨A₁, A₁_in, C, C_pos, zeta_bnd2⟩ := LogDerivZetaBndUnif2
  obtain ⟨A₂, A₂_in, holo⟩ := LogDerivZetaHolcLargeT'
  refine ⟨min A₁ A₂, C, C_pos, ?_, ?_, ?_⟩
  · exact ⟨lt_min A₁_in.1 A₂_in.1, le_trans (min_le_left _ _) A₁_in.2⟩
  ·                                                                                  
    intro σ t ht hσ
    have hσ' : σ ∈ Ici (1 - A₁ / Real.log |t| ^ 1) := by

      have hAle : min A₁ A₂ ≤ A₁ := min_le_left _ _
      have hlogpos : 0 < Real.log |t| := by
                               
        exact Real.log_pos (lt_trans (by norm_num) ht)
      have := sub_le_sub_left
        (div_le_div_of_nonneg_right (show min A₁ A₂ ≤ A₁ from hAle) (le_of_lt hlogpos)) 1
                                     
      have hthr : 1 - A₁ / Real.log |t| ^ 1 ≤ 1 - (min A₁ A₂) / Real.log |t| ^ 1 := by
        simpa [pow_one] using this
                                           
      have : σ ∈ Ici (1 - (min A₁ A₂) / Real.log |t| ^ 1) := by
        simpa [pow_one] using hσ
      exact le_trans hthr (mem_Ici.mp this)
                                                                           
    have hmain := zeta_bnd2 σ t ht (by simpa [pow_one] using hσ')
    have hlog_ge_one : (1 : ℝ) ≤ Real.log |t| := by
                                                              
      have hpos : 0 < |t| := lt_trans (by norm_num) ht
      have hle : Real.exp 1 ≤ |t| := by
        have : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
        exact this.trans (le_of_lt ht)
      have := Real.log_le_log (Real.exp_pos 1) hle
      simpa [Real.log_exp] using this
    have hpow : Real.log |t| ^ (2 : ℕ) ≤ Real.log |t| ^ (9 : ℕ) := by
      exact pow_le_pow_right₀ hlog_ge_one (by decide : (2 : ℕ) ≤ 9)
                                   
    have : C * Real.log |t| ^ (2 : ℕ) ≤ C * Real.log |t| ^ (9 : ℕ) :=
      mul_le_mul_of_nonneg_left hpow (le_of_lt C_pos)
    exact (le_trans hmain this)
  ·                                                                    
    intro T hT
                                                                           
    have hsubset :
        ((Icc ((1 : ℝ) - min A₁ A₂ / Real.log T ^ 1) 2) ×ℂ (Icc (-T) T) \ {1}) ⊆
        ((Icc ((1 : ℝ) - A₂ / Real.log T ^ 1) 2) ×ℂ (Icc (-T) T) \ {1}) := by
      intro s hs
      rcases hs with ⟨hs_box, hs_ne⟩
      rcases hs_box with ⟨hre, him⟩
      rcases hre with ⟨hre_left, hre_right⟩
                                     
      constructor
      ·                                                     
        constructor
        ·                                              
          constructor
          ·                                  
            have hAle : min A₁ A₂ ≤ A₂ := min_le_right _ _
            have hlogpos : 0 < Real.log T := by
              have hT' : 1 < T := by linarith
              exact Real.log_pos hT'
            have := sub_le_sub_left
              (div_le_div_of_nonneg_right hAle (le_of_lt hlogpos)) 1
            have hthr : 1 - A₂ / Real.log T ^ 1 ≤ 1 - (min A₁ A₂) / Real.log T ^ 1 := by
              simpa [pow_one] using this
            exact le_trans hthr hre_left
          · exact hre_right
        · exact him
      · exact hs_ne
    exact (holo T hT).mono hsubset


open _root_.Filter _root_.Topology


end Erdos970

end

theorem solution : type_of% @Erdos970.LogDerivZetaBoundedAndHolo := @Erdos970.LogDerivZetaBoundedAndHolo
