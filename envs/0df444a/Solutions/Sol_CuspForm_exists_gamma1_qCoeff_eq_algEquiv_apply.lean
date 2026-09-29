-- Prove2me | solution 1 for CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/0bdf13b2-7579-5cfc-bdd7-2f50312548ff

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even
import Theorems.Thm_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq
import Theorems.Thm_WLight_exists_mdifferentiable_div_of_monicRel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Filter Topology
open scoped MatrixGroups ModularForm Manifold

namespace GammaOneGaloisAllWeights

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section QExp

variable {N : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (N : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ N).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

theorem coe_eq_of_qExpansion_eq [NeZero N] {F G : Type*} [FunLike F ℍ ℂ] [FunLike G ℍ ℂ] {a b : ℤ}
    [ModularFormClass F (Γ₁ℝ N) a] [ModularFormClass G (Γ₁ℝ N) b] (f : F) (g : G)
    (h : qExpansion 1 (⇑f) = qExpansion 1 (⇑g)) : (⇑f : ℍ → ℂ) = ⇑g := by
  funext τ
  have hf := hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods N))
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ
  have hg := hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex g (one_mem_strictPeriods N))
    (ModularFormClass.holo g) (ModularFormClass.bdd_at_infty g) τ
  rw [h] at hf
  exact hf.unique hg

theorem coe_modularForm (f : CuspForm (Γ₁ℝ N) k) :
    (⇑(ModularFormClass.modularForm f : ModularForm (Γ₁ℝ N) k) : ℍ → ℂ) = ⇑f := rfl

theorem coe_mulModularForm {a b : ℤ} (f : CuspForm (Γ₁ℝ N) a) (g : ModularForm (Γ₁ℝ N) b) :
    (⇑(f.mulModularForm g) : ℍ → ℂ) = ⇑f * ⇑g := rfl

theorem qExpansion_mulModularForm {a b : ℤ} (f : CuspForm (Γ₁ℝ N) a) (g : ModularForm (Γ₁ℝ N) b) :
    qExpansion 1 (⇑(f.mulModularForm g)) = qExpansion 1 (⇑f) * qExpansion 1 (⇑g) := by
  rw [coe_mulModularForm]
  exact ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods N) f g

end QExp

section Transport

variable (K : IntermediateField ℚ ℂ) (N : ℕ) (k : ℤ)

abbrev ι : ↥K →+* ℂ := algebraMap ↥K ℂ

def Stab : Prop :=
  ∀ (σ : ↥K ≃ₐ[ℚ] ↥K) (f : CuspForm (Γ₁ℝ N) k) (p : PowerSeries ↥K),
    qExpansion 1 (⇑f) = p.map (ι K) →
      ∃ f' : CuspForm (Γ₁ℝ N) k, qExpansion 1 (⇑f') = (p.map (σ : ↥K →+* ↥K)).map (ι K)

variable {K N k}

theorem stab_of_forall_eq_zero (h : ∀ f : CuspForm (Γ₁ℝ N) k, f = 0) : Stab K N k := by
  intro σ f p hp
  refine ⟨0, ?_⟩
  have hp0 : p = 0 := by
    apply PowerSeries.map_injective (ι K) (algebraMap ↥K ℂ).injective
    rw [← hp, h f, CuspForm.coe_zero, qExpansion_zero, map_zero]
  rw [CuspForm.coe_zero, qExpansion_zero, hp0, map_zero, map_zero]

theorem stab_of_even [NeZero N]
    (hK : K = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (hk : Even k) : Stab K N k := by
  intro σ f p hp
  obtain ⟨f', hf'⟩ := CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply_of_even N k hk K hK σ f
    (fun m => PowerSeries.coeff m p) (fun m => by
      show PowerSeries.coeff m (qExpansion 1 (⇑f)) = _
      rw [hp, PowerSeries.coeff_map]; rfl)
  refine ⟨f', ?_⟩
  ext m
  have := hf' m
  simp only [ModularFormClass.qCoeff] at this
  rw [this, PowerSeries.coeff_map, PowerSeries.coeff_map, RingHom.coe_coe]
  rfl

end Transport

theorem eq_zero_of_mul_eq_zero {u v : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) v) (huv : ∀ τ : ℍ, u τ * v τ = 0) {τ₀ : ℍ} (hv0 : v τ₀ ≠ 0) :
    u = 0 := by
  have hvc : ContinuousAt (v ∘ ofComplex) (τ₀ : ℂ) :=
    (UpperHalfPlane.mdifferentiableAt_iff.1 (hv τ₀)).continuousAt
  have hv0' : (v ∘ ofComplex) (τ₀ : ℂ) ≠ 0 := by simpa [Function.comp, ofComplex_apply] using hv0
  have hne : ∀ᶠ z in 𝓝 (τ₀ : ℂ), (v ∘ ofComplex) z ≠ 0 := hvc.eventually_ne hv0'
  have hu0 : (u ∘ ofComplex) =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    filter_upwards [hne] with z hz
    have := huv (ofComplex z)
    simp only [Function.comp_apply, Pi.zero_apply] at hz ⊢
    exact (mul_eq_zero.1 this).resolve_right hz
  have hana : AnalyticOnNhd ℂ (u ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.1 hu).analyticOnNhd isOpen_upperHalfPlaneSet
  have hEq := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ₀.im_pos hu0
  funext τ
  have := hEq τ.im_pos
  simpa [Function.comp, ofComplex_apply] using this

theorem isZeroAtImInfty_of_mul_self {g : ℍ → ℂ} (h : IsZeroAtImInfty (g * g)) :
    IsZeroAtImInfty g := by
  rw [UpperHalfPlane.IsZeroAtImInfty, Filter.ZeroAtFilter] at h ⊢
  have h₁ : Tendsto (fun τ => ‖g τ‖ * ‖g τ‖) atImInfty (𝓝 0) := by
    have := tendsto_zero_iff_norm_tendsto_zero.mp h
    simpa [norm_mul] using this
  have h₂ : Tendsto (fun τ => Real.sqrt (‖g τ‖ * ‖g τ‖)) atImInfty (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h₁
    simpa [Function.comp_def] using this
  refine tendsto_zero_iff_norm_tendsto_zero.mpr (h₂.congr fun τ => ?_)
  exact Real.sqrt_mul_self (norm_nonneg _)

section OddStep

variable (K : IntermediateField ℚ ℂ) {N : ℕ} {k : ℤ} [NeZero N]

theorem stab_of_anchor {w : ℤ} (E : ModularForm (Γ₁ℝ N) w) (hE : E ≠ 0)
    (e : PowerSeries ℤ) (hEe : ModularCurve.IsIntegralQExp (⇑E) e)
    (h1 : Stab K N (k + w)) (h2 : Stab K N (k + k)) : Stab K N k := by
  classical
  intro σ f p hp

  set eK : PowerSeries ↥K := e.map (Int.castRingHom ↥K) with heK
  have hEe' : e.map (Int.castRingHom ℂ) = qExpansion 1 (⇑E) := hEe
  have heKι : eK.map (ι K) = qExpansion 1 (⇑E) := by
    rw [← hEe']
    ext n
    simp [heK, PowerSeries.coeff_map]
  have heKσ : eK.map (σ : ↥K →+* ↥K) = eK := by
    ext n
    simp [heK, PowerSeries.coeff_map]
  set φh : PowerSeries ℂ := (p.map (σ : ↥K →+* ↥K)).map (ι K) with hφh

  have hfE : qExpansion 1 (⇑(f.mulModularForm E)) = (p * eK).map (ι K) := by
    rw [qExpansion_mulModularForm, map_mul, hp, heKι]
  have hff : qExpansion 1 (⇑(f.mulModularForm (ModularFormClass.modularForm f))) =
      (p * p).map (ι K) := by
    rw [qExpansion_mulModularForm, coe_modularForm, map_mul, hp]
  obtain ⟨G, hG⟩ := h1 σ (f.mulModularForm E) (p * eK) hfE
  obtain ⟨H, hH⟩ := h2 σ (f.mulModularForm (ModularFormClass.modularForm f)) (p * p) hff
  have hQE : qExpansion 1 (⇑E) ≠ 0 := fun h =>
    hE ((ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods N) E).mp h)
  have hG' : qExpansion 1 (⇑G) = φh * qExpansion 1 (⇑E) := by
    rw [hG, map_mul, map_mul, heKσ, heKι]
  have hH' : qExpansion 1 (⇑H) = φh * φh := by
    rw [hH, map_mul, map_mul]

  have hval : ∀ τ : ℍ, G τ * G τ = H τ * E τ * E τ := by
    have hq : qExpansion 1 (⇑(G.mulModularForm (ModularFormClass.modularForm G))) =
        qExpansion 1 (⇑((H.mulModularForm E).mulModularForm E)) := by
      rw [qExpansion_mulModularForm, qExpansion_mulModularForm, qExpansion_mulModularForm,
        coe_modularForm, hG', hH']
      ring
    have hfun := coe_eq_of_qExpansion_eq _ _ hq
    intro τ
    have hτ := congrFun hfun τ
    simpa [coe_mulModularForm, coe_modularForm, mul_assoc] using hτ

  have hEfun : (⇑E : ℍ → ℂ) ≠ 0 := by
    intro h0
    exact hE ((ModularForm.coe_eq_zero_iff E).mp h0)
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : ℍ, E τ₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hEfun (funext hcon)
  have hEhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑E) := ModularFormClass.holo E
  have hGhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑G) := ModularFormClass.holo G
  have hHhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑H) := ModularFormClass.holo H
  let cc : ℕ → ℍ → ℂ := fun i => if i = 0 then -⇑H else 0
  have hcc : ∀ i < 2, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (cc i) := by
    intro i _
    by_cases hi : i = 0
    · simpa [cc, hi] using hHhol.neg
    · have h__af := (mdifferentiable_const : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun _ : ℍ => (0 : ℂ))
      simp [cc, hi] at h__af ⊢
      exact h__af
  have hrel : (⇑G) ^ 2 + ∑ i ∈ Finset.range 2, cc i * (⇑E) ^ (2 - i) * (⇑G) ^ i = 0 := by
    funext τ
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
      Pi.zero_apply, cc, if_true, show (1 : ℕ) ≠ 0 from one_ne_zero, if_false, Pi.neg_apply]
    rw [pow_two, hval τ]; ring
  obtain ⟨φ, hφhol, hφE⟩ := WLight.exists_mdifferentiable_div_of_monicRel hGhol hEhol hEfun hcc hrel
  have hφE' : ∀ τ : ℍ, φ τ * E τ = G τ := fun τ => congrFun hφE τ

  have hφsq : ∀ τ : ℍ, φ τ * φ τ = H τ := by
    have hzero : ∀ τ : ℍ, (φ τ * φ τ - H τ) * (E τ * E τ) = 0 := by
      intro τ
      have h := hval τ
      rw [← hφE' τ] at h
      linear_combination h
    have hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => φ τ * φ τ - H τ) := (hφhol.mul hφhol).sub hHhol
    have hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => E τ * E τ) := hEhol.mul hEhol
    have := eq_zero_of_mul_eq_zero hdiff hv hzero (τ₀ := τ₀) (mul_ne_zero hτ₀ hτ₀)
    intro τ
    exact sub_eq_zero.mp (congrFun this τ)

  have hinv : ∀ γ ∈ Gamma1 N, φ ∣[k] γ = φ := by
    intro γ hγ
    have hGγ : (⇑G : ℍ → ℂ) ∣[k + w] γ = ⇑G := by
      have := SlashInvariantForm.slash_action_eqn G (γ : GL (Fin 2) ℝ) (Subgroup.mem_map_of_mem _ hγ)
      simpa [ModularForm.SL_slash] using this
    have hEγ : (⇑E : ℍ → ℂ) ∣[w] γ = ⇑E := by
      have := SlashInvariantForm.slash_action_eqn E (γ : GL (Fin 2) ℝ) (Subgroup.mem_map_of_mem _ hγ)
      simpa [ModularForm.SL_slash] using this
    have hprod : (φ ∣[k] γ) * ⇑E = φ * ⇑E := by
      have h := ModularForm.mul_slash_SL2 k w γ φ ⇑E
      rw [hEγ, hφE, hGγ] at h
      rw [hφE]; exact h.symm
    have hzero : ∀ τ : ℍ, ((φ ∣[k] γ) τ - φ τ) * E τ = 0 := by
      intro τ
      have := congrFun hprod τ
      simp only [Pi.mul_apply] at this
      linear_combination this
    have hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => (φ ∣[k] γ) τ - φ τ) := by
      have h₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (φ ∣[k] γ) := by
        rw [ModularForm.SL_slash]; exact hφhol.slash k _
      exact h₁.sub hφhol
    have := eq_zero_of_mul_eq_zero hdiff hEhol hzero hτ₀
    funext τ
    exact sub_eq_zero.mp (by simpa using congrFun this τ)

  have hcusp : ∀ A : SL(2, ℤ), IsZeroAtImInfty (φ ∣[k] A) := by
    intro A
    apply isZeroAtImInfty_of_mul_self
    have hφφ : φ * φ = ⇑H := funext fun τ => hφsq τ
    have h := ModularForm.mul_slash_SL2 k k A φ φ
    rw [hφφ] at h
    rw [← h]
    exact CuspFormClass.zero_at_infty_slash H A

  let φC : CuspForm (Γ₁ℝ N) k :=
    { toFun := φ
      slash_action_eq' := by
        rintro _ ⟨γ, hγ, rfl⟩
        have := hinv γ hγ
        rwa [ModularForm.SL_slash] at this
      holo' := hφhol
      zero_at_cusps' := fun {c} hc =>
        (OnePoint.isZeroAt_iff_forall_SL2Z
          ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)).mpr fun A _ => hcusp A }
  refine ⟨φC, ?_⟩
  have hprod : qExpansion 1 (⇑φC) * qExpansion 1 (⇑E) = φh * qExpansion 1 (⇑E) := by
    rw [← hG', ← qExpansion_mulModularForm, coe_mulModularForm]
    exact congrArg (qExpansion 1) hφE
  exact mul_right_cancel₀ hQE hprod

end OddStep

section Assembly

variable (N : ℕ)

def kN : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))}

theorem anchor [NeZero N] (h10 : (1 : ZMod N) ≠ 0) (h11 : (1 : ZMod N) ≠ -1) :
    ∃ (E : ModularForm (Γ₁ℝ N) ((3 : ℕ) : ℤ)) (e : PowerSeries ℤ), E ≠ 0 ∧
      ModularCurve.IsIntegralQExp (⇑E) e := by
  classical
  obtain ⟨G, hG, -⟩ := ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq N 3 le_rfl
  have hint := hG 1 h10
  refine ⟨G 1, _, ?_, hint⟩
  rw [ModularCurve.IsIntegralQExp] at hint
  intro h0
  have h1 := congrArg (PowerSeries.coeff 1) hint
  rw [h0, ModularForm.coe_zero, qExpansion_zero, map_zero, PowerSeries.coeff_map,
    PowerSeries.coeff_mk] at h1
  simp [Nat.divisors_one, Finset.filter_singleton, h11] at h1

theorem neg_one_mem_Gamma1 (hN : N ∣ 2) : (-1 : SL(2, ℤ)) ∈ Gamma1 N := by
  rw [Gamma1_mem]
  have h2 : ((2 : ℕ) : ZMod N) = 0 := (ZMod.natCast_eq_zero_iff 2 N).mpr hN
  have hneg : ((-1 : ℤ) : ZMod N) = 1 := by
    have h11 : (1 : ZMod N) + 1 = 0 := by simpa [one_add_one_eq_two] using h2
    push_cast
    linear_combination -h11
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Matrix.SpecialLinearGroup.coe_neg, hneg]

theorem neg_one_mem_Gamma1GL (hN : N ∣ 2) : (-1 : GL (Fin 2) ℝ) ∈ Γ₁ℝ N := by
  refine Subgroup.mem_map.mpr ⟨-1, neg_one_mem_Gamma1 N hN, ?_⟩
  ext i j
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  fin_cases i <;> fin_cases j <;> simp [Units.val_neg]

theorem stab_all [NeZero N] (k : ℤ) : Stab (kN N) N k := by
  rcases Int.even_or_odd k with hk | hk
  · exact stab_of_even rfl hk
  by_cases hN : N ∣ 2
  ·
    refine stab_of_forall_eq_zero fun f => ?_
    have h := ModularForm.eq_zero_of_neg_one_mem (neg_one_mem_Gamma1GL N hN) hk
      (ModularFormClass.modularForm f)
    have hcoe : (⇑f : ℍ → ℂ) = 0 := by
      rw [← coe_modularForm f, h, ModularForm.coe_zero]
    exact DFunLike.ext' (by rw [hcoe, CuspForm.coe_zero])
  ·
    have h10 : (1 : ZMod N) ≠ 0 := by
      intro h
      have hN1 : N ∣ 1 := (ZMod.natCast_eq_zero_iff 1 N).mp (by simpa using h)
      exact hN ((Nat.dvd_one.mp hN1).symm ▸ one_dvd 2)
    have h11 : (1 : ZMod N) ≠ -1 := by
      intro h
      have h2 : ((2 : ℕ) : ZMod N) = 0 := by
        rw [Nat.cast_two, ← one_add_one_eq_two]
        nth_rewrite 2 [h]
        exact add_neg_cancel 1
      exact hN ((ZMod.natCast_eq_zero_iff 2 N).mp h2)
    obtain ⟨E, e, hE0, hEe⟩ := anchor N h10 h11
    have hk3 : Even (k + ((3 : ℕ) : ℤ)) := by
      push_cast
      exact hk.add_odd ⟨1, by norm_num⟩
    exact stab_of_anchor (kN N) E hE0 e hEe (stab_of_even rfl hk3) (stab_of_even rfl ⟨k, rfl⟩)

theorem main [NeZero N] (k : ℤ) (σ : ↥(kN N) ≃ₐ[ℚ] ↥(kN N)) (f : CuspForm (Γ₁ℝ N) k)
    (c : ℕ → ↥(kN N)) (hf : ∀ m : ℕ, ModularFormClass.qCoeff f m = (c m : ℂ)) :
    ∃ f' : CuspForm (Γ₁ℝ N) k, ∀ m : ℕ, ModularFormClass.qCoeff f' m = (σ (c m) : ℂ) := by
  have hp : qExpansion 1 (⇑f) = (PowerSeries.mk c).map (ι (kN N)) := by
    ext m
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact hf m
  obtain ⟨f', hf'⟩ := stab_all N k σ f (PowerSeries.mk c) hp
  refine ⟨f', fun m => ?_⟩
  show PowerSeries.coeff m (qExpansion 1 (⇑f')) = _
  rw [hf', PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_mk, RingHom.coe_coe]
  rfl

end Assembly

end GammaOneGaloisAllWeights

end

theorem solution (N : ℕ) [NeZero N] (k : ℤ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (σ : ↥K ≃ₐ[ℚ] ↥K) (f : CuspForm (CongruenceSubgroup.Gamma1 N) k) (c : ℕ → ↥K)
    (hf : ∀ m : ℕ, ModularFormClass.qCoeff f m = (c m : ℂ)) :
    ∃ f' : CuspForm (CongruenceSubgroup.Gamma1 N) k,
      ∀ m : ℕ, ModularFormClass.qCoeff f' m = (σ (c m) : ℂ) := by
  subst hK
  exact GammaOneGaloisAllWeights.main N k σ f c hf

end S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply
end P2MW
export P2MW.S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply (solution)
