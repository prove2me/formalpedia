-- Prove2me | solution 1 for CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1d052b3a-6ecb-520a-9062-3104d0d24533

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even
import Theorems.Thm_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq
import Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic
import Theorems.Thm_WLight_exists_mdifferentiable_div_of_monicRel
import Theorems.Thm_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Filter Topology
open scoped MatrixGroups ModularForm Manifold

namespace GammaOneCyclotomic

section FieldFacts

variable (K : IntermediateField ℚ ℂ)

theorem mem_of_forall_algEquiv_apply_eq (x : ℂ) (hx : ∀ σ : ℂ ≃ₐ[K] ℂ, σ x = x) : x ∈ K := by
  by_contra hxK
  have hx' : x ∉ Set.range (algebraMap K ℂ) := by
    rintro ⟨y, rfl⟩
    exact hxK y.2
  obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_algEquiv_apply_ne_of_notMem_range hx'
  exact hσ (hx σ)

theorem algEquiv_apply_of_mem (σ : ℂ ≃ₐ[K] ℂ) {x : ℂ} (hx : x ∈ K) : σ x = x :=
  σ.commutes ⟨x, hx⟩

end FieldFacts

section Descent

variable (K : IntermediateField ℚ ℂ) {V : Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] {ι : Type*} (c : ι → V →ₗ[ℂ] ℂ)

theorem span_range_eq_top (hc : ∀ v : V, (∀ i, c i v = 0) → v = 0) :
    Submodule.span ℂ (Set.range c) = ⊤ := by
  set W : Submodule ℂ (Module.Dual ℂ V) := Submodule.span ℂ (Set.range c) with hWdef
  have hW : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    rw [Submodule.mem_bot]
    exact hc v fun i => hv (c i) (Submodule.subset_span ⟨i, rfl⟩)
  have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)
  rw [hW, Submodule.dualAnnihilator_bot] at h
  exact h.symm

theorem exists_basis_of_stable (hc : ∀ v : V, (∀ i, c i v = 0) → v = 0)
    (hstab : ∀ (σ : ℂ ≃ₐ[K] ℂ) (v : V), ∃ w : V, ∀ i, c i w = σ (c i v)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ V), ∀ (j : Fin n) (i : ι), c i (b j) ∈ K := by
  classical
  obtain ⟨t, ht_sub, ht_span, ht_ind⟩ := exists_linearIndependent ℂ (Set.range c)
  have ht_fin : t.Finite := LinearIndependent.set_finite_of_isNoetherian ht_ind
  letI : Fintype t := ht_fin.fintype
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : t → Module.Dual ℂ V)) := by
    rw [Subtype.range_coe, ht_span, span_range_eq_top c hc]
  let β : Module.Basis t ℂ (Module.Dual ℂ V) := Module.Basis.mk ht_ind htop

  let T : V →ₗ[ℂ] (t → ℂ) := LinearMap.pi fun i : t => (i : Module.Dual ℂ V)
  have hT_apply : ∀ (v : V) (i : t), T v i = (i : Module.Dual ℂ V) v := fun v i => rfl
  have hT_inj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply hc v
    intro i
    have hmem : c i ∈ Submodule.span ℂ t := by
      rw [ht_span]; exact Submodule.subset_span ⟨i, rfl⟩
    refine Submodule.span_induction (p := fun φ _ => φ v = 0) ?_ ?_ ?_ ?_ hmem
    · intro φ hφ
      have := congrFun hv ⟨φ, hφ⟩
      simpa [hT_apply] using this
    · simp
    · intro φ ψ _ _ h₁ h₂
      simp [h₁, h₂]
    · intro a φ _ h
      simp [h]
  have hdim : Module.finrank ℂ V = Module.finrank ℂ (t → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card, ← Subspace.dual_finrank_eq,
      Module.finrank_eq_card_basis β]
  let e : V ≃ₗ[ℂ] (t → ℂ) := T.linearEquivOfInjective hT_inj hdim
  have he_apply : ∀ (v : V) (i : t), e v i = (i : Module.Dual ℂ V) v := fun v i => rfl
  let b₀ : Module.Basis t ℂ V := (Pi.basisFun ℂ t).map e.symm
  have hb₀ : ∀ j i : t, (i : Module.Dual ℂ V) (b₀ j) = if i = j then 1 else 0 := by
    intro j i
    rw [← he_apply]
    simp [b₀, Pi.single_apply]

  have hfix : ∀ (σ : ℂ ≃ₐ[K] ℂ) (j : t) (i : ι), σ (c i (b₀ j)) = c i (b₀ j) := by
    intro σ j
    obtain ⟨w, hw⟩ := hstab σ (b₀ j)
    have hew : e w = e (b₀ j) := by
      funext i
      obtain ⟨i₀, hi₀⟩ := ht_sub i.2
      have h₁ := hb₀ j i
      rw [← hi₀] at h₁
      rw [he_apply, he_apply, ← hi₀, hw i₀, h₁]
      split_ifs <;> simp
    have hwj : w = b₀ j := e.injective hew
    intro i
    rw [← hw i, hwj]
  refine ⟨Fintype.card t, b₀.reindex (Fintype.equivFin t), fun j i => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact mem_of_forall_algEquiv_apply_eq K _ fun σ => hfix σ _ i

end Descent

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

theorem eq_of_qExpansion_eq [NeZero N] (f g : CuspForm (Γ₁ℝ N) k)
    (h : qExpansion 1 (⇑f) = qExpansion 1 (⇑g)) : f = g :=
  DFunLike.ext' (coe_eq_of_qExpansion_eq f g h)

variable (N k) in

def qExpLin : CuspForm (Γ₁ℝ N) k →ₗ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion 1 (⇑f)
  map_add' f g := by
    rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N) f g]
  map_smul' a f := by
    rw [CuspForm.IsGLPos.coe_smul,
      ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N) a f, RingHom.id_apply]

@[scoped simp] theorem qExpLin_apply (f : CuspForm (Γ₁ℝ N) k) : qExpLin N k f = qExpansion 1 (⇑f) := rfl

theorem coe_modularForm (f : CuspForm (Γ₁ℝ N) k) :
    (⇑(ModularFormClass.modularForm f : ModularForm (Γ₁ℝ N) k) : ℍ → ℂ) = ⇑f := rfl

theorem coe_mulModularForm {a b : ℤ} (f : CuspForm (Γ₁ℝ N) a) (g : ModularForm (Γ₁ℝ N) b) :
    (⇑(f.mulModularForm g) : ℍ → ℂ) = ⇑f * ⇑g := rfl

theorem qExpansion_mulModularForm {a b : ℤ} (f : CuspForm (Γ₁ℝ N) a) (g : ModularForm (Γ₁ℝ N) b) :
    qExpansion 1 (⇑(f.mulModularForm g)) = qExpansion 1 (⇑f) * qExpansion 1 (⇑g) := by
  rw [coe_mulModularForm]
  exact ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods N) f g

end QExp

def Stab (K : IntermediateField ℚ ℂ) (N : ℕ) (k : ℤ) : Prop :=
  ∀ (σ : ℂ ≃ₐ[K] ℂ) (f : CuspForm (Γ₁ℝ N) k),
    ∃ f' : CuspForm (Γ₁ℝ N) k, qExpansion 1 (⇑f') = (qExpansion 1 (⇑f)).map (σ : ℂ →+* ℂ)

section Stability

variable (K : IntermediateField ℚ ℂ) {N : ℕ} {k : ℤ}

theorem stab_of_basis {n : ℕ} (b : Module.Basis (Fin n) ℂ (CuspForm (Γ₁ℝ N) k))
    (hb : ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ K) : Stab K N k := by
  intro σ f
  set r : Fin n → ℂ := fun i => b.repr f i with hr
  have hf : f = ∑ i, r i • b i := by simp [hr]
  refine ⟨∑ i, σ (r i) • b i, ?_⟩
  have key : ∀ s : Fin n → ℂ,
      qExpansion 1 (⇑(∑ i, s i • b i)) = ∑ i, s i • qExpansion 1 (⇑(b i)) := by
    intro s
    change qExpLin N k (∑ i, s i • b i) = ∑ i, s i • qExpLin N k (b i)
    simp [map_sum, map_smul]
  conv_rhs => rw [hf]
  rw [key, key]
  ext m
  simp only [map_sum, map_smul, smul_eq_mul, PowerSeries.coeff_map, RingHom.coe_coe, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact (algEquiv_apply_of_mem K σ (hb i m)).symm

theorem stab_of_forall_eq_zero (h : ∀ f : CuspForm (Γ₁ℝ N) k, f = 0) : Stab K N k := by
  intro σ f
  refine ⟨0, ?_⟩
  rw [h f, CuspForm.coe_zero, qExpansion_zero, map_zero]

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

variable [NeZero N]

theorem stab_of_anchor {w : ℤ} (E : ModularForm (Γ₁ℝ N) w) (hE : E ≠ 0)
    (hEK : ∀ σ : ℂ ≃ₐ[K] ℂ, (qExpansion 1 (⇑E)).map (σ : ℂ →+* ℂ) = qExpansion 1 (⇑E))
    (h1 : Stab K N (k + w)) (h2 : Stab K N (k + k)) : Stab K N k := by
  classical
  intro σ f
  set φh : PowerSeries ℂ := (qExpansion 1 (⇑f)).map (σ : ℂ →+* ℂ) with hφh

  obtain ⟨G, hG⟩ := h1 σ (f.mulModularForm E)
  obtain ⟨H, hH⟩ := h2 σ (f.mulModularForm (ModularFormClass.modularForm f))
  have hQE : qExpansion 1 (⇑E) ≠ 0 := fun h =>
    hE ((ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods N) E).mp h)
  have hG' : qExpansion 1 (⇑G) = φh * qExpansion 1 (⇑E) := by
    rw [hG, qExpansion_mulModularForm, map_mul, hEK]
  have hH' : qExpansion 1 (⇑H) = φh * φh := by
    rw [hH, qExpansion_mulModularForm, coe_modularForm, map_mul]

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

theorem exists_basis_of_stab (h : Stab K N k) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (Γ₁ℝ N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ K := by
  haveI : FiniteDimensional ℂ (CuspForm (Γ₁ℝ N) k) := CuspForm.finiteDimensional_of_isArithmetic _ k
  let c : ℕ → CuspForm (Γ₁ℝ N) k →ₗ[ℂ] ℂ := fun m => (PowerSeries.coeff m).comp (qExpLin N k)
  have hc_apply : ∀ (m : ℕ) (f : CuspForm (Γ₁ℝ N) k),
      c m f = PowerSeries.coeff m (qExpansion 1 (⇑f)) := fun m f => rfl
  have hc : ∀ f : CuspForm (Γ₁ℝ N) k, (∀ m, c m f = 0) → f = 0 := by
    intro f hf
    refine eq_of_qExpansion_eq f 0 ?_
    ext m
    rw [CuspForm.coe_zero, qExpansion_zero, map_zero, ← hc_apply, hf m]
  have hstab : ∀ (σ : ℂ ≃ₐ[K] ℂ) (f : CuspForm (Γ₁ℝ N) k),
      ∃ f' : CuspForm (Γ₁ℝ N) k, ∀ m, c m f' = σ (c m f) := by
    intro σ f
    obtain ⟨f', hf'⟩ := h σ f
    refine ⟨f', fun m => ?_⟩
    rw [hc_apply, hc_apply, hf', PowerSeries.coeff_map, RingHom.coe_coe]
  obtain ⟨n, b, hb⟩ := exists_basis_of_stable K c hc hstab
  exact ⟨n, b, fun i m => hb i m⟩

end Stability

section Assembly

variable (N : ℕ)

def kN : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))}

theorem anchor [NeZero N] (h10 : (1 : ZMod N) ≠ 0) (h11 : (1 : ZMod N) ≠ -1) :
    ∃ E : ModularForm (Γ₁ℝ N) ((3 : ℕ) : ℤ), E ≠ 0 ∧
      ∀ σ' : ℂ →+* ℂ, (qExpansion 1 (⇑E)).map σ' = qExpansion 1 (⇑E) := by
  classical
  obtain ⟨G, hG, -⟩ := ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq N 3 le_rfl
  have hint := hG 1 h10
  rw [ModularCurve.IsIntegralQExp] at hint
  refine ⟨G 1, ?_, fun σ' => ?_⟩
  · intro h0
    have h1 := congrArg (PowerSeries.coeff 1) hint
    rw [h0, ModularForm.coe_zero, qExpansion_zero, map_zero, PowerSeries.coeff_map,
      PowerSeries.coeff_mk] at h1
    simp [Nat.divisors_one, Finset.filter_singleton, h11] at h1
  · rw [← hint]
    ext n
    simp only [PowerSeries.coeff_map]
    exact (RingHom.congr_fun (RingHom.ext_int (σ'.comp (Int.castRingHom ℂ)) (Int.castRingHom ℂ)) _)

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

theorem main [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (Γ₁ℝ N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ kN N := by
  rcases Int.even_or_odd k with hk | hk
  · exact CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even N k hk
  by_cases hN : N ∣ 2
  ·
    refine exists_basis_of_stab (kN N) (stab_of_forall_eq_zero (kN N) fun f => ?_)
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
    obtain ⟨E, hE0, hEfix⟩ := anchor N h10 h11
    have heven : ∀ k' : ℤ, Even k' → Stab (kN N) N k' := fun k' hk' => by
      obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even N k' hk'
      exact stab_of_basis (kN N) b hb
    have hk3 : Even (k + ((3 : ℕ) : ℤ)) := by
      push_cast
      exact hk.add_odd ⟨1, by norm_num⟩
    have hs : Stab (kN N) N k :=
      stab_of_anchor (kN N) E hE0 (fun σ => hEfix _) (heven _ hk3) (heven _ ⟨k, rfl⟩)
    exact exists_basis_of_stab (kN N) hs

end Assembly

end GammaOneCyclotomic
p2m_reactivate "P2MW.S_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp.GammaOneCyclotomic"

end
p2m_reactivate "P2MW.S_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp.GammaOneCyclotomic"

theorem solution (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma1 N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈
        IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} :=
  GammaOneCyclotomic.main N k

end S_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp
end P2MW
export P2MW.S_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp (solution)
