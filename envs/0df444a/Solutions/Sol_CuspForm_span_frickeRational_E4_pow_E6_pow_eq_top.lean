-- Prove2me | solution 1 for CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/d8651d83-d1bb-5311-9f86-0dbdb272f647

import Mathlib
import Theorems.Thm_WLight_frickeFunction_modularity_package
import Theorems.Thm_WLight_levelN_structure_package
import Theorems.Thm_WLight_exists_levelFraction_of_stable_family
import Theorems.Thm_WLight_exists_monicRel_j_of_mdifferentiable_levelFraction
import Theorems.Thm_WLight_frickeFunction_intBaseChange
import Theorems.Thm_WLight_exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction
import Theorems.Thm_WLight_exists_monicRel_j_K_of_mdifferentiable_frickeQuotient
import Theorems.Thm_WLight_linearIndependent_complex_of_qExpansion_rational
import Theorems.Thm_WLight_exists_twist_of_flat
import Theorems.Thm_WLight_span_inter_rational_of_twist_stable
import Theorems.Thm_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range
import Theorems.Thm_WLight_isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le
import Theorems.Thm_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Complex UpperHalfPlane ModularForm Function Filter
open scoped Real Manifold MatrixGroups ModularForm Topology

namespace FrickeSpan

local notation "Δ" => ModularForm.discriminant

section Analytic

theorem differentiableAt_comp_ofComplex {u : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (τ : ℍ) :
    DifferentiableAt ℂ (u ∘ ofComplex) (τ : ℂ) :=
  UpperHalfPlane.mdifferentiableAt_iff.1 (hu τ)

theorem eq_zero_of_mul_eq_zero {u v : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) v) (huv : ∀ τ : ℍ, u τ * v τ = 0) {τ₀ : ℍ} (hv0 : v τ₀ ≠ 0) :
    u = 0 := by
  have hvc : ContinuousAt (v ∘ ofComplex) (τ₀ : ℂ) := (differentiableAt_comp_ofComplex hv τ₀).continuousAt
  have hv0' : (v ∘ ofComplex) (τ₀ : ℂ) ≠ 0 := by simpa [Function.comp, ofComplex_apply] using hv0
  have hu0 : (u ∘ ofComplex) =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    filter_upwards [hvc.eventually_ne hv0'] with z hz
    have := huv (ofComplex z)
    simp only [Function.comp_apply, Pi.zero_apply] at hz ⊢
    exact (mul_eq_zero.1 this).resolve_right hz
  have hEq := ((UpperHalfPlane.mdifferentiable_iff.1 hu).analyticOnNhd
    isOpen_upperHalfPlaneSet).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ₀.im_pos hu0
  funext τ
  simpa [Function.comp, ofComplex_apply] using hEq τ.im_pos

theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := CuspForm.discriminant.holo'

theorem disc_ne_zero (τ : ℍ) : Δ τ ≠ 0 := discriminant_ne_zero τ

theorem periodic_disc_one : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL

theorem isBoundedAtImInfty_disc : IsBoundedAtImInfty (Δ : ℍ → ℂ) :=
  ModularFormClass.bdd_at_infty CuspForm.discriminant

theorem periodic_ofComplex_natCast {g : ℍ → ℂ} (h : Periodic (g ∘ ofComplex) 1) (n : ℕ) :
    Periodic (g ∘ ofComplex) n := by
  simpa using h.nat_mul n

theorem periodic_mul {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g * g') ∘ ofComplex) c := by
  intro z; have h1 := h z; have h2 := h' z
  simp only [comp_apply, Pi.mul_apply] at h1 h2 ⊢; rw [h1, h2]

theorem periodic_add {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g + g') ∘ ofComplex) c := by
  intro z; have h1 := h z; have h2 := h' z
  simp only [comp_apply, Pi.add_apply] at h1 h2 ⊢; rw [h1, h2]

theorem periodic_smul {g : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c) (a : ℂ) :
    Periodic ((a • g) ∘ ofComplex) c := by
  intro z; have h1 := h z; simp only [comp_apply, Pi.smul_apply] at h1 ⊢; rw [h1]

theorem mdifferentiable_inv {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (h0 : ∀ τ : ℍ, g τ ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => (g τ)⁻¹) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h1 := UpperHalfPlane.mdifferentiable_iff.1 hg
  exact (h1.inv fun z _ => h0 _).congr fun z _ => by simp [comp_apply]

theorem mdifferentiable_div_disc_pow {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (r : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => g τ / Δ τ ^ r) := by
  have := hg.mul (mdifferentiable_inv (mdifferentiable_disc.pow r) fun τ => pow_ne_zero _ (disc_ne_zero τ))
  first
    | simpa [div_eq_mul_inv] using this
    | (simpa [div_eq_mul_inv] using (this :))
    | (simpa [Function.comp_def] using this)
    | exact this
    | (have h__ := this; (try simp [div_eq_mul_inv] at h__); (try simp [div_eq_mul_inv]); exact h__)

end Analytic

section Params

variable {N : ℕ} [NeZero N]
variable (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})

abbrev Idx (N : ℕ) : Type := Option {v : Fin 2 → ZMod N // v ≠ 0}

def gen : Idx N → ℍ → ℂ := fun o => o.elim jf fun v => fricke v.1

def genSet : Set (ℍ → ℂ) := insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}

def evK (R : MvPolynomial (Idx N) K) : ℍ → ℂ :=
  MvPolynomial.aeval (gen fricke jf) (MvPolynomial.map (algebraMap K ℂ) R)

theorem evK_def (R : MvPolynomial (Idx N) K) :
    evK fricke jf K R = MvPolynomial.aeval (gen fricke jf) (MvPolynomial.map (algebraMap K ℂ) R) := rfl

theorem evK_add (R S : MvPolynomial (Idx N) K) : evK fricke jf K (R + S) = evK fricke jf K R + evK fricke jf K S := by
  simp [evK]

theorem evK_mul (R S : MvPolynomial (Idx N) K) : evK fricke jf K (R * S) = evK fricke jf K R * evK fricke jf K S := by
  simp [evK]

theorem evK_C (c : K) : evK fricke jf K (MvPolynomial.C c) = fun _ => (c : ℂ) := by
  funext τ
  simp only [evK, MvPolynomial.map_C, MvPolynomial.aeval_C, Pi.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  rfl

theorem evK_one : evK fricke jf K 1 = 1 := by simp [evK]

theorem evK_zero : evK fricke jf K 0 = 0 := by simp [evK]

theorem evK_X (o : Idx N) : evK fricke jf K (MvPolynomial.X o) = gen fricke jf o := by
  simp [evK, MvPolynomial.map_X]

def redN (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) (ZMod N) :=
  (γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N)

def vm (γ : SL(2, ℤ)) (v : Fin 2 → ZMod N) : Fin 2 → ZMod N := Matrix.vecMul v (redN γ)

theorem redN_eq (γ : SL(2, ℤ)) :
    redN (N := N) γ = (Int.castRingHom (ZMod N)).mapMatrix (γ : Matrix (Fin 2) (Fin 2) ℤ) := rfl

theorem redN_mul (γ γ' : SL(2, ℤ)) : redN (N := N) (γ * γ') = redN γ * redN γ' := by
  rw [redN_eq, redN_eq, redN_eq, Matrix.SpecialLinearGroup.coe_mul, map_mul]

theorem redN_one : redN (N := N) 1 = 1 := by
  rw [redN, Matrix.SpecialLinearGroup.coe_one]; simp

theorem vm_mul (γ γ' : SL(2, ℤ)) (v : Fin 2 → ZMod N) : vm (γ * γ') v = vm γ' (vm γ v) := by
  simp only [vm, redN_mul, Matrix.vecMul_vecMul]

theorem vm_one (v : Fin 2 → ZMod N) : vm (N := N) 1 v = v := by simp [vm, redN_one]

theorem vm_ne_zero (γ : SL(2, ℤ)) {v : Fin 2 → ZMod N} (hv : v ≠ 0) : vm γ v ≠ 0 := by
  intro h
  apply hv
  have : vm γ⁻¹ (vm γ v) = v := by rw [← vm_mul, mul_inv_cancel, vm_one]
  rw [← this, h, vm, Matrix.zero_vecMul]

def idxMap (α : SL(2, ℤ)) : Idx N → Idx N :=
  fun o => o.map fun v => ⟨vm α v.1, vm_ne_zero α v.2⟩

def cw (G : ℍ → ℂ) (α : SL(2, ℤ)) : ℍ → ℂ := fun τ => G (α • τ)

theorem cw_apply (G : ℍ → ℂ) (α : SL(2, ℤ)) (τ : ℍ) : cw G α τ = G (α • τ) := rfl

theorem cw_mul (G : ℍ → ℂ) (α β : SL(2, ℤ)) : cw G (α * β) = cw (cw G α) β := by
  funext τ; simp [cw, mul_smul]

theorem cw_one (G : ℍ → ℂ) : cw G 1 = G := by funext τ; simp [cw]

theorem cw_eq_slash (G : ℍ → ℂ) (α : SL(2, ℤ)) : cw G α = G ∣[(0 : ℤ)] α := by
  funext τ
  rw [ModularForm.SL_slash_apply, cw_apply, neg_zero, zpow_zero, mul_one]

theorem mdifferentiable_cw {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) (α : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (cw G α) := by
  rw [cw_eq_slash, ModularForm.SL_slash]; exact hG.slash _ _

def cwAlgHom (α : SL(2, ℤ)) : (ℍ → ℂ) →ₐ[ℂ] (ℍ → ℂ) where
  toFun G := cw G α
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[scoped simp] theorem cwAlgHom_apply (α : SL(2, ℤ)) (G : ℍ → ℂ) : cwAlgHom α G = cw G α := rfl

theorem cw_mul_fun (G G' : ℍ → ℂ) (α : SL(2, ℤ)) : cw (G * G') α = cw G α * cw G' α := rfl
theorem cw_add_fun (G G' : ℍ → ℂ) (α : SL(2, ℤ)) : cw (G + G') α = cw G α + cw G' α := rfl
theorem cw_smul_fun (c : ℂ) (G : ℍ → ℂ) (α : SL(2, ℤ)) : cw (c • G) α = c • cw G α := rfl
theorem cw_sub_fun (G G' : ℍ → ℂ) (α : SL(2, ℤ)) : cw (G - G') α = cw G α - cw G' α := rfl

theorem cw_sum {ι : Type*} (s : Finset ι) (G : ι → ℍ → ℂ) (α : SL(2, ℤ)) :
    cw (∑ i ∈ s, G i) α = ∑ i ∈ s, cw (G i) α := map_sum (cwAlgHom α) G s

theorem mdifferentiable_E₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₄ : ℍ → ℂ) := E₄.holo'
theorem mdifferentiable_E₆ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₆ : ℍ → ℂ) := E₆.holo'

theorem mem_SL (A : SL(2, ℤ)) : (A : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨A, rfl⟩

theorem E₄_smul (A : SL(2, ℤ)) (τ : ℍ) :
    E₄ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (4 : ℤ) * E₄ τ := by
  have := SlashInvariantForm.slash_action_eqn'' E₄ (Γ := 𝒮ℒ) (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [← ModularGroup.sl_moeb] at this
  exact_mod_cast this

theorem E₆_smul (A : SL(2, ℤ)) (τ : ℍ) :
    E₆ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (6 : ℤ) * E₆ τ := by
  have := SlashInvariantForm.slash_action_eqn'' E₆ (Γ := 𝒮ℒ) (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [← ModularGroup.sl_moeb] at this
  exact_mod_cast this

theorem disc_smul (A : SL(2, ℤ)) (τ : ℍ) :
    Δ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ := by
  have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant (Γ := 𝒮ℒ)
    (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [CuspForm.coe_discriminant, ← ModularGroup.sl_moeb] at this
  exact this

theorem exists_E₄_ne_zero : ∃ τ : ℍ, E₄ τ ≠ 0 := by
  by_contra h
  push Not at h
  have : (E₄ : ModularForm 𝒮ℒ 4) = 0 := DFunLike.ext _ _ fun τ => by simpa using h τ
  exact EisensteinSeries.E_ne_zero (by norm_num) ⟨2, rfl⟩ this

theorem exists_E₆_ne_zero : ∃ τ : ℍ, E₆ τ ≠ 0 := by
  by_contra h
  push Not at h
  have : (E₆ : ModularForm 𝒮ℒ 6) = 0 := DFunLike.ext _ _ fun τ => by simpa using h τ
  exact EisensteinSeries.E_ne_zero (by norm_num) ⟨3, rfl⟩ this

include hjf in
theorem mdifferentiable_jf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := by
  have : jf = fun τ => E₄ τ ^ 3 / Δ τ ^ 1 := by funext τ; rw [hjf, pow_one]
  rw [this]; exact mdifferentiable_div_disc_pow (mdifferentiable_E₄.pow 3) 1

include hjf in
theorem jf_smul (α : SL(2, ℤ)) (τ : ℍ) : jf (α • τ) = jf τ := by
  have hd : denom (α : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
  have hΔ : Δ τ ≠ 0 := discriminant_ne_zero τ
  rw [hjf, hjf, disc_smul, E₄_smul]
  field_simp

include hjf in
theorem cw_jf (α : SL(2, ℤ)) : cw jf α = jf := funext (jf_smul jf hjf α)

include hjf in

theorem E₄_cube_eq (τ : ℍ) : E₄ τ ^ 3 = jf τ * Δ τ := by
  rw [hjf]; field_simp [disc_ne_zero τ]

include hjf in

theorem E₆_sq_eq (τ : ℍ) : E₆ τ ^ 2 = (jf τ - 1728) * Δ τ := by
  have h := discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [hjf, sub_mul, div_mul_cancel₀ _ (disc_ne_zero τ)]
  linear_combination (1728 : ℂ) * h

include hjf in
theorem exists_jf_ne_zero : ∃ τ : ℍ, jf τ ≠ 0 := by
  obtain ⟨τ, hτ⟩ := exists_E₄_ne_zero
  exact ⟨τ, fun h => pow_ne_zero 3 hτ (by rw [E₄_cube_eq jf hjf, h, zero_mul])⟩

include hjf in
theorem exists_jf_sub_ne_zero : ∃ τ : ℍ, jf τ - 1728 ≠ 0 := by
  obtain ⟨τ, hτ⟩ := exists_E₆_ne_zero
  exact ⟨τ, fun h => pow_ne_zero 2 hτ (by rw [E₆_sq_eq jf hjf, h, zero_mul])⟩

include hW hfricke in

theorem fricke_eq : fricke = fun (a : Fin 2 → ZMod N) (τ : ℍ) =>
    -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 *
      (((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
        PeriodPair.weierstrassP (L τ) ((((a 0).val : ℂ) * (τ : ℂ) + ((a 1).val : ℂ)) / (N : ℂ))) := by
  funext a τ; rw [hfricke, hW]

include hL hW hfricke in
theorem fricke_smul (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ) : fricke v (γ • τ) = fricke (vm γ v) τ := by
  have pkg := WLight.frickeFunction_modularity_package N L hL
  rw [← fricke_eq L W hW fricke hfricke] at pkg
  exact pkg.1 v γ τ

include hL hW hfricke in
theorem mdifferentiable_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v) := by
  have pkg := WLight.frickeFunction_modularity_package N L hL
  rw [← fricke_eq L W hW fricke hfricke] at pkg
  exact pkg.2.2.1 v hv

include hL hW hfricke in
theorem fricke_Gamma_smul (v : Fin 2 → ZMod N) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N)
    (τ : ℍ) : fricke v (γ • τ) = fricke v τ := by
  have pkg := WLight.frickeFunction_modularity_package N L hL
  rw [← fricke_eq L W hW fricke hfricke] at pkg
  exact pkg.2.2.2.2.2.2.1 v γ hγ τ

include hL hW hfricke hjf in
theorem cw_gen (α : SL(2, ℤ)) (o : Idx N) : cw (gen fricke jf o) α = gen fricke jf (idxMap α o) := by
  cases o with
  | none => exact cw_jf jf hjf α
  | some v => funext τ; exact fricke_smul L hL W hW fricke hfricke v.1 α τ

include hL hW hfricke hjf in
theorem mdifferentiable_gen (o : Idx N) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (gen fricke jf o) := by
  cases o with
  | none => exact mdifferentiable_jf jf hjf
  | some v => exact mdifferentiable_fricke L hL W hW fricke hfricke v.2

theorem cw_aeval {ι : Type} (g : ι → ℍ → ℂ) (R : MvPolynomial ι ℂ) (α : SL(2, ℤ)) :
    cw (MvPolynomial.aeval g R) α = MvPolynomial.aeval (fun i => cw (g i) α) R := by
  have := MvPolynomial.comp_aeval g (cwAlgHom α)
  simpa using congrArg (fun F => F R) this

include hL hW hfricke hjf in

theorem cw_evK (R : MvPolynomial (Idx N) K) (α : SL(2, ℤ)) :
    cw (evK fricke jf K R) α = evK fricke jf K (MvPolynomial.rename (idxMap α) R) := by
  rw [evK, evK, cw_aeval, MvPolynomial.map_rename, MvPolynomial.aeval_rename]
  have : (fun i => cw (gen fricke jf i) α) = gen fricke jf ∘ idxMap α :=
    funext fun o => cw_gen L hL W hW fricke hfricke jf hjf α o
  rw [this]

include hL hW hfricke hjf in
theorem mdifferentiable_evK (R : MvPolynomial (Idx N) K) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (evK fricke jf K R) := by
  rw [evK]
  induction (MvPolynomial.map (algebraMap K ℂ) R) using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C]; exact mdifferentiable_const
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p o hp => rw [map_mul, MvPolynomial.aeval_X]; exact hp.mul (mdifferentiable_gen L hL W hW fricke hfricke jf hjf o)

include hL hW hfricke hjf in
theorem evK_Gamma_smul (R : MvPolynomial (Idx N) K) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    cw (evK fricke jf K R) γ = evK fricke jf K R := by
  rw [evK, cw_aeval]
  have : (fun i => cw (gen fricke jf i) γ) = gen fricke jf := by
    funext o
    cases o with
    | none => exact cw_jf jf hjf γ
    | some v => funext τ; exact fricke_Gamma_smul L hL W hW fricke hfricke v.1 hγ τ
  rw [this]

theorem gen_mem_genSet (o : Idx N) : gen fricke jf o ∈ genSet (N := N) fricke jf := by
  cases o with
  | none => exact Set.mem_insert _ _
  | some v => exact Set.mem_insert_of_mem _ ⟨v.1, v.2, rfl⟩

theorem aeval_mem_adjoin (R : MvPolynomial (Idx N) ℂ) :
    MvPolynomial.aeval (gen fricke jf) R ∈ Algebra.adjoin ℂ (genSet (N := N) fricke jf) := by
  induction R using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C]; exact Subalgebra.algebraMap_mem _ c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p o hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact mul_mem hp (Algebra.subset_adjoin (gen_mem_genSet fricke jf o))

theorem evK_mem_adjoin (R : MvPolynomial (Idx N) K) :
    evK fricke jf K R ∈ Algebra.adjoin ℂ (genSet (N := N) fricke jf) := aeval_mem_adjoin fricke jf _

include hL hW hfricke hjf in

theorem adjoin_isDomain {x y : ℍ → ℂ} (hx : x ∈ Algebra.adjoin ℂ (genSet (N := N) fricke jf))
    (hy : y ∈ Algebra.adjoin ℂ (genSet (N := N) fricke jf)) (hxy : x * y = 0) : x = 0 ∨ y = 0 := by
  obtain ⟨-, -, -, -, -, h6⟩ := WLight.levelN_structure_package N L hL W hW fricke hfricke jf hjf
  exact h6 x y hx hy hxy

include hL hW hfricke hjf in
theorem evK_mul_ne_zero {R S : MvPolynomial (Idx N) K} (hR : evK fricke jf K R ≠ 0) (hS : evK fricke jf K S ≠ 0) :
    evK fricke jf K (R * S) ≠ 0 := by
  rw [evK_mul]
  intro h
  rcases adjoin_isDomain L hL W hW fricke hfricke jf hjf (evK_mem_adjoin fricke jf K R)
    (evK_mem_adjoin fricke jf K S) h with h | h
  · exact hR h
  · exact hS h

theorem exists_evK_of_mem_adjoin {x : ℍ → ℂ} (hx : x ∈ Algebra.adjoin K (genSet (N := N) fricke jf)) :
    ∃ R : MvPolynomial (Idx N) K, evK fricke jf K R = x := by
  classical
  rw [Algebra.adjoin_eq_range] at hx
  obtain ⟨R₀, rfl⟩ := hx
  have hsec : ∀ y : genSet (N := N) fricke jf, ∃ o : Idx N, gen fricke jf o = y := by
    rintro ⟨y, hy⟩
    rcases hy with rfl | ⟨v, hv, rfl⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨v, hv⟩, rfl⟩
  choose sec hsec using hsec
  refine ⟨MvPolynomial.rename sec R₀, ?_⟩
  rw [evK, MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_rename]
  have : (gen fricke jf ∘ sec) = Subtype.val := funext hsec
  rw [this]
  rfl

def IsFQ (G : ℍ → ℂ) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∃ P Q : MvPolynomial (Idx N) K,
    evK fricke jf K Q ≠ 0 ∧ G * evK fricke jf K Q = evK fricke jf K P

include hL hW hfricke hjf in
theorem IsFQ.add {G G' : ℍ → ℂ} (h : IsFQ fricke jf K G) (h' : IsFQ fricke jf K G') :
    IsFQ fricke jf K (G + G') := by
  obtain ⟨hG, P, Q, hQ, hGQ⟩ := h
  obtain ⟨hG', P', Q', hQ', hGQ'⟩ := h'
  refine ⟨hG.add hG', P * Q' + P' * Q, Q * Q', evK_mul_ne_zero L hL W hW fricke hfricke jf hjf K hQ hQ', ?_⟩
  rw [evK_add, evK_mul, evK_mul, evK_mul, add_mul, ← hGQ, ← hGQ']
  ring

theorem IsFQ.smul {G : ℍ → ℂ} (h : IsFQ fricke jf K G) (c : K) : IsFQ fricke jf K ((c : ℂ) • G) := by
  obtain ⟨hG, P, Q, hQ, hGQ⟩ := h
  refine ⟨hG.const_smul _, MvPolynomial.C c * P, Q, hQ, ?_⟩
  rw [evK_mul, evK_C, smul_mul_assoc, hGQ]
  funext τ; simp [smul_eq_mul]

theorem isFQ_zero : IsFQ fricke jf K (0 : ℍ → ℂ) :=
  ⟨mdifferentiable_const, 0, 1, by rw [evK_one]; exact one_ne_zero, by rw [evK_zero, zero_mul]⟩

include hL hW hfricke hjf in
theorem IsFQ.mul {G G' : ℍ → ℂ} (h : IsFQ fricke jf K G) (h' : IsFQ fricke jf K G') :
    IsFQ fricke jf K (G * G') := by
  obtain ⟨hG, P, Q, hQ, hGQ⟩ := h
  obtain ⟨hG', P', Q', hQ', hGQ'⟩ := h'
  refine ⟨hG.mul hG', P * P', Q * Q', evK_mul_ne_zero L hL W hW fricke hfricke jf hjf K hQ hQ', ?_⟩
  rw [evK_mul, evK_mul, ← hGQ, ← hGQ']; ring

include hL hW hfricke hjf in
theorem isFQ_evK (R : MvPolynomial (Idx N) K) : IsFQ fricke jf K (evK fricke jf K R) :=
  ⟨mdifferentiable_evK L hL W hW fricke hfricke jf hjf K R, R, 1, by rw [evK_one]; exact one_ne_zero,
    by rw [evK_one, mul_one]⟩

include hL hW hfricke hjf in
theorem isFQ_jf : IsFQ fricke jf K jf := by
  have := isFQ_evK L hL W hW fricke hfricke jf hjf K (MvPolynomial.X none)
  rwa [evK_X] at this

include hL hW hfricke hjf in
theorem isFQ_const (c : K) : IsFQ fricke jf K (fun _ : ℍ => (c : ℂ)) := by
  have := isFQ_evK L hL W hW fricke hfricke jf hjf K (MvPolynomial.C c)
  rwa [evK_C] at this

include hL hW hfricke hjf in
theorem isFQ_one : IsFQ fricke jf K (1 : ℍ → ℂ) := by
  have h1 : (fun _ : ℍ => ((1 : K) : ℂ)) = 1 := by funext τ; simp
  exact h1 ▸ isFQ_const L hL W hW fricke hfricke jf hjf K 1

theorem evK_neg (R : MvPolynomial (Idx N) K) : evK fricke jf K (-R) = -evK fricke jf K R := by
  simp [evK]

theorem IsFQ.neg {G : ℍ → ℂ} (h : IsFQ fricke jf K G) : IsFQ fricke jf K (-G) := by
  obtain ⟨hG, P, Q, hQ, hGQ⟩ := h
  exact ⟨hG.neg, -P, Q, hQ, by rw [evK_neg, neg_mul, hGQ]⟩

include hL hW hfricke hjf in
theorem IsFQ.sub {G G' : ℍ → ℂ} (h : IsFQ fricke jf K G) (h' : IsFQ fricke jf K G') :
    IsFQ fricke jf K (G - G') := by
  rw [sub_eq_add_neg]
  exact h.add L hL W hW fricke hfricke jf hjf K h'.neg

include hL hW hfricke hjf in
theorem IsFQ.pow {G : ℍ → ℂ} (h : IsFQ fricke jf K G) (n : ℕ) : IsFQ fricke jf K (G ^ n) := by
  induction n with
  | zero => simpa using isFQ_one L hL W hW fricke hfricke jf hjf K
  | succ n ih => rw [pow_succ]; exact ih.mul L hL W hW fricke hfricke jf hjf K h

include hL hW hfricke hjf in

theorem isFQ_cw {G : ℍ → ℂ} (h : IsFQ fricke jf K G) (α : SL(2, ℤ)) : IsFQ fricke jf K (cw G α) := by
  obtain ⟨hG, P, Q, hQ, hGQ⟩ := h
  refine ⟨mdifferentiable_cw hG α, MvPolynomial.rename (idxMap α) P, MvPolynomial.rename (idxMap α) Q, ?_, ?_⟩
  · rw [← cw_evK L hL W hW fricke hfricke jf hjf]
    intro h0
    apply hQ
    have : cw (cw (evK fricke jf K Q) α) α⁻¹ = 0 := by rw [h0]; rfl
    rwa [← cw_mul, mul_inv_cancel, cw_one] at this
  · rw [← cw_evK L hL W hW fricke hfricke jf hjf, ← cw_evK L hL W hW fricke hfricke jf hjf, ← cw_mul_fun, hGQ]

include hL hW hfricke hjf in

theorem isFQ_Gamma_smul {G : ℍ → ℂ} (h : IsFQ fricke jf K G) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) : cw G γ = G := by
  obtain ⟨hG, P, Q, hQ, hGQ⟩ := h
  have h1 : cw G γ * evK fricke jf K Q = evK fricke jf K P := by
    have := congrArg (fun F => cw F γ) hGQ
    simp only [cw_mul_fun, evK_Gamma_smul L hL W hW fricke hfricke jf hjf K _ hγ] at this
    exact this
  have h2 : ∀ τ, (cw G γ - G) τ * evK fricke jf K Q τ = 0 := by
    intro τ
    have := congrFun h1 τ
    have h' := congrFun hGQ τ
    simp only [Pi.mul_apply, Pi.sub_apply] at this h' ⊢
    rw [sub_mul, this, h', sub_self]
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀, evK fricke jf K Q τ₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hQ (funext hall)
  have := eq_zero_of_mul_eq_zero ((mdifferentiable_cw hG γ).sub hG)
    (mdifferentiable_evK L hL W hW fricke hfricke jf hjf K Q) h2 hτ₀
  exact sub_eq_zero.1 this

include hL hW hfricke hjf in

def M : Submodule K (ℍ → ℂ) where
  carrier := {G | IsFQ fricke jf K G}
  add_mem' hG hG' := IsFQ.add L hL W hW fricke hfricke jf hjf K hG hG'
  zero_mem' := isFQ_zero fricke jf K
  smul_mem' c _ hG := IsFQ.smul fricke jf K hG c

theorem mem_M {G : ℍ → ℂ} : G ∈ M L hL W hW fricke hfricke jf hjf K ↔ IsFQ fricke jf K G := Iff.rfl

section Width

variable (N)

theorem natCast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

theorem qParam_one_eq_pow (τ : ℍ) : Periodic.qParam 1 τ = Periodic.qParam N τ ^ N := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  push_cast
  field_simp

theorem qExpansion_coeff_unique' {h : ℝ} (hh : 0 < h) {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hc : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam h τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hc).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

theorem qExpansion_coeff_widthN {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion N g).coeff n = if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 := by
  classical
  have hperN : Periodic (g ∘ ofComplex) N := periodic_ofComplex_natCast hper N
  set c : ℕ → ℂ := fun n => if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 with hc
  have hNpos : 0 < N := NeZero.pos N
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam N τ ^ m) (g τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hg hbd τ
    have hinj : Function.Injective fun m : ℕ => N * m := mul_right_injective₀ hNpos.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ => N * m),
        (fun m => c m • Periodic.qParam N τ ^ m) x = 0 := by
      intro x hx
      have : ¬ (N : ℕ) ∣ x := by
        rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).1 ?_
    convert h1 using 1 <;> try with_reducible_and_instances rfl
    funext m
    simp only [comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hNpos]
    rw [qParam_one_eq_pow N τ, ← pow_mul]
  rw [← qExpansion_coeff_unique' (natCast_pos N) (analyticAt_cuspFunction_zero (natCast_pos N)
    hperN hg hbd) hsum n]

theorem qExpansion_E₄_rat (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (E₄ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [ModularForm.E₄, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-(2 * 4 / bernoulli 4) * (ArithmeticFunction.sigma 3 n : ℚ), by push_cast; ring⟩

theorem qExpansion_E₆_rat (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (E₆ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [ModularForm.E₆, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-(2 * 6 / bernoulli 6) * (ArithmeticFunction.sigma 5 n : ℚ), by push_cast; ring⟩

theorem qExpansion_disc_rat_one (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (Δ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  let A : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)
  let B : ModularForm 𝒮ℒ 12 := (E₆.pow 2).mcast (by norm_num)
  have hfun : (Δ : ℍ → ℂ) = ⇑((1728 : ℂ)⁻¹ • (A - B)) := by
    funext z
    rw [discriminant_eq_E₄_cube_sub_E₆_sq, IsGLPos.smul_apply, sub_apply]
    simp only [A, B, coe_mcast, coe_pow, Pi.pow_apply, smul_eq_mul]
    ring
  obtain ⟨p4, hp4⟩ : ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = qExpansion 1 (E₄ : ℍ → ℂ) := by
    choose r hr using qExpansion_E₄_rat
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  obtain ⟨p6, hp6⟩ : ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = qExpansion 1 (E₆ : ℍ → ℂ) := by
    choose r hr using qExpansion_E₆_rat
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  have hq : qExpansion 1 (Δ : ℍ → ℂ) = ((1728 : ℚ)⁻¹ • (p4 ^ 3 - p6 ^ 2)).map (algebraMap ℚ ℂ) := by
    rw [hfun, IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]
    simp only [A, B, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
    rw [PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_sub,
      map_pow, map_pow, hp4, hp6]
    congr 1
    simp
  refine ⟨PowerSeries.coeff n ((1728 : ℚ)⁻¹ • (p4 ^ 3 - p6 ^ 2)), ?_⟩
  rw [hq, PowerSeries.coeff_map]
  rfl

theorem qExpansion_disc_rat (n : ℕ) : ∃ r : ℚ, (qExpansion N (Δ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [qExpansion_coeff_widthN N mdifferentiable_disc periodic_disc_one isBoundedAtImInfty_disc n]
  split_ifs with h
  · exact qExpansion_disc_rat_one _
  · exact ⟨0, by simp⟩

theorem ratCast_mem (r : ℚ) : ((r : ℂ)) ∈ K := by
  have : (r : ℂ) = algebraMap ℚ ℂ r := rfl
  rw [this]; exact K.algebraMap_mem r

structure Nice (m : ℕ) (g : ℍ → ℂ) : Prop where
  mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g
  periodic : Periodic ((g * Δ ^ m) ∘ ofComplex) N
  bdd : IsBoundedAtImInfty (g * Δ ^ m)

structure RatAt (m : ℕ) (g : ℍ → ℂ) : Prop extends Nice N m g where
  mem : ∀ n, (qExpansion N (g * Δ ^ m)).coeff n ∈ K

variable {N K}

theorem Nice.mdiff_mul {m : ℕ} {g : ℍ → ℂ} (h : Nice N m g) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g * Δ ^ m) :=
  h.mdiff.mul (mdifferentiable_disc.pow m)

theorem Nice.analyticAt {m : ℕ} {g : ℍ → ℂ} (h : Nice N m g) : AnalyticAt ℂ (cuspFunction N (g * Δ ^ m)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) h.periodic h.mdiff_mul h.bdd

theorem analyticAt_disc : AnalyticAt ℂ (cuspFunction N (Δ : ℍ → ℂ)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) (periodic_ofComplex_natCast periodic_disc_one N)
    mdifferentiable_disc isBoundedAtImInfty_disc

theorem Nice.succ {m : ℕ} {g : ℍ → ℂ} (h : Nice N m g) : Nice N (m + 1) g where
  mdiff := h.mdiff
  periodic := by
    rw [pow_succ, ← mul_assoc]
    exact periodic_mul h.periodic (periodic_ofComplex_natCast periodic_disc_one N)
  bdd := by rw [pow_succ, ← mul_assoc]; exact h.bdd.mul isBoundedAtImInfty_disc

theorem Nice.of_le {m m' : ℕ} (hm : m ≤ m') {g : ℍ → ℂ} (h : Nice N m g) : Nice N m' g := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => simpa using h
  | succ d ih => exact (ih (Nat.le_add_right m d)).succ

theorem Nice.add {m : ℕ} {g g' : ℍ → ℂ} (h : Nice N m g) (h' : Nice N m g') : Nice N m (g + g') where
  mdiff := h.mdiff.add h'.mdiff
  periodic := by rw [add_mul]; exact periodic_add h.periodic h'.periodic
  bdd := by rw [add_mul]; exact h.bdd.add h'.bdd

theorem Nice.smul {m : ℕ} {g : ℍ → ℂ} (h : Nice N m g) (c : ℂ) : Nice N m (c • g) where
  mdiff := h.mdiff.const_smul c
  periodic := by rw [smul_mul_assoc]; exact periodic_smul h.periodic c
  bdd := by
    rw [smul_mul_assoc]
    have := h.bdd.const_mul_left c
    first
      | simpa [smul_eq_mul] using this
      | (simpa [smul_eq_mul] using (this :))
      | (simpa [Function.comp_def] using this)
      | exact this
      | (have h__ := this; (try simp [smul_eq_mul] at h__); (try simp [smul_eq_mul]); exact h__)

theorem nice_zero (m : ℕ) : Nice N m (0 : ℍ → ℂ) where
  mdiff := mdifferentiable_const
  periodic := by intro z; simp
  bdd := by rw [zero_mul]; exact UpperHalfPlane.zero_form_isBoundedAtImInfty

theorem Nice.sum {m : ℕ} {ι : Type*} (s : Finset ι) {g : ι → ℍ → ℂ} (h : ∀ i ∈ s, Nice N m (g i))
    (c : ι → ℂ) : Nice N m (∑ i ∈ s, c i • g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using nice_zero m
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact ((h a (Finset.mem_insert_self a s)).smul (c a)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem qExpansion_sum {m : ℕ} {ι : Type*} (s : Finset ι) {g : ι → ℍ → ℂ} (h : ∀ i ∈ s, Nice N m (g i))
    (c : ι → ℂ) (n : ℕ) :
    (qExpansion N ((∑ i ∈ s, c i • g i) * Δ ^ m)).coeff n = ∑ i ∈ s, c i * (qExpansion N (g i * Δ ^ m)).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mul,
        qExpansion_add ((h a (Finset.mem_insert_self a s)).smul (c a)).analyticAt
          (Nice.sum s (fun i hi => h i (Finset.mem_insert_of_mem hi)) c).analyticAt,
        map_add, ih fun i hi => h i (Finset.mem_insert_of_mem hi), smul_mul_assoc,
        qExpansion_smul (h a (Finset.mem_insert_self a s)).analyticAt, map_smul, smul_eq_mul]

theorem RatAt.succ {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) : RatAt N K (m + 1) g where
  toNice := h.toNice.succ
  mem := by
    intro n
    rw [pow_succ, ← mul_assoc, qExpansion_mul h.analyticAt analyticAt_disc, PowerSeries.coeff_mul]
    refine sum_mem fun ij _ => mul_mem (h.mem _) ?_
    obtain ⟨r, hr⟩ := qExpansion_disc_rat N ij.2
    rw [hr]; exact ratCast_mem K r

theorem RatAt.of_le {m m' : ℕ} (hm : m ≤ m') {g : ℍ → ℂ} (h : RatAt N K m g) : RatAt N K m' g := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => simpa using h
  | succ d ih => exact (ih (Nat.le_add_right m d)).succ

theorem coeff_map_mem (R : MvPolynomial (Idx N) K) (mo : Idx N →₀ ℕ) :
    (MvPolynomial.map (algebraMap K ℂ) R).coeff mo ∈ K := by
  rw [MvPolynomial.coeff_map]; exact (R.coeff mo).2

include hL hW hfricke hjf hK in

theorem IsFQ.exists_ratAt {G : ℍ → ℂ} (h : IsFQ fricke jf K G) : ∃ m, RatAt N K m G := by
  obtain ⟨hG, P, Q, hQ, hGQ⟩ := h
  have hint := WLight.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient N L hL W hW fricke hfricke jf hjf
    K hK G hG P Q hQ hGQ
  obtain ⟨m, hper, hbdd, hmem⟩ := WLight.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction N L hL
    W hW fricke hfricke jf hjf K hK hG (MvPolynomial.map (algebraMap K ℂ) P)
    (MvPolynomial.map (algebraMap K ℂ) Q) (coeff_map_mem P) (coeff_map_mem Q) hQ hGQ hint
  exact ⟨m, ⟨⟨hG, hper, hbdd⟩, hmem⟩⟩

include hL hW hfricke hjf hK in

theorem M_flat (s : Finset (ℍ → ℂ)) (hs : (↑s : Set (ℍ → ℂ)) ⊆ (M L hL W hW fricke hfricke jf hjf K : Set (ℍ → ℂ)))
    (hind : LinearIndependent K (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ))) :
    LinearIndependent ℂ (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) := by
  classical
  have hrat : ∀ f : ↥s, ∃ m, RatAt N K m (f : ℍ → ℂ) := fun f =>
    IsFQ.exists_ratAt L hL W hW fricke hfricke jf hjf hK (hs (by simp))
  choose mf hmf using hrat
  set M₀ : ℕ := ∑ f : ↥s, mf f
  have hM₀ : ∀ f : ↥s, RatAt N K M₀ (f : ℍ → ℂ) := fun f =>
    (hmf f).of_le (Finset.single_le_sum (fun g _ => Nat.zero_le (mf g)) (Finset.mem_univ f))
  refine WLight.linearIndependent_complex_of_qExpansion_rational N K s M₀ (fun f hf => ?_) hind
  have h := hM₀ ⟨f, hf⟩
  exact ⟨h.mdiff, h.periodic, h.bdd, h.mem⟩

end Width

section Key

include hL hW hfricke hjf hK in

theorem mem_span_M {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (γ • τ) = G τ)
    (hpb : ∀ α : SL(2, ℤ), ∃ m : ℕ, IsBoundedAtImInfty (cw G α * Δ ^ m)) :
    G ∈ Submodule.span ℂ (M L hL W hW fricke hfricke jf hjf K : Set (ℍ → ℂ)) := by
  classical

  set S : Set (ℍ → ℂ) := {F | ∃ α : SL(2, ℤ), F = cw G α} with hS
  have hGS : G ∈ S := ⟨1, (cw_one G).symm⟩
  have hhol : ∀ F ∈ S, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
    rintro F ⟨α, rfl⟩; exact mdifferentiable_cw hG α
  have hpb' : ∀ F ∈ S, ∃ m : ℕ, IsBoundedAtImInfty (F * ModularForm.discriminant ^ m) := by
    rintro F ⟨α, rfl⟩; exact hpb α
  have hst : ∀ γ : SL(2, ℤ), ∀ F ∈ S, (F ∘ (γ • ·)) ∈ S := by
    rintro γ F ⟨α, rfl⟩
    exact ⟨α * γ, by rw [cw_mul]; rfl⟩
  have hinvS : ∀ F ∈ S, ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, F (γ • τ) = F τ := by
    rintro F ⟨α, rfl⟩ γ hγ τ
    simp only [cw_apply]
    have : α • γ • τ = (α * γ * α⁻¹) • α • τ := by simp only [mul_smul, inv_smul_smul]
    rw [this]
    exact hinv _ (Subgroup.Normal.conj_mem (CongruenceSubgroup.Gamma_normal N) γ hγ α) _
  obtain ⟨a, b, ha, hb, hb0, hGb⟩ := WLight.exists_levelFraction_of_stable_family N L hL W hW fricke hfricke
    jf hjf S hhol hpb' hst hinvS hGS

  have hpbG : ∀ γ : SL(2, ℤ), ∃ m : ℕ, IsBoundedAtImInfty ((G ∘ (γ • ·)) * ModularForm.discriminant ^ m) :=
    fun γ => hpb γ
  obtain ⟨d, p, hprel⟩ := WLight.exists_monicRel_j_of_mdifferentiable_levelFraction N L hL W hW fricke hfricke
    jf hjf ha hb hb0 hG hGb hpbG

  obtain ⟨n, lam, Gi, Pi, Qi, di, pi, hGsum, hGimd, hPQ, -, -⟩ :=
    WLight.frickeFunction_intBaseChange N L hL W hW fricke hfricke jf hjf hG ha hb hb0 hGb p hprel

  subst hK
  have hGiM : ∀ i, Gi i ∈ M L hL W hW fricke hfricke jf hjf
      (IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))}) := by
    intro i
    obtain ⟨hPi, hQi, hQi0, hrel⟩ := hPQ i
    obtain ⟨RP, hRP⟩ := exists_evK_of_mem_adjoin fricke jf _ hPi
    obtain ⟨RQ, hRQ⟩ := exists_evK_of_mem_adjoin fricke jf _ hQi
    exact ⟨hGimd i, RP, RQ, by rw [hRQ]; exact hQi0, by rw [hRQ, hRP]; exact hrel⟩
  rw [hGsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hGiM i))

end Key

section Twist

variable (σ : ℂ ≃ₐ[K] ℂ)

local notation "𝕄" => M L hL W hW fricke hfricke jf hjf K

include hK in
theorem exists_twist : ∃ T : (ℍ → ℂ) → (ℍ → ℂ), ∀ (ι : Type) [Fintype ι] (c : ι → ℂ) (e : ι → ℍ → ℂ),
    (∀ i, e i ∈ 𝕄) → T (∑ i, c i • e i) = ∑ i, σ (c i) • e i :=
  WLight.exists_twist_of_flat K 𝕄 (M_flat L hL W hW fricke hfricke jf hjf hK) σ

include hK in

def Tw : (ℍ → ℂ) → (ℍ → ℂ) := (exists_twist L hL W hW fricke hfricke jf hjf K hK σ).choose

variable {L hL W hW fricke hfricke jf hjf K}

local notation "𝕋" => Tw L hL W hW fricke hfricke jf hjf K hK σ

theorem Tw_rep {ι : Type} [Fintype ι] (c : ι → ℂ) (e : ι → ℍ → ℂ) (he : ∀ i, e i ∈ 𝕄) :
    𝕋 (∑ i, c i • e i) = ∑ i, σ (c i) • e i :=
  (exists_twist L hL W hW fricke hfricke jf hjf K hK σ).choose_spec ι c e he

theorem exists_rep {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (e : Fin n → ℍ → ℂ), (∀ i, e i ∈ 𝕄) ∧ u = ∑ i, c i • e i := by
  obtain ⟨n, c, g, hu⟩ := Submodule.mem_span_set'.1 hu
  exact ⟨n, c, fun i => (g i : ℍ → ℂ), fun i => (g i).2, hu.symm⟩

theorem sum_smul_mem_span {ι : Type} [Fintype ι] (c : ι → ℂ) (e : ι → ℍ → ℂ) (he : ∀ i, e i ∈ 𝕄) :
    ∑ i, c i • e i ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)) :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (he i))

theorem Tw_mem_span {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) :
    𝕋 u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)) := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  rw [Tw_rep hK σ c e he]
  exact sum_smul_mem_span _ e he

theorem Tw_add {u v : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)))
    (hv : v ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) :
    𝕋 (u + v) =
      𝕋 u + 𝕋 v := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  obtain ⟨n', c', e', he', rfl⟩ := exists_rep hv
  have hsum : (∑ i, c i • e i) + (∑ i, c' i • e' i) =
      ∑ i : Fin n ⊕ Fin n', Sum.elim c c' i • Sum.elim e e' i := by
    rw [Fintype.sum_sum_type]; rfl
  rw [hsum, Tw_rep hK σ _ _ (fun i => by cases i <;> simp [he, he']),
    Tw_rep hK σ c e he, Tw_rep hK σ c' e' he',
    Fintype.sum_sum_type]
  rfl

theorem Tw_smul (a : ℂ) {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) :
    𝕋 (a • u) = σ a • 𝕋 u := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  have hsum : a • (∑ i, c i • e i) = ∑ i, (a * c i) • e i := by
    rw [Finset.smul_sum]; simp_rw [smul_smul]
  rw [hsum, Tw_rep hK σ _ e he, Tw_rep hK σ c e he,
    Finset.smul_sum]
  simp_rw [map_mul, smul_smul]

theorem Tw_mul {u v : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)))
    (hv : v ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) :
    𝕋 (u * v) =
      𝕋 u * 𝕋 v := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  obtain ⟨n', c', e', he', rfl⟩ := exists_rep hv
  have hprod : ∀ (x : Fin n → ℂ) (y : Fin n' → ℂ), (∑ i, x i • e i) * (∑ j, y j • e' j) =
      ∑ ij : Fin n × Fin n', (x ij.1 * y ij.2) • (e ij.1 * e' ij.2) := by
    intro x y
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [smul_mul_smul_comm]
  have hee : ∀ ij : Fin n × Fin n', e ij.1 * e' ij.2 ∈ 𝕄 := fun ij =>
    IsFQ.mul L hL W hW fricke hfricke jf hjf K (he ij.1) (he' ij.2)
  rw [hprod, Tw_rep hK σ _ _ hee, Tw_rep hK σ c e he,
    Tw_rep hK σ c' e' he', hprod]
  simp_rw [map_mul]

theorem Tw_of_mem {e : ℍ → ℂ} (he : e ∈ 𝕄) : 𝕋 e = e := by
  have h1 : e = ∑ _i : Fin 1, (1 : ℂ) • e := by simp
  conv_lhs => rw [h1]
  rw [Tw_rep hK σ _ _ (fun _ => he)]
  simp

theorem mem_span_of_mem {e : ℍ → ℂ} (he : e ∈ 𝕄) : e ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)) :=
  Submodule.subset_span he

theorem one_mem_span : (1 : ℍ → ℂ) ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)) :=
  mem_span_of_mem (isFQ_one L hL W hW fricke hfricke jf hjf K)

theorem mul_mem_span {u v : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)))
    (hv : v ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) : u * v ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)) := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  obtain ⟨n', c', e', he', rfl⟩ := exists_rep hv
  rw [Finset.sum_mul_sum]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  rw [smul_mul_smul_comm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (IsFQ.mul L hL W hW fricke hfricke jf hjf K (he i) (he' j)))

theorem pow_mem_span {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) (n : ℕ) :
    u ^ n ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)) := by
  induction n with
  | zero => rw [pow_zero]; exact one_mem_span
  | succ n ih => rw [pow_succ]; exact mul_mem_span ih hu

theorem Tw_pow {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) (n : ℕ) :
    𝕋 (u ^ n) = (𝕋 u) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact Tw_of_mem hK σ (isFQ_one L hL W hW fricke hfricke jf hjf K)
  | succ n ih =>
      rw [pow_succ, pow_succ, Tw_mul hK σ (pow_mem_span hu n) hu, ih]

theorem cw_mem_span {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) (α : SL(2, ℤ)) :
    cw u α ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)) := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  rw [cw_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [cw_smul_fun]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (isFQ_cw L hL W hW fricke hfricke jf hjf K (he i) α))

theorem Tw_cw {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) (α : SL(2, ℤ)) :
    𝕋 (cw u α) = cw (𝕋 u) α := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  have h1 : cw (∑ i, c i • e i) α = ∑ i, c i • cw (e i) α := by rw [cw_sum]; rfl
  rw [h1, Tw_rep hK σ _ _ (fun i => isFQ_cw L hL W hW fricke hfricke jf hjf K (he i) α),
    Tw_rep hK σ c e he, cw_sum]
  rfl

theorem mdifferentiable_of_mem_span {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  have : ∀ i ∈ (Finset.univ : Finset (Fin n)), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c i • e i) :=
    fun i _ => ((he i).1).const_smul (c i)
  exact MDifferentiable.sum (t := Finset.univ) this

theorem Tw_mdifferentiable {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (𝕋 u) :=
  mdifferentiable_of_mem_span (Tw_mem_span hK σ hu)

theorem Gamma_smul_of_mem_span {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)))
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) : cw u γ = u := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  rw [cw_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [cw_smul_fun, isFQ_Gamma_smul L hL W hW fricke hfricke jf hjf K (he i) hγ]

include hK in

theorem exists_common_ratAt {ι : Type} [Fintype ι] (e : ι → ℍ → ℂ) (he : ∀ i, e i ∈ 𝕄) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ i, RatAt N K m (e i) := by
  classical
  have : ∀ i, ∃ m, RatAt N K m (e i) := fun i => IsFQ.exists_ratAt L hL W hW fricke hfricke jf hjf hK (he i)
  choose mf hmf using this
  refine ⟨∑ i, mf i, fun m hm i => (hmf i).of_le (le_trans ?_ hm)⟩
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (mf j)) (Finset.mem_univ i)

theorem Tw_coeff {ι : Type} [Fintype ι] (c : ι → ℂ) (e : ι → ℍ → ℂ) (he : ∀ i, e i ∈ 𝕄) {m : ℕ}
    (hm : ∀ i, RatAt N K m (e i)) (n : ℕ) :
    (qExpansion N (𝕋 (∑ i, c i • e i) * Δ ^ m)).coeff n =
      σ ((qExpansion N ((∑ i, c i • e i) * Δ ^ m)).coeff n) := by
  rw [Tw_rep hK σ c e he,
    qExpansion_sum Finset.univ (fun i _ => (hm i).toNice) (fun i => σ (c i)) n,
    qExpansion_sum Finset.univ (fun i _ => (hm i).toNice) c n, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  congr 1
  obtain ⟨z, hz⟩ : ∃ z : K, (z : ℂ) = (qExpansion N (e i * Δ ^ m)).coeff n := ⟨⟨_, (hm i).mem n⟩, rfl⟩
  rw [← hz]
  exact (σ.commutes z).symm

theorem nice_Tw {ι : Type} [Fintype ι] (c : ι → ℂ) (e : ι → ℍ → ℂ) (he : ∀ i, e i ∈ 𝕄) {m : ℕ}
    (hm : ∀ i, RatAt N K m (e i)) : Nice N m (𝕋 (∑ i, c i • e i)) := by
  rw [Tw_rep hK σ c e he]
  exact Nice.sum Finset.univ (fun i _ => (hm i).toNice) _

theorem nice_sum {ι : Type} [Fintype ι] (c : ι → ℂ) (e : ι → ℍ → ℂ) {m : ℕ}
    (hm : ∀ i, RatAt N K m (e i)) : Nice N m (∑ i, c i • e i) :=
  Nice.sum Finset.univ (fun i _ => (hm i).toNice) _

end Twist

section Stability

theorem tendsto_E {k : ℕ} (hk3 : 3 ≤ k) (hk2 : Even k) :
    Tendsto (⇑(ModularForm.E hk3) : ℍ → ℂ) atImInfty (𝓝 1) := by
  have hanal := ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.E hk3) one_pos
    one_mem_strictPeriods_SL
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E hk3) one_mem_strictPeriods_SL
  have hval : cuspFunction 1 (⇑(ModularForm.E hk3)) 0 = 1 := by
    have h0 := qExpansion_coeff (⇑(ModularForm.E hk3)) (h := (1 : ℝ)) 0
    rw [EisensteinSeries.E_qExpansion_coeff_zero hk3 hk2] at h0
    simpa using h0.symm
  have := (hanal.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)).congr
    (fun τ => eq_cuspFunction τ one_ne_zero hper)
  simpa [hval] using this

theorem tendsto_E₄ : Tendsto (⇑E₄ : ℍ → ℂ) atImInfty (𝓝 1) := tendsto_E (by norm_num) ⟨2, rfl⟩
theorem tendsto_E₆ : Tendsto (⇑E₆ : ℍ → ℂ) atImInfty (𝓝 1) := tendsto_E (by norm_num) ⟨3, rfl⟩

theorem bdd_of_mul_tendsto_one {h e : ℍ → ℂ} (hhe : IsBoundedAtImInfty (h * e))
    (he : Tendsto e atImInfty (𝓝 1)) : IsBoundedAtImInfty h := by
  have hne : ∀ᶠ τ in atImInfty, e τ ≠ 0 := he.eventually_ne one_ne_zero
  have hinv : Tendsto (fun τ => (e τ)⁻¹) atImInfty (𝓝 1) := by simpa using he.inv₀ one_ne_zero
  have hb : IsBoundedAtImInfty ((h * e) * fun τ => (e τ)⁻¹) := hhe.mul (hinv.isBigO_one ℝ)
  refine (hb.congr' ?_ EventuallyEq.rfl)
  filter_upwards [hne] with τ hτ
  simp only [Pi.mul_apply]
  field_simp

theorem bdd_pow {f : ℍ → ℂ} (hf : IsBoundedAtImInfty f) (n : ℕ) : IsBoundedAtImInfty (f ^ n) := by
  induction n with
  | zero => first | simpa using Filter.const_boundedAtFilter atImInfty (1 : ℂ) | (simp only [pow_zero]; exact Filter.const_boundedAtFilter atImInfty (1 : ℂ)) | (simp; exact Filter.const_boundedAtFilter atImInfty (1 : ℂ))
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem periodic_of_Gamma_invariant {N : ℕ} [NeZero N] {u : ℍ → ℂ}
    (h : ∀ γ ∈ CongruenceSubgroup.Gamma N, cw u γ = u) : Periodic (u ∘ ofComplex) N := by
  have hT : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    have := CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
    rwa [Int.natAbs_natCast] at this
  have hu : ∀ τ : ℍ, u ((ModularGroup.T ^ (N : ℤ)) • τ) = u τ := fun τ => congrFun (h _ hT) τ
  intro w
  by_cases hw : 0 < im w
  · have this : 0 < im (w + N) := by simpa using hw
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    have := hu ⟨w, hw⟩
    rw [modular_T_zpow_smul] at this
    convert this using 2 <;> try with_reducible_and_instances rfl
    ext
    simp [add_comm, UpperHalfPlane.coe_vadd]
  · push Not at hw
    have : im (w + N) ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

theorem periodic_disc_fun (φ : ℂ → ℂ) : Periodic ((fun τ : ℍ => φ (Δ τ)) ∘ ofComplex) 1 := by
  intro z
  have := periodic_disc_one z
  simp only [comp_apply] at this ⊢
  rw [this]

variable {L hL W hW fricke hfricke jf hjf K}
variable (σ : ℂ ≃ₐ[K] ℂ)

local notation "𝕄" => M L hL W hW fricke hfricke jf hjf K
local notation "𝕊" => Submodule.span ℂ (M L hL W hW fricke hfricke jf hjf K : Set (ℍ → ℂ))
local notation "𝕋" => Tw L hL W hW fricke hfricke jf hjf K hK σ

include hK in

theorem transport_pow_div (m p q : ℕ) (E J : ℍ → ℂ) (_hEhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E)
    (hEJ : ∀ τ : ℍ, E τ ^ p = J τ * Δ τ) (hJM : J ∈ 𝕄) (hJ0 : ∃ τ : ℍ, J τ ≠ 0)
    (hJinv : ∀ α : SL(2, ℤ), cw J α = J) (hE1 : Tendsto E atImInfty (𝓝 1))
    {v : ℍ → ℂ} (hv : v ∈ 𝕊) (hvinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, cw v γ = v)
    (hvpb : ∀ α : SL(2, ℤ), IsBoundedAtImInfty (cw v α * Δ ^ m))
    (h : ∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ, (v τ * Δ τ ^ m) ^ p = E τ ^ (p * q) * G τ) :
    ∃ G' : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G' ∧
      ∀ τ : ℍ, (𝕋 v τ * Δ τ ^ m) ^ p = E τ ^ (p * q) * G' τ := by
  obtain ⟨G, hG, hGrel⟩ := h
  have hΔ : ∀ τ : ℍ, Δ τ ≠ 0 := disc_ne_zero
  have hΔm : ∀ τ : ℍ, Δ τ ^ m ≠ 0 := fun τ => pow_ne_zero _ (hΔ τ)

  let W₁ : ℍ → ℂ := fun τ => G τ * Δ τ ^ q / (Δ τ ^ m) ^ p
  have hW₁hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) W₁ := by
    have := mdifferentiable_div_disc_pow (hG.mul (mdifferentiable_disc.pow q)) (m * p)
    convert this using 1 <;> try with_reducible_and_instances rfl
    funext τ; simp only [W₁, pow_mul, Pi.mul_apply, Pi.pow_apply]
  have hvW : ∀ τ : ℍ, v τ ^ p = J τ ^ q * W₁ τ := by
    intro τ
    have e1 : v τ ^ p * (Δ τ ^ m) ^ p = J τ ^ q * Δ τ ^ q * G τ := by
      rw [← mul_pow, hGrel τ, pow_mul, hEJ τ, mul_pow]
    have hp : (Δ τ ^ m) ^ p ≠ 0 := pow_ne_zero _ (hΔm τ)
    simp only [W₁]
    field_simp
    linear_combination e1
  have hvWfun : v ^ p = J ^ q * W₁ := funext fun τ => by simp [hvW τ]

  have hW₁inv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, W₁ (γ • τ) = W₁ τ := by
    intro γ hγ
    have hzero : ∀ τ : ℍ, (cw W₁ γ - W₁) τ * (J ^ q) τ = 0 := by
      intro τ
      have h1 := congrArg (fun F => cw F γ) hvWfun
      try simp only at h1
      rw [show cw (v ^ p) γ = (cw v γ) ^ p from rfl, hvinv γ hγ, cw_mul_fun,
        show cw (J ^ q) γ = (cw J γ) ^ q from rfl, isFQ_Gamma_smul L hL W hW fricke hfricke jf hjf K hJM hγ] at h1
      have := congrFun h1 τ
      have h2 := congrFun hvWfun τ
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, cw_apply] at this h2 ⊢
      linear_combination h2 - this
    obtain ⟨τ₀, hτ₀⟩ := hJ0
    have hJq : (J ^ q) τ₀ ≠ 0 := by simpa using pow_ne_zero q hτ₀
    have := eq_zero_of_mul_eq_zero ((mdifferentiable_cw hW₁hol γ).sub hW₁hol) (hJM.1.pow q) hzero hJq
    intro τ
    have := congrFun this τ
    simpa [sub_eq_zero, cw_apply] using this
  have hW₁pb : ∀ α : SL(2, ℤ), ∃ r : ℕ, IsBoundedAtImInfty (cw W₁ α * Δ ^ r) := by
    intro α
    refine ⟨m * p, ?_⟩
    have hid : ∀ τ : ℍ, (cw W₁ α τ * (Δ τ ^ m) ^ p) * E τ ^ (p * q) =
        (cw v α τ * Δ τ ^ m) ^ p * Δ τ ^ q := by
      intro τ
      have h1 : (cw v α τ) ^ p = (cw J α τ) ^ q * cw W₁ α τ :=
        congrFun (congrArg (fun F => cw F α) hvWfun) τ
      rw [show cw J α τ = J τ from congrFun (hJinv α) τ] at h1
      rw [pow_mul, hEJ τ, mul_pow, mul_pow, h1]
      ring
    have hb : IsBoundedAtImInfty ((fun τ => cw W₁ α τ * (Δ τ ^ m) ^ p) * fun τ => E τ ^ (p * q)) := by
      have h3 : IsBoundedAtImInfty (fun τ => (cw v α τ * Δ τ ^ m) ^ p * Δ τ ^ q) :=
        (bdd_pow (hvpb α) p).mul (bdd_pow isBoundedAtImInfty_disc q)
      refine h3.congr' ?_ EventuallyEq.rfl
      exact Eventually.of_forall fun τ => (hid τ).symm
    have hE' : Tendsto (fun τ => E τ ^ (p * q)) atImInfty (𝓝 1) := by simpa using hE1.pow (p * q)
    have := bdd_of_mul_tendsto_one hb hE'
    convert this using 1 <;> try with_reducible_and_instances rfl
    funext τ; simp [pow_mul, cw_apply]
  have hW₁span : W₁ ∈ 𝕊 := mem_span_M L hL W hW fricke hfricke jf hjf K hK hW₁hol hW₁inv hW₁pb

  have hJq_mem : J ^ q ∈ 𝕄 := IsFQ.pow L hL W hW fricke hfricke jf hjf K hJM q
  have hTv : (𝕋 v) ^ p = J ^ q * 𝕋 W₁ := by
    rw [← Tw_pow hK σ hv p, hvWfun, Tw_mul hK σ (Submodule.subset_span hJq_mem) hW₁span, Tw_of_mem hK σ hJq_mem]
  refine ⟨fun τ => 𝕋 W₁ τ * (Δ τ ^ m) ^ p / Δ τ ^ q, ?_, fun τ => ?_⟩
  · have := mdifferentiable_div_disc_pow ((Tw_mdifferentiable hK σ hW₁span).mul ((mdifferentiable_disc.pow m).pow p)) q
    convert this using 1 <;> try with_reducible_and_instances rfl
  · have h1 := congrFun hTv τ
    simp only [Pi.pow_apply, Pi.mul_apply] at h1
    have hq0 : Δ τ ^ q ≠ 0 := pow_ne_zero _ (hΔ τ)
    rw [mul_pow, h1, pow_mul, hEJ τ, mul_pow]
    field_simp

include hK in

theorem isZero_Tw {u : ℍ → ℂ} (hu : u ∈ 𝕊) (r : ℕ) (hz : IsZeroAtImInfty (u * Δ ^ r)) :
    IsZeroAtImInfty (𝕋 u * Δ ^ r) := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  obtain ⟨m₀, hm₀⟩ := exists_common_ratAt hK e he
  have hΔ : ∀ τ : ℍ, Δ τ ≠ 0 := disc_ne_zero

  have gen_facts : ∀ (w : ℍ → ℂ), Nice N (r + m₀) w → (∀ γ ∈ CongruenceSubgroup.Gamma N, cw w γ = w) →
      let F : ℍ → ℂ := fun τ => w τ * Δ τ ^ r / Δ τ
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ Periodic (F ∘ ofComplex) N ∧
        IsBoundedAtImInfty (F * Δ ^ (m₀ + 1)) ∧ F * Δ = w * Δ ^ r ∧ F * Δ ^ (m₀ + 1) = w * Δ ^ (r + m₀) := by
    intro w hw hwinv F
    have hFeq : F = w * fun τ => Δ τ ^ r / Δ τ := by funext τ; simp only [F, Pi.mul_apply]; ring
    have hF1 : F * Δ = w * Δ ^ r := by
      funext τ; have hΔτ := hΔ τ; simp only [F, Pi.mul_apply, Pi.pow_apply]; field_simp
    have hF2 : F * Δ ^ (m₀ + 1) = w * Δ ^ (r + m₀) := by
      funext τ; have hΔτ := hΔ τ; simp only [F, Pi.mul_apply, Pi.pow_apply, pow_add, pow_one]; field_simp
    refine ⟨?_, ?_, ?_, hF1, hF2⟩
    · have hq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => Δ τ ^ r / Δ τ) := by
        have h' : (fun τ : ℍ => Δ τ ^ r / Δ τ) = (fun τ => (Δ ^ r : ℍ → ℂ) τ / Δ τ ^ 1) := by
          funext τ; simp
        rw [h']; exact mdifferentiable_div_disc_pow (mdifferentiable_disc.pow r) 1
      rw [hFeq]; exact hw.mdiff.mul hq
    · rw [hFeq]
      exact periodic_mul (periodic_of_Gamma_invariant hwinv)
        (periodic_ofComplex_natCast (periodic_disc_fun fun x => x ^ r / x) N)
    · rw [hF2]; exact hw.bdd
  have hM1 : 1 ≤ m₀ + 1 := Nat.le_add_left 1 m₀
  have hrat : ∀ i, RatAt N K (r + m₀) (e i) := hm₀ _ (Nat.le_add_left m₀ r)

  have huN : Nice N (r + m₀) (∑ i, c i • e i) := nice_sum c e hrat
  have huinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, cw (∑ i, c i • e i) γ = ∑ i, c i • e i := fun γ hγ =>
    Gamma_smul_of_mem_span (sum_smul_mem_span c e he) hγ
  obtain ⟨hFhol, hFper, hFbd, hF1, hF2⟩ := gen_facts _ huN huinv
  have hcoef := (WLight.isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le N hM1 hFhol hFper hFbd).1
    (by rw [hF1]; exact hz)
  rw [hF2] at hcoef

  have hTuN : Nice N (r + m₀) (𝕋 (∑ i, c i • e i)) := nice_Tw hK σ c e he hrat
  have hTuinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, cw (𝕋 (∑ i, c i • e i)) γ = 𝕋 (∑ i, c i • e i) :=
    fun γ hγ => Gamma_smul_of_mem_span (Tw_mem_span hK σ (sum_smul_mem_span c e he)) hγ
  obtain ⟨hFhol', hFper', hFbd', hF1', hF2'⟩ := gen_facts _ hTuN hTuinv
  have := (WLight.isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le N hM1 hFhol' hFper' hFbd').2
  rw [hF1', hF2'] at this
  refine this fun n' hn' => ?_
  rw [Tw_coeff hK σ c e he hrat, hcoef n' hn', map_zero]

variable (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
variable (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)

def Φ : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ] (ℍ → ℂ) where
  toFun f := fun τ => f τ * (E₄ τ ^ a * E₆ τ ^ b) / Δ τ ^ m
  map_add' f g := by funext τ; simp only [CuspForm.add_apply, Pi.add_apply]; ring
  map_smul' c f := by funext τ; simp only [CuspForm.IsGLPos.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem Φ_apply (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (τ : ℍ) :
    Φ Γ k a b m f τ = f τ * (E₄ τ ^ a * E₆ τ ^ b) / Δ τ ^ m := rfl

theorem Φ_mul_disc (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (τ : ℍ) :
    f τ * (E₄ τ ^ a * E₆ τ ^ b) = Φ Γ k a b m f τ * Δ τ ^ m := by
  rw [Φ_apply, div_mul_cancel₀ _ (pow_ne_zero _ (disc_ne_zero τ))]

theorem mdifferentiable_Φ (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Φ Γ k a b m f) :=
  mdifferentiable_div_disc_pow (f.holo'.mul ((mdifferentiable_E₄.pow a).mul (mdifferentiable_E₆.pow b))) m

include hΓ hk in

theorem crit_Φ (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    ((∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ,
        (Φ Γ k a b m f τ * Δ τ ^ m) ^ 3 = E₄ τ ^ (3 * a) * G τ) ∧
      (∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ,
        (Φ Γ k a b m f τ * Δ τ ^ m) ^ 2 = E₆ τ ^ (2 * b) * G τ) ∧
      (∀ A : SL(2, ℤ), IsZeroAtImInfty (((Φ Γ k a b m f) ∘ (A • ·)) * Δ ^ m)) ∧
      ∀ γ ∈ Γ, ∀ τ : ℍ, Φ Γ k a b m f (γ • τ) = Φ Γ k a b m f τ) := by
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  exact (CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff Γ k a b m hk (Φ Γ k a b m f)
    (mdifferentiable_Φ Γ k a b m f)).1 ⟨f, Φ_mul_disc Γ k a b m f⟩

include hΓ hk hK in
theorem Φ_mem_span (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : Φ Γ k a b m f ∈ 𝕊 := by
  obtain ⟨-, -, h₃, h₄⟩ := crit_Φ Γ hΓ k a b m hk f
  refine mem_span_M L hL W hW fricke hfricke jf hjf K hK (mdifferentiable_Φ Γ k a b m f)
    (fun γ hγ τ => h₄ γ (hΓ hγ) τ) fun α => ⟨m, (h₃ α).isBoundedAtImInfty⟩

include hΓ hk hK in

theorem exists_Φ_eq_Tw (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ f' : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k, Φ Γ k a b m f' = 𝕋 (Φ Γ k a b m f) := by
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  set v := Φ Γ k a b m f with hvdef
  obtain ⟨h₁, h₂, h₃, h₄⟩ := crit_Φ Γ hΓ k a b m hk f
  have hv : v ∈ 𝕊 := Φ_mem_span hK Γ hΓ k a b m hk f
  have hvinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, cw v γ = v := fun γ hγ => funext fun τ => h₄ γ (hΓ hγ) τ
  have hvpb : ∀ α : SL(2, ℤ), IsBoundedAtImInfty (cw v α * Δ ^ m) := fun α => (h₃ α).isBoundedAtImInfty

  have h₁' := transport_pow_div hK σ m 3 a (E₄ : ℍ → ℂ) jf mdifferentiable_E₄ (E₄_cube_eq jf hjf)
    (isFQ_jf L hL W hW fricke hfricke jf hjf K) (exists_jf_ne_zero jf hjf) (cw_jf jf hjf) tendsto_E₄ hv hvinv hvpb h₁
  have hJ : (fun τ : ℍ => jf τ - 1728) ∈ 𝕄 := by
    have h1 := (isFQ_jf L hL W hW fricke hfricke jf hjf K).sub L hL W hW fricke hfricke jf hjf K
      (isFQ_const L hL W hW fricke hfricke jf hjf K (algebraMap ℚ K 1728))
    have h1728 : ((algebraMap ℚ K 1728 : K) : ℂ) = 1728 := by
      rw [eq_ratCast, SubfieldClass.coe_ratCast]; norm_num
    have h2 : (jf - fun _ : ℍ => ((algebraMap ℚ K 1728 : K) : ℂ)) = fun τ => jf τ - 1728 := by
      funext τ; simp only [Pi.sub_apply, h1728]
    rw [h2] at h1
    exact h1
  have h₂' := transport_pow_div hK σ m 2 b (E₆ : ℍ → ℂ) (fun τ => jf τ - 1728) mdifferentiable_E₆
    (E₆_sq_eq jf hjf) hJ (exists_jf_sub_ne_zero jf hjf)
    (fun α => funext fun τ => by simp only [cw_apply]; rw [jf_smul jf hjf]) tendsto_E₆ hv hvinv hvpb h₂

  have h₃' : ∀ A : SL(2, ℤ), IsZeroAtImInfty (((𝕋 v) ∘ (A • ·)) * Δ ^ m) := by
    intro A
    have : ((𝕋 v) ∘ (A • ·)) = cw (𝕋 v) A := rfl
    rw [this, ← Tw_cw hK σ hv A]
    exact isZero_Tw hK σ (cw_mem_span hv A) m (h₃ A)

  have h₄' : ∀ γ ∈ Γ, ∀ τ : ℍ, 𝕋 v (γ • τ) = 𝕋 v τ := by
    intro γ hγ τ
    have hinv : cw v γ = v := funext fun τ => h₄ γ hγ τ
    have := Tw_cw hK σ hv γ
    rw [hinv] at this
    have := congrFun this τ
    simpa [cw_apply] using this.symm
  obtain ⟨f', hf'⟩ := (CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff Γ k a b m hk (𝕋 v)
    (Tw_mdifferentiable hK σ hv)).2 ⟨h₁', h₂', h₃', h₄'⟩
  refine ⟨f', funext fun τ => ?_⟩
  rw [Φ_apply, hf' τ, mul_div_assoc, div_self (pow_ne_zero _ (disc_ne_zero τ)), mul_one]

end Stability

section Final

variable {L hL W hW fricke hfricke jf hjf K}
variable (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
variable (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)

local notation "𝕄" => M L hL W hW fricke hfricke jf hjf K
local notation "𝕊" => Submodule.span ℂ (M L hL W hW fricke hfricke jf hjf K : Set (ℍ → ℂ))

theorem exists_Efun_ne_zero : ∃ τ : ℍ, E₄ τ ^ a * E₆ τ ^ b ≠ 0 := by
  obtain ⟨τ₄, h₄⟩ := exists_E₄_ne_zero
  by_contra h
  push Not at h
  have hprod : ∀ τ : ℍ, E₄ τ = 0 ∨ E₆ τ = 0 := fun τ =>
    (mul_eq_zero.1 (h τ)).imp eq_zero_of_pow_eq_zero eq_zero_of_pow_eq_zero
  have hmul : ∀ τ : ℍ, E₆ τ * E₄ τ = 0 := fun τ => by
    rcases hprod τ with h0 | h0 <;> simp [h0]
  have := eq_zero_of_mul_eq_zero mdifferentiable_E₆ mdifferentiable_E₄ hmul h₄
  obtain ⟨τ₆, h₆⟩ := exists_E₆_ne_zero
  exact h₆ (by simpa using congrFun this τ₆)

theorem Φ_injective : Function.Injective (Φ Γ k a b m) := by
  intro f g hfg
  have h : ∀ τ : ℍ, (⇑(f - g) : ℍ → ℂ) τ * (E₄ τ ^ a * E₆ τ ^ b) = 0 := by
    intro τ
    have := congrFun hfg τ
    rw [Φ_apply, Φ_apply, div_left_inj' (pow_ne_zero _ (disc_ne_zero τ))] at this
    simp only [CuspForm.sub_apply, sub_mul, this, sub_self]
  obtain ⟨τ₀, hτ₀⟩ := exists_Efun_ne_zero a b
  have hz := eq_zero_of_mul_eq_zero (f - g).holo' ((mdifferentiable_E₄.pow a).mul (mdifferentiable_E₆.pow b))
    (fun τ => by simpa using h τ) (τ₀ := τ₀) (by simpa using hτ₀)
  have : f - g = 0 := DFunLike.ext _ _ fun τ => by simpa using congrFun hz τ
  exact sub_eq_zero.1 this

include L hL W hW hfricke hjf hΓ hk hK in

theorem main :
    Submodule.span ℂ {f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k |
      ∃ P Q : MvPolynomial (Idx N) ℂ,
        (∀ mo, P.coeff mo ∈ K) ∧ (∀ mo, Q.coeff mo ∈ K) ∧
        MvPolynomial.aeval (gen fricke jf) Q ≠ 0 ∧
        ∀ τ : ℍ, f τ * (E₄ τ ^ a * E₆ τ ^ b) * MvPolynomial.aeval (gen fricke jf) Q τ =
          Δ τ ^ m * MvPolynomial.aeval (gen fricke jf) P τ} = ⊤ := by
  classical
  set S : Set (CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) := {f |
      ∃ P Q : MvPolynomial (Idx N) ℂ,
        (∀ mo, P.coeff mo ∈ K) ∧ (∀ mo, Q.coeff mo ∈ K) ∧
        MvPolynomial.aeval (gen fricke jf) Q ≠ 0 ∧
        ∀ τ : ℍ, f τ * (E₄ τ ^ a * E₆ τ ^ b) * MvPolynomial.aeval (gen fricke jf) Q τ =
          Δ τ ^ m * MvPolynomial.aeval (gen fricke jf) P τ} with hSdef
  rw [eq_top_iff]
  rintro f -

  let V : Submodule ℂ (ℍ → ℂ) := LinearMap.range (Φ Γ k a b m)
  have hVle : V ≤ 𝕊 := by
    rintro _ ⟨g, rfl⟩; exact Φ_mem_span hK Γ hΓ k a b m hk g
  have hstab : ∀ (σ : ℂ ≃ₐ[K] ℂ) (v : ℍ → ℂ), v ∈ V →
      ∃ (s : Finset (ℍ → ℂ)) (c : (ℍ → ℂ) → ℂ), (↑s : Set (ℍ → ℂ)) ⊆ (𝕄 : Set (ℍ → ℂ)) ∧
        v = ∑ w ∈ s, c w • w ∧ (∑ w ∈ s, σ (c w) • w) ∈ V := by
    rintro σ _ ⟨g, rfl⟩
    obtain ⟨cf, hsupp, hsum⟩ := Submodule.mem_span_set.1 (hVle ⟨g, rfl⟩)
    refine ⟨cf.support, cf, hsupp, ?_, ?_⟩
    · rw [← hsum]; rfl
    · have hrep : (Φ Γ k a b m g : ℍ → ℂ) = ∑ i : ↥cf.support, cf i • (i : ℍ → ℂ) := by
        rw [← hsum, Finsupp.sum, ← Finset.sum_coe_sort]
      have hT : Tw L hL W hW fricke hfricke jf hjf K hK σ (Φ Γ k a b m g) = ∑ w ∈ cf.support, σ (cf w) • w := by
        rw [hrep, Tw_rep hK σ (fun i : ↥cf.support => cf i) (fun i => (i : ℍ → ℂ)) (fun i => hsupp i.2),
          Finset.sum_coe_sort cf.support (fun w => σ (cf w) • w)]
      obtain ⟨g', hg'⟩ := exists_Φ_eq_Tw hK σ Γ hΓ k a b m hk g
      rw [← hT, ← hg']
      exact ⟨g', rfl⟩
  have G1 : ∀ c : ℂ, (∀ σ : ℂ ≃ₐ[K] ℂ, σ c = c) → ∃ x : K, algebraMap K ℂ x = c := by
    intro c hc
    by_contra hnot
    have hc' : c ∉ Set.range (algebraMap K ℂ) := fun ⟨x, hx⟩ => hnot ⟨x, hx⟩
    obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_algEquiv_apply_ne_of_notMem_range (F := K) (E := ℂ) hc'
    exact hσ (hc σ)
  have hdesc := WLight.span_inter_rational_of_twist_stable K 𝕄 (M_flat L hL W hW fricke hfricke jf hjf hK)
    V hVle hstab G1 (v := Φ Γ k a b m f) ⟨f, rfl⟩

  have hsub : {y : ℍ → ℂ | y ∈ V ∧ y ∈ 𝕄} ⊆ (Φ Γ k a b m) '' S := by
    rintro y ⟨⟨g, rfl⟩, hyM⟩
    refine ⟨g, ?_, rfl⟩
    obtain ⟨-, P, Q, hQ, hGQ⟩ := hyM
    refine ⟨MvPolynomial.map (algebraMap K ℂ) P, MvPolynomial.map (algebraMap K ℂ) Q, coeff_map_mem P,
      coeff_map_mem Q, hQ, fun τ => ?_⟩
    have h1 := congrFun hGQ τ
    simp only [Pi.mul_apply] at h1
    change g τ * (E₄ τ ^ a * E₆ τ ^ b) * evK fricke jf K Q τ = Δ τ ^ m * evK fricke jf K P τ
    rw [Φ_mul_disc Γ k a b m g τ, ← h1]
    ring
  have h1 : (Φ Γ k a b m f : ℍ → ℂ) ∈ (Submodule.span ℂ S).map (Φ Γ k a b m) := by
    rw [Submodule.map_span]; exact Submodule.span_mono hsub hdesc
  obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.1 h1
  rw [← Φ_injective Γ k a b m hgf]
  exact hg

end Final

end Params

end FrickeSpan
p2m_reactivate "P2MW.S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.FrickeSpan"

end
p2m_reactivate "P2MW.S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.FrickeSpan"

open Complex Real UpperHalfPlane
open scoped MatrixGroups ModularForm

theorem solution
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m) :
    Submodule.span ℂ {f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k |
      ∃ P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ,
        (∀ mo, P.coeff mo ∈ K) ∧ (∀ mo, Q.coeff mo ∈ K) ∧
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) Q ≠ 0 ∧
        ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
            MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
              o.elim jf fun v => fricke v.1) Q τ =
          ModularForm.discriminant τ ^ m *
            MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
              o.elim jf fun v => fricke v.1) P τ} = ⊤ :=
  FrickeSpan.main (L := L) (hL := hL) (W := W) (hW := hW) (hfricke := hfricke) (hjf := hjf) hK Γ hΓ k a b m hk

end S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top
end P2MW
export P2MW.S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top (solution)
