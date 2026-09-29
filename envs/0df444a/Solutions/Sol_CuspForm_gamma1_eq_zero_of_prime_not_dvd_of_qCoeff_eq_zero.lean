-- Prove2me | solution 1 for CuspForm.gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/120a5a8c-8813-5120-8be0-60c2cf80b5c8

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"

set_option autoImplicit false
set_option maxHeartbeats 3200000

p2m_open "CongruenceSubgroup ModularForm UpperHalfPlane Filter Function Complex Function.Complex"
open scoped ModularForm UpperHalfPlane MatrixGroups Real

noncomputable section

namespace SupportVanishing

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {N p : ℕ} {k : ℤ}

def transGL (p : ℕ) : GL (Fin 2) ℝ := upperTriangularGL 1 ((p : ℝ)⁻¹) 1 (by norm_num)

def lowGL (p : ℕ) (hp : p ≠ 0) : GL (Fin 2) ℝ := upperTriangularGL 1 0 p (by simpa using hp)

@[scoped simp] theorem val_transGL (p : ℕ) :
    ((transGL p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (p : ℝ)⁻¹; 0, 1] := rfl

@[scoped simp] theorem val_lowGL (p : ℕ) (hp : p ≠ 0) :
    ((lowGL p hp : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), 0; 0, (p : ℝ)] := rfl

theorem det_transGL (p : ℕ) : ((transGL p).det : ℝ) = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_transGL, Matrix.det_fin_two_of]; ring

theorem det_lowGL (p : ℕ) (hp : p ≠ 0) : ((lowGL p hp).det : ℝ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_lowGL, Matrix.det_fin_two_of]; ring

@[scoped simp] theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

theorem val_mapGL_eq (g : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![((g 0 0 : ℤ) : ℝ), ((g 0 1 : ℤ) : ℝ); ((g 1 0 : ℤ) : ℝ), ((g 1 1 : ℤ) : ℝ)] := by
  ext i j
  rw [mapGL_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem val_transGL_pow (p : ℕ) (hp : p ≠ 0) (n : ℕ) :
    ((transGL p ^ n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (n : ℝ) * (p : ℝ)⁻¹; 0, 1] := by
  induction n with
  | zero => rw [pow_zero]; ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih, val_transGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem transGL_smul (p : ℕ) (τ : ℍ) : transGL p • τ = ((p : ℝ)⁻¹) +ᵥ τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [det_transGL]; exact one_pos), coe_vadd]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_transGL]
  ring

theorem slash_transGL_apply (p : ℕ) (f : ℍ → ℂ) (τ : ℍ) : (f ∣[k] transGL p) τ = f (transGL p • τ) := by
  rw [ModularForm.slash_apply]
  have hσ : UpperHalfPlane.σ (transGL p) = .refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, if_pos (by rw [det_transGL]; exact one_pos)]
  rw [hσ, det_transGL]
  simp [UpperHalfPlane.denom, val_transGL]

theorem slash_lowGL_slash_heckeDiagMatrix (hp : p ≠ 0) (f : ℍ → ℂ) :
    (f ∣[k] lowGL p hp) ∣[k] heckeDiagMatrix p = ((p : ℂ) ^ (k - 2)) • f := by
  have hprod : lowGL p hp * heckeDiagMatrix p
      = Matrix.GeneralLinearGroup.mkOfDetNeZero ((p : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; positivity) := by
    ext i j
    rw [Units.val_mul, val_lowGL, val_heckeDiagMatrix hp]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]
  rw [← SlashAction.slash_mul, hprod]
  funext τ
  rw [ModularForm.slash_apply, Pi.smul_apply, smul_eq_mul]
  have hdet : ((Matrix.GeneralLinearGroup.mkOfDetNeZero ((p : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; positivity)).det : ℝ)
      = (p : ℝ) ^ 2 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    simp [Matrix.det_smul, Fintype.card_fin]
  have hdetpos : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  have hσ : UpperHalfPlane.σ (Matrix.GeneralLinearGroup.mkOfDetNeZero ((p : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; positivity)) = .refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, if_pos (by rw [hdet]; exact hdetpos)]
  have hsmul : (Matrix.GeneralLinearGroup.mkOfDetNeZero ((p : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; positivity)) • τ = τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [hdet]; exact hdetpos)]
    have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, Matrix.smul_apply]
    field_simp
  rw [hσ, hdet, hsmul]
  simp only [ContinuousAlgEquiv.refl_apply]
  have hden : UpperHalfPlane.denom (Matrix.GeneralLinearGroup.mkOfDetNeZero
      ((p : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; positivity)) (τ : ℂ) = p := by
    simp [UpperHalfPlane.denom, Matrix.smul_apply]
  rw [hden]
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [abs_of_pos hdetpos]
  push_cast
  rw [← zpow_natCast, ← zpow_mul, mul_assoc, ← zpow_add₀ hp', mul_comm]
  congr 2
  push_cast
  ring

section Trans

variable [NeZero N]

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  simp [Gamma1_mem, ModularGroup.T]

theorem periodic_of_slash_T {F : ℍ → ℂ}
    (h : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = F) :
    Periodic (F ∘ ofComplex) 1 := by
  have hT : ∀ τ : ℍ, F ((1 : ℝ) +ᵥ τ) = F τ := by
    intro τ
    have := congrFun h τ
    change (F ∣[k] ModularGroup.T) τ = F τ at this
    rw [SL_slash_apply] at this
    rw [← modular_T_smul]
    rw [← this]
    simp [denom, ModularGroup.T]
  intro w
  by_cases hw : 0 < w.im
  · have : 0 < (w + 1).im := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert hT ⟨w, hw⟩ using 2
    ext
    simp [add_comm]
  · have hw : w.im ≤ 0 := le_of_not_gt hw
    have : (w + 1).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

theorem apply_vadd_eq (hp : p ≠ 0) (f : CuspForm Γ₁(N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = 0) (τ : ℍ) :
    f (((p : ℝ)⁻¹) +ᵥ τ) = f τ := by
  have hgT : (⇑f : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = ⇑f :=
    SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ (T_mem_Gamma1 N))
  have hper : Periodic (⇑f ∘ ofComplex) 1 := periodic_of_slash_T hgT
  have hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑f) := f.holo'
  have hbdd : IsBoundedAtImInfty (⇑f) := ModularFormClass.bdd_at_infty f
  have h1 := UpperHalfPlane.hasSum_qExpansion one_pos hper hhol hbdd τ
  have h2 := UpperHalfPlane.hasSum_qExpansion one_pos hper hhol hbdd (((p : ℝ)⁻¹) +ᵥ τ)

  set ζ : ℂ := Complex.exp (2 * π * Complex.I * (p : ℂ)⁻¹) with hζ
  have hq : Periodic.qParam 1 ((((p : ℝ)⁻¹) +ᵥ τ : ℍ) : ℂ) = Periodic.qParam 1 (τ : ℂ) * ζ := by
    rw [coe_vadd, Periodic.qParam, Periodic.qParam, hζ, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hζp : ζ ^ p = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
    rw [show (p : ℂ) * (2 * π * Complex.I * (p : ℂ)⁻¹) = (1 : ℕ) * (2 * π * Complex.I) by
      field_simp; push_cast; ring]
    exact Complex.exp_nat_mul_two_pi_mul_I 1
  have hterm : (fun m : ℕ => (qExpansion 1 (⇑f)).coeff m • Periodic.qParam 1 ((((p : ℝ)⁻¹) +ᵥ τ : ℍ) : ℂ) ^ m)
      = fun m : ℕ => (qExpansion 1 (⇑f)).coeff m • Periodic.qParam 1 (τ : ℂ) ^ m := by
    funext m
    by_cases hpm : p ∣ m
    · obtain ⟨r, rfl⟩ := hpm
      rw [hq, mul_pow, pow_mul, pow_mul, hζp, one_pow, mul_one]
    · have h0 : (qExpansion 1 (⇑f)).coeff m = 0 := hf m hpm
      rw [h0, zero_smul, zero_smul]
  rw [hterm] at h2
  exact h2.unique h1

theorem slash_transGL_eq (hp : p ≠ 0) (f : CuspForm Γ₁(N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = 0) :
    (⇑f : ℍ → ℂ) ∣[k] transGL p = ⇑f := by
  funext τ
  rw [slash_transGL_apply, transGL_smul, apply_vadd_eq hp f hf τ]

theorem slash_transGL_pow_eq (hp : p ≠ 0) (f : CuspForm Γ₁(N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = 0) (n : ℕ) :
    (⇑f : ℍ → ℂ) ∣[k] (transGL p ^ n) = ⇑f := by
  induction n with
  | zero => rw [pow_zero, SlashAction.slash_one]
  | succ n ih => rw [pow_succ, SlashAction.slash_mul, ih, slash_transGL_eq hp f hf]

end Trans

section Cocycle

theorem exists_cocycle (hp : p.Prime) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) :
    ∃ (x y : ℕ) (γ'' : SL(2, ℤ)), γ'' ∈ Gamma1 N ∧
      γ'' 0 0 = γ 0 0 - x * γ 1 0 ∧ γ'' 1 0 = p * γ 1 0 ∧ γ'' 1 1 = γ 1 1 - y * γ 1 0 ∧
      (p : ℤ) * γ'' 0 1 = γ 0 1 - x * γ 1 1 - y * (γ 0 0 - x * γ 1 0) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe; rwa [Matrix.det_fin_two] at h

  obtain ⟨x, hx⟩ : ∃ x : ℕ, ¬ (p : ℤ) ∣ γ 0 0 - x * γ 1 0 := by
    by_cases ha : (p : ℤ) ∣ γ 0 0
    · refine ⟨1, ?_⟩
      intro h
      have hc : (p : ℤ) ∣ γ 1 0 := by
        have : (p : ℤ) ∣ γ 0 0 - (γ 0 0 - 1 * γ 1 0) := dvd_sub ha h
        simpa using this
      have : (p : ℤ) ∣ 1 := by
        rw [← hdet]
        exact dvd_sub (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hc _)
      exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
    · exact ⟨0, by simpa using ha⟩
  set u : ℤ := γ 0 0 - x * γ 1 0 with hu
  set b' : ℤ := γ 0 1 - x * γ 1 1 with hb'
  have hu0 : ((u : ℤ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

  set y : ℕ := (((b' : ℤ) : ZMod p) * ((u : ℤ) : ZMod p)⁻¹).val with hy
  have hyc : ((y : ℕ) : ZMod p) = ((b' : ℤ) : ZMod p) * ((u : ℤ) : ZMod p)⁻¹ := by
    rw [hy, ZMod.natCast_zmod_val]
  have hdiv : (p : ℤ) ∣ b' - y * u := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hyc, mul_assoc, inv_mul_cancel₀ hu0, mul_one, sub_self]
  obtain ⟨r, hr⟩ := hdiv
  have hdet'' : Matrix.det !![u, r; (p : ℤ) * γ 1 0, γ 1 1 - y * γ 1 0] = 1 := by
    rw [Matrix.det_fin_two_of]
    have hr' : (p : ℤ) * r = b' - y * u := hr.symm
    linear_combination hdet - γ 1 0 * hr'
  refine ⟨x, y, ⟨_, hdet''⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Gamma1_mem] at hγ ⊢
    obtain ⟨ha, he, hc⟩ := hγ
    refine ⟨?_, ?_, ?_⟩
    · show ((u : ℤ) : ZMod N) = 1
      rw [hu]; push_cast; rw [ha, hc]; ring
    · show ((γ 1 1 - y * γ 1 0 : ℤ) : ZMod N) = 1
      push_cast; rw [he, hc]; ring
    · show (((p : ℤ) * γ 1 0 : ℤ) : ZMod N) = 0
      push_cast; rw [hc]; ring
  · rfl
  · rfl
  · rfl
  · show (p : ℤ) * r = _
    rw [← hr]

theorem lowGL_mul_eq (hp : p ≠ 0) {γ γ'' : SL(2, ℤ)} {x y : ℕ}
    (h00 : γ'' 0 0 = γ 0 0 - x * γ 1 0) (h10 : γ'' 1 0 = p * γ 1 0) (h11 : γ'' 1 1 = γ 1 1 - y * γ 1 0)
    (h01 : (p : ℤ) * γ'' 0 1 = γ 0 1 - x * γ 1 1 - y * (γ 0 0 - x * γ 1 0)) :
    lowGL p hp * Matrix.SpecialLinearGroup.mapGL ℝ γ
      = transGL p ^ x * Matrix.SpecialLinearGroup.mapGL ℝ γ'' * transGL p ^ y * lowGL p hp := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  have h00' : ((γ'' 0 0 : ℤ) : ℝ) = γ 0 0 - x * γ 1 0 := by exact_mod_cast h00
  have h10' : ((γ'' 1 0 : ℤ) : ℝ) = p * γ 1 0 := by exact_mod_cast h10
  have h11' : ((γ'' 1 1 : ℤ) : ℝ) = γ 1 1 - y * γ 1 0 := by exact_mod_cast h11
  have h01' : (p : ℝ) * ((γ'' 0 1 : ℤ) : ℝ) = γ 0 1 - x * γ 1 1 - y * (γ 0 0 - x * γ 1 0) := by
    exact_mod_cast h01
  have h01'' : ((γ'' 0 1 : ℤ) : ℝ) = (p : ℝ)⁻¹ * (γ 0 1 - x * γ 1 1 - y * (γ 0 0 - x * γ 1 0)) := by
    rw [← h01', ← mul_assoc, inv_mul_cancel₀ hp', one_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, val_lowGL, val_transGL_pow p hp,
    val_transGL_pow p hp, val_mapGL_eq, val_mapGL_eq, h00', h10', h11', h01'']
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

end Cocycle

section Main

variable [NeZero N]

def lowGLQ (hp : p ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), 0; 0, (p : ℚ)]
    (by rw [Matrix.det_fin_two_of]; simp; exact_mod_cast hp)

theorem lowGLQ_map (hp : p ≠ 0) : (lowGLQ hp).map (Rat.castHom ℝ) = lowGL p hp := by
  apply Units.ext
  rw [val_lowGL]
  show (lowGLQ hp : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ) = _
  unfold lowGLQ
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem isCusp_smul_of_rat {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) {g : GL (Fin 2) ℝ}
    (gQ : GL (Fin 2) ℚ) (hg : gQ.map (Rat.castHom ℝ) = g) : IsCusp (g • c) 𝒮ℒ := by
  subst hg
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  exact ⟨gQ • c₀, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

def lowForm (hp : p.Prime) (f : CuspForm Γ₁(N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = 0) : CuspForm Γ₁(N) k :=
  { toFun := (⇑f : ℍ → ℂ) ∣[k] lowGL p hp.ne_zero
    slash_action_eq' := by
      intro A hA
      obtain ⟨γ, hγ, rfl⟩ := hA
      obtain ⟨x, y, γ'', hγ'', h00, h10, h11, h01⟩ := exists_cocycle (N := N) hp hγ
      rw [← SlashAction.slash_mul, lowGL_mul_eq hp.ne_zero h00 h10 h11 h01, SlashAction.slash_mul,
        SlashAction.slash_mul, SlashAction.slash_mul, slash_transGL_pow_eq hp.ne_zero f hf x,
        SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ''),
        slash_transGL_pow_eq hp.ne_zero f hf y]
    holo' := f.holo'.slash k _
    zero_at_cusps' := by
      intro c hc
      refine OnePoint.IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps f ?_)
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
      exact isCusp_smul_of_rat hc (lowGLQ hp.ne_zero) (lowGLQ_map hp.ne_zero) }

theorem coe_lowForm (hp : p.Prime) (f : CuspForm Γ₁(N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = 0) :
    (⇑(lowForm hp f hf) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] lowGL p hp.ne_zero := rfl

theorem main (hp : p.Prime) (hpN : ¬ p ∣ N) (f : CuspForm Γ₁(N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = 0) : f = 0 := by
  set g := lowForm hp f hf with hg
  have hgδ : (⇑g : ℍ → ℂ) ∣[k] heckeDiagMatrix p = ((p : ℂ) ^ (k - 2)) • (⇑f : ℍ → ℂ) := by
    rw [hg, coe_lowForm, slash_lowGL_slash_heckeDiagMatrix hp.ne_zero]
  have hy : ∀ γ ∈ Γ₁(N), ((⇑g : ℍ → ℂ) ∣[k] heckeDiagMatrix p) ∣[k] γ = (⇑g : ℍ → ℂ) ∣[k] heckeDiagMatrix p := by
    intro γ hγ
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    rw [hgδ]
    change (((p : ℂ) ^ (k - 2)) • (⇑f : ℍ → ℂ)) ∣[k] γ₀ = _
    rw [ModularForm.SL_smul_slash]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ₀)
  have hg0 : g = 0 := CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1 hp hpN k g hy
  have hf0 : ((p : ℂ) ^ (k - 2)) • (⇑f : ℍ → ℂ) = 0 := by
    rw [← hgδ, hg0]
    change ((0 : ℍ → ℂ)) ∣[k] heckeDiagMatrix p = 0
    exact SlashAction.zero_slash k _
  have hpk : ((p : ℂ) ^ (k - 2)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hf0' : (⇑f : ℍ → ℂ) = 0 := by
    have := congrArg (fun F : ℍ → ℂ => ((p : ℂ) ^ (k - 2))⁻¹ • F) hf0
    simpa [smul_smul, inv_mul_cancel₀ hpk] using this
  exact DFunLike.ext f 0 fun τ => congrFun hf0' τ

end Main

end SupportVanishing
p2m_reactivate "P2MW.S_CuspForm_gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero.SupportVanishing"

end
p2m_reactivate "P2MW.S_CuspForm_gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero.SupportVanishing"

open scoped MatrixGroups in
theorem solution
    {N p : ℕ} [NeZero N] (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma1 N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = 0) : f = 0 :=
  SupportVanishing.main hp hpN f hf

end S_CuspForm_gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
end P2MW
export P2MW.S_CuspForm_gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero (solution)
