-- Prove2me | solution 1 for CuspForm.HasNebentypus.exists_isFiniteOrderHeckeChar_centralScalar_mul_of_isAdelicLiftOfGamma1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e2fff075-2fab-59ac-b2d3-b7cb9c12a802

import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_DirichletCharacter_isFiniteOrderHeckeChar_dirichletIdeleChar
import Theorems.Thm_DirichletCharacter_admitsModulus_dirichletIdeleChar
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_apply_centralScalar_mul_eq_of_forall_snd_eq_one_of_archCoord_pos
import Theorems.Thm_RatIdele_sub_natCast_val_unitResidue_mem_idealBall_of_forall_valued_eq_one
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_apply_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_HasNebentypus_exists_isFiniteOrderHeckeChar_centralScalar_mul_of_isAdelicLiftOfGamma1

set_option autoImplicit false

open NumberField AutomorphicForm
open NumberField.AdelicLevel AdelicDock IsDedekindDomain

namespace R2cGlue

noncomputable section

theorem glpair_ext {g h : AdelicGL2 (𝓞 ℚ) ℚ}
    (ha : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ h)
    (hf : glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ h) : g = h := by
  ext i j
  refine Prod.ext ?_ ?_
  · exact congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing ℚ) =>
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j) ha
  · exact congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) hf

theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    centralScalar (𝓞 ℚ) ℚ z * g = g * centralScalar (𝓞 ℚ) ℚ z := by
  ext : 1
  rw [Units.val_mul, Units.val_mul]
  exact Matrix.scalar_commute (z : AdeleRing (𝓞 ℚ) ℚ) (fun r' => mul_comm _ _)
    ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))

def prin (q : ℚˣ) : (AdeleRing (𝓞 ℚ) ℚ)ˣ := Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) q

theorem prin_inv (q : ℚˣ) : prin q⁻¹ = (prin q)⁻¹ := by unfold prin; exact map_inv _ q

theorem centralScalar_prin (q : ℚˣ) :
    centralScalar (𝓞 ℚ) ℚ (prin q) = globalPoints (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) q) := by
  ext i j
  simp only [globalPoints, centralScalar, prin, Matrix.GeneralLinearGroup.map, Units.coe_map,
    Matrix.GeneralLinearGroup.scalar, MonoidHom.coe_coe]
  by_cases h : i = j <;> simp [h, Matrix.algebraMap_matrix_apply]

theorem glFin_centralScalar_entry (w : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (i j : Fin 2) :
    ((glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ) w)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) _) i j
      = Matrix.diagonal (fun _ => (w : FiniteAdeleRing (𝓞 ℚ) ℚ)) i j := by
  rw [glFin_apply]
  show adeleFin (𝓞 ℚ) ℚ (Matrix.diagonal
    (fun _ => (finIncl (𝓞 ℚ) ℚ (w : FiniteAdeleRing (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ)) i j) = _
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    rfl
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, map_zero]

theorem finEmbed_scalar_eq_centralScalar (e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    finEmbed (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) e)
      = centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ) e) := by
  apply glpair_ext
  · rw [glArch_finEmbed]
    symm
    ext i j
    rw [glArch_apply]
    show adeleArch (𝓞 ℚ) ℚ (Matrix.diagonal
      (fun _ => (finIncl (𝓞 ℚ) ℚ (e : FiniteAdeleRing (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ)) i j)
      = ((1 : GL (Fin 2) (InfiniteAdeleRing ℚ)) : Matrix (Fin 2) (Fin 2) _) i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq]
      have h1 : adeleArch (𝓞 ℚ) ℚ (finIncl (𝓞 ℚ) ℚ (e : FiniteAdeleRing (𝓞 ℚ) ℚ)) = 1 := rfl
      rw [h1, Units.val_one, Matrix.one_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero, Units.val_one, Matrix.one_apply_ne h]
  · rw [glFin_finEmbed]
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [glFin_centralScalar_entry,
      show ((Matrix.GeneralLinearGroup.scalar (Fin 2) e :
          GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
        = Matrix.scalar (Fin 2) ((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            FiniteAdeleRing (𝓞 ℚ) ℚ) from rfl]
    by_cases h : i = j
    · subst h
      simp [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, h]

theorem scalar_mem_finiteLevelZero (L : Ideal (𝓞 ℚ)) (e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (he : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((e : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) e ∈ finiteLevelZero (𝓞 ℚ) ℚ L := by
  have hint : ∀ e' : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, (∀ v, Valued.v ((e' : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1) →
      IsLevelZeroMatrix (𝓞 ℚ) ℚ L ((Matrix.GeneralLinearGroup.scalar (Fin 2) e' :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
    intro e' he'
    have hval : ((Matrix.GeneralLinearGroup.scalar (Fin 2) e' : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = Matrix.scalar (Fin 2) (e' : FiniteAdeleRing (𝓞 ℚ) ℚ) := rfl
    refine ⟨fun i j => ?_, ?_⟩
    · rw [hval, Matrix.scalar_apply]
      by_cases h : i = j
      · subst h; rw [Matrix.diagonal_apply_eq]
        exact fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (he' v).le
      · rw [Matrix.diagonal_apply_ne _ h]; exact zero_mem_integralFiniteAdeles
    · rw [hval, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)]
      exact zero_mem_idealBall L
  refine ⟨hint e he, ?_⟩
  rw [← map_inv]
  exact hint e⁻¹ fun v => by
    have h1 := he v
    have hprod : ((e : FiniteAdeleRing (𝓞 ℚ) ℚ) v) * (((e⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
      rw [← coe_mul_apply, Units.mul_inv]; rfl
    have := congrArg Valued.v hprod
    rw [map_mul, map_one, h1, one_mul] at this
    exact this

theorem natGenerator_padicPlace (ℓ : ℕ) [Fact ℓ.Prime] :
    Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) (padicPlace ℓ) = ℓ :=
  congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨ℓ, Fact.out⟩)

end

end R2cGlue

open R2cGlue in
theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hε : CuspForm.HasNebentypus ε h)
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) :
    ∃ ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ,
      HeckeCharacter.IsFiniteOrderHeckeChar ℚ ω ∧
      HeckeCharacter.AdmitsModulus ℚ ω (AdelicDock.ratLevel M) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M →
        (ω (uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) = ε (ℓ : ZMod M)) ∧
      ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (x : AdelicGL2 (𝓞 ℚ) ℚ),
        Φ (centralScalar (𝓞 ℚ) ℚ z * x) = (ω z : ℂ) * Φ x := by
  classical
  have hM : M ≠ 0 := NeZero.ne M
  refine ⟨ε.dirichletIdeleChar, DirichletCharacter.isFiniteOrderHeckeChar_dirichletIdeleChar ε, ?_, ?_, ?_⟩
  ·
    exact DirichletCharacter.admitsModulus_dirichletIdeleChar ε
  ·
    intro ℓ hℓ hℓM
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hgen := natGenerator_padicPlace ℓ
    have hv : ¬ Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) (padicPlace ℓ) ∣ M := by rw [hgen]; exact hℓM
    have := DirichletCharacter.coe_dirichletIdeleChar_finIncl_localUnit_of_valued_exp_neg_one ε hv
      (uniformizerUnit ℚ (padicPlace ℓ)) (valued_uniformizerUnit ℚ (padicPlace ℓ))
    rw [hgen] at this
    exact this
  ·
    intro z x

    set q : ℚˣ := Units.mk0 (RatIdele.ρ z) (RatIdele.ρ_ne_zero z) with hq_def
    set z' : (AdeleRing (𝓞 ℚ) ℚ)ˣ := prin q⁻¹ * z with hz'_def
    set f : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := RatIdele.finPart z' with hf_def
    set a : (AdeleRing (𝓞 ℚ) ℚ)ˣ := z' * (Units.map (finIncl (𝓞 ℚ) ℚ) f)⁻¹ with ha_def
    have hz_split : z = prin q * (a * Units.map (finIncl (𝓞 ℚ) ℚ) f) := by
      rw [ha_def, inv_mul_cancel_right, hz'_def, prin_inv, mul_inv_cancel_left]

    have hz'2 : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((z' : AdeleRing (𝓞 ℚ) ℚ).2 v) = RatIdele.unitAt v z := by
      intro v
      rw [hz'_def, RatIdele.unitAt, Units.val_mul, prin, Units.coe_map, MonoidHom.coe_coe]
      show ((algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) ↑q⁻¹).2 v * (z : AdeleRing (𝓞 ℚ) ℚ).2 v = _
      rw [RatIdele.algebraMap_adeleRing_snd, Units.val_inv_eq_inv_val, map_inv₀, mul_comm]
      rfl
    have hfu : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((f : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
      intro v; rw [hf_def, RatIdele.finPart_apply, hz'2]; exact RatIdele.valued_unitAt v z
    have ha2 : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((a : AdeleRing (𝓞 ℚ) ℚ).2 v) = 1 := by
      intro v
      have hfv : ((Units.map (finIncl (𝓞 ℚ) ℚ) f : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 v = (z' : AdeleRing (𝓞 ℚ) ℚ).2 v := by
        rw [Units.coe_map, finIncl_apply_snd, hf_def, RatIdele.finPart_apply]
      have hmul : ((a : AdeleRing (𝓞 ℚ) ℚ).2 v) * ((Units.map (finIncl (𝓞 ℚ) ℚ) f : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 v
          = (z' : AdeleRing (𝓞 ℚ) ℚ).2 v := by
        rw [show ((a : AdeleRing (𝓞 ℚ) ℚ).2 v) * (((Units.map (finIncl (𝓞 ℚ) ℚ) f : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 v)
            = ((a * Units.map (finIncl (𝓞 ℚ) ℚ) f : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 v from rfl, ha_def, inv_mul_cancel_right]
      rw [hfv] at hmul
      have hne : (z' : AdeleRing (𝓞 ℚ) ℚ).2 v ≠ 0 := by
        intro h0; have := RatIdele.valued_unitAt v z; rw [← hz'2, h0, map_zero] at this; exact zero_ne_one this
      exact mul_right_cancel₀ hne (hmul.trans (one_mul _).symm)
    have hapos : 0 < RatIdele.archCoord a := by
      have h1 : RatIdele.archCoord a = RatIdele.archCoord z' := by
        rw [ha_def, RatIdele.archCoord_mul, ← map_inv, RatIdele.archCoord_finIncl, mul_one]
      have h2 : RatIdele.archCoord z' = RatIdele.archCoord z * ((RatIdele.ρ z : ℝ))⁻¹ := by
        rw [hz'_def, RatIdele.archCoord_mul, prin, RatIdele.archCoord_principal, Units.val_inv_eq_inv_val,
          Rat.cast_inv, mul_comm]
        rfl
      rw [h1, h2]
      have h3 := (RatIdele.ρ_spec z).2
      have hρ : (RatIdele.ρ z : ℝ) ≠ 0 := by exact_mod_cast RatIdele.ρ_ne_zero z
      have : RatIdele.archCoord z * (RatIdele.ρ z : ℝ)⁻¹ = (RatIdele.archCoord z * RatIdele.ρ z) * ((RatIdele.ρ z : ℝ)⁻¹) ^ 2 := by
        field_simp
      rw [this]
      exact mul_pos h3 (by positivity)

    set r : ZMod M := RatIdele.unitResidue M (Units.map (finIncl (𝓞 ℚ) ℚ) f) with hr_def
    have hd : ((Matrix.GeneralLinearGroup.scalar (Fin 2) f : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((r.val : ℤ) : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (ratLevel M) := by
      have hKR := RatIdele.sub_natCast_val_unitResidue_mem_idealBall_of_forall_valued_eq_one M f hfu
      have h11 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) f : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 = (f : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
        show Matrix.scalar (Fin 2) (f : FiniteAdeleRing (𝓞 ℚ) ℚ) 1 1 = _
        rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      rw [h11, Int.cast_natCast, map_natCast]
      exact hKR
    have hΦ4 : Φ (centralScalar (𝓞 ℚ) ℚ z * x) = (ε (r.val : ℤ))⁻¹ * Φ x := by
      rw [hz_split, map_mul, map_mul, centralScalar_prin, mul_assoc, mul_assoc, hΦ.left_inv,
        CuspForm.IsAdelicLiftOfGamma1.apply_centralScalar_mul_eq_of_forall_snd_eq_one_of_archCoord_pos hΦ hM a ha2 hapos,
        centralScalar_mul_comm, ← finEmbed_scalar_eq_centralScalar]
      exact CuspForm.IsAdelicLiftOfGamma1.apply_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero hε hΦ _
        (scalar_mem_finiteLevelZero (ratLevel M) f hfu) _ hd x

    have hω : ((ε.dirichletIdeleChar z : ℂˣ) : ℂ) = (ε r)⁻¹ := by
      rw [hz_split, map_mul, map_mul, Units.val_mul, Units.val_mul, prin, DirichletCharacter.dirichletIdeleChar_principal,
        DirichletCharacter.dirichletIdeleChar_eq_one_of_snd_eq_one_of_pos ε ha2 hapos, Units.val_one, one_mul, one_mul,
        DirichletCharacter.coe_dirichletIdeleChar_apply]
    rw [hΦ4, hω, Int.cast_natCast, ZMod.natCast_zmod_val]

end S_CuspForm_HasNebentypus_exists_isFiniteOrderHeckeChar_centralScalar_mul_of_isAdelicLiftOfGamma1
end P2MW
export P2MW.S_CuspForm_HasNebentypus_exists_isFiniteOrderHeckeChar_centralScalar_mul_of_isAdelicLiftOfGamma1 (solution)
