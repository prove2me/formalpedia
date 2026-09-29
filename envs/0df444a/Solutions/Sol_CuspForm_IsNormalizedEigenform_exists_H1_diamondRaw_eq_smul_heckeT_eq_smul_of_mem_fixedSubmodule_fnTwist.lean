-- Prove2me | solution 1 for CuspForm.IsNormalizedEigenform.exists_H1_diamondRaw_eq_smul_heckeT_eq_smul_of_mem_fixedSubmodule_fnTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e25c2e1d-d2b9-5576-9709-12266882fbb6

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.SlashActions
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul
import Theorems.Thm_CuspForm_IsAdelicLiftOf_levelZero_inv
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Theorems.Thm_HeckeCharacter_IsFiniteOrderHeckeChar_exists_dirichletIdeleChar_eq_of_admitsModulus
import Definitions.Def_ModularCurve_PeriodTransfer
import Mathlib.GroupTheory.Transfer
import Theorems.Thm_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt
import Definitions.Def_ModularCurve_PeriodMapBundled
import Theorems.Thm_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0
import Theorems.Thm_ModularCurve_Period_IsEquivariantPrimitive_isParabolicHom_periodHom
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_CuspForm_IsNormalizedEigenform_exists_H1_diamondRaw_eq_smul_heckeT_eq_smul_of_mem_fixedSubmodule_fnTwist

set_option autoImplicit false

namespace TwistedPeriodDescent

open NumberField AutomorphicForm LocalNewvector AdelicDock NumberField.AdelicLevel
open scoped MatrixGroups ModularForm

private noncomputable def chiSq (q : ℕ) [Fact q.Prime] (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : ℤ_[q]ˣ) : ℂ :=
  (ξ (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
      (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
        (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom
          (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) : ℂ) ^ 2

private theorem chiSq_def (q : ℕ) [Fact q.Prime] (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : ℤ_[q]ˣ) :
    chiSq q ξ u =
      (ξ (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
        (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
          (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom
            (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) : ℂ) ^ 2 :=
  rfl

private theorem chiSq_ne_zero (q : ℕ) [Fact q.Prime] (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : ℤ_[q]ˣ) :
    chiSq q ξ u ≠ 0 :=
  pow_ne_zero 2 (Units.ne_zero _)

variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private abbrev fn (y : AdelicSpan φ) : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := (AdelicSpan.toFn φ y).toFn

private def HasReading (y : AdelicSpan φ) (F : UpperHalfPlane → ℂ) : Prop :=
  ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 → LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
    fn y h = (F ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I

private noncomputable def slashSpanPos {M : ℕ} (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    Submodule ℂ (UpperHalfPlane → ℂ) :=
  Submodule.span ℂ (Set.range fun β : {β : GL (Fin 2) ℚ // 0 < ((Matrix.GeneralLinearGroup.det β : ℚˣ) : ℚ)} =>
    (⇑g) ∣[(2 : ℤ)] (β : GL (Fin 2) ℚ).map (Rat.castHom ℝ))

private theorem slash_map_mem_slashSpanPos {M : ℕ} (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (β : GL (Fin 2) ℚ)
    (hβ : 0 < ((Matrix.GeneralLinearGroup.det β : ℚˣ) : ℚ)) :
    (⇑g) ∣[(2 : ℤ)] β.map (Rat.castHom ℝ) ∈ slashSpanPos g :=
  Submodule.subset_span ⟨⟨β, hβ⟩, rfl⟩

end TwistedPeriodDescent

namespace TwistedPeriodDescent

open UpperHalfPlane
open scoped MatrixGroups ModularForm

private theorem apply_eq_apply_of_hasDerivAt_zero {D : ℂ → ℂ}
    (hD : ∀ τ : ℍ, HasDerivAt D 0 ↑τ) (z w : ℍ) : D ↑z = D ↑w := by
  have hmem : ∀ s : ℍ, (↑s : ℂ) ∈ {c : ℂ | 0 < c.im} := fun s => s.2
  refine isOpen_upperHalfPlaneSet.is_const_of_fderiv_eq_zero
    ((convex_halfSpace_im_gt 0).isPreconnected)
    (fun x hx => ((hD ⟨x, hx⟩).differentiableAt).differentiableWithinAt)
    (fun x hx => ?_) (hmem z) (hmem w)
  have h0 := ((hD ⟨x, hx⟩).hasFDerivAt).fderiv
  rw [Pi.zero_apply, h0]
  ext1
  simp

private theorem sub_eq_const_of_forall_hasDerivAt {Fp Gp : ℂ → ℂ} {f : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasDerivAt Fp (f τ) ↑τ) (hG : ∀ τ : ℍ, HasDerivAt Gp (f τ) ↑τ) :
    ∃ c : ℂ, ∀ τ : ℍ, Fp ↑τ - Gp ↑τ = c := by
  refine ⟨Fp ↑UpperHalfPlane.I - Gp ↑UpperHalfPlane.I, fun τ => ?_⟩
  exact apply_eq_apply_of_hasDerivAt_zero
    (D := fun z => Fp z - Gp z) (fun s => by simpa using (hF s).fun_sub (hG s)) τ UpperHalfPlane.I

private theorem slash_two_apply_of_det_pos (F : ℍ → ℂ) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (τ : ℍ) :
    (F ∣[(2 : ℤ)] g) τ = F (g • τ) * ((g.val.det : ℝ) : ℂ) / denom g τ ^ 2 := by
  have hdet : 0 < g.det.val := by rwa [Matrix.GeneralLinearGroup.val_det_apply]
  have hσ : UpperHalfPlane.σ g (F (g • τ)) = F (g • τ) := by
    rw [UpperHalfPlane.σ, if_pos hdet]
    rfl
  rw [ModularForm.slash_apply, hσ, abs_of_pos hdet, Matrix.GeneralLinearGroup.val_det_apply,
    show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one, zpow_neg, zpow_ofNat, div_eq_mul_inv]

private theorem hasDerivAt_comp_smul_of_det_pos {Gp F : ℍ → ℂ}
    (hGp : ∀ τ : ℍ, HasDerivAt (Gp ∘ ofComplex) (F τ) ↑τ) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => Gp (g • ofComplex z)) ((F ∣[(2 : ℤ)] g) τ) ↑τ := by
  have hfun : (fun z : ℂ => Gp (g • ofComplex z))
      = (Gp ∘ ofComplex) ∘ (fun z : ℂ => ((g • ofComplex z : ℍ) : ℂ)) := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply]
  have houter : HasDerivAt (Gp ∘ ofComplex) (F (g • τ))
      ((fun z : ℂ => ((g • ofComplex z : ℍ) : ℂ)) ↑τ) := by
    simpa only [ofComplex_apply] using hGp (g • τ)
  have hcomp := houter.comp (↑τ : ℂ) (hasStrictDerivAt_smul hg τ).hasDerivAt
  rw [← hfun] at hcomp
  convert hcomp using 1
  all_goals try rfl
  rw [slash_two_apply_of_det_pos F g hg τ]
  ring

private theorem hasDerivAt_comp_smul_ofComplex_of_det_pos {Gp F : ℍ → ℂ}
    (hGp : ∀ τ : ℍ, HasDerivAt (Gp ∘ ofComplex) (F τ) ↑τ) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (τ : ℍ) :
    HasDerivAt ((fun w : ℍ => Gp (g • w)) ∘ ofComplex) ((F ∣[(2 : ℤ)] g) τ) ↑τ := by
  have h : ((fun w : ℍ => Gp (g • w)) ∘ ofComplex) = fun z : ℂ => Gp (g • ofComplex z) := by
    funext z
    simp only [Function.comp_apply]
  rw [h]
  exact hasDerivAt_comp_smul_of_det_pos hGp g hg τ

private theorem det_mapGL_pos (γ : SL(2, ℤ)) : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ).val.det := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL, Units.val_one]
  exact one_pos

end TwistedPeriodDescent

open NumberField AdelicDock IsDedekindDomain

namespace TwistedPeriodDescent

namespace HeckeCosets

variable (p : ℕ) [hp : Fact p.Prime]

private noncomputable def repZ (i : Fin (p + 1)) : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
  if (i : ℕ) < p then !![1, ((i : ℕ) : ℤ_[p]); 0, (p : ℤ_[p])] else !![(p : ℤ_[p]), 0; 0, 1]

private theorem repZ_of_lt {i : Fin (p + 1)} (hi : (i : ℕ) < p) :
    repZ p i = !![1, ((i : ℕ) : ℤ_[p]); 0, (p : ℤ_[p])] := by
  simp [repZ, hi]

private theorem repZ_last : repZ p (Fin.last p) = !![(p : ℤ_[p]), 0; 0, 1] := by
  simp [repZ]

private theorem det_repZ (i : Fin (p + 1)) : (repZ p i).det = (p : ℤ_[p]) := by
  unfold repZ
  split_ifs <;> simp [Matrix.det_fin_two_of]

private theorem exists_repZ_eq (m : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hdet : ‖m.det‖ = (p : ℝ)⁻¹) :
    ∃ (i : Fin (p + 1)) (k : GL (Fin 2) ℤ_[p]), (k : Matrix (Fin 2) (Fin 2) ℤ_[p]) * repZ p i = m := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hdet_lt : ‖m.det‖ < 1 := by
    rw [hdet]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

  have mk_unit : ∀ k : Matrix (Fin 2) (Fin 2) ℤ_[p], (p : ℤ_[p]) * k.det = m.det →
      ∃ u : GL (Fin 2) ℤ_[p], (u : Matrix (Fin 2) (Fin 2) ℤ_[p]) = k := by
    intro k hk
    have hnorm : ‖k.det‖ = 1 := by
      have h1 : ‖(p : ℤ_[p]) * k.det‖ = (p : ℝ)⁻¹ := by rw [hk, hdet]
      rw [norm_mul, PadicInt.norm_p] at h1
      exact mul_left_cancel₀ (inv_ne_zero hp0) (h1.trans (mul_one _).symm)
    have hu : IsUnit k := (Matrix.isUnit_iff_isUnit_det k).mpr (PadicInt.isUnit_iff.mpr hnorm)
    exact ⟨hu.unit, rfl⟩
  set a := m 0 0 with ha
  set b := m 0 1 with hb
  set c := m 1 0 with hc
  set d := m 1 1 with hd
  have hm : m = !![a, b; c, d] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hdet' : m.det = a * d - b * c := by rw [hm, Matrix.det_fin_two_of]
  by_cases hprim : ‖a‖ = 1 ∨ ‖c‖ = 1
  ·

    obtain ⟨t, hbt, hdt⟩ : ∃ t : ℤ_[p], ‖b - a * t‖ < 1 ∧ ‖d - c * t‖ < 1 := by
      rcases hprim with hau | hcu
      · have hau' : IsUnit a := PadicInt.isUnit_iff.mpr hau
        refine ⟨hau'.unit⁻¹ * b, ?_, ?_⟩
        · have : b - a * ((hau'.unit⁻¹ : ℤ_[p]ˣ) * b) = 0 := by
            rw [← mul_assoc, hau'.mul_val_inv, one_mul, sub_self]
          rw [this, norm_zero]; exact zero_lt_one
        ·
          have hkey : a * (d - c * ((hau'.unit⁻¹ : ℤ_[p]ˣ) * b)) = m.det := by
            rw [hdet']
            have : a * (c * ((hau'.unit⁻¹ : ℤ_[p]ˣ) * b)) = b * c := by
              calc a * (c * ((hau'.unit⁻¹ : ℤ_[p]ˣ) * b))
                  = (a * (hau'.unit⁻¹ : ℤ_[p]ˣ)) * (c * b) := by ring
                _ = b * c := by rw [hau'.mul_val_inv, one_mul, mul_comm]
            rw [mul_sub, this]
          have := congrArg norm hkey
          rw [norm_mul, hau, one_mul] at this
          rw [this]; exact hdet_lt
      · have hcu' : IsUnit c := PadicInt.isUnit_iff.mpr hcu
        refine ⟨hcu'.unit⁻¹ * d, ?_, ?_⟩
        · have hkey : c * (b - a * ((hcu'.unit⁻¹ : ℤ_[p]ˣ) * d)) = -m.det := by
            rw [hdet']
            have : c * (a * ((hcu'.unit⁻¹ : ℤ_[p]ˣ) * d)) = a * d := by
              calc c * (a * ((hcu'.unit⁻¹ : ℤ_[p]ˣ) * d))
                  = (c * (hcu'.unit⁻¹ : ℤ_[p]ˣ)) * (a * d) := by ring
                _ = a * d := by rw [hcu'.mul_val_inv, one_mul]
            rw [mul_sub, this]; ring
          have := congrArg norm hkey
          rw [norm_mul, hcu, one_mul, norm_neg] at this
          rw [this]; exact hdet_lt
        · have : d - c * ((hcu'.unit⁻¹ : ℤ_[p]ˣ) * d) = 0 := by
            rw [← mul_assoc, hcu'.mul_val_inv, one_mul, sub_self]
          rw [this, norm_zero]; exact zero_lt_one

    set j : ℕ := (PadicInt.toZMod t).val with hj
    have hjp : j < p := ZMod.val_lt _
    have htj : ‖t - (j : ℤ_[p])‖ < 1 := by
      have h1 : PadicInt.toZMod (t - (j : ℤ_[p])) = 0 := by
        rw [map_sub, map_natCast, hj, ZMod.natCast_zmod_val, sub_self]
      have h2 : t - (j : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := RingHom.mem_ker.mpr h1
      rw [PadicInt.ker_toZMod] at h2
      exact PadicInt.mem_nonunits.mp ((IsLocalRing.mem_maximalIdeal _).mp h2)
    have hbj : ‖b - a * (j : ℤ_[p])‖ < 1 := by
      have : b - a * (j : ℤ_[p]) = (b - a * t) + a * (t - (j : ℤ_[p])) := by ring
      rw [this]
      have ha1 : ‖a * (t - (j : ℤ_[p]))‖ < 1 := by
        rw [norm_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (PadicInt.norm_le_one a) (norm_nonneg _) htj
      exact lt_of_le_of_lt (PadicInt.nonarchimedean _ _) (max_lt hbt ha1)
    have hdj : ‖d - c * (j : ℤ_[p])‖ < 1 := by
      have : d - c * (j : ℤ_[p]) = (d - c * t) + c * (t - (j : ℤ_[p])) := by ring
      rw [this]
      have hc1 : ‖c * (t - (j : ℤ_[p]))‖ < 1 := by
        rw [norm_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (PadicInt.norm_le_one c) (norm_nonneg _) htj
      exact lt_of_le_of_lt (PadicInt.nonarchimedean _ _) (max_lt hdt hc1)
    obtain ⟨y₁, hy₁⟩ := (PadicInt.norm_lt_one_iff_dvd _).mp hbj
    obtain ⟨y₂, hy₂⟩ := (PadicInt.norm_lt_one_iff_dvd _).mp hdj
    obtain ⟨u, hu⟩ := mk_unit !![a, y₁; c, y₂] (by
      rw [Matrix.det_fin_two_of, hdet']

      have e1 : (p : ℤ_[p]) * y₁ = b - a * (j : ℤ_[p]) := hy₁.symm
      have e2 : (p : ℤ_[p]) * y₂ = d - c * (j : ℤ_[p]) := hy₂.symm
      linear_combination a * e2 - c * e1)
    refine ⟨⟨j, by omega⟩, u, ?_⟩
    rw [hu, repZ_of_lt p (by simpa using hjp), hm]
    ext i l
    fin_cases i <;> fin_cases l
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp [Matrix.mul_apply, Fin.sum_univ_two]; linear_combination -hy₁
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp [Matrix.mul_apply, Fin.sum_univ_two]; linear_combination -hy₂
  ·
    rw [not_or] at hprim
    have ha1 : ‖a‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one a) hprim.1
    have hc1 : ‖c‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one c) hprim.2
    obtain ⟨a', ha'⟩ := (PadicInt.norm_lt_one_iff_dvd _).mp ha1
    obtain ⟨c', hc'⟩ := (PadicInt.norm_lt_one_iff_dvd _).mp hc1
    obtain ⟨u, hu⟩ := mk_unit !![a', b; c', d] (by
      rw [Matrix.det_fin_two_of, hdet', ha', hc']; ring)
    refine ⟨Fin.last p, u, ?_⟩
    rw [hu, repZ_last, hm]
    ext i l
    fin_cases i <;> fin_cases l <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha', hc', mul_comm]

private theorem repZ_injective_mod_units {i j : Fin (p + 1)} (k : GL (Fin 2) ℤ_[p])
    (h : (k : Matrix (Fin 2) (Fin 2) ℤ_[p]) * repZ p i = repZ p j) : i = j := by
  have hpn : ¬ IsUnit (p : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_p]
    exact (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)).ne
  set K : Matrix (Fin 2) (Fin 2) ℤ_[p] := (k : Matrix (Fin 2) (Fin 2) ℤ_[p]) with hK
  by_cases hi : (i : ℕ) < p <;> by_cases hj : (j : ℕ) < p
  ·
    rw [repZ_of_lt p hi, repZ_of_lt p hj] at h
    have h00 := congr_fun (congr_fun h 0) 0
    have h01 := congr_fun (congr_fun h 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01

    rw [h00, one_mul] at h01
    have hdvd : ‖((j : ℕ) : ℤ_[p]) - ((i : ℕ) : ℤ_[p])‖ < 1 := by
      rw [← h01, add_sub_cancel_left, norm_mul, PadicInt.norm_p]
      calc ‖K 0 1‖ * (p : ℝ)⁻¹ ≤ 1 * (p : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (by positivity)
        _ < 1 := by rw [one_mul]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    have hz : ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) = 0 := by
      have hd : (p : ℤ) ∣ ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) :=
        (PadicInt.norm_int_lt_one_iff_dvd _).mp (by push_cast; simpa using hdvd)
      exact Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_sub_lt_iff]; omega)
    exact Fin.ext (by omega)
  ·
    exfalso
    rw [repZ_of_lt p hi, Fin.eq_last_of_not_lt hj, repZ_last] at h
    have h00 := congr_fun (congr_fun h 0) 0
    have h10 := congr_fun (congr_fun h 1) 0
    have h11 := congr_fun (congr_fun h 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h10 h11

    rw [h10, zero_mul, zero_add] at h11
    exact hpn (IsUnit.of_mul_eq_one (K 1 1) (by rw [mul_comm]; exact h11))
  ·
    exfalso
    rw [Fin.eq_last_of_not_lt hi, repZ_last, repZ_of_lt p hj] at h
    have h00 := congr_fun (congr_fun h 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

    exact hpn (IsUnit.of_mul_eq_one (K 0 0) (by rw [mul_comm]; exact h00))
  · rw [Fin.eq_last_of_not_lt hi, Fin.eq_last_of_not_lt hj]

private theorem exists_perm_repZ_mul (u : GL (Fin 2) ℤ_[p]) :
    ∃ σ : Equiv.Perm (Fin (p + 1)), ∀ i, ∃ k : GL (Fin 2) ℤ_[p],
      repZ p i * (u : Matrix (Fin 2) (Fin 2) ℤ_[p]) = (k : Matrix (Fin 2) (Fin 2) ℤ_[p]) * repZ p (σ i) := by
  classical

  have hcls : ∀ i : Fin (p + 1), ∃ (j : Fin (p + 1)) (k : GL (Fin 2) ℤ_[p]),
      (k : Matrix (Fin 2) (Fin 2) ℤ_[p]) * repZ p j = repZ p i * (u : Matrix (Fin 2) (Fin 2) ℤ_[p]) := by
    intro i
    apply exists_repZ_eq
    rw [Matrix.det_mul, det_repZ, norm_mul, PadicInt.norm_p]
    have hu : ‖((u : Matrix (Fin 2) (Fin 2) ℤ_[p]).det)‖ = 1 := by
      have := (Matrix.GeneralLinearGroup.det u).isUnit
      rw [Matrix.GeneralLinearGroup.val_det_apply] at this
      exact PadicInt.isUnit_iff.mp this
    rw [hu, mul_one]
  choose f k hk using hcls

  have hinj : Function.Injective f := by
    intro i i' hii'
    have h1 := hk i
    have h2 := hk i'
    rw [hii'] at h1
    have hR : repZ p (f i') = ((k i')⁻¹ : GL (Fin 2) ℤ_[p]) * (repZ p i' * (u : Matrix (Fin 2) (Fin 2) ℤ_[p])) :=
      by rw [← h2, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [hR] at h1
    have h3 : ((k i : Matrix (Fin 2) (Fin 2) ℤ_[p]) * ((k i')⁻¹ : GL (Fin 2) ℤ_[p]) * repZ p i') *
        (u : Matrix (Fin 2) (Fin 2) ℤ_[p]) = repZ p i * (u : Matrix (Fin 2) (Fin 2) ℤ_[p]) := by
      rw [← h1]; simp only [Matrix.mul_assoc]
    have h4 := (Units.mul_left_inj u).mp h3
    have h5 : ((k i * (k i')⁻¹ : GL (Fin 2) ℤ_[p]) : Matrix (Fin 2) (Fin 2) ℤ_[p]) * repZ p i' = repZ p i := by
      rw [Units.val_mul]; exact h4
    exact (repZ_injective_mod_units p _ h5).symm
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hinj
  refine ⟨Equiv.ofBijective f hbij, fun i => ⟨k i, ?_⟩⟩
  simp only [Equiv.ofBijective_apply]
  exact (hk i).symm

end HeckeCosets

namespace DescentSupportA

private theorem coe_finComponent {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (w : HeightOneSpectrum R) (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ((AdelicLevel.finComponent R K w g) : Matrix (Fin 2) (Fin 2) (w.adicCompletion K))
      = (AdelicLevel.finAdeleEval R K w).mapMatrix
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) := by
  ext i j
  rw [AdelicLevel.finComponent_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    AdelicLevel.finAdeleEval_apply]

private theorem glEq_of_forall_finComponent_eq {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {g h : GL (Fin 2) (FiniteAdeleRing R K)}
    (H : ∀ w : HeightOneSpectrum R, AdelicLevel.finComponent R K w g = AdelicLevel.finComponent R K w h) :
    g = h := by
  refine Matrix.GeneralLinearGroup.ext fun i j => congrFun (congrFun ?_ i) j
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun w => ?_
  rw [← coe_finComponent w g, ← coe_finComponent w h, H w]

private theorem commute_of_finComponent_eq_one (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    {w x : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hw : AdelicLevel.finComponent (𝓞 ℚ) ℚ v w = 1)
    (hx : ∀ w' : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), w' ≠ v →
      AdelicLevel.finComponent (𝓞 ℚ) ℚ w' x = 1) :
    w * x = x * w := by
  refine glEq_of_forall_finComponent_eq fun w' => ?_
  rw [map_mul, map_mul]
  rcases eq_or_ne w' v with rfl | hw'
  · rw [hw, one_mul, mul_one]
  · rw [hx w' hw', mul_one, one_mul]

section S1

private theorem mapMatrix_injective {A B : Type*} [Semiring A] [Semiring B] {f : A →+* B}
    (hf : Function.Injective f) :
    Function.Injective ((RingHom.mapMatrix f : Matrix (Fin 2) (Fin 2) A →+* _)) := fun M N h => by
  ext i j
  exact hf (by simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using congrFun (congrFun h i) j)

private theorem exists_glMap_eq {R : Type*} [CommRing R] {K : Type*} [CommRing K]
    (f : R →+* K) (hf : Function.Injective f) (x : GL (Fin 2) K)
    (hx : ∀ i j, ∃ r, f r = (x : Matrix (Fin 2) (Fin 2) K) i j)
    (hx' : ∀ i j, ∃ r, f r = ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) :
    ∃ c : GL (Fin 2) R, Matrix.GeneralLinearGroup.map (n := Fin 2) f c = x := by
  set M : Matrix (Fin 2) (Fin 2) R := fun i j => Classical.choose (hx i j) with hM
  set M' : Matrix (Fin 2) (Fin 2) R := fun i j => Classical.choose (hx' i j)
  have hMim : f.mapMatrix M = (x : Matrix (Fin 2) (Fin 2) K) :=
    Matrix.ext fun i j => Classical.choose_spec (hx i j)
  have hM'im : f.mapMatrix M' = ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
    Matrix.ext fun i j => Classical.choose_spec (hx' i j)
  have hinj : Function.Injective ((RingHom.mapMatrix f : Matrix (Fin 2) (Fin 2) R →+* _)) :=
    mapMatrix_injective hf
  have hMM' : M * M' = 1 := hinj (by
    rw [map_mul, hMim, hM'im, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have hM'M : M' * M = 1 := hinj (by
    rw [map_mul, hM'im, hMim, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  refine ⟨⟨M, M', hMM', hM'M⟩, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact congrFun (congrFun hMim i) j

private theorem exists_finComponent_eq_padicGL_map (p : ℕ) [Fact p.Prime] (I : Ideal (𝓞 ℚ))
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ I) :
    ∃ c : GL (Fin 2) ℤ_[p],
      AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) u
        = padicGL p (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[p] ℚ_[p]) c) := by
  obtain ⟨hu₁, hu₂⟩ := AdelicLevel.mem_finiteLevelOne_iff.mp hu
  set cq : GL (Fin 2) ℚ_[p] := Matrix.GeneralLinearGroup.map (n := Fin 2)
    (padicRingEquiv p).symm.toRingHom (AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) u) with hcq

  have hcq_inv : padicGL p cq = AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) u :=
    Matrix.GeneralLinearGroup.ext fun i j => by
      rw [padicGL_apply, hcq, Matrix.GeneralLinearGroup.map_apply]
      exact RingEquiv.apply_symm_apply _ _

  have hex : ∀ (e : GL (Fin 2) ((padicPlace p).adicCompletion ℚ)),
      (∀ i j, (e : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace p).adicCompletionIntegers ℚ) →
      ∀ i j, ∃ r : ℤ_[p], algebraMap ℤ_[p] ℚ_[p] r
        = (Matrix.GeneralLinearGroup.map (n := Fin 2) (padicRingEquiv p).symm.toRingHom e
            : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j := fun e he i j => by
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact ⟨⟨_, (norm_le_one_iff_mem p _).mpr
      ((RingEquiv.apply_symm_apply (padicRingEquiv p) _).symm ▸ he i j)⟩,
      (PadicInt.algebraMap_apply _).trans rfl⟩
  have hmem : ∀ i j, (AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) u
      : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace p).adicCompletionIntegers ℚ := fun i j => by
    rw [AdelicLevel.finComponent_apply]; exact hu₁.integral i j (padicPlace p)
  have hmem' : ∀ i j, (AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) u⁻¹
      : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace p).adicCompletionIntegers ℚ := fun i j => by
    rw [AdelicLevel.finComponent_apply]; exact hu₂.integral i j (padicPlace p)
  obtain ⟨c, hc⟩ := exists_glMap_eq (algebraMap ℤ_[p] ℚ_[p])
    (IsFractionRing.injective ℤ_[p] ℚ_[p]) cq (hcq ▸ hex _ hmem)
    (by rw [hcq, ← map_inv, ← map_inv]; exact hex _ hmem')
  exact ⟨c, hcq_inv ▸ congrArg (padicGL p) hc.symm⟩

end S1

end DescentSupportA

namespace DescentEngine

open NumberField AdelicDock HeckeCosets DescentSupportA

variable (p : ℕ) [hp : Fact p.Prime]

private noncomputable abbrev ι : GL (Fin 2) ℤ_[p] →* GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[p] ℚ_[p])

private theorem ι_mem_padicK1_zero (k : GL (Fin 2) ℤ_[p]) : ι p k ∈ LocalNewvector.padicK1 p 0 :=
  ⟨k, rfl, by simp, by simp⟩

private theorem coe_ι (k : GL (Fin 2) ℤ_[p]) :
    ((ι p k : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = (k : Matrix (Fin 2) (Fin 2) ℤ_[p]).map (algebraMap ℤ_[p] ℚ_[p]) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

private noncomputable def ρQ (i : Fin (p + 1)) : GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((repZ p i).map (algebraMap ℤ_[p] ℚ_[p])) (by
    rw [show (repZ p i).map (algebraMap ℤ_[p] ℚ_[p]) = (algebraMap ℤ_[p] ℚ_[p]).mapMatrix (repZ p i) from rfl,
      ← RingHom.map_det, det_repZ, map_natCast]
    exact_mod_cast hp.out.ne_zero)

private theorem coe_ρQ (i : Fin (p + 1)) :
    ((ρQ p i : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) = (repZ p i).map (algebraMap ℤ_[p] ℚ_[p]) := rfl

private noncomputable def ρA (i : Fin (p + 1)) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  padicToFinAdelic p (ρQ p i)

private theorem ρQ_mul_ι (c : GL (Fin 2) ℤ_[p]) :
    ∃ σ : Equiv.Perm (Fin (p + 1)), ∀ i, ∃ k : GL (Fin 2) ℤ_[p], ρQ p i * ι p c = ι p k * ρQ p (σ i) := by
  obtain ⟨σ, hσ⟩ := exists_perm_repZ_mul p c
  refine ⟨σ, fun i => ?_⟩
  obtain ⟨k, hk⟩ := hσ i
  refine ⟨k, Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, coe_ρQ, coe_ρQ, coe_ι, coe_ι, ← Matrix.map_mul, ← Matrix.map_mul, hk]

private theorem padicToFinAdelic_ι_mem {N : ℕ} (hN : N ≠ 0) (hpN : ¬ p ∣ N) (k : GL (Fin 2) ℤ_[p]) :
    padicToFinAdelic p (ι p k) ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N) := by
  rw [padicToFinAdelic_apply, localEmbed_mem_finiteLevelOne_iff]
  exact padicGL_mem_localLevelOne p hN (by rw [Nat.factorization_eq_zero_of_not_dvd hpN]) (ι_mem_padicK1_zero p k)

private theorem exists_perm_mul_ρA_inv {N : ℕ} (hN : N ≠ 0) (hpN : ¬ p ∣ N)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N)) :
    ∃ σ : Equiv.Perm (Fin (p + 1)), ∀ i, ∃ u' ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N),
      u * (ρA p i)⁻¹ = (ρA p (σ i))⁻¹ * u' := by

  obtain ⟨c, hc⟩ := exists_finComponent_eq_padicGL_map p (ratLevel N) hu

  set e : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) := padicToFinAdelic p (ι p c) with he
  set w : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) := e⁻¹ * u with hw
  have he_mem : e ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N) := padicToFinAdelic_ι_mem p hN hpN c
  have hw_mem : w ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N) := mul_mem (inv_mem he_mem) hu
  have hw_comp : AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) w = 1 := by
    rw [hw, map_mul, map_inv, he, finComponent_padicToFinAdelic_self, hc, inv_mul_cancel]
  have hu_eq : u = e * w := by rw [hw, mul_inv_cancel_left]

  obtain ⟨σ, hσ⟩ := ρQ_mul_ι p c⁻¹
  refine ⟨σ, fun i => ?_⟩
  obtain ⟨k, hk⟩ := hσ i

  have hQ : ι p c * (ρQ p i)⁻¹ = (ρQ p (σ i))⁻¹ * (ι p k)⁻¹ := by
    rw [map_inv] at hk

    have := congrArg (fun x : GL (Fin 2) ℚ_[p] => x⁻¹) hk
    simp only [mul_inv_rev, inv_inv] at this
    exact this
  refine ⟨(padicToFinAdelic p (ι p k))⁻¹ * w, mul_mem (inv_mem (padicToFinAdelic_ι_mem p hN hpN k)) hw_mem, ?_⟩

  have hcomm : w * (ρA p i)⁻¹ = (ρA p i)⁻¹ * w := by
    refine commute_of_finComponent_eq_one (padicPlace p) hw_comp fun w' hw' => ?_
    simp only [ρA, map_inv, finComponent_padicToFinAdelic_of_ne _ _ hw', inv_one]
  calc u * (ρA p i)⁻¹ = e * (w * (ρA p i)⁻¹) := by rw [hu_eq, mul_assoc]
    _ = e * (ρA p i)⁻¹ * w := by rw [hcomm, mul_assoc]
    _ = padicToFinAdelic p (ι p c * (ρQ p i)⁻¹) * w := by rw [he, ρA, map_mul, map_inv]
    _ = padicToFinAdelic p ((ρQ p (σ i))⁻¹ * (ι p k)⁻¹) * w := by rw [hQ]
    _ = (ρA p (σ i))⁻¹ * ((padicToFinAdelic p (ι p k))⁻¹ * w) := by
      rw [map_mul, map_inv, map_inv, ρA, mul_assoc]

end DescentEngine

namespace DescentEngine

open NumberField AdelicDock AutomorphicForm LocalNewvector

variable (p : ℕ) [hp : Fact p.Prime]

private theorem padicPlace_ne {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) : padicPlace q ≠ padicPlace p := by
  intro h
  unfold padicPlace at h
  exact hqp (congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective h))

private theorem padicToAdelic_comm {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (g : GL (Fin 2) ℚ_[q]) (r : GL (Fin 2) ℚ_[p]) :
    padicToAdelic q g * padicToAdelic p r = padicToAdelic p r * padicToAdelic q g := by
  rw [padicToAdelic_apply, padicToAdelic_apply, ← map_mul, ← map_mul]
  congr 1
  exact DescentSupportA.commute_of_finComponent_eq_one (padicPlace p)
    (finComponent_padicToFinAdelic_of_ne q g (padicPlace_ne p hqp).symm)
    (fun w' hw' => finComponent_padicToFinAdelic_of_ne p r hw')

variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private noncomputable def heckeAway (ψ : AdelicSpan φ) : AdelicSpan φ :=
  ∑ i : Fin (p + 1), (ρQ p i)⁻¹ • ψ

private theorem heckeAway_add (ψ₁ ψ₂ : AdelicSpan φ) :
    heckeAway p (ψ₁ + ψ₂) = heckeAway p ψ₁ + heckeAway p ψ₂ := by
  simp only [heckeAway, smul_add, Finset.sum_add_distrib]

private theorem heckeAway_smul (c : ℂ) (ψ : AdelicSpan φ) : heckeAway p (c • ψ) = c • heckeAway p ψ := by
  simp only [heckeAway, Finset.smul_sum, smul_comm c]

private theorem heckeAway_padic_smul {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (g : GL (Fin 2) ℚ_[q]) (ψ : AdelicSpan φ) :
    heckeAway p (g • ψ) = g • heckeAway p ψ := by
  unfold heckeAway
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [AdelicSpan.padic_smul_def, ← mul_smul]
  rw [padicToAdelic_comm p hqp]

private def evalHom (z : AdelicGL2 (𝓞 ℚ) ℚ) : AdelicFnCarrier ℚ →+ ℂ where
  toFun ψ := ψ.toFn z
  map_zero' := rfl
  map_add' _ _ := rfl

private def spanToFnHom (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : AdelicSpan φ →+ AdelicFnCarrier ℚ where
  toFun := AdelicSpan.toFn φ
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem heckeAway_self_apply (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    (AdelicSpan.toFn φ (heckeAway p (AdelicSpan.self φ))).toFn z
      = ∑ i : Fin (p + 1), φ (z * finEmbed (𝓞 ℚ) ℚ (ρA p i)⁻¹) := by
  have h1 : AdelicSpan.toFn φ (heckeAway p (AdelicSpan.self φ))
      = ∑ i : Fin (p + 1), AdelicSpan.toFn φ ((ρQ p i)⁻¹ • AdelicSpan.self φ) := by
    unfold heckeAway
    exact map_sum (spanToFnHom φ) _ _
  have h2 : (∑ i : Fin (p + 1), AdelicSpan.toFn φ ((ρQ p i)⁻¹ • AdelicSpan.self φ)).toFn z
      = ∑ i : Fin (p + 1), (AdelicSpan.toFn φ ((ρQ p i)⁻¹ • AdelicSpan.self φ)).toFn z :=
    map_sum (evalHom z) (fun i => AdelicSpan.toFn φ ((ρQ p i)⁻¹ • AdelicSpan.self φ)) Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul, AdelicSpan.toFn_self,
    AdelicFnCarrier.toFn_mk, padicToAdelic_apply, ρA, map_inv, map_inv]

private theorem heckeAway_self_level_inv {N : ℕ} (hN : N ≠ 0) (hpN : ¬ p ∣ N)
    (hlev : ∀ u ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N), ∀ x, φ (x * finEmbed (𝓞 ℚ) ℚ u) = φ x) :
    ∀ u ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N), ∀ x,
      (AdelicSpan.toFn φ (heckeAway p (AdelicSpan.self φ))).toFn (x * finEmbed (𝓞 ℚ) ℚ u)
        = (AdelicSpan.toFn φ (heckeAway p (AdelicSpan.self φ))).toFn x := by
  intro u hu x
  rw [heckeAway_self_apply, heckeAway_self_apply]
  obtain ⟨σ, hσ⟩ := exists_perm_mul_ρA_inv p hN hpN hu
  calc ∑ i : Fin (p + 1), φ (x * finEmbed (𝓞 ℚ) ℚ u * finEmbed (𝓞 ℚ) ℚ (ρA p i)⁻¹)
      = ∑ i : Fin (p + 1), φ (x * finEmbed (𝓞 ℚ) ℚ (ρA p (σ i))⁻¹) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        obtain ⟨u', hu', h⟩ := hσ i
        rw [mul_assoc, ← map_mul, h, map_mul, ← mul_assoc, hlev u' hu']
    _ = ∑ i : Fin (p + 1), φ (x * finEmbed (𝓞 ℚ) ℚ (ρA p i)⁻¹) :=
        Equiv.sum_comp σ (fun i => φ (x * finEmbed (𝓞 ℚ) ℚ (ρA p i)⁻¹))

end DescentEngine

namespace DescentEngine

open NumberField AdelicDock AutomorphicForm IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (p : ℕ) [hp : Fact p.Prime]

private def repMat (i : Fin (p + 1)) : Matrix (Fin 2) (Fin 2) ℤ :=
  if (i : ℕ) < p then !![1, ((i : ℕ) : ℤ); 0, (p : ℤ)] else !![(p : ℤ), 0; 0, 1]

omit hp in
private theorem det_repMat (i : Fin (p + 1)) : (repMat p i).det = (p : ℤ) := by
  unfold repMat; split_ifs <;> simp [Matrix.det_fin_two_of]

omit hp in
private theorem repMat_lowerLeft (i : Fin (p + 1)) : repMat p i 1 0 = 0 := by
  unfold repMat; split_ifs <;> rfl

private theorem repZ_eq_map (i : Fin (p + 1)) :
    HeckeCosets.repZ p i = (repMat p i).map (Int.castRingHom ℤ_[p]) := by
  unfold HeckeCosets.repZ repMat
  split_ifs <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp

private theorem coe_ρQ_eq_map (i : Fin (p + 1)) :
    ((ρQ p i : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = (repMat p i).map (Int.castRingHom ℚ_[p]) := by
  rw [coe_ρQ, repZ_eq_map, Matrix.map_map]
  congr 1

private noncomputable def repQ (i : Fin (p + 1)) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((repMat p i).map (Int.castRingHom ℚ)) (by
    rw [show (repMat p i).map (Int.castRingHom ℚ) = (Int.castRingHom ℚ).mapMatrix (repMat p i) from rfl,
      ← RingHom.map_det, det_repMat, map_natCast]
    exact_mod_cast hp.out.ne_zero)

private theorem coe_repQ (i : Fin (p + 1)) :
    ((repQ p i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = (repMat p i).map (Int.castRingHom ℚ) := rfl

private theorem map_repQ_eq_heckeMatrix {i : Fin (p + 1)} (hi : (i : ℕ) < p) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (repQ p i) = ModularForm.heckeMatrix p (i : ℕ) := by
  refine Units.ext ?_
  rw [ModularForm.val_heckeMatrix hp.out.ne_zero]
  ext a b
  rw [Matrix.GeneralLinearGroup.map_apply, coe_repQ, repMat, if_pos hi]
  fin_cases a <;> fin_cases b <;> simp

private theorem map_repQ_last_eq_heckeDiagMatrix :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (repQ p (Fin.last p)) = ModularForm.heckeDiagMatrix p := by
  refine Units.ext ?_
  rw [ModularForm.val_heckeDiagMatrix hp.out.ne_zero]
  ext a b
  rw [Matrix.GeneralLinearGroup.map_apply, coe_repQ, repMat, if_neg (by simp)]
  fin_cases a <;> fin_cases b <;> simp

private theorem finComponent_glFin_globalPoints_repQ (i : Fin (p + 1)) :
    AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p)
        (AdelicLevel.glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (repQ p i)))
      = padicGL p (ρQ p i) := by
  refine Matrix.GeneralLinearGroup.ext fun a b => ?_
  rw [AdelicLevel.finComponent_apply, padicGL_apply, coe_ρQ_eq_map, Matrix.map_apply, eq_intCast, map_intCast]
  change (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((repQ p i : Matrix (Fin 2) (Fin 2) ℚ) a b)) (padicPlace p) = _
  rw [coe_repQ, Matrix.map_apply]
  change ((algebraMap ℚ ((padicPlace p).adicCompletion ℚ)).comp (Int.castRingHom ℚ)) (repMat p i a b) = _
  rw [eq_intCast]

private theorem algebraMap_mem_adicCompletionIntegers_of_den {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : v ≠ padicPlace p) {x : ℚ} (hx : x.den = 1 ∨ x.den = p) :
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) x) v ∈ v.adicCompletionIntegers ℚ := by
  have hden : (x.den : 𝓞 ℚ) ∉ v.asIdeal := by
    intro hmem
    have hgen : Rat.HeightOneSpectrum.natGenerator v ∣ x.den := by
      rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
      first | exact Ideal.mem_map_of_mem _ hmem | simpa using Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hmem
    rcases hx with h1 | hpd
    · rw [h1, Nat.dvd_one] at hgen
      exact (Rat.HeightOneSpectrum.prime_natGenerator v).one_lt.ne' hgen
    · rw [hpd] at hgen
      have heq : Rat.HeightOneSpectrum.natGenerator v = p :=
        (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hp.out).mp hgen
      apply hv
      unfold padicPlace
      rw [Equiv.eq_symm_apply]
      exact Subtype.ext heq
  have h := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := ℚ) v x
  have h' : Valued.v ((algebraMap ℚ (v.adicCompletion ℚ)) x) = v.valuation ℚ x := by
    convert h using 2
    all_goals try rfl
  rw [mem_adicCompletionIntegers]
  change Valued.v ((algebraMap ℚ (v.adicCompletion ℚ)) x) ≤ 1
  rw [h']
  exact Rat.valuation_le_one_iff_den.mpr hden

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain

variable (p : ℕ) [hp : Fact p.Prime]

section GlobalPointsLemmas

private theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

private noncomputable def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

private theorem ratArchHom_apply (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ratArchHom g = LanglandsTunnell.ratArchGL2 g := rfl

private theorem ratArch_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (g * g')
      = LanglandsTunnell.ratArchGL2 g * LanglandsTunnell.ratArchGL2 g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

private theorem ratArch_inv (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 g⁻¹ = (LanglandsTunnell.ratArchGL2 g)⁻¹ := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, map_inv]

private theorem ratArch_eq_one_of_glArch_eq_one {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    LanglandsTunnell.ratArchGL2 u = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [hu, map_one, map_one]

private theorem ratArch_finEmbed (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (finEmbed (𝓞 ℚ) ℚ u) = 1 :=
  ratArch_eq_one_of_glArch_eq_one (glArch_finEmbed (𝓞 ℚ) ℚ u)

private theorem ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ) = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))))
      ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = (Rat.castHom ℝ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)
  rw [eq_ratCast, eq_ratCast]

private theorem glFin_globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

end GlobalPointsLemmas

private theorem gl_ext_of_arch_fin {x y : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (h₁ : glArch (𝓞 ℚ) ℚ x = glArch (𝓞 ℚ) ℚ y) (h₂ : glFin (𝓞 ℚ) ℚ x = glFin (𝓞 ℚ) ℚ y) : x = y := by
  refine Units.ext (Matrix.ext fun a b => Prod.ext ?_ ?_)
  · exact congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing ℚ) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) a b) h₁
  · exact congrArg
      (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) h₂

private theorem finEmbed_mul_comm_of_glFin_eq_one {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    finEmbed (𝓞 ℚ) ℚ u * h = h * finEmbed (𝓞 ℚ) ℚ u := by
  refine gl_ext_of_arch_fin ?_ ?_
  · rw [map_mul, map_mul, glArch_finEmbed, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_finEmbed, hh, one_mul, mul_one]

private noncomputable def archPart (γ : GL (Fin 2) ℚ) : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) :=
  globalPoints (𝓞 ℚ) ℚ γ * (finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)))⁻¹

private theorem glFin_archPart (γ : GL (Fin 2) ℚ) : glFin (𝓞 ℚ) ℚ (archPart γ) = 1 := by
  rw [archPart, map_mul, map_inv, glFin_finEmbed, mul_inv_cancel]

private theorem ratArch_archPart (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (archPart γ) = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  rw [archPart, ratArch_mul, ratArch_inv, ratArch_finEmbed, inv_one, mul_one, ratArch_globalPoints]

private theorem globalPoints_eq_archPart_mul (γ : GL (Fin 2) ℚ) :
    globalPoints (𝓞 ℚ) ℚ γ = archPart γ * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)) := by
  rw [archPart, inv_mul_cancel_right]

private noncomputable def repInvMat (i : Fin (p + 1)) : Matrix (Fin 2) (Fin 2) ℚ :=
  if (i : ℕ) < p then !![1, ((-((i : ℕ) : ℤ) : ℤ) : ℚ) / (p : ℚ); 0, ((1 : ℤ) : ℚ) / (p : ℚ)]
  else !![((1 : ℤ) : ℚ) / (p : ℚ), 0; 0, 1]

private theorem coe_repQ_mul_repInvMat (i : Fin (p + 1)) :
    ((repQ p i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) * repInvMat p i = 1 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [coe_repQ]
  unfold repMat repInvMat
  split_ifs <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_two]; (try field_simp); (try ring))

private theorem coe_repQ_inv (i : Fin (p + 1)) :
    (((repQ p i)⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = repInvMat p i := by
  rw [Matrix.coe_units_inv, Matrix.inv_eq_right_inv (coe_repQ_mul_repInvMat p i)]

private def IsPShape (x : ℚ) : Prop := (∃ n : ℤ, x = n) ∨ ∃ n : ℤ, x = (n : ℚ) / (p : ℚ)

private theorem isPShape_repQ_entry (i : Fin (p + 1)) (a b : Fin 2) :
    IsPShape p (((repQ p i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) a b) := by
  rw [coe_repQ, Matrix.map_apply, eq_intCast]
  exact Or.inl ⟨_, rfl⟩

omit hp in
private theorem isPShape_repInvMat_entry (i : Fin (p + 1)) (a b : Fin 2) : IsPShape p (repInvMat p i a b) := by
  unfold repInvMat IsPShape
  split_ifs <;> fin_cases a <;> fin_cases b <;> simp only [Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue, Fin.mk_one, Fin.zero_eta]
  · exact Or.inl ⟨1, by simp⟩
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl ⟨0, by simp⟩
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl ⟨0, by simp⟩
  · exact Or.inl ⟨0, by simp⟩
  · exact Or.inl ⟨1, by simp⟩

private theorem mem_of_isPShape {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ padicPlace p) {x : ℚ} (hx : IsPShape p x) :
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) x) v ∈ v.adicCompletionIntegers ℚ := by
  rcases hx with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · exact algebraMap_mem_adicCompletionIntegers_of_den p hv (Or.inl (Rat.den_intCast n))
  · rw [div_eq_mul_inv, map_mul, ← finAdeleEval_apply, map_mul, finAdeleEval_apply, finAdeleEval_apply]
    refine mul_mem (algebraMap_mem_adicCompletionIntegers_of_den p hv (Or.inl (Rat.den_intCast n))) ?_
    refine algebraMap_mem_adicCompletionIntegers_of_den p hv (Or.inr ?_)
    rw [Rat.inv_natCast_den, if_neg hp.out.ne_zero]

private noncomputable def kRep (i : Fin (p + 1)) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (repQ p i)) * (ρA p i)⁻¹

private theorem finComponent_kRep_self (i : Fin (p + 1)) : finComponent (𝓞 ℚ) ℚ (padicPlace p) (kRep p i) = 1 := by
  rw [kRep, map_mul, map_inv, finComponent_glFin_globalPoints_repQ, ρA, finComponent_padicToFinAdelic_self,
    mul_inv_cancel]

private theorem finComponent_kRep_of_ne {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ padicPlace p) (i : Fin (p + 1)) :
    finComponent (𝓞 ℚ) ℚ v (kRep p i) = finComponent (𝓞 ℚ) ℚ v (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (repQ p i))) := by
  rw [kRep, map_mul, map_inv, ρA, finComponent_padicToFinAdelic_of_ne p _ hv, inv_one, mul_one]

private theorem finComponent_kRep_inv_of_ne {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ padicPlace p) (i : Fin (p + 1)) :
    finComponent (𝓞 ℚ) ℚ v (kRep p i)⁻¹
      = finComponent (𝓞 ℚ) ℚ v (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (repQ p i)⁻¹)) := by
  rw [map_inv, finComponent_kRep_of_ne p hv, map_inv (globalPoints (𝓞 ℚ) ℚ), map_inv (glFin (𝓞 ℚ) ℚ),
    map_inv (finComponent (𝓞 ℚ) ℚ v)]

private theorem one_entry_mem (v : HeightOneSpectrum (𝓞 ℚ)) (a b : Fin 2) :
    ((1 : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) a b
      ∈ v.adicCompletionIntegers ℚ := by
  rw [Units.val_one, Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

private theorem entry_mem_integral {g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} {m : Matrix (Fin 2) (Fin 2) ℚ}
    (hself : finComponent (𝓞 ℚ) ℚ (padicPlace p) g = 1)
    (hne : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ padicPlace p → ∀ a b : Fin 2,
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) v
        = (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (m a b)) v)
    (hm : ∀ a b, IsPShape p (m a b)) (a b : Fin 2) :
    (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  intro v
  by_cases hv : v = padicPlace p
  · subst hv
    rw [← finComponent_apply, hself]
    exact one_entry_mem _ a b
  · rw [hne v hv a b]
    exact mem_of_isPShape p hv (hm a b)

private theorem lowerLeft_mem_idealBall (N : Ideal (𝓞 ℚ)) {g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    {m : Matrix (Fin 2) (Fin 2) ℚ} (hself : finComponent (𝓞 ℚ) ℚ (padicPlace p) g = 1)
    (hne : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ padicPlace p → ∀ a b : Fin 2,
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) v
        = (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (m a b)) v)
    (hm : m 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0 ∈ idealBall (𝓞 ℚ) ℚ N := by
  intro v
  by_cases hv : v = padicPlace p
  · subst hv
    rw [← finComponent_apply, hself, Units.val_one, Matrix.one_apply_ne (by decide), map_zero]
    exact zero_le'
  · rw [hne v hv 1 0, hm, map_zero]
    change Valued.v ((0 : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ _
    rw [← finAdeleEval_apply, map_zero, map_zero]
    exact zero_le'

private theorem kRep_entry_of_ne {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ padicPlace p) (i : Fin (p + 1)) (a b : Fin 2) :
    ((kRep p i : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) v
      = (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (((repQ p i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) a b)) v := by
  rw [← finComponent_apply, finComponent_kRep_of_ne p hv, finComponent_apply, glFin_globalPoints_apply]

private theorem kRep_inv_entry_of_ne {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ padicPlace p) (i : Fin (p + 1)) (a b : Fin 2) :
    ((((kRep p i)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) v
      = (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (repInvMat p i a b)) v := by
  rw [← finComponent_apply, finComponent_kRep_inv_of_ne p hv, finComponent_apply, glFin_globalPoints_apply,
    coe_repQ_inv]

omit hp in
private theorem repInvMat_lowerLeft (i : Fin (p + 1)) : repInvMat p i 1 0 = 0 := by
  unfold repInvMat; split_ifs <;> rfl

private theorem coe_repQ_lowerLeft (i : Fin (p + 1)) : ((repQ p i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := by
  rw [coe_repQ, Matrix.map_apply, repMat_lowerLeft, map_zero]

private theorem kRep_mem_finiteLevelZero (N : Ideal (𝓞 ℚ)) (i : Fin (p + 1)) :
    kRep p i ∈ finiteLevelZero (𝓞 ℚ) ℚ N := by
  rw [mem_finiteLevelZero_iff]
  refine ⟨⟨entry_mem_integral p (finComponent_kRep_self p i) (fun v hv => kRep_entry_of_ne p hv i)
      (isPShape_repQ_entry p i), lowerLeft_mem_idealBall p N (finComponent_kRep_self p i)
      (fun v hv => kRep_entry_of_ne p hv i) (coe_repQ_lowerLeft p i)⟩, ?_⟩
  have hself : finComponent (𝓞 ℚ) ℚ (padicPlace p) (kRep p i)⁻¹ = 1 := by
    rw [map_inv, finComponent_kRep_self, inv_one]
  exact ⟨entry_mem_integral p hself (fun v hv => kRep_inv_entry_of_ne p hv i) (isPShape_repInvMat_entry p i),
    lowerLeft_mem_idealBall p N hself (fun v hv => kRep_inv_entry_of_ne p hv i) (repInvMat_lowerLeft p i)⟩

private theorem globalPoints_repQ_mul_mul_padicToAdelic_inv {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hh : glFin (𝓞 ℚ) ℚ h = 1) (i : Fin (p + 1)) :
    globalPoints (𝓞 ℚ) ℚ (repQ p i) * h * padicToAdelic p (ρQ p i)⁻¹
      = (archPart (repQ p i) * h) * finEmbed (𝓞 ℚ) ℚ (kRep p i) := by
  rw [kRep]
  set G := glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (repQ p i)) with hG
  have h1 : globalPoints (𝓞 ℚ) ℚ (repQ p i) = archPart (repQ p i) * finEmbed (𝓞 ℚ) ℚ G :=
    globalPoints_eq_archPart_mul _
  rw [map_mul, map_inv, padicToAdelic_apply, map_inv, ρA, h1, mul_assoc (archPart _),
    finEmbed_mul_comm_of_glFin_eq_one hh]
  simp only [mul_assoc]

private theorem glFin_archPart_mul {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hh : glFin (𝓞 ℚ) ℚ h = 1) (γ : GL (Fin 2) ℚ) :
    glFin (𝓞 ℚ) ℚ (archPart γ * h) = 1 := by
  rw [map_mul, glFin_archPart, hh, one_mul]

private theorem ratArch_archPart_mul (h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (archPart γ * h)
      = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ * LanglandsTunnell.ratArchGL2 h := by
  rw [ratArch_mul, ratArch_archPart]

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open scoped ModularForm

variable (p : ℕ) [hp : Fact p.Prime]

omit hp in

private theorem exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne {M : ℕ} (hM : M ≠ 0)
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (γ : GL (Fin 2) ℚ) (h : AdelicGL2 (𝓞 ℚ) ℚ)
      (u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)),
      AdelicLevel.glFin (𝓞 ℚ) ℚ h = 1 ∧
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ ∧
          u ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) ∧
            x = globalPoints (𝓞 ℚ) ℚ γ * h * AdelicDock.finEmbed (𝓞 ℚ) ℚ u := by
  obtain ⟨γ', hlev, hpos⟩ :=
    AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat (AdelicDock.ratLevel_ne_bot hM) x
  set y : AdelicGL2 (𝓞 ℚ) ℚ := globalPoints (𝓞 ℚ) ℚ γ' * x with hy
  set u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    AdelicLevel.glFin (𝓞 ℚ) ℚ y with hu
  refine ⟨γ'⁻¹, y * (AdelicDock.finEmbed (𝓞 ℚ) ℚ u)⁻¹, u, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, map_inv, AdelicDock.glFin_finEmbed, mul_inv_cancel]
  · have hy_pos : LanglandsTunnell.ratArchGL2 y ∈ Matrix.GLPos (Fin 2) ℝ :=
      hpos default (IsTotallyReal.isReal default)
    rw [← map_inv, ratArch_mul, ratArch_finEmbed]
    simpa using hy_pos
  · exact (AdelicLevel.mem_levelOne_iff).mp hlev
  · rw [map_inv, hy]
    group

omit hp in
private theorem σ_apply_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < (g.det : ℝ)) (z : ℂ) :
    UpperHalfPlane.σ g z = z := by
  rw [UpperHalfPlane.σ, if_pos hg]
  rfl

omit hp in

private noncomputable def slashHom (k : ℤ) (A : GL (Fin 2) ℝ) : (UpperHalfPlane → ℂ) →+ (UpperHalfPlane → ℂ) where
  toFun f := f ∣[k] A
  map_zero' := SlashAction.zero_slash k A
  map_add' f g := SlashAction.add_slash k A f g

private theorem det_map_repQ (i : Fin (p + 1)) :
    ((Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (repQ p i)).det : ℝ) = (p : ℝ) := by
  rw [Matrix.GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_coe]
  change (Rat.castHom ℝ) (Matrix.det ((repMat p i).map (Int.castRingHom ℚ))) = _
  rw [show (repMat p i).map (Int.castRingHom ℚ) = (Int.castRingHom ℚ).mapMatrix (repMat p i) from rfl,
    ← RingHom.map_det, det_repMat, map_natCast, map_natCast]

private theorem map_repQ_mem_GLPos (i : Fin (p + 1)) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (repQ p i) ∈ Matrix.GLPos (Fin 2) ℝ := by
  rw [Matrix.mem_glpos, det_map_repQ]
  exact_mod_cast hp.out.pos

private theorem sum_slash_map_repQ (f : UpperHalfPlane → ℂ) :
    ∑ i : Fin (p + 1), f ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (repQ p i)
      = ModularForm.heckeT 2 p f := by
  rw [ModularForm.heckeT_def, Fin.sum_univ_castSucc, map_repQ_last_eq_heckeDiagMatrix, Finset.sum_range]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_repQ_eq_heckeMatrix p (by simp)]
  rfl

variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private theorem heckeAway_self_left_inv (hleft : ∀ (γ : GL (Fin 2) ℚ) (x : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (globalPoints (𝓞 ℚ) ℚ γ * x) = φ x) (γ : GL (Fin 2) ℚ) (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    (AdelicSpan.toFn φ (heckeAway p (AdelicSpan.self φ))).toFn (globalPoints (𝓞 ℚ) ℚ γ * x)
      = (AdelicSpan.toFn φ (heckeAway p (AdelicSpan.self φ))).toFn x := by
  rw [heckeAway_self_apply, heckeAway_self_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, hleft]

private theorem sum_apply_eq_heckeT_slash {ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {F : UpperHalfPlane → ℂ} {N : Ideal (𝓞 ℚ)}
    (hleft : ∀ (γ : GL (Fin 2) ℚ) (x : AdelicGL2 (𝓞 ℚ) ℚ), ψ (globalPoints (𝓞 ℚ) ℚ γ * x) = ψ x)
    (hK₀ : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ N, ∀ x, ψ (x * finEmbed (𝓞 ℚ) ℚ u) = ψ x)
    (happly : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 → LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
      ψ h = (F ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I)
    {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    ∑ i : Fin (p + 1), ψ (h * finEmbed (𝓞 ℚ) ℚ (ρA p i)⁻¹)
      = ((ModularForm.heckeT 2 p F) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := by
  have hterm : ∀ i : Fin (p + 1), ψ (h * finEmbed (𝓞 ℚ) ℚ (ρA p i)⁻¹)
      = ((F ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (repQ p i))
          ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := by
    intro i
    have h1 : h * finEmbed (𝓞 ℚ) ℚ (ρA p i)⁻¹
        = globalPoints (𝓞 ℚ) ℚ (repQ p i)⁻¹
            * ((archPart (repQ p i) * h) * finEmbed (𝓞 ℚ) ℚ (kRep p i)) := by
      rw [← globalPoints_repQ_mul_mul_padicToAdelic_inv p hh i, map_inv (globalPoints (𝓞 ℚ) ℚ),
        mul_assoc (globalPoints (𝓞 ℚ) ℚ (repQ p i)) h, inv_mul_cancel_left]
      simp only [padicToAdelic_apply, map_inv, ρA]
    have hpos' : LanglandsTunnell.ratArchGL2 (archPart (repQ p i) * h) ∈ Matrix.GLPos (Fin 2) ℝ := by
      rw [ratArch_archPart_mul]
      exact Subgroup.mul_mem _ (map_repQ_mem_GLPos p i) hpos
    rw [h1, hleft, hK₀ _ (kRep_mem_finiteLevelZero p _ i), happly _ (glFin_archPart_mul hh _) hpos',
      ratArch_archPart_mul, SlashAction.slash_mul]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← sum_slash_map_repQ, ← Finset.sum_apply]
  exact congrFun (map_sum (slashHom 2 (LanglandsTunnell.ratArchGL2 h))
    (fun i : Fin (p + 1) => F ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (repQ p i)) Finset.univ).symm
    UpperHalfPlane.I

private theorem sum_apply_eq_of_glFin_eq_one {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hφg : g.IsAdelicLiftOf φ)
    (hK₀ : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M), ∀ x, φ (x * finEmbed (𝓞 ℚ) ℚ u) = φ x)
    {c : ℂ} (hT : ModularForm.heckeT 2 p ⇑g = c • ⇑g)
    {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    ∑ i : Fin (p + 1), φ (h * finEmbed (𝓞 ℚ) ℚ (ρA p i)⁻¹) = c * φ h := by
  rw [sum_apply_eq_heckeT_slash p hφg.left_inv hK₀ (fun h hh hpos => hφg.apply_eq h hh hpos) hh hpos, hT,
    ModularForm.smul_slash, Pi.smul_apply, smul_eq_mul, σ_apply_of_det_pos ((Matrix.mem_glpos _).mp hpos),
    hφg.apply_eq h hh hpos]

private theorem heckeAway_self_eq_smul {M : ℕ} (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hφg : g.IsAdelicLiftOf φ)
    (hK₀ : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M), ∀ x, φ (x * finEmbed (𝓞 ℚ) ℚ u) = φ x)
    {c : ℂ} (hT : ModularForm.heckeT 2 p ⇑g = c • ⇑g) :
    heckeAway p (AdelicSpan.self φ) = c • AdelicSpan.self φ := by
  refine AdelicSpan.ext φ (AdelicFnCarrier.ext fun z => ?_)
  obtain ⟨γ, h, u, hh, hpos, hu, rfl⟩ := exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hM z
  have hR : (AdelicSpan.toFn φ (c • AdelicSpan.self φ)).toFn
        (globalPoints (𝓞 ℚ) ℚ γ * h * finEmbed (𝓞 ℚ) ℚ u) = c * φ h := by
    change c * φ (globalPoints (𝓞 ℚ) ℚ γ * h * finEmbed (𝓞 ℚ) ℚ u) = c * φ h
    rw [hφg.level_inv u hu, hφg.left_inv]
  rw [hR, heckeAway_self_level_inv p hM hpM hφg.level_inv u hu, heckeAway_self_left_inv p hφg.left_inv,
    heckeAway_self_apply]
  exact sum_apply_eq_of_glFin_eq_one p hφg hK₀ hT hh hpos

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open scoped ModularForm

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private theorem hasReading_zero : HasReading (0 : AdelicSpan φ) (0 : UpperHalfPlane → ℂ) := by
  intro h _ _
  rw [SlashAction.zero_slash]
  rfl

private theorem hasReading_add {y₁ y₂ : AdelicSpan φ} {F₁ F₂ : UpperHalfPlane → ℂ} (h₁ : HasReading y₁ F₁)
    (h₂ : HasReading y₂ F₂) : HasReading (y₁ + y₂) (F₁ + F₂) := by
  intro h hh hpos
  rw [SlashAction.add_slash, Pi.add_apply, ← h₁ h hh hpos, ← h₂ h hh hpos]
  rfl

private theorem hasReading_smul {y : AdelicSpan φ} {F : UpperHalfPlane → ℂ} (hy : HasReading y F) (c : ℂ) :
    HasReading (c • y) (c • F) := by
  intro h hh hpos
  rw [ModularForm.smul_slash, Pi.smul_apply, σ_apply_of_det_pos ((Matrix.mem_glpos _).mp hpos), smul_eq_mul,
    ← hy h hh hpos]
  rfl

private theorem glFin_conj_eq_one (δ : GL (Fin 2) ℚ) {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : glFin (𝓞 ℚ) ℚ h = 1) :
    glFin (𝓞 ℚ) ℚ ((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) = 1 := by
  rw [map_mul, map_mul, hh, mul_one, map_inv, inv_mul_cancel]

private theorem heckeAway_zero (p : ℕ) [Fact p.Prime] : heckeAway p (0 : AdelicSpan φ) = 0 := by
  simp [heckeAway]

private theorem heckeAway_eq_smul_of_mem_span (p : ℕ) [Fact p.Prime] {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) {c : ℂ}
    (hself : heckeAway p (AdelicSpan.self φ) = c • AdelicSpan.self φ) {y : AdelicSpan φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ)) :
    heckeAway p y = c • y := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    rw [heckeAway_padic_smul p hqp, hself, smul_comm]
  | zero => rw [heckeAway_zero, smul_zero]
  | add y₁ y₂ _ _ ih₁ ih₂ => rw [heckeAway_add, ih₁, ih₂, smul_add]
  | smul d y _ ih => rw [heckeAway_smul, ih, smul_comm]

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain
open scoped ModularForm

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}

private theorem continuous_denom (A : GL (Fin 2) ℝ) : Continuous fun τ : UpperHalfPlane => UpperHalfPlane.denom A τ := by
  unfold UpperHalfPlane.denom
  exact (continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const

private theorem continuous_slash {f : UpperHalfPlane → ℂ} (hf : Continuous f) (k : ℤ) (A : GL (Fin 2) ℝ) :
    Continuous (f ∣[k] A) := by
  have h1 : Continuous fun τ : UpperHalfPlane => UpperHalfPlane.σ A (f (A • τ)) :=
    (UpperHalfPlane.σ A).continuous.comp (hf.comp (continuous_const_smul A))
  have h2 : Continuous fun τ : UpperHalfPlane => UpperHalfPlane.denom A τ ^ (-k) :=
    (continuous_denom A).zpow₀ _ fun τ => Or.inl (UpperHalfPlane.denom_ne_zero A τ)
  have h3 : Continuous fun τ : UpperHalfPlane =>
      UpperHalfPlane.σ A (f (A • τ)) * |A.det.val| ^ (k - 1) * UpperHalfPlane.denom A τ ^ (-k) :=
    (h1.mul continuous_const).mul h2
  rw [ModularForm.slash_def]
  exact h3

private theorem dense_ratPoints :
    Dense (((↑) : UpperHalfPlane → ℂ) ⁻¹'
      {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)}) := by
  have h1 : Dense (Set.range ((↑) : ℚ → ℝ) ×ˢ Set.range ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prod Rat.denseRange_cast
  have h2 : {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)} =
      Complex.equivRealProdCLM ⁻¹' (Set.range ((↑) : ℚ → ℝ) ×ˢ Set.range ((↑) : ℚ → ℝ)) := by
    ext w; simp [Set.mem_prod]
  have hS : Dense {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)} := by
    rw [h2]; exact h1.preimage Complex.equivRealProdCLM.toHomeomorph.isOpenMap
  exact hS.preimage UpperHalfPlane.isOpenEmbedding_coe.isOpenMap

private theorem exists_glFin_eq_one_and_smul_I_eq (z : UpperHalfPlane) (hx : (z : ℂ).re ∈ Set.range ((↑) : ℚ → ℝ))
    (hy : (z : ℂ).im ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∃ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 ∧ LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ ∧
      LanglandsTunnell.ratArchGL2 h • UpperHalfPlane.I = z := by
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  have hy0 : (0 : ℝ) < y := by rw [hy]; exact z.im_pos
  have hyq : (0 : ℚ) < y := by exact_mod_cast hy0
  let A : Matrix (Fin 2) (Fin 2) ℚ := !![y, x; 0, 1]
  have hdetA : A.det = y := by simp [A, Matrix.det_fin_two_of]
  let γ : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [hdetA]; exact hyq.ne')
  let h : AdelicGL2 (𝓞 ℚ) ℚ :=
    globalPoints (𝓞 ℚ) ℚ γ * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ))⁻¹
  have hfin : glFin (𝓞 ℚ) ℚ h = 1 := by
    simp only [h, map_mul, glFin_finEmbed, mul_inv_cancel]
  have hP : LanglandsTunnell.ratArchGL2 h = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
    simp only [h, ratArch_mul, ratArch_finEmbed, mul_one, ratArch_globalPoints]
  have hPmat : ((LanglandsTunnell.ratArchGL2 h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(y : ℝ), (x : ℝ); 0, 1] := by
    rw [hP]
    ext i j
    change (Rat.castHom ℝ) (A i j) = _
    fin_cases i <;> fin_cases j <;> simp [A]
  have hdetP : ((LanglandsTunnell.ratArchGL2 h).det.val : ℝ) = y := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hPmat, Matrix.det_fin_two_of]; ring
  have hdetpos : (0 : ℝ) < (LanglandsTunnell.ratArchGL2 h).det.val := by rw [hdetP]; exact hy0
  refine ⟨h, hfin, (Matrix.mem_glpos _).mpr hdetpos, ?_⟩
  rw [UpperHalfPlane.coe_re] at hx
  rw [UpperHalfPlane.coe_im] at hy
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hdetpos]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hPmat, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, UpperHalfPlane.coe_I,
    Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_one, div_one]
  apply Complex.ext <;> simp [← hx, ← hy]

private theorem eq_of_forall_slash_apply_I {F G : UpperHalfPlane → ℂ} (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 → LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
      (F ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I
        = (G ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I) :
    F = G := by
  refine Continuous.ext_on dense_ratPoints hF hG ?_
  rintro z ⟨hx, hy⟩
  obtain ⟨h, hfin, hpos, hz⟩ := exists_glFin_eq_one_and_smul_I_eq z hx hy
  have hdet : (0 : ℝ) < (LanglandsTunnell.ratArchGL2 h).det.val := (Matrix.mem_glpos _).mp hpos
  have key := hFG h hfin hpos
  rw [ModularForm.slash_apply, ModularForm.slash_apply, σ_apply_of_det_pos hdet, σ_apply_of_det_pos hdet, hz]
    at key
  have hne : |(LanglandsTunnell.ratArchGL2 h).det.val| ^ ((2 : ℤ) - 1)
      * UpperHalfPlane.denom (LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I ^ (-(2 : ℤ)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast zpow_ne_zero _ (abs_ne_zero.mpr hdet.ne'))
      (zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ _))
  rw [mul_assoc, mul_assoc] at key
  exact mul_right_cancel₀ hne key

end DescentEngine

namespace DescentSupportB

open NumberField NumberField.AdelicLevel AdelicDock IsDedekindDomain

section S4c

private theorem natGenerator_padicPlace (p : ℕ) [Fact p.Prime] :
    Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) (padicPlace p) = p :=
  congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, Fact.out⟩)

private theorem eq_padicPlace_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
      ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    v = padicPlace (Rat.HeightOneSpectrum.natGenerator v) := by
  haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  refine ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply v).symm.trans ?_
  exact congrArg _ (Subtype.ext rfl)

private theorem padicPlace_injective {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (h : padicPlace p = padicPlace q) : p = q :=
  congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective h)

private theorem valued_natCast_eq_of_factorization_eq (ℓ : ℕ) [Fact ℓ.Prime]
    {N M : ℕ} (hN : N ≠ 0) (hM : M ≠ 0) (hfac : N.factorization ℓ = M.factorization ℓ) :
    Valued.v (padicRingEquiv ℓ (N : ℚ_[ℓ])) = Valued.v (padicRingEquiv ℓ (M : ℚ_[ℓ])) := by
  have hN' : (N : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast hN
  have hM' : (M : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast hM
  refine le_antisymm ?_ ?_
  · rw [valued_le_valued_iff ℓ _ _ hM', norm_natCast_eq_zpow_neg_factorization ℓ hN,
      norm_natCast_eq_zpow_neg_factorization ℓ hM, hfac]
  · rw [valued_le_valued_iff ℓ _ _ hN', norm_natCast_eq_zpow_neg_factorization ℓ hN,
      norm_natCast_eq_zpow_neg_factorization ℓ hM, hfac]

private theorem idealBound_ratLevel_eq_of_factorization_eq {q : ℕ} [Fact q.Prime] {N M : ℕ}
    (hN : N ≠ 0) (hM : M ≠ 0)
    (hfac : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q → N.factorization ℓ = M.factorization ℓ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ≠ padicPlace q) :
    idealBound (𝓞 ℚ) (ratLevel N) v = idealBound (𝓞 ℚ) (ratLevel M) v := by
  haveI hℓp : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hvℓ : v = padicPlace (Rat.HeightOneSpectrum.natGenerator v) :=
    eq_padicPlace_natGenerator v
  have hne : Rat.HeightOneSpectrum.natGenerator v ≠ q := fun heq =>
    hv <| (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective <|
      Subtype.ext <| heq.trans (natGenerator_padicPlace q).symm
  rw [hvℓ, idealBound_ratLevel _ hN, idealBound_ratLevel _ hM,
    valued_natCast_eq_of_factorization_eq _ hN hM (hfac _ hℓp.out hne)]

end S4c

section S4a

private theorem exists_padicGL_map_eq_finComponent {q : ℕ} [Fact q.Prime] {I : Ideal (𝓞 ℚ)}
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ I) :
    ∃ c : GL (Fin 2) ℤ_[q],
      padicGL q (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c)
        = finComponent (𝓞 ℚ) ℚ (padicPlace q) u := by
  obtain ⟨hu₁, hu₂⟩ := mem_finiteLevelZero_iff.mp hu
  set cq : GL (Fin 2) ℚ_[q] := Matrix.GeneralLinearGroup.map (n := Fin 2)
    (padicRingEquiv q).symm.toRingHom (finComponent (𝓞 ℚ) ℚ (padicPlace q) u) with hcq
  have hcq_inv : padicGL q cq = finComponent (𝓞 ℚ) ℚ (padicPlace q) u :=
    Matrix.GeneralLinearGroup.ext fun i j => by
      rw [padicGL_apply, hcq, Matrix.GeneralLinearGroup.map_apply]
      exact RingEquiv.apply_symm_apply _ _
  have hex : ∀ (e : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)),
      (∀ i j, (e : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace q).adicCompletionIntegers ℚ) →
      ∀ i j, ∃ r : ℤ_[q], algebraMap ℤ_[q] ℚ_[q] r
        = (Matrix.GeneralLinearGroup.map (n := Fin 2) (padicRingEquiv q).symm.toRingHom e
            : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j := fun e he i j => by
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact ⟨⟨_, (norm_le_one_iff_mem q _).mpr
      ((RingEquiv.apply_symm_apply (padicRingEquiv q) _).symm ▸ he i j)⟩,
      (PadicInt.algebraMap_apply _).trans rfl⟩
  have hmem : ∀ i j, (finComponent (𝓞 ℚ) ℚ (padicPlace q) u
      : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace q).adicCompletionIntegers ℚ := fun i j => by
    rw [finComponent_apply]; exact hu₁.integral i j (padicPlace q)
  have hmem' : ∀ i j, (finComponent (𝓞 ℚ) ℚ (padicPlace q) u⁻¹
      : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace q).adicCompletionIntegers ℚ := fun i j => by
    rw [finComponent_apply]; exact hu₂.integral i j (padicPlace q)
  obtain ⟨c, hc⟩ := DescentSupportA.exists_glMap_eq (algebraMap ℤ_[q] ℚ_[q])
    (IsFractionRing.injective ℤ_[q] ℚ_[q]) cq (hcq ▸ hex _ hmem)
    (by rw [hcq, ← map_inv, ← map_inv]; exact hex _ hmem')
  exact ⟨c, hc ▸ hcq_inv⟩

private theorem map_algebraMap_scalar_eq_centralGL {q : ℕ} [Fact q.Prime] (d : ℤ_[q]ˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q])
        (Units.map (algebraMap ℤ_[q] (Matrix (Fin 2) (Fin 2) ℤ_[q])).toMonoidHom d)
      = LocalNewvector.centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom d) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp only [LocalNewvector.centralGL, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, Matrix.algebraMap_matrix_apply,
    apply_ite (algebraMap ℤ_[q] ℚ_[q]), map_zero]
  rfl

private theorem isUnit_entry_of_lowerLeft_mem {q : ℕ} [Fact q.Prime] (c : GL (Fin 2) ℤ_[q])
    (hc10 : ¬ IsUnit ((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0)) :
    IsUnit ((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1) := by
  have hdet : IsUnit (Matrix.det (c : Matrix (Fin 2) (Fin 2) ℤ_[q])) :=
    (Matrix.isUnit_iff_isUnit_det _).mp c.isUnit
  rw [Matrix.det_fin_two] at hdet
  by_contra h11
  have h10m : (q : ℤ_[q]) ∣ (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0 :=
    (PadicInt.norm_lt_one_iff_dvd _).mp (PadicInt.not_isUnit_iff.mp hc10)
  have h11m : (q : ℤ_[q]) ∣ (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1 :=
    (PadicInt.norm_lt_one_iff_dvd _).mp (PadicInt.not_isUnit_iff.mp h11)
  have hdetm : (q : ℤ_[q]) ∣
      (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 0 0 * (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1
        - (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 0 1 * (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0 :=
    dvd_sub (Dvd.dvd.mul_left h11m _) (Dvd.dvd.mul_left h10m _)
  exact PadicInt.not_isUnit_iff.mpr ((PadicInt.norm_lt_one_iff_dvd _).mpr hdetm) hdet

private theorem exists_finComponent_eq_centralGL_mul {q : ℕ} [Fact q.Prime] {N : ℕ} (hN : N ≠ 0)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N)) :
    ∃ (z : ℚ_[q]ˣ) (k : GL (Fin 2) ℚ_[q]), k ∈ LocalNewvector.padicK1 q (N.factorization q) ∧
      finComponent (𝓞 ℚ) ℚ (padicPlace q) u = padicGL q (LocalNewvector.centralGL q z * k) := by
  obtain ⟨c, hcfin⟩ := exists_padicGL_map_eq_finComponent (q := q) hu

  have hc10 : (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0
      ∈ Ideal.span {(q : ℤ_[q]) ^ N.factorization q} := by
    rw [← valued_coe_le_idealBound_iff q hN]
    have hcoe : padicRingEquiv q (((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0 : ℤ_[q]) : ℚ_[q])
        = (finComponent (𝓞 ℚ) ℚ (padicPlace q) u : Matrix (Fin 2) (Fin 2) _) 1 0 := by
      rw [← hcfin, padicGL_apply, Matrix.GeneralLinearGroup.map_apply, PadicInt.algebraMap_apply]
    rw [hcoe, finComponent_apply]
    exact (mem_finiteLevelZero_iff.mp hu).1.lowerLeft (padicPlace q)
  rcases eq_or_ne (N.factorization q) 0 with hfac | hfac
  ·
    refine ⟨1, Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c, ?_, ?_⟩
    · rw [hfac, LocalNewvector.padicK1_zero_eq_integralSubgroup,
        ← LocalNewvector.congruenceK1_zero_eq_integralSubgroup (K := ℚ_[q]) (q : ℤ_[q]),
        LocalNewvector.congruenceK1_zero]
      exact ⟨c, rfl⟩
    · rw [map_one, one_mul, hcfin]
  ·
    have hc10_nonunit : ¬ IsUnit ((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0) := fun hcu => by
      have hqdvd : (q : ℤ_[q]) ∣ (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0 := by
        obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp hc10
        exact ⟨(q : ℤ_[q]) ^ (N.factorization q - 1) * k, by
          rw [hk, ← mul_assoc, ← pow_succ']
          congr 2; omega⟩
      exact PadicInt.not_isUnit_iff.mpr ((PadicInt.norm_lt_one_iff_dvd _).mpr hqdvd) hcu
    obtain ⟨d, hd⟩ := (isUnit_entry_of_lowerLeft_mem c hc10_nonunit)
    set sc : GL (Fin 2) ℤ_[q] :=
      Units.map (algebraMap ℤ_[q] (Matrix (Fin 2) (Fin 2) ℤ_[q])).toMonoidHom d with hsc
    set k' : GL (Fin 2) ℤ_[q] := sc⁻¹ * c with hk'

    have hsc_inv_coe : ((sc⁻¹ : GL (Fin 2) ℤ_[q]) : Matrix (Fin 2) (Fin 2) ℤ_[q])
        = (↑d⁻¹ : ℤ_[q]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[q]) := by
      rw [hsc, ← map_inv]
      simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        Algebra.algebraMap_eq_smul_one]

    have hk'_row1 : ∀ j, (k' : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 j
        = (↑d⁻¹ : ℤ_[q]) * (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 j := fun j => by
      rw [hk', Units.val_mul, hsc_inv_coe, Matrix.smul_mul, one_mul, Matrix.smul_apply,
        smul_eq_mul]
    refine ⟨Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom d,
      Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) k', ?_, ?_⟩
    ·
      rw [LocalNewvector.mem_congruenceK1_iff]
      refine ⟨k', rfl, ?_, ?_⟩
      · rw [hk'_row1 0]; exact Ideal.mul_mem_left _ _ hc10
      · rw [hk'_row1 1, ← hd, d.inv_mul, sub_self]; exact Ideal.zero_mem _
    · rw [← map_algebraMap_scalar_eq_centralGL d, ← hsc, ← map_mul, hk', mul_inv_cancel_left,
        hcfin]

end S4a

section S4b

private theorem isLevelZeroMatrix_of_finComponent_eq_and {q : ℕ} [Fact q.Prime] {N M : ℕ}
    (hsame : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ padicPlace q →
      idealBound (𝓞 ℚ) (ratLevel N) v = idealBound (𝓞 ℚ) (ratLevel M) v)
    {g u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : IsLevelZeroMatrix (𝓞 ℚ) ℚ (ratLevel N)
      (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)))
    (hgq : finComponent (𝓞 ℚ) ℚ (padicPlace q) g = 1)
    (hgaway : ∀ v ≠ padicPlace q, finComponent (𝓞 ℚ) ℚ v g = finComponent (𝓞 ℚ) ℚ v u) :
    IsLevelZeroMatrix (𝓞 ℚ) ℚ (ratLevel M)
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  refine ⟨fun i j v => ?_, fun v => ?_⟩
  all_goals rcases eq_or_ne v (padicPlace q) with rfl | hv
  · rw [← finComponent_apply, hgq, Units.val_one]
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.one_apply_eq]; exact one_mem _
    · rw [Matrix.one_apply_ne hij]; exact zero_mem _
  · rw [← finComponent_apply, hgaway v hv, finComponent_apply]; exact hu.integral i j v
  · rw [← finComponent_apply, hgq, Units.val_one,
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_zero]
    exact zero_le'
  · rw [← finComponent_apply, hgaway v hv, finComponent_apply, ← hsame v hv]
    exact hu.lowerLeft v

private theorem mul_padicToFinAdelic_inv_mem_finiteLevelZero {q : ℕ} [Fact q.Prime] {N M : ℕ}
    (hsame : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ padicPlace q →
      idealBound (𝓞 ℚ) (ratLevel N) v = idealBound (𝓞 ℚ) (ratLevel M) v)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N))
    (c : GL (Fin 2) ℚ_[q]) (hc : finComponent (𝓞 ℚ) ℚ (padicPlace q) u = padicGL q c) :
    u * (padicToFinAdelic q c)⁻¹ ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M) := by
  obtain ⟨hu₁, hu₂⟩ := mem_finiteLevelZero_iff.mp hu
  set g := u * (padicToFinAdelic q c)⁻¹ with hg
  have hgq : finComponent (𝓞 ℚ) ℚ (padicPlace q) g = 1 := by
    rw [hg, map_mul, map_inv, finComponent_padicToFinAdelic_self, hc, mul_inv_cancel]
  have hgaway : ∀ v ≠ padicPlace q,
      finComponent (𝓞 ℚ) ℚ v g = finComponent (𝓞 ℚ) ℚ v u := fun v hv => by
    rw [hg, map_mul, map_inv, finComponent_padicToFinAdelic_of_ne q c hv, inv_one, mul_one]
  rw [mem_finiteLevelZero_iff]
  exact ⟨isLevelZeroMatrix_of_finComponent_eq_and hsame hu₁ hgq hgaway,
    isLevelZeroMatrix_of_finComponent_eq_and hsame hu₂ (g := g⁻¹) (u := u⁻¹)
      (by rw [map_inv, hgq, inv_one])
      (fun v hv => by rw [map_inv, hgaway v hv, map_inv])⟩

end S4b

section S4d

private theorem algebraMap_intCast_apply_padicPlace_eq (p : ℕ) [Fact p.Prime] (n : ℤ) :
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (padicPlace p)
      = padicRingEquiv p ((n : ℤ_[p]) : ℚ_[p]) := by
  have hL : (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (padicPlace p) =
      (n : (padicPlace p).adicCompletion ℚ) := by
    change ((algebraMap ℚ ((padicPlace p).adicCompletion ℚ)).comp (Int.castRingHom ℚ)) n = _
    exact eq_intCast _ n
  have hR : padicRingEquiv p ((n : ℤ_[p]) : ℚ_[p]) = (n : (padicPlace p).adicCompletion ℚ) := by
    rw [PadicInt.coe_intCast, map_intCast]
  exact hL.trans hR.symm

private theorem isLevelZeroMatrix_mapMatrix_of_int_entries {N : ℕ} (hN : N ≠ 0)
    (δ : Matrix (Fin 2) (Fin 2) ℚ) (hδ : ∀ a b, ∃ n : ℤ, δ a b = n)
    (hlow : ∃ m : ℤ, δ 1 0 = (N : ℚ) * m) :
    IsLevelZeroMatrix (𝓞 ℚ) ℚ (ratLevel N)
      ((algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix δ) := by
  refine ⟨fun i j v => ?_, fun v => ?_⟩
  all_goals
    haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
      ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    rw [eq_padicPlace_natGenerator v]
    set ℓ := Rat.HeightOneSpectrum.natGenerator v
  · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    obtain ⟨n, hn⟩ := hδ i j
    rw [hn, algebraMap_intCast_apply_padicPlace_eq ℓ n]
    exact padicRingEquiv_coe_mem ℓ _
  · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    obtain ⟨m, hm⟩ := hlow
    have hNm : δ 1 0 = ((N * m : ℤ) : ℚ) := by push_cast; linarith [hm]
    rw [hNm, algebraMap_intCast_apply_padicPlace_eq ℓ (N * m)]
    rw [(valued_coe_le_idealBound_iff ℓ hN _)]
    have hdvd : (ℓ : ℤ_[ℓ]) ^ N.factorization ℓ ∣ (↑(N * m) : ℤ_[ℓ]) := by
      have hdvdZ : (ℓ : ℤ) ^ N.factorization ℓ ∣ (N * m : ℤ) := by
        refine Dvd.dvd.mul_right ?_ m
        exact_mod_cast Nat.ordProj_dvd N ℓ
      obtain ⟨k, hk⟩ := hdvdZ
      exact ⟨(k : ℤ_[ℓ]), by push_cast [hk]; ring⟩
    exact Ideal.mem_span_singleton.mpr hdvd

private theorem map_algebraMap_mem_finiteLevelZero {N : ℕ} (hN : N ≠ 0) (δ : GL (Fin 2) ℚ)
    (hδ : ∀ a b : Fin 2, ∃ n : ℤ, (δ : Matrix (Fin 2) (Fin 2) ℚ) a b = n)
    (hδ' : ∀ a b : Fin 2, ∃ n : ℤ, ((δ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) a b = n)
    (hlow : ∃ m : ℤ, (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (N : ℚ) * m)
    (hlow' : ∃ m : ℤ, ((δ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (N : ℚ) * m) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) δ
      ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) := by
  rw [mem_finiteLevelZero_iff]
  have hcoe : ∀ (γ : GL (Fin 2) ℚ),
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) γ
        : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix (γ : Matrix (Fin 2) (Fin 2) ℚ) :=
    fun γ => Matrix.ext fun i j => Matrix.GeneralLinearGroup.map_apply _ i j γ
  rw [hcoe δ, ← Matrix.GeneralLinearGroup.map_inv, hcoe δ⁻¹]
  exact ⟨isLevelZeroMatrix_mapMatrix_of_int_entries hN _ hδ hlow,
    isLevelZeroMatrix_mapMatrix_of_int_entries hN _ hδ' hlow'⟩

end S4d

end DescentSupportB

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open scoped ModularForm

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private theorem fn_padic_smul_self {q : ℕ} [Fact q.Prime] (x : GL (Fin 2) ℚ_[q]) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn (x • AdelicSpan.self φ) z = φ (z * padicToAdelic q x) := by
  rw [fn, AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul, AdelicSpan.toFn_self,
    AdelicFnCarrier.toFn_mk]

private theorem fn_add (y₁ y₂ : AdelicSpan φ) (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn (y₁ + y₂) z = fn y₁ z + fn y₂ z := rfl

private theorem fn_csmul (c : ℂ) (y : AdelicSpan φ) (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn (c • y) z = c * fn y z := rfl

private theorem fn_zero (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn (0 : AdelicSpan φ) z = 0 := rfl

private theorem fn_padic_smul {q : ℕ} [Fact q.Prime] (x : GL (Fin 2) ℚ_[q]) (y : AdelicSpan φ) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn (x • y) z = fn y (z * padicToAdelic q x) := by
  rw [fn, fn, AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul]

private theorem fn_heckeAway (p : ℕ) [Fact p.Prime] (y : AdelicSpan φ) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn (heckeAway p y) z = ∑ i : Fin (p + 1), fn y (z * finEmbed (𝓞 ℚ) ℚ (ρA p i)⁻¹) := by
  have h1 : AdelicSpan.toFn φ (heckeAway p y) = ∑ i : Fin (p + 1), AdelicSpan.toFn φ ((ρQ p i)⁻¹ • y) := by
    unfold heckeAway
    exact map_sum (spanToFnHom φ) _ _
  have h2 : (∑ i : Fin (p + 1), AdelicSpan.toFn φ ((ρQ p i)⁻¹ • y)).toFn z
      = ∑ i : Fin (p + 1), (AdelicSpan.toFn φ ((ρQ p i)⁻¹ • y)).toFn z :=
    map_sum (evalHom z) (fun i => AdelicSpan.toFn φ ((ρQ p i)⁻¹ • y)) Finset.univ
  rw [fn, h1, h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← fn, fn_padic_smul, padicToAdelic_apply, ρA, map_inv, map_inv]

private theorem hasReading_iff (y : AdelicSpan φ) (F : UpperHalfPlane → ℂ) :
    HasReading y F ↔ ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 →
      LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
        fn y h = (F ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := Iff.rfl

private theorem continuous_heckeT {F : UpperHalfPlane → ℂ} (hF : Continuous F) (ℓ : ℕ) :
    Continuous (ModularForm.heckeT 2 ℓ F) := by
  rw [ModularForm.heckeT_def]
  refine Continuous.add ?_ (continuous_slash hF 2 _)
  have h : (∑ j ∈ Finset.range ℓ, F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ j)
      = fun τ => ∑ j ∈ Finset.range ℓ, (F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ j) τ := by
    funext τ
    exact Finset.sum_apply τ _ _
  rw [h]
  exact continuous_finsetSum _ fun j _ => continuous_slash hF 2 _

private theorem glFin_globalPoints_eq_map (δ : GL (Fin 2) ℚ) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ)
      = Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) δ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_globalPoints_apply]
  rfl

private theorem mapGL_entry_int (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (a b : Fin 2) :
    ∃ n : ℤ, ((Matrix.SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) a b = n :=
  ⟨γ a b, by simp [Matrix.SpecialLinearGroup.mapGL]⟩

private theorem mapGL_lowerLeft_of_mem_Gamma0 {N : ℕ} {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ m : ℤ, ((Matrix.SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (N : ℚ) * m := by
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) N).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  refine ⟨m, ?_⟩
  simp [Matrix.SpecialLinearGroup.mapGL, hm]

private theorem glFin_globalPoints_mapGL_mem_finiteLevelZero {N : ℕ} (hN : N ≠ 0) {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ)) ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) := by
  rw [glFin_globalPoints_eq_map]
  refine DescentSupportB.map_algebraMap_mem_finiteLevelZero hN _ (mapGL_entry_int γ) ?_
    (mapGL_lowerLeft_of_mem_Gamma0 hγ) ?_
  · rw [← map_inv]
    exact mapGL_entry_int γ⁻¹
  · rw [← map_inv]
    exact mapGL_lowerLeft_of_mem_Gamma0 (Subgroup.inv_mem _ hγ)

private theorem map_castHom_mapGL (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.SpecialLinearGroup.mapGL ℚ γ)
      = Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp [Matrix.SpecialLinearGroup.mapGL]

private theorem mapGL_mem_GLPos (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) ∈ Matrix.GLPos (Fin 2) ℝ := by
  rw [Matrix.mem_glpos]
  simp [Matrix.SpecialLinearGroup.mapGL]

end DescentEngine

namespace DescentEngine

open NumberField AutomorphicForm
open scoped ModularForm

private theorem continuous_of_mem_slashSpanPos {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {F : UpperHalfPlane → ℂ} (hF : F ∈ slashSpanPos g) : Continuous F := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨β, rfl⟩ := hF
    exact continuous_slash (CuspFormClass.holo g).continuous 2 _
  | zero => exact continuous_const
  | add F₁ F₂ _ _ h₁ h₂ => exact h₁.add h₂
  | smul c F _ h => exact h.const_smul c

end DescentEngine

end TwistedPeriodDescent

namespace TwistedPeriodDescent

open NumberField NumberField.AdelicLevel AdelicDock IsDedekindDomain

section Ideles

variable (q : ℕ) [Fact q.Prime]

private noncomputable def unitIdele (u : ℤ_[q]ˣ) : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map (finIncl (𝓞 ℚ) ℚ)
    (localUnit (𝓞 ℚ) ℚ (padicPlace q)
      (Units.map (padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))

private theorem unitIdele_inv (u : ℤ_[q]ˣ) : unitIdele q u⁻¹ = (unitIdele q u)⁻¹ := by
  unfold unitIdele
  rw [map_inv, map_inv, map_inv, map_inv]

private theorem unitIdele_mul (u v : ℤ_[q]ˣ) : unitIdele q (u * v) = unitIdele q u * unitIdele q v := by
  unfold unitIdele
  rw [map_mul, map_mul, map_mul, map_mul]

private theorem unitIdele_one : unitIdele q 1 = 1 := by
  unfold unitIdele
  rw [map_one, map_one, map_one, map_one]

private theorem chiSq_eq_sq (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : ℤ_[q]ˣ) :
    chiSq q ξ u = ((ξ (unitIdele q u) : ℂˣ) : ℂ) ^ 2 :=
  rfl

private theorem chiSq_mul (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u v : ℤ_[q]ˣ) :
    chiSq q ξ (u * v) = chiSq q ξ u * chiSq q ξ v := by
  rw [chiSq_eq_sq, chiSq_eq_sq, chiSq_eq_sq, unitIdele_mul, map_mul, Units.val_mul, mul_pow]

private theorem chiSq_one (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) : chiSq q ξ (1 : ℤ_[q]ˣ) = 1 := by
  rw [chiSq_eq_sq, unitIdele_one, map_one, Units.val_one, one_pow]

private theorem coe_component (u : ℤ_[q]ˣ) :
    ((Units.map (padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u) :
        ((padicPlace q).adicCompletion ℚ)ˣ) : (padicPlace q).adicCompletion ℚ) =
      padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q]) := by
  rw [Units.coe_map, Units.coe_map]
  rfl

private theorem valued_padicRingEquiv_coe_unit (u : ℤ_[q]ˣ) :
    Valued.v (padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q])) = 1 := by
  have hle : ∀ w : ℤ_[q]ˣ, Valued.v (padicRingEquiv q ((w : ℤ_[q]) : ℚ_[q])) ≤ 1 := fun w =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ (padicPlace q)).mp
      (padicRingEquiv_coe_mem q (w : ℤ_[q]))
  have hmul : Valued.v (padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q])) *
      Valued.v (padicRingEquiv q (((u⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) : ℚ_[q])) = 1 := by
    rw [← map_mul, ← map_mul, ← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one, map_one, map_one]
  refine le_antisymm (hle u) ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := hmul.symm
    _ ≤ Valued.v (padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q])) * 1 := mul_le_mul_right (hle u⁻¹) _
    _ = _ := mul_one _

private theorem unitAt_unitIdele (u : ℤ_[q]ˣ) :
    RatIdele.unitAt (padicPlace q) (unitIdele q u) = padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q]) := by
  have ht : Valued.v
      ((Units.map (padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u) :
        ((padicPlace q).adicCompletion ℚ)ˣ) : (padicPlace q).adicCompletion ℚ) = 1 := by
    rw [coe_component]
    exact valued_padicRingEquiv_coe_unit q u
  unfold unitIdele
  rw [RatIdele.unitAt_finIncl_localUnit_self _ _ ht, coe_component]

private theorem exists_units_coe_eq_natCast {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) :
    ∃ u : ℤ_[q]ˣ, (u : ℤ_[q]) = (ℓ : ℤ_[q]) := by
  have hnorm : ‖(ℓ : ℤ_[q])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => ?_)
    have hdvd : ((q : ℕ) : ℤ) ∣ ((ℓ : ℕ) : ℤ) := (PadicInt.norm_int_lt_one_iff_dvd _).mp (by exact_mod_cast hlt)
    have hqℓ : q ∣ ℓ := by exact_mod_cast hdvd
    exact hℓq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) hℓ).mp hqℓ).symm
  exact PadicInt.isUnit_iff.mpr hnorm

private theorem natGenerator_padicPlace (ℓ : ℕ) [Fact ℓ.Prime] :
    Rat.HeightOneSpectrum.natGenerator (padicPlace ℓ) = ℓ :=
  RatIdele.natGenerator_primesEquiv_symm ⟨ℓ, Fact.out⟩

private theorem eq_padicPlace_of_natGenerator_dvd {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : Rat.HeightOneSpectrum.natGenerator w ∣ q) : w = padicPlace q := by
  refine RatIdele.eq_of_natGenerator_eq ?_
  rw [natGenerator_padicPlace]
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) (Fact.out : q.Prime)).mp hw

private theorem valued_padicRingEquiv_natCast_self (ℓ : ℕ) [Fact ℓ.Prime] :
    Valued.v (padicRingEquiv ℓ ((ℓ : ℕ) : ℚ_[ℓ])) = WithZero.exp (-1 : ℤ) := by
  rw [map_natCast, ← map_natCast (algebraMap ℚ ((padicPlace ℓ).adicCompletion ℚ)), RatIdele.valued_algebraMap_rat]
  have h := RatIdele.valuation_natGenerator (padicPlace ℓ)
  rwa [natGenerator_padicPlace] at h

variable {q} [NeZero q]

private theorem coe_dirichletIdeleChar_unitIdele_inv (χ : DirichletCharacter ℂ q) {ℓ : ℕ}
    {u : ℤ_[q]ˣ} (hu : (u : ℤ_[q]) = (ℓ : ℤ_[q])) :
    ((χ.dirichletIdeleChar (unitIdele q u⁻¹) : ℂˣ) : ℂ) = χ ((ℓ : ℕ) : ZMod q) := by
  have hres : ((ℓ : ℕ) : ZMod q) * RatIdele.unitResidue q (unitIdele q u⁻¹) = 1 := by
    refine RatIdele.natCast_mul_unitResidue_eq_one q fun w hw => ?_
    obtain rfl := eq_padicPlace_of_natGenerator_dvd q hw
    have hℓ' : ((ℓ : ℕ) : (padicPlace q).adicCompletion ℚ) = padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q]) := by
      rw [hu, PadicInt.coe_natCast, map_natCast]
    rw [unitAt_unitIdele, hℓ', ← map_mul, ← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one, map_one]
  have hχ : χ ((ℓ : ℕ) : ZMod q) * χ (RatIdele.unitResidue q (unitIdele q u⁻¹)) = 1 := by
    rw [← map_mul, hres, map_one]
  rw [DirichletCharacter.coe_dirichletIdeleChar_apply]
  exact (eq_inv_of_mul_eq_one_left hχ).symm

private theorem coe_dirichletIdeleChar_map_localUnit (χ : DirichletCharacter ℂ q) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓq : ℓ ≠ q) (t : ((padicPlace ℓ).adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : (padicPlace ℓ).adicCompletion ℚ) = WithZero.exp (-1 : ℤ)) :
    ((χ.dirichletIdeleChar (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (padicPlace ℓ) t)) : ℂˣ) : ℂ) =
      χ ((ℓ : ℕ) : ZMod q) := by
  have hv : ¬ Rat.HeightOneSpectrum.natGenerator (padicPlace ℓ) ∣ q := by
    rw [natGenerator_padicPlace]
    exact fun h => hℓq ((Nat.prime_dvd_prime_iff_eq (Fact.out : ℓ.Prime) (Fact.out : q.Prime)).mp h)
  have h := DirichletCharacter.coe_dirichletIdeleChar_finIncl_localUnit_of_valued_exp_neg_one χ hv t ht
  rwa [natGenerator_padicPlace] at h

end Ideles

section Values

variable {q : ℕ} [Fact q.Prime]

private theorem coe_apply_map_localUnit_eq (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hξfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ ξ) (hξmod : HeckeCharacter.AdmitsModulus ℚ ξ (ratLevel q))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (t₁ t₂ : ((padicPlace ℓ).adicCompletion ℚ)ˣ)
    (ht₁ : Valued.v (t₁ : (padicPlace ℓ).adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (ht₂ : Valued.v (t₂ : (padicPlace ℓ).adicCompletion ℚ) = WithZero.exp (-1 : ℤ)) :
    ((ξ (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (padicPlace ℓ) t₁)) : ℂˣ) : ℂ) =
      ((ξ (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (padicPlace ℓ) t₂)) : ℂˣ) : ℂ) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hmod : HeckeCharacter.AdmitsModulus ℚ ξ (Ideal.span {((q : ℕ) : 𝓞 ℚ)}) := hξmod
  obtain ⟨χ, hχ⟩ := hξfin.exists_dirichletIdeleChar_eq_of_admitsModulus hmod
  rw [← hχ, coe_dirichletIdeleChar_map_localUnit χ ℓ hℓq t₁ ht₁, coe_dirichletIdeleChar_map_localUnit χ ℓ hℓq t₂ ht₂]

private theorem coe_apply_uniformizerIdele_mul_coe_apply_unitIdele (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hξfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ ξ) (hξmod : HeckeCharacter.AdmitsModulus ℚ ξ (ratLevel q))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q)
    {u : ℤ_[q]ˣ} (hu : (u : ℤ_[q]) = (ℓ : ℤ_[q])) :
    ((ξ (AutomorphicForm.uniformizerIdele ℚ (@padicPlace ℓ ⟨hℓ⟩)) : ℂˣ) : ℂ) * ((ξ (unitIdele q u) : ℂˣ) : ℂ) = 1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hmod : HeckeCharacter.AdmitsModulus ℚ ξ (Ideal.span {((q : ℕ) : 𝓞 ℚ)}) := hξmod
  obtain ⟨χ, hχ⟩ := hξfin.exists_dirichletIdeleChar_eq_of_admitsModulus hmod
  have h1 : ((ξ (AutomorphicForm.uniformizerIdele ℚ (padicPlace ℓ)) : ℂˣ) : ℂ) = χ ((ℓ : ℕ) : ZMod q) := by
    rw [← hχ]
    exact coe_dirichletIdeleChar_map_localUnit χ ℓ hℓq _ (valued_uniformizerUnit ℚ (padicPlace ℓ))
  have h2 : ((ξ (unitIdele q u⁻¹) : ℂˣ) : ℂ) = χ ((ℓ : ℕ) : ZMod q) := by
    rw [← hχ]
    exact coe_dirichletIdeleChar_unitIdele_inv χ hu
  rw [unitIdele_inv, map_inv] at h2
  rw [h1, ← h2, Units.val_inv_eq_inv_val, inv_mul_cancel₀]
  exact Units.ne_zero _

end Values

section Det

private theorem det_finEmbed (x : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    Matrix.GeneralLinearGroup.det (finEmbed (𝓞 ℚ) ℚ x) =
      Units.map (finIncl (𝓞 ℚ) ℚ) (Matrix.GeneralLinearGroup.det x) := by
  refine Units.ext ?_
  rw [Units.coe_map]
  change (finMat (𝓞 ℚ) ℚ (x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))).det =
    finIncl (𝓞 ℚ) ℚ ((x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)).det)
  refine Prod.ext ?_ ?_
  · have h := RingHom.map_det (adeleArch (𝓞 ℚ) ℚ) (finMat (𝓞 ℚ) ℚ (x : Matrix _ _ _))
    rw [mapMatrix_arch_finMat, Matrix.det_one, adeleArch_apply] at h
    rw [finIncl_apply_fst]
    exact h
  · have h := RingHom.map_det (adeleFin (𝓞 ℚ) ℚ) (finMat (𝓞 ℚ) ℚ (x : Matrix _ _ _))
    rw [mapMatrix_fin_finMat, adeleFin_apply] at h
    rw [finIncl_apply_snd]
    exact h

private theorem det_localEmbed (v : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 2) (v.adicCompletion ℚ)) :
    Matrix.GeneralLinearGroup.det (localEmbed (𝓞 ℚ) ℚ v g) =
      localUnit (𝓞 ℚ) ℚ v (Matrix.GeneralLinearGroup.det g) := by
  refine Units.ext (Subtype.ext (funext fun w => ?_))
  change finAdeleEval (𝓞 ℚ) ℚ w (localMat (𝓞 ℚ) ℚ v (g : Matrix _ _ _)).det =
    finAdeleEval (𝓞 ℚ) ℚ w (localUnit (𝓞 ℚ) ℚ v (Matrix.GeneralLinearGroup.det g) : FiniteAdeleRing (𝓞 ℚ) ℚ)
  rw [RingHom.map_det, finAdeleEval_apply]
  by_cases hw : w = v
  · subst hw
    rw [mapMatrix_localMat_self, localUnit_apply_self]
    rfl
  · rw [mapMatrix_localMat_of_ne (𝓞 ℚ) ℚ v _ hw, Matrix.det_one, localUnit_apply_of_ne (𝓞 ℚ) ℚ v _ hw]

variable (ℓ : ℕ) [Fact ℓ.Prime]

private theorem det_padicGL (r : GL (Fin 2) ℚ_[ℓ]) :
    Matrix.GeneralLinearGroup.det (padicGL ℓ r) =
      Units.map (padicRingEquiv ℓ).toMonoidHom (Matrix.GeneralLinearGroup.det r) := by
  have hmat : ((padicGL ℓ r : GL (Fin 2) ((padicPlace ℓ).adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) ((padicPlace ℓ).adicCompletion ℚ)) =
      (padicRingEquiv ℓ).toRingHom.mapMatrix (r : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) := by
    ext i j
    simp [padicGL_apply]
  refine Units.ext ?_
  rw [Units.coe_map]
  change ((padicGL ℓ r : GL (Fin 2) ((padicPlace ℓ).adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) ((padicPlace ℓ).adicCompletion ℚ)).det =
    (padicRingEquiv ℓ).toMonoidHom ((r : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]).det)
  rw [hmat, ← RingHom.map_det]
  rfl

private theorem chiDet_padicToAdelic (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (r : GL (Fin 2) ℚ_[ℓ]) :
    AutomorphicForm.chiDet (𝓞 ℚ) ℚ ξ (padicToAdelic ℓ r) =
      ((ξ (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (padicPlace ℓ)
        (Units.map (padicRingEquiv ℓ).toMonoidHom (Matrix.GeneralLinearGroup.det r)))) : ℂˣ) : ℂ) := by
  unfold AutomorphicForm.chiDet
  rw [padicToAdelic_apply, det_finEmbed, padicToFinAdelic_apply, det_localEmbed, det_padicGL]

private theorem chiDet_mul (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (x y : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    AutomorphicForm.chiDet (𝓞 ℚ) ℚ ξ (x * y) =
      AutomorphicForm.chiDet (𝓞 ℚ) ℚ ξ x * AutomorphicForm.chiDet (𝓞 ℚ) ℚ ξ y := by
  unfold AutomorphicForm.chiDet
  rw [map_mul, map_mul, Units.val_mul]

private theorem chiDet_inv (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    AutomorphicForm.chiDet (𝓞 ℚ) ℚ ξ x⁻¹ = (AutomorphicForm.chiDet (𝓞 ℚ) ℚ ξ x)⁻¹ := by
  unfold AutomorphicForm.chiDet
  rw [map_inv, map_inv, Units.val_inv_eq_inv_val]

private theorem chiDet_padicToAdelic_of_det_eq {q : ℕ} [Fact q.Prime] (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hξfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ ξ) (hξmod : HeckeCharacter.AdmitsModulus ℚ ξ (ratLevel q))
    (hℓq : ℓ ≠ q) (r : GL (Fin 2) ℚ_[ℓ])
    (hr : ((Matrix.GeneralLinearGroup.det r : ℚ_[ℓ]ˣ) : ℚ_[ℓ]) = ((ℓ : ℕ) : ℚ_[ℓ])) :
    AutomorphicForm.chiDet (𝓞 ℚ) ℚ ξ (padicToAdelic ℓ r) =
      ((ξ (AutomorphicForm.uniformizerIdele ℚ (padicPlace ℓ)) : ℂˣ) : ℂ) := by
  rw [chiDet_padicToAdelic]
  unfold AutomorphicForm.uniformizerIdele
  refine coe_apply_map_localUnit_eq ξ hξfin hξmod ℓ hℓq _ _ ?_ (valued_uniformizerUnit ℚ (padicPlace ℓ))
  rw [Units.coe_map]
  change Valued.v (padicRingEquiv ℓ ((Matrix.GeneralLinearGroup.det r : ℚ_[ℓ]ˣ) : ℚ_[ℓ])) = _
  rw [hr]
  exact valued_padicRingEquiv_natCast_self ℓ

end Det

section Atoms

open RatIdele

variable {q : ℕ} [Fact q.Prime]

private theorem apply_eq_one_of_unitAt_eq_one (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hξfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ ξ) (hξmod : HeckeCharacter.AdmitsModulus ℚ ξ (ratLevel q))
    (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (hx : unitAt (padicPlace q) x = 1) : ξ x = 1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hmod : HeckeCharacter.AdmitsModulus ℚ ξ (Ideal.span {((q : ℕ) : 𝓞 ℚ)}) := hξmod
  obtain ⟨χ, hχ⟩ := hξfin.exists_dirichletIdeleChar_eq_of_admitsModulus hmod
  have hres : unitResidue q x = 1 := unitResidue_eq_one q fun w hw => by
    obtain rfl := eq_padicPlace_of_natGenerator_dvd q hw
    exact hx
  refine Units.ext ?_
  rw [← hχ, DirichletCharacter.coe_dirichletIdeleChar_apply, hres, map_one, inv_one, Units.val_one]

private theorem _root_.TwistedPeriodDescent.coe_finComponent (v : HeightOneSpectrum (𝓞 ℚ)) (w : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ((finComponent (𝓞 ℚ) ℚ v w : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      (finAdeleEval (𝓞 ℚ) ℚ v).mapMatrix (w : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  ext i j
  rfl

p2m_export "TwistedPeriodDescent" "coe_finComponent"

private theorem coe_glFin (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    ((glFin (𝓞 ℚ) ℚ h : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) =
      (adeleFin (𝓞 ℚ) ℚ).mapMatrix (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) := by
  ext i j
  rfl

private theorem valued_finAdeleEval_det_le_one {N : Ideal (𝓞 ℚ)} {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hm : IsLevelZeroMatrix (𝓞 ℚ) ℚ N m) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (finAdeleEval (𝓞 ℚ) ℚ v m.det) ≤ 1 := by
  have hint : ∀ i j, Valued.v (finAdeleEval (𝓞 ℚ) ℚ v (m i j)) ≤ 1 := fun i j =>
    valued_apply_le_one (hm.integral i j) v
  rw [Matrix.det_fin_two, map_sub, map_mul, map_mul]
  refine (Valued.v.map_sub _ _).trans (max_le ?_ ?_)
  · rw [Valuation.map_mul]
    exact mul_le_one' (hint 0 0) (hint 1 1)
  · rw [Valuation.map_mul]
    exact mul_le_one' (hint 0 1) (hint 1 0)

private theorem valued_det_eq_one_of_mem_finiteLevelZero {N : Ideal (𝓞 ℚ)} {w : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hw : w ∈ finiteLevelZero (𝓞 ℚ) ℚ N) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (((Matrix.GeneralLinearGroup.det w : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
  obtain ⟨h₁, h₂⟩ := (mem_finiteLevelZero_iff).mp hw
  have hle₁ := valued_finAdeleEval_det_le_one h₁ v
  have hle₂ := valued_finAdeleEval_det_le_one h₂ v
  have hmul : Valued.v (finAdeleEval (𝓞 ℚ) ℚ v (w : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)).det) *
      Valued.v (finAdeleEval (𝓞 ℚ) ℚ v
        ((w⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)).det) = 1 := by
    rw [← Valuation.map_mul, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one, Valuation.map_one]
  change Valued.v (finAdeleEval (𝓞 ℚ) ℚ v (w : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)).det) = 1
  refine le_antisymm hle₁ ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := hmul.symm
    _ ≤ Valued.v (finAdeleEval (𝓞 ℚ) ℚ v (w : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)).det) * 1 :=
        mul_le_mul_right hle₂ _
    _ = _ := mul_one _

private theorem chiDet_finEmbed_eq_one_of_finComponent_eq_one (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hξfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ ξ) (hξmod : HeckeCharacter.AdmitsModulus ℚ ξ (ratLevel q))
    {N : Ideal (𝓞 ℚ)} {w : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hw : w ∈ finiteLevelZero (𝓞 ℚ) ℚ N)
    (hq : finComponent (𝓞 ℚ) ℚ (padicPlace q) w = 1) :
    AutomorphicForm.chiDet (𝓞 ℚ) ℚ ξ (finEmbed (𝓞 ℚ) ℚ w) = 1 := by
  unfold AutomorphicForm.chiDet
  rw [det_finEmbed]
  set x : (AdeleRing (𝓞 ℚ) ℚ)ˣ := Units.map (finIncl (𝓞 ℚ) ℚ) (Matrix.GeneralLinearGroup.det w) with hxdef
  have hsnd : (x : AdeleRing (𝓞 ℚ) ℚ).2 =
      ((Matrix.GeneralLinearGroup.det w : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    rw [hxdef, Units.coe_map, finIncl_apply_snd]
  have hρ : ρ x = 1 := by
    refine ρ_eq_of_isNormalizer ⟨fun v => ?_, ?_⟩
    · rw [hsnd, valued_det_eq_one_of_mem_finiteLevelZero hw v, map_one]
    · rw [hxdef, archCoord_finIncl, Rat.cast_one, mul_one]
      exact zero_lt_one
  have hdetq : ((Matrix.GeneralLinearGroup.det w : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) (padicPlace q)
      = 1 := by
    change finAdeleEval (𝓞 ℚ) ℚ (padicPlace q) (w : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)).det = 1
    rw [RingHom.map_det, ← coe_finComponent, hq, Units.val_one, Matrix.det_one]
  have hunit : unitAt (padicPlace q) x = 1 := by
    unfold unitAt
    rw [hρ, map_one, inv_one, mul_one, hsnd, hdetq]
  rw [apply_eq_one_of_unitAt_eq_one ξ hξfin hξmod x hunit, Units.val_one]

private theorem archCoord_eq_of_isReal (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (v : InfinitePlace ℚ) (hv : v.IsReal) :
    archCoord x = InfinitePlace.Completion.ringEquivRealOfIsReal hv ((x : AdeleRing (𝓞 ℚ) ℚ).1 v) := by
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  rfl

private theorem archCoord_det (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    archCoord (Matrix.GeneralLinearGroup.det h) =
      ((LanglandsTunnell.ratArchGL2 h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  have hmat : ((LanglandsTunnell.ratArchGL2 h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (InfinitePlace.Completion.ringEquivRealOfIsReal
          (IsTotallyReal.isReal (default : InfinitePlace ℚ))).toRingHom.mapMatrix
        ((archEval ℚ default).mapMatrix
          ((adeleArch (𝓞 ℚ) ℚ).mapMatrix (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))) := by
    ext i j
    rfl
  rw [hmat, ← RingHom.map_det, ← RingHom.map_det, ← RingHom.map_det,
    archCoord_eq_of_isReal _ default (IsTotallyReal.isReal (default : InfinitePlace ℚ))]
  rfl

private theorem chiDet_eq_one_of_glFin_eq_one (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hξfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ ξ) (hξmod : HeckeCharacter.AdmitsModulus ℚ ξ (ratLevel q))
    (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    AutomorphicForm.chiDet (𝓞 ℚ) ℚ ξ h = 1 := by
  unfold AutomorphicForm.chiDet
  set x : (AdeleRing (𝓞 ℚ) ℚ)ˣ := Matrix.GeneralLinearGroup.det h with hxdef
  have hsnd : (x : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := by
    change adeleFin (𝓞 ℚ) ℚ (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)).det = 1
    rw [RingHom.map_det, ← coe_glFin, hh, Units.val_one, Matrix.det_one]
  have h1 : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) w = 1 := fun _ => rfl
  have hpos' : 0 < archCoord x := by
    rw [hxdef, archCoord_det]
    exact (Matrix.mem_glpos _).mp hpos
  have hρ : ρ x = 1 := by
    rw [ρ_eq_archSign_of_snd_eq_one fun w => by rw [hsnd, h1 w]]
    unfold archSign
    rw [if_pos hpos']
  have hunit : unitAt (padicPlace q) x = 1 := by
    unfold unitAt
    rw [hρ, map_one, inv_one, mul_one, hsnd, h1]
  rw [apply_eq_one_of_unitAt_eq_one ξ hξfin hξmod x hunit, Units.val_one]

private theorem idealMultiplicity_padicPlace_ratLevel :
    HeckeCharacter.idealMultiplicity ℚ (padicPlace q) (ratLevel q) = 1 := by
  have hq : ratLevel q = (padicPlace q).asIdeal := by
    rw [asIdeal_eq_span_natGenerator, natGenerator_padicPlace]
    rfl
  unfold HeckeCharacter.idealMultiplicity
  rw [hq]
  exact Associates.count_self (Associates.irreducible_mk.mpr (padicPlace q).prime.irreducible)

private theorem valued_padicRingEquiv_coe_sub_one_le {u : ℤ_[q]ˣ} (hu : PadicInt.toZMod (u : ℤ_[q]) = 1) :
    Valued.v (padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q]) - 1) ≤ WithZero.exp (-1 : ℤ) := by
  have hker : (u : ℤ_[q]) - 1 ∈ RingHom.ker (PadicInt.toZMod : ℤ_[q] →+* ZMod q) := by
    rw [RingHom.mem_ker, map_sub, hu, map_one, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hker
  obtain ⟨w, hw⟩ := hker
  have hcoe : padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q]) - 1 =
      padicRingEquiv q ((q : ℕ) : ℚ_[q]) * padicRingEquiv q ((w : ℤ_[q]) : ℚ_[q]) := by
    rw [← map_one (padicRingEquiv q), ← map_sub, ← map_mul, ← PadicInt.coe_one, ← PadicInt.coe_sub, hw,
      PadicInt.coe_mul, PadicInt.coe_natCast]
  have hwle : Valued.v (padicRingEquiv q ((w : ℤ_[q]) : ℚ_[q])) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ (padicPlace q)).mp (padicRingEquiv_coe_mem q w)
  rw [hcoe, Valuation.map_mul, valued_padicRingEquiv_natCast_self q]
  calc WithZero.exp (-1 : ℤ) * Valued.v (padicRingEquiv q ((w : ℤ_[q]) : ℚ_[q]))
      ≤ WithZero.exp (-1 : ℤ) * 1 := mul_le_mul_right hwle _
    _ = WithZero.exp (-1 : ℤ) := mul_one _

private theorem chiSq_eq_one_of_toZMod_eq_one (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hξmod : HeckeCharacter.AdmitsModulus ℚ ξ (ratLevel q)) {u : ℤ_[q]ˣ}
    (hu : PadicInt.toZMod (u : ℤ_[q]) = 1) : chiSq q ξ u = 1 := by
  have hξ : ξ (unitIdele q u) = 1 := by
    refine hξmod (unitIdele q u) ?_ ?_
    · unfold unitIdele
      rw [Units.coe_map, finIncl_apply_fst]
    · intro v
      unfold unitIdele
      rw [Units.coe_map, finIncl_apply_snd]
      by_cases hv : v = padicPlace q
      · subst hv
        rw [localUnit_apply_self, coe_component, idealMultiplicity_padicPlace_ratLevel]
        exact ⟨valued_padicRingEquiv_coe_unit q u, by simpa using valued_padicRingEquiv_coe_sub_one_le hu⟩
      · rw [localUnit_apply_of_ne (𝓞 ℚ) ℚ (padicPlace q) _ hv, sub_self, Valuation.map_one, Valuation.map_zero]
        exact ⟨rfl, zero_le'⟩
  rw [chiSq_eq_sq, hξ, Units.val_one, one_pow]

end Atoms

end TwistedPeriodDescent

open NumberField AdelicDock IsDedekindDomain

namespace TwistedPeriodDescent

namespace DescentSupportB

open NumberField NumberField.AdelicLevel AdelicDock IsDedekindDomain

section S5

variable {q : ℕ} [Fact q.Prime]

private theorem finComponent_lowerRight_eq {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} {c : GL (Fin 2) ℤ_[q]}
    (hcfin : padicGL q (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c)
      = finComponent (𝓞 ℚ) ℚ (padicPlace q) u) :
    ((finComponent (𝓞 ℚ) ℚ (padicPlace q) u : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ)) 1 1
      = padicRingEquiv q (((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1 : ℤ_[q]) : ℚ_[q]) := by
  rw [← hcfin, padicGL_apply, Matrix.GeneralLinearGroup.map_apply, PadicInt.algebraMap_apply]

private theorem lowerLeft_mem_span_of_mem_finiteLevelZero {N : ℕ} (hN : N ≠ 0)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N))
    {c : GL (Fin 2) ℤ_[q]}
    (hcfin : padicGL q (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c)
      = finComponent (𝓞 ℚ) ℚ (padicPlace q) u) :
    (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0 ∈ Ideal.span {(q : ℤ_[q]) ^ N.factorization q} := by
  rw [← valued_coe_le_idealBound_iff q hN]
  have hcoe : padicRingEquiv q (((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0 : ℤ_[q]) : ℚ_[q])
      = (finComponent (𝓞 ℚ) ℚ (padicPlace q) u : Matrix (Fin 2) (Fin 2) _) 1 0 := by
    rw [← hcfin, padicGL_apply, Matrix.GeneralLinearGroup.map_apply, PadicInt.algebraMap_apply]
  rw [hcoe, finComponent_apply]
  exact (mem_finiteLevelZero_iff.mp hu).1.lowerLeft (padicPlace q)

private theorem lowerRight_sub_one_mem_span_of_mem_finiteLevelOne {N : ℕ} (hN : N ≠ 0)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N))
    {c : GL (Fin 2) ℤ_[q]}
    (hcfin : padicGL q (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c)
      = finComponent (𝓞 ℚ) ℚ (padicPlace q) u) :
    (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1 - 1 ∈ Ideal.span {(q : ℤ_[q]) ^ N.factorization q} := by
  rw [← valued_coe_le_idealBound_iff q hN]
  have hcoe : padicRingEquiv q ((((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1 - 1 : ℤ_[q])) : ℚ_[q])
      = (finComponent (𝓞 ℚ) ℚ (padicPlace q) u : Matrix (Fin 2) (Fin 2) _) 1 1 - 1 := by
    rw [← hcfin, padicGL_apply, Matrix.GeneralLinearGroup.map_apply, PadicInt.algebraMap_apply,
      PadicInt.coe_sub, PadicInt.coe_one, map_sub, map_one]
  rw [hcoe, DescentSupportA.coe_finComponent, RingHom.mapMatrix_apply, Matrix.map_apply,
    ← map_one (finAdeleEval (𝓞 ℚ) ℚ (padicPlace q)), ← map_sub, finAdeleEval_apply]
  exact (mem_finiteLevelOne_iff.mp hu).1.lowerRight (padicPlace q)

private theorem exists_units_eq_of_sub_one_mem_span {n : ℕ} (hn : n ≠ 0) {x : ℤ_[q]}
    (hx : x - 1 ∈ Ideal.span {(q : ℤ_[q]) ^ n}) :
    ∃ d : ℤ_[q]ˣ, (d : ℤ_[q]) = x ∧ ‖(d : ℤ_[q]) - 1‖ < 1 := by
  have hdvd : (q : ℤ_[q]) ∣ x - 1 := by
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp hx
    exact ⟨(q : ℤ_[q]) ^ (n - 1) * k, by
      rw [hk, ← mul_assoc, ← pow_succ']
      congr 2; omega⟩
  have hlt : ‖x - 1‖ < 1 := (PadicInt.norm_lt_one_iff_dvd _).mpr hdvd
  have hnon : 1 - x ∈ nonunits ℤ_[q] := PadicInt.mem_nonunits.mpr (by rwa [norm_sub_rev])
  have hunit : IsUnit x := by simpa using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hnon
  obtain ⟨d, hd⟩ := hunit
  exact ⟨d, hd, by rw [hd]; exact hlt⟩

private theorem exists_finComponent_eq_centralGL_mul_of_lowerRight {N : ℕ} (hN : N ≠ 0)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N))
    {d : ℤ_[q]ˣ}
    (hd : ((finComponent (𝓞 ℚ) ℚ (padicPlace q) u : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ)) 1 1 = padicRingEquiv q ((d : ℤ_[q]) : ℚ_[q])) :
    ∃ k : GL (Fin 2) ℚ_[q], k ∈ LocalNewvector.padicK1 q (N.factorization q) ∧
      finComponent (𝓞 ℚ) ℚ (padicPlace q) u
        = padicGL q (LocalNewvector.centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom d) * k) := by
  obtain ⟨c, hcfin⟩ := exists_padicGL_map_eq_finComponent (q := q) hu
  have hc10 := lowerLeft_mem_span_of_mem_finiteLevelZero hN hu hcfin

  have hd' : (d : ℤ_[q]) = (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1 := by
    have h := hd
    rw [finComponent_lowerRight_eq hcfin] at h
    exact Subtype.ext ((padicRingEquiv q).injective h).symm
  set sc : GL (Fin 2) ℤ_[q] :=
    Units.map (algebraMap ℤ_[q] (Matrix (Fin 2) (Fin 2) ℤ_[q])).toMonoidHom d with hsc
  set k' : GL (Fin 2) ℤ_[q] := sc⁻¹ * c with hk'
  have hsc_inv_coe : ((sc⁻¹ : GL (Fin 2) ℤ_[q]) : Matrix (Fin 2) (Fin 2) ℤ_[q])
      = (↑d⁻¹ : ℤ_[q]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[q]) := by
    rw [hsc, ← map_inv]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Algebra.algebraMap_eq_smul_one]
  have hk'_row1 : ∀ j, (k' : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 j
      = (↑d⁻¹ : ℤ_[q]) * (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 j := fun j => by
    rw [hk', Units.val_mul, hsc_inv_coe, Matrix.smul_mul, one_mul, Matrix.smul_apply, smul_eq_mul]
  refine ⟨Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) k', ?_, ?_⟩
  · rw [LocalNewvector.mem_congruenceK1_iff]
    refine ⟨k', rfl, ?_, ?_⟩
    · rw [hk'_row1 0]; exact Ideal.mul_mem_left _ _ hc10
    · rw [hk'_row1 1, ← hd', d.inv_mul, sub_self]; exact Ideal.zero_mem _
  · rw [← map_algebraMap_scalar_eq_centralGL d, ← hsc, ← map_mul, hk', mul_inv_cancel_left, hcfin]

private theorem exists_units_lowerRight_of_mem_finiteLevelOne {N : ℕ} (hN : N ≠ 0) (hNq : N.factorization q ≠ 0)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N)) :
    ∃ d : ℤ_[q]ˣ,
      ((finComponent (𝓞 ℚ) ℚ (padicPlace q) u : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) :
          Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ)) 1 1 = padicRingEquiv q ((d : ℤ_[q]) : ℚ_[q]) ∧
        ‖(d : ℤ_[q]) - 1‖ < 1 := by
  obtain ⟨c, hcfin⟩ :=
    exists_padicGL_map_eq_finComponent (q := q) (finiteLevelOne_le_finiteLevelZero (𝓞 ℚ) ℚ _ hu)
  obtain ⟨d, hd, hd1⟩ :=
    exists_units_eq_of_sub_one_mem_span hNq (lowerRight_sub_one_mem_span_of_mem_finiteLevelOne hN hu hcfin)
  exact ⟨d, by rw [finComponent_lowerRight_eq hcfin, hd], hd1⟩

end S5

end DescentSupportB

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open scoped ModularForm MatrixGroups

section CharacterAtoms

variable (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)

private theorem chiDet_mul' (x z : AdelicGL2 (𝓞 ℚ) ℚ) :
    chiDet (𝓞 ℚ) ℚ ξ (x * z) = chiDet (𝓞 ℚ) ℚ ξ x * chiDet (𝓞 ℚ) ℚ ξ z := by
  simp only [chiDet, map_mul, Units.val_mul]

private theorem toZMod_eq_one_of_norm_sub_one_lt_one {q : ℕ} [Fact q.Prime] {x : ℤ_[q]} (hx : ‖x - 1‖ < 1) :
    PadicInt.toZMod x = 1 := by
  have hmem : x - 1 ∈ IsLocalRing.maximalIdeal ℤ_[q] :=
    (IsLocalRing.mem_maximalIdeal _).mpr (PadicInt.mem_nonunits.mpr hx)
  rwa [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem

private theorem chiSq_eq_one_of_norm_sub_one_lt_one {q : ℕ} [Fact q.Prime]
    (hξmod : HeckeCharacter.AdmitsModulus ℚ ξ (ratLevel q)) (u : ℤ_[q]ˣ) (hu : ‖(u : ℤ_[q]) - 1‖ < 1) :
    chiSq q ξ u = 1 :=
  chiSq_eq_one_of_toZMod_eq_one ξ hξmod (toZMod_eq_one_of_norm_sub_one_lt_one hu)

end CharacterAtoms

section Twisted

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable {ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}

private theorem fnTwist_globalPoints_mul (hΦg : g.IsAdelicLiftOf Φ)
    (hξfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ ξ) (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fnTwist ℚ ξ Φ (globalPoints (𝓞 ℚ) ℚ γ * z) = fnTwist ℚ ξ Φ z := by
  rw [fnTwist_apply, fnTwist_apply, chiDet_globalPoints_mul ℚ ξ hξfin.isIdeleClassChar, hΦg.left_inv]

private theorem fnTwist_mul_finEmbed (hM : M ≠ 0) (hΦg : g.IsAdelicLiftOf Φ) {q : ℕ} [Fact q.Prime]
    (hξfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ ξ) (hξmod : HeckeCharacter.AdmitsModulus ℚ ξ (ratLevel q)) {w : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hw : w ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M)) (hwq : finComponent (𝓞 ℚ) ℚ (padicPlace q) w = 1)
    (x : AdelicGL2 (𝓞 ℚ) ℚ) : fnTwist ℚ ξ Φ (x * finEmbed (𝓞 ℚ) ℚ w) = fnTwist ℚ ξ Φ x := by
  rw [fnTwist_apply, fnTwist_apply, chiDet_mul', chiDet_finEmbed_eq_one_of_finComponent_eq_one ξ hξfin hξmod hw hwq,
    mul_one, hΦg.levelZero_inv hM w hw]

private theorem exists_hasReading_padic_smul_self_fnTwist (hM : M ≠ 0) (hΦg : g.IsAdelicLiftOf Φ)
    (hξfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ ξ) {q : ℕ} [Fact q.Prime]
    (hξmod : HeckeCharacter.AdmitsModulus ℚ ξ (ratLevel q)) (x : GL (Fin 2) ℚ_[q]) :
    ∃ F ∈ slashSpanPos g, HasReading (x • AdelicSpan.self (fnTwist ℚ ξ Φ)) F := by
  obtain ⟨δ, a, u, ha, hapos, hu, hdec⟩ :=
    exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hM (padicToAdelic q x)
  have harch : LanglandsTunnell.ratArchGL2 a = (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) δ)⁻¹ := by
    have h0 : LanglandsTunnell.ratArchGL2 (padicToAdelic q x) = 1 := by
      rw [padicToAdelic_apply]; exact ratArch_finEmbed _
    rw [hdec, ratArch_mul, ratArch_mul, ratArch_finEmbed, mul_one, ratArch_globalPoints] at h0
    exact eq_inv_of_mul_eq_one_right h0

  have hδpos : 0 < ((Matrix.GeneralLinearGroup.det (δ⁻¹ : GL (Fin 2) ℚ) : ℚˣ) : ℚ) := by
    have h1 := (Matrix.mem_glpos _).mp hapos
    rw [harch, ← map_inv, Matrix.GeneralLinearGroup.map_det] at h1
    simpa using h1
  refine ⟨chiDet (𝓞 ℚ) ℚ ξ (padicToAdelic q x) • ((⇑g) ∣[(2 : ℤ)] δ⁻¹.map (Rat.castHom ℝ)),
    Submodule.smul_mem _ _ (slash_map_mem_slashSpanPos g δ⁻¹ hδpos), ?_⟩
  intro h hh hpos
  have hval : fn (x • AdelicSpan.self (fnTwist ℚ ξ Φ)) h = fnTwist ℚ ξ Φ (h * padicToAdelic q x) := by
    show (AdelicSpan.toFn _ _).toFn h = _
    rw [AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul, AdelicSpan.toFn_self,
      AdelicFnCarrier.toFn_mk]
  have hre : h * globalPoints (𝓞 ℚ) ℚ δ * a
      = globalPoints (𝓞 ℚ) ℚ δ * (((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) * a) := by
    group
  have hh' : glFin (𝓞 ℚ) ℚ (((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) * a) = 1 := by
    rw [map_mul, glFin_conj_eq_one δ hh, ha, mul_one]
  have hratarch : LanglandsTunnell.ratArchGL2 (((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) * a)
      = (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) δ)⁻¹ * LanglandsTunnell.ratArchGL2 h := by
    rw [ratArch_mul, ratArch_mul, ratArch_mul, ratArch_inv, ratArch_globalPoints, harch, mul_assoc,
      mul_inv_cancel, mul_one]
  have hpos' : LanglandsTunnell.ratArchGL2 (((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) * a)
      ∈ Matrix.GLPos (Fin 2) ℝ := by
    rw [hratarch, ← harch]
    exact Subgroup.mul_mem _ hapos hpos

  have hΦval : Φ (h * padicToAdelic q x)
      = (((⇑g) ∣[(2 : ℤ)] δ⁻¹.map (Rat.castHom ℝ)) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := by
    rw [hdec, ← mul_assoc, ← mul_assoc, hΦg.level_inv u hu, hre, hΦg.left_inv, hΦg.apply_eq _ hh' hpos', hratarch,
      SlashAction.slash_mul, map_inv]

  rw [hval, fnTwist_apply, hΦval, ModularForm.smul_slash, Pi.smul_apply,
    σ_apply_of_det_pos ((Matrix.mem_glpos _).mp hpos), smul_eq_mul, chiDet_mul',
    chiDet_eq_one_of_glFin_eq_one ξ hξfin hξmod h hh hpos, one_mul]

private theorem exists_hasReading_of_mem_span_fnTwist (hM : M ≠ 0) (hΦg : g.IsAdelicLiftOf Φ)
    (hξfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ ξ) {q : ℕ} [Fact q.Prime]
    (hξmod : HeckeCharacter.AdmitsModulus ℚ ξ (ratLevel q)) {y : AdelicSpan (fnTwist ℚ ξ Φ)}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self (fnTwist ℚ ξ Φ))) :
    ∃ F ∈ slashSpanPos g, HasReading y F := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    exact exists_hasReading_padic_smul_self_fnTwist hM hΦg hξfin hξmod x
  | zero => exact ⟨0, Submodule.zero_mem _, hasReading_zero⟩
  | add y₁ y₂ _ _ ih₁ ih₂ =>
    obtain ⟨F₁, hF₁, h₁⟩ := ih₁
    obtain ⟨F₂, hF₂, h₂⟩ := ih₂
    exact ⟨F₁ + F₂, Submodule.add_mem _ hF₁ hF₂, hasReading_add h₁ h₂⟩
  | smul c y _ ih =>
    obtain ⟨F, hF, h⟩ := ih
    exact ⟨c • F, Submodule.smul_mem _ c hF, hasReading_smul h c⟩

end Twisted

section SpanVector

variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}

private theorem fn_globalPoints_mul_of_mem_span' (hleft : ∀ (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (globalPoints (𝓞 ℚ) ℚ γ * z) = φ z) {q : ℕ} [Fact q.Prime] {y : AdelicSpan φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ))
    (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    rw [fn_padic_smul_self, fn_padic_smul_self, mul_assoc, hleft]
  | zero => rfl
  | add y₁ y₂ _ _ ih₁ ih₂ => rw [fn_add, fn_add, ih₁, ih₂]
  | smul c y _ ih => rw [fn_csmul, fn_csmul, ih]

private theorem fn_mul_finEmbed_of_mem_span_of_qtrivial' {M : ℕ} {q : ℕ} [Fact q.Prime]
    (hK₀ : ∀ w ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M), finComponent (𝓞 ℚ) ℚ (padicPlace q) w = 1 →
      ∀ x, φ (x * finEmbed (𝓞 ℚ) ℚ w) = φ x)
    {y : AdelicSpan φ} (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ))
    {w : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hw : w ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M))
    (hwq : finComponent (𝓞 ℚ) ℚ (padicPlace q) w = 1) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn y (z * finEmbed (𝓞 ℚ) ℚ w) = fn y z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    rw [fn_padic_smul_self, fn_padic_smul_self, padicToAdelic_apply, mul_assoc, ← map_mul,
      DescentSupportA.commute_of_finComponent_eq_one (padicPlace q) hwq
        (fun w' hw' => finComponent_padicToFinAdelic_of_ne q x hw'),
      map_mul, ← mul_assoc, hK₀ w hw hwq]
  | zero => rfl
  | add y₁ y₂ _ _ ih₁ ih₂ => rw [fn_add, fn_add, ih₁, ih₂]
  | smul c y _ ih => rw [fn_csmul, fn_csmul, ih]

private theorem fn_mul_finEmbed_eq_chiSq_mul {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) {q : ℕ} [Fact q.Prime]
    (hfac : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q → N.factorization ℓ = M.factorization ℓ)
    (hK₀ : ∀ w ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M), finComponent (𝓞 ℚ) ℚ (padicPlace q) w = 1 →
      ∀ x, φ (x * finEmbed (𝓞 ℚ) ℚ w) = φ x)
    {y : AdelicSpan φ} (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ))
    (hfix : y ∈ fixedSubmodule (padicK1 q (N.factorization q)) (AdelicSpan φ))
    (hcent : ∀ d : ℤ_[q]ˣ, centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom d) • y = chiSq q ξ d • y)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N)) (d : ℤ_[q]ˣ)
    (hd : ((finComponent (𝓞 ℚ) ℚ (padicPlace q) u : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ)) 1 1 = padicRingEquiv q ((d : ℤ_[q]) : ℚ_[q]))
    (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn y (z * finEmbed (𝓞 ℚ) ℚ u) = chiSq q ξ d * fn y z := by
  obtain ⟨k, hk, hcomp⟩ := DescentSupportB.exists_finComponent_eq_centralGL_mul_of_lowerRight hN hu hd
  have hunit : Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom d = Units.map PadicInt.Coe.ringHom.toMonoidHom d :=
    Units.ext (PadicInt.algebraMap_apply _)
  set c : GL (Fin 2) ℚ_[q] := centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom d) * k with hc
  rw [hunit] at hcomp
  have hw : u * (padicToFinAdelic q c)⁻¹ ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M) :=
    DescentSupportB.mul_padicToFinAdelic_inv_mem_finiteLevelZero
      (fun v hv => DescentSupportB.idealBound_ratLevel_eq_of_factorization_eq hN hM hfac v hv) hu c hcomp
  have hwq : finComponent (𝓞 ℚ) ℚ (padicPlace q) (u * (padicToFinAdelic q c)⁻¹) = 1 := by
    rw [map_mul, map_inv, finComponent_padicToFinAdelic_self q, hcomp, mul_inv_cancel]
  have hcy : c • y = chiSq q ξ d • y := by
    rw [hc, mul_smul, mem_fixedSubmodule_iff.mp hfix k hk, hcent]
  have hsplit : u = u * (padicToFinAdelic q c)⁻¹ * padicToFinAdelic q c := by group
  rw [hsplit, map_mul, ← mul_assoc, ← padicToAdelic_apply, ← fn_padic_smul, hcy, fn_csmul,
    fn_mul_finEmbed_of_mem_span_of_qtrivial' hK₀ hy hw hwq]

private theorem glFin_globalPoints_mapGL_lowerRight {q : ℕ} [Fact q.Prime] (γ : SL(2, ℤ)) :
    ((finComponent (𝓞 ℚ) ℚ (padicPlace q)
        (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ))) :
          GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ)) 1 1
      = padicRingEquiv q (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ_[q]) : ℚ_[q]) := by
  have hentry : ((Matrix.SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1
      = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ) := by
    simp [Matrix.SpecialLinearGroup.mapGL]
  rw [DescentSupportA.coe_finComponent, RingHom.mapMatrix_apply, Matrix.map_apply, glFin_globalPoints_eq_map,
    Matrix.GeneralLinearGroup.map_apply, finAdeleEval_apply, hentry]
  exact DescentSupportB.algebraMap_intCast_apply_padicPlace_eq q _

private theorem slash_eq_inv_chiSq_smul_of_hasReading {N : ℕ} {q : ℕ} [Fact q.Prime] (hN : N ≠ 0)
    {y : AdelicSpan φ} {F : UpperHalfPlane → ℂ} (hF : Continuous F) (hread : HasReading y F)
    (hleft : ∀ (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ), fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z)
    (hright : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N), ∀ d : ℤ_[q]ˣ,
      ((finComponent (𝓞 ℚ) ℚ (padicPlace q) u : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) :
          Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ)) 1 1 = padicRingEquiv q ((d : ℤ_[q]) : ℚ_[q]) →
        ∀ z : AdelicGL2 (𝓞 ℚ) ℚ, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = chiSq q ξ d * fn y z)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (u : ℤ_[q]ˣ)
    (hu : ((u : ℤ_[q]) : ℚ_[q]) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ_[q])) :
    F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = (chiSq q ξ u)⁻¹ • F := by
  set δ : GL (Fin 2) ℚ := Matrix.SpecialLinearGroup.mapGL ℚ γ with hδ
  refine eq_of_forall_slash_apply_I (continuous_slash hF 2 _) (hF.const_smul (chiSq q ξ u)⁻¹) fun h hh hpos => ?_
  have hpos' : LanglandsTunnell.ratArchGL2 (archPart δ * h) ∈ Matrix.GLPos (Fin 2) ℝ := by
    rw [ratArch_archPart_mul, hδ, map_castHom_mapGL]
    exact Subgroup.mul_mem _ (mapGL_mem_GLPos γ) hpos
  have hread' := (hasReading_iff y F).mp hread
  have h1 := hread' (archPart δ * h) (glFin_archPart_mul hh δ) hpos'
  rw [ratArch_archPart_mul, hδ, map_castHom_mapGL, SlashAction.slash_mul] at h1
  rw [← hδ] at h1
  set G := glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ) with hGdef
  have hG : G ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) := glFin_globalPoints_mapGL_mem_finiteLevelZero hN hγ
  have h2 : archPart δ * h = globalPoints (𝓞 ℚ) ℚ δ * (h * finEmbed (𝓞 ℚ) ℚ G⁻¹) := by
    rw [archPart, mul_assoc, ← map_inv, finEmbed_mul_comm_of_glFin_eq_one hh]

  have hGu : ((finComponent (𝓞 ℚ) ℚ (padicPlace q) G : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ)) 1 1 = padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q]) := by
    rw [hGdef, hδ, glFin_globalPoints_mapGL_lowerRight, hu, PadicInt.coe_intCast]

  have h3 : fn y h = chiSq q ξ u * fn y (h * finEmbed (𝓞 ℚ) ℚ G⁻¹) := by
    rw [← hright G hG u hGu, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  rw [h2, hleft] at h1
  rw [← h1, ModularForm.smul_slash, Pi.smul_apply, σ_apply_of_det_pos ((Matrix.mem_glpos _).mp hpos), smul_eq_mul,
    ← hread' h hh hpos, h3, ← mul_assoc, inv_mul_cancel₀ (chiSq_ne_zero q ξ u), one_mul]

private theorem eq_zero_of_hasReading_zero' {N : ℕ} {q : ℕ} [Fact q.Prime] (hN : N ≠ 0) (hNq : N.factorization q ≠ 0)
    (hξmod : HeckeCharacter.AdmitsModulus ℚ ξ (ratLevel q)) {y : AdelicSpan φ} (hread : HasReading y 0)
    (hleft : ∀ (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ), fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z)
    (hright : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N), ∀ d : ℤ_[q]ˣ,
      ((finComponent (𝓞 ℚ) ℚ (padicPlace q) u : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) :
          Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ)) 1 1 = padicRingEquiv q ((d : ℤ_[q]) : ℚ_[q]) →
        ∀ z : AdelicGL2 (𝓞 ℚ) ℚ, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = chiSq q ξ d * fn y z) :
    y = 0 := by
  refine AdelicSpan.ext φ (AdelicFnCarrier.ext fun z => ?_)
  obtain ⟨γ, h, u, hh, hpos, hu, rfl⟩ := exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hN z
  obtain ⟨d, hd, hd1⟩ := DescentSupportB.exists_units_lowerRight_of_mem_finiteLevelOne hN hNq hu
  change fn y _ = fn (0 : AdelicSpan φ) _
  rw [fn_zero, hright u (finiteLevelOne_le_finiteLevelZero (𝓞 ℚ) ℚ _ hu) d hd,
    chiSq_eq_one_of_norm_sub_one_lt_one ξ hξmod d hd1, one_mul, hleft,
    (hasReading_iff y 0).mp hread h hh hpos, SlashAction.zero_slash]
  rfl

end SpanVector

end DescentEngine

section LevelArithmetic

open scoped MatrixGroups

variable {L q : ℕ}

private theorem ne_zero_of_factorization_eq_two' (hq2 : L.factorization q = 2) : L ≠ 0 := by
  rintro rfl
  simp at hq2

private theorem dvd_of_factorization_eq_two' (hq : q.Prime) (hq2 : L.factorization q = 2) : q ∣ L :=
  (Nat.Prime.dvd_iff_one_le_factorization hq (ne_zero_of_factorization_eq_two' hq2)).mpr (by omega)

private theorem div_ne_zero_of_factorization_eq_two' (hq : q.Prime) (hq2 : L.factorization q = 2) : L / q ≠ 0 :=
  (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (ne_zero_of_factorization_eq_two' hq2))
    (dvd_of_factorization_eq_two' hq hq2)) hq.pos).ne'

private theorem factorization_div_eq (hq : q.Prime) (hq2 : L.factorization q = 2) (ℓ : ℕ) :
    (L / q).factorization ℓ = L.factorization ℓ - (Nat.factorization q) ℓ := by
  rw [Nat.factorization_div (dvd_of_factorization_eq_two' hq hq2), Finsupp.coe_tsub, Pi.sub_apply]

private theorem factorization_div_self (hq : q.Prime) (hq2 : L.factorization q = 2) : (L / q).factorization q = 1 := by
  rw [factorization_div_eq hq hq2, hq2, Nat.Prime.factorization_self hq]

private theorem factorization_div_of_ne (hq : q.Prime) (hq2 : L.factorization q = 2) {ℓ : ℕ} (hℓq : ℓ ≠ q) :
    (L / q).factorization ℓ = L.factorization ℓ := by
  rw [factorization_div_eq hq hq2, Nat.Prime.factorization hq, Finsupp.single_eq_of_ne hℓq, Nat.sub_zero]

private theorem dvd_div_of_factorization_eq_two (hq : q.Prime) (hq2 : L.factorization q = 2) : q ∣ L / q :=
  (Nat.Prime.dvd_iff_one_le_factorization hq (div_ne_zero_of_factorization_eq_two' hq hq2)).mpr
    (le_of_eq (factorization_div_self hq hq2).symm)

private theorem exists_units_coe_eq_intCast [Fact q.Prime] {n : ℤ} (hn : ¬ ((q : ℕ) : ℤ) ∣ n) :
    ∃ u : ℤ_[q]ˣ, (u : ℤ_[q]) = (n : ℤ_[q]) := by
  have hnorm : ‖(n : ℤ_[q])‖ = 1 :=
    le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => hn ((PadicInt.norm_int_lt_one_iff_dvd _).mp hlt))
  obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.mpr hnorm
  exact ⟨u, hu⟩

private theorem exists_units_lowerRight_of_mem_GammaH [Fact q.Prime] {N : ℕ} (hqN : q ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CohCarrier.GammaH N ⊥) :
    γ ∈ CongruenceSubgroup.Gamma0 N ∧ ∃ u : ℤ_[q]ˣ,
      ((u : ℤ_[q]) : ℚ_[q]) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ_[q]) ∧ ‖(u : ℤ_[q]) - 1‖ < 1 := by
  obtain ⟨hγ0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  refine ⟨hγ0, ?_⟩

  have hd : ((N : ℕ) : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1 := by
    have h1 : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = 1 := by
      have h := congrArg Units.val (Subgroup.mem_bot.mp hH)
      rw [CohCarrier.val_gamma0Units, Units.val_one] at h
      simpa [CongruenceSubgroup.Gamma0Map] using h
    have h2 : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1 : ℤ) : ZMod N) = 0 := by
      push_cast; rw [h1, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
  have hdq : ((q : ℕ) : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1 := (Int.natCast_dvd_natCast.mpr hqN).trans hd
  have hnot : ¬ ((q : ℕ) : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := fun h => by
    have h1 : ((q : ℕ) : ℤ) ∣ (1 : ℤ) := by
      have h2 := dvd_sub h hdq
      rwa [sub_sub_cancel] at h2
    exact (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp (by exact_mod_cast h1))
  obtain ⟨u, hu⟩ := exists_units_coe_eq_intCast hnot
  refine ⟨u, by rw [hu, PadicInt.coe_intCast], ?_⟩
  rw [hu]
  have h3 := (PadicInt.norm_int_lt_one_iff_dvd (p := q) ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1)).mpr hdq
  simpa using h3

end LevelArithmetic

open NumberField AutomorphicForm LocalNewvector AdelicDock NumberField.AdelicLevel HeckeCharacter in
open scoped MatrixGroups ModularForm in

private theorem readingCore
    {L : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 L) 2}
    {q : ℕ} [Fact q.Prime] (hq2 : L.factorization q = 2)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (ξ : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hηfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ ξ)
    (hηmod : HeckeCharacter.AdmitsModulus ℚ ξ (AdelicDock.ratLevel q))
    (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ ξ Φ))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ ξ Φ)))
    (hy0 : y ≠ 0)
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q 1)
      (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ ξ Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ, LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y =
      ((ξ (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
          (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
            (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom
              (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) : ℂ) ^ 2) • y) :
    ∃ F : UpperHalfPlane → ℂ,
      F ∈ slashSpanPos g ∧ HasReading y F ∧ F ≠ 0 ∧
      (∀ (σ : CongruenceSubgroup.Gamma0 (L / q)) (u : ℤ_[q]ˣ),
        ((u : ℤ_[q]) : ℚ_[q]) =
            ((((σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ_[q]) →
          F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (chiSq q ξ u)⁻¹ • F) ∧
      (∀ γ : SL(2, ℤ), γ ∈ CohCarrier.GammaH (L / q) ⊥ →
          F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = F) ∧
      (∀ (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ), fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z) ∧
      (∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel (L / q)), ∀ d : ℤ_[q]ˣ,
        ((finComponent (𝓞 ℚ) ℚ (padicPlace q) u : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ)) 1 1 =
          padicRingEquiv q ((d : ℤ_[q]) : ℚ_[q]) →
            ∀ z : AdelicGL2 (𝓞 ℚ) ℚ, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = chiSq q ξ d * fn y z) := by
  have hq : q.Prime := Fact.out
  have hL : L ≠ 0 := ne_zero_of_factorization_eq_two' hq2
  have hN : L / q ≠ 0 := div_ne_zero_of_factorization_eq_two' hq hq2
  have hNq : (L / q).factorization q ≠ 0 := by rw [factorization_div_self hq hq2]; exact one_ne_zero
  have hfac : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q → (L / q).factorization ℓ = L.factorization ℓ :=
    fun ℓ _ hℓq => factorization_div_of_ne hq hq2 hℓq
  have hfix' : y ∈ fixedSubmodule (padicK1 q ((L / q).factorization q)) (AdelicSpan (fnTwist ℚ ξ Φ)) := by
    rwa [factorization_div_self hq hq2]
  have hcent' : ∀ d : ℤ_[q]ˣ, centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom d) • y = chiSq q ξ d • y :=
    fun d => hcent d

  have hleft : ∀ (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ), fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z :=
    DescentEngine.fn_globalPoints_mul_of_mem_span' (DescentEngine.fnTwist_globalPoints_mul hΦg hηfin) hy
  have hright : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel (L / q)), ∀ d : ℤ_[q]ˣ,
      ((finComponent (𝓞 ℚ) ℚ (padicPlace q) u : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) :
          Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ)) 1 1 = padicRingEquiv q ((d : ℤ_[q]) : ℚ_[q]) →
        ∀ z : AdelicGL2 (𝓞 ℚ) ℚ, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = chiSq q ξ d * fn y z :=
    fun u hu d hd z => DescentEngine.fn_mul_finEmbed_eq_chiSq_mul hL hN hfac
      (fun w hw hwq x => DescentEngine.fnTwist_mul_finEmbed hL hΦg hηfin hηmod hw hwq x) hy hfix' hcent' hu d hd z

  obtain ⟨F, hFspan, hread⟩ := DescentEngine.exists_hasReading_of_mem_span_fnTwist hL hΦg hηfin hηmod hy
  have hFcont : Continuous F := DescentEngine.continuous_of_mem_slashSpanPos hFspan
  have hslash : ∀ (σ : CongruenceSubgroup.Gamma0 (L / q)) (u : ℤ_[q]ˣ),
      ((u : ℤ_[q]) : ℚ_[q]) = ((((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ_[q]) →
        F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (chiSq q ξ u)⁻¹ • F :=
    fun σ u hu => DescentEngine.slash_eq_inv_chiSq_smul_of_hasReading hN hFcont hread hleft hright σ.2 u hu
  refine ⟨F, hFspan, hread, ?_, hslash, ?_, hleft, hright⟩
  · rintro rfl
    exact hy0 (DescentEngine.eq_zero_of_hasReading_zero' hN hNq hηmod hread hleft hright)
  · intro γ hγ
    obtain ⟨hγ0, u, hu, hu1⟩ := exists_units_lowerRight_of_mem_GammaH (dvd_div_of_factorization_eq_two hq hq2) hγ
    exact (hslash ⟨γ, hγ0⟩ u hu).trans
      (by rw [DescentEngine.chiSq_eq_one_of_norm_sub_one_lt_one ξ hηmod u hu1, inv_one, one_smul])

end TwistedPeriodDescent

namespace TwistedPeriodDescent

open NumberField AutomorphicForm LocalNewvector AdelicDock NumberField.AdelicLevel HeckeCharacter
open scoped ModularForm

namespace DescentEngine

open HeckeCosets

variable (ℓ : ℕ) [Fact ℓ.Prime]

private theorem coe_det_ρQ (i : Fin (ℓ + 1)) :
    ((Matrix.GeneralLinearGroup.det (ρQ ℓ i) : ℚ_[ℓ]ˣ) : ℚ_[ℓ]) = ((ℓ : ℕ) : ℚ_[ℓ]) := by
  change ((ρQ ℓ i : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]).det = _
  rw [coe_ρQ ℓ i, show (repZ ℓ i).map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) = (algebraMap ℤ_[ℓ] ℚ_[ℓ]).mapMatrix (repZ ℓ i) from rfl,
    ← RingHom.map_det, det_repZ, map_natCast]

variable {ℓ}

private theorem chiDet_finEmbed_ρA_inv {q : ℕ} [Fact q.Prime] (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hξfin : IsFiniteOrderHeckeChar ℚ ξ) (hξmod : AdmitsModulus ℚ ξ (ratLevel q)) (hℓq : ℓ ≠ q) (i : Fin (ℓ + 1)) :
    chiDet (𝓞 ℚ) ℚ ξ (finEmbed (𝓞 ℚ) ℚ (ρA ℓ i)⁻¹) =
      ((ξ (uniformizerIdele ℚ (padicPlace ℓ)) : ℂˣ) : ℂ)⁻¹ := by
  rw [ρA, map_inv, ← padicToAdelic_apply, chiDet_inv,
    chiDet_padicToAdelic_of_det_eq ℓ ξ hξfin hξmod hℓq (ρQ ℓ i) (coe_det_ρQ ℓ i)]

private theorem heckeAway_self_fnTwist_eq_smul {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {a : ℂ}
    (hΦ : heckeAway ℓ (AdelicSpan.self Φ) = a • AdelicSpan.self Φ)
    {q : ℕ} [Fact q.Prime] (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hξfin : IsFiniteOrderHeckeChar ℚ ξ) (hξmod : AdmitsModulus ℚ ξ (ratLevel q)) (hℓq : ℓ ≠ q) :
    heckeAway ℓ (AdelicSpan.self (fnTwist ℚ ξ Φ)) =
      (((ξ (uniformizerIdele ℚ (padicPlace ℓ)) : ℂˣ) : ℂ)⁻¹ * a) • AdelicSpan.self (fnTwist ℚ ξ Φ) := by
  have hΦz : ∀ z : AdelicGL2 (𝓞 ℚ) ℚ,
      ∑ i : Fin (ℓ + 1), Φ (z * finEmbed (𝓞 ℚ) ℚ (ρA ℓ i)⁻¹) = a * Φ z := by
    intro z
    have h := congrArg (fun w : AdelicSpan Φ => (AdelicSpan.toFn Φ w).toFn z) hΦ
    rw [heckeAway_self_apply ℓ] at h
    exact h
  refine AdelicSpan.ext _ (AdelicFnCarrier.ext fun z => ?_)
  rw [heckeAway_self_apply ℓ]
  change ∑ i : Fin (ℓ + 1), fnTwist ℚ ξ Φ (z * finEmbed (𝓞 ℚ) ℚ (ρA ℓ i)⁻¹) =
    (((ξ (uniformizerIdele ℚ (padicPlace ℓ)) : ℂˣ) : ℂ)⁻¹ * a) * fnTwist ℚ ξ Φ z
  have hterm : ∀ i : Fin (ℓ + 1), fnTwist ℚ ξ Φ (z * finEmbed (𝓞 ℚ) ℚ (ρA ℓ i)⁻¹) =
      (chiDet (𝓞 ℚ) ℚ ξ z * ((ξ (uniformizerIdele ℚ (padicPlace ℓ)) : ℂˣ) : ℂ)⁻¹) *
        Φ (z * finEmbed (𝓞 ℚ) ℚ (ρA ℓ i)⁻¹) := by
    intro i
    rw [fnTwist_apply, chiDet_mul, chiDet_finEmbed_ρA_inv ξ hξfin hξmod hℓq i]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum, hΦz z, fnTwist_apply]
  ring

omit [Fact ℓ.Prime] in

private theorem repMat_lowerRight (i : Fin (ℓ + 1)) : repMat ℓ i 1 1 = if (i : ℕ) < ℓ then (ℓ : ℤ) else 1 := by
  unfold repMat; split_ifs <;> rfl

private theorem finComponent_kRep_lowerRight {q : ℕ} [Fact q.Prime] (hqℓ : q ≠ ℓ) {uℓ : ℤ_[q]ˣ}
    (huℓ : ((uℓ : ℤ_[q]) : ℚ_[q]) = (ℓ : ℚ_[q])) (i : Fin (ℓ + 1)) :
    ((finComponent (𝓞 ℚ) ℚ (padicPlace q) (kRep ℓ i) : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ)) 1 1 =
      padicRingEquiv q (((if (i : ℕ) < ℓ then uℓ else 1 : ℤ_[q]ˣ) : ℤ_[q]) : ℚ_[q]) := by
  rw [finComponent_apply, kRep_entry_of_ne ℓ (padicPlace_ne ℓ hqℓ) i 1 1, coe_repQ, Matrix.map_apply,
    repMat_lowerRight, eq_intCast]
  split_ifs with hi
  · rw [DescentSupportB.algebraMap_intCast_apply_padicPlace_eq q, Int.cast_natCast, PadicInt.coe_natCast, huℓ]
  · rw [DescentSupportB.algebraMap_intCast_apply_padicPlace_eq q, Int.cast_one, Units.val_one]

private theorem sum_apply_eq_twisted_slash {q : ℕ} [Fact q.Prime] (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) {N : Ideal (𝓞 ℚ)}
    {ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {F : UpperHalfPlane → ℂ}
    (hleft : ∀ (γ : GL (Fin 2) ℚ) (x : AdelicGL2 (𝓞 ℚ) ℚ), ψ (globalPoints (𝓞 ℚ) ℚ γ * x) = ψ x)
    (hright : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ N, ∀ d : ℤ_[q]ˣ,
      ((finComponent (𝓞 ℚ) ℚ (padicPlace q) u : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) :
          Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ)) 1 1 = padicRingEquiv q ((d : ℤ_[q]) : ℚ_[q]) →
        ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, ψ (x * finEmbed (𝓞 ℚ) ℚ u) = chiSq q ξ d * ψ x)
    (happly : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 → LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
      ψ h = (F ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I)
    (hqℓ : q ≠ ℓ) {uℓ : ℤ_[q]ˣ} (huℓ : ((uℓ : ℤ_[q]) : ℚ_[q]) = (ℓ : ℚ_[q]))
    {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    ∑ i : Fin (ℓ + 1), ψ (h * finEmbed (𝓞 ℚ) ℚ (ρA ℓ i)⁻¹) =
      ((chiSq q ξ uℓ • (∑ j : Fin ℓ, F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ (j : ℕ)) +
          F ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix ℓ) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := by
  have hterm : ∀ i : Fin (ℓ + 1), ψ (h * finEmbed (𝓞 ℚ) ℚ (ρA ℓ i)⁻¹)
      = chiSq q ξ (if (i : ℕ) < ℓ then uℓ else 1) *
        ((F ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (repQ ℓ i))
          ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := by
    intro i
    have h1 : h * finEmbed (𝓞 ℚ) ℚ (ρA ℓ i)⁻¹
        = globalPoints (𝓞 ℚ) ℚ (repQ ℓ i)⁻¹
            * ((archPart (repQ ℓ i) * h) * finEmbed (𝓞 ℚ) ℚ (kRep ℓ i)) := by
      rw [← globalPoints_repQ_mul_mul_padicToAdelic_inv ℓ hh i, map_inv (globalPoints (𝓞 ℚ) ℚ),
        mul_assoc (globalPoints (𝓞 ℚ) ℚ (repQ ℓ i)) h, inv_mul_cancel_left]
      simp only [padicToAdelic_apply, map_inv, ρA]
    have hpos' : LanglandsTunnell.ratArchGL2 (archPart (repQ ℓ i) * h) ∈ Matrix.GLPos (Fin 2) ℝ := by
      rw [ratArch_archPart_mul]
      exact Subgroup.mul_mem _ (map_repQ_mem_GLPos ℓ i) hpos
    rw [h1, hleft, hright _ (kRep_mem_finiteLevelZero ℓ _ i) _ (finComponent_kRep_lowerRight hqℓ huℓ i),
      happly _ (glFin_archPart_mul hh _) hpos', ratArch_archPart_mul, SlashAction.slash_mul]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Fin.sum_univ_castSucc]

  have hlast : chiSq q ξ (if ((Fin.last ℓ : Fin (ℓ + 1)) : ℕ) < ℓ then uℓ else 1) = 1 := by
    rw [Fin.val_last, if_neg (lt_irrefl ℓ), chiSq_one]
  rw [hlast, one_mul, map_repQ_last_eq_heckeDiagMatrix ℓ]

  have hupper : ∀ j : Fin ℓ,
      chiSq q ξ (if ((Fin.castSucc j : Fin (ℓ + 1)) : ℕ) < ℓ then uℓ else 1) *
        ((F ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (repQ ℓ (Fin.castSucc j)))
          ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I
      = chiSq q ξ uℓ *
        ((F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ (j : ℕ)) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h)
          UpperHalfPlane.I := by
    intro j
    rw [Fin.val_castSucc, if_pos j.isLt, map_repQ_eq_heckeMatrix ℓ (i := Fin.castSucc j) j.isLt, Fin.val_castSucc]
  rw [Finset.sum_congr rfl fun j _ => hupper j, ← Finset.mul_sum]

  rw [SlashAction.add_slash, ModularForm.smul_slash, σ_apply_of_det_pos ((Matrix.mem_glpos _).mp hpos), Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  congr 2
  rw [show (∑ j : Fin ℓ, F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ (j : ℕ)) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h
      = ∑ j : Fin ℓ, (F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ (j : ℕ)) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h from
      map_sum (slashHom 2 (LanglandsTunnell.ratArchGL2 h)) _ Finset.univ, Finset.sum_apply]

omit [Fact ℓ.Prime] in

private theorem continuous_twisted_hecke {F : UpperHalfPlane → ℂ} (hF : Continuous F) (c : ℂ) :
    Continuous (c • (∑ j : Fin ℓ, F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ (j : ℕ)) +
      F ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix ℓ) := by
  refine Continuous.add (Continuous.const_smul ?_ c) (continuous_slash hF 2 _)
  have h : (∑ j : Fin ℓ, F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ (j : ℕ))
      = fun τ => ∑ j : Fin ℓ, (F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ (j : ℕ)) τ := by
    funext τ
    exact Finset.sum_apply τ _ _
  rw [h]
  exact continuous_finsetSum _ fun j _ => continuous_slash hF 2 _

private theorem twisted_hecke_reading_eq_smul {q : ℕ} [Fact q.Prime] (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) {N : Ideal (𝓞 ℚ)}
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {y : AdelicSpan φ} {F : UpperHalfPlane → ℂ} (hF : Continuous F)
    (hread : HasReading y F)
    (hleft : ∀ (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ), fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z)
    (hright : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ N, ∀ d : ℤ_[q]ˣ,
      ((finComponent (𝓞 ℚ) ℚ (padicPlace q) u : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) :
          Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ)) 1 1 = padicRingEquiv q ((d : ℤ_[q]) : ℚ_[q]) →
        ∀ z : AdelicGL2 (𝓞 ℚ) ℚ, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = chiSq q ξ d * fn y z)
    (hqℓ : q ≠ ℓ) {uℓ : ℤ_[q]ˣ} (huℓ : ((uℓ : ℤ_[q]) : ℚ_[q]) = (ℓ : ℚ_[q]))
    {c : ℂ} (heig : heckeAway ℓ y = c • y) :
    chiSq q ξ uℓ • (∑ j : Fin ℓ, F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ (j : ℕ)) +
      F ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix ℓ = c • F := by
  refine eq_of_forall_slash_apply_I (continuous_twisted_hecke hF _) (hF.const_smul c) fun h hh hpos => ?_
  have hread' := (hasReading_iff y F).mp hread
  rw [← sum_apply_eq_twisted_slash ξ (ψ := fn y) hleft hright hread' hqℓ huℓ hh hpos, ← fn_heckeAway ℓ, heig,
    fn_csmul, hread' h hh hpos, ModularForm.smul_slash, Pi.smul_apply,
    σ_apply_of_det_pos ((Matrix.mem_glpos _).mp hpos), smul_eq_mul]

end DescentEngine

open DescentEngine

private theorem heckeLaw
    {L : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 L) 2} (hg : g.IsNormalizedEigenform)
    {q : ℕ} [Fact q.Prime] (hq2 : L.factorization q = 2)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (ξ : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hηfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ ξ)
    (hηmod : HeckeCharacter.AdmitsModulus ℚ ξ (AdelicDock.ratLevel q))
    (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ ξ Φ))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ ξ Φ)))
    (F : UpperHalfPlane → ℂ) (hFspan : F ∈ slashSpanPos g) (hread : HasReading y F)
    (hleft : ∀ (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ), fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z)
    (hright : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel (L / q)), ∀ d : ℤ_[q]ˣ,
        ((finComponent (𝓞 ℚ) ℚ (padicPlace q) u : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ)) 1 1 =
          padicRingEquiv q ((d : ℤ_[q]) : ℚ_[q]) →
            ∀ z : AdelicGL2 (𝓞 ℚ) ℚ, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = chiSq q ξ d * fn y z)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L) (uℓ : ℤ_[q]ˣ) (huℓ : ((uℓ : ℤ_[q]) : ℚ_[q]) = (ℓ : ℚ_[q])) :
    ∑ j : Fin ℓ, F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ (j : ℕ) +
        (chiSq q ξ uℓ)⁻¹ • F ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix ℓ =
      ((ξ (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) *
          ModularFormClass.qCoeff g ℓ) • F := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hL : L ≠ 0 := by
    rintro rfl
    rw [Nat.factorization_zero, Finsupp.zero_apply] at hq2
    exact two_ne_zero hq2.symm
  have hqℓ : q ≠ ℓ := by
    rintro rfl
    exact hℓL (Nat.dvd_of_factorization_pos (by rw [hq2]; exact two_ne_zero))

  have hTg : ModularForm.heckeT 2 ℓ (⇑g) = ModularFormClass.qCoeff g ℓ • (⇑g) := by
    have h := congrArg (fun f : CuspForm (CongruenceSubgroup.Gamma0 L) 2 => (⇑f : UpperHalfPlane → ℂ))
      (CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul L g hg ℓ hℓ hℓL)
    simpa [CuspForm.coe_heckeTLin_apply, CuspForm.coe_smul] using h
  have hΦ : heckeAway ℓ (AdelicSpan.self Φ) = ModularFormClass.qCoeff g ℓ • AdelicSpan.self Φ :=
    heckeAway_self_eq_smul ℓ hL hℓL hΦg (hΦg.levelZero_inv hL) hTg

  set ϖ : ℂ := ((ξ (uniformizerIdele ℚ (padicPlace ℓ)) : ℂˣ) : ℂ) with hϖdef
  have hself : heckeAway ℓ (AdelicSpan.self (fnTwist ℚ ξ Φ)) =
      (ϖ⁻¹ * ModularFormClass.qCoeff g ℓ) • AdelicSpan.self (fnTwist ℚ ξ Φ) :=
    heckeAway_self_fnTwist_eq_smul hΦ ξ hηfin hηmod hqℓ.symm
  have heig : heckeAway ℓ y = (ϖ⁻¹ * ModularFormClass.qCoeff g ℓ) • y :=
    heckeAway_eq_smul_of_mem_span ℓ hqℓ hself hy

  have hdict := twisted_hecke_reading_eq_smul ξ (continuous_of_mem_slashSpanPos hFspan) hread hleft hright hqℓ huℓ
    heig

  have hu : (uℓ : ℤ_[q]) = (ℓ : ℤ_[q]) := by
    refine Subtype.ext ?_
    rw [PadicInt.coe_natCast]
    exact huℓ
  have hX : ((ξ (unitIdele q uℓ) : ℂˣ) : ℂ) = ϖ⁻¹ :=
    eq_inv_of_mul_eq_one_right (coe_apply_uniformizerIdele_mul_coe_apply_unitIdele ξ hηfin hηmod hℓ hqℓ.symm hu)
  have hχ : chiSq q ξ uℓ = (ϖ ^ 2)⁻¹ := by
    rw [chiSq_eq_sq, hX, inv_pow]
  have hχ0 : chiSq q ξ uℓ ≠ 0 := chiSq_ne_zero q ξ uℓ
  have hϖ0 : ϖ ≠ 0 := Units.ne_zero _
  calc ∑ j : Fin ℓ, F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ (j : ℕ) +
        (chiSq q ξ uℓ)⁻¹ • F ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix ℓ
      = (chiSq q ξ uℓ)⁻¹ • (chiSq q ξ uℓ • (∑ j : Fin ℓ, F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ (j : ℕ)) +
          F ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix ℓ) := by
        rw [smul_add, smul_smul, inv_mul_cancel₀ hχ0, one_smul]
    _ = (chiSq q ξ uℓ)⁻¹ • (ϖ⁻¹ * ModularFormClass.qCoeff g ℓ) • F := by rw [hdict]
    _ = (ϖ * ModularFormClass.qCoeff g ℓ) • F := by
        rw [smul_smul, hχ, inv_inv, sq, mul_assoc, ← mul_assoc ϖ ϖ⁻¹, mul_inv_cancel₀ hϖ0, one_mul]

end TwistedPeriodDescent

open scoped MatrixGroups

namespace TwistedPeriodDescent

open CohCarrier ModularCurve.Period UpperHalfPlane CongruenceSubgroup

section Transfer

variable {N : ℕ} {H : Subgroup (ZMod N)ˣ} {ℓ : ℕ}

private noncomputable def transferFactor (T : (GammaHUpper N H ℓ).LeftTransversal)
    (γ : ↥(GammaH N H)) (q : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ) : ↥(GammaHUpper N H ℓ) :=
  ⟨((T.2.leftQuotientEquiv q : ↥(GammaH N H)))⁻¹ * ((γ • T).2.leftQuotientEquiv q : ↥(GammaH N H)),
    QuotientGroup.leftRel_apply.mp <|
      Quotient.exact' ((T.2.leftQuotientEquiv.symm_apply_apply q).trans
        ((γ • T).2.leftQuotientEquiv.symm_apply_apply q).symm)⟩

private theorem heckeT_apply_ofMul [NeZero ℓ] (T : (GammaHUpper N H ℓ).LeftTransversal)
    {A : Type*} [AddCommGroup A] (φ : H1 N H A) (γ : ↥(GammaH N H)) :
    letI := (GammaHUpper N H ℓ).fintypeQuotientOfFiniteIndex
    heckeT N H ℓ A φ (Additive.ofMul γ) =
      ∑ q : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ,
        φ (Additive.ofMul (conjL N H ℓ (transferFactor T γ q))) := by
  letI := (GammaHUpper N H ℓ).fintypeQuotientOfFiniteIndex
  show Multiplicative.toAdd
      (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL N H ℓ)) γ) = _
  rw [MonoidHom.transfer_def _ T]
  simp only [Subgroup.leftTransversals.diff, toAdd_prod]
  rfl

end Transfer

section Trace

variable {N : ℕ} {H : Subgroup (ZMod N)ˣ} {ℓ : ℕ} [NeZero ℓ]

private noncomputable def diagGL (ℓ : ℕ) [NeZero ℓ] : GL (Fin 2) ℝ :=
  ModularForm.upperTriangularGL 1 0 ℓ (by rw [one_mul]; exact_mod_cast NeZero.ne ℓ)

private theorem conjRel_diagGL_conjL (t : ↥(GammaHUpper N H ℓ)) :
    conjRel (diagGL ℓ) ((t : ↥(GammaH N H)) : SL(2, ℤ))
      ((conjL N H ℓ t : ↥(GammaH N H)) : SL(2, ℤ)) := by
  have hb : ((((t : ↥(GammaH N H)) : SL(2, ℤ)) 0 1 / (ℓ : ℤ) : ℤ) : ℝ) * (ℓ : ℝ) =
      ((((t : ↥(GammaH N H)) : SL(2, ℤ)) 0 1 : ℤ) : ℝ) := by
    exact_mod_cast Int.ediv_mul_cancel (dvd_of_mem_GammaHUpper N H ℓ t)
  unfold conjRel
  refine (Matrix.GeneralLinearGroup.ext_iff _ _).mpr fun i j => ?_
  rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  fin_cases i <;> fin_cases j <;>
    simp [diagGL, conjL, conjUpperMat, Matrix.mul_apply, Fin.sum_univ_two, hb] <;> ring

private theorem diagGL_smul_smul (t : ↥(GammaHUpper N H ℓ)) (z : ℍ) :
    diagGL ℓ • (((t : ↥(GammaH N H)) : SL(2, ℤ)) • z) =
      ((conjL N H ℓ t : ↥(GammaH N H)) : SL(2, ℤ)) • (diagGL ℓ • z) :=
  (conjRel_diagGL_conjL t).smul_comm z

private noncomputable def heckeTrace (T : (GammaHUpper N H ℓ).LeftTransversal) (Fp : ℍ → ℂ) :
    ℍ → ℂ :=
  letI := (GammaHUpper N H ℓ).fintypeQuotientOfFiniteIndex
  fun w => ∑ q : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ,
    Fp (diagGL ℓ • ((((T.2.leftQuotientEquiv q : ↥(GammaH N H)) : SL(2, ℤ)))⁻¹ • w))

private theorem heckeTrace_smul_sub (T : (GammaHUpper N H ℓ).LeftTransversal) {Fp : ℍ → ℂ}
    (hFp : IsEquivariantPrimitive (GammaH N H) Fp) (γ : ↥(GammaH N H)) (w : ℍ) :
    heckeTrace T Fp ((γ : SL(2, ℤ)) • w) - heckeTrace T Fp w =
      heckeT N H ℓ ℂ hFp.periodHom (Additive.ofMul γ) := by
  letI := (GammaHUpper N H ℓ).fintypeQuotientOfFiniteIndex
  rw [heckeT_apply_ofMul T]
  have hterm : ∀ q : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ,
      Fp (diagGL ℓ • ((((T.2.leftQuotientEquiv q : ↥(GammaH N H)) : SL(2, ℤ)))⁻¹ •
        ((γ : SL(2, ℤ)) • w))) =
      Fp (diagGL ℓ • ((((T.2.leftQuotientEquiv (γ⁻¹ • q) : ↥(GammaH N H)) : SL(2, ℤ)))⁻¹ • w)) +
        hFp.period (conjL N H ℓ (transferFactor T γ q)) := by
    intro q
    have hβ : ((γ • T).2.leftQuotientEquiv q : ↥(GammaH N H)) =
        γ * (T.2.leftQuotientEquiv (γ⁻¹ • q) : ↥(GammaH N H)) := by
      rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, smul_eq_mul]
    have hfac : ((T.2.leftQuotientEquiv q : ↥(GammaH N H)))⁻¹ * γ =
        (transferFactor T γ q : ↥(GammaH N H)) *
          ((T.2.leftQuotientEquiv (γ⁻¹ • q) : ↥(GammaH N H)))⁻¹ := by
      show _ = ((T.2.leftQuotientEquiv q : ↥(GammaH N H)))⁻¹ *
          ((γ • T).2.leftQuotientEquiv q : ↥(GammaH N H)) * _
      rw [hβ]
      group
    have h1 : (((T.2.leftQuotientEquiv q : ↥(GammaH N H)) : SL(2, ℤ)))⁻¹ • ((γ : SL(2, ℤ)) • w) =
        ((transferFactor T γ q : ↥(GammaH N H)) : SL(2, ℤ)) •
          ((((T.2.leftQuotientEquiv (γ⁻¹ • q) : ↥(GammaH N H)) : SL(2, ℤ)))⁻¹ • w) :=
      calc (((T.2.leftQuotientEquiv q : ↥(GammaH N H)) : SL(2, ℤ)))⁻¹ • ((γ : SL(2, ℤ)) • w)
          = ((((T.2.leftQuotientEquiv q : ↥(GammaH N H)) : SL(2, ℤ)))⁻¹ * (γ : SL(2, ℤ))) • w :=
            (mul_smul _ _ _).symm
        _ = (((((T.2.leftQuotientEquiv q : ↥(GammaH N H)))⁻¹ * γ : ↥(GammaH N H))) : SL(2, ℤ)) • w := by
            rw [Subgroup.coe_mul, Subgroup.coe_inv]
        _ = ((((transferFactor T γ q : ↥(GammaH N H)) *
              ((T.2.leftQuotientEquiv (γ⁻¹ • q) : ↥(GammaH N H)))⁻¹ : ↥(GammaH N H))) : SL(2, ℤ)) • w := by
            rw [hfac]
        _ = ((transferFactor T γ q : ↥(GammaH N H)) : SL(2, ℤ)) •
              ((((T.2.leftQuotientEquiv (γ⁻¹ • q) : ↥(GammaH N H)) : SL(2, ℤ)))⁻¹ • w) := by
            rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]
    rw [h1, diagGL_smul_smul (transferFactor T γ q)]
    have h2 := hFp.sub_eq_period (conjL N H ℓ (transferFactor T γ q))
      (diagGL ℓ • ((((T.2.leftQuotientEquiv (γ⁻¹ • q) : ↥(GammaH N H)) : SL(2, ℤ)))⁻¹ • w))
    linear_combination h2
  have hre : (∑ q : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ,
      Fp (diagGL ℓ • ((((T.2.leftQuotientEquiv (γ⁻¹ • q) : ↥(GammaH N H)) : SL(2, ℤ)))⁻¹ • w))) =
      ∑ q : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ,
        Fp (diagGL ℓ • ((((T.2.leftQuotientEquiv q : ↥(GammaH N H)) : SL(2, ℤ)))⁻¹ • w)) :=
    Fintype.sum_equiv (MulAction.toPerm (γ⁻¹ : ↥(GammaH N H))) _ _ fun _ => rfl
  unfold heckeTrace
  simp only [hterm, Finset.sum_add_distrib, IsEquivariantPrimitive.periodHom_apply]
  linear_combination hre

private theorem isEquivariantPrimitive_heckeTrace (T : (GammaHUpper N H ℓ).LeftTransversal)
    {Fp : ℍ → ℂ} (hFp : IsEquivariantPrimitive (GammaH N H) Fp) :
    IsEquivariantPrimitive (GammaH N H) (heckeTrace T Fp) :=
  fun γ => ⟨heckeT N H ℓ ℂ hFp.periodHom (Additive.ofMul γ), fun w => heckeTrace_smul_sub T hFp γ w⟩

private theorem periodHom_heckeTrace (T : (GammaHUpper N H ℓ).LeftTransversal) {Fp : ℍ → ℂ}
    (hFp : IsEquivariantPrimitive (GammaH N H) Fp) :
    (isEquivariantPrimitive_heckeTrace T hFp).periodHom = heckeT N H ℓ ℂ hFp.periodHom :=
  AddMonoidHom.ext fun x => heckeTrace_smul_sub T hFp (Additive.toMul x) UpperHalfPlane.I

end Trace

section Cosets

open scoped ModularForm

variable {N : ℕ} {ℓ : ℕ} [NeZero ℓ]

private theorem mem_GammaH_bot {A : SL(2, ℤ)} (hc : ((A 1 0 : ℤ) : ZMod N) = 0)
    (hd : ((A 1 1 : ℤ) : ZMod N) = 1) : A ∈ GammaH N ⊥ :=
  mem_GammaH_iff.mpr ⟨Gamma0_mem.mpr hc,
    Subgroup.mem_bot.mpr (Units.ext (by simpa [gamma0Units, Gamma0Map] using hd))⟩

private def transSL (j : ℤ) : SL(2, ℤ) :=
  ⟨!![1, j; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

private def lastSL (σ : SL(2, ℤ)) (hσℓ : (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ℓ) : SL(2, ℤ) :=
  ⟨!![σ 0 0 * ℓ, σ 0 1; σ 1 0, 1], by
    rw [Matrix.det_fin_two_of]
    have h := Matrix.SpecialLinearGroup.det_coe σ
    rw [Matrix.det_fin_two] at h
    have h11 : (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ℓ := hσℓ
    rw [h11] at h
    linear_combination h⟩

private theorem transSL_mem (j : ℤ) : transSL j ∈ GammaH N ⊥ :=
  mem_GammaH_bot (by simp [transSL]) (by simp [transSL])

omit [NeZero ℓ] in
private theorem lastSL_mem {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 N)
    (hσℓ : (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ℓ) : lastSL σ hσℓ ∈ GammaH N ⊥ :=
  mem_GammaH_bot (by simpa [lastSL] using Gamma0_mem.mp hσ) (by simp [lastSL])

private def reps {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 N) (hσℓ : (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ℓ) :
    Option (Fin ℓ) → ↥(GammaH N ⊥)
  | none => ⟨lastSL σ hσℓ, lastSL_mem hσ hσℓ⟩
  | some j => ⟨transSL ((j : ℕ) : ℤ), transSL_mem _⟩

private theorem diagGL_mul_mapGL_transSL (j : ℕ) :
    diagGL ℓ * Matrix.SpecialLinearGroup.mapGL ℝ (transSL (j : ℤ)) = ModularForm.heckeMatrix ℓ j := by
  refine (Matrix.GeneralLinearGroup.ext_iff _ _).mpr fun i k => ?_
  rw [Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    ModularForm.val_heckeMatrix (NeZero.ne ℓ)]
  fin_cases i <;> fin_cases k <;>
    simp [diagGL, transSL, Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagGL_mul_mapGL_lastSL {σ : SL(2, ℤ)} (hσℓ : (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ℓ) :
    diagGL ℓ * Matrix.SpecialLinearGroup.mapGL ℝ (lastSL σ hσℓ) =
      Matrix.SpecialLinearGroup.mapGL ℝ σ * ModularForm.heckeDiagMatrix ℓ := by
  have h11 : ((((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ)) : ℝ) = (ℓ : ℝ) := by exact_mod_cast hσℓ
  refine (Matrix.GeneralLinearGroup.ext_iff _ _).mpr fun i k => ?_
  rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, ModularForm.val_heckeDiagMatrix (NeZero.ne ℓ)]
  fin_cases i <;> fin_cases k <;>
    simp [diagGL, lastSL, Matrix.mul_apply, Fin.sum_univ_two, h11]
  ring

private theorem slash_diagGL_mul_mapGL_mul {F : ℍ → ℂ}
    (hFΓ : ∀ γ : SL(2, ℤ), γ ∈ GammaH N ⊥ →
      F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = F)
    (k : ↥(GammaHUpper N ⊥ ℓ)) (g : GL (Fin 2) ℝ) :
    F ∣[(2 : ℤ)] (diagGL ℓ * Matrix.SpecialLinearGroup.mapGL ℝ ((k : ↥(GammaH N ⊥)) : SL(2, ℤ)) * g) =
      F ∣[(2 : ℤ)] (diagGL ℓ * g) := by
  have hconj : diagGL ℓ * Matrix.SpecialLinearGroup.mapGL ℝ ((k : ↥(GammaH N ⊥)) : SL(2, ℤ)) =
      Matrix.SpecialLinearGroup.mapGL ℝ ((conjL N ⊥ ℓ k : ↥(GammaH N ⊥)) : SL(2, ℤ)) * diagGL ℓ :=
    conjRel_diagGL_conjL k
  calc F ∣[(2 : ℤ)] (diagGL ℓ * Matrix.SpecialLinearGroup.mapGL ℝ ((k : ↥(GammaH N ⊥)) : SL(2, ℤ)) * g)
      = F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL N ⊥ ℓ k : ↥(GammaH N ⊥)) : SL(2, ℤ)) *
          diagGL ℓ * g) := by rw [hconj]
    _ = ((F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL N ⊥ ℓ k : ↥(GammaH N ⊥)) : SL(2, ℤ))))
          ∣[(2 : ℤ)] diagGL ℓ) ∣[(2 : ℤ)] g := by rw [SlashAction.slash_mul, SlashAction.slash_mul]
    _ = (F ∣[(2 : ℤ)] diagGL ℓ) ∣[(2 : ℤ)] g := by rw [hFΓ _ (conjL N ⊥ ℓ k).2]
    _ = F ∣[(2 : ℤ)] (diagGL ℓ * g) := by rw [SlashAction.slash_mul]

private theorem transSL_mul_apply_01 (j : ℤ) (A : SL(2, ℤ)) : (transSL j * A) 0 1 = A 0 1 + j * A 1 1 := by
  simp [transSL, Matrix.mul_apply, Fin.sum_univ_two]

omit [NeZero ℓ] in

private theorem lastSL_mul_apply_01 {σ : SL(2, ℤ)} (hσℓ : (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ℓ)
    (A : SL(2, ℤ)) : (lastSL σ hσℓ * A) 0 1 = σ 0 0 * ℓ * A 0 1 + σ 0 1 * A 1 1 := by
  simp [lastSL, Matrix.mul_apply, Fin.sum_univ_two]

omit [NeZero ℓ] in

private theorem transSL_mul_lastSL_inv_apply_01 (i : ℤ) {σ : SL(2, ℤ)}
    (hσℓ : (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ℓ) :
    (transSL i * (lastSL σ hσℓ)⁻¹) 0 1 = -σ 0 1 + i * (σ 0 0 * ℓ) := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp [transSL, lastSL, Matrix.mul_apply, Fin.sum_univ_two]

private theorem transSL_mul_transSL_inv_apply_01 (i j : ℤ) :
    (transSL i * (transSL j)⁻¹) 0 1 = i - j := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp [transSL, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private def cosetClass {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 N) (hσℓ : (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ℓ)
    (o : Option (Fin ℓ)) : ↥(GammaH N ⊥) ⧸ GammaHUpper N ⊥ ℓ :=
  (((reps hσ hσℓ o)⁻¹ : ↥(GammaH N ⊥)) : ↥(GammaH N ⊥) ⧸ GammaHUpper N ⊥ ℓ)

omit [NeZero ℓ] in

private theorem cast_apply_01_ne_zero (hℓ : ℓ.Prime) {σ : SL(2, ℤ)}
    (hσℓ : (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ℓ) : ((σ 0 1 : ℤ) : ZMod ℓ) ≠ 0 := by
  haveI : Fact (1 < ℓ) := ⟨hℓ.one_lt⟩
  intro h0
  have h := Matrix.SpecialLinearGroup.det_coe σ
  rw [Matrix.det_fin_two] at h
  have h11 : (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ℓ := hσℓ
  rw [h11] at h
  have hz := congrArg (fun z : ℤ => (z : ZMod ℓ)) h
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, zero_sub,
    Int.cast_one] at hz
  rw [show (((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod ℓ) = 0 from h0, zero_mul, neg_zero] at hz
  exact zero_ne_one hz

private theorem sum_slash_diagGL_eq (hℓ : ℓ.Prime) {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 N)
    (hσℓ : (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ℓ) {F : ℍ → ℂ}
    (hFΓ : ∀ γ : SL(2, ℤ), γ ∈ GammaH N ⊥ →
      F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = F)
    (T : (GammaHUpper N ⊥ ℓ).LeftTransversal) :
    letI := (GammaHUpper N ⊥ ℓ).fintypeQuotientOfFiniteIndex
    (∑ q : ↥(GammaH N ⊥) ⧸ GammaHUpper N ⊥ ℓ,
      F ∣[(2 : ℤ)] (diagGL ℓ * Matrix.SpecialLinearGroup.mapGL ℝ
        (((T.2.leftQuotientEquiv q : ↥(GammaH N ⊥)) : SL(2, ℤ)))⁻¹)) =
    ∑ j : Fin ℓ, F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ j +
      F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ σ * ModularForm.heckeDiagMatrix ℓ) := by
  letI := (GammaHUpper N ⊥ ℓ).fintypeQuotientOfFiniteIndex

  have hmemK : ∀ x : ↥(GammaH N ⊥), x ∈ GammaHUpper N ⊥ ℓ ↔ (((x : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ) = 0 :=
    fun x => by rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper]
  have hb0 := cast_apply_01_ne_zero hℓ hσℓ

  have hne : ∀ i : Fin ℓ, cosetClass hσ hσℓ (some i) ≠ cosetClass hσ hσℓ none := by
    intro i h
    have hmem := QuotientGroup.eq.mp h
    rw [inv_inv, hmemK, Subgroup.coe_mul, Subgroup.coe_inv] at hmem
    change ((((transSL ((i : ℕ) : ℤ) * (lastSL σ hσℓ)⁻¹) 0 1 : ℤ)) : ZMod ℓ) = 0 at hmem
    rw [transSL_mul_lastSL_inv_apply_01] at hmem
    simp only [Int.cast_add, Int.cast_neg, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
      add_zero, neg_eq_zero] at hmem
    exact hb0 hmem
  have hinj : Function.Injective (cosetClass hσ hσℓ) := by
    rintro (_ | i) (_ | j) h
    · rfl
    · exact absurd h.symm (hne j)
    · exact absurd h (hne i)
    · have hmem := QuotientGroup.eq.mp h
      rw [inv_inv, hmemK, Subgroup.coe_mul, Subgroup.coe_inv] at hmem
      change ((((transSL ((i : ℕ) : ℤ) * (transSL ((j : ℕ) : ℤ))⁻¹) 0 1 : ℤ)) : ZMod ℓ) = 0 at hmem
      rw [transSL_mul_transSL_inv_apply_01, Int.cast_sub, sub_eq_zero, Int.cast_natCast, Int.cast_natCast,
        ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at hmem
      exact congrArg some (Fin.ext hmem)
  have hsurj : Function.Surjective (cosetClass hσ hσℓ) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      by_cases hd : ((((x : ↥(GammaH N ⊥)) : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ) = 0
      · refine ⟨none, QuotientGroup.eq.mpr ?_⟩
        rw [inv_inv, hmemK, Subgroup.coe_mul]
        change ((((lastSL σ hσℓ * ((x : ↥(GammaH N ⊥)) : SL(2, ℤ))) 0 1 : ℤ)) : ZMod ℓ) = 0
        rw [lastSL_mul_apply_01]
        simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, hd, mul_zero, zero_mul,
          zero_add]
      ·
        have hval0 : (((((x : ↥(GammaH N ⊥)) : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ)).val ≠ 0 :=
          fun h0 => hd ((ZMod.val_eq_zero _).mp h0)
        have hg : Nat.gcd (((((x : ↥(GammaH N ⊥)) : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ)).val ℓ = 1 :=
          Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr
            (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hval0) (ZMod.val_lt _)))
        have hc : ((((x : ↥(GammaH N ⊥)) : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ)⁻¹ *
            ((((x : ↥(GammaH N ⊥)) : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ) = 1 := by
          rw [mul_comm, ZMod.mul_inv_eq_gcd, hg, Nat.cast_one]
        refine ⟨some ⟨(-((((x : ↥(GammaH N ⊥)) : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ) *
            ((((x : ↥(GammaH N ⊥)) : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ)⁻¹).val, ZMod.val_lt _⟩,
          QuotientGroup.eq.mpr ?_⟩
        rw [inv_inv, hmemK, Subgroup.coe_mul]
        change ((((transSL (((-((((x : ↥(GammaH N ⊥)) : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ) *
            ((((x : ↥(GammaH N ⊥)) : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ)⁻¹).val : ℕ) : ℤ) *
          ((x : ↥(GammaH N ⊥)) : SL(2, ℤ))) 0 1 : ℤ)) : ZMod ℓ) = 0
        rw [transSL_mul_apply_01]
        simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
        rw [mul_assoc, hc, mul_one, add_neg_cancel]

  have hval : ∀ o : Option (Fin ℓ),
      F ∣[(2 : ℤ)] (diagGL ℓ * Matrix.SpecialLinearGroup.mapGL ℝ
        (((T.2.leftQuotientEquiv (cosetClass hσ hσℓ o) : ↥(GammaH N ⊥)) : SL(2, ℤ)))⁻¹) =
      F ∣[(2 : ℤ)] (diagGL ℓ * Matrix.SpecialLinearGroup.mapGL ℝ ((reps hσ hσℓ o : ↥(GammaH N ⊥)) : SL(2, ℤ))) := by
    intro o
    have hq : (((T.2.leftQuotientEquiv (cosetClass hσ hσℓ o) : ↥(GammaH N ⊥))) :
        ↥(GammaH N ⊥) ⧸ GammaHUpper N ⊥ ℓ) =
        (((reps hσ hσℓ o)⁻¹ : ↥(GammaH N ⊥)) : ↥(GammaH N ⊥) ⧸ GammaHUpper N ⊥ ℓ) :=
      T.2.quotientGroupMk_leftQuotientEquiv (cosetClass hσ hσℓ o)
    have hk := QuotientGroup.eq.mp hq
    have hTinv : ((T.2.leftQuotientEquiv (cosetClass hσ hσℓ o) : ↥(GammaH N ⊥)))⁻¹ =
        (((T.2.leftQuotientEquiv (cosetClass hσ hσℓ o) : ↥(GammaH N ⊥)))⁻¹ *
            ((reps hσ hσℓ o)⁻¹ : ↥(GammaH N ⊥))) * reps hσ hσℓ o :=
      (inv_mul_cancel_right _ _).symm
    rw [← Subgroup.coe_inv, hTinv, Subgroup.coe_mul, map_mul, ← mul_assoc]
    exact slash_diagGL_mul_mapGL_mul hFΓ ⟨_, hk⟩ _
  rw [← Equiv.sum_comp (Equiv.ofBijective (cosetClass hσ hσℓ) ⟨hinj, hsurj⟩), Fintype.sum_option]
  simp only [Equiv.ofBijective_apply, hval, reps, diagGL_mul_mapGL_transSL, diagGL_mul_mapGL_lastSL hσℓ]
  exact add_comm _ _

end Cosets

section Deriv

open scoped ModularForm

variable {N : ℕ} {H : Subgroup (ZMod N)ˣ} {ℓ : ℕ} [NeZero ℓ]

private theorem det_diagGL_mul_mapGL_pos (s : SL(2, ℤ)) :
    0 < (diagGL ℓ * Matrix.SpecialLinearGroup.mapGL ℝ s).val.det := by
  rw [Units.val_mul, Matrix.det_mul]
  refine mul_pos ?_ (det_mapGL_pos s)
  simp [diagGL, Matrix.det_fin_two_of, Nat.pos_of_ne_zero (NeZero.ne ℓ)]

private theorem hasDerivAt_heckeTrace (T : (GammaHUpper N H ℓ).LeftTransversal) {F Fp : ℍ → ℂ}
    (hFpF : ∀ τ : ℍ, HasDerivAt (Fp ∘ ofComplex) (F τ) ↑τ) (τ : ℍ) :
    letI := (GammaHUpper N H ℓ).fintypeQuotientOfFiniteIndex
    HasDerivAt (heckeTrace T Fp ∘ ofComplex)
      ((∑ q : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ,
        F ∣[(2 : ℤ)] (diagGL ℓ * Matrix.SpecialLinearGroup.mapGL ℝ
          (((T.2.leftQuotientEquiv q : ↥(GammaH N H)) : SL(2, ℤ)))⁻¹)) τ) ↑τ := by
  letI := (GammaHUpper N H ℓ).fintypeQuotientOfFiniteIndex
  have hfun : (heckeTrace T Fp ∘ ofComplex) = fun z : ℂ => ∑ q : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ,
      Fp ((diagGL ℓ * Matrix.SpecialLinearGroup.mapGL ℝ
        (((T.2.leftQuotientEquiv q : ↥(GammaH N H)) : SL(2, ℤ)))⁻¹) • ofComplex z) := by
    funext z
    simp only [Function.comp_apply, heckeTrace, mul_smul]
    rfl
  rw [hfun, Finset.sum_apply]
  exact HasDerivAt.fun_sum fun q _ => hasDerivAt_comp_smul_of_det_pos hFpF _ (det_diagGL_mul_mapGL_pos _) τ

end Deriv

section HeckeLaw

open scoped ModularForm

private theorem heckeT_periodHom_eq {N : ℕ} [NeZero N] {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime)
    {σ : SL(2, ℤ)} (hσ : σ ∈ CongruenceSubgroup.Gamma0 N)
    (hσℓ : (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ℓ)
    {F Fp Gp : ℍ → ℂ}
    (hFΓ : ∀ γ : SL(2, ℤ), γ ∈ CohCarrier.GammaH N ⊥ →
      F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = F)
    (hFp : ModularCurve.Period.IsEquivariantPrimitive (CohCarrier.GammaH N ⊥) Fp)
    (hFpF : ∀ τ : ℍ, HasDerivAt (Fp ∘ UpperHalfPlane.ofComplex) (F τ) ↑τ)
    (hGp : ModularCurve.Period.IsEquivariantPrimitive (CohCarrier.GammaH N ⊥) Gp)
    (hGpF : ∀ τ : ℍ, HasDerivAt (Gp ∘ UpperHalfPlane.ofComplex)
      ((∑ j : Fin ℓ, F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ j +
        F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ σ * ModularForm.heckeDiagMatrix ℓ)) τ) ↑τ) :
    CohCarrier.heckeT N ⊥ ℓ ℂ hFp.periodHom = hGp.periodHom := by
  letI := (GammaHUpper N ⊥ ℓ).fintypeQuotientOfFiniteIndex
  rw [← periodHom_heckeTrace (default : (GammaHUpper N ⊥ ℓ).LeftTransversal) hFp]
  refine IsEquivariantPrimitive.periodHom_eq_of_hasDerivAt _ hGp (fun τ => ?_) hGpF
  rw [← sum_slash_diagGL_eq hℓ hσ hσℓ hFΓ default]
  exact hasDerivAt_heckeTrace default hFpF τ

end HeckeLaw

end TwistedPeriodDescent

namespace TwistedPeriodDescent

open UpperHalfPlane Filter Topology ModularCurve.Period CongruenceSubgroup
open scoped MatrixGroups ModularForm

section CuspTransport

private theorem map_castHom_mapGL (g : SL(2, ℤ)) :
    (Matrix.SpecialLinearGroup.mapGL ℚ g : GL (Fin 2) ℚ).map (Rat.castHom ℝ) =
      Matrix.SpecialLinearGroup.mapGL ℝ g := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix]

private theorem mapGL_smul_eq (g : SL(2, ℤ)) (z : ℍ) :
    (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) • z = g • z :=
  rfl

private theorem exists_tendsto_comp_smul_map {Gp : ℍ → ℂ}
    (hlim : ∀ δ : SL(2, ℤ), ∃ Lim : ℂ, Tendsto (fun w : ℍ => Gp (δ • w)) atImInfty (𝓝 Lim))
    (M : GL (Fin 2) ℚ) :
    ∃ Lim : ℂ, Tendsto (fun w : ℍ => Gp ((M.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) • w)) atImInfty (𝓝 Lim) := by
  obtain ⟨g, hg⟩ := (M • (OnePoint.infty : OnePoint ℚ)).exists_mem_SL2 ℤ
  set U : GL (Fin 2) ℚ := (Matrix.SpecialLinearGroup.mapGL ℚ g)⁻¹ * M with hU
  have hUinf : U • (OnePoint.infty : OnePoint ℚ) = OnePoint.infty := by
    rw [hU, mul_smul, ← hg, inv_smul_smul]
  have hU10 : U 1 0 = 0 := OnePoint.smul_infty_eq_self_iff.mp hUinf
  have hUR10 : (U.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) 1 0 = 0 := by
    rw [Matrix.GeneralLinearGroup.map_apply, hU10, map_zero]
  have hM : (M.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) =
      Matrix.SpecialLinearGroup.mapGL ℝ g * U.map (Rat.castHom ℝ) := by
    rw [← map_castHom_mapGL, ← map_mul, hU, mul_inv_cancel_left]
  obtain ⟨Lim, hLim⟩ := hlim g
  refine ⟨Lim, ?_⟩
  have h := hLim.comp (UpperHalfPlane.tendsto_smul_atImInfty hUR10)
  refine h.congr fun w => ?_
  simp only [Function.comp_apply]
  rw [hM, mul_smul, mapGL_smul_eq]

end CuspTransport

section Primitive

variable {M : ℕ} (g : CuspForm (Gamma0 M) 2)

private theorem exists_primitive_of_mem_slashSpanPos {Gfun : ℍ → ℂ}
    (hGg : ∀ τ : ℍ, HasDerivAt (Gfun ∘ ofComplex) (g τ) ↑τ)
    (hGlim : ∀ δ : SL(2, ℤ), ∃ Lim : ℂ, Tendsto (fun w : ℍ => Gfun (δ • w)) atImInfty (𝓝 Lim))
    {F : ℍ → ℂ} (hF : F ∈ slashSpanPos g) :
    ∃ Fp : ℍ → ℂ, (∀ τ : ℍ, HasDerivAt (Fp ∘ ofComplex) (F τ) ↑τ) ∧
      ∀ δ : SL(2, ℤ), ∃ Lim : ℂ, Tendsto (fun w : ℍ => Fp (δ • w)) atImInfty (𝓝 Lim) := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨⟨β, hβ⟩, rfl⟩ := hF
    set βR : GL (Fin 2) ℝ := (β : GL (Fin 2) ℚ).map (Rat.castHom ℝ) with hβR
    have hβRdet : 0 < βR.val.det := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hβR, Matrix.GeneralLinearGroup.map_det]
      simp only [Units.coe_map, MonoidHom.coe_coe, Rat.coe_castHom]
      exact_mod_cast hβ
    refine ⟨fun w => Gfun (βR • w), fun τ => hasDerivAt_comp_smul_ofComplex_of_det_pos hGg βR hβRdet τ,
      fun δ => ?_⟩
    obtain ⟨Lim, hLim⟩ := exists_tendsto_comp_smul_map hGlim (β * Matrix.SpecialLinearGroup.mapGL ℚ δ)
    refine ⟨Lim, hLim.congr fun w => ?_⟩
    simp only
    rw [map_mul, map_castHom_mapGL, mul_smul, mapGL_smul_eq]
  | zero =>
    refine ⟨0, fun τ => ?_, fun δ => ⟨0, ?_⟩⟩
    · simpa [Function.comp_def] using hasDerivAt_const (↑τ : ℂ) (0 : ℂ)
    · exact tendsto_const_nhds
  | add F₁ F₂ _ _ ih₁ ih₂ =>
    obtain ⟨Fp₁, h₁, l₁⟩ := ih₁
    obtain ⟨Fp₂, h₂, l₂⟩ := ih₂
    refine ⟨Fp₁ + Fp₂, fun τ => ?_, fun δ => ?_⟩
    · have := (h₁ τ).add (h₂ τ)
      first | exact this | simpa [Function.comp_def] using this | simpa +zetaDelta [Function.comp_def] using this
    · obtain ⟨L₁, hL₁⟩ := l₁ δ
      obtain ⟨L₂, hL₂⟩ := l₂ δ
      exact ⟨L₁ + L₂, by simpa using hL₁.add hL₂⟩
  | smul c F _ ih =>
    obtain ⟨Fp, h, l⟩ := ih
    refine ⟨c • Fp, fun τ => ?_, fun δ => ?_⟩
    · have := (h τ).const_smul c
      first | exact this | simpa [Function.comp_def] using this | simpa +zetaDelta [Function.comp_def] using this
    · obtain ⟨Lim, hLim⟩ := l δ
      exact ⟨c • Lim, by simpa using hLim.const_smul c⟩

end Primitive

section Equivariance

variable {Γ : Subgroup SL(2, ℤ)} {Fp F : ℍ → ℂ}

private theorem isEquivariantPrimitive_of_slash_eq
    (hFpF : ∀ τ : ℍ, HasDerivAt (Fp ∘ ofComplex) (F τ) ↑τ)
    (hinv : ∀ γ : SL(2, ℤ), γ ∈ Γ → F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = F) :
    IsEquivariantPrimitive Γ Fp := by
  intro γ
  have h1 : ∀ τ : ℍ, HasDerivAt
      (fun z : ℂ => Fp ((Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ) • ofComplex z))
      (F τ) ↑τ := by
    intro τ
    have := hasDerivAt_comp_smul_of_det_pos hFpF
      (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ))) (det_mapGL_pos _) τ
    rwa [hinv _ γ.2] at this
  obtain ⟨c, hc⟩ := sub_eq_const_of_forall_hasDerivAt h1 hFpF
  refine ⟨c, fun z => ?_⟩
  have := hc z
  simpa only [Function.comp_apply, ofComplex_apply, mapGL_smul_eq] using this

private theorem isEquivariantPrimitive_const_smul (hFp : IsEquivariantPrimitive Γ Fp) (c : ℂ) :
    IsEquivariantPrimitive Γ (c • Fp) := by
  intro γ
  refine ⟨c * hFp.period γ, fun z => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← mul_sub, hFp.sub_eq_period γ z]

private theorem periodHom_const_smul (hFp : IsEquivariantPrimitive Γ Fp) (c : ℂ) :
    (isEquivariantPrimitive_const_smul hFp c).periodHom = c • hFp.periodHom := by
  refine DFunLike.ext _ _ fun x => ?_
  obtain ⟨γ, rfl⟩ : ∃ γ : Γ, Additive.ofMul γ = x := ⟨Additive.toMul x, rfl⟩
  rw [(isEquivariantPrimitive_const_smul hFp c).periodHom_apply, AddMonoidHom.smul_apply, hFp.periodHom_apply,
    smul_eq_mul]
  have h1 := (isEquivariantPrimitive_const_smul hFp c).sub_eq_period γ UpperHalfPlane.I
  have h2 := hFp.sub_eq_period γ UpperHalfPlane.I
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  rw [← h1, ← h2, mul_sub]

private theorem diamondRaw_periodHom_eq_smul {N : ℕ} (hFp : IsEquivariantPrimitive (CohCarrier.GammaH N ⊥) Fp)
    (hFpF : ∀ τ : ℍ, HasDerivAt (Fp ∘ ofComplex) (F τ) ↑τ) (σ : Gamma0 N) (c : ℂ)
    (hσ : F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) = c • F) :
    CohCarrier.diamondRaw N ⊥ ℂ σ hFp.periodHom = c • hFp.periodHom := by

  have h1 : ∀ τ : ℍ, HasDerivAt
      (fun z : ℂ => Fp ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) • ofComplex z))
      ((c • F) τ) ↑τ := by
    intro τ
    have := hasDerivAt_comp_smul_of_det_pos hFpF
      (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ))) (det_mapGL_pos _) τ
    rwa [hσ] at this
  have h2 : ∀ τ : ℍ, HasDerivAt (fun z : ℂ => c * Fp (ofComplex z)) ((c • F) τ) ↑τ := by
    intro τ
    simpa [Function.comp_def] using (hFpF τ).const_mul c
  obtain ⟨d, hd⟩ := sub_eq_const_of_forall_hasDerivAt h1 h2
  have hd' : ∀ w : ℍ, Fp ((σ : SL(2, ℤ)) • w) - c * Fp w = d := fun w => by
    simpa only [ofComplex_apply, mapGL_smul_eq] using hd w
  refine DFunLike.ext _ _ fun x => ?_
  obtain ⟨γ, rfl⟩ : ∃ γ : ↥(CohCarrier.GammaH N ⊥), Additive.ofMul γ = x := ⟨Additive.toMul x, rfl⟩
  show hFp.periodHom (Additive.ofMul (CohCarrier.conjHom N ⊥ σ γ)) = c • hFp.periodHom (Additive.ofMul γ)
  rw [hFp.periodHom_apply, hFp.periodHom_apply, smul_eq_mul]
  have e1 := hFp.sub_eq_period (CohCarrier.conjHom N ⊥ σ γ) ((σ : SL(2, ℤ)) • UpperHalfPlane.I)
  have e2 := hFp.sub_eq_period γ UpperHalfPlane.I
  have e3 : ((CohCarrier.conjHom N ⊥ σ γ : ↥(CohCarrier.GammaH N ⊥)) : SL(2, ℤ)) •
      ((σ : SL(2, ℤ)) • UpperHalfPlane.I) = (σ : SL(2, ℤ)) • ((γ : SL(2, ℤ)) • UpperHalfPlane.I) := by
    rw [smul_smul, smul_smul]
    congr 1
    show (σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ * (σ : SL(2, ℤ)) = (σ : SL(2, ℤ)) * (γ : SL(2, ℤ))
    group
  rw [e3] at e1
  have d1 := hd' ((γ : SL(2, ℤ)) • UpperHalfPlane.I)
  have d2 := hd' UpperHalfPlane.I
  rw [← e1, ← e2]
  linear_combination d1 - d2

end Equivariance

section WeightZero

variable {Γ : Subgroup SL(2, ℤ)} {Fp : ℍ → ℂ}

private theorem invariant_of_forall_period_eq_zero
    (hF : IsEquivariantPrimitive Γ Fp) (hzero : ∀ γ : Γ, hF.period γ = 0)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (z : ℍ) : Fp (γ • z) = Fp z := by
  have h := hF.sub_eq_period ⟨γ, hγ⟩ z
  rw [hzero ⟨γ, hγ⟩] at h
  exact sub_eq_zero.mp h

private theorem periodHom_eq_zero_iff (hF : IsEquivariantPrimitive Γ Fp) :
    hF.periodHom = 0 ↔ ∀ γ : Γ, hF.period γ = 0 := by
  constructor
  · intro h γ
    have : hF.periodHom (Additive.ofMul γ) = (0 : Additive Γ →+ ℂ) (Additive.ofMul γ) := by
      rw [h]
    simpa [hF.periodHom_apply] using this
  · intro h
    refine DFunLike.ext _ _ fun γ => ?_
    show hF.period (Additive.toMul γ) = 0
    exact h _

private theorem slash_zero_apply (G : ℍ → ℂ) (δ : SL(2, ℤ)) (τ : ℍ) :
    (G ∣[(0 : ℤ)] δ) τ = G (δ • τ) := by
  rw [ModularForm.SL_slash_def]
  simp

variable (Γ) [Γ.FiniteIndex]

private noncomputable def weightZeroModularForm
    (hholo : ∀ τ : ℍ, DifferentiableAt ℂ (Fp ∘ ofComplex) ↑τ)
    (hinv : ∀ γ ∈ Γ, ∀ z : ℍ, Fp (γ • z) = Fp z)
    (hlim : ∀ δ : SL(2, ℤ), ∃ Lim : ℂ, Tendsto (fun w : ℍ => Fp (δ • w)) atImInfty (𝓝 Lim)) :
    ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0 where
  toFun := Fp
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    show Fp ∣[(0 : ℤ)] γ = Fp
    funext τ
    exact (slash_zero_apply Fp γ τ).trans (hinv γ hγ τ)
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    intro z hz
    exact (hholo ⟨z, hz⟩).differentiableWithinAt
  bdd_at_cusps' := by
    intro c hc
    have hle : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
      rintro g ⟨γ, -, rfl⟩
      exact ⟨γ, rfl⟩
    obtain ⟨δ, rfl⟩ := isCusp_SL2Z_iff'.mp (hc.mono hle)
    rw [OnePoint.isBoundedAt_iff (g := Matrix.SpecialLinearGroup.mapGL ℝ δ) rfl]
    obtain ⟨Lim, hLim⟩ := hlim δ
    have hslash : Fp ∣[(0 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ δ)
        = fun w : ℍ => Fp (δ • w) := by
      funext τ
      exact slash_zero_apply Fp δ τ
    rw [hslash]
    exact hLim.isBigO_one ℝ

private theorem exists_const_of_invariant_of_tendsto
    (hholo : ∀ τ : ℍ, DifferentiableAt ℂ (Fp ∘ ofComplex) ↑τ)
    (hinv : ∀ γ ∈ Γ, ∀ z : ℍ, Fp (γ • z) = Fp z)
    (hlim : ∀ δ : SL(2, ℤ), ∃ Lim : ℂ, Tendsto (fun w : ℍ => Fp (δ • w)) atImInfty (𝓝 Lim)) :
    ∃ c : ℂ, Fp = Function.const ℍ c := by
  obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero (weightZeroModularForm Γ hholo hinv hlim)
  exact ⟨c, hc⟩

variable {Γ}

private theorem periodHom_ne_zero_of_mem_slashSpanPos {F : ℍ → ℂ} (hFp : IsEquivariantPrimitive Γ Fp)
    (hFpF : ∀ τ : ℍ, HasDerivAt (Fp ∘ ofComplex) (F τ) ↑τ)
    (hlim : ∀ δ : SL(2, ℤ), ∃ Lim : ℂ, Tendsto (fun w : ℍ => Fp (δ • w)) atImInfty (𝓝 Lim))
    (hF0 : F ≠ 0) : hFp.periodHom ≠ 0 := by
  intro hzero
  apply hF0
  have hinv : ∀ γ ∈ Γ, ∀ z : ℍ, Fp (γ • z) = Fp z := fun γ hγ z =>
    invariant_of_forall_period_eq_zero hFp ((periodHom_eq_zero_iff hFp).mp hzero) hγ z
  have hholo : ∀ τ : ℍ, DifferentiableAt ℂ (Fp ∘ ofComplex) ↑τ := fun τ => (hFpF τ).differentiableAt
  obtain ⟨c, hc⟩ := exists_const_of_invariant_of_tendsto Γ hholo hinv hlim
  funext τ
  have h1 : HasDerivAt (Fp ∘ ofComplex) (F τ) ↑τ := hFpF τ
  have h2 : HasDerivAt (Fp ∘ ofComplex) 0 ↑τ := by
    have : Fp ∘ ofComplex = fun _ : ℂ => c := by
      funext z
      simp [hc]
    rw [this]
    exact hasDerivAt_const _ _
  exact h1.unique h2

end WeightZero

section Periods

private theorem Gamma_le_GammaH (N : ℕ) (H : Subgroup (ZMod N)ˣ) : Gamma N ≤ CohCarrier.GammaH N H := by
  intro A hA
  obtain ⟨h00, h01, h10, h11⟩ := Gamma_mem.mp hA
  have hA0 : A ∈ Gamma0 N := Gamma0_mem.mpr h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units N ⟨A, hA0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]
  exact one_mem H

private scoped instance GammaH_finiteIndex (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    (CohCarrier.GammaH N H).FiniteIndex :=
  IsCongruenceSubgroup.finiteIndex ⟨N, NeZero.ne N, Gamma_le_GammaH N H⟩

private theorem sigma_apply_of_det_pos {A : GL (Fin 2) ℝ} (hA : 0 < A.val.det) (c : ℂ) : UpperHalfPlane.σ A c = c := by
  have hdet : 0 < A.det.val := by rwa [Matrix.GeneralLinearGroup.val_det_apply]
  rw [UpperHalfPlane.σ, if_pos hdet]
  rfl

private theorem periods
    {L : ℕ} (g : CuspForm (CongruenceSubgroup.Gamma0 L) 2)
    {q : ℕ} [Fact q.Prime] (hq2 : L.factorization q = 2)
    (ξ : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (F : UpperHalfPlane → ℂ) (hFspan : F ∈ slashSpanPos g) (hF0 : F ≠ 0)
    (hdia : ∀ (σ : CongruenceSubgroup.Gamma0 (L / q)) (u : ℤ_[q]ˣ),
        ((u : ℤ_[q]) : ℚ_[q]) =
            ((((σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ_[q]) →
          F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (chiSq q ξ u)⁻¹ • F)
    (hone : ∀ γ : SL(2, ℤ), γ ∈ CohCarrier.GammaH (L / q) ⊥ →
        F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = F)
    (hCL : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ L → ∀ uℓ : ℤ_[q]ˣ, ((uℓ : ℤ_[q]) : ℚ_[q]) = (ℓ : ℚ_[q]) →
        ∑ j : Fin ℓ, F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ (j : ℕ) +
            (chiSq q ξ uℓ)⁻¹ • F ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix ℓ =
          ((ξ (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) *
              ModularFormClass.qCoeff g ℓ) • F) :
    ∃ φ : CohCarrier.H1 (L / q) ⊥ ℂ, φ ≠ 0 ∧
      φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH (L / q) ⊥) ℂ ∧
      (∀ (σ : CongruenceSubgroup.Gamma0 (L / q)) (u : ℤ_[q]ˣ),
        ((u : ℤ_[q]) : ℚ_[q]) =
            ((((σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ_[q]) →
          CohCarrier.diamondRaw (L / q) ⊥ ℂ σ φ = (chiSq q ξ u)⁻¹ • φ) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ L →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CohCarrier.heckeT (L / q) ⊥ ℓ ℂ φ =
          ((ξ (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) *
            ModularFormClass.qCoeff g ℓ) • φ := by
  classical
  have hqp : q.Prime := Fact.out
  have hL0 : L ≠ 0 := by
    rintro rfl
    simp at hq2
  haveI : NeZero L := ⟨hL0⟩
  have hqL : q ∣ L := Nat.dvd_of_factorization_pos (by rw [hq2]; norm_num)
  have hN0 : L / q ≠ 0 := by
    intro h
    rcases (Nat.div_eq_zero_iff).mp h with h | h
    · exact hqp.ne_zero h
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) hqL) (not_le.mpr h)
  haveI : NeZero (L / q) := ⟨hN0⟩

  obtain ⟨Gfun, hGg, -, -, hGlim⟩ := ModularCurve.Period.CuspForm.exists_equivariantPrimitive_gamma0 g
  obtain ⟨Fp, hFpF, hFplim⟩ := exists_primitive_of_mem_slashSpanPos g hGg hGlim hFspan
  have hFp : IsEquivariantPrimitive (CohCarrier.GammaH (L / q) ⊥) Fp :=
    isEquivariantPrimitive_of_slash_eq hFpF hone
  refine ⟨hFp.periodHom, periodHom_ne_zero_of_mem_slashSpanPos hFp hFpF hFplim hF0,
    mem_parabolicHoms_iff.mpr (hFp.isParabolicHom_periodHom hFplim), fun σ u hu => ?_, fun ℓ hℓ hℓL => ?_⟩
  · exact diamondRaw_periodHom_eq_smul hFp hFpF σ _ (hdia σ u hu)
  · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    haveI hℓf : Fact ℓ.Prime := ⟨hℓ⟩
    set c : ℂ := ((ξ (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) *
      ModularFormClass.qCoeff g ℓ) with hc

    have hℓq : ¬ q ∣ ℓ := fun h => hℓL (((Nat.prime_dvd_prime_iff_eq hqp hℓ).mp h) ▸ hqL)
    have hℓunit : IsUnit ((ℓ : ℕ) : ℤ_[q]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes hqp hℓ).mpr (fun h => hℓq (h ▸ dvd_rfl))
    set uℓ : ℤ_[q]ˣ := hℓunit.unit with huℓ
    have huℓval : ((uℓ : ℤ_[q]) : ℚ_[q]) = (ℓ : ℚ_[q]) := by
      rw [huℓ, IsUnit.unit_spec, PadicInt.coe_natCast]

    have hcop : Nat.Coprime ℓ (L / q) :=
      (Nat.Prime.coprime_iff_not_dvd hℓ).mpr (fun h => hℓL (h.trans (Nat.div_dvd_of_dvd hqL)))
    obtain ⟨σ, hσ0, hσ11⟩ : ∃ σ : SL(2, ℤ), σ ∈ Gamma0 (L / q) ∧ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ℓ := by
      have hg : (Nat.gcd ℓ (L / q) : ℤ) = 1 := by exact_mod_cast hcop
      refine ⟨⟨!![Nat.gcdA ℓ (L / q), -Nat.gcdB ℓ (L / q); ((L / q : ℕ) : ℤ), (ℓ : ℤ)], ?_⟩, ?_, ?_⟩
      · rw [Matrix.det_fin_two_of]
        have := Nat.gcd_eq_gcd_ab ℓ (L / q)
        rw [hg] at this
        linear_combination -this
      · rw [Gamma0_mem]
        show (((L / q : ℕ) : ℤ) : ZMod (L / q)) = 0
        rw [Int.cast_natCast, ZMod.natCast_self]
      · rfl

    have hσlaw : F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) = (chiSq q ξ uℓ)⁻¹ • F := by
      refine hdia ⟨σ, hσ0⟩ uℓ ?_
      rw [huℓval]
      change (ℓ : ℚ_[q]) = (((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ_[q])
      rw [hσ11]
      push_cast
      rfl

    have hdiagdet : 0 < (ModularForm.heckeDiagMatrix ℓ : GL (Fin 2) ℝ).val.det := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact ModularForm.det_heckeDiagMatrix_pos ℓ
    have hsum : ∑ j : Fin ℓ, F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ (j : ℕ) +
        F ∣[(2 : ℤ)] ((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ) =
          c • F := by
      rw [SlashAction.slash_mul, hσlaw, ModularForm.smul_slash, sigma_apply_of_det_pos hdiagdet, hc]
      exact hCL ℓ hℓ hℓL uℓ huℓval

    have hGp : IsEquivariantPrimitive (CohCarrier.GammaH (L / q) ⊥) (c • Fp) := isEquivariantPrimitive_const_smul hFp c
    have hGpF : ∀ τ : ℍ, HasDerivAt ((c • Fp) ∘ ofComplex)
        ((∑ j : Fin ℓ, F ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ (j : ℕ) +
          F ∣[(2 : ℤ)] ((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ)) τ) ↑τ := by
      intro τ
      rw [hsum]
      first | exact (hFpF τ).const_smul c | simpa [Function.comp_def] using (hFpF τ).const_smul c | simpa +zetaDelta [Function.comp_def] using (hFpF τ).const_smul c
    have key := heckeT_periodHom_eq hℓ hσ0 hσ11 hone hFp hFpF hGp hGpF
    rw [key, periodHom_const_smul hFp c]

end Periods

end TwistedPeriodDescent
p2m_reactivate "P2MW.S_CuspForm_IsNormalizedEigenform_exists_H1_diamondRaw_eq_smul_heckeT_eq_smul_of_mem_fixedSubmodule_fnTwist.TwistedPeriodDescent"

theorem solution
    {L : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 L) 2} (hg : g.IsNormalizedEigenform)
    (q : ℕ) [Fact q.Prime] (hq2 : L.factorization q = 2)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hηfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ η)
    (hηmod : HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel q))
    (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)))
    (hy0 : y ≠ 0)
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q 1)
      (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ, LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y =
      ((η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
          (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
            (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom
              (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) : ℂ) ^ 2) • y) :
    ∃ φ : CohCarrier.H1 (L / q) ⊥ ℂ, φ ≠ 0 ∧
      φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH (L / q) ⊥) ℂ ∧
      (∀ (σ : CongruenceSubgroup.Gamma0 (L / q)) (u : ℤ_[q]ˣ),
        ((u : ℤ_[q]) : ℚ_[q]) =
            ((((σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ_[q]) →
          CohCarrier.diamondRaw (L / q) ⊥ ℂ σ φ =
            ((η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
                (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
                  (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom
                    (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) : ℂ) ^ 2)⁻¹ • φ) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ L →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CohCarrier.heckeT (L / q) ⊥ ℓ ℂ φ =
          ((η (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) *
            ModularFormClass.qCoeff g ℓ) • φ := by
  obtain ⟨F, hFspan, hread, hF0, hdia, hone, hleft, hright⟩ :=
    TwistedPeriodDescent.readingCore hq2 Φ hΦg η hηfin hηmod y hy hy0 hfix hcent
  exact TwistedPeriodDescent.periods g hq2 η F hFspan hF0 hdia hone fun ℓ hℓ hℓL uℓ huℓ =>
    TwistedPeriodDescent.heckeLaw hg hq2 Φ hΦg η hηfin hηmod y hy F hFspan hread hleft hright hℓ hℓL uℓ huℓ

end S_CuspForm_IsNormalizedEigenform_exists_H1_diamondRaw_eq_smul_heckeT_eq_smul_of_mem_fixedSubmodule_fnTwist
end P2MW
export P2MW.S_CuspForm_IsNormalizedEigenform_exists_H1_diamondRaw_eq_smul_heckeT_eq_smul_of_mem_fixedSubmodule_fnTwist (solution)
