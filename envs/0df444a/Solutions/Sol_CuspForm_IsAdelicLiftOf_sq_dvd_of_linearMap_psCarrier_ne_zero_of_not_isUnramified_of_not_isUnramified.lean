-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOf.sq_dvd_of_linearMap_psCarrier_ne_zero_of_not_isUnramified_of_not_isUnramified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b5acea12-8f3d-507f-b995-1b6a86010052

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Theorems.Thm_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOf_sq_dvd_of_linearMap_psCarrier_ne_zero_of_not_isUnramified_of_not_isUnramified
p2m_attr_erase "instance" "FLT.SpectralSide.instCompactSpaceMatrix"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv"

set_option autoImplicit false

open LocalNewvector

namespace PrincipalSeriesLevelOne

section Plumbing

variable {R : Type*} [CommRing R]

private def lowerUnip (r : R) : GL (Fin 2) R :=
  ⟨!![1, 0; r, 1], !![1, 0; -r, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private def upperUnip (r : R) : GL (Fin 2) R :=
  ⟨!![1, r; 0, 1], !![1, -r; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private def diagUnit (w : Rˣ) : GL (Fin 2) R :=
  ⟨!![(w : R), 0; 0, 1], !![((w⁻¹ : Rˣ) : R), 0; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private def weyl : GL (Fin 2) R :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

end Plumbing

variable (p : ℕ) [Fact p.Prime]

private theorem exists_borelElem_eq (b : GL (Fin 2) ℚ_[p]) (hb : (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 = 0) :
    ∃ (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]), b = borelElem p a₁ a₂ x := by
  have hdet : (b : Matrix (Fin 2) (Fin 2) ℚ_[p]).det ≠ 0 := by
    intro h0
    simpa [h0] using (Matrix.isUnit_iff_isUnit_det _).mp b.isUnit
  rw [Matrix.det_fin_two, hb, mul_zero, sub_zero] at hdet
  refine ⟨Units.mk0 _ (left_ne_zero_of_mul hdet), Units.mk0 _ (right_ne_zero_of_mul hdet),
    (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1, ?_⟩
  apply Units.ext
  show (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [borelElem, hb]

private theorem lowerUnip_mem (z : ℤ_[p]) (hz : ‖z‖ < 1) :
    lowerUnip (algebraMap ℤ_[p] ℚ_[p] z) ∈ padicK1 p 1 := by
  rw [mem_congruenceK1_iff]
  refine ⟨lowerUnip z, ?_, ?_, ?_⟩
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerUnip, Matrix.GeneralLinearGroup.map]
  · simpa [lowerUnip, Ideal.mem_span_singleton] using (PadicInt.norm_lt_one_iff_dvd z).mp hz
  · simp [lowerUnip]

private theorem upperUnip_mem (z : ℤ_[p]) : upperUnip (algebraMap ℤ_[p] ℚ_[p] z) ∈ padicK1 p 1 := by
  rw [mem_congruenceK1_iff]
  refine ⟨upperUnip z, ?_, ?_, ?_⟩
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperUnip, Matrix.GeneralLinearGroup.map]
  · simp [upperUnip]
  · simp [upperUnip]

private theorem borelElem_unit_mem (u : ℚ_[p]ˣ) (hu : ‖(u : ℚ_[p])‖ = 1) : borelElem p u 1 0 ∈ padicK1 p 1 := by
  rw [mem_congruenceK1_iff]
  refine ⟨diagUnit (PadicInt.mkUnits hu), ?_, ?_, ?_⟩
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagUnit, borelElem, Matrix.GeneralLinearGroup.map]
  · simp [diagUnit]
  · simp [diagUnit]

private theorem weyl_mul_borelElem (u : ℚ_[p]ˣ) : (weyl : GL (Fin 2) ℚ_[p]) * borelElem p u 1 0 = borelElem p 1 u 0 * weyl := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weyl, borelElem, Matrix.mul_apply, Fin.sum_univ_two]

private theorem exists_borelElem_mul_mem (g : GL (Fin 2) ℚ_[p]) :
    ∃ (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (k : GL (Fin 2) ℚ_[p]), k ∈ padicK1 p 1 ∧
      (g = borelElem p a₁ a₂ x * k ∨ g = borelElem p a₁ a₂ x * weyl * k) := by
  set c : ℚ_[p] := (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 with hc_def
  set d : ℚ_[p] := (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 with hd_def
  by_cases hcd : ‖c‖ < ‖d‖
  ·
    have hd : d ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hcd
      exact absurd hcd (not_lt.mpr (norm_nonneg c))
    have hdpos : 0 < ‖d‖ := lt_of_le_of_lt (norm_nonneg c) hcd
    have hlt : ‖c / d‖ < 1 := by
      rw [norm_div]
      exact (div_lt_one hdpos).mpr hcd
    set z : ℤ_[p] := ⟨c / d, hlt.le⟩
    have hzlt : ‖z‖ < 1 := hlt
    have hzq' : algebraMap ℤ_[p] ℚ_[p] z = c / d := rfl
    have hkey : d * (c / d) = c := mul_div_cancel₀ c hd
    set k : GL (Fin 2) ℚ_[p] := lowerUnip (algebraMap ℤ_[p] ℚ_[p] z) with hk_def
    have hk : k ∈ padicK1 p 1 := lowerUnip_mem p z hzlt
    have hb : ((g * k⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 = 0 := by
      simp [hk_def, lowerUnip, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hzq', ← hc_def, ← hd_def, hkey]
    obtain ⟨a₁, a₂, x, hbx⟩ := exists_borelElem_eq p (g * k⁻¹) hb
    refine ⟨a₁, a₂, x, k, hk, Or.inl ?_⟩
    rw [← hbx, inv_mul_cancel_right]
  ·
    have hdc : ‖d‖ ≤ ‖c‖ := not_lt.mp hcd
    have hc : c ≠ 0 := by
      intro h0
      have hd0 : d = 0 := by
        rw [h0, norm_zero] at hdc
        exact norm_le_zero_iff.mp hdc
      have hdet : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]).det ≠ 0 := by
        intro hd'
        simpa [hd'] using (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
      apply hdet
      simp [Matrix.det_fin_two, ← hc_def, ← hd_def, h0, hd0]
    have hz : ‖d / c‖ ≤ 1 := by
      rw [norm_div]
      exact div_le_one_of_le₀ hdc (norm_nonneg c)
    set z : ℤ_[p] := ⟨d / c, hz⟩
    have hzq' : algebraMap ℤ_[p] ℚ_[p] z = d / c := rfl
    have hkey : c * (d / c) = d := mul_div_cancel₀ d hc
    set k : GL (Fin 2) ℚ_[p] := upperUnip (algebraMap ℤ_[p] ℚ_[p] z) with hk_def
    have hk : k ∈ padicK1 p 1 := upperUnip_mem p z
    have hb : ((g * (weyl * k)⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 = 0 := by
      rw [mul_inv_rev]
      simp [hk_def, upperUnip, weyl, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hzq', ← hc_def, ← hd_def,
        hkey]
    obtain ⟨a₁, a₂, x, hbx⟩ := exists_borelElem_eq p (g * (weyl * k)⁻¹) hb
    refine ⟨a₁, a₂, x, k, hk, Or.inr ?_⟩
    rw [mul_assoc, ← hbx, inv_mul_cancel_right]

private theorem exists_unit_of_not_isUnramified {μ : ℚ_[p]ˣ →* ℂˣ} (h : ¬ IsUnramified p μ) :
    ∃ u : ℚ_[p]ˣ, ‖(u : ℚ_[p])‖ = 1 ∧ (μ u : ℂ) ≠ 1 := by
  by_contra hcon
  apply h
  intro u hu
  by_contra hne
  exact hcon ⟨u, hu, fun h1 => hne (Units.val_eq_one.mp h1)⟩

private theorem eq_zero_of_eq_mul_self {a w : ℂ} (ha : a ≠ 1) (h : w = a * w) : w = 0 := by
  have h' : (1 - a) * w = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (Ne.symm ha))

section Vanishing

variable {p} {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {w : GL (Fin 2) ℚ_[p] → ℂ}

private theorem apply_one_eq_zero (hw : w ∈ principalSeries p μ₁ μ₂)
    (hfix : ∀ k ∈ padicK1 p 1, ∀ y : GL (Fin 2) ℚ_[p], w (y * k) = w y) (h₁ : ¬ IsUnramified p μ₁) : w 1 = 0 := by
  obtain ⟨u, hu, hne⟩ := exists_unit_of_not_isUnramified p h₁
  have h := apply_borelElem_mul_of_mem_principalSeries p hw u 1 0 1
  rw [mul_one, ← one_mul (borelElem p u 1 0), hfix _ (borelElem_unit_mem p u hu) 1, map_one, Units.val_one, mul_one,
    halfModulus_eq_one_of_norm_eq_one p hu (by simp), mul_one] at h
  exact eq_zero_of_eq_mul_self hne h

private theorem apply_weyl_eq_zero (hw : w ∈ principalSeries p μ₁ μ₂)
    (hfix : ∀ k ∈ padicK1 p 1, ∀ y : GL (Fin 2) ℚ_[p], w (y * k) = w y) (h₂ : ¬ IsUnramified p μ₂) : w weyl = 0 := by
  obtain ⟨u, hu, hne⟩ := exists_unit_of_not_isUnramified p h₂
  have h := apply_borelElem_mul_of_mem_principalSeries p hw 1 u 0 weyl
  rw [← weyl_mul_borelElem, hfix _ (borelElem_unit_mem p u hu) weyl, map_one, Units.val_one, one_mul,
    halfModulus_eq_one_of_norm_eq_one p (by simp) hu, mul_one] at h
  exact eq_zero_of_eq_mul_self hne h

private theorem eq_zero_of_fixed (hw : w ∈ principalSeries p μ₁ μ₂)
    (hfix : ∀ k ∈ padicK1 p 1, ∀ y : GL (Fin 2) ℚ_[p], w (y * k) = w y)
    (h₁ : ¬ IsUnramified p μ₁) (h₂ : ¬ IsUnramified p μ₂) (g : GL (Fin 2) ℚ_[p]) : w g = 0 := by
  obtain ⟨a₁, a₂, x, k, hk, hg | hg⟩ := exists_borelElem_mul_mem p g
  · rw [hg, hfix k hk, ← mul_one (borelElem p a₁ a₂ x), apply_borelElem_mul_of_mem_principalSeries p hw,
      apply_one_eq_zero hw hfix h₁, mul_zero]
  · rw [hg, hfix k hk, apply_borelElem_mul_of_mem_principalSeries p hw, apply_weyl_eq_zero hw hfix h₂, mul_zero]

end Vanishing

private theorem fixedSubmodule_padicK1_one_eq_bot {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    (h₁ : ¬ IsUnramified p μ₁) (h₂ : ¬ IsUnramified p μ₂) :
    fixedSubmodule (padicK1 p 1) (PSCarrier p μ₁ μ₂) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [mem_fixedSubmodule_iff] at hv
  have hsm : ∀ (k : GL (Fin 2) ℚ_[p]) (y : GL (Fin 2) ℚ_[p]),
      PSCarrier.toFn p μ₁ μ₂ (k • v) y = PSCarrier.toFn p μ₁ μ₂ v (y * k) := fun _ _ => rfl
  have hfix : ∀ k ∈ padicK1 p 1, ∀ y : GL (Fin 2) ℚ_[p],
      PSCarrier.toFn p μ₁ μ₂ v (y * k) = PSCarrier.toFn p μ₁ μ₂ v y := by
    intro k hk y
    rw [← hsm k y, hv k hk]
  apply PSCarrier.ext p μ₁ μ₂
  intro y
  exact eq_zero_of_fixed (PSCarrier.toFn_mem p μ₁ μ₂ v) hfix h₁ h₂ y

end PrincipalSeriesLevelOne

set_option autoImplicit false

open LocalNewvector NumberField AdelicDock

namespace AdelicSpanFixedVector

private theorem adelic_ext {x y : GL (Fin 2) (AdeleRing (RingOfIntegers ℚ) ℚ)}
    (harch : AdelicLevel.glArch (RingOfIntegers ℚ) ℚ x = AdelicLevel.glArch (RingOfIntegers ℚ) ℚ y)
    (hfin : ∀ w : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers ℚ),
      AdelicLevel.finComponent (RingOfIntegers ℚ) ℚ w (AdelicLevel.glFin (RingOfIntegers ℚ) ℚ x) =
        AdelicLevel.finComponent (RingOfIntegers ℚ) ℚ w (AdelicLevel.glFin (RingOfIntegers ℚ) ℚ y)) :
    x = y := by
  apply Units.ext
  apply matrix_eq_of_mapMatrix_arch_fin_eq (RingOfIntegers ℚ) ℚ
  · exact congrArg Units.val harch
  · apply matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (RingOfIntegers ℚ) ℚ
    intro w
    exact congrArg Units.val (hfin w)

variable (q : ℕ) [Fact q.Prime]

private noncomputable def qPart (h : GL (Fin 2) (AdeleRing (RingOfIntegers ℚ) ℚ)) : GL (Fin 2) ℚ_[q] :=
  Matrix.GeneralLinearGroup.map (padicRingEquiv q).symm.toRingHom
    (AdelicLevel.finComponent (RingOfIntegers ℚ) ℚ (padicPlace q) (AdelicLevel.glFin (RingOfIntegers ℚ) ℚ h))

private theorem padicGL_qPart (h : GL (Fin 2) (AdeleRing (RingOfIntegers ℚ) ℚ)) :
    padicGL q (qPart q h) =
      AdelicLevel.finComponent (RingOfIntegers ℚ) ℚ (padicPlace q) (AdelicLevel.glFin (RingOfIntegers ℚ) ℚ h) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp [qPart, padicGL_apply, Matrix.GeneralLinearGroup.map_apply]

private noncomputable def stripped (h : GL (Fin 2) (AdeleRing (RingOfIntegers ℚ) ℚ)) : GL (Fin 2) (AdeleRing (RingOfIntegers ℚ) ℚ) :=
  h * (padicToAdelic q (qPart q h))⁻¹

private theorem finComponent_stripped (h : GL (Fin 2) (AdeleRing (RingOfIntegers ℚ) ℚ)) :
    AdelicLevel.finComponent (RingOfIntegers ℚ) ℚ (padicPlace q)
      (AdelicLevel.glFin (RingOfIntegers ℚ) ℚ (stripped q h)) = 1 := by
  simp only [stripped, map_mul, map_inv, glFin_padicToAdelic, finComponent_padicToFinAdelic_self, padicGL_qPart,
    mul_inv_cancel]

private theorem padicToAdelic_mul_stripped (h : GL (Fin 2) (AdeleRing (RingOfIntegers ℚ) ℚ)) (k : GL (Fin 2) ℚ_[q]) :
    padicToAdelic q k * stripped q h = stripped q h * padicToAdelic q k := by
  apply adelic_ext
  · simp only [map_mul, glArch_padicToAdelic, one_mul, mul_one]
  · intro w
    by_cases hw : w = padicPlace q
    · subst hw
      simp only [map_mul, glFin_padicToAdelic, finComponent_padicToFinAdelic_self, finComponent_stripped, mul_one,
        one_mul]
    · simp only [map_mul, glFin_padicToAdelic, finComponent_padicToFinAdelic_of_ne q k hw, mul_one, one_mul]

private theorem padicToAdelic_mul_stripped_self (h : GL (Fin 2) (AdeleRing (RingOfIntegers ℚ) ℚ)) :
    padicToAdelic q (qPart q h) * stripped q h = h := by
  rw [padicToAdelic_mul_stripped, stripped, inv_mul_cancel_right]

private theorem padicToAdelic_smul_self {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {Φ : AutomorphicForm.AdelicGL2 (RingOfIntegers ℚ) ℚ → ℂ} (hlift : g.IsAdelicLiftOf Φ)
    {k : GL (Fin 2) ℚ_[q]} (hk : k ∈ padicK1 q (M.factorization q)) :
    (padicToAdelic q k : AutomorphicForm.AdelicGL2 (RingOfIntegers ℚ) ℚ) • AdelicSpan.self Φ = AdelicSpan.self Φ := by
  have hmem : padicToFinAdelic q k ∈ AdelicLevel.finiteLevelOne (RingOfIntegers ℚ) ℚ (ratLevel M) := by
    have h1 := padicToAdelic_mem_levelOne q (NeZero.ne M) le_rfl hk
    rwa [AdelicLevel.mem_levelOne_iff, glFin_padicToAdelic] at h1
  apply AdelicSpan.ext Φ
  rw [AdelicSpan.toFn_smul, AdelicSpan.toFn_self]
  apply AdelicFnCarrier.ext
  intro x
  rw [AdelicFnCarrier.toFn_smul, AdelicFnCarrier.toFn_mk, padicToAdelic_apply]
  exact hlift.level_inv _ hmem x

private theorem eq_zero_of_forall_smul_self {Φ : AutomorphicForm.AdelicGL2 (RingOfIntegers ℚ) ℚ → ℂ}
    {V : Type*} [AddCommGroup V] [Module ℂ V] (f : AdelicSpan Φ →ₗ[ℂ] V)
    (hf : ∀ h : AutomorphicForm.AdelicGL2 (RingOfIntegers ℚ) ℚ, f (h • AdelicSpan.self Φ) = 0) : f = 0 := by
  have e_mem : ∀ (h : AutomorphicForm.AdelicGL2 (RingOfIntegers ℚ) ℚ)
      (hm : h • AdelicFnCarrier.mk Φ ∈ AdelicSpanSubmodule Φ),
      AdelicSpan.mk Φ (h • AdelicFnCarrier.mk Φ) hm = h • AdelicSpan.self Φ := fun _ _ => AdelicSpan.ext Φ rfl
  have e_zero : ∀ hm : (0 : AdelicFnCarrier ℚ) ∈ AdelicSpanSubmodule Φ, AdelicSpan.mk Φ 0 hm = 0 :=
    fun _ => AdelicSpan.ext Φ rfl
  have e_add : ∀ (x y : AdelicFnCarrier ℚ) (hx : x ∈ AdelicSpanSubmodule Φ) (hy : y ∈ AdelicSpanSubmodule Φ)
      (hxy : x + y ∈ AdelicSpanSubmodule Φ),
      AdelicSpan.mk Φ (x + y) hxy = AdelicSpan.mk Φ x hx + AdelicSpan.mk Φ y hy := fun _ _ _ _ _ => AdelicSpan.ext Φ rfl
  have e_smul : ∀ (c : ℂ) (x : AdelicFnCarrier ℚ) (hx : x ∈ AdelicSpanSubmodule Φ) (hcx : c • x ∈ AdelicSpanSubmodule Φ),
      AdelicSpan.mk Φ (c • x) hcx = c • AdelicSpan.mk Φ x hx := fun _ _ _ _ => AdelicSpan.ext Φ rfl
  have key : ∀ (v : AdelicFnCarrier ℚ)
      (hv : v ∈ Submodule.span ℂ {ψ : AdelicFnCarrier ℚ |
        ∃ h : AutomorphicForm.AdelicGL2 (RingOfIntegers ℚ) ℚ, ψ = h • AdelicFnCarrier.mk Φ}),
      f (AdelicSpan.mk Φ v hv) = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [e_mem, hf]
    | zero => rw [e_zero, map_zero]
    | add x y hx hy ihx ihy => rw [e_add x y hx hy, map_add, ihx, ihy, add_zero]
    | smul c x hx ih => rw [e_smul c x hx, map_smul, ih, smul_zero]
  apply LinearMap.ext
  intro ψ
  obtain ⟨v, hv⟩ := ψ
  exact key v hv

private theorem exists_mem_fixedSubmodule_map_ne_zero {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (Φ : AutomorphicForm.AdelicGL2 (RingOfIntegers ℚ) ℚ → ℂ) (hlift : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (f : AdelicSpan Φ →ₗ[ℂ] PSCarrier q μ₁ μ₂)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : AdelicSpan Φ), f (x • v) = x • f v) (hf0 : f ≠ 0) :
    ∃ ψ : AdelicSpan Φ, ψ ∈ fixedSubmodule (padicK1 q (M.factorization q)) (AdelicSpan Φ) ∧ f ψ ≠ 0 := by
  have hgen : ∃ h : AutomorphicForm.AdelicGL2 (RingOfIntegers ℚ) ℚ, f (h • AdelicSpan.self Φ) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    exact hf0 (eq_zero_of_forall_smul_self f hcon)
  obtain ⟨h, hh⟩ := hgen
  refine ⟨stripped q h • AdelicSpan.self Φ, ?_, ?_⟩
  · rw [mem_fixedSubmodule_iff]
    intro k hk
    rw [AdelicSpan.padic_smul_def, ← mul_smul, padicToAdelic_mul_stripped, mul_smul, padicToAdelic_smul_self q hlift hk]
  · intro h0
    apply hh
    rw [← padicToAdelic_mul_stripped_self q h, mul_smul, ← AdelicSpan.padic_smul_def, hf, h0, smul_zero]

end AdelicSpanFixedVector

theorem solution
    {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (_hlift : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (_hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v) (_hf0 : f ≠ 0)
    (_hμ₁ : ¬ LocalNewvector.IsUnramified q μ₁) (_hμ₂ : ¬ LocalNewvector.IsUnramified q μ₂) :
    q ^ 2 ∣ M := by
  obtain ⟨ψ, hψ, hfψ⟩ := AdelicSpanFixedVector.exists_mem_fixedSubmodule_map_ne_zero q g Φ _hlift μ₁ μ₂ f _hf _hf0
  have hw : f ψ ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q (M.factorization q))
      (LocalNewvector.PSCarrier q μ₁ μ₂) := by
    rw [LocalNewvector.mem_fixedSubmodule_iff] at hψ ⊢
    intro k hk
    rw [← _hf k ψ, hψ k hk]
  have hq : q.Prime := Fact.out
  rw [hq.pow_dvd_iff_le_factorization (NeZero.ne M)]
  by_contra hlt
  have hle : M.factorization q ≤ 1 := Nat.lt_succ_iff.mp (Nat.lt_of_not_le hlt)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · rw [h0, LocalNewvector.PSCarrier.fixedSubmodule_padicK1_zero_eq_bot q (Or.inl _hμ₁), Submodule.mem_bot] at hw
    exact hfψ hw
  · rw [h1, PrincipalSeriesLevelOne.fixedSubmodule_padicK1_one_eq_bot q _hμ₁ _hμ₂, Submodule.mem_bot] at hw
    exact hfψ hw

#print axioms solution

end S_CuspForm_IsAdelicLiftOf_sq_dvd_of_linearMap_psCarrier_ne_zero_of_not_isUnramified_of_not_isUnramified
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOf_sq_dvd_of_linearMap_psCarrier_ne_zero_of_not_isUnramified_of_not_isUnramified (solution)
