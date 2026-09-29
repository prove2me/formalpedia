-- Prove2me | solution 1 for CuspForm.IsNormalizedEigenform.exists_isNormalizedEigenform_qCoeff_eq_mul_of_adelicLift_fnTwist_of_mem_span_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/f1503b6a-3108-5e95-8d5a-2ee8d06b7e72

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_LocalNewvector_ConductorDatum
import Theorems.Thm_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Theorems.Thm_CuspForm_exists_eq_sum_smul_slash_of_forall_slash_eq
import Theorems.Thm_CuspForm_IsAdelicLiftOf_levelZero_inv
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_qCoeff_eq_mul_of_adelicLift_fnTwist_of_mem_span_of_fixed

set_option autoImplicit false

open NumberField AdelicDock IsDedekindDomain

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
      have h__ := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) hmem
      try simp at h__
      try simp
      exact h__
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

private noncomputable def slashSpan (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) : Submodule ℂ (UpperHalfPlane → ℂ) :=
  Submodule.span ℂ (Set.range fun β : GL (Fin 2) ℚ => (⇑g) ∣[(2 : ℤ)] β.map (Rat.castHom ℝ))

private theorem slash_map_mem_slashSpan (β : GL (Fin 2) ℚ) : (⇑g) ∣[(2 : ℤ)] β.map (Rat.castHom ℝ) ∈ slashSpan g :=
  Submodule.subset_span ⟨β, rfl⟩

private theorem coe_mem_slashSpan : (⇑g : UpperHalfPlane → ℂ) ∈ slashSpan g := by
  simpa [SlashAction.slash_one] using slash_map_mem_slashSpan (g := g) 1

private def HasReading (y : AdelicSpan φ) (F : UpperHalfPlane → ℂ) : Prop :=
  ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 → LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
    (AdelicSpan.toFn φ y).toFn h = (F ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I

private theorem hasReading_zero : HasReading (0 : AdelicSpan φ) (0 : UpperHalfPlane → ℂ) := by
  intro h _ _
  rw [SlashAction.zero_slash]
  rfl

private theorem HasReading.add {y₁ y₂ : AdelicSpan φ} {F₁ F₂ : UpperHalfPlane → ℂ} (h₁ : HasReading y₁ F₁)
    (h₂ : HasReading y₂ F₂) : HasReading (y₁ + y₂) (F₁ + F₂) := by
  intro h hh hpos
  rw [SlashAction.add_slash, Pi.add_apply, ← h₁ h hh hpos, ← h₂ h hh hpos]
  rfl

private theorem HasReading.smul {y : AdelicSpan φ} {F : UpperHalfPlane → ℂ} (hy : HasReading y F) (c : ℂ) :
    HasReading (c • y) (c • F) := by
  intro h hh hpos
  rw [ModularForm.smul_slash, Pi.smul_apply, σ_apply_of_det_pos ((Matrix.mem_glpos _).mp hpos), smul_eq_mul,
    ← hy h hh hpos]
  rfl

private theorem glFin_conj_eq_one (δ : GL (Fin 2) ℚ) {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : glFin (𝓞 ℚ) ℚ h = 1) :
    glFin (𝓞 ℚ) ℚ ((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) = 1 := by
  rw [map_mul, map_mul, hh, mul_one, map_inv, inv_mul_cancel]

private theorem exists_hasReading_padic_smul_self (hM : M ≠ 0) (hφg : g.IsAdelicLiftOf φ) {q : ℕ} [Fact q.Prime]
    (x : GL (Fin 2) ℚ_[q]) :
    ∃ F ∈ slashSpan g, HasReading (x • AdelicSpan.self φ) F := by
  obtain ⟨δ, a, u, ha, hapos, hu, hdec⟩ :=
    exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hM (padicToAdelic q x)

  have harch : LanglandsTunnell.ratArchGL2 a = (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) δ)⁻¹ := by
    have h0 : LanglandsTunnell.ratArchGL2 (padicToAdelic q x) = 1 := by
      rw [padicToAdelic_apply]; exact ratArch_finEmbed _
    rw [hdec, ratArch_mul, ratArch_mul, ratArch_finEmbed, mul_one, ratArch_globalPoints] at h0
    exact eq_inv_of_mul_eq_one_right h0
  refine ⟨(⇑g) ∣[(2 : ℤ)] δ⁻¹.map (Rat.castHom ℝ), slash_map_mem_slashSpan δ⁻¹, ?_⟩
  intro h hh hpos
  have hval : (AdelicSpan.toFn φ (x • AdelicSpan.self φ)).toFn h = φ (h * padicToAdelic q x) := by
    rw [AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul, AdelicSpan.toFn_self,
      AdelicFnCarrier.toFn_mk]
  rw [hval, hdec, ← mul_assoc, ← mul_assoc, hφg.level_inv u hu]
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
  rw [hre, hφg.left_inv, hφg.apply_eq _ hh' hpos', hratarch, SlashAction.slash_mul, map_inv]

private theorem exists_hasReading_of_mem_span (hM : M ≠ 0) (hφg : g.IsAdelicLiftOf φ) {q : ℕ} [Fact q.Prime]
    {y : AdelicSpan φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ)) :
    ∃ F ∈ slashSpan g, HasReading y F := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    exact exists_hasReading_padic_smul_self hM hφg x
  | zero => exact ⟨0, Submodule.zero_mem _, hasReading_zero⟩
  | add y₁ y₂ _ _ ih₁ ih₂ =>
    obtain ⟨F₁, hF₁, h₁⟩ := ih₁
    obtain ⟨F₂, hF₂, h₂⟩ := ih₂
    exact ⟨F₁ + F₂, Submodule.add_mem _ hF₁ hF₂, h₁.add h₂⟩
  | smul c y _ ih =>
    obtain ⟨F, hF, h⟩ := ih
    exact ⟨c • F, Submodule.smul_mem _ c hF, h.smul c⟩

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
  convert h3 using 1
  all_goals try rfl

private theorem continuous_of_mem_slashSpan {F : UpperHalfPlane → ℂ} (hF : F ∈ slashSpan g) : Continuous F := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨β, rfl⟩ := hF
    exact continuous_slash (CuspFormClass.holo g).continuous 2 _
  | zero => exact continuous_const
  | add F₁ F₂ _ _ h₁ h₂ => exact h₁.add h₂
  | smul c F _ h => exact h.const_smul c

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

private abbrev fn (y : AdelicSpan φ) : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := (AdelicSpan.toFn φ y).toFn

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

private theorem fn_globalPoints_mul_of_mem_span (hφg : g.IsAdelicLiftOf φ) {q : ℕ} [Fact q.Prime] {y : AdelicSpan φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ))
    (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    rw [fn_padic_smul_self, fn_padic_smul_self, mul_assoc, hφg.left_inv]
  | zero => rfl
  | add y₁ y₂ _ _ ih₁ ih₂ => rw [fn_add, fn_add, ih₁, ih₂]
  | smul c y _ ih => rw [fn_csmul, fn_csmul, ih]

private theorem fn_mul_finEmbed_of_mem_span_of_qtrivial {q : ℕ} [Fact q.Prime]
    (hK₀ : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M), ∀ x, φ (x * finEmbed (𝓞 ℚ) ℚ u) = φ x)
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
      map_mul, ← mul_assoc, hK₀ w hw]
  | zero => rfl
  | add y₁ y₂ _ _ ih₁ ih₂ => rw [fn_add, fn_add, ih₁, ih₂]
  | smul c y _ ih => rw [fn_csmul, fn_csmul, ih]

private theorem level_lowered_dvd (M q a : ℕ) : M / q ^ (M.factorization q - a) ∣ M :=
  Nat.div_dvd_of_dvd ((Nat.pow_dvd_pow q (Nat.sub_le _ _)).trans (Nat.ordProj_dvd M q))

private theorem level_lowered_ne_zero {M : ℕ} (hM : M ≠ 0) (q a : ℕ) (hq : q ≠ 0) :
    M / q ^ (M.factorization q - a) ≠ 0 :=
  (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM)
    ((Nat.pow_dvd_pow q (Nat.sub_le _ _)).trans (Nat.ordProj_dvd M q))) (pow_pos (Nat.pos_of_ne_zero hq) _)).ne'

private theorem factorization_level_lowered_self {q : ℕ} (hq : q.Prime) {a : ℕ} (hva : a < M.factorization q) :
    (M / q ^ (M.factorization q - a)).factorization q = a := by
  rw [Nat.factorization_div (Nat.ordProj_dvd M q |> fun h => (Nat.pow_dvd_pow q (Nat.sub_le _ _)).trans h),
    Finsupp.coe_tsub, Pi.sub_apply, Nat.Prime.factorization_pow hq, Finsupp.single_eq_same]
  omega

private theorem factorization_level_lowered_of_ne {q : ℕ} (hq : q.Prime) {a : ℕ} {ℓ : ℕ} (hℓq : ℓ ≠ q) : (M / q ^ (M.factorization q - a)).factorization ℓ = M.factorization ℓ := by
  rw [Nat.factorization_div (Nat.ordProj_dvd M q |> fun h => (Nat.pow_dvd_pow q (Nat.sub_le _ _)).trans h),
    Finsupp.coe_tsub, Pi.sub_apply, Nat.Prime.factorization_pow hq, Finsupp.single_eq_of_ne hℓq]
  simp

private theorem fn_mul_finEmbed_of_mem_finiteLevelZero_lowered (hM : M ≠ 0)
    (hK₀ : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M), ∀ x, φ (x * finEmbed (𝓞 ℚ) ℚ u) = φ x)
    {q : ℕ} [hq : Fact q.Prime] {a : ℕ} (hva : a < M.factorization q) {y : AdelicSpan φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ))
    (hfix : y ∈ fixedSubmodule (padicK1 q a) (AdelicSpan φ)) (hcent : ∀ z : ℚ_[q]ˣ, centralGL q z • y = y)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel (M / q ^ (M.factorization q - a)))) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z := by
  have hM' : M / q ^ (M.factorization q - a) ≠ 0 := level_lowered_ne_zero hM q a hq.out.ne_zero
  obtain ⟨zc, k, hk, hcomp⟩ := DescentSupportB.exists_finComponent_eq_centralGL_mul (q := q) hM' hu
  rw [factorization_level_lowered_self hq.out hva] at hk
  set c : GL (Fin 2) ℚ_[q] := centralGL q zc * k with hc
  have hw : u * (padicToFinAdelic q c)⁻¹ ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M) :=
    DescentSupportB.mul_padicToFinAdelic_inv_mem_finiteLevelZero
      (fun v hv => DescentSupportB.idealBound_ratLevel_eq_of_factorization_eq hM' hM
        (fun ℓ _ hℓq => factorization_level_lowered_of_ne hq.out hℓq) v hv) hu c hcomp
  have hwq : finComponent (𝓞 ℚ) ℚ (padicPlace q) (u * (padicToFinAdelic q c)⁻¹) = 1 := by
    rw [map_mul, map_inv, finComponent_padicToFinAdelic_self q, hcomp, mul_inv_cancel]

  have hcy : c • y = y := by
    rw [hc, mul_smul, mem_fixedSubmodule_iff.mp hfix k hk, hcent]
  have hsplit : u = u * (padicToFinAdelic q c)⁻¹ * padicToFinAdelic q c := by group
  rw [hsplit, map_mul, ← mul_assoc, ← padicToAdelic_apply, ← fn_padic_smul, hcy,
    fn_mul_finEmbed_of_mem_span_of_qtrivial hK₀ hy hw hwq]

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

private theorem slash_eq_of_hasReading {N : ℕ} (hN : N ≠ 0) {y : AdelicSpan φ} {F : UpperHalfPlane → ℂ} (hF : Continuous F)
    (hread : HasReading y F) (hleft : ∀ γ z, fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z)
    (hright : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N), ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = F := by
  set δ : GL (Fin 2) ℚ := Matrix.SpecialLinearGroup.mapGL ℚ γ with hδ
  refine eq_of_forall_slash_apply_I (continuous_slash hF 2 _) hF fun h hh hpos => ?_
  have hpos' : LanglandsTunnell.ratArchGL2 (archPart δ * h) ∈ Matrix.GLPos (Fin 2) ℝ := by
    rw [ratArch_archPart_mul, hδ, map_castHom_mapGL]
    exact Subgroup.mul_mem _ (mapGL_mem_GLPos γ) hpos
  have hread' := (hasReading_iff y F).mp hread
  have h1 := hread' (archPart δ * h) (glFin_archPart_mul hh δ) hpos'
  rw [ratArch_archPart_mul, hδ, map_castHom_mapGL, SlashAction.slash_mul] at h1
  rw [← hδ] at h1

  have hG : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ) ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) :=
    glFin_globalPoints_mapGL_mem_finiteLevelZero hN hγ
  have h2 : archPart δ * h
      = globalPoints (𝓞 ℚ) ℚ δ * (h * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ))⁻¹) := by
    rw [archPart, mul_assoc, ← map_inv, finEmbed_mul_comm_of_glFin_eq_one hh]
  rw [h2, hleft, hright _ (Subgroup.inv_mem _ hG)] at h1
  rw [← h1, hread' h hh hpos]

private theorem eq_zero_of_hasReading_zero {N : ℕ} (hN : N ≠ 0) {y : AdelicSpan φ} (hread : HasReading y 0)
    (hleft : ∀ γ z, fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z)
    (hright : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N), ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z) :
    y = 0 := by
  refine AdelicSpan.ext φ (AdelicFnCarrier.ext fun z => ?_)
  obtain ⟨γ, h, u, hh, hpos, hu, rfl⟩ := exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hN z
  change fn y _ = fn (0 : AdelicSpan φ) _
  rw [fn_zero, hright u (finiteLevelOne_le_finiteLevelZero (𝓞 ℚ) ℚ _ hu), hleft,
    (hasReading_iff y 0).mp hread h hh hpos, SlashAction.zero_slash]
  rfl

private theorem heckeT_reading_eq_smul {N : ℕ} (ℓ : ℕ) [Fact ℓ.Prime] {y : AdelicSpan φ} {F : UpperHalfPlane → ℂ}
    (hF : Continuous F) (hread : HasReading y F) (hleft : ∀ γ z, fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z)
    (hright : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N), ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z)
    {c : ℂ} (heig : heckeAway ℓ y = c • y) : ModularForm.heckeT 2 ℓ F = c • F := by
  refine eq_of_forall_slash_apply_I (continuous_heckeT hF ℓ) (hF.const_smul c) fun h hh hpos => ?_
  have hread' := (hasReading_iff y F).mp hread
  have hdict := sum_apply_eq_heckeT_slash ℓ (ψ := fn y) (F := F) (N := ratLevel N) hleft hright hread' hh hpos
  rw [← hdict, ← fn_heckeAway, heig, fn_csmul, hread' h hh hpos, ModularForm.smul_slash, Pi.smul_apply,
    σ_apply_of_det_pos ((Matrix.mem_glpos _).mp hpos), smul_eq_mul]

private theorem exists_eq_sum_of_mem_slashSpan {F : UpperHalfPlane → ℂ} (hF : F ∈ slashSpan g) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (β : ι → GL (Fin 2) ℚ),
      F = ∑ i, c i • ((⇑g) ∣[(2 : ℤ)] (β i).map (Rat.castHom ℝ)) := by
  obtain ⟨l, hl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hF
  refine ⟨l.support, inferInstance, fun i => l i, fun i => (i : GL (Fin 2) ℚ), ?_⟩
  rw [← hl, Finsupp.sum, ← Finset.sum_coe_sort]

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open scoped ModularForm

private theorem engine_of_K₀ {M : ℕ} (hM : M ≠ 0) {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hg : g.IsNormalizedEigenform) (q : ℕ) [hq : Fact q.Prime]
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (hK₀ : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M), ∀ x, Φ (x * finEmbed (𝓞 ℚ) ℚ u) = Φ x)
    (a : ℕ) (hva : a < M.factorization q) (y : AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self Φ))
    (hy₀ : y ≠ 0) (hfix : y ∈ fixedSubmodule (padicK1 q a) (AdelicSpan Φ))
    (hcent : ∀ z : ℚ_[q]ˣ, centralGL q z • y = y) :
    ∃ h₀ : CuspForm (CongruenceSubgroup.Gamma0 (M / q ^ (M.factorization q - a))) 2, h₀ ≠ 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (_ : ¬ ℓ ∣ M) (hℓM' : ¬ ℓ ∣ M / q ^ (M.factorization q - a)),
        CuspForm.heckeTLin 2 hℓ hℓM' h₀ = ModularFormClass.qCoeff g ℓ • h₀ := by
  set M' : ℕ := M / q ^ (M.factorization q - a) with hM'def
  have hM' : M' ≠ 0 := level_lowered_ne_zero hM q a hq.out.ne_zero
  haveI : NeZero M := ⟨hM⟩

  obtain ⟨F, hFspan, hread⟩ := exists_hasReading_of_mem_span hM hΦg hy
  have hFcont : Continuous F := continuous_of_mem_slashSpan hFspan
  have hleft : ∀ γ z, fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z := fn_globalPoints_mul_of_mem_span hΦg hy
  have hright : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M'), ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z :=
    fun u hu z => fn_mul_finEmbed_of_mem_finiteLevelZero_lowered hM hK₀ hva hy hfix hcent hu z
  obtain ⟨ι, _, c, β, hF⟩ := exists_eq_sum_of_mem_slashSpan hFspan
  obtain ⟨h₀, hh₀⟩ := CuspForm.exists_eq_sum_smul_slash_of_forall_slash_eq g c β F hF (by
    rintro γ' ⟨γ, hγ, rfl⟩
    exact slash_eq_of_hasReading hM' hFcont hread hleft hright hγ)
  refine ⟨h₀, ?_, ?_⟩
  ·
    rintro rfl
    apply hy₀
    have hF0 : F = 0 := by rw [← hh₀, CuspForm.coe_zero]
    exact eq_zero_of_hasReading_zero hM' (by simpa [hF0] using hread) hleft hright
  · intro ℓ hℓ hℓM hℓM'
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hqℓ : q ≠ ℓ := by
      rintro rfl
      exact hℓM (Nat.dvd_of_factorization_pos (by omega))

    have hTg : ModularForm.heckeT 2 ℓ (⇑g) = ModularFormClass.qCoeff g ℓ • (⇑g) := by
      have := congrArg (fun f : CuspForm (CongruenceSubgroup.Gamma0 M) 2 => (⇑f : UpperHalfPlane → ℂ))
        (CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul M g hg ℓ hℓ hℓM)
      simpa [CuspForm.coe_heckeTLin_apply, CuspForm.coe_smul] using this
    have hself : heckeAway ℓ (AdelicSpan.self Φ) = ModularFormClass.qCoeff g ℓ • AdelicSpan.self Φ :=
      heckeAway_self_eq_smul ℓ hM hℓM hΦg hK₀ hTg
    have heig : heckeAway ℓ y = ModularFormClass.qCoeff g ℓ • y := heckeAway_eq_smul_of_mem_span ℓ hqℓ hself hy
    have hTF : ModularForm.heckeT 2 ℓ F = ModularFormClass.qCoeff g ℓ • F :=
      heckeT_reading_eq_smul (N := M') ℓ hFcont hread hleft hright heig
    have h1 : (⇑(CuspForm.heckeTLin 2 hℓ hℓM' h₀) : UpperHalfPlane → ℂ) = ModularForm.heckeT 2 ℓ (⇑h₀) :=
      CuspForm.coe_heckeTLin_apply 2 hℓ hℓM' h₀
    rw [hh₀] at h1
    have h3 : (⇑(ModularFormClass.qCoeff g ℓ • h₀) : UpperHalfPlane → ℂ) = ModularFormClass.qCoeff g ℓ • F := by
      rw [CuspForm.IsGLPos.coe_smul, hh₀]
    exact CuspForm.ext fun τ => congrFun (h1.trans (hTF.trans h3.symm)) τ

end DescentEngine

namespace DescentEngine

open NumberField AutomorphicForm LocalNewvector ModularFormClass

private theorem engine {M : ℕ} (hM : M ≠ 0) {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hg : g.IsNormalizedEigenform) (q : ℕ) [Fact q.Prime]
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ) (a : ℕ) (hva : a < M.factorization q)
    (y : AdelicSpan Φ) (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self Φ))
    (hy₀ : y ≠ 0) (hfix : y ∈ fixedSubmodule (padicK1 q a) (AdelicSpan Φ))
    (hcent : ∀ z : ℚ_[q]ˣ, centralGL q z • y = y) :
    ∃ h₀ : CuspForm (CongruenceSubgroup.Gamma0 (M / q ^ (M.factorization q - a))) 2, h₀ ≠ 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (_ : ¬ ℓ ∣ M) (hℓM' : ¬ ℓ ∣ M / q ^ (M.factorization q - a)),
        CuspForm.heckeTLin 2 hℓ hℓM' h₀ = qCoeff g ℓ • h₀ :=
  engine_of_K₀ hM hg q hΦg (hΦg.levelZero_inv hM) a hva y hy hy₀ hfix hcent

private theorem goodEigensystemOccursAt_of_engine_output {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {M' : ℕ} (hM' : M' ≠ 0) (hdvd : M' ∣ M)
    (h₀ : CuspForm (CongruenceSubgroup.Gamma0 M') 2) (h₀ne : h₀ ≠ 0)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (_ : ¬ ℓ ∣ M) (hℓM' : ¬ ℓ ∣ M'),
      CuspForm.heckeTLin 2 hℓ hℓM' h₀ = qCoeff g ℓ • h₀) :
    g.GoodEigensystemOccursAt M' := by
  haveI : NeZero M' := ⟨hM'⟩
  obtain ⟨h, hh, hcoef⟩ := CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul h₀ne
    (fun ℓ => qCoeff g ℓ) {ℓ | ℓ ∣ M} (fun ℓ hℓ hℓM' hS => heig ℓ hℓ hS hℓM')
  exact ⟨h, hh, fun ℓ hℓ hℓM => hcoef ℓ hℓ (fun hd => hℓM (hd.trans hdvd)) hℓM⟩

end DescentEngine

noncomputable section

namespace TwistEngineAux

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector HeckeCharacter

section Places

private theorem padicPlace_ne_of_ne {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p ≠ q) :
    padicPlace p ≠ padicPlace q := by
  intro heq
  have h' := congrArg (fun v : HeightOneSpectrum (𝓞 ℚ) => (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) heq
  simp only [padicPlace, Equiv.apply_symm_apply] at h'
  exact h h'

private theorem natGenerator_padicPlace (p : ℕ) [Fact p.Prime] :
    Rat.HeightOneSpectrum.natGenerator (padicPlace p) = p := by
  show (Rat.HeightOneSpectrum.primesEquiv (padicPlace p) : ℕ) = p
  rw [padicPlace, Equiv.apply_symm_apply]

private theorem natCast_mem_asIdeal_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator v ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    show ((n : ℕ) : ℤ) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((n : ℕ) : 𝓞 ℚ) from (map_natCast _ n).symm]
  exact Ideal.apply_mem_of_equiv_iff.symm

private theorem eq_padicPlace_of_natCast_mem {q : ℕ} [hq : Fact q.Prime] {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : v = padicPlace q := by
  have h3 : Rat.HeightOneSpectrum.natGenerator v = q :=
    (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hq.out).mp
      ((natCast_mem_asIdeal_iff v q).mp hv)
  unfold padicPlace
  rw [Equiv.eq_symm_apply]
  exact Subtype.ext h3

private theorem idealMultiplicity_ratLevel_pow_eq_zero {q : ℕ} [hq : Fact q.Prime] (b : ℕ)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ padicPlace q) :
    idealMultiplicity ℚ v (ratLevel (q ^ b)) = 0 := by
  unfold idealMultiplicity
  by_contra hne
  have hdvd : v.asIdeal ∣ ratLevel (q ^ b) :=
    (Associates.count_ne_zero_iff_dvd (ratLevel_ne_bot (pow_ne_zero b hq.out.ne_zero)) v.irreducible).mp hne
  rw [Ideal.dvd_iff_le] at hdvd
  have hmem : ((q ^ b : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := hdvd (by unfold ratLevel; exact Ideal.mem_span_singleton_self _)
  rw [Nat.cast_pow] at hmem
  exact hv (eq_padicPlace_of_natCast_mem (v.isPrime.mem_of_pow_mem b hmem))

private theorem natCast_natGenerator_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Rat.HeightOneSpectrum.prime_natGenerator v).ne_zero

private theorem prime_natCast_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    Prime ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) := by
  have hcast : ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) =
      Rat.ringOfIntegersEquiv.symm ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) :=
    (map_natCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm
  rw [hcast]
  exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr
    (Nat.prime_iff_prime_int.mp (Rat.HeightOneSpectrum.prime_natGenerator v))

private theorem asIdeal_eq_span_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ)} := by
  have hmax : (Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (natCast_natGenerator_ne_zero v)).mpr (prime_natCast_natGenerator v)).isMaximal
      ((Ideal.span_singleton_eq_bot (α := 𝓞 ℚ)).not.mpr (natCast_natGenerator_ne_zero v))
  exact (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr
    ((natCast_mem_asIdeal_iff v _).mpr dvd_rfl))).symm

private theorem asIdeal_padicPlace (p : ℕ) [Fact p.Prime] :
    (padicPlace p).asIdeal = Ideal.span {((p : ℕ) : 𝓞 ℚ)} := by
  rw [asIdeal_eq_span_natGenerator, natGenerator_padicPlace]

private theorem valued_natCast (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Valued.v ((n : ℕ) : v.adicCompletion ℚ) = v.intValuation ((n : ℕ) : 𝓞 ℚ) := by
  have h1 : ((n : ℕ) : v.adicCompletion ℚ) = algebraMap ℚ (v.adicCompletion ℚ) ((n : ℕ) : ℚ) :=
    (map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) n).symm
  have h2 : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((n : ℕ) : ℚ)) = v.valuation ℚ ((n : ℕ) : ℚ) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [h1, h2, show ((n : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((n : ℕ) : 𝓞 ℚ) from (map_natCast (algebraMap (𝓞 ℚ) ℚ) _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]

private theorem valued_natCast_self (p : ℕ) [hp : Fact p.Prime] :
    Valued.v ((p : ℕ) : (padicPlace p).adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [valued_natCast]
  exact HeightOneSpectrum.intValuation_singleton (v := padicPlace p) (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    (asIdeal_padicPlace p)

private theorem valued_natCast_of_ne (p : ℕ) [Fact p.Prime] {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ padicPlace p) :
    Valued.v ((p : ℕ) : v.adicCompletion ℚ) = 1 := by
  rw [valued_natCast]
  exact HeightOneSpectrum.intValuation_eq_one_iff.mpr fun hmem => hv (eq_padicPlace_of_natCast_mem hmem)

private theorem natCast_prime_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) [hp : Fact p.Prime] :
    ((p : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
  intro h
  have h1 := valued_natCast v p
  rw [h, Valuation.map_zero] at h1
  exact HeightOneSpectrum.intValuation_ne_zero v _ (Nat.cast_ne_zero.mpr hp.out.ne_zero) h1.symm

private def natUnitAt (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) [Fact p.Prime] : (v.adicCompletion ℚ)ˣ :=
  Units.mk0 _ (natCast_prime_ne_zero v p)

private theorem coe_natUnitAt (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) [Fact p.Prime] :
    ((natUnitAt v p : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = ((p : ℕ) : v.adicCompletion ℚ) := rfl

end Places

section Character

variable (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)

private theorem apply_eq_one_of_admitsModulus {q : ℕ} [Fact q.Prime] {b : ℕ}
    (hηb : AdmitsModulus ℚ η (ratLevel (q ^ b))) (u : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hu1 : (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1)
    (hunit : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((u : AdeleRing (𝓞 ℚ) ℚ).2 v) = 1)
    (huq : (u : AdeleRing (𝓞 ℚ) ℚ).2 (padicPlace q) = 1) :
    η u = 1 := by
  refine hηb u hu1 fun v => ⟨hunit v, ?_⟩
  by_cases hv : v = padicPlace q
  · subst hv
    rw [huq, sub_self, map_zero]
    exact zero_le'
  · rw [idealMultiplicity_ratLevel_pow_eq_zero b hv, Nat.cast_zero, neg_zero, WithZero.exp_zero]
    calc Valued.v ((u : AdeleRing (𝓞 ℚ) ℚ).2 v - 1)
        ≤ max (Valued.v ((u : AdeleRing (𝓞 ℚ) ℚ).2 v)) (Valued.v (1 : (v.adicCompletion ℚ))) :=
          Valuation.map_sub _ _ _
      _ = 1 := by rw [hunit v, Valuation.map_one, max_self]

private theorem apply_finIncl_localUnit_eq_one {q : ℕ} [Fact q.Prime] {b : ℕ}
    (hηb : AdmitsModulus ℚ η (ratLevel (q ^ b))) (p : ℕ) [Fact p.Prime] (hpq : p ≠ q)
    (t : ((padicPlace p).adicCompletion ℚ)ˣ) (ht : Valued.v (t : (padicPlace p).adicCompletion ℚ) = 1) :
    η (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (padicPlace p) t)) = 1 := by
  refine apply_eq_one_of_admitsModulus η hηb _ ?_ ?_ ?_
  · exact finIncl_apply_fst (𝓞 ℚ) ℚ _
  · intro v
    simp only [Units.coe_map, finIncl_apply_snd]
    by_cases hv : v = padicPlace p
    · subst hv
      rw [localUnit_apply_self]
      exact ht
    · rw [localUnit_apply_of_ne _ _ _ _ hv, Valuation.map_one]
  · simp only [Units.coe_map, finIncl_apply_snd]
    exact localUnit_apply_of_ne _ _ _ _ (padicPlace_ne_of_ne hpq).symm

private theorem apply_finIncl_localUnit_natUnitAt {q : ℕ} [Fact q.Prime] {b : ℕ}
    (hηb : AdmitsModulus ℚ η (ratLevel (q ^ b))) (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) :
    η (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (padicPlace p) (natUnitAt (padicPlace p) p))) =
      η (uniformizerIdele ℚ (padicPlace p)) := by
  have hsplit : natUnitAt (padicPlace p) p =
      uniformizerUnit ℚ (padicPlace p) * (natUnitAt (padicPlace p) p * (uniformizerUnit ℚ (padicPlace p))⁻¹) := by
    rw [mul_comm (uniformizerUnit ℚ (padicPlace p)), inv_mul_cancel_right]
  have hval : Valued.v ((natUnitAt (padicPlace p) p * (uniformizerUnit ℚ (padicPlace p))⁻¹ :
      ((padicPlace p).adicCompletion ℚ)ˣ) : (padicPlace p).adicCompletion ℚ) = 1 := by
    rw [Units.val_mul, Valuation.map_mul, Units.val_inv_eq_inv_val, map_inv₀, coe_natUnitAt, valued_natCast_self,
      valued_uniformizerUnit, mul_inv_cancel₀ WithZero.exp_ne_zero]
  rw [hsplit, map_mul, map_mul, map_mul, apply_finIncl_localUnit_eq_one η hηb p hpq _ hval, mul_one]
  rfl

end Character

section Archimedean

variable (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)

private def archEquiv (w : InfinitePlace ℚ) : w.Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)

private def archHom : ℝ →* AdeleRing (𝓞 ℚ) ℚ where
  toFun s := ((fun w => (archEquiv w).symm s : InfiniteAdeleRing ℚ), (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))
  map_one' := Prod.ext (funext fun w => map_one (archEquiv w).symm) rfl
  map_mul' s t :=
    Prod.ext (funext fun w => map_mul (archEquiv w).symm s t) (one_mul (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)).symm

private theorem archHom_fst_apply (s : ℝ) (w : InfinitePlace ℚ) : (archHom s).1 w = (archEquiv w).symm s := rfl

private theorem archHom_snd (s : ℝ) : (archHom s).2 = 1 := rfl

private theorem apply_map_archHom_eq_one (hη : IsFiniteOrderHeckeChar ℚ η) (u : ℝˣ) (hu : 0 < (u : ℝ)) :
    η (Units.map archHom u) = 1 := by
  obtain ⟨n, hn, hηn⟩ := isOfFinOrder_iff_pow_eq_one.mp hη.isOfFinOrder
  have hs : 0 < (u : ℝ) ^ ((n : ℝ)⁻¹) := Real.rpow_pos_of_pos hu _
  have hu' : u = (Units.mk0 _ hs.ne') ^ n := by
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Real.rpow_inv_natCast_pow hu.le hn.ne']
  have h1 : η (Units.map archHom (Units.mk0 _ hs.ne')) ^ n = 1 := by
    have h2 := congrArg (fun χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ => χ (Units.map archHom (Units.mk0 _ hs.ne'))) hηn
    simpa using h2
  rw [hu', map_pow, map_pow, h1]

private theorem det_eq_map_archHom {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : glFin (𝓞 ℚ) ℚ h = 1) :
    h.det = Units.map archHom (LanglandsTunnell.ratArchGL2 h).det := by
  have h1 : ((LanglandsTunnell.ratArchGL2 h).det : ℝ) = archEquiv default ((h.det : AdeleRing (𝓞 ℚ) ℚ).1 default) := by
    simp only [LanglandsTunnell.ratArchGL2, Matrix.GeneralLinearGroup.map_det, archComponent, glArch, Units.coe_map]
    rfl
  have h2 : (h.det : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := by
    have h3 := congrArg (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (g.det : FiniteAdeleRing (𝓞 ℚ) ℚ)) hh
    simp only [glFin, Matrix.GeneralLinearGroup.map_det, Units.coe_map, map_one, Units.val_one] at h3
    exact h3
  ext1
  refine Prod.ext ?_ ?_
  · funext w
    have hw : w = default := Subsingleton.elim w default
    subst hw
    show (h.det : AdeleRing (𝓞 ℚ) ℚ).1 default = (archEquiv default).symm ((LanglandsTunnell.ratArchGL2 h).det : ℝ)
    rw [h1, RingEquiv.symm_apply_apply]
  · exact h2

private theorem eta_det_eq_one_of_glFin_eq_one_of_glPos (hη : IsFiniteOrderHeckeChar ℚ η)
    {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    (η h.det : ℂ) = 1 := by
  rw [det_eq_map_archHom hh, apply_map_archHom_eq_one η hη _ ((Matrix.mem_glpos _).mp hpos), Units.val_one]

end Archimedean

section Local

variable (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)

private theorem det_padicToAdelic (p : ℕ) [Fact p.Prime] (k : GL (Fin 2) ℚ_[p]) :
    (padicToAdelic p k).det =
      Units.map (finIncl (𝓞 ℚ) ℚ)
        (localUnit (𝓞 ℚ) ℚ (padicPlace p) (Units.map (padicRingEquiv p).toRingHom.toMonoidHom k.det)) := by

  have hfin : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      ((padicToAdelic p k).det : AdeleRing (𝓞 ℚ) ℚ).2 w =
        ((finComponent (𝓞 ℚ) ℚ w (padicToFinAdelic p k)).det : w.adicCompletion ℚ) := by
    intro w
    have e1 : glFin (𝓞 ℚ) ℚ (padicToAdelic p k) = padicToFinAdelic p k := glFin_finEmbed _ _ _
    have e2 := congrArg (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      ((finComponent (𝓞 ℚ) ℚ w g).det : w.adicCompletion ℚ)) e1
    simp only [glFin, finComponent, Matrix.GeneralLinearGroup.map_det, Units.coe_map] at e2 ⊢
    exact e2
  have harch : ((padicToAdelic p k).det : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := by
    have e1 : glArch (𝓞 ℚ) ℚ (padicToAdelic p k) = 1 := glArch_finEmbed _ _ _
    have e2 := congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing ℚ) => (g.det : InfiniteAdeleRing ℚ)) e1
    simp only [glArch, Matrix.GeneralLinearGroup.map_det, Units.coe_map, map_one, Units.val_one] at e2
    exact e2
  ext1
  refine Prod.ext ?_ ?_
  · rw [harch]
    exact (finIncl_apply_fst (𝓞 ℚ) ℚ _).symm
  · refine Subtype.ext (funext fun w => ?_)
    change ((padicToAdelic p k).det : AdeleRing (𝓞 ℚ) ℚ).2 w =
      ((localUnit (𝓞 ℚ) ℚ (padicPlace p) (Units.map (padicRingEquiv p).toRingHom.toMonoidHom k.det) :
        (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w
    rw [hfin w]
    by_cases hw : w = padicPlace p
    · subst hw
      rw [finComponent_padicToFinAdelic_self, localUnit_apply_self]
      simp only [padicGL, Matrix.GeneralLinearGroup.map_det, Units.coe_map]
      rfl
    · rw [finComponent_padicToFinAdelic_of_ne p k hw, localUnit_apply_of_ne _ _ _ _ hw, map_one, Units.val_one]

private theorem map_det_eq_natUnitAt (p : ℕ) [Fact p.Prime] {k : GL (Fin 2) ℚ_[p]}
    (hk : (k.det : ℚ_[p]) = (p : ℚ_[p])) :
    Units.map (padicRingEquiv p).toRingHom.toMonoidHom k.det = natUnitAt (padicPlace p) p := by
  ext
  rw [Units.coe_map, coe_natUnitAt]
  change padicRingEquiv p (k.det : ℚ_[p]) = _
  rw [hk, map_natCast]

private theorem eta_det_padicToAdelic_inv_of_det_eq {q : ℕ} [Fact q.Prime] {b : ℕ}
    (hηb : AdmitsModulus ℚ η (ratLevel (q ^ b))) (p : ℕ) [Fact p.Prime] (hpq : p ≠ q)
    {k : GL (Fin 2) ℚ_[p]} (hk : (k.det : ℚ_[p]) = (p : ℚ_[p])) :
    (η (padicToAdelic p k⁻¹).det : ℂ) = (η (uniformizerIdele ℚ (padicPlace p)) : ℂ)⁻¹ := by
  rw [map_inv, map_inv, map_inv, det_padicToAdelic, map_det_eq_natUnitAt p hk,
    apply_finIncl_localUnit_natUnitAt η hηb p hpq, Units.val_inv_eq_inv_val]

end Local

section Principal

variable (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)

private def compFin (w : HeightOneSpectrum (𝓞 ℚ)) : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* (w.adicCompletion ℚ)ˣ :=
  Units.map ((finAdeleEval (𝓞 ℚ) ℚ w).comp (adeleFin (𝓞 ℚ) ℚ)).toMonoidHom

private theorem coe_compFin (w : HeightOneSpectrum (𝓞 ℚ)) (u : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((compFin w u : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ) = (u : AdeleRing (𝓞 ℚ) ℚ).2 w := rfl

private def compArch : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* (InfiniteAdeleRing ℚ)ˣ :=
  Units.map (adeleArch (𝓞 ℚ) ℚ).toMonoidHom

private theorem coe_compArch (u : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((compArch u : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = (u : AdeleRing (𝓞 ℚ) ℚ).1 := rfl

private theorem apply_eq_one_of_comp {q : ℕ} [Fact q.Prime] {b : ℕ}
    (hηb : AdmitsModulus ℚ η (ratLevel (q ^ b))) (u : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (h1 : compArch u = 1)
    (h2 : ∀ w : HeightOneSpectrum (𝓞 ℚ), Valued.v ((compFin w u : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ) = 1)
    (h3 : compFin (padicPlace q) u = 1) : η u = 1 := by
  refine apply_eq_one_of_admitsModulus η hηb u ?_ ?_ ?_
  · rw [← coe_compArch, h1, Units.val_one]
  · intro w
    rw [← coe_compFin]
    exact h2 w
  · rw [← coe_compFin, h3, Units.val_one]

private theorem coe_compFin_map_finIncl (w : HeightOneSpectrum (𝓞 ℚ)) (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((compFin w (Units.map (finIncl (𝓞 ℚ) ℚ) x) : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ) =
      ((x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w := rfl

private theorem compArch_map_finIncl (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    compArch (Units.map (finIncl (𝓞 ℚ) ℚ) x) = 1 := by
  ext
  rw [coe_compArch, Units.val_one]
  exact finIncl_apply_fst (𝓞 ℚ) ℚ _

private theorem coe_compFin_map_archHom (w : HeightOneSpectrum (𝓞 ℚ)) (u : ℝˣ) :
    ((compFin w (Units.map archHom u) : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ) = 1 := by
  rw [coe_compFin]
  change ((1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) w = 1
  rfl

private def principalNat (ℓ : ℕ) [hℓ : Fact ℓ.Prime] : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) (Units.mk0 ((ℓ : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hℓ.out.ne_zero))

private theorem coe_principalNat (ℓ : ℕ) [Fact ℓ.Prime] :
    ((principalNat ℓ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) = ((ℓ : ℕ) : AdeleRing (𝓞 ℚ) ℚ) := by
  change algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((ℓ : ℕ) : ℚ) = _
  rw [map_natCast]

private theorem coe_compFin_principalNat (w : HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] :
    ((compFin w (principalNat ℓ) : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ) = ((ℓ : ℕ) : w.adicCompletion ℚ) := by
  change (((finAdeleEval (𝓞 ℚ) ℚ w).comp (adeleFin (𝓞 ℚ) ℚ)).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))
    ((ℓ : ℕ) : ℚ) = _
  exact map_natCast _ ℓ

private def archNat (ℓ : ℕ) [hℓ : Fact ℓ.Prime] : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map archHom (Units.mk0 ((ℓ : ℕ) : ℝ) (Nat.cast_ne_zero.mpr hℓ.out.ne_zero))

private theorem compArch_archNat_eq (ℓ : ℕ) [Fact ℓ.Prime] : compArch (archNat ℓ) = compArch (principalNat ℓ) := by
  ext1
  rw [coe_compArch, coe_compArch]
  have hP : ((principalNat ℓ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = ((ℓ : ℕ) : InfiniteAdeleRing ℚ) :=
    map_natCast ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ))) ℓ
  rw [hP]
  funext w
  change (archEquiv w).symm ((ℓ : ℕ) : ℝ) = ((ℓ : ℕ) : InfiniteAdeleRing ℚ) w
  rw [map_natCast]
  rfl

private def localNat (v : HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v (natUnitAt v ℓ))

private theorem coe_compFin_localNat_self (v : HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] :
    ((compFin v (localNat v ℓ) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = ((ℓ : ℕ) : v.adicCompletion ℚ) := by
  rw [localNat, coe_compFin_map_finIncl, localUnit_apply_self, coe_natUnitAt]

private theorem coe_compFin_localNat_of_ne (v : HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ) [Fact ℓ.Prime]
    {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    ((compFin w (localNat v ℓ) : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ) = 1 := by
  rw [localNat, coe_compFin_map_finIncl, localUnit_apply_of_ne _ _ _ _ hw]

private theorem apply_uniformizerIdele_mul_apply_localUnit_natUnitAt (hη : IsFiniteOrderHeckeChar ℚ η)
    {q : ℕ} [Fact q.Prime] {b : ℕ} (hηb : AdmitsModulus ℚ η (ratLevel (q ^ b)))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    η (uniformizerIdele ℚ (padicPlace ℓ)) *
      η (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (padicPlace q) (natUnitAt (padicPlace q) ℓ))) = 1 := by
  have hℓq' : padicPlace ℓ ≠ padicPlace q := padicPlace_ne_of_ne hℓq

  have hP : η (principalNat ℓ) = 1 := hη.isIdeleClassChar _

  have hA : η (archNat ℓ) = 1 :=
    apply_map_archHom_eq_one η hη _ (by rw [Units.val_mk0]; exact_mod_cast (Fact.out : ℓ.Prime).pos)

  set X : (AdeleRing (𝓞 ℚ) ℚ)ˣ := archNat ℓ * localNat (padicPlace ℓ) ℓ * localNat (padicPlace q) ℓ with hX
  set U : (AdeleRing (𝓞 ℚ) ℚ)ˣ := principalNat ℓ * X⁻¹ with hU
  have hXU : X * U = principalNat ℓ := by
    rw [hU, mul_comm, inv_mul_cancel_right]
  have hUarch : compArch U = 1 := by
    rw [hU, map_mul, map_inv, hX, map_mul, map_mul, compArch_archNat_eq, localNat, compArch_map_finIncl,
      localNat, compArch_map_finIncl, mul_one, mul_one, mul_inv_cancel]
  have hUfin : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      ((compFin w U : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ) =
        ((ℓ : ℕ) : w.adicCompletion ℚ) *
          (((compFin w (localNat (padicPlace ℓ) ℓ) : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ) *
            ((compFin w (localNat (padicPlace q) ℓ) : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ))⁻¹ := by
    intro w
    rw [hU, map_mul, map_inv, hX, map_mul, map_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mul,
      Units.val_mul, coe_compFin_principalNat, archNat, coe_compFin_map_archHom, one_mul]
  have hUq : compFin (padicPlace q) U = 1 := by
    ext
    rw [hUfin, coe_compFin_localNat_of_ne _ _ hℓq'.symm, coe_compFin_localNat_self, one_mul,
      mul_inv_cancel₀ (natCast_prime_ne_zero _ ℓ), Units.val_one]
  have hUval : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Valued.v ((compFin w U : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ) = 1 := by
    intro w
    rw [hUfin]
    by_cases hwℓ : w = padicPlace ℓ
    · subst hwℓ
      rw [coe_compFin_localNat_self, coe_compFin_localNat_of_ne _ _ hℓq', mul_one,
        mul_inv_cancel₀ (natCast_prime_ne_zero _ ℓ), Valuation.map_one]
    · rw [coe_compFin_localNat_of_ne _ _ hwℓ, one_mul]
      by_cases hwq : w = padicPlace q
      · subst hwq
        rw [coe_compFin_localNat_self, mul_inv_cancel₀ (natCast_prime_ne_zero _ ℓ), Valuation.map_one]
      · rw [coe_compFin_localNat_of_ne _ _ hwq, inv_one, mul_one]
        exact valued_natCast_of_ne ℓ hwℓ
  have hUη : η U = 1 := apply_eq_one_of_comp η hηb U hUarch hUval hUq

  have hprod : η X * η U = 1 := by rw [← map_mul, hXU, hP]
  rw [hUη, mul_one, hX, map_mul, map_mul, hA, one_mul] at hprod
  rw [← hprod, localNat, localNat, apply_finIncl_localUnit_natUnitAt η hηb ℓ hℓq]

end Principal

end TwistEngineAux

end

namespace TwistEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector HeckeCharacter
open DescentEngine TwistEngineAux

section DetFinEmbed

private theorem det_finEmbed_snd_apply (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((finEmbed (𝓞 ℚ) ℚ u).det : AdeleRing (𝓞 ℚ) ℚ).2 w
      = ((finComponent (𝓞 ℚ) ℚ w u).det : w.adicCompletion ℚ) := by
  have e1 : glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ u) = u := glFin_finEmbed (𝓞 ℚ) ℚ u
  have e2 := congrArg (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
    ((finComponent (𝓞 ℚ) ℚ w g).det : w.adicCompletion ℚ)) e1
  simp only [glFin, finComponent, Matrix.GeneralLinearGroup.map_det, Units.coe_map] at e2 ⊢
  exact e2

private theorem det_finEmbed_fst (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ((finEmbed (𝓞 ℚ) ℚ u).det : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := by
  have e1 : glArch (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ u) = 1 := glArch_finEmbed (𝓞 ℚ) ℚ u
  have e2 := congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing ℚ) => (g.det : InfiniteAdeleRing ℚ)) e1
  simp only [glArch, Matrix.GeneralLinearGroup.map_det, Units.coe_map, map_one, Units.val_one] at e2
  exact e2

private theorem valued_det_finComponent_eq_one_of_mem_finiteLevelZero
    {N : Ideal (𝓞 ℚ)} {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ N) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((finComponent (𝓞 ℚ) ℚ w u).det : w.adicCompletion ℚ) = 1 := by
  have hle : ∀ g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ),
      IsLevelZeroMatrix (𝓞 ℚ) ℚ N (g : Matrix _ _ _) →
      Valued.v ((finComponent (𝓞 ℚ) ℚ w g).det : w.adicCompletion ℚ) ≤ 1 := by
    intro g hg
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    all_goals
      rw [Valuation.map_mul]
      refine mul_le_one' ?_ ?_
      all_goals
        rw [finComponent_apply]
        exact valued_apply_le_one (hg.integral _ _) w
  have h1 : Valued.v ((finComponent (𝓞 ℚ) ℚ w u).det : w.adicCompletion ℚ) ≤ 1 := hle u hu.1
  have h2 : Valued.v ((finComponent (𝓞 ℚ) ℚ w u⁻¹).det : w.adicCompletion ℚ) ≤ 1 := hle u⁻¹ hu.2
  refine le_antisymm h1 ?_
  have hprod : Valued.v ((finComponent (𝓞 ℚ) ℚ w u).det : w.adicCompletion ℚ)
      * Valued.v ((finComponent (𝓞 ℚ) ℚ w u⁻¹).det : w.adicCompletion ℚ) = 1 := by
    rw [← Valuation.map_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel,
      map_one, map_one, Units.val_one, map_one]
  calc (1 : _) = _ := hprod.symm
    _ ≤ Valued.v ((finComponent (𝓞 ℚ) ℚ w u).det : w.adicCompletion ℚ) * 1 := by gcongr
    _ = _ := mul_one _

private theorem padicToFinAdelic_centralGL_mem_finiteLevelZero (q : ℕ) [Fact q.Prime]
    (M : ℕ) (u : ℤ_[q]ˣ) :
    padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u))
      ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M) := by
  have hbody : ∀ u' : ℤ_[q]ˣ, IsLevelZeroMatrix (𝓞 ℚ) ℚ (ratLevel M)
      ((padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u'))).val) := by
    intro u'
    refine ⟨fun i j w => ?_, ?_⟩
    · rw [padicToFinAdelic_apply, coe_localEmbed]
      by_cases hw : w = padicPlace q
      · subst hw
        rw [localMat_apply_self, padicGL_apply]
        show padicRingEquiv q
            ((algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q])) ((u' : ℤ_[q]) : ℚ_[q]) i j)
          ∈ (padicPlace q).adicCompletionIntegers ℚ
        rw [Matrix.algebraMap_matrix_apply]
        split_ifs
        · exact padicRingEquiv_coe_mem q (u' : ℤ_[q])
        · rw [map_zero]; exact zero_mem _
      · rw [localMat_apply_of_ne (𝓞 ℚ) ℚ (padicPlace q) _ i j hw, Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    · intro w
      rw [padicToFinAdelic_apply, coe_localEmbed]
      by_cases hw : w = padicPlace q
      · subst hw
        rw [localMat_apply_self, padicGL_apply]
        show Valued.v (padicRingEquiv q
            ((algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q])) ((u' : ℤ_[q]) : ℚ_[q]) 1 0)) ≤ _
        rw [Matrix.algebraMap_matrix_apply, if_neg (by decide), map_zero, map_zero]
        exact zero_le'
      · rw [localMat_apply_of_ne (𝓞 ℚ) ℚ (padicPlace q) _ 1 0 hw,
          Matrix.one_apply_ne (by decide), map_zero]
        exact zero_le'
  refine mem_finiteLevelZero_iff.mpr ⟨hbody u, ?_⟩
  have hinv : (padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))⁻¹
      = padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u⁻¹)) := by
    rw [← map_inv, ← map_inv, ← map_inv]
  rw [hinv]
  exact hbody u⁻¹

end DetFinEmbed

section TwistSubLemmas

variable (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)

private theorem eta_det_globalPoints_eq_one (hη : IsFiniteOrderHeckeChar ℚ η) (γ : GL (Fin 2) ℚ) :
    (η (globalPoints (𝓞 ℚ) ℚ γ).det : ℂ) = 1 := by
  have hdet : (globalPoints (𝓞 ℚ) ℚ γ).det
      = Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) (Matrix.GeneralLinearGroup.det γ) := by
    rw [globalPoints, Matrix.GeneralLinearGroup.map_det]
  rw [hdet, hη.isIdeleClassChar (Matrix.GeneralLinearGroup.det γ), Units.val_one]

private theorem eta_det_finEmbed_eq_one_of_finiteLevelZero_of_qtrivial
    {q : ℕ} [Fact q.Prime] {b : ℕ} (hηb : AdmitsModulus ℚ η (ratLevel (q ^ b)))
    {N : ℕ} (hN : N ≠ 0) {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N))
    (hqtriv : finComponent (𝓞 ℚ) ℚ (padicPlace q) u = 1) :
    (η (finEmbed (𝓞 ℚ) ℚ u).det : ℂ) = 1 := by
  have _ := hN
  rw [show η (finEmbed (𝓞 ℚ) ℚ u).det = 1 from ?_, Units.val_one]
  refine apply_eq_one_of_comp η hηb _ ?_ ?_ ?_
  · ext; rw [coe_compArch, det_finEmbed_fst, Units.val_one]
  · intro w; rw [coe_compFin, det_finEmbed_snd_apply]
    exact valued_det_finComponent_eq_one_of_mem_finiteLevelZero hu w
  · ext; rw [coe_compFin, det_finEmbed_snd_apply, hqtriv, map_one, Units.val_one]

private theorem eta_det_padicToAdelic_ρQ_inv
    {q : ℕ} [Fact q.Prime] {b : ℕ} (hηb : AdmitsModulus ℚ η (ratLevel (q ^ b)))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (i : Fin (ℓ + 1)) :
    (η (padicToAdelic ℓ (ρQ ℓ i)⁻¹).det : ℂ) =
      (η (uniformizerIdele ℚ (@padicPlace ℓ ⟨Fact.out⟩)) : ℂ)⁻¹ := by
  refine eta_det_padicToAdelic_inv_of_det_eq η hηb ℓ hℓq ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_ρQ,
    show ((HeckeCosets.repZ ℓ i).map (algebraMap ℤ_[ℓ] ℚ_[ℓ]))
        = (algebraMap ℤ_[ℓ] ℚ_[ℓ]).mapMatrix (HeckeCosets.repZ ℓ i) from rfl,
    ← RingHom.map_det, HeckeCosets.det_repZ, map_natCast]

private theorem fnTwist_ne_zero_iff (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    fnTwist ℚ η Φ ≠ 0 ↔ Φ ≠ 0 := by
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · ext g
    have hg : chiDet (𝓞 ℚ) ℚ η g * Φ g = 0 := by have := congrFun h g; simpa [fnTwist_apply] using this
    exact (mul_eq_zero.mp hg).resolve_left (by exact_mod_cast Units.ne_zero _)
  · ext g; simp only [fnTwist_apply, h, Pi.zero_apply, mul_zero]

private theorem fnTwist_left_inv (hη : IsFiniteOrderHeckeChar ℚ η)
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hΦleft : ∀ (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ), Φ (globalPoints (𝓞 ℚ) ℚ γ * z) = Φ z)
    (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fnTwist ℚ η Φ (globalPoints (𝓞 ℚ) ℚ γ * z) = fnTwist ℚ η Φ z := by
  rw [fnTwist_apply, fnTwist_apply, chiDet_globalPoints_mul ℚ η hη.isIdeleClassChar, hΦleft]

private theorem fnTwist_levelZero_inv_of_qtrivial {q : ℕ} [Fact q.Prime] {b : ℕ}
    (hηb : AdmitsModulus ℚ η (ratLevel (q ^ b)))
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {M : ℕ} (hM : M ≠ 0)
    (hK₀ : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M), ∀ x, Φ (x * finEmbed (𝓞 ℚ) ℚ u) = Φ x)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M))
    (huq : finComponent (𝓞 ℚ) ℚ (padicPlace q) u = 1) (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    fnTwist ℚ η Φ (x * finEmbed (𝓞 ℚ) ℚ u) = fnTwist ℚ η Φ x := by
  simp only [fnTwist_apply, hK₀ u hu x, chiDet, map_mul, Units.val_mul,
    eta_det_finEmbed_eq_one_of_finiteLevelZero_of_qtrivial η hηb hM hu huq, mul_one]

end TwistSubLemmas

section TwistedEngine

open scoped ModularForm

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
variable {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable (ηc : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
variable {q : ℕ} [Fact q.Prime]

private theorem exists_hasReading_padic_smul_self_twist (hM : M ≠ 0) (hφg : g.IsAdelicLiftOf Φ)
    (hη : IsFiniteOrderHeckeChar ℚ ηc) (x : GL (Fin 2) ℚ_[q]) :
    ∃ F ∈ slashSpan g, HasReading (φ := fnTwist ℚ ηc Φ) (x • AdelicSpan.self (fnTwist ℚ ηc Φ)) F := by
  obtain ⟨F₀, hF₀span, hread₀⟩ := exists_hasReading_padic_smul_self hM hφg x
  refine ⟨chiDet (𝓞 ℚ) ℚ ηc (padicToAdelic q x) • F₀, Submodule.smul_mem _ _ hF₀span, ?_⟩
  intro h hh hpos
  change fn (x • AdelicSpan.self (fnTwist ℚ ηc Φ)) h
    = ((chiDet (𝓞 ℚ) ℚ ηc (padicToAdelic q x) • F₀)
        ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I
  rw [fn_padic_smul_self, fnTwist_apply, ModularForm.smul_slash, Pi.smul_apply,
    σ_apply_of_det_pos ((Matrix.mem_glpos _).mp hpos), smul_eq_mul]
  have hR : (F₀ ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I = Φ (h * padicToAdelic q x) := by
    have hrd := hread₀ h hh hpos
    change fn (x • AdelicSpan.self Φ) h = _ at hrd
    rw [fn_padic_smul_self] at hrd
    exact hrd.symm
  rw [hR, chiDet, map_mul, map_mul, Units.val_mul,
    eta_det_eq_one_of_glFin_eq_one_of_glPos ηc hη hh hpos, one_mul, chiDet]

private theorem exists_hasReading_of_mem_span_twist (hM : M ≠ 0) (hφg : g.IsAdelicLiftOf Φ)
    (hη : IsFiniteOrderHeckeChar ℚ ηc)
    {y : AdelicSpan (fnTwist ℚ ηc Φ)}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self (fnTwist ℚ ηc Φ))) :
    ∃ F ∈ slashSpan g, HasReading y F := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨x, rfl⟩ := hy; exact exists_hasReading_padic_smul_self_twist ηc hM hφg hη x
  | zero => exact ⟨0, Submodule.zero_mem _, hasReading_zero⟩
  | add y₁ y₂ _ _ ih₁ ih₂ =>
    obtain ⟨F₁, hF₁, h₁⟩ := ih₁; obtain ⟨F₂, hF₂, h₂⟩ := ih₂
    exact ⟨F₁ + F₂, Submodule.add_mem _ hF₁ hF₂, h₁.add h₂⟩
  | smul c y _ ih => obtain ⟨F, hF, h⟩ := ih; exact ⟨c • F, Submodule.smul_mem _ c hF, h.smul c⟩

private theorem fn_globalPoints_mul_of_mem_span_twist (hφg : g.IsAdelicLiftOf Φ)
    (hη : IsFiniteOrderHeckeChar ℚ ηc)
    {y : AdelicSpan (fnTwist ℚ ηc Φ)}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self (fnTwist ℚ ηc Φ)))
    (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    rw [fn_padic_smul_self, fn_padic_smul_self, mul_assoc, fnTwist_left_inv ηc hη hφg.left_inv]
  | zero => rfl
  | add y₁ y₂ _ _ ih₁ ih₂ => rw [fn_add, fn_add, ih₁, ih₂]
  | smul c y _ ih => rw [fn_csmul, fn_csmul, ih]

private theorem factorization_level_lowered_self_le {q : ℕ} (hq : q.Prime) {a : ℕ}
    (hae : a ≤ M.factorization q) :
    (M / q ^ (M.factorization q - a)).factorization q = a := by
  rcases lt_or_eq_of_le hae with h | h
  · exact factorization_level_lowered_self hq h
  · rw [h, Nat.sub_self, pow_zero, Nat.div_one]

private theorem fn_mul_finEmbed_of_mem_finiteLevelZero_lowered_twist (hM : M ≠ 0) (hφg : g.IsAdelicLiftOf Φ)
    {b : ℕ} (hηb : AdmitsModulus ℚ ηc (ratLevel (q ^ b)))
    {a : ℕ} (hae : a ≤ M.factorization q)
    {y : AdelicSpan (fnTwist ℚ ηc Φ)}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self (fnTwist ℚ ηc Φ)))
    (hfix : y ∈ fixedSubmodule (padicK1 q a) (AdelicSpan (fnTwist ℚ ηc Φ)))
    (hcent : ∀ z : ℚ_[q]ˣ, centralGL q z • y = y)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel (M / q ^ (M.factorization q - a))))
    (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z := by
  haveI hqP : Fact q.Prime := inferInstance
  have hM' : M / q ^ (M.factorization q - a) ≠ 0 := level_lowered_ne_zero hM q a hqP.out.ne_zero
  obtain ⟨zc, k, hk, hcomp⟩ := DescentSupportB.exists_finComponent_eq_centralGL_mul (q := q) hM' hu
  rw [factorization_level_lowered_self_le hqP.out hae] at hk
  set c : GL (Fin 2) ℚ_[q] := centralGL q zc * k with hcdef
  have hw : u * (padicToFinAdelic q c)⁻¹ ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M) :=
    DescentSupportB.mul_padicToFinAdelic_inv_mem_finiteLevelZero
      (fun v hv => DescentSupportB.idealBound_ratLevel_eq_of_factorization_eq hM' hM
        (fun ℓ _ hℓq => factorization_level_lowered_of_ne hqP.out hℓq) v hv) hu c hcomp
  have hwq : finComponent (𝓞 ℚ) ℚ (padicPlace q) (u * (padicToFinAdelic q c)⁻¹) = 1 := by
    rw [map_mul, map_inv, finComponent_padicToFinAdelic_self q, hcomp, mul_inv_cancel]
  have hcy : c • y = y := by
    rw [hcdef, mul_smul, mem_fixedSubmodule_iff.mp hfix k hk, hcent]
  have hsplit : u = u * (padicToFinAdelic q c)⁻¹ * padicToFinAdelic q c := by group
  rw [hsplit, map_mul, ← mul_assoc, ← padicToAdelic_apply, ← fn_padic_smul, hcy]
  clear hfix hcent hcy hcdef hcomp hk hsplit

  have hK₀ := hφg.levelZero_inv hM
  have hK₀q : ∀ w ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M),
      finComponent (𝓞 ℚ) ℚ (padicPlace q) w = 1 →
      ∀ x, fnTwist ℚ ηc Φ (x * finEmbed (𝓞 ℚ) ℚ w) = fnTwist ℚ ηc Φ x :=
    fun w hwM hwq' x => fnTwist_levelZero_inv_of_qtrivial ηc hηb hM hK₀ hwM hwq' x
  induction hy using Submodule.span_induction with
  | mem y' hy' =>
    obtain ⟨x, rfl⟩ := hy'
    rw [fn_padic_smul_self, fn_padic_smul_self, padicToAdelic_apply, mul_assoc, ← map_mul,
      DescentSupportA.commute_of_finComponent_eq_one (padicPlace q) hwq
        (fun w' hw' => finComponent_padicToFinAdelic_of_ne q x hw'),
      map_mul, ← mul_assoc, hK₀q _ hw hwq]
  | zero => rfl
  | add y₁ y₂ _ _ ih₁ ih₂ => rw [fn_add, fn_add, ih₁, ih₂]
  | smul c' y' _ ih => rw [fn_csmul, fn_csmul, ih]

private theorem heckeAway_self_eq_smul_twist (ℓ : ℕ) [Fact ℓ.Prime] (hM : M ≠ 0) (hℓM : ¬ ℓ ∣ M)
    (hℓq : ℓ ≠ q) (hφg : g.IsAdelicLiftOf Φ)
    {b : ℕ} (hηb : AdmitsModulus ℚ ηc (ratLevel (q ^ b)))
    {c : ℂ} (hT : ModularForm.heckeT 2 ℓ ⇑g = c • ⇑g) :
    heckeAway ℓ (AdelicSpan.self (fnTwist ℚ ηc Φ)) =
      ((ηc (uniformizerIdele ℚ (@padicPlace ℓ ⟨Fact.out⟩)) : ℂ)⁻¹ * c) • AdelicSpan.self (fnTwist ℚ ηc Φ) := by
  refine AdelicSpan.ext _ (AdelicFnCarrier.ext fun z => ?_)
  have hself' : ∀ w, fn (AdelicSpan.self (fnTwist ℚ ηc Φ)) w = fnTwist ℚ ηc Φ w := fun w => by
    rw [fn, AdelicSpan.toFn_self, AdelicFnCarrier.toFn_mk]
  have hself : ∀ w, fn (AdelicSpan.self Φ) w = Φ w := fun w => by
    rw [fn, AdelicSpan.toFn_self, AdelicFnCarrier.toFn_mk]
  show fn (heckeAway ℓ (AdelicSpan.self (fnTwist ℚ ηc Φ))) z
    = fn (((ηc (uniformizerIdele ℚ (@padicPlace ℓ ⟨Fact.out⟩)) : ℂ)⁻¹ * c)
        • AdelicSpan.self (fnTwist ℚ ηc Φ)) z
  rw [fn_heckeAway, fn_csmul, hself']
  have hterm : ∀ i : Fin (ℓ + 1), fn (AdelicSpan.self (fnTwist ℚ ηc Φ)) (z * finEmbed (𝓞 ℚ) ℚ (ρA ℓ i)⁻¹)
      = (ηc z.det : ℂ) * (ηc (uniformizerIdele ℚ (@padicPlace ℓ ⟨Fact.out⟩)) : ℂ)⁻¹
          * Φ (z * finEmbed (𝓞 ℚ) ℚ (ρA ℓ i)⁻¹) := by
    intro i
    have hw : (ηc (finEmbed (𝓞 ℚ) ℚ (ρA ℓ i)⁻¹).det : ℂ)
        = (ηc (uniformizerIdele ℚ (@padicPlace ℓ ⟨Fact.out⟩)) : ℂ)⁻¹ := by
      have hρ : finEmbed (𝓞 ℚ) ℚ (ρA ℓ i)⁻¹ = (padicToAdelic ℓ (ρQ ℓ i))⁻¹ := by
        rw [map_inv, ρA, padicToAdelic_apply]
      rw [hρ, ← map_inv]
      exact eta_det_padicToAdelic_ρQ_inv ηc hηb ℓ hℓq i
    rw [hself', fnTwist_apply, chiDet, map_mul, map_mul, Units.val_mul, hw]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum]
  have hsum0 : ∑ i : Fin (ℓ + 1), Φ (z * finEmbed (𝓞 ℚ) ℚ (ρA ℓ i)⁻¹)
      = fn (heckeAway ℓ (AdelicSpan.self Φ)) z := by
    rw [fn_heckeAway]; exact (Finset.sum_congr rfl fun i _ => (hself _).symm).symm
  have hengine : heckeAway ℓ (AdelicSpan.self Φ) = c • AdelicSpan.self Φ :=
    heckeAway_self_eq_smul ℓ hM hℓM hφg (hφg.levelZero_inv hM) hT
  rw [hsum0, hengine, fn_csmul, hself, fnTwist_apply, chiDet]
  ring

private theorem eta_det_centralGL_padic_eq_one_of_int_unit (hM : M ≠ 0) (hφg : g.IsAdelicLiftOf Φ)
    {y : AdelicSpan (fnTwist ℚ ηc Φ)}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self (fnTwist ℚ ηc Φ)))
    (hy₀ : y ≠ 0) (hcent : ∀ z : ℚ_[q]ˣ, centralGL q z • y = y)
    (t : ℤ_[q]ˣ) :
    (ηc (padicToAdelic q (centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom t))).det : ℂ) = 1 := by
  set zc : ℚ_[q]ˣ := Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom t
  set c : GL (Fin 2) ℚ_[q] := centralGL q zc

  have hcK₀ : padicToFinAdelic q c ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M) := by
    have halgebra : (algebraMap ℤ_[q] ℚ_[q] : ℤ_[q] →+* ℚ_[q]) = PadicInt.Coe.ringHom := rfl
    show padicToFinAdelic q (centralGL q zc) ∈ _
    rw [show zc = Units.map PadicInt.Coe.ringHom.toMonoidHom t from by rw [← halgebra]]
    exact padicToFinAdelic_centralGL_mem_finiteLevelZero q M t

  have hcomm : ∀ x : GL (Fin 2) ℚ_[q], c * x = x * c := fun x =>
    Units.ext (Algebra.commutes (zc : ℚ_[q]) x.val)

  have hscale : ∀ w, fn y (w * padicToAdelic q c)
      = chiDet (𝓞 ℚ) ℚ ηc (padicToAdelic q c) * fn y w := by
    have hK₀ := hφg.levelZero_inv hM
    intro w
    clear hcent hy₀
    induction hy using Submodule.span_induction with
    | mem y' hy' =>
      obtain ⟨x, rfl⟩ := hy'
      rw [fn_padic_smul_self, fn_padic_smul_self, mul_assoc, ← map_mul, hcomm x, map_mul,
        ← mul_assoc, fnTwist_apply, fnTwist_apply]
      have hΦeq : Φ (w * padicToAdelic q x * padicToAdelic q c) = Φ (w * padicToAdelic q x) := by
        rw [show padicToAdelic q c = finEmbed (𝓞 ℚ) ℚ (padicToFinAdelic q c)
          from padicToAdelic_apply q c]
        exact hK₀ _ hcK₀ _
      rw [hΦeq, chiDet, chiDet, chiDet, map_mul, map_mul, Units.val_mul]
      ring
    | zero => simp only [fn_zero, mul_zero]
    | add y₁ y₂ _ _ ih₁ ih₂ => rw [fn_add, fn_add, ih₁, ih₂]; ring
    | smul c' y' _ ih => rw [fn_csmul, fn_csmul, ih]; ring

  have hfixc : ∀ w, fn y (w * padicToAdelic q c) = fn y w := fun w => by
    rw [← fn_padic_smul, hcent zc]

  obtain ⟨w₀, hw₀⟩ : ∃ w, fn y w ≠ 0 := by
    by_contra h; push Not at h
    exact hy₀ (AdelicSpan.ext _ (AdelicFnCarrier.ext fun w => (h w).trans (fn_zero w).symm))

  have heq := (hfixc w₀).symm.trans (hscale w₀)
  have hsc : chiDet (𝓞 ℚ) ℚ ηc (padicToAdelic q c) = 1 :=
    mul_right_cancel₀ hw₀ (heq.symm.trans (one_mul _).symm)
  rw [chiDet] at hsc; exact hsc

end TwistedEngine

private theorem engine_twist {M : ℕ} (hM : M ≠ 0) {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hg : g.IsNormalizedEigenform) (q : ℕ) [hq : Fact q.Prime]
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hη : IsFiniteOrderHeckeChar ℚ η)
    (b : ℕ) (hηb : AdmitsModulus ℚ η (ratLevel (q ^ b)))
    (a : ℕ) (hae : a ≤ M.factorization q)
    (y : AdelicSpan (fnTwist ℚ η Φ))
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self (fnTwist ℚ η Φ)))
    (hy₀ : y ≠ 0)
    (hfix : y ∈ fixedSubmodule (padicK1 q a) (AdelicSpan (fnTwist ℚ η Φ)))
    (hcent : ∀ z : ℚ_[q]ˣ, centralGL q z • y = y) :
    ∃ h₀ : CuspForm (CongruenceSubgroup.Gamma0 (M / q ^ (M.factorization q - a))) 2, h₀ ≠ 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (_ : ¬ ℓ ∣ M) (_ : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M / q ^ (M.factorization q - a)),
        CuspForm.heckeTLin 2 hℓ hℓM' h₀ =
          ((η (uniformizerIdele ℚ (@padicPlace ℓ ⟨hℓ⟩)) : ℂ)⁻¹ * ModularFormClass.qCoeff g ℓ) • h₀ := by
  set M' : ℕ := M / q ^ (M.factorization q - a) with hM'def
  have hM' : M' ≠ 0 := level_lowered_ne_zero hM q a hq.out.ne_zero
  haveI : NeZero M := ⟨hM⟩

  obtain ⟨F, hFspan, hread⟩ := exists_hasReading_of_mem_span_twist η hM hΦg hη hy
  have hFcont : Continuous F := continuous_of_mem_slashSpan hFspan
  have hleft : ∀ γ z, fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z :=
    fun γ z => fn_globalPoints_mul_of_mem_span_twist η hΦg hη hy γ z
  have hright : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M'), ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z :=
    fun u hu z => fn_mul_finEmbed_of_mem_finiteLevelZero_lowered_twist η hM hΦg hηb hae hy hfix hcent hu z
  obtain ⟨ι, _, c, β, hF⟩ := exists_eq_sum_of_mem_slashSpan hFspan
  obtain ⟨h₀, hh₀⟩ := CuspForm.exists_eq_sum_smul_slash_of_forall_slash_eq g c β F hF (by
    rintro γ' ⟨γ, hγ, rfl⟩
    exact slash_eq_of_hasReading hM' hFcont hread hleft hright hγ)
  refine ⟨h₀, ?_, ?_⟩
  · rintro rfl
    apply hy₀
    have hF0 : F = 0 := by rw [← hh₀, CuspForm.coe_zero]
    exact eq_zero_of_hasReading_zero hM' (by simpa [hF0] using hread) hleft hright
  · intro ℓ hℓ hℓM hℓq hℓM'
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hqℓ : q ≠ ℓ := fun hql => hℓq hql.symm
    have hTg : ModularForm.heckeT 2 ℓ (⇑g) = ModularFormClass.qCoeff g ℓ • (⇑g) := by
      have := congrArg (fun f : CuspForm (CongruenceSubgroup.Gamma0 M) 2 => (⇑f : UpperHalfPlane → ℂ))
        (CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul M g hg ℓ hℓ hℓM)
      simpa [CuspForm.coe_heckeTLin_apply, CuspForm.coe_smul] using this
    have hself : heckeAway ℓ (AdelicSpan.self (fnTwist ℚ η Φ))
        = ((η (uniformizerIdele ℚ (@padicPlace ℓ ⟨Fact.out⟩)) : ℂ)⁻¹ * ModularFormClass.qCoeff g ℓ)
            • AdelicSpan.self (fnTwist ℚ η Φ) :=
      heckeAway_self_eq_smul_twist η ℓ hM hℓM hℓq hΦg hηb hTg
    have heig : heckeAway ℓ y
        = ((η (uniformizerIdele ℚ (@padicPlace ℓ ⟨Fact.out⟩)) : ℂ)⁻¹ * ModularFormClass.qCoeff g ℓ) • y :=
      heckeAway_eq_smul_of_mem_span ℓ hqℓ hself hy
    have hTF : ModularForm.heckeT 2 ℓ F
        = ((η (uniformizerIdele ℚ (@padicPlace ℓ ⟨Fact.out⟩)) : ℂ)⁻¹ * ModularFormClass.qCoeff g ℓ) • F :=
      heckeT_reading_eq_smul (N := M') ℓ hFcont hread hleft hright heig
    have h1 : (⇑(CuspForm.heckeTLin 2 hℓ hℓM' h₀) : UpperHalfPlane → ℂ) = ModularForm.heckeT 2 ℓ (⇑h₀) :=
      CuspForm.coe_heckeTLin_apply 2 hℓ hℓM' h₀
    rw [hh₀] at h1
    have h3 : (⇑(((η (uniformizerIdele ℚ (@padicPlace ℓ ⟨hℓ⟩)) : ℂ)⁻¹ * ModularFormClass.qCoeff g ℓ) • h₀)
          : UpperHalfPlane → ℂ)
        = ((η (uniformizerIdele ℚ (@padicPlace ℓ ⟨Fact.out⟩)) : ℂ)⁻¹ * ModularFormClass.qCoeff g ℓ) • F := by
      rw [CuspForm.IsGLPos.coe_smul, hh₀]
    exact CuspForm.ext fun τ => congrFun (h1.trans (hTF.trans h3.symm)) τ

private theorem quadraticity_bridge {M : ℕ} [NeZero M] {q : ℕ} [Fact q.Prime]
    {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hη : IsFiniteOrderHeckeChar ℚ η)
    (b : ℕ) (hηb : AdmitsModulus ℚ η (ratLevel (q ^ b)))
    {y : AdelicSpan (fnTwist ℚ η Φ)}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self (fnTwist ℚ η Φ)))
    (hy₀ : y ≠ 0)
    (hcent : ∀ z : ℚ_[q]ˣ, centralGL q z • y = y)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓq : ℓ ≠ q) :
    (η (uniformizerIdele ℚ (@padicPlace ℓ ⟨hℓ⟩)) : ℂ)⁻¹ = (η (uniformizerIdele ℚ (@padicPlace ℓ ⟨hℓ⟩)) : ℂ) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have _ := hℓM
  have hM : M ≠ 0 := NeZero.ne M
  have hqℓ : ¬ (q : ℕ) ∣ ℓ := fun h => hℓq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) hℓ).mp h).symm

  have hℓu : IsUnit ((ℓ : ℤ_[q])) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes (Fact.out : q.Prime) hℓ).mpr fun h => hℓq h.symm
  set t : ℤ_[q]ˣ := hℓu.unit
  set zc : ℚ_[q]ˣ := Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom t with hzc

  have hα := eta_det_centralGL_padic_eq_one_of_int_unit η hM hΦg hy hy₀ hcent t

  have hsq : (η (Units.map (finIncl (𝓞 ℚ) ℚ)
      (localUnit (𝓞 ℚ) ℚ (padicPlace q) (natUnitAt (padicPlace q) ℓ))) : ℂ) ^ 2 = 1 := by
    rw [← hα, det_padicToAdelic q]

    have hdet2 : (centralGL q zc).det = zc ^ 2 := by
      ext
      change Matrix.det ((algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q])) (zc : ℚ_[q])) = _
      rw [Algebra.algebraMap_eq_smul_one, Matrix.det_smul, Matrix.det_one, mul_one,
        Fintype.card_fin, Units.val_pow_eq_pow_val]
    have htrans : Units.map (padicRingEquiv q).toRingHom.toMonoidHom zc = natUnitAt (padicPlace q) ℓ := by
      ext
      rw [Units.coe_map, coe_natUnitAt]
      change padicRingEquiv q (zc : ℚ_[q]) = _
      have hzcval : (zc : ℚ_[q]) = (ℓ : ℚ_[q]) := by
        rw [hzc, Units.coe_map]
        show algebraMap ℤ_[q] ℚ_[q] (t : ℤ_[q]) = (ℓ : ℚ_[q])
        rw [show (t : ℤ_[q]) = (ℓ : ℤ_[q]) from hℓu.unit_spec, map_natCast]
      rw [hzcval, map_natCast]
    rw [hdet2, map_pow, htrans, map_pow, map_pow, map_pow, Units.val_pow_eq_pow_val]

  have hβ := apply_uniformizerIdele_mul_apply_localUnit_natUnitAt η hη hηb ℓ hℓq
  have hπsq : (η (uniformizerIdele ℚ (@padicPlace ℓ ⟨hℓ⟩)) : ℂ) ^ 2 = 1 := by
    have hinv : η (uniformizerIdele ℚ (padicPlace ℓ)) = (η (Units.map (finIncl (𝓞 ℚ) ℚ)
        (localUnit (𝓞 ℚ) ℚ (padicPlace q) (natUnitAt (padicPlace q) ℓ))))⁻¹ :=
      eq_inv_of_mul_eq_one_left hβ
    calc (η (uniformizerIdele ℚ (padicPlace ℓ)) : ℂ) ^ 2
        = ((η (Units.map (finIncl (𝓞 ℚ) ℚ)
            (localUnit (𝓞 ℚ) ℚ (padicPlace q) (natUnitAt (padicPlace q) ℓ))) : ℂ) ^ 2)⁻¹ := by
          rw [hinv, Units.val_inv_eq_inv_val, inv_pow]
      _ = 1 := by rw [hsq, inv_one]

  rw [sq] at hπsq
  exact (eq_inv_of_mul_eq_one_left hπsq).symm

end TwistEngine

open DescentEngine TwistEngine NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm LocalNewvector HeckeCharacter in
theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNormalizedEigenform)
    (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hη : HeckeCharacter.IsFiniteOrderHeckeChar ℚ η)
    (b : ℕ) (hηb : HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel (q ^ b)))
    (a : ℕ) (hae : a ≤ M.factorization q)
    (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)))
    (hy₀ : y ≠ 0)
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a)
      (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)))
    (hcent : ∀ z : ℚ_[q]ˣ, LocalNewvector.centralGL q z • y = y) :
    ∃ h : CuspForm (CongruenceSubgroup.Gamma0 (M / q ^ (M.factorization q - a))) 2, h.IsNormalizedEigenform ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ≠ q →
        ModularFormClass.qCoeff h ℓ =
          (η (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) * ModularFormClass.qCoeff g ℓ := by
  have hM : M ≠ 0 := NeZero.ne M
  obtain ⟨h₀, h₀ne, heig⟩ := engine_twist hM hg q hΦg η hη b hηb a hae y hy hy₀ hfix hcent
  have hbridge : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ≠ q →
      (η (uniformizerIdele ℚ (@padicPlace ℓ ⟨hℓ⟩)) : ℂ)⁻¹ =
        (η (uniformizerIdele ℚ (@padicPlace ℓ ⟨hℓ⟩)) : ℂ) :=
    fun ℓ hℓ hℓM hℓq => quadraticity_bridge hΦg η hη b hηb hy hy₀ hcent ℓ hℓ hℓM hℓq
  set M' : ℕ := M / q ^ (M.factorization q - a) with hM'def
  have hM' : M' ≠ 0 := level_lowered_ne_zero hM q a (Fact.out : q.Prime).ne_zero
  haveI : NeZero M' := ⟨hM'⟩
  have hdvd : M' ∣ M := level_lowered_dvd M q a
  obtain ⟨h, hh, hcoef⟩ := CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul h₀ne
    (fun ℓ => if hℓ : ℓ.Prime then
        (η (uniformizerIdele ℚ (@padicPlace ℓ ⟨hℓ⟩)) : ℂ)⁻¹ * ModularFormClass.qCoeff g ℓ
      else 0)
    {ℓ | ℓ ∣ M ∨ ℓ = q}
    (fun ℓ hℓ hℓM' hℓS => by
      simp only [Set.mem_setOf_eq, not_or] at hℓS
      simp only [dif_pos hℓ]
      exact heig ℓ hℓ hℓS.1 hℓS.2 hℓM')
  refine ⟨h, hh, fun ℓ hℓ hℓM hℓq => ?_⟩
  have hℓM' : ¬ ℓ ∣ M' := fun hd => hℓM (hd.trans hdvd)
  have hℓS : ℓ ∉ ({ℓ | ℓ ∣ M ∨ ℓ = q} : Set ℕ) := by
    simp only [Set.mem_setOf_eq, not_or]; exact ⟨hℓM, hℓq⟩
  rw [hcoef ℓ hℓ hℓM' hℓS, dif_pos hℓ, hbridge ℓ hℓ hℓM hℓq]

#print axioms solution

end S_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_qCoeff_eq_mul_of_adelicLift_fnTwist_of_mem_span_of_fixed
end P2MW
export P2MW.S_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_qCoeff_eq_mul_of_adelicLift_fnTwist_of_mem_span_of_fixed (solution)
