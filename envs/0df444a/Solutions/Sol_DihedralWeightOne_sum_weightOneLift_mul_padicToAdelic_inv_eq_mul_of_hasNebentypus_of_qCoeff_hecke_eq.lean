-- Prove2me | solution 1 for DihedralWeightOne.sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_of_hasNebentypus_of_qCoeff_hecke_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/b6b6ebff-4beb-5284-b692-894fc892fdca

import Mathlib
import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_DihedralWeightOne_sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_slash_apply_I_mul_det
import Theorems.Thm_DihedralWeightOne_weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift
import Theorems.Thm_AutomorphicForm_ext_of_invariant_of_forall_glFin_eq_one_rat
import Theorems.Thm_CuspForm_qCoeff_heckeTLinOne
import Theorems.Thm_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DihedralWeightOne_sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_of_hasNebentypus_of_qCoeff_hecke_eq

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

open NumberField AdelicDock AutomorphicForm

variable (p : ℕ) [hp : Fact p.Prime]

omit hp in
private theorem σ_apply_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < (g.det : ℝ)) (z : ℂ) :
    UpperHalfPlane.σ g z = z := by
  rw [UpperHalfPlane.σ, if_pos hg]
  rfl

private theorem eq_ρQ_of_coe_eq (ρ : Fin (p + 1) → GL (Fin 2) ℚ_[p])
    (hρ : ∀ i : Fin (p + 1), ((ρ i : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      if (i : ℕ) < p then !![(1 : ℚ_[p]), ((i : ℕ) : ℚ_[p]); 0, (p : ℚ_[p])]
      else !![(p : ℚ_[p]), 0; 0, 1]) (i : Fin (p + 1)) :
    ρ i = ρQ p i := by
  refine Units.ext ?_
  rw [hρ i, coe_ρQ]
  unfold HeckeCosets.repZ
  split_ifs
  · ext a b; fin_cases a <;> fin_cases b <;> simp
  · ext a b; fin_cases a <;> fin_cases b <;> simp

private theorem padicToAdelic_ρQ_inv (i : Fin (p + 1)) :
    padicToAdelic p (ρQ p i)⁻¹ = finEmbed (𝓞 ℚ) ℚ (ρA p i)⁻¹ := by
  rw [map_inv, map_inv, padicToAdelic_apply]
  rfl

private theorem sum_apply_mul_finEmbed_eq {N : ℕ} (hN : N ≠ 0) (hpN : ¬ p ∣ N)
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hlev : ∀ u ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N), ∀ x, Φ (x * finEmbed (𝓞 ℚ) ℚ u) = Φ x)
    {u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N)) (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∑ i : Fin (p + 1), Φ (x * finEmbed (𝓞 ℚ) ℚ u * padicToAdelic p (ρQ p i)⁻¹)
      = ∑ i : Fin (p + 1), Φ (x * padicToAdelic p (ρQ p i)⁻¹) := by
  obtain ⟨σ, hσ⟩ := exists_perm_mul_ρA_inv p hN hpN hu
  simp only [padicToAdelic_ρQ_inv]
  calc ∑ i : Fin (p + 1), Φ (x * finEmbed (𝓞 ℚ) ℚ u * finEmbed (𝓞 ℚ) ℚ (ρA p i)⁻¹)
      = ∑ i : Fin (p + 1), Φ (x * finEmbed (𝓞 ℚ) ℚ (ρA p (σ i))⁻¹) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        obtain ⟨u', hu', h⟩ := hσ i
        rw [mul_assoc, ← map_mul, h, map_mul, ← mul_assoc, hlev u' hu']
    _ = ∑ i : Fin (p + 1), Φ (x * finEmbed (𝓞 ℚ) ℚ (ρA p i)⁻¹) :=
        Equiv.sum_comp σ (fun i => Φ (x * finEmbed (𝓞 ℚ) ℚ (ρA p i)⁻¹))

end DescentEngine

namespace GammaOneHeckeEigen

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Function
open scoped MatrixGroups ModularForm

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ M).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

theorem cusp_periodic (F : CuspForm (Γ₁ℝ M) k) : Periodic (⇑F ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex F (one_mem_strictPeriods M)

theorem cusp_holo (F : CuspForm (Γ₁ℝ M) k) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'

theorem cusp_bdd (F : CuspForm (Γ₁ℝ M) k) : IsBoundedAtImInfty (⇑F : ℍ → ℂ) := by
  haveI : Fact (IsCusp OnePoint.infty (Γ₁ℝ M)) :=
    ⟨(Γ₁ℝ M).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods M)⟩
  exact ModularFormClass.bdd_at_infty F

theorem cusp_ext_of_qCoeff {F G : CuspForm (Γ₁ℝ M) k} (h : ∀ n : ℕ, qCoeff (⇑F) n = qCoeff (⇑G) n) :
    F = G :=
  DFunLike.coe_injective (UpperHalfPlane.eq_of_forall_qCoeff_eq (cusp_periodic F) (cusp_holo F)
    (cusp_bdd F) (cusp_periodic G) (cusp_holo G) (cusp_bdd G) h)

theorem qCoeff_smul (c : ℂ) (F : CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    qCoeff (⇑(c • F)) n = c * qCoeff (⇑F) n := by
  have han : AnalyticAt ℂ (cuspFunction 1 (⇑F)) 0 :=
    analyticAt_cuspFunction_zero one_pos (cusp_periodic F) (cusp_holo F) (cusp_bdd F)
  rw [qCoeff, qCoeff, CuspForm.IsGLPos.coe_smul, qExpansion_smul han c, map_smul, smul_eq_mul]

section NeZero

variable [NeZero M]

omit [NeZero M] in

theorem dirichlet_pow_totient (ε : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    ε (ℓ : ZMod M) ^ Nat.totient M = 1 := by
  rw [← ZMod.coe_unitOfCoprime ℓ hℓ, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient,
    Units.val_one, map_one]

theorem totient_ne_zero : Nat.totient M ≠ 0 := (Nat.totient_pos.2 (NeZero.pos M)).ne'

theorem dirichlet_ne_zero (ε : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ M) :
    ε (ℓ : ZMod M) ≠ 0 := fun h0 => by
  have h := dirichlet_pow_totient ε hℓ
  rw [h0, zero_pow totient_ne_zero] at h
  exact zero_ne_one h

end NeZero

variable {ε : DirichletCharacter ℂ M} {h : CuspForm (Gamma1 M) 1}

theorem hecke_eigen (hε : CuspForm.HasNebentypus ε h) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) {lam : ℂ}
    (hT : ∀ n : ℕ,
      qCoeff (⇑h) (ℓ * n) +
          ε (ℓ : ZMod M) * (ℓ : ℂ) ^ ((1 : ℤ) - 1) * (if ℓ ∣ n then qCoeff (⇑h) (n / ℓ) else 0) =
        lam * qCoeff (⇑h) n) :
    CuspForm.heckeTLinOne 1 hℓ hℓM h = lam • h := by
  refine cusp_ext_of_qCoeff fun n => ?_
  rw [CuspForm.qCoeff_heckeTLinOne 1 hℓ hℓM h n,
    hε.diamondLinOne_apply_eq_smul ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM), qCoeff_smul, qCoeff_smul,
    ← hT n]
  split_ifs <;> ring

theorem inv_smul_heckeU_add_slash_eq [NeZero M] (hε : CuspForm.HasNebentypus ε h) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) {lam : ℂ}
    (hT : ∀ n : ℕ,
      qCoeff (⇑h) (ℓ * n) +
          ε (ℓ : ZMod M) * (ℓ : ℂ) ^ ((1 : ℤ) - 1) * (if ℓ ∣ n then qCoeff (⇑h) (n / ℓ) else 0) =
        lam * qCoeff (⇑h) n) :
    (ε (ℓ : ZMod M))⁻¹ • ModularForm.heckeU 1 ℓ ⇑h + (⇑h) ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix ℓ
      = ((ε (ℓ : ZMod M))⁻¹ * lam) • (⇑h : ℍ → ℂ) := by
  have hcop : Nat.Coprime ℓ M := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM
  have hε0 : ε (ℓ : ZMod M) ≠ 0 := dirichlet_ne_zero ε hcop
  have hfun : ModularForm.heckeU 1 ℓ ⇑h + ε (ℓ : ZMod M) • ((⇑h) ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix ℓ)
      = lam • (⇑h : ℍ → ℂ) := by
    have h1 := congrArg (fun f : CuspForm (Gamma1 M) 1 => (⇑f : ℍ → ℂ)) (hecke_eigen hε hℓ hℓM hT)
    rw [CuspForm.coe_heckeTLinOne_apply, hε.diamondLinOne_apply_eq_smul hcop, CuspForm.IsGLPos.coe_smul,
      CuspForm.IsGLPos.coe_smul, ModularForm.smul_slash, σ_heckeDiagMatrix, ContinuousAlgEquiv.refl_apply] at h1
    exact h1
  rw [mul_smul, ← hfun, smul_add, ← mul_smul, inv_mul_cancel₀ hε0, one_smul]

end GammaOneHeckeEigen

open DescentEngine NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm DihedralWeightOne in
open scoped ModularForm in
theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
    (hε : CuspForm.HasNebentypus ε h)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (ρ : Fin (ℓ + 1) → GL (Fin 2) ℚ_[ℓ])
    (hρ : ∀ i : Fin (ℓ + 1), ((ρ i : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) =
      if (i : ℕ) < ℓ then !![(1 : ℚ_[ℓ]), ((i : ℕ) : ℚ_[ℓ]); 0, (ℓ : ℚ_[ℓ])]
      else !![(ℓ : ℚ_[ℓ]), 0; 0, 1])
    (lam : ℂ)
    (hT : ∀ n : ℕ,
      ModularFormClass.qCoeff h (ℓ * n) +
          ε (ℓ : ZMod M) * (ℓ : ℂ) ^ ((1 : ℤ) - 1) *
            (if ℓ ∣ n then ModularFormClass.qCoeff h (n / ℓ) else 0) =
        lam * ModularFormClass.qCoeff h n)
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∑ i : Fin (ℓ + 1), weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h) (x * AdelicDock.padicToAdelic ℓ (ρ i)⁻¹) =
      (ε (ℓ : ZMod M))⁻¹ * (ℓ : ℂ) * lam * weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h) x := by
  have hM : M ≠ 0 := NeZero.ne M
  have hℓ : ℓ.Prime := Fact.out
  have hρ' : ∀ i, ρ i = ρQ ℓ i := eq_ρQ_of_coe_eq ℓ ρ hρ
  obtain ⟨hleft, hlev, harch⟩ :=
    DihedralWeightOne.weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift hM (⇑h)
      (fun γ hγ => SlashInvariantForm.slash_action_eqn h (γ : GL (Fin 2) ℝ) ⟨γ, hγ, rfl⟩)
  have key : (fun z : AdelicGL2 (𝓞 ℚ) ℚ =>
        ∑ i : Fin (ℓ + 1), weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h) (z * padicToAdelic ℓ (ρ i)⁻¹))
      = fun z => (ε (ℓ : ZMod M))⁻¹ * (ℓ : ℂ) * lam * weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h) z := by
    refine AutomorphicForm.ext_of_invariant_of_forall_glFin_eq_one_rat (ratLevel_ne_bot hM)
      ?_ ?_ ?_ ?_ ?_
    · intro γ z
      simp only [mul_assoc, hleft]
    · intro γ z
      simp only [hleft]
    · intro u hu z
      simp only [hρ']
      exact sum_apply_mul_finEmbed_eq ℓ hM hℓM hlev hu z
    · intro u hu z
      simp only [hlev u hu]
    · intro X hX hpos
      have hdet : 0 < ((LanglandsTunnell.ratArchGL2 X).det : ℝ) := (Matrix.mem_glpos _).mp hpos
      rw [DihedralWeightOne.sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_slash_apply_I_mul_det hε ℓ hℓM ρ hρ
          hX hpos,
        GammaOneHeckeEigen.inv_smul_heckeU_add_slash_eq hε hℓ hℓM hT, ModularForm.smul_slash,
        Pi.smul_apply, σ_apply_of_det_pos hdet, smul_eq_mul, harch X hX hpos]
      unfold DihedralWeightOne.weightOneArchLift
      simp only [zpow_one]
      ring
  exact congrFun key x

end S_DihedralWeightOne_sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_of_hasNebentypus_of_qCoeff_hecke_eq
end P2MW
export P2MW.S_DihedralWeightOne_sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_of_hasNebentypus_of_qCoeff_hecke_eq (solution)
