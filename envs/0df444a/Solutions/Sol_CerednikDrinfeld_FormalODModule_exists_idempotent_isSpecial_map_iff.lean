-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_idempotent_isSpecial_map_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c61c017f-b37f-536a-8ca3-04ec68439ecd

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_lieZero_lieOne_map_and_eq_span_image
import Theorems.Thm_Module_Invertible_of_projective_of_forall_finrank_eq_one
import Theorems.Thm_Matrix_finrank_ker_eq_one_and_iff_det_eq_zero_and_of_mul_eq_zero
import Theorems.Thm_Submodule_finrank_baseChange_eq_finrank_of_isCompl_of_eq_span_image
import Theorems.Thm_WittVector_exists_ringHom_padicInt_and_root_of_forall_sq_sub_mul_add_ne_zero
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_lieZero_lieOne_and_eq_ker_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_idempotent_isSpecial_map_iff

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

namespace SpecialClopenSol

section MatrixAlg

variable {S : Type} [CommRing S]

theorem sub_smul_one_mul_sub_smul_one_eq_zero {m : Type} [Fintype m] [DecidableEq m]
    (T : Matrix m m S) (a b t n : S) (hT : T * T = t • T - n • (1 : Matrix m m S))
    (hab : a + b = t) (habn : a * b = n) :
    (T - a • (1 : Matrix m m S)) * (T - b • (1 : Matrix m m S)) = 0 := by
  have h1 : (T - a • (1 : Matrix m m S)) * (T - b • (1 : Matrix m m S)) =
      T * T - (a + b) • T + (a * b) • (1 : Matrix m m S) := by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
    module
  rw [h1, hT, hab, habn]
  module

theorem smul_one_mulVec {m : Type} [Fintype m] [DecidableEq m] (s : S) (v : m → S) :
    (s • (1 : Matrix m m S)).mulVec v = s • v := by
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]

theorem sub_smul_one_mulVec {m : Type} [Fintype m] [DecidableEq m] (T : Matrix m m S) (s : S) (v : m → S) :
    (T - s • (1 : Matrix m m S)).mulVec v = T.mulVec v - s • v := by
  rw [Matrix.sub_mulVec, smul_one_mulVec]

theorem isCompl_ker_of_mul_eq_zero {m : Type} [Fintype m] [DecidableEq m]
    (T : Matrix m m S) (a b : S)
    (h₁ : (T - a • (1 : Matrix m m S)) * (T - b • (1 : Matrix m m S)) = 0)
    (h₂ : (T - b • (1 : Matrix m m S)) * (T - a • (1 : Matrix m m S)) = 0)
    (hu : IsUnit (a - b)) :
    IsCompl (LinearMap.ker (Matrix.mulVecLin (T - a • (1 : Matrix m m S))))
      (LinearMap.ker (Matrix.mulVecLin (T - b • (1 : Matrix m m S)))) := by
  obtain ⟨w, hw⟩ : ∃ w : S, w * (a - b) = 1 := hu.exists_left_inv
  refine IsCompl.of_eq ?_ ?_
  · rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      sub_smul_one_mulVec, sub_smul_one_mulVec, sub_eq_zero, sub_eq_zero] at hv
    have h3 : (a - b) • v = 0 := by rw [sub_smul, ← hv.1, ← hv.2, sub_self]
    calc v = (w * (a - b)) • v := by rw [hw, one_smul]
      _ = 0 := by rw [← smul_smul, h3, smul_zero]
  · rw [Submodule.eq_top_iff']
    intro v
    rw [Submodule.mem_sup]
    refine ⟨w • (T - b • (1 : Matrix m m S)).mulVec v, ?_, w • (a • (1 : Matrix m m S) - T).mulVec v, ?_, ?_⟩
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h₁,
        Matrix.zero_mulVec, smul_zero]
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
      have : (T - b • (1 : Matrix m m S)) * (a • (1 : Matrix m m S) - T) =
          -((T - b • (1 : Matrix m m S)) * (T - a • (1 : Matrix m m S))) := by
        rw [← mul_neg, neg_sub]
      rw [this, h₂, neg_zero, Matrix.zero_mulVec, smul_zero]
    · rw [← smul_add, ← Matrix.add_mulVec, sub_add_sub_cancel', Matrix.sub_mulVec, smul_one_mulVec,
        smul_one_mulVec, ← sub_smul, smul_smul, hw, one_smul]

end MatrixAlg

section Eigen

variable (p : ℕ) [Fact p.Prime]

theorem intCast_eq_smul_one {S : Type} [CommRing S] {m : Type} [Fintype m] [DecidableEq m] (z : ℤ) :
    ((z : Matrix m m S)) = (z : S) • (1 : Matrix m m S) := by
  rw [← map_intCast (algebraMap S (Matrix m m S)) z, Algebra.algebraMap_eq_smul_one]

theorem natCast_eq_smul_one {S : Type} [CommRing S] {m : Type} [Fintype m] [DecidableEq m] (z : ℕ) :
    ((z : Matrix m m S)) = (z : S) • (1 : Matrix m m S) := by
  rw [← map_natCast (algebraMap S (Matrix m m S)) z, Algebra.algebraMap_eq_smul_one]

theorem eigenSplit (ω : Zp2 p) (t n : ℤ)
    (hirr : ∀ x : ZMod p, x ^ 2 - (t : ZMod p) * x + (n : ZMod p) ≠ 0)
    (hω : ω * ω = (t : Zp2 p) * ω - (n : Zp2 p)) (hσ : WittVector.frobenius ω = (t : Zp2 p) - ω)
    (hdense : ∀ (k : ℕ) (x : Zp2 p), ∃ c d : ℤ, x - ((c : Zp2 p) + (d : Zp2 p) * ω) ∈ Ideal.span {((p : Zp2 p)) ^ k})
    {S : Type} [CommRing S] (hS : IsNilpotent (p : S)) (j : Zp2 p →+* S) (Y : FormalODModule p S) :
    IsUnit (j ω - j (WittVector.frobenius ω)) ∧
    (MvFormalGroup.linearPart (Y.act ω) - j ω • (1 : Matrix (Fin 2) (Fin 2) S)) *
        (MvFormalGroup.linearPart (Y.act ω) - j (WittVector.frobenius ω) • (1 : Matrix (Fin 2) (Fin 2) S)) = 0 ∧
    Y.lieZero j = LinearMap.ker (Matrix.mulVecLin
        (MvFormalGroup.linearPart (Y.act ω) - j ω • (1 : Matrix (Fin 2) (Fin 2) S))) ∧
    Y.lieOne j = LinearMap.ker (Matrix.mulVecLin
        (MvFormalGroup.linearPart (Y.act ω) - j (WittVector.frobenius ω) • (1 : Matrix (Fin 2) (Fin 2) S))) ∧
    IsCompl (Y.lieZero j) (Y.lieOne j) :=
  CerednikDrinfeld.FormalODModule.isCompl_lieZero_lieOne_and_eq_ker_of_isNilpotent p ω t n hirr hω hσ hdense hS j Y

end Eigen

section Natural

theorem linearPart_seriesMap {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') (φ : Series S) :
    MvFormalGroup.linearPart (Series.map f φ) = (MvFormalGroup.linearPart φ).map f := by
  ext i k
  simp only [MvFormalGroup.linearPart, Series.map, Matrix.of_apply, Matrix.map_apply, MvPowerSeries.coeff_map]

theorem map_sub_smul_one {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') {m : Type} [Fintype m]
    [DecidableEq m] (T : Matrix m m S) (a : S) :
    (T - a • (1 : Matrix m m S)).map f = T.map f - f a • (1 : Matrix m m S') := by
  ext i k
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, map_sub, smul_eq_mul,
    map_mul]
  split_ifs <;> simp

theorem det_map_sub_smul_one {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S')
    (T : Matrix (Fin 2) (Fin 2) S) (a : S) :
    (T.map f - f a • (1 : Matrix (Fin 2) (Fin 2) S')).det = f (T - a • (1 : Matrix (Fin 2) (Fin 2) S)).det := by
  rw [← map_sub_smul_one, RingHom.map_det]
  rfl

end Natural

section IdemNil

variable {S : Type} [CommRing S]

theorem eq_zero_of_isIdempotentElem_of_isNilpotent {d : S} (hd : IsIdempotentElem d) (hn : IsNilpotent d) :
    d = 0 := by
  obtain ⟨k, hk⟩ := hn
  rw [← hd.pow_succ_eq k, pow_succ, hk, zero_mul]

theorem isNilpotent_iff_of_isUnit_mul {u x : S} (hu : IsUnit u) :
    IsNilpotent (u * x) ↔ IsNilpotent x := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have : x = v * (u * x) := by rw [← mul_assoc, hv, one_mul]
    rw [this]
    exact Commute.isNilpotent_mul_left (Commute.all _ _) h
  · intro h
    exact Commute.isNilpotent_mul_left (Commute.all _ _) h

theorem one_sub_mul_one_sub_eq_one_iff {x y : S} (hx : IsIdempotentElem x) (hy : IsIdempotentElem y) :
    (1 - x) * (1 - y) = 1 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hux : IsUnit (1 - x) := isUnit_iff_exists_inv.mpr ⟨_, h⟩
    have huy : IsUnit (1 - y) := isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact h⟩
    have h1 := (IsIdempotentElem.iff_eq_one_of_isUnit hux).mp hx.one_sub
    have h2 := (IsIdempotentElem.iff_eq_one_of_isUnit huy).mp hy.one_sub
    exact ⟨by simpa using h1, by simpa using h2⟩
  · rintro ⟨rfl, rfl⟩
    simp

theorem isIdempotentElem_det {m : Type} [Fintype m] [DecidableEq m] {N : Matrix m m S} (hN : N * N = N) :
    IsIdempotentElem N.det := by
  show N.det * N.det = N.det
  rw [← Matrix.det_mul, hN]

theorem sub_smul_one_mul_comm {m : Type} [Fintype m] [DecidableEq m] (T : Matrix m m S) (a b : S) :
    (T - a • (1 : Matrix m m S)) * (T - b • (1 : Matrix m m S)) =
      (T - b • (1 : Matrix m m S)) * (T - a • (1 : Matrix m m S)) := by
  rw [sub_mul, mul_sub, mul_sub, sub_mul, mul_sub, mul_sub]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  rw [mul_comm a b]
  abel

theorem idem_of_mul_eq_zero {m : Type} [Fintype m] [DecidableEq m] (T : Matrix m m S) (a b w : S)
    (h : (T - a • (1 : Matrix m m S)) * (T - b • (1 : Matrix m m S)) = 0) (hw : w * (a - b) = 1) :
    (w • (T - b • (1 : Matrix m m S))) * (w • (T - b • (1 : Matrix m m S))) =
      w • (T - b • (1 : Matrix m m S)) := by
  have hsq : (T - b • (1 : Matrix m m S)) * (T - b • (1 : Matrix m m S)) =
      (a - b) • (T - b • (1 : Matrix m m S)) := by
    have : T - b • (1 : Matrix m m S) = (T - a • (1 : Matrix m m S)) + (a - b) • (1 : Matrix m m S) := by
      rw [sub_smul]; abel
    have h2 : (T - b • (1 : Matrix m m S)) * (T - b • (1 : Matrix m m S)) =
        ((T - a • (1 : Matrix m m S)) + (a - b) • (1 : Matrix m m S)) * (T - b • (1 : Matrix m m S)) := by
      rw [← this]
    rw [h2, add_mul, h, zero_add, smul_mul_assoc, one_mul]
  rw [smul_mul_assoc, mul_smul_comm, hsq, smul_smul, smul_smul, mul_assoc, hw, mul_one]

end IdemNil

section Core

variable (p : ℕ) [Fact p.Prime]

theorem finite_and_projective_of_isCompl {S : Type} [CommRing S] (L₀ L₁ : Submodule S (Fin 2 → S))
    (h : IsCompl L₀ L₁) : Module.Finite S ↥L₀ ∧ Module.Projective S ↥L₀ := by
  have hcomp : (Submodule.projectionOnto L₀ L₁ h) ∘ₗ L₀.subtype = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply]
    exact Submodule.projectionOnto_apply_left h x
  have hsurj : Function.Surjective (Submodule.projectionOnto L₀ L₁ h) :=
    fun x => ⟨(x : Fin 2 → S), Submodule.projectionOnto_apply_left h x⟩
  exact ⟨Module.Finite.of_surjective _ hsurj, Module.Projective.of_split L₀.subtype _ hcomp⟩

theorem core (ω : Zp2 p) (t n : ℤ)
    (hirr : ∀ x : ZMod p, x ^ 2 - (t : ZMod p) * x + (n : ZMod p) ≠ 0)
    (hω : ω * ω = (t : Zp2 p) * ω - (n : Zp2 p)) (hσ : WittVector.frobenius ω = (t : Zp2 p) - ω)
    (hdense : ∀ (k : ℕ) (x : Zp2 p), ∃ c d : ℤ, x - ((c : Zp2 p) + (d : Zp2 p) * ω) ∈ Ideal.span {((p : Zp2 p)) ^ k})
    {S : Type} [CommRing S] (hS : IsNilpotent (p : S)) (j : Zp2 p →+* S) (Y : FormalODModule p S) :
    Y.IsSpecial j ↔
      IsNilpotent (MvFormalGroup.linearPart (Y.act ω) - j ω • (1 : Matrix (Fin 2) (Fin 2) S)).det ∧
      IsNilpotent (MvFormalGroup.linearPart (Y.act ω) -
        j (WittVector.frobenius ω) • (1 : Matrix (Fin 2) (Fin 2) S)).det := by
  obtain ⟨hu, hprod, hZero, hOne, hcompl⟩ := eigenSplit p ω t n hirr hω hσ hdense hS j Y

  have field_case : ∀ (K : Type) [Field K] [Algebra S K],
      (Module.finrank K (K ⊗[S] ↥(Y.lieZero j)) = 1 ∧ Module.finrank K (K ⊗[S] ↥(Y.lieOne j)) = 1) ↔
      (algebraMap S K (MvFormalGroup.linearPart (Y.act ω) - j ω • (1 : Matrix (Fin 2) (Fin 2) S)).det = 0 ∧
       algebraMap S K (MvFormalGroup.linearPart (Y.act ω) -
        j (WittVector.frobenius ω) • (1 : Matrix (Fin 2) (Fin 2) S)).det = 0) := by
    intro K _ _
    have hK : IsNilpotent (p : K) := by
      have := hS.map (algebraMap S K)
      rwa [map_natCast] at this
    obtain ⟨hu', hprod', hZero', hOne', hcompl'⟩ :=
      eigenSplit p ω t n hirr hω hσ hdense hK ((algebraMap S K).comp j) (Y.map (algebraMap S K))
    obtain ⟨-, hspan0, hspan1⟩ :=
      CerednikDrinfeld.FormalODModule.isCompl_lieZero_lieOne_map_and_eq_span_image p j Y hcompl (algebraMap S K)
    have hT' : MvFormalGroup.linearPart ((Y.map (algebraMap S K)).act ω) =
        (MvFormalGroup.linearPart (Y.act ω)).map (algebraMap S K) := by
      rw [FormalODModule.map_act]
      exact linearPart_seriesMap (algebraMap S K) (Y.act ω)
    simp only [RingHom.coe_comp, Function.comp_apply, hT', ← map_sub_smul_one] at hprod' hZero' hOne' hu'

    obtain ⟨hc0, hc1⟩ := Submodule.finrank_baseChange_eq_finrank_of_isCompl_of_eq_span_image
      (Y.lieZero j) (Y.lieOne j) hcompl _ _ hcompl' hspan0 hspan1
    rw [hc0, hc1, hZero', hOne', map_sub_smul_one, map_sub_smul_one]

    have hab' : algebraMap S K (j ω) ≠ algebraMap S K (j (WittVector.frobenius ω)) := by
      intro heq
      rw [heq, sub_self] at hu'
      exact not_isUnit_zero hu'
    rw [map_sub_smul_one, map_sub_smul_one] at hprod'
    rw [Matrix.finrank_ker_eq_one_and_iff_det_eq_zero_and_of_mul_eq_zero _ _ _ hprod' hab',
      det_map_sub_smul_one, det_map_sub_smul_one]
  constructor
  · rintro ⟨-, hinv0, hinv1⟩
    haveI := hinv0; haveI := hinv1
    rw [nilpotent_iff_mem_prime, nilpotent_iff_mem_prime]
    have key : ∀ J : Ideal S, J.IsPrime →
        (MvFormalGroup.linearPart (Y.act ω) - j ω • (1 : Matrix (Fin 2) (Fin 2) S)).det ∈ J ∧
        (MvFormalGroup.linearPart (Y.act ω) -
          j (WittVector.frobenius ω) • (1 : Matrix (Fin 2) (Fin 2) S)).det ∈ J := by
      intro J hJ
      haveI := hJ
      have h1 : Module.finrank J.ResidueField (J.ResidueField ⊗[S] ↥(Y.lieZero j)) = 1 :=
        Module.Invertible.finrank_eq_one _ _
      have h2 : Module.finrank J.ResidueField (J.ResidueField ⊗[S] ↥(Y.lieOne j)) = 1 :=
        Module.Invertible.finrank_eq_one _ _
      obtain ⟨e1, e2⟩ := (field_case J.ResidueField).mp ⟨h1, h2⟩
      exact ⟨Ideal.algebraMap_residueField_eq_zero.mp e1, Ideal.algebraMap_residueField_eq_zero.mp e2⟩
    exact ⟨fun J hJ => (key J hJ).1, fun J hJ => (key J hJ).2⟩
  · rintro ⟨hna, hnb⟩
    obtain ⟨hfin0, hproj0⟩ := finite_and_projective_of_isCompl (Y.lieZero j) (Y.lieOne j) hcompl
    obtain ⟨hfin1, hproj1⟩ := finite_and_projective_of_isCompl (Y.lieOne j) (Y.lieZero j) hcompl.symm
    have hfield : ∀ (K : Type) [Field K] [Algebra S K],
        Module.finrank K (K ⊗[S] ↥(Y.lieZero j)) = 1 ∧ Module.finrank K (K ⊗[S] ↥(Y.lieOne j)) = 1 := by
      intro K _ _
      apply (field_case K).mpr
      exact ⟨(hna.map (algebraMap S K)).eq_zero, (hnb.map (algebraMap S K)).eq_zero⟩
    refine ⟨hcompl, ?_, ?_⟩
    · haveI := hfin0; haveI := hproj0
      exact Module.Invertible.of_projective_of_forall_finrank_eq_one _ fun K _ _ => (hfield K).1
    · haveI := hfin1; haveI := hproj1
      exact Module.Invertible.of_projective_of_forall_finrank_eq_one _ fun K _ _ => (hfield K).2

end Core

section Quad

theorem zmod_two_quad : ∀ x : ZMod 2, x ^ 2 - (1 : ZMod 2) * x + (1 : ZMod 2) ≠ 0 := by decide

theorem exists_irreducible_quadratic (p : ℕ) [hp : Fact p.Prime] :
    ∃ t n : ℤ, ∀ x : ZMod p, x ^ 2 - (t : ZMod p) * x + (n : ZMod p) ≠ 0 := by
  by_cases h2 : p = 2
  · subst h2
    refine ⟨1, 1, fun x => ?_⟩
    have := zmod_two_quad x
    push_cast
    exact this
  · have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact h2
    obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare hchar
    obtain ⟨n₀, rfl⟩ := ZMod.intCast_surjective c
    refine ⟨0, -n₀, fun x hx => hc ⟨x, ?_⟩⟩
    push_cast at hx
    linear_combination (-1 : ZMod p) * hx

end Quad

end SpecialClopenSol

open SpecialClopenSol in
theorem solution
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (hS : IsNilpotent (p : S))
    (j : Zp2 p →+* S) (Y : FormalODModule p S) :
    ∃ e : S, IsIdempotentElem e ∧
      ∀ (S' : Type) [CommRing S'] (f : S →+* S'), (Y.map f).IsSpecial (f.comp j) ↔ f e = 1 := by
  obtain ⟨t, n, hirr⟩ := exists_irreducible_quadratic p
  obtain ⟨ι, ω, -, hω, hσ, -, hdense⟩ :=
    WittVector.exists_ringHom_padicInt_and_root_of_forall_sq_sub_mul_add_ne_zero p t n hirr
  obtain ⟨hu, hprod, -, -, -⟩ := eigenSplit p ω t n hirr hω hσ hdense hS j Y
  set T : Matrix (Fin 2) (Fin 2) S := MvFormalGroup.linearPart (Y.act ω) with hT_def
  set a : S := j ω with ha_def
  set b : S := j (WittVector.frobenius ω) with hb_def
  obtain ⟨w, hw⟩ : ∃ w : S, w * (a - b) = 1 := hu.exists_left_inv
  have hw' : (-w) * (b - a) = 1 := by rw [← hw]; ring

  have hNb : (w • (T - b • (1 : Matrix (Fin 2) (Fin 2) S))) * (w • (T - b • (1 : Matrix (Fin 2) (Fin 2) S))) =
      w • (T - b • (1 : Matrix (Fin 2) (Fin 2) S)) := idem_of_mul_eq_zero T a b w hprod hw
  have hNa : ((-w) • (T - a • (1 : Matrix (Fin 2) (Fin 2) S))) * ((-w) • (T - a • (1 : Matrix (Fin 2) (Fin 2) S))) =
      (-w) • (T - a • (1 : Matrix (Fin 2) (Fin 2) S)) :=
    idem_of_mul_eq_zero T b a (-w) (by rw [← sub_smul_one_mul_comm]; exact hprod) hw'
  set da : S := ((-w) • (T - a • (1 : Matrix (Fin 2) (Fin 2) S))).det with hda_def
  set db : S := (w • (T - b • (1 : Matrix (Fin 2) (Fin 2) S))).det with hdb_def
  have hda_idem : IsIdempotentElem da := isIdempotentElem_det hNa
  have hdb_idem : IsIdempotentElem db := isIdempotentElem_det hNb
  have hda : da = w ^ 2 * (T - a • (1 : Matrix (Fin 2) (Fin 2) S)).det := by
    rw [hda_def, Matrix.det_smul, Fintype.card_fin]; ring
  have hdb : db = w ^ 2 * (T - b • (1 : Matrix (Fin 2) (Fin 2) S)).det := by
    rw [hdb_def, Matrix.det_smul, Fintype.card_fin]
  refine ⟨(1 - da) * (1 - db), hda_idem.one_sub.mul hdb_idem.one_sub, ?_⟩
  intro S' _ f
  have hS' : IsNilpotent (p : S') := by
    have := hS.map f
    rwa [map_natCast] at this
  have hcore := core p ω t n hirr hω hσ hdense hS' (f.comp j) (Y.map f)
  have hT' : MvFormalGroup.linearPart ((Y.map f).act ω) = T.map f := by
    rw [FormalODModule.map_act]
    exact linearPart_seriesMap f (Y.act ω)
  simp only [RingHom.coe_comp, Function.comp_apply, hT'] at hcore
  rw [hcore, det_map_sub_smul_one, det_map_sub_smul_one]
  have hwf : IsUnit (f w ^ 2) := (IsUnit.map f (isUnit_iff_exists_inv.mpr ⟨_, hw⟩)).pow 2
  rw [← isNilpotent_iff_of_isUnit_mul hwf (x := f (T - a • (1 : Matrix (Fin 2) (Fin 2) S)).det),
    ← isNilpotent_iff_of_isUnit_mul hwf (x := f (T - b • (1 : Matrix (Fin 2) (Fin 2) S)).det)]
  have e1 : f w ^ 2 * f (T - a • (1 : Matrix (Fin 2) (Fin 2) S)).det = f da := by
    rw [hda, map_mul, map_pow]
  have e2 : f w ^ 2 * f (T - b • (1 : Matrix (Fin 2) (Fin 2) S)).det = f db := by
    rw [hdb, map_mul, map_pow]
  rw [e1, e2, map_mul, map_sub, map_sub, map_one,
    one_sub_mul_one_sub_eq_one_iff (hda_idem.map f) (hdb_idem.map f)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨eq_zero_of_isIdempotentElem_of_isNilpotent (hda_idem.map f) h1,
      eq_zero_of_isIdempotentElem_of_isNilpotent (hdb_idem.map f) h2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    exact ⟨IsNilpotent.zero, IsNilpotent.zero⟩

end S_CerednikDrinfeld_FormalODModule_exists_idempotent_isSpecial_map_iff
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_idempotent_isSpecial_map_iff (solution)
