-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.isCompl_lieZero_lieOne_and_eq_ker_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/53f88fbf-4590-5b8f-80a9-4dd1a9953a69

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_isCompl_lieZero_lieOne_and_eq_ker_of_isNilpotent

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

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

section Disc

theorem zmod_two_disc_ne_zero :
    ∀ τ ν : ZMod 2, (∀ x : ZMod 2, x ^ 2 - τ * x + ν ≠ 0) → τ ^ 2 - 4 * ν ≠ 0 := by decide

theorem isUnit_intCast_disc (p : ℕ) [hp : Fact p.Prime] (t n : ℤ)
    (hirr : ∀ x : ZMod p, x ^ 2 - (t : ZMod p) * x + (n : ZMod p) ≠ 0)
    {S : Type} [CommRing S] (hS : IsNilpotent (p : S)) :
    IsUnit ((t ^ 2 - 4 * n : ℤ) : S) := by

  have hΔ : ((t ^ 2 - 4 * n : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have h0' : (t : ZMod p) ^ 2 - 4 * (n : ZMod p) = 0 := by push_cast at h0; exact h0
    by_cases h2 : p = 2
    · subst h2
      exact zmod_two_disc_ne_zero _ _ hirr h0'
    · have h2u : (2 : ZMod p) ≠ 0 := by
        intro h
        have hd : (p : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp (by exact_mod_cast h)
        have hp2 : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hd
        have := hp.out.two_le
        exact h2 (by omega)
      obtain ⟨i, hi⟩ : ∃ i : ZMod p, i * 2 = 1 := ⟨(2 : ZMod p)⁻¹, inv_mul_cancel₀ h2u⟩
      have h4 : (4 : ZMod p) ≠ 0 := by
        have : (4 : ZMod p) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2u h2u
      have hx : (4 : ZMod p) * (((t : ZMod p) * i) ^ 2 - (t : ZMod p) * ((t : ZMod p) * i) + (n : ZMod p)) = 0 := by
        linear_combination ((t : ZMod p) ^ 2 * (i * 2 - 1)) * hi + (-1 : ZMod p) * h0'
      exact hirr _ ((mul_eq_zero.mp hx).resolve_left h4)

  set Δ : ℤ := t ^ 2 - 4 * n with hΔ_def
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  obtain ⟨w, hw⟩ : ∃ w : ZMod p, (Δ : ZMod p) * w = 1 := ⟨_, mul_inv_cancel₀ hΔ⟩
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective w
  have hdvd : (p : ℤ) ∣ Δ * m - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_mul, Int.cast_one, sub_eq_zero]
    exact hw
  obtain ⟨k, hk⟩ := hdvd
  have hS' : IsNilpotent ((p : S) * (k : S)) := Commute.isNilpotent_mul_right (Commute.all _ _) hS
  have hcast : (Δ : S) * (m : S) = 1 + (p : S) * (k : S) := by
    have h := congrArg (fun z : ℤ => (z : S)) hk
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, Int.cast_natCast] at h
    linear_combination h
  have hunit : IsUnit ((Δ : S) * (m : S)) := by rw [hcast]; exact hS'.isUnit_one_add
  exact isUnit_of_mul_isUnit_left hunit

end Disc

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
    IsCompl (Y.lieZero j) (Y.lieOne j) := by

  let ℓ : Zp2 p →+* Matrix (Fin 2) (Fin 2) S := (MvFormalGroup.linearPartHom Y.F).comp Y.actRingHom
  have hℓ : ∀ c, ℓ c = MvFormalGroup.linearPart (Y.act c) := fun c => by
    show MvFormalGroup.linearPartHom Y.F (Y.actRingHom c) = _
    rw [MvFormalGroup.linearPartHom_apply, FormalODModule.actRingHom_apply, FormalODModule.actEnd_toPowerSeries]
  set T : Matrix (Fin 2) (Fin 2) S := MvFormalGroup.linearPart (Y.act ω) with hT_def
  set a : S := j ω with ha_def
  set b : S := j (WittVector.frobenius ω) with hb_def
  have hTℓ : ℓ ω = T := hℓ ω

  have hb : b = (t : S) - a := by rw [hb_def, hσ, map_sub, map_intCast]
  have ha2 : a * a = (t : S) * a - (n : S) := by
    have := congrArg j hω
    rw [map_mul, map_sub, map_mul, map_intCast, map_intCast] at this
    exact this
  have hab : a + b = (t : S) := by rw [hb]; abel
  have habn : a * b = (n : S) := by rw [hb, mul_sub, ha2]; ring
  have hT2 : T * T = (t : S) • T - (n : S) • (1 : Matrix (Fin 2) (Fin 2) S) := by
    have := congrArg ℓ hω
    rw [map_mul, map_sub, map_mul, map_intCast, map_intCast, hTℓ, intCast_eq_smul_one, intCast_eq_smul_one,
      smul_mul_assoc, one_mul] at this
    exact this
  have hprod₁ := sub_smul_one_mul_sub_smul_one_eq_zero T a b (t : S) (n : S) hT2 hab habn
  have hprod₂ := sub_smul_one_mul_sub_smul_one_eq_zero T b a (t : S) (n : S) hT2 (by rw [add_comm, hab])
    (by rw [mul_comm, habn])

  have hu : IsUnit (a - b) := by
    have hsq : (a - b) ^ 2 = ((t ^ 2 - 4 * n : ℤ) : S) := by
      rw [hb]; push_cast; linear_combination (4 : S) * ha2
    have := isUnit_intCast_disc p t n hirr hS
    rw [← hsq] at this
    exact (isUnit_pow_iff two_ne_zero).mp this

  obtain ⟨N, hN⟩ := hS
  have hℓpN : ℓ ((p : Zp2 p) ^ N) = 0 := by
    rw [map_pow, map_natCast, natCast_eq_smul_one, smul_pow, one_pow, hN, zero_smul]
  have hjpN : j ((p : Zp2 p) ^ N) = 0 := by rw [map_pow, map_natCast, hN]

  have key : ∀ c : Zp2 p, ∃ m m' : ℤ,
      ℓ c = (m : S) • (1 : Matrix (Fin 2) (Fin 2) S) + (m' : S) • T ∧
      j c = (m : S) + (m' : S) * a ∧ j (WittVector.frobenius c) = (m : S) + (m' : S) * b := by
    intro c
    obtain ⟨m, m', hmm⟩ := hdense N c
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmm
    have hc : c = (m : Zp2 p) + (m' : Zp2 p) * ω + y * (p : Zp2 p) ^ N := by rw [hy]; abel
    refine ⟨m, m', ?_, ?_, ?_⟩
    · rw [hc, map_add, map_add, map_mul, map_mul, hℓpN, mul_zero, add_zero, map_intCast, map_intCast, hTℓ,
        intCast_eq_smul_one, intCast_eq_smul_one, smul_mul_assoc, one_mul]
    · rw [hc, map_add, map_add, map_mul, map_mul, hjpN, mul_zero, add_zero, map_intCast, map_intCast]
    · rw [hc, map_add, map_add, map_mul, map_mul, map_add, map_add, map_mul, map_mul, map_pow, map_natCast,
        hjpN, mul_zero, add_zero, map_intCast, map_intCast, map_intCast, map_intCast]

  have hlieAct : ∀ c (v : Fin 2 → S), Y.lieAct c v = (ℓ c).mulVec v := fun c v => by
    rw [hℓ]; rfl

  have hZero : Y.lieZero j = LinearMap.ker (Matrix.mulVecLin (T - a • (1 : Matrix (Fin 2) (Fin 2) S))) := by
    ext v
    rw [FormalODModule.lieZero, Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      sub_smul_one_mulVec, sub_eq_zero]
    constructor
    · intro h
      have := h ω
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero,
        hlieAct, hTℓ] at this
      exact this
    · intro hv c
      obtain ⟨m, m', h1, h2, -⟩ := key c
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, hlieAct,
        h1, h2, Matrix.add_mulVec, smul_one_mulVec, Matrix.smul_mulVec, hv, smul_smul, ← add_smul]
  have hOne : Y.lieOne j = LinearMap.ker (Matrix.mulVecLin (T - b • (1 : Matrix (Fin 2) (Fin 2) S))) := by
    ext v
    rw [FormalODModule.lieOne, Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      sub_smul_one_mulVec, sub_eq_zero]
    constructor
    · intro h
      have := h ω
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero,
        hlieAct, hTℓ] at this
      exact this
    · intro hv c
      obtain ⟨m, m', h1, -, h3⟩ := key c
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, hlieAct,
        h1, h3, Matrix.add_mulVec, smul_one_mulVec, Matrix.smul_mulVec, hv, smul_smul, ← add_smul]
  refine ⟨hu, hprod₁, hZero, hOne, ?_⟩
  rw [hZero, hOne]
  exact isCompl_ker_of_mul_eq_zero T a b hprod₁ hprod₂ hu

end Eigen

end SpecialClopenSol

theorem solution
    (p : ℕ) [Fact p.Prime] (ω : Zp2 p) (t n : ℤ)
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
  SpecialClopenSol.eigenSplit p ω t n hirr hω hσ hdense hS j Y

end S_CerednikDrinfeld_FormalODModule_isCompl_lieZero_lieOne_and_eq_ker_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_isCompl_lieZero_lieOne_and_eq_ker_of_isNilpotent (solution)
