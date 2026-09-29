-- Prove2me | solution 1 for CuspForm.alSlash_coe_heckeTLinH_eq_coe_heckeTLinH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b72e3f62-ee74-5d9e-b1d9-e2326f95554c

import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CuspForm_TwoCuspLattice
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspForm_stableT
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_alSlash_coe_heckeTLinH_eq_coe_heckeTLinH

set_option autoImplicit false
set_option maxHeartbeats 6400000

open scoped ModularForm MatrixGroups

noncomputable section

namespace RepsConj

section Identities

variable (p R a b : ℤ)

def Wm : Matrix (Fin 2) (Fin 2) ℤ := !![p * a, b; p * R, p]

def Lt (ℓ t : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, t; 0, ℓ]

def Linf (ℓ x y z : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![x, y; p * R * z, ℓ] * !![ℓ, 0; 0, 1]

def g1 (ℓ t s E : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![p * a + t * (p * R) - R * E, -(a * b) - t * b * R + a * E;
     (p * R) * (ℓ - 1 + s * R), p * a - ℓ * R * b - a * s * (p * R)]

theorem case1 (ℓ t s E : ℤ) (hb : p * a - R * b = 1) (hE : ℓ * E = b + t * p - s * (p * a + t * (p * R))) :
    Lt ℓ t * Wm p R a b = g1 p R a b ℓ t s E * Wm p R a b * Lt ℓ s := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lt, Wm, g1, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (-(p * a + p * t * R)) * hb
  · linear_combination (-(b + t * p)) * hb + (b * R - p * a) * hE
  · linear_combination (-(ℓ * p * R)) * hb
  · linear_combination (-(ℓ * p)) * hb

def g2 (ℓ t F x y z : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![ℓ * F - (b + t * p) * (p * R) * z + R * (F * y - (b + t * p) * x),
      -(a * b) - t * b * R + R * z * b * (b + t * p) - a * F * y + a * (b + t * p) * x;
     (p * R) * (ℓ - ℓ * p * z + R * y - ℓ * x),
      -(ℓ * R * b) + ℓ * b * (p * R) * z - a * (p * R) * y + ℓ * p * a * x]

theorem case2 (ℓ t F x y z : ℤ) (hb : p * a - R * b = 1) (hρ : x * ℓ - y * (p * R * z) = 1) (hF : ℓ * F = p * a + t * (p * R)) :
    Lt ℓ t * Wm p R a b = g2 p R a b ℓ t F x y z * Wm p R a b * Linf p R ℓ x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lt, Wm, g2, Linf, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (-(p * ℓ * (a * x + R * b * z)) + p * R * z * y) * hF +
      (p * R * ℓ * F * z * y - (p * a + t * (p * R)) * ℓ * x) * hb + (-(p * a + t * (p * R))) * hρ
  · linear_combination (-(b * (ℓ + R * y))) * hF + (-((b + t * p) * (x * ℓ - y * (p * R * z)))) * hb + (-(b + t * p)) * hρ
  · linear_combination (-(ℓ * p * R * (x * ℓ - y * (p * R * z)))) * hb + (-(ℓ * p * R)) * hρ
  · linear_combination (-(ℓ * p * (x * ℓ - y * (p * R * z)))) * hb + (-(ℓ * p)) * hρ

def e3 (ℓ s G : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![ℓ * p * a - R * (b - s * p * a), -(ℓ * a * b) + a * (b - s * p * a);
     (p * R) * (1 - G), -(R * b) + p * a * G]

def g3 (ℓ s G x y z : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![x, y; p * R * z, ℓ] * e3 p R a b ℓ s G

theorem case3 (ℓ s G x y z : ℤ) (hb : p * a - R * b = 1) (hG : ℓ * G = 1 - s * R) :
    Linf p R ℓ x y z * Wm p R a b = g3 p R a b ℓ s G x y z * Wm p R a b * Lt ℓ s := by

  have key : !![ℓ, 0; 0, 1] * Wm p R a b = e3 p R a b ℓ s G * Wm p R a b * Lt ℓ s := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Lt, Wm, e3, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (-(ℓ * p * a)) * hb
    · linear_combination (-(ℓ * b)) * hb
    · linear_combination (-(p * R)) * hb
    · linear_combination (-p) * hb + (p * (R * b - p * a)) * hG
  rw [Linf, g3, Matrix.mul_assoc, key, ← Matrix.mul_assoc, ← Matrix.mul_assoc]

end Identities

section Congr

variable (p R a b : ℤ)

theorem g1_10 (ℓ t s E : ℤ) : g1 p R a b ℓ t s E 1 0 = (p * R) * (ℓ - 1 + s * R) := by simp [g1]
theorem g1_11 (ℓ t s E : ℤ) (hb : p * a - R * b = 1) : g1 p R a b ℓ t s E 1 1 - 1 = R * (b - ℓ * b - a * s * p) := by
  simp [g1]; linear_combination hb
theorem g2_10 (ℓ t F x y z : ℤ) : g2 p R a b ℓ t F x y z 1 0 = (p * R) * (ℓ - ℓ * p * z + R * y - ℓ * x) := by simp [g2]
theorem g2_11 (ℓ t F x y z : ℤ) (hb : p * a - R * b = 1) (hρ : x * ℓ - y * (p * R * z) = 1) :
    g2 p R a b ℓ t F x y z 1 1 - 1 = R * (-(ℓ * b) + ℓ * b * p * z - a * p * y + y * p * z + ℓ * x * b) := by
  simp [g2]; linear_combination (ℓ * x) * hb + hρ
theorem g3_10 (ℓ s G x y z : ℤ) : g3 p R a b ℓ s G x y z 1 0 =
    (p * R) * (z * (ℓ * p * a - R * (b - s * p * a)) + ℓ * (1 - G)) := by
  simp [g3, e3, Matrix.mul_apply, Fin.sum_univ_two]; ring
theorem g3_11 (ℓ s G x y z : ℤ) (hb : p * a - R * b = 1) (hG : ℓ * G = 1 - s * R) : g3 p R a b ℓ s G x y z 1 1 - 1 =
    R * (p * z * (-(ℓ * a * b) + a * (b - s * p * a)) - ℓ * b - s + b - s * R * b) := by
  simp [g3, e3, Matrix.mul_apply, Fin.sum_univ_two]; linear_combination (1 - s * R) * hb + (p * a) * hG

end Congr

end RepsConj

namespace ALTCommute

def Lmat (M : ℕ) (ℓ : ℕ) (x y z : ℤ) : Option (Fin ℓ) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![x, y; (M : ℤ) * z, (ℓ : ℤ)] * !![(ℓ : ℤ), 0; 0, 1]
  | some t => !![1, ((t : ℕ) : ℤ); 0, (ℓ : ℤ)]

open RepsConj in

theorem int_reps (M : ℕ) [NeZero M] (p : ℕ) (W : ModularForm.AtkinLehnerDatum M p) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (x y z : ℤ) (hρ : x * ℓ - y * (M * z) = 1) :
    ∃ (π : Option (Fin ℓ) ≃ Option (Fin ℓ)) (g : Option (Fin ℓ) → SL(2, ℤ)),
      (∀ i, g i ∈ CongruenceSubgroup.Gamma0 M ∧ ((((g i : SL(2, ℤ)) 1 1 : ℤ)) : ZMod W.R) = 1) ∧
      ∀ i, Lmat M ℓ x y z i * W.mat = (g i : Matrix (Fin 2) (Fin 2) ℤ) * W.mat * Lmat M ℓ x y z (π i) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩

  set pp : ℤ := (p : ℤ) with hpp
  set R : ℤ := (W.R : ℤ) with hR
  set a : ℤ := W.a
  set b : ℤ := W.b
  have hb : pp * a - R * b = 1 := W.bezout
  have hM : (M : ℤ) = pp * R := W.hM_int
  have hWm : W.mat = Wm pp R a b := rfl
  have hp0 : pp ≠ 0 := by rw [hpp]; exact_mod_cast W.q_pos.ne'
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero

  have hℓp : ((p : ℤ) : ZMod ℓ) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd_natCast] at h
    exact hℓM (h.trans ⟨W.R, W.hM⟩)
  have hℓR : ((W.R : ℤ) : ZMod ℓ) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd_natCast] at h
    exact hℓM (h.trans ⟨p, W.hM.trans (Nat.mul_comm _ _)⟩)
  have hℓM' : ((M : ℤ) : ZMod ℓ) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd_natCast] at h
    exact hℓM h

  let u : Fin ℓ → ℤ := fun t => pp * a + (t : ℕ) * (pp * R)
  let q : Fin ℓ → ℤ := fun t => b + (t : ℕ) * pp

  let sOf : Fin ℓ → Fin ℓ := fun t => ⟨(((q t : ℤ) : ZMod ℓ) * ((u t : ℤ) : ZMod ℓ)⁻¹).val, ZMod.val_lt _⟩
  let s0 : Fin ℓ := ⟨(((W.R : ℤ) : ZMod ℓ)⁻¹).val, ZMod.val_lt _⟩
  let πf : Option (Fin ℓ) → Option (Fin ℓ) := fun i =>
    match i with
    | none => some s0
    | some t => if ((u t : ℤ) : ZMod ℓ) = 0 then none else some (sOf t)

  have hsOf : ∀ t, ((((sOf t : ℕ) : ℤ)) : ZMod ℓ) = ((q t : ℤ) : ZMod ℓ) * ((u t : ℤ) : ZMod ℓ)⁻¹ := by
    intro t; simp [sOf, ZMod.natCast_zmod_val]
  have hs0 : ((((s0 : ℕ) : ℤ)) : ZMod ℓ) = ((W.R : ℤ) : ZMod ℓ)⁻¹ := by simp [s0, ZMod.natCast_zmod_val]
  have hE : ∀ t, ((u t : ℤ) : ZMod ℓ) ≠ 0 → (ℓ : ℤ) ∣ q t - ((sOf t : ℕ) : ℤ) * u t := by
    intro t hu
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_sub, Int.cast_mul, hsOf t, inv_mul_cancel_right₀ hu, sub_self]
  have hF : ∀ t, ((u t : ℤ) : ZMod ℓ) = 0 → (ℓ : ℤ) ∣ u t := fun t hu => (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hu
  have hG : (ℓ : ℤ) ∣ 1 - ((s0 : ℕ) : ℤ) * R := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_sub, Int.cast_one, Int.cast_mul, hs0, hR, inv_mul_cancel₀ hℓR, sub_self]
  have hρ' : x * ℓ - y * (pp * R * z) = 1 := by rw [← hM]; exact hρ
  have hLnone : Lmat M ℓ x y z none = Linf pp R ℓ x y z := by
    show !![x, y; (M : ℤ) * z, (ℓ : ℤ)] * !![(ℓ : ℤ), 0; 0, 1] = _
    rw [hM]; rfl
  have hLsome : ∀ t : Fin ℓ, Lmat M ℓ x y z (some t) = Lt ℓ ((t : ℕ) : ℤ) := fun t => rfl

  let gm : Option (Fin ℓ) → Matrix (Fin 2) (Fin 2) ℤ := fun i =>
    match i with
    | none => g3 pp R a b ℓ ((s0 : ℕ) : ℤ) ((1 - ((s0 : ℕ) : ℤ) * R) / ℓ) x y z
    | some t => if ((u t : ℤ) : ZMod ℓ) = 0 then g2 pp R a b ℓ ((t : ℕ) : ℤ) (u t / ℓ) x y z
        else g1 pp R a b ℓ ((t : ℕ) : ℤ) ((sOf t : ℕ) : ℤ) ((q t - ((sOf t : ℕ) : ℤ) * u t) / ℓ)

  have hid : ∀ i, Lmat M ℓ x y z i * W.mat = gm i * W.mat * Lmat M ℓ x y z (πf i) := by
    intro i
    cases i with
    | none =>
      show Lmat M ℓ x y z none * W.mat = g3 pp R a b ℓ ((s0 : ℕ) : ℤ) ((1 - ((s0 : ℕ) : ℤ) * R) / ℓ) x y z * W.mat * Lmat M ℓ x y z (some s0)
      rw [hLnone, hLsome, hWm]
      exact case3 pp R a b ℓ _ _ x y z hb (Int.mul_ediv_cancel' hG)
    | some t =>
      by_cases hu : ((u t : ℤ) : ZMod ℓ) = 0
      · show Lmat M ℓ x y z (some t) * W.mat = (if ((u t : ℤ) : ZMod ℓ) = 0 then g2 pp R a b ℓ ((t : ℕ) : ℤ) (u t / ℓ) x y z else g1 pp R a b ℓ ((t : ℕ) : ℤ) ((sOf t : ℕ) : ℤ) ((q t - ((sOf t : ℕ) : ℤ) * u t) / ℓ)) * W.mat *
          Lmat M ℓ x y z (if ((u t : ℤ) : ZMod ℓ) = 0 then none else some (sOf t))
        rw [if_pos hu, if_pos hu, hLnone, hLsome, hWm]
        exact case2 pp R a b ℓ _ _ x y z hb hρ' (Int.mul_ediv_cancel' (hF t hu))
      · show Lmat M ℓ x y z (some t) * W.mat = (if ((u t : ℤ) : ZMod ℓ) = 0 then g2 pp R a b ℓ ((t : ℕ) : ℤ) (u t / ℓ) x y z else g1 pp R a b ℓ ((t : ℕ) : ℤ) ((sOf t : ℕ) : ℤ) ((q t - ((sOf t : ℕ) : ℤ) * u t) / ℓ)) * W.mat *
          Lmat M ℓ x y z (if ((u t : ℤ) : ZMod ℓ) = 0 then none else some (sOf t))
        rw [if_neg hu, if_neg hu, hLsome, hLsome, hWm]
        exact case1 pp R a b ℓ _ _ _ hb (Int.mul_ediv_cancel' (hE t hu))

  have hdetL : ∀ i, (Lmat M ℓ x y z i).det = ℓ := by
    intro i
    cases i with
    | none =>
      show (!![x, y; (M : ℤ) * z, (ℓ : ℤ)] * !![(ℓ : ℤ), 0; 0, 1]).det = ℓ
      rw [Matrix.det_mul, Matrix.det_fin_two_of, Matrix.det_fin_two_of]
      linear_combination (ℓ : ℤ) * hρ
    | some t =>
      show (!![1, ((t : ℕ) : ℤ); 0, (ℓ : ℤ)]).det = ℓ
      rw [Matrix.det_fin_two_of]; ring
  have hdet : ∀ i, (gm i).det = 1 := by
    intro i
    have h := congrArg Matrix.det (hid i)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, hdetL, hdetL, W.det_mat] at h

    have hne : (ℓ : ℤ) * (p : ℤ) ≠ 0 := mul_ne_zero hℓ0 (by exact_mod_cast W.q_pos.ne')
    apply mul_right_cancel₀ hne
    linear_combination h.symm

  have h10 : ∀ i, ∃ c : ℤ, gm i 1 0 = (M : ℤ) * c := by
    intro i
    cases i with
    | none =>
      refine ⟨z * (ℓ * pp * a - R * (b - ((s0 : ℕ) : ℤ) * pp * a)) + ℓ * (1 - (1 - ((s0 : ℕ) : ℤ) * R) / ℓ), ?_⟩
      show g3 pp R a b ℓ ((s0 : ℕ) : ℤ) ((1 - ((s0 : ℕ) : ℤ) * R) / ℓ) x y z 1 0 = _
      rw [hM]; exact g3_10 pp R a b ℓ _ _ x y z
    | some t =>
      by_cases hu : ((u t : ℤ) : ZMod ℓ) = 0
      · refine ⟨ℓ - ℓ * pp * z + R * y - ℓ * x, ?_⟩
        show (if ((u t : ℤ) : ZMod ℓ) = 0 then g2 pp R a b ℓ ((t : ℕ) : ℤ) (u t / ℓ) x y z else g1 pp R a b ℓ ((t : ℕ) : ℤ) ((sOf t : ℕ) : ℤ) ((q t - ((sOf t : ℕ) : ℤ) * u t) / ℓ)) 1 0 = _
        rw [if_pos hu, hM]; exact g2_10 pp R a b ℓ _ _ x y z
      · refine ⟨ℓ - 1 + ((sOf t : ℕ) : ℤ) * R, ?_⟩
        show (if ((u t : ℤ) : ZMod ℓ) = 0 then g2 pp R a b ℓ ((t : ℕ) : ℤ) (u t / ℓ) x y z else g1 pp R a b ℓ ((t : ℕ) : ℤ) ((sOf t : ℕ) : ℤ) ((q t - ((sOf t : ℕ) : ℤ) * u t) / ℓ)) 1 0 = _
        rw [if_neg hu, hM]; exact g1_10 pp R a b ℓ _ _ _
  have h11 : ∀ i, ∃ c : ℤ, gm i 1 1 - 1 = R * c := by
    intro i
    cases i with
    | none =>
      exact ⟨pp * z * (-(ℓ * a * b) + a * (b - ((s0 : ℕ) : ℤ) * pp * a)) - ℓ * b - ((s0 : ℕ) : ℤ) + b - ((s0 : ℕ) : ℤ) * R * b,
        g3_11 pp R a b ℓ _ _ x y z hb (Int.mul_ediv_cancel' hG)⟩
    | some t =>
      by_cases hu : ((u t : ℤ) : ZMod ℓ) = 0
      · refine ⟨-(ℓ * b) + ℓ * b * pp * z - a * pp * y + y * pp * z + ℓ * x * b, ?_⟩
        show (if ((u t : ℤ) : ZMod ℓ) = 0 then g2 pp R a b ℓ ((t : ℕ) : ℤ) (u t / ℓ) x y z else g1 pp R a b ℓ ((t : ℕ) : ℤ) ((sOf t : ℕ) : ℤ) ((q t - ((sOf t : ℕ) : ℤ) * u t) / ℓ)) 1 1 - 1 = _
        rw [if_pos hu]; exact g2_11 pp R a b ℓ _ _ x y z hb hρ'
      · refine ⟨b - ℓ * b - a * ((sOf t : ℕ) : ℤ) * pp, ?_⟩
        show (if ((u t : ℤ) : ZMod ℓ) = 0 then g2 pp R a b ℓ ((t : ℕ) : ℤ) (u t / ℓ) x y z else g1 pp R a b ℓ ((t : ℕ) : ℤ) ((sOf t : ℕ) : ℤ) ((q t - ((sOf t : ℕ) : ℤ) * u t) / ℓ)) 1 1 - 1 = _
        rw [if_neg hu]; exact g1_11 pp R a b ℓ _ _ _ hb

  have finEq : ∀ t t' : Fin ℓ, ((((t : ℕ) : ℤ)) : ZMod ℓ) = ((((t' : ℕ) : ℤ)) : ZMod ℓ) → t = t' := by
    intro t t' h
    simp only [Int.cast_natCast] at h
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt ((ZMod.natCast_eq_natCast_iff _ _ _).mp h) t.2 t'.2)
  have hpnz : ((pp : ℤ) : ZMod ℓ) ≠ 0 := by rw [hpp]; exact hℓp
  have hRnz : ((R : ℤ) : ZMod ℓ) ≠ 0 := by rw [hR]; exact hℓR
  have huq : ∀ t, u t - R * q t = 1 := by intro t; simp only [u, q]; linear_combination hb

  have hs0ne : ∀ t, ((u t : ℤ) : ZMod ℓ) ≠ 0 → sOf t ≠ s0 := by
    intro t hu he
    have e : ((q t : ℤ) : ZMod ℓ) * ((u t : ℤ) : ZMod ℓ)⁻¹ = ((W.R : ℤ) : ZMod ℓ)⁻¹ := by rw [← hsOf, ← hs0, he]
    have e2 : ((q t : ℤ) : ZMod ℓ) = ((W.R : ℤ) : ZMod ℓ)⁻¹ * ((u t : ℤ) : ZMod ℓ) := by
      rw [← e, inv_mul_cancel_right₀ hu]
    have e3 : (((u t - R * q t : ℤ)) : ZMod ℓ) = 0 := by
      rw [Int.cast_sub, Int.cast_mul, e2, ← mul_assoc, hR, mul_inv_cancel₀ hℓR, one_mul, sub_self]
    rw [huq t, Int.cast_one] at e3
    exact one_ne_zero e3

  have hinj1 : ∀ t t', ((u t : ℤ) : ZMod ℓ) ≠ 0 → ((u t' : ℤ) : ZMod ℓ) ≠ 0 → sOf t = sOf t' → t = t' := by
    intro t t' hu hu' he
    have e : ((q t : ℤ) : ZMod ℓ) * ((u t : ℤ) : ZMod ℓ)⁻¹ = ((q t' : ℤ) : ZMod ℓ) * ((u t' : ℤ) : ZMod ℓ)⁻¹ := by
      rw [← hsOf, ← hsOf, he]
    have e2 : ((q t : ℤ) : ZMod ℓ) * ((u t' : ℤ) : ZMod ℓ) = ((q t' : ℤ) : ZMod ℓ) * ((u t : ℤ) : ZMod ℓ) := by
      have := congrArg (fun w => w * ((u t : ℤ) : ZMod ℓ) * ((u t' : ℤ) : ZMod ℓ)) e
      rwa [inv_mul_cancel_right₀ hu, mul_assoc, mul_comm (((u t : ℤ) : ZMod ℓ)), ← mul_assoc, inv_mul_cancel_right₀ hu'] at this
    have e3 : (((q t * u t' - q t' * u t : ℤ)) : ZMod ℓ) = 0 := by rw [Int.cast_sub, Int.cast_mul, Int.cast_mul, e2, sub_self]
    have e4 : q t * u t' - q t' * u t = (((t : ℕ) : ℤ) - ((t' : ℕ) : ℤ)) * pp := by
      simp only [u, q]; linear_combination ((((t : ℕ) : ℤ) - ((t' : ℕ) : ℤ)) * pp) * hb
    rw [e4, Int.cast_mul, mul_eq_zero] at e3
    rcases e3 with e3 | e3
    · rw [Int.cast_sub, sub_eq_zero] at e3; exact finEq t t' e3
    · exact absurd e3 hpnz

  have hinj2 : ∀ t t', ((u t : ℤ) : ZMod ℓ) = 0 → ((u t' : ℤ) : ZMod ℓ) = 0 → t = t' := by
    intro t t' hu hu'
    have e3 : (((u t - u t' : ℤ)) : ZMod ℓ) = 0 := by rw [Int.cast_sub, hu, hu', sub_self]
    have e4 : u t - u t' = (((t : ℕ) : ℤ) - ((t' : ℕ) : ℤ)) * (pp * R) := by simp only [u]; ring
    rw [e4, Int.cast_mul, mul_eq_zero, Int.cast_mul, mul_eq_zero] at e3
    rcases e3 with e3 | e3 | e3
    · rw [Int.cast_sub, sub_eq_zero] at e3; exact finEq t t' e3
    · exact absurd e3 hpnz
    · exact absurd e3 hRnz
  have hinj : Function.Injective πf := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some t' =>
        exfalso
        change some s0 = (if ((u t' : ℤ) : ZMod ℓ) = 0 then none else some (sOf t')) at hij
        split_ifs at hij with hu
        exact hs0ne t' hu (Option.some_injective _ hij).symm
    | some t =>
      cases j with
      | none =>
        exfalso
        change (if ((u t : ℤ) : ZMod ℓ) = 0 then none else some (sOf t)) = some s0 at hij
        split_ifs at hij with hu
        exact hs0ne t hu (Option.some_injective _ hij)
      | some t' =>
        change (if ((u t : ℤ) : ZMod ℓ) = 0 then none else some (sOf t)) =
          (if ((u t' : ℤ) : ZMod ℓ) = 0 then none else some (sOf t')) at hij
        by_cases hu : ((u t : ℤ) : ZMod ℓ) = 0 <;> by_cases hu' : ((u t' : ℤ) : ZMod ℓ) = 0
        · rw [hinj2 t t' hu hu']
        · rw [if_pos hu, if_neg hu'] at hij; exact absurd hij (by simp)
        · rw [if_neg hu, if_pos hu'] at hij; exact absurd hij (by simp)
        · rw [if_neg hu, if_neg hu'] at hij; rw [hinj1 t t' hu hu' (Option.some_injective _ hij)]
  have hbij : Function.Bijective πf := Finite.injective_iff_bijective.mp hinj

  refine ⟨Equiv.ofBijective πf hbij, fun i => ⟨gm i, hdet i⟩, fun i => ⟨?_, ?_⟩, fun i => ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    obtain ⟨c, hc⟩ := h10 i
    show ((gm i 1 0 : ℤ) : ZMod M) = 0
    rw [hc]; push_cast; simp
  · obtain ⟨c, hc⟩ := h11 i
    show ((gm i 1 1 : ℤ) : ZMod W.R) = 1
    rw [← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, hc, hR]; push_cast; simp
  · exact hid i

end ALTCommute

namespace ALTCommute

theorem sum_slash {ι : Type*} (s : Finset ι) (k : ℤ) (F : ι → UpperHalfPlane → ℂ) (g : GL (Fin 2) ℝ) :
    (∑ i ∈ s, F i) ∣[k] g = ∑ i ∈ s, (F i) ∣[k] g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

def rep (ℓ : ℕ) (σ : GL (Fin 2) ℝ) : Option (Fin ℓ) → GL (Fin 2) ℝ
  | none => σ * ModularForm.heckeDiagMatrix ℓ
  | some j => ModularForm.heckeMatrix ℓ j

theorem heckeU_add_slash_eq_sum (k : ℤ) (ℓ : ℕ) (σ : GL (Fin 2) ℝ) (f : UpperHalfPlane → ℂ) :
    ModularForm.heckeU k ℓ f + f ∣[k] (σ * ModularForm.heckeDiagMatrix ℓ) =
      ∑ i : Option (Fin ℓ), f ∣[k] rep ℓ σ i := by
  rw [Fintype.sum_option, ModularForm.heckeU_def, add_comm, Finset.sum_range]
  rfl

end ALTCommute

namespace CuspForm p2m_export "CuspForm" "ext gammaLift unitOfPrimeNotDvd heckeTLinH coe_heckeTLinH_apply coe_heckeTLinH_eq stableT" end CuspForm
p2m_open_scoped "CuspForm" in
open ALTCommute in

theorem CuspForm.alSlash_coe_heckeTLinH_eq_coe_heckeTLinH_of_reps
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (W : ModularForm.AtkinLehnerDatum M p) (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (hreps : ∃ (π : Option (Fin ℓ) ≃ Option (Fin ℓ)) (g : Option (Fin ℓ) → SL(2, ℤ)),
      (∀ i, g i ∈ CohCarrier.GammaH M H) ∧
      ∀ i, rep ℓ ((Matrix.SpecialLinearGroup.mapGL ℝ
            (CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ)) i * W.alGL =
        (Matrix.SpecialLinearGroup.mapGL ℝ (g i) : GL (Fin 2) ℝ) *
          (W.alGL * rep ℓ ((Matrix.SpecialLinearGroup.mapGL ℝ
              (CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ)) (π i)))
    (f X : CuspForm (CohCarrier.GammaH M H) k) (hX : ⇑X = ModularForm.alSlash W k ⇑f) :
    ModularForm.alSlash W k ⇑(CuspForm.heckeTLinH k hℓ hℓM f) = ⇑(CuspForm.heckeTLinH k hℓ hℓM X) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hT := CuspForm.stableT M H k hℓ hℓM
  set σℓ : GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ
    (CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) with hσℓ
  rw [CuspForm.coe_heckeTLinH_apply k hℓ hℓM hT, CuspForm.coe_heckeTLinH_apply k hℓ hℓM hT,
    hX, ModularForm.alSlash_def, ModularForm.alSlash_def,
    heckeU_add_slash_eq_sum, heckeU_add_slash_eq_sum, sum_slash]
  simp only [← SlashAction.slash_mul]
  obtain ⟨π, g, hg, hrel⟩ := hreps
  rw [← Equiv.sum_comp π (fun i => (⇑f) ∣[k] (W.alGL * rep ℓ σℓ i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hrel i, SlashAction.slash_mul]
  congr 1
  exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ (hg i))

namespace ALTCommute

def rho0 (M : ℕ) (ℓ : ℕ) (x y z : ℤ) (hρ : x * ℓ - y * (M * z) = 1) : SL(2, ℤ) :=
  ⟨!![x, y; (M : ℤ) * z, (ℓ : ℤ)], by rw [Matrix.det_fin_two_of]; linarith⟩

theorem rho0_mem (M : ℕ) (ℓ : ℕ) (x y z : ℤ) (hρ : x * ℓ - y * (M * z) = 1) :
    rho0 M ℓ x y z hρ ∈ CongruenceSubgroup.Gamma0 M := by
  rw [CongruenceSubgroup.Gamma0_mem]
  show ((((M : ℤ) * z : ℤ)) : ZMod M) = 0
  push_cast
  simp

theorem rho0_apply_11 (M : ℕ) (ℓ : ℕ) (x y z : ℤ) (hρ : x * ℓ - y * (M * z) = 1) :
    ((rho0 M ℓ x y z hρ : SL(2, ℤ)) 1 1 : ℤ) = ℓ := rfl

theorem exists_rho0 (M : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    ∃ x y z : ℤ, x * ℓ - y * (M * z) = 1 := by
  have hcop : IsCoprime (ℓ : ℤ) (M : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM
  obtain ⟨u, v, huv⟩ := hcop
  exact ⟨u, -v, 1, by linear_combination huv⟩

theorem val_mapGL_eq_map (g : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (g : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) := rfl

theorem val_rep_eq_map (M : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) (x y z : ℤ) (hρ : x * ℓ - y * (M * z) = 1) (i : Option (Fin ℓ)) :
    ((rep ℓ (Matrix.SpecialLinearGroup.mapGL ℝ (rho0 M ℓ x y z hρ) : GL (Fin 2) ℝ) i : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) = (Lmat M ℓ x y z i).map (Int.castRingHom ℝ) := by
  have hl : ℓ ≠ 0 := hℓ.ne_zero
  cases i with
  | none =>
    show ((Matrix.SpecialLinearGroup.mapGL ℝ (rho0 M ℓ x y z hρ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
      ((ModularForm.heckeDiagMatrix ℓ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [ModularForm.val_heckeDiagMatrix hl, Lmat, Matrix.map_mul, val_mapGL_eq_map]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | some t =>
    show ((ModularForm.heckeMatrix ℓ t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [ModularForm.val_heckeMatrix hl, Lmat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem val_alGL_eq_map {M p : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M p) :
    ((W.alGL : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (W.mat).map (Int.castRingHom ℝ) := W.alGL_coe

theorem hreps_of_int {M : ℕ} [NeZero M] {p : ℕ} (W : ModularForm.AtkinLehnerDatum M p) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (x y z : ℤ) (hρ : x * ℓ - y * (M * z) = 1)
    (π : Option (Fin ℓ) ≃ Option (Fin ℓ)) (g : Option (Fin ℓ) → SL(2, ℤ))
    (hint : ∀ i, Lmat M ℓ x y z i * W.mat = (g i : Matrix (Fin 2) (Fin 2) ℤ) * W.mat * Lmat M ℓ x y z (π i)) :
    ∀ i, rep ℓ (Matrix.SpecialLinearGroup.mapGL ℝ (rho0 M ℓ x y z hρ) : GL (Fin 2) ℝ) i * W.alGL =
      (Matrix.SpecialLinearGroup.mapGL ℝ (g i) : GL (Fin 2) ℝ) *
        (W.alGL * rep ℓ (Matrix.SpecialLinearGroup.mapGL ℝ (rho0 M ℓ x y z hρ) : GL (Fin 2) ℝ) (π i)) := by
  intro i
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, val_rep_eq_map M hℓ, val_rep_eq_map M hℓ, val_mapGL_eq_map,
    val_alGL_eq_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hint i, Matrix.mul_assoc]

end ALTCommute

p2m_open_scoped "CuspForm" in
open ALTCommute in

theorem CuspForm.alSlash_coe_heckeTLinH_eq_coe_heckeTLinH_of_int
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (x y z : ℤ) (hρ : x * ℓ - y * (M * z) = 1)
    (hint : ∃ (π : Option (Fin ℓ) ≃ Option (Fin ℓ)) (g : Option (Fin ℓ) → SL(2, ℤ)),
      (∀ i, g i ∈ CongruenceSubgroup.Gamma0 M ∧ ((((g i : SL(2, ℤ)) 1 1 : ℤ)) : ZMod W.R) = 1) ∧
      ∀ i, Lmat M ℓ x y z i * W.mat = (g i : Matrix (Fin 2) (Fin 2) ℤ) * W.mat * Lmat M ℓ x y z (π i))
    (f X : CuspForm (CohCarrier.GammaH M H) k) (hX : ⇑X = ModularForm.alSlash W k ⇑f) :
    ModularForm.alSlash W k ⇑(CuspForm.heckeTLinH k hℓ hℓM f) = ⇑(CuspForm.heckeTLinH k hℓ hℓM X) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hT := CuspForm.stableT M H k hℓ hℓM
  let ρ : CongruenceSubgroup.Gamma0 M := ⟨rho0 M ℓ x y z hρ, rho0_mem M ℓ x y z hρ⟩
  have hρ11 : ((((ρ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ := by
    show (((rho0 M ℓ x y z hρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ
    rw [rho0_apply_11]; push_cast; rfl
  set σ₀ : GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ (rho0 M ℓ x y z hρ) : GL (Fin 2) ℝ) with hσ₀
  rw [CuspForm.coe_heckeTLinH_eq k hℓ hℓM hT ρ hρ11, CuspForm.coe_heckeTLinH_eq k hℓ hℓM hT ρ hρ11,
    hX, ModularForm.alSlash_def, ModularForm.alSlash_def]
  change (ModularForm.heckeU k ℓ ⇑f + ⇑f ∣[k] (σ₀ * ModularForm.heckeDiagMatrix ℓ)) ∣[k] W.alGL =
    ModularForm.heckeU k ℓ (⇑f ∣[k] W.alGL) + (⇑f ∣[k] W.alGL) ∣[k] (σ₀ * ModularForm.heckeDiagMatrix ℓ)
  rw [heckeU_add_slash_eq_sum, heckeU_add_slash_eq_sum, sum_slash]
  simp only [← SlashAction.slash_mul]
  obtain ⟨π, g, hg, hint⟩ := hint
  have hrel := hreps_of_int W hℓ x y z hρ π g hint

  have hgH : ∀ i, g i ∈ CohCarrier.GammaH M H := by
    intro i
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨(hg i).1, hHp _ ?_⟩
    apply Units.ext
    have hR : W.R = M / p := (Nat.div_eq_of_eq_mul_left (Fact.out : p.Prime).pos (W.hM.trans (Nat.mul_comm p W.R))).symm
    have h1 := (hg i).2
    rw [hR] at h1
    simp only [ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units, Units.val_one]
    have e1 : ((CongruenceSubgroup.Gamma0Map M) ⟨g i, (hg i).1⟩ : ZMod M) = (((g i : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) := rfl
    rw [ZMod.castHom_apply, e1, ZMod.cast_intCast (Nat.div_dvd_of_dvd hpM)]
    exact h1
  rw [← Equiv.sum_comp π (fun i => (⇑f) ∣[k] (W.alGL * rep ℓ σ₀ i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hrel i, SlashAction.slash_mul]
  congr 1
  exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ (hgH i))

theorem solution
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (f X : CuspForm (CohCarrier.GammaH M H) k) (hX : ⇑X = ModularForm.alSlash W k ⇑f) :
    ModularForm.alSlash W k ⇑(CuspForm.heckeTLinH k hℓ hℓM f) = ⇑(CuspForm.heckeTLinH k hℓ hℓM X) := by
  obtain ⟨x, y, z, hρ⟩ := ALTCommute.exists_rho0 M hℓ hℓM
  exact CuspForm.alSlash_coe_heckeTLinH_eq_coe_heckeTLinH_of_int M p hpM H hHp W k hℓ hℓM x y z hρ
    (ALTCommute.int_reps M p W hℓ hℓM x y z hρ) f X hX

end

end S_CuspForm_alSlash_coe_heckeTLinH_eq_coe_heckeTLinH
end P2MW
export P2MW.S_CuspForm_alSlash_coe_heckeTLinH_eq_coe_heckeTLinH (solution)
