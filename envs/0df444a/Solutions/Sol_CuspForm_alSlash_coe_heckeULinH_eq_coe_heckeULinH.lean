-- Prove2me | solution 1 for CuspForm.alSlash_coe_heckeULinH_eq_coe_heckeULinH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/a45c87ec-bb0f-52e9-9933-553eb3beae6a

import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Theorems.Thm_CuspForm_stableU
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_alSlash_coe_heckeULinH_eq_coe_heckeULinH
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open scoped ModularForm MatrixGroups

noncomputable section

namespace UWComm

theorem sum_slash {ι : Type*} (s : Finset ι) (k : ℤ) (F : ι → UpperHalfPlane → ℂ) (g : GL (Fin 2) ℝ) :
    (∑ i ∈ s, F i) ∣[k] g = ∑ i ∈ s, (F i) ∣[k] g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

def beta (q j : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, j; 0, q]

def gam (p R a b q j j' t : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![p * a + j * p * R - t * R, -(a * b) - j * R * b + t * a;
     p * R * (q - 1 + j' * R), 1 - (q - 1) * R * b - j' * p * R * a]

theorem key (p R a b q j j' t : ℤ) (hbez : p * a - R * b = 1)
    (ht : q * t = b + j * p - j' * (p * a + j * p * R)) :
    beta q j * !![p * a, b; p * R, p] = gam p R a b q j j' t * (!![p * a, b; p * R, p] * beta q j') := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp only [beta, gam, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta, Fin.mk_one]
  · linear_combination (-(p * a + j * p * R)) * hbez
  · linear_combination (-((p * a + j * p * R) * j' + t * q)) * hbez + (-1 : ℤ) * ht
  · linear_combination (-(p * R * (q - 1))) * hbez
  · linear_combination (j' * p * R) * hbez

theorem det_gam (p R a b q j j' t : ℤ) (hbez : p * a - R * b = 1)
    (ht : q * t = b + j * p - j' * (p * a + j * p * R)) (hp : p ≠ 0) (hq : q ≠ 0) :
    (gam p R a b q j j' t).det = 1 := by
  have h := congrArg Matrix.det (key p R a b q j j' t hbez ht)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul] at h
  have hb : ∀ j₀ : ℤ, (beta q j₀).det = q := by intro j₀; simp [beta, Matrix.det_fin_two_of]
  have hW : (!![p * a, b; p * R, p] : Matrix (Fin 2) (Fin 2) ℤ).det = p := by
    rw [Matrix.det_fin_two_of]; linear_combination p * hbez
  rw [hb, hb, hW] at h

  have hpq : (p * q : ℤ) ≠ 0 := mul_ne_zero hp hq
  have : ((gam p R a b q j j' t).det - 1) * (p * q) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp this with h1 | h1
  · linarith
  · exact absurd h1 hpq

end UWComm

open UWComm in
set_option maxHeartbeats 6400000 in
theorem solution
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p)
    (f X : CuspForm (CohCarrier.GammaH M H) k) (hX : ⇑X = ModularForm.alSlash W k ⇑f) :
    ModularForm.alSlash W k ⇑(CuspForm.heckeULinH k q f) = ⇑(CuspForm.heckeULinH k q X) := by
  have hp : p.Prime := Fact.out
  have hU := CuspForm.stableU M H k hq hqM

  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hq.pos).symm⟩

  have hMR : M = p * W.R := W.hM
  have hqR : (n + 1) ∣ W.R := by
    have : (n + 1) ∣ p * W.R := hMR ▸ hqM
    rcases (Nat.Prime.dvd_mul hq).mp this with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp h) hqp
    · exact h
  have hRq : ((W.R : ℕ) : ZMod (n + 1)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hqR
  have hpa : ((p : ℤ) : ZMod (n + 1)) * ((W.a : ℤ) : ZMod (n + 1)) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod (n + 1))) W.bezout
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, Int.cast_natCast] at h
    rw [hRq, zero_mul, sub_zero] at h
    exact_mod_cast h

  let π : ZMod (n + 1) ≃ ZMod (n + 1) :=
    { toFun := fun x => ((p : ℤ) : ZMod (n + 1)) * x + ((W.b : ℤ) : ZMod (n + 1))
      invFun := fun y => ((W.a : ℤ) : ZMod (n + 1)) * (y - ((W.b : ℤ) : ZMod (n + 1)))
      left_inv := fun x => by
        show ((W.a : ℤ) : ZMod (n + 1)) * ((((p : ℤ) : ZMod (n + 1)) * x + _) - _) = x
        rw [add_sub_cancel_right, ← mul_assoc, mul_comm ((W.a : ℤ) : ZMod (n + 1)), hpa, one_mul]
      right_inv := fun y => by
        show ((p : ℤ) : ZMod (n + 1)) * (((W.a : ℤ) : ZMod (n + 1)) * (y - _)) + _ = y
        rw [← mul_assoc, hpa, one_mul, sub_add_cancel] }

  have hval : ∀ x : ZMod (n + 1), ((x.val : ℕ) : ZMod (n + 1)) = x := fun x => ZMod.natCast_zmod_val x
  have hdvd : ∀ j : ZMod (n + 1), ((n + 1 : ℕ) : ℤ) ∣
      (W.b + j.val * (p : ℤ) -
        (π j).val * ((p : ℤ) * W.a + j.val * (p : ℤ) * (W.R : ℤ))) := by
    intro j
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hπ : (((π j).val : ℕ) : ZMod (n + 1)) = ((p : ℤ) : ZMod (n + 1)) * j + ((W.b : ℤ) : ZMod (n + 1)) := hval (π j)
    have hpa' : ((p : ℕ) : ZMod (n + 1)) * ((W.a : ℤ) : ZMod (n + 1)) = 1 := by exact_mod_cast hpa
    push_cast
    rw [hval j, hπ, hRq]
    push_cast
    linear_combination (-(((p : ℕ) : ZMod (n + 1)) * j + ((W.b : ℤ) : ZMod (n + 1)))) * hpa'
  choose t ht using hdvd

  have hbez : (p : ℤ) * W.a - (W.R : ℤ) * W.b = 1 := W.bezout
  have htj : ∀ j : ZMod (n + 1), ((n + 1 : ℕ) : ℤ) * t j =
      W.b + j.val * (p : ℤ) - (π j).val * ((p : ℤ) * W.a + j.val * (p : ℤ) * (W.R : ℤ)) :=
    fun j => (ht j).symm
  let γ : ZMod (n + 1) → SL(2, ℤ) := fun j =>
    ⟨gam p W.R W.a W.b (n + 1 : ℕ) j.val (π j).val (t j),
      det_gam _ _ _ _ _ _ _ _ hbez (htj j) (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)⟩

  have hγ0 : ∀ j, γ j ∈ CongruenceSubgroup.Gamma0 M := by
    intro j
    rw [CongruenceSubgroup.Gamma0_mem]
    show (((p : ℤ) * W.R * ((n + 1 : ℕ) - 1 + (π j).val * (W.R : ℤ)) : ℤ) : ZMod M) = 0
    rw [show ((p : ℤ) * W.R : ℤ) = (M : ℤ) by exact_mod_cast hMR.symm]
    simp
  have hγH : ∀ j, γ j ∈ CohCarrier.GammaH M H := by
    intro j
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨hγ0 j, hHp _ ?_⟩
    apply Units.ext
    rw [Units.val_one]
    have hdiv : M / p = W.R := Nat.div_eq_of_eq_mul_left hp.pos (hMR.trans (mul_comm _ _))
    show ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (CohCarrier.gamma0Units M ⟨γ j, hγ0 j⟩) : (ZMod (M / p))ˣ) : ZMod (M / p)) = 1
    rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units, ZMod.castHom_apply]
    show ZMod.cast ((((1 : ℤ) - ((n + 1 : ℕ) - 1) * (W.R : ℤ) * W.b - (π j).val * (p : ℤ) * W.R * W.a : ℤ) : ZMod M)) = (1 : ZMod (M / p))
    rw [ZMod.cast_intCast (Nat.div_dvd_of_dvd hpM)]
    have hR0 : ((W.R : ℕ) : ZMod (M / p)) = 0 := by rw [hdiv]; exact ZMod.natCast_self W.R
    push_cast
    rw [hR0]
    ring

  have hrel : ∀ j : ZMod (n + 1),
      (ModularForm.heckeMatrix (n + 1) j.val : GL (Fin 2) ℝ) * W.alGL =
        (Matrix.SpecialLinearGroup.mapGL ℝ (γ j) : GL (Fin 2) ℝ) *
          (W.alGL * ModularForm.heckeMatrix (n + 1) (π j).val) := by
    intro j
    have hk := key (p : ℤ) W.R W.a W.b (n + 1 : ℕ) j.val (π j).val (t j) hbez (htj j)
    have hk' := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A.map (Int.castRingHom ℝ)) hk
    simp only [Matrix.map_mul] at hk'
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, ModularForm.val_heckeMatrix hq.ne_zero,
      ModularForm.val_heckeMatrix hq.ne_zero, ModularForm.AtkinLehnerDatum.alGL_coe]
    have e1 : (!![(1 : ℝ), (j.val : ℝ); 0, ((n + 1 : ℕ) : ℝ)] : Matrix (Fin 2) (Fin 2) ℝ) =
        (beta (n + 1 : ℕ) j.val).map (Int.castRingHom ℝ) := by
      ext i l; fin_cases i <;> fin_cases l <;> simp [beta]
    have e2 : (!![(1 : ℝ), ((π j).val : ℝ); 0, ((n + 1 : ℕ) : ℝ)] : Matrix (Fin 2) (Fin 2) ℝ) =
        (beta (n + 1 : ℕ) (π j).val).map (Int.castRingHom ℝ) := by
      ext i l; fin_cases i <;> fin_cases l <;> simp [beta]
    have e3 : (W.mat).map (algebraMap ℤ ℝ) = (!![(p : ℤ) * W.a, W.b; (p : ℤ) * W.R, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) := by
      rfl
    have e4 : ((Matrix.SpecialLinearGroup.mapGL ℝ (γ j) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (gam p W.R W.a W.b (n + 1 : ℕ) j.val (π j).val (t j)).map (Int.castRingHom ℝ) := by
      rfl
    rw [e1, e2, e3, e4]
    exact hk'

  rw [CuspForm.coe_heckeULinH_apply k hU f, CuspForm.coe_heckeULinH_apply k hU X, hX,
    ModularForm.alSlash_def, ModularForm.alSlash_def, ModularForm.heckeU_def, ModularForm.heckeU_def, sum_slash]
  simp only [← SlashAction.slash_mul]
  rw [Finset.sum_range (fun i => (⇑f) ∣[k] (ModularForm.heckeMatrix (n + 1) i * W.alGL)),
    Finset.sum_range (fun i => (⇑f) ∣[k] (W.alGL * ModularForm.heckeMatrix (n + 1) i))]

  change ∑ j : ZMod (n + 1), (⇑f) ∣[k] (ModularForm.heckeMatrix (n + 1) j.val * W.alGL) =
    ∑ j : ZMod (n + 1), (⇑f) ∣[k] (W.alGL * ModularForm.heckeMatrix (n + 1) j.val)
  rw [← Equiv.sum_comp π (fun j => (⇑f) ∣[k] (W.alGL * ModularForm.heckeMatrix (n + 1) j.val))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hrel j, SlashAction.slash_mul]
  congr 1
  exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ (hγH j))

end
end S_CuspForm_alSlash_coe_heckeULinH_eq_coe_heckeULinH
end P2MW
export P2MW.S_CuspForm_alSlash_coe_heckeULinH_eq_coe_heckeULinH (solution)
